#!/usr/bin/env python3
"""Regression tests for `scripts/paper_nodes.py`'s two audit-block readers and its
`printed-global` extraction parser.

Run either way, from the repo root:

    python3 scripts/test_paper_nodes.py
    python3 -m pytest scripts/test_paper_nodes.py

No network, no Lean, no build: every case is a scratch fragment written to a temporary
file, plus a final pair of cases that parse the repository's own `AxiomAudit.lean`.

**What these are protecting.**  `read_inventory` used to collect *every*
identifier-shaped token following `#assert_axioms_clean` until the next `#` token.  A
Lean declaration written inside the marker block — `lemma foo : True := trivial`, whether
by accident or on purpose — therefore contributed `lemma`, `foo`, `True` and `trivial`
to the inventory, after which the node checker believed `foo` was axiom-checked when
nothing checked it: a silently disarmed gate, which is the exact failure class this
tooling exists to prevent.  `read_pending` had the mirror hazard once the block grew a
`SECTION:` line, since `SECTION` is itself identifier-shaped and parsed as a staged
declaration of that name.  Both are now hard violations, and these tests are what keep
them so.
"""

import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_nodes  # noqa: E402

REPO = Path(os.path.dirname(os.path.abspath(__file__))).parent


def fragment(body):
    """Write `body` to a scratch file and return its path (cleaned up by the caller)."""
    handle = tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False)
    handle.write(body)
    handle.close()
    return handle.name


class BlockReaderTest(unittest.TestCase):
    """Base class: parse a scratch fragment, clean up after."""

    def setUp(self):
        self.paths = []

    def tearDown(self):
        for path in self.paths:
            os.unlink(path)

    def inventory(self, body, block="TEST-INVENTORY"):
        path = fragment(body)
        self.paths.append(path)
        return paper_nodes.read_inventory(path, block)

    def pending(self, body, block="TEST-PENDING"):
        path = fragment(body)
        self.paths.append(path)
        return paper_nodes.read_pending(path, block)


class ReadInventoryTest(BlockReaderTest):

    def test_absent_markers_give_none(self):
        self.assertIsNone(self.inventory("-- nothing to see here\n"))

    def test_clean_block_parses_with_no_problems(self):
        parsed = self.inventory(
            "-- TEST-INVENTORY-BEGIN\n"
            "#assert_axioms_clean\n"
            "  -- a comment naming Foo.bar is not an entry\n"
            "  Foo.bar Foo.baz\n"
            "  Foo.qux'\n"
            "-- TEST-INVENTORY-END\n")
        self.assertEqual(parsed.names, {"Foo.bar", "Foo.baz", "Foo.qux'"})
        self.assertEqual(parsed.problems, [])

    def test_declaration_inside_the_block_is_a_violation(self):
        """The regression this file exists for: a `lemma` smuggled into the block."""
        parsed = self.inventory(
            "-- TEST-INVENTORY-BEGIN\n"
            "#assert_axioms_clean\n"
            "  Foo.bar\n"
            "lemma smuggled : True := trivial\n"
            "-- TEST-INVENTORY-END\n")
        self.assertTrue(parsed.problems, "a `lemma` in the block must be reported")
        joined = "\n".join(parsed.problems)
        self.assertIn("INVENTORY BLOCK CONTAMINATED", joined)
        self.assertIn("'lemma'", joined)
        # And the smuggled declaration must NOT have entered the inventory: this is the
        # half that made the old hole dangerous rather than merely untidy.
        self.assertNotIn("smuggled", parsed.names)
        self.assertNotIn("True", parsed.names)
        self.assertNotIn("trivial", parsed.names)
        self.assertEqual(parsed.names, {"Foo.bar"})

    def test_every_declaration_keyword_is_rejected(self):
        for keyword in ("def", "theorem", "instance", "abbrev", "structure",
                        "inductive", "class", "example", "axiom", "opaque",
                        "namespace", "section", "end", "variable", "import",
                        "noncomputable", "private", "protected", "partial", "unsafe",
                        "attribute", "set_option", "macro", "syntax", "notation",
                        "deriving", "where"):
            with self.subTest(keyword=keyword):
                parsed = self.inventory(
                    "-- TEST-INVENTORY-BEGIN\n"
                    "#assert_axioms_clean\n"
                    f"  Foo.bar {keyword}\n"
                    "-- TEST-INVENTORY-END\n")
                self.assertTrue(parsed.problems, f"{keyword!r} must be rejected")
                self.assertNotIn(keyword, parsed.names)

    def test_structural_tokens_are_rejected(self):
        for token in (":=", "=>", "@[simp]", "(", "⟨x,"):
            with self.subTest(token=token):
                parsed = self.inventory(
                    "-- TEST-INVENTORY-BEGIN\n"
                    "#assert_axioms_clean\n"
                    f"  Foo.bar {token}\n"
                    "-- TEST-INVENTORY-END\n")
                self.assertTrue(parsed.problems, f"{token!r} must be rejected")
                self.assertEqual(parsed.names, {"Foo.bar"})

    def test_name_before_any_command_is_rejected(self):
        parsed = self.inventory(
            "-- TEST-INVENTORY-BEGIN\n"
            "  Foo.stray\n"
            "#assert_axioms_clean\n"
            "  Foo.bar\n"
            "-- TEST-INVENTORY-END\n")
        self.assertTrue(any("appears before any" in p for p in parsed.problems))
        self.assertEqual(parsed.names, {"Foo.bar"})

    def test_non_assert_command_is_rejected(self):
        parsed = self.inventory(
            "-- TEST-INVENTORY-BEGIN\n"
            "#eval 1\n"
            "#assert_axioms_clean\n"
            "  Foo.bar\n"
            "-- TEST-INVENTORY-END\n")
        self.assertTrue(any("#eval" in p for p in parsed.problems))
        # Tokens under a rejected command must not be collected either.
        self.assertEqual(parsed.names, {"Foo.bar"})

    def test_other_assert_commands_are_allowed_but_not_collected(self):
        """`#assert_fields Foo a b` is legal in a block and contributes no entries."""
        parsed = self.inventory(
            "-- TEST-INVENTORY-BEGIN\n"
            "#assert_axioms_clean\n"
            "  Foo.bar\n"
            "#assert_fields Foo fst snd\n"
            "-- TEST-INVENTORY-END\n")
        self.assertEqual(parsed.problems, [])
        self.assertEqual(parsed.names, {"Foo.bar"})

    def test_open_in_prefix_is_permitted_before_a_command(self):
        parsed = self.inventory(
            "-- TEST-INVENTORY-BEGIN\n"
            "open Foo Bar in\n"
            "#assert_axioms_clean\n"
            "  baz\n"
            "-- TEST-INVENTORY-END\n")
        self.assertEqual(parsed.problems, [])
        self.assertEqual(parsed.names, {"baz"})

    def test_open_without_a_following_command_is_rejected(self):
        parsed = self.inventory(
            "-- TEST-INVENTORY-BEGIN\n"
            "#assert_axioms_clean\n"
            "  Foo.bar\n"
            "open Foo in\n"
            "-- TEST-INVENTORY-END\n")
        self.assertTrue(parsed.problems)
        self.assertIn("unfinished `open", "\n".join(parsed.problems))

    def test_open_in_an_argument_list_is_rejected(self):
        """`open` is a prefix, never an entry: `… Foo.bar open Foo.baz` is malformed."""
        parsed = self.inventory(
            "-- TEST-INVENTORY-BEGIN\n"
            "#assert_axioms_clean\n"
            "  Foo.bar open Foo.baz\n"
            "-- TEST-INVENTORY-END\n")
        self.assertTrue(parsed.problems)
        self.assertNotIn("Foo.baz", parsed.names)


class ReadPendingTest(BlockReaderTest):

    def test_absent_markers_give_none(self):
        self.assertIsNone(self.pending("-- nothing here\n"))

    def test_block_without_a_section_line_parses_as_before(self):
        parsed = self.pending(
            "-- TEST-PENDING-BEGIN\n"
            "-- Foo.bar   -- M2: proof pending\n"
            "-- Foo.baz   -- M2: same\n"
            "-- TEST-PENDING-END\n")
        self.assertEqual(set(parsed.entries), {"Foo.bar", "Foo.baz"})
        self.assertEqual(parsed.consumers, {})
        self.assertEqual(parsed.problems, [])
        self.assertEqual(parsed.entries["Foo.bar"], "M2: proof pending")

    def test_section_line_is_not_parsed_as_a_declaration(self):
        """`SECTION` is identifier-shaped; the section test must run first."""
        parsed = self.pending(
            "-- TEST-PENDING-BEGIN\n"
            "-- Foo.bar   -- M2: proof pending\n"
            "-- SECTION: consumers (un-annotated)\n"
            "-- Foo.consumer   -- consumes Foo.bar\n"
            "-- TEST-PENDING-END\n")
        self.assertEqual(parsed.problems, [])
        self.assertEqual(set(parsed.entries), {"Foo.bar"})
        self.assertEqual(set(parsed.consumers), {"Foo.consumer"})
        self.assertNotIn("SECTION", parsed.entries)
        self.assertNotIn("SECTION", parsed.consumers)

    def test_bare_section_label_and_switching_back(self):
        parsed = self.pending(
            "-- TEST-PENDING-BEGIN\n"
            "-- SECTION: consumers\n"
            "-- Foo.consumer   -- consumes something\n"
            "-- SECTION: main\n"
            "-- Foo.bar        -- M2: proof pending\n"
            "-- TEST-PENDING-END\n")
        self.assertEqual(parsed.problems, [])
        self.assertEqual(set(parsed.entries), {"Foo.bar"})
        self.assertEqual(set(parsed.consumers), {"Foo.consumer"})

    def test_unknown_section_is_a_violation(self):
        parsed = self.pending(
            "-- TEST-PENDING-BEGIN\n"
            "-- SECTION: whatever\n"
            "-- Foo.bar   -- M2: proof pending\n"
            "-- TEST-PENDING-END\n")
        self.assertTrue(any("UNKNOWN PENDING SECTION" in p for p in parsed.problems))

    def test_duplicate_across_sections_is_a_violation(self):
        parsed = self.pending(
            "-- TEST-PENDING-BEGIN\n"
            "-- Foo.bar   -- M2: proof pending\n"
            "-- SECTION: consumers\n"
            "-- Foo.bar   -- consumes itself\n"
            "-- TEST-PENDING-END\n")
        self.assertTrue(any("DUPLICATE PENDING ENTRY" in p for p in parsed.problems))
        self.assertEqual(parsed.consumers, {})

    def test_consumer_without_a_reason_is_a_violation(self):
        parsed = self.pending(
            "-- TEST-PENDING-BEGIN\n"
            "-- SECTION: consumers\n"
            "-- Foo.consumer\n"
            "-- TEST-PENDING-END\n")
        self.assertTrue(any("no reason given" in p for p in parsed.problems))

    def test_code_line_in_the_block_is_a_violation(self):
        parsed = self.pending(
            "-- TEST-PENDING-BEGIN\n"
            "lemma smuggled : True := trivial\n"
            "-- TEST-PENDING-END\n")
        self.assertTrue(any("must be a `--` comment" in p for p in parsed.problems))
        self.assertEqual(parsed.entries, {})


class RepositoryBlocksTest(unittest.TestCase):
    """The repository's own blocks must parse clean.  This is the live gate."""

    AUDIT = REPO / "AxiomAudit.lean"
    INVENTORY_BLOCKS = ("MA-INVENTORY", "CF-INVENTORY", "FFS-INVENTORY",
                        "CONDENSATION-INVENTORY", "SPI-INVENTORY")
    PENDING_BLOCKS = ("CONDENSATION-PENDING", "SPI-PENDING")

    def test_every_inventory_block_is_uncontaminated(self):
        for block in self.INVENTORY_BLOCKS:
            with self.subTest(block=block):
                parsed = paper_nodes.read_inventory(self.AUDIT, block)
                self.assertIsNotNone(parsed, f"{block} markers are missing")
                self.assertEqual(parsed.problems, [])
                self.assertTrue(parsed.names)

    def test_every_pending_block_parses_clean(self):
        for block in self.PENDING_BLOCKS:
            with self.subTest(block=block):
                parsed = paper_nodes.read_pending(self.AUDIT, block)
                if parsed is None:
                    self.skipTest(f"no {block} block in this checkout")
                self.assertEqual(parsed.problems, [])
                self.assertFalse(set(parsed.entries) & set(parsed.consumers))


class PrintedGlobalSchemeTest(unittest.TestCase):
    """The `printed-global` extraction parser against the committed SPI extraction.

    The per-kind counts here duplicate the checker's drift guard on purpose: the checker
    proves the extraction is what the paper is, this proves the *parser* still reads it
    the same way after an edit to `paper_nodes.py`.
    """

    SOURCE = REPO / "SafeParetoImprovements/notes/oesterheld-conitzer-2022-spi.txt"

    def setUp(self):
        if not self.SOURCE.exists():
            self.skipTest("no SPI extraction in this checkout")
        self.text = self.SOURCE.read_text(encoding="utf-8")

    def test_node_set_and_kinds(self):
        nodes = paper_nodes.printed_global_nodes(self.text)
        self.assertEqual(len(nodes), 37)
        kinds = {}
        for node in nodes:
            kinds[node.split()[0]] = kinds.get(node.split()[0], 0) + 1
        self.assertEqual(kinds, {"Definition": 8, "Assumption": 2, "Theorem": 4,
                                 "Lemma": 10, "Proposition": 12, "Corollary": 1})
        # Headers glued to a page break, an Example-headed proposition, and the torn
        # Theorem 17 are the cases the parser is specifically written around.
        self.assertIn("Theorem 1", nodes)
        self.assertIn("Corollary 14", nodes)
        self.assertIn("Proposition 5", nodes)
        self.assertNotIn("Theorem 17", nodes)

    def test_first_occurrence_wins_and_floats_are_dropped(self):
        decls = paper_nodes.printed_global_declarations(self.text)
        # Lemma 4 is restated in Appendix C; the main-text statement is the one kept.
        self.assertLess(decls["Lemma 4"].position, self.text.find("Proof of Lemma 4"))
        # Proposition 16 is interrupted by two figure pages and a table.
        body = decls["Proposition 16"].body
        self.assertNotIn("Figure", body)
        self.assertNotIn("Table 7", body)
        self.assertTrue(body.rstrip().endswith("= ui (a)."))
        self.assertEqual(decls["Lemma 19"].title,
                         "path independence of iterated strict dominance")

    def test_item_references_are_not_nodes(self):
        found = paper_nodes.PRINTED_GLOBAL_NODE_ID.findall("Paper node: `Lemma 2.2`")
        self.assertEqual(found, [])
        found = paper_nodes.PRINTED_GLOBAL_NODE_ID.findall("Paper node: `Lemma 2`, `Theorem 3`")
        self.assertEqual(found, [("Lemma", "2"), ("Theorem", "3")])

    def test_sections_skip_algorithm_boxes(self):
        titles = [title for _, title in paper_nodes.printed_global_sections(self.text)]
        self.assertIn("§3.1 Unilateral safe Pareto Improvements", titles)
        self.assertIn("Appendix D.2.1 The omnilateral SPI problem", titles)
        self.assertFalse(any("Return True" in t or "minimax" in t for t in titles))


if __name__ == "__main__":
    unittest.main(verbosity=2)
