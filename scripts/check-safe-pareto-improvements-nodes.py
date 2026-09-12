#!/usr/bin/env python3
"""Check Safe Pareto Improvements `Paper node:` annotations against the committed source.

Oesterheld and Conitzer's *Safe Pareto Improvements for Delegated Game Playing* (JAAMAS
36, 2022; doi 10.1007/s10458-022-09574-6) numbers its results on **global** counters that
never reset: Definitions on one (`Definition 1` … `Definition 8`), Assumptions on another
(`Assumption 1`, `Assumption 2`), and Theorem, Lemma, Proposition and Corollary on a
single shared one (`Theorem 1`, `Lemma 2`, `Theorem 3`, `Lemma 4`, `Proposition 5`, …
`Lemma 28`).  Examples are set as `Proposition (Example) n` and are Propositions.  The
paper labels nothing, so the printed kind-and-number pair is the provenance key — the
kind is part of it, since `Lemma 2` and `Definition 2` are different nodes.

**What is different here, and why it matters.**  As for Condensation, no TeX source for
this paper exists in this project: there is no arXiv record (arXiv 2403.05103 is a later
paper by the same authors, not this one), and the committed *source* is
`SafeParetoImprovements/notes/oesterheld-conitzer-2022-spi.txt`, a `pdftotext -layout`
extraction of the committed PDF.  The counters cannot be emulated; this checker reads the
printed numbers off the extraction's header lines through the `printed-global` scheme in
`scripts/paper_nodes.py`.

That puts more weight on the extraction than the TeX-backed papers put on their TeX, so
this checker adds the same guard Condensation's does.  Before checking anything it
re-derives the node set and asserts that it is *exactly* the 37 parseable nodes of the
paper, with the expected count of each kind.  A re-extraction with a different
`pdftotext`, a reflowed header, or a truncated file then fails loudly, instead of quietly
shrinking the set of nodes an annotation is permitted to name.

**Why 37 and not 38.**  The paper prints 38 numbered headers.  `Theorem 17` (Tennenholtz
2004, a cited external result) has its header torn across two lines by a display-size
delimiter in the extraction (`Theorem` / `(︁ n 17 (Tennenholtz 2004 [55]). Let …`) and is
not parsed.  That is accepted deliberately: the formalization does not carry it
(Proposition 18 is proved directly), so a `Paper node:` line citing it is an INVALID NODE
until someone decides to carry it, at which point the parser is what changes.  Two other
things the parser absorbs are not drift either: `Lemma 4` is printed twice (§4.4.2, and
restated at the head of Appendix C), and one mid-paragraph cross-reference inside the
proof of Lemma 21 is header-shaped (`Assumption 1 (with or without Lemma 2.2). That is,
…`).  Both name a node already declared, and the first occurrence wins.

The annotation format is a docstring line

    Paper node: `<Kind> <n>`

as in the other libraries.  The kind must match the paper, so citing `Theorem 4` for what
is printed `Lemma 4` is a violation, and an item reference such as `Lemma 2.2` names no
node — the node is `Lemma 2`, and the docstring says which item in prose.

Enforced, fail-closed:

1. **Validity** — every node cited in a `Paper node:` line is numbered in the committed
   extraction (a line may cite several, comma-separated), and a `Paper node:` line that
   parses to *no* node is itself a violation, so a typo cannot pass as silence.
2. **Anchoring** — `Paper node:` is reserved for the audited surface: every occurrence
   must sit inside a `/-- … -/` declaration docstring, be that docstring's last line, and
   be followed by a *named* declaration.  Internal lemmas cite the paper in prose.
3. **Per-declaration coverage** — every annotated declaration is listed in
   `AxiomAudit.lean`'s SPI-INVENTORY block, or staged in its SPI-PENDING block.  Sharing
   a node with some other listed declaration is not enough: the annotation claims a paper
   node for *this* statement, so this statement is what must be axiom-checked.

While the paper is `in-progress` and *nothing* is annotated, an absent SPI-INVENTORY
block is reported as a note rather than a failure; the block becomes mandatory with the
first annotated declaration.  The SPI-PENDING block is the staging device for endpoints
whose statement is final but whose proof is still `sorry`; it is pure Lean comment, and
`paper_nodes.run_node_check` fences it exactly as it does Condensation's (a name in both
blocks, a stale entry, a malformed line, and a non-empty block on a `completed` paper are
all hard failures).  See the preamble of the CONDENSATION-INVENTORY block in
`AxiomAudit.lean` for the rationale, which is shared.

The keyword rules for this library — every `theorem` carries a `Paper node:` line naming a
result, and `private theorem` never occurs — are `scripts/lint_paper_labels.py`'s job;
`SafeParetoImprovements` is registered there with the bare-integer form.

The converse direction (every *node* carries a Lean statement) is not checked: the
formalization is at milestone M0 and the scope table in
`SafeParetoImprovements/notes/scoping.md` §1 is still being ruled on.  The per-section
coverage readout below is the progress view in the meantime; once the scope is settled it
should become a `scope_manifest` passed to `paper_nodes.run_node_check`, as Finite
Factored Sets does.

Run from the repo root.
"""

import collections
import os
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_nodes  # noqa: E402
from papers import PAPERS  # noqa: E402

SOURCE = Path("SafeParetoImprovements/notes/oesterheld-conitzer-2022-spi.txt")
LIB = Path("SafeParetoImprovements")
ROOT_MODULE = Path("SafeParetoImprovements.lean")
AUDIT = Path("AxiomAudit.lean")
INVENTORY_BLOCK = "SPI-INVENTORY"
PENDING_BLOCK = "SPI-PENDING"
# Read the status from the registry rather than restating it here: the completed-paper
# gate on the pending block must arm itself when `papers.py` says the paper is done.
STATUS = PAPERS["safe-pareto-improvements"]["status"]

# The paper's parseable node inventory, counted off the PDF (38 printed headers less
# Theorem 17, see above).  This is the extraction-drift guard; it is a statement about
# the *paper* and the extraction together, so it changes only if one of them does.
EXPECTED_TOTAL = 37
EXPECTED_BY_KIND = {
    "Definition": 8,
    "Assumption": 2,
    "Theorem": 4,
    "Lemma": 10,
    "Proposition": 12,
    "Corollary": 1,
}
# The section each node is printed in, for the coverage readout.  Global counters carry
# no section information, so this is recorded here rather than derived.
SECTION_OF = {
    "Definition 1": "3", "Definition 2": "3", "Theorem 1": "3",
    "Definition 3": "4", "Lemma 2": "4", "Definition 4": "4", "Theorem 3": "4",
    "Assumption 1": "4", "Assumption 2": "4", "Lemma 4": "4",
    "Proposition 5": "4", "Proposition 6": "4", "Proposition 7": "4", "Proposition 8": "4",
    "Definition 5": "4", "Theorem 9": "4", "Proposition 10": "4",
    "Definition 6": "5", "Definition 7": "5", "Lemma 11": "5", "Proposition 12": "5",
    "Lemma 13": "5", "Corollary 14": "5", "Theorem 15": "5", "Proposition 16": "5",
    "Proposition 18": "A",
    "Lemma 19": "D", "Lemma 20": "D", "Lemma 21": "D", "Lemma 22": "D",
    "Proposition 23": "D", "Proposition 24": "D", "Proposition 25": "D",
    "Proposition 26": "D", "Definition 8": "D", "Lemma 27": "D", "Lemma 28": "D",
}
SECTIONS = ("3", "4", "5", "A", "D")


def derive_nodes():
    """The node set, with the extraction-drift guard.  Returns (nodes, failures)."""
    text = SOURCE.read_text(encoding="utf-8")
    nodes = paper_nodes.printed_global_nodes(text)
    failures = []

    if not nodes:
        failures.append(
            f"FAIL: {SOURCE}: no numbered nodes found — is the extraction intact?")
        return nodes, failures

    by_kind = collections.Counter(node.split(" ", 1)[0] for node in nodes)
    if len(nodes) != EXPECTED_TOTAL or by_kind != collections.Counter(EXPECTED_BY_KIND):
        failures.append(
            f"FAIL: {SOURCE}: derived {len(nodes)} nodes "
            f"({format_kinds(by_kind)}), expected {EXPECTED_TOTAL} "
            f"({format_kinds(collections.Counter(EXPECTED_BY_KIND))}). "
            "The committed extraction has drifted from the paper this checker was "
            "written against: re-extract with `pdftotext -layout`, or — if the paper "
            "itself changed — update EXPECTED_BY_KIND and SECTION_OF here and the scope "
            "table in SafeParetoImprovements/README.md together."
        )
    unplaced = sorted(nodes - set(SECTION_OF), key=paper_nodes.printed_global_node_sort_key)
    if unplaced:
        failures.append(
            f"FAIL: {SOURCE}: derived node(s) with no section recorded in SECTION_OF: "
            + ", ".join(unplaced))
    return nodes, failures


def format_kinds(counter):
    return ", ".join("%d %s" % (counter[kind], kind)
                     for kind in EXPECTED_BY_KIND if counter.get(kind))


def coverage_readout(nodes, cited):
    """Which of the paper's nodes are cited by at least one declaration."""
    lines = ["  coverage: %d/%d nodes cited by at least one declaration"
             % (len(cited), len(nodes))]
    for section in SECTIONS:
        in_section = {n for n in nodes if SECTION_OF.get(n) == section}
        hit = sorted(in_section & cited, key=paper_nodes.printed_global_node_sort_key)
        label = ("App. %s" % section) if section.isalpha() else ("§%s" % section)
        lines.append("    %-7s %2d/%2d%s"
                     % (label + ":", len(hit), len(in_section),
                        "  " + ", ".join(hit) if hit else ""))
    missing = sorted(set(nodes) - cited, key=paper_nodes.printed_global_node_sort_key)
    if missing:
        lines.append("  not yet cited (%d): %s" % (len(missing), ", ".join(missing)))
    return "\n".join(lines)


def main():
    nodes, failures = derive_nodes()
    if failures:
        for failure in failures:
            print(failure)
        return 1

    def report(*, citations, nodes, source, inventory):
        head = ("safe-pareto-improvements node check: OK "
                "(%d citations, %d distinct nodes, %d numbered in the paper, "
                "%d inventoried endpoints)"
                % (citations, len(nodes), len(source), len(inventory)))
        return head + "\n" + coverage_readout(source, nodes)

    return paper_nodes.run_node_check(
        tex=SOURCE,
        lib=LIB,
        root_module=ROOT_MODULE,
        audit=AUDIT,
        inventory_block=INVENTORY_BLOCK,
        node_id_re=paper_nodes.PRINTED_GLOBAL_NODE_ID,
        source_nodes=nodes,
        node_shape="(Definition|Assumption|Theorem|Lemma|Proposition|Corollary) <n>",
        empty_source_message=f"{SOURCE}: no numbered nodes found — is the source intact?",
        summary=report,
        inventory_required=False,
        pending_block=PENDING_BLOCK,
        paper_status=STATUS,
    )


sys.exit(main())
