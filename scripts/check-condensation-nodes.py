#!/usr/bin/env python3
"""Check Condensation `Paper node:` annotations against the committed paper source.

Eisenstat's *Condensation: A Theory of Concepts* (July 2025) numbers its results
through a single section-scoped LaTeX theorem counter shared by `definition`,
`proposition`, `lemma`, `theorem`, `corollary` and `example`, so its printed identifiers
read `<section>.<n>` — `Definition 2.1` through `Corollary 5.10`.  That is the same
counter discipline as ModalAgents', and the paper labels nothing, so the printed number
is the provenance key.

**What is different here, and why it matters.**  No TeX source for this paper exists in
this project — there is no arXiv record (the paper is OpenReview `HwKFJ3odui`, author
copy `sameisenstat.net/doc/condensation-25-07.pdf`), and the author's sources are not
public.  The committed *source* is therefore `Condensation/notes/condensation-25-07.txt`,
a `pdftotext -layout` extraction of the committed PDF, and the counter cannot be
emulated: this checker reads the printed numbers off the extraction's header lines.

That puts more weight on the extraction than the other papers put on their TeX, so this
checker adds a guard the TeX-backed ones do not need.  Before checking anything it
re-derives the node set and asserts that it is *exactly* the paper's 42 nodes, with the
expected count of each kind.  A re-extraction with a different `pdftotext`, a reflowed
header, or a truncated file then fails loudly, instead of quietly shrinking the set of
nodes an annotation is permitted to name — which would turn this gate into one that
passes because it is checking nothing.

The extractor emits the font's own slots for f-ligatures rather than resolving them, so
"Definition" appears as `De\x1cnition` (printing as "Denition", reading as a dropped
`fi`); the header regex in `scripts/paper_nodes.py` accepts that spelling and normalises
the kind.  A corollary for anyone editing that code: **never `splitlines()` this file** —
Python splits on `\x1c`/`\x1d`/`\x1e`, which are exactly the ligature slots, and every
Definition header vanishes.

The annotation format is a docstring line

    Paper node: <Kind> <section>.<n> (§<section>).

as in the other libraries.  The kind must match the paper, so citing `Theorem 4.13` for
what is printed `Lemma 4.13` is a violation.

Enforced, fail-closed:

1. **Validity** — every node cited in a `Paper node:` line is numbered in the committed
   extraction (a line may cite several, comma-separated), and a `Paper node:` line that
   parses to *no* node is itself a violation, so a typo cannot pass as silence.
2. **Anchoring** — `Paper node:` is reserved for the audited surface: every occurrence
   must sit inside a `/-- … -/` declaration docstring, be that docstring's last line, and
   be followed by a *named* declaration.  Internal lemmas cite the paper in prose.
3. **Per-declaration coverage** — every annotated declaration is listed in
   `AxiomAudit.lean`'s CONDENSATION-INVENTORY block.  Sharing a node with some other
   listed declaration is not enough: the annotation claims a paper node for *this*
   statement, so this statement is what must be axiom-checked.

While the paper is `in-progress` and *nothing* is annotated, an absent
CONDENSATION-INVENTORY block is reported as a note rather than a failure — there is no
endpoint for it to protect yet, and `scripts/check_paper_wiring.py` runs this checker as
a gate, so an in-progress paper must not fail it spuriously.  The block becomes mandatory
with the first annotated declaration, and until it is listed each annotated declaration
is an uninventoried endpoint.

**Staged endpoints, and why rule 3 has a second door.**  This formalization is
mid-flight, and it reaches the paper's endpoints statement-first: several declarations
already carry a `Paper node:` line because their *statement* is final and is the paper's
real endpoint, while their proof is still `sorry`.  Such a declaration cannot be listed
in the CONDENSATION-INVENTORY block — that block wraps `#assert_axioms_clean`, and a
`sorry` is exactly what that command exists to catch, so listing it would either fail the
axiom gate or, worse, tempt someone to weaken it.  Dropping the annotation instead would
be a lie about the statement's provenance.  So the audit file carries a second block,

    -- CONDENSATION-PENDING-BEGIN
    -- Condensation.LatentModel.perfect_tfae_A            -- M2: proof pending
    -- CONDENSATION-PENDING-END

which is pure Lean comment — it compiles to nothing and asserts nothing.  It is a
*declaration of intent*, not a discharge: an annotated endpoint satisfies rule 3 by being
listed in either block, and the pending block says out loud, in the same file as the
axiom gate and under review with it, that this endpoint is claimed but not yet proved.

The staging is fenced so it buys nothing beyond that, and every fence is a hard failure:

* a name listed in **both** blocks fails — an endpoint is axiom-checked or proof-pending,
  never both, and this is what stops one being quietly "proved" in one place while it is
  still excused in the other;
* a pending entry naming **no annotated declaration** fails — a stale entry left behind
  when an endpoint is renamed or retired would otherwise sit there excusing nothing;
* a **malformed** pending line (not a `--` comment, no declaration name, no reason given)
  fails rather than being skipped, so the block cannot degrade into a place to hide
  things;
* and a non-empty pending block on a paper registered **`completed`** fails — staging is
  a mid-flight device, and a finished paper has every endpoint inside the axiom gate.
  The status is read from `scripts/papers.py` below rather than asserted here, so that
  gate arms itself the moment the registry says the paper is done.

A surviving non-empty block prints as a note (`N endpoints pending (sorry) — not
axiom-checked`), never as a violation: the situation it describes is honest work in
progress, and the count is the thing to watch shrink.

**The block's second section, and the declarations that are not endpoints.**  A `sorry`
does not stop at the endpoint that contains it: anything that *consumes* a staged
endpoint depends on `sorryAx` too, and some of those consumers carry no `Paper node:`
line of their own, so none of the rules above reaches them.  They are still outside the
axiom gate, and a ledger that cannot name them is a ledger that drifts.  The pending
block therefore has a second half, opened by a section line:

    -- SECTION: consumers (un-annotated)
    -- Condensation.LatentModel.entropy_joint_le_condScore  -- consumes (4.7)-(4.9)

Its entries obey the same line discipline (a `--` comment, a declaration name, a
non-empty reason, no name twice across *either* section) and their own two fences: a
consumer must name a real declaration under `Condensation/`, and it must **not** carry a
`Paper node:` annotation — one that acquires an annotation has become an endpoint and
belongs in the main section, which fails as an `ANNOTATED CONSUMER`.  Consumers never
satisfy the endpoint-coverage rule; they exist so that
`scripts/check_sorry_ledger.py` can demand, mechanically, that *every* declaration
depending on `sorryAx` is named in this block.  A block with no section line parses
exactly as it did before the section existed.

The keyword rules for this library — every `theorem` carries a `Paper node:` line, and
`private theorem` never occurs — are *not* duplicated here.  `scripts/lint_paper_labels.py`
already takes a per-library list of accepted label forms; `Condensation` is registered
there with the `<section>.<n>` form, so a bare integer will not do.

The converse direction (every *node* carries a Lean statement) is not yet checked: the
scope is settled (42 nodes, with Examples 5.1–5.3 proposed out pending a ruling) but the
formalization is at milestone M1.  The per-section coverage readout below is the
progress view in the meantime; when the scope ruling lands it should become a
`scope_manifest` passed to `paper_nodes.run_node_check`, as Finite Factored Sets does.

Run from the repo root.
"""

import collections
import os
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_nodes  # noqa: E402
from papers import PAPERS  # noqa: E402

SOURCE = Path("Condensation/notes/condensation-25-07.txt")
LIB = Path("Condensation")
ROOT_MODULE = Path("Condensation.lean")
AUDIT = Path("AxiomAudit.lean")
INVENTORY_BLOCK = "CONDENSATION-INVENTORY"
PENDING_BLOCK = "CONDENSATION-PENDING"
# Read the status from the registry rather than restating it here: the completed-paper
# gate on the pending block must arm itself when `papers.py` says the paper is done.
STATUS = PAPERS["condensation"]["status"]

# The paper's node inventory, counted off the PDF.  This is the extraction-drift guard
# described above; it is a statement about the *paper*, so it changes only if the paper
# does.
EXPECTED_TOTAL = 42
EXPECTED_BY_KIND = {
    "Definition": 18,
    "Proposition": 9,
    "Lemma": 4,
    "Theorem": 3,
    "Corollary": 3,
    "Example": 5,
}
# Section n's node count, for the coverage readout.
SECTIONS = ("2", "3", "4", "5")


def derive_nodes():
    """The node set, with the extraction-drift guard.  Returns (nodes, failures)."""
    text = SOURCE.read_text(encoding="utf-8")
    nodes = paper_nodes.printed_extraction_nodes(text)
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
            "itself changed — update EXPECTED_BY_KIND here and the scope table in "
            "Condensation/README.md together."
        )
    return nodes, failures


def format_kinds(counter):
    return ", ".join("%d %s" % (counter[kind], kind)
                     for kind in EXPECTED_BY_KIND if counter.get(kind))


def coverage_readout(nodes, cited):
    """Which of the paper's nodes are cited by at least one declaration."""
    lines = ["  coverage: %d/%d nodes cited by at least one declaration"
             % (len(cited), len(nodes))]
    for section in SECTIONS:
        in_section = {n for n in nodes if n.split(" ", 1)[1].split(".")[0] == section}
        hit = sorted(in_section & cited, key=paper_nodes.printed_extraction_node_sort_key)
        lines.append("    §%s: %2d/%2d%s"
                     % (section, len(hit), len(in_section),
                        "  " + ", ".join(hit) if hit else ""))
    missing = sorted(set(nodes) - cited, key=paper_nodes.printed_extraction_node_sort_key)
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
        head = ("condensation node check: OK "
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
        node_id_re=paper_nodes.PRINTED_EXTRACTION_NODE_ID,
        source_nodes=nodes,
        node_shape="(Definition|Proposition|Lemma|Theorem|Corollary|Example) "
                   "<section>.<n>",
        empty_source_message=f"{SOURCE}: no numbered nodes found — is the source intact?",
        summary=report,
        inventory_required=False,
        pending_block=PENDING_BLOCK,
        paper_status=STATUS,
    )


sys.exit(main())
