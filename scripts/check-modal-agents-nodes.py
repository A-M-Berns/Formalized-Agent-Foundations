#!/usr/bin/env python3
"""Check ModalAgents `Paper node:` annotations against the arXiv source.

Barász et al. (arXiv:1401.5577) label only 22 of their nodes, and several nodes the
formalization proves are unlabeled, so a label-based checker cannot cover this paper.
The stable source ID here is the *printed* theorem number.  That paper declares

    \\newtheorem{theorem}{Theorem}[section]

with `lemma`, `proposition`, `corollary` and `condition` sharing that counter, so numbers
read `<section>.<n>` and reset at every unstarred `\\section`.  This checker derives the
node set by emulating that counter over the committed TeX rather than hard-coding a
table, so it survives a source update.  Note that the paper's `definition` environment is
a bare `trivlist` with no counter at all — definitions are *unnumbered*, and citing one
is therefore a violation.

The annotation format is a docstring line

    Paper node: <Kind> <section>.<n> (§<section>).

matching the Cartesian Frames library's shape.  The kind must match the environment used
in the TeX, so citing `Theorem 4.5` for what is printed `Lemma 4.5` is a violation.

Enforced, fail-closed:

1. **Validity** — every node cited in a `Paper node:` line is actually numbered in the
   committed TeX source (a line may cite several nodes, comma-separated), and a
   `Paper node:` line that parses to *no* node at all is a violation (catches typos such
   as "Therem 4.7" that would otherwise be silently ignored).
2. **Anchoring** — the literal string `Paper node:` is reserved for the audited surface.
   Every occurrence must sit inside a `/-- … -/` declaration docstring, must be that
   docstring's last line, and that docstring must be followed by a *named* declaration
   (an anonymous `instance` cannot be inventoried, so it cannot carry an annotation).
   Internal lemmas cite paper nodes in prose, without the reserved string.
3. **Per-declaration coverage** — every annotated declaration must itself be listed in
   `AxiomAudit.lean`'s MA-INVENTORY block.  Sharing a node with some other listed
   declaration is *not* enough: the annotation claims a paper node for *this* statement,
   so this statement is what must be axiom-checked.

Declaration identity is namespace-aware: the checker tracks `namespace`/`section`/`end`
nesting to compute each declaration's fully qualified name, and matches it against the
inventory exactly.  `ModalAgents/` declares its surface at the root namespace and the
MA-INVENTORY block carries no `open … in`, so — unlike the Cartesian Frames checker —
there is no root-prefix fallback.  There is no bare-suffix matching either: `foo` in the
inventory never covers `A.B.foo` in the library.

The `printed-counter` scheme itself lives in `scripts/paper_nodes.py`, shared with the
trust-surface generator so there is one implementation of the counter emulation.

The converse direction (every *node* has a Lean statement) is deliberately not checked:
this formalization does not claim node-completeness for that paper.  One numbered node
is currently unformalized — Theorem 4.6, on self-referential modal agents.  See
`ModalAgents/README.md`.

Run from the repo root.
"""

import os
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_nodes  # noqa: E402

TEX = Path("ModalAgents/notes/1401.5577-main.tex")
LIB = Path("ModalAgents")
ROOT_MODULE = Path("ModalAgents.lean")
AUDIT = Path("AxiomAudit.lean")


def summary(*, citations, nodes, source, inventory):
    return ("modal-agents node check: OK "
            f"({citations} citations, {len(nodes)} distinct nodes, "
            f"{len(source)} numbered in the paper, {len(inventory)} inventoried endpoints)")


sys.exit(paper_nodes.run_node_check(
    tex=TEX,
    lib=LIB,
    root_module=ROOT_MODULE,
    audit=AUDIT,
    inventory_block="MA-INVENTORY",
    node_id_re=paper_nodes.PRINTED_COUNTER_NODE_ID,
    source_nodes=paper_nodes.printed_counter_nodes(TEX.read_text()),
    node_shape="(Theorem|Lemma|Proposition|Corollary|Condition) <section>.<n>",
    empty_source_message=f"{TEX}: no numbered nodes found — is the source intact?",
    summary=summary,
))
