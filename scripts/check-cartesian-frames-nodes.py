#!/usr/bin/env python3
"""Check Cartesian Frames `Paper node:` annotations against the arXiv source.

The paper numbers nodes in prose rather than assigning LaTeX labels to most of them.
This checker treats the printed `(Definition|Claim|Theorem) n` as the stable source ID.
It enforces, fail-closed:

1. **Validity** — every node cited in a `Paper node:` line is actually numbered in the
   committed TeX source (a line may cite several nodes, comma-separated), and a
   `Paper node:` line that parses to *no* node at all is a violation (catches typos
   such as "Defnition 4" that would otherwise be silently ignored).
2. **Anchoring** — the literal string `Paper node:` is reserved for the audited
   surface.  Every occurrence must sit inside a `/-- … -/` declaration docstring, must
   be that docstring's last line, and that docstring must be followed by a *named*
   declaration (an anonymous `instance` cannot be inventoried, so it cannot carry an
   annotation).  Internal lemmas and worked examples cite paper nodes in prose, without
   the reserved string.
3. **Per-declaration coverage** — every annotated declaration must itself be listed in
   `AxiomAudit.lean`'s CF-INVENTORY block.  Sharing a node with some other listed
   declaration is *not* enough: the annotation claims a paper node for *this*
   statement, so this statement is what must be axiom-checked.

Declaration identity is namespace-aware: the checker tracks `namespace`/`section`/`end`
nesting to compute each declaration's fully qualified name, and matches it against the
inventory exactly (inventory entries may omit the `CartesianFrames.` root prefix, since
the block is elaborated under `open CartesianFrames in`).  There is no bare-suffix
matching — `foo` in the inventory never covers `A.B.foo` in the library.

The `printed-inline` scheme itself lives in `scripts/paper_nodes.py`, shared with the
trust-surface generator so there is one implementation of "where is node N".

Run from the repo root.
"""

import os
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_nodes  # noqa: E402

TEX = Path("CartesianFrames/notes/2109.10996v1-main.tex")
LIB = Path("CartesianFrames")
ROOT_MODULE = Path("CartesianFrames.lean")
AUDIT = Path("AxiomAudit.lean")


def summary(*, citations, nodes, source, inventory):
    return ("cartesian-frames node check: OK "
            f"({citations} citations, {len(nodes)} distinct nodes, "
            f"{len(inventory)} inventoried endpoints)")


sys.exit(paper_nodes.run_node_check(
    tex=TEX,
    lib=LIB,
    root_module=ROOT_MODULE,
    audit=AUDIT,
    inventory_block="CF-INVENTORY",
    node_id_re=paper_nodes.PRINTED_INLINE_NODE_ID,
    source_nodes=paper_nodes.printed_inline_nodes(TEX.read_text()),
    node_shape="(Definition|Claim|Theorem) <number>",
    root_prefix="CartesianFrames",
    summary=summary,
))
