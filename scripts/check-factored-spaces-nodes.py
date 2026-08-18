#!/usr/bin/env python3
"""Check FactoredSpaces `Paper node:` annotations against the arXiv source.

Garrabrant, Mayer, Wache, Lang, Eisenstat and Dell (arXiv:2412.02579, *Factored space
models*) label 45 of their 50 numbered nodes and leave five unlabeled — Definition 4.2
(the factored space itself), Definition 5.1, Proposition 5.6, Definition 5.7 and
Definition C.6 — so a label-based checker cannot cover this paper.  The stable source ID
here is the *printed* number.  That paper's `meta/environment.tex` declares

    \\newtheorem{theorem}{Theorem}[section]

with `definition`, `example`, `lemma`, `corollary`, `remark`, `summary`, `notation` and
`proposition` sharing that counter, so numbers read `<section>.<n>` and reset at every
unstarred `\\section`; after `\\appendix` the section prints as a letter (`Lemma A.1`).
Several results are wrapped in thmtools' `\\begin{restatable}[title]{lemma}{name}` — the
wrapper counts as the wrapped environment, and the `\\name*` restatement later in the
appendix re-prints the same number and does not count.  This checker derives the node
set by emulating that counter over the committed TeX rather than hard-coding a table
(scheme `printed-counter-appendix` in `scripts/paper_nodes.py`), so it survives a source
update.

The annotation format is a docstring line

    Paper node: <Kind> <section>.<n> (§<section>).

The kind must match the environment used in the TeX, so citing `Theorem 6.3` for what is
printed `Lemma 6.3` is a violation.

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
   `AxiomAudit.lean`'s FS-INVENTORY block.  Sharing a node with some other listed
   declaration is *not* enough: the annotation claims a paper node for *this* statement,
   so this statement is what must be axiom-checked.

Declaration identity is namespace-aware: the checker tracks `namespace`/`section`/`end`
nesting to compute each declaration's fully qualified name.  The library lives in the
`FactoredSpaces` namespace and the FS-INVENTORY block is preceded by
`open FactoredSpaces in`, so a bare inventory name resolves under that root prefix (as
in the Cartesian Frames and Finite Factored Sets checkers).

The converse inventory direction — that every name listed between the FS-INVENTORY markers
is a real, annotated declaration — is not and cannot be enforced here (the block also
carries non-vacuity witnesses); an inventory line naming a declaration that does not exist
is caught only when `AxiomAudit.lean` is elaborated.  `lake build AxiomAudit` is therefore
part of this contract, not an independent one.

Node-completeness (every numbered node has a Lean statement) is enforced through
`FactoredSpaces/notes/scope-manifest.json` once that file exists (a completed
formalization); while the paper is `in-progress` in `scripts/papers.py` the check runs
without it.

Run from the repo root.
"""

import json
import os
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_nodes  # noqa: E402

TEX = Path("FactoredSpaces/notes/2412.02579v2-main.tex")
LIB = Path("FactoredSpaces")
ROOT_MODULE = Path("FactoredSpaces.lean")
AUDIT = Path("AxiomAudit.lean")
MANIFEST = Path("FactoredSpaces/notes/scope-manifest.json")


def summary(*, citations, nodes, source, inventory):
    tail = "; scope manifest: exact coverage" if MANIFEST.exists() else ""
    return ("factored-spaces node check: OK "
            f"({citations} citations, {len(nodes)} distinct nodes, "
            f"{len(source)} numbered in the paper, {len(inventory)} inventoried endpoints"
            f"{tail})")


_manifest = None
if MANIFEST.exists():
    _manifest = json.loads(MANIFEST.read_text())
    _manifest["path"] = str(MANIFEST)


sys.exit(paper_nodes.run_node_check(
    tex=TEX,
    lib=LIB,
    root_module=ROOT_MODULE,
    audit=AUDIT,
    inventory_block="FS-INVENTORY",
    root_prefix="FactoredSpaces",
    node_id_re=paper_nodes.PRINTED_COUNTER_APPENDIX_NODE_ID,
    source_nodes=paper_nodes.printed_counter_appendix_nodes(TEX.read_text()),
    node_shape="(Definition|Theorem|Lemma|Proposition|Corollary) <section>.<n>",
    empty_source_message=f"{TEX}: no numbered nodes found — is the source intact?",
    summary=summary,
    scope_manifest=_manifest,
))
