#!/usr/bin/env python3
"""Check Finite Factored Sets `Paper node:` annotations against the arXiv source.

Garrabrant (arXiv:2109.11513) carries only 32 `\\label` commands, and two of those are not
on numbered nodes at all (`tab:my_label` labels a table, `inftime` labels
`\\section{Inferring Time}`), so exactly 30 of its 98 numbered nodes are labelled.  The
labels it does carry are working names (`templabel1`, `templabel2`, `templabel4`), so a
label-based checker cannot cover this paper.  The stable source ID here is the *printed*
number.

That paper declares its theorem environments **without** a `[section]` argument and
without sharing counters, so every environment numbers independently and never resets:
`Definition 1`…`Definition 50` run the length of the paper alongside
`Proposition 1`…`Proposition 36`, `Theorem 1`…`Theorem 3`, `Lemma 1`…`Lemma 3`,
`Corollary 1`, `Example 1`…`Example 4` and `Conjecture 1`.  This is the
`printed-independent` scheme in `scripts/paper_nodes.py` — a different counter discipline
from ModalAgents' single section-scoped counter, not a variant of it.  As there, the node
set is *derived* by emulating the counters over the committed TeX rather than hard-coded,
so it survives a source update.

Two hazards in this particular source, both handled in `paper_nodes.py` rather than here:

* the theorem environments from `miri-tech-article.cls`'s `miritools.sty` are declared
  inside an `\\if@environments` conditional, and `main.tex` separately declares
  `example`, `conjecture`, `proposition`, `corollary` and `lemma2`;
* `lemma2` is a *second* counter that also prints "Lemma".  The `lemma` counter is never
  used — all three printed Lemmas come from `lemma2` — so a checker that emulated `lemma`
  and ignored `lemma2` would silently find no lemmas at all.  `paper_nodes.py` maps
  environments to printed names explicitly and *fails closed* if two environments sharing
  a printed name are both used, since a printed number would then not identify a node.

The annotation format is a docstring line

    Paper node: <Kind> <n> (§<section>).

matching the other libraries' shape.  The kind must match the environment used in the
TeX, so citing `Theorem 1` for what is printed `Proposition 1` is a violation.

Enforced, fail-closed:

1. **Validity** — every node cited in a `Paper node:` line is actually numbered in the
   committed TeX source (a line may cite several nodes, comma-separated), and a
   `Paper node:` line that parses to *no* node at all is a violation (catches typos such
   as "Propositon 4" that would otherwise be silently ignored).
2. **Anchoring** — the literal string `Paper node:` is reserved for the audited surface.
   Every occurrence must sit inside a `/-- … -/` declaration docstring, must be that
   docstring's last line, and that docstring must be followed by a *named* declaration
   (an anonymous `instance` cannot be inventoried, so it cannot carry an annotation).
   Internal lemmas cite paper nodes in prose, without the reserved string.
3. **Per-declaration coverage** — every annotated declaration must itself be listed in
   `AxiomAudit.lean`'s FFS-INVENTORY block.  Sharing a node with some other listed
   declaration is *not* enough: the annotation claims a paper node for *this* statement,
   so this statement is what must be axiom-checked.

Declaration identity is namespace-aware: the checker tracks `namespace`/`section`/`end`
nesting to compute each declaration's fully qualified name, and matches it against the
inventory exactly (inventory entries may omit the `FiniteFactoredSets.` root prefix,
since the block is elaborated under `open FiniteFactoredSets in`).  There is no
bare-suffix matching — `foo` in the inventory never covers `A.B.foo` in the library.

4. **Exact scope coverage** — `FiniteFactoredSets/notes/scope-manifest.json` records the
   ruling (Example 3 out of scope) and the nine nodes rendered by Mathlib
   vocabulary with no carrier of ours; the checker requires that (numbered nodes in the
   TeX) − out_of_scope − mathlib_rendered equal the annotated node set, in both
   directions.  Removing the only carrier of an in-scope node, or annotating a node the
   manifest says is rendered, is a violation.  Editing the manifest is a scope change.

One thing this checker deliberately does **not** enforce, which a reader has mistaken for
enforced in the past:

* **The converse inventory direction** — that every name listed between the FFS-INVENTORY
  markers is a real, annotated declaration.  The block holds far more entries than there
  are annotations (it also carries the non-vacuity witnesses), so no such correspondence
  could be enforced; an inventory line naming a declaration that does not exist passes this
  checker and is caught only when `AxiomAudit.lean` is elaborated, by
  `#assert_axioms_clean` failing to resolve the name.  `lake build AxiomAudit` is therefore
  part of this contract, not an independent one.

Run from the repo root.
"""

import json
import os
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_nodes  # noqa: E402

TEX = Path("FiniteFactoredSets/notes/2109.11513-main.tex")
LIB = Path("FiniteFactoredSets")
ROOT_MODULE = Path("FiniteFactoredSets.lean")
AUDIT = Path("AxiomAudit.lean")
MANIFEST = Path("FiniteFactoredSets/notes/scope-manifest.json")


def summary(*, citations, nodes, source, inventory):
    return ("finite-factored-sets node check: OK "
            f"({citations} citations, {len(nodes)} distinct nodes, "
            f"{len(source)} numbered in the paper, {len(inventory)} inventoried endpoints; "
            f"scope manifest: exact coverage)")


_manifest = json.loads(MANIFEST.read_text())
_manifest["path"] = str(MANIFEST)


sys.exit(paper_nodes.run_node_check(
    tex=TEX,
    lib=LIB,
    root_module=ROOT_MODULE,
    audit=AUDIT,
    inventory_block="FFS-INVENTORY",
    root_prefix="FiniteFactoredSets",
    node_id_re=paper_nodes.PRINTED_INDEPENDENT_NODE_ID,
    source_nodes=paper_nodes.printed_independent_nodes(TEX.read_text()),
    node_shape="(Definition|Theorem|Proposition|Corollary|Lemma|Example|Conjecture) <n>",
    empty_source_message=f"{TEX}: no numbered nodes found — is the source intact?",
    summary=summary,
    scope_manifest=_manifest,
))
