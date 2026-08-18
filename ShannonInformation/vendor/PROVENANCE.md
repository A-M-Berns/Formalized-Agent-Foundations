# Provenance of the vendored Shannon-information substrate

This directory records where `PFR/` came from, exactly what was changed, and how to
reproduce or update it. **`PFR/` is third-party source. Do not edit it by hand.**

## Upstream

| field | value |
| --- | --- |
| repository | <https://github.com/teorth/pfr> |
| project | Polynomial Freiman–Ruzsa conjecture formalization (Tao et al.) |
| commit | `01c9b666945eaf73b3f7d8b20ffe003f8640e630` |
| commit date | 2026-06-27 |
| commit subject | `fix: use site.url for header nav links (#276)` |
| upstream toolchain | `leanprover/lean4:v4.31.0` |
| upstream Mathlib pin | `e1d1de3bbb575ceb968a895a3462d5a9ca4b22c9` |
| licence | Apache License 2.0 — full text in `LICENSE-PFR` |

### Why this commit and not `master`

`master` is on `leanprover/lean4:v4.34.0-rc1`. FAF is pinned at **v4.31.0**, and
`lakefile.lean` documents why that pin is load-bearing (it is the last upstream Foundation
commit that still contains `Foundation.Modal`, which `ModalAgents` is stated over).

PFR was itself on v4.31.0 from `38e9417` (2026-06-16) through `b56e834^` (2026-07-03).
`01c9b66` is the **last commit in that window**, so vendoring from it removes the
toolchain gap entirely and the Foundation pin does not have to move. That is the single
decision that makes this vendoring cheap; see the PR description.

## FAF context at import time

| field | value |
| --- | --- |
| FAF toolchain | `leanprover/lean4:v4.31.0` |
| FAF Mathlib pin | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (the v4.31.0 release tag) |

Upstream and FAF therefore share a toolchain but pin *different* Mathlib commits, weeks
apart. The two patches below are exactly the drift between them.

## Module closure

25 PFR-internal modules, 6,074 lines, listed in topological build order in
`CLOSURE.txt`. It is **derived, not curated**: `closure.py` walks `import` edges from the
four entropy-bearing modules

```
PFR.ForMathlib.Entropy.Basic
PFR.ForMathlib.Entropy.Measure
PFR.ForMathlib.Entropy.Kernel.Basic
PFR.ForMathlib.Entropy.Kernel.MutualInfo
```

and takes everything PFR-internal that is reachable. Deriving it rather than hand-picking
is what guarantees the vendored tree contains no PFR-specific additive-combinatorics
machinery: `ForMathlib/Entropy/Group.lean`, the Ruzsa-distance development and the
`AddCombi` dependency are simply not reachable from entropy, and so are absent.

`EXTERNAL-IMPORTS.txt` records the non-PFR modules the closure imports. **Every entry is
`Mathlib.*`.** An entry from `AddCombi`, `checkdecls`, or any other PFR dependency would
mean the closure had reached beyond information theory and should be treated as a
regression.

Files are kept at **upstream module paths** (`PFR/ForMathlib/…`, `PFR/Mathlib/…`) so that
`diff` against an upstream checkout stays readable. This mirrors how `ProvabilityLogic/`
is vendored in this repository.

## Local patches

Two, both recorded as unified diffs in `patches/`, both **compatibility only**. Neither
changes a statement, a definition, or a proof of any mathematical fact.

### `0001-drop-obsolete-positivity-extension.patch`

`PFR/ForMathlib/Entropy/Measure.lean` ends with a `positivity` tactic extension for
`measureMutualInfo`. It does not elaborate against FAF's Mathlib:
`Mathlib.Meta.Positivity.PositivityExt.eval` takes its partial-order argument as
`Q(PartialOrder $α)` here, where upstream's Mathlib pin had `Option _`.

The extension is **removed**, not repaired. Consequences:

- the theorem it wrapped, `measureMutualInfo_nonneg`, is defined above it and is
  **untouched**, still proved, and re-exported through `ShannonInformation.API`;
- the only loss is automation: `positivity` will not discharge `0 ≤ Im[μ]` by itself.
  Cite `measureMutualInfo_nonneg` instead.

Repairing rather than removing it would be a fine follow-up, but it would mean FAF
maintaining a tactic extension against a moving Mathlib API for no mathematical gain.

### `0002-funext-for-MeasurableEquiv-map_symm.patch`

In `PFR/ForMathlib/Entropy/Kernel/Basic.lean`, `entropy_prodMkLeft_unit` closes with
`rw [← MeasurableEquiv.map_symm]`. That rewrite cannot fire against FAF's Mathlib, where
the lemma is stated *applied to a measure*

```lean
lemma map_symm {μ : Measure α} (e : β ≃ᵐ α) : μ.map e.symm = μ.comap e
```

while the goal at that point is an equality of the *functions* `Measure.map` and
`Measure.comap`. A `funext ν` before the rewrite is the whole fix. The statement being
proved is unchanged.

### Anything else?

No. `vendor-pfr.sh --verify` re-derives the closure from upstream, applies these two
patches, and diffs the result against the committed tree; it reports `IDENTICAL`. If that
ever fails, the committed tree has drifted from its recorded provenance and the difference
must be classified (mathematics vs. compatibility) before anything is merged.

## Reproducing and updating

```sh
# regenerate PFR/ from upstream + patches (overwrites the committed tree)
ShannonInformation/vendor/vendor-pfr.sh

# audit only: regenerate into a temp dir and diff against the committed tree
ShannonInformation/vendor/vendor-pfr.sh --verify
```

To move to a newer upstream commit:

1. bump `PFR_REV` in `vendor-pfr.sh` and the tables above;
2. run the script without `--verify` and rebuild (`lake build PFR ShannonInformation`);
3. for each new breakage, decide whether the fix is *compatibility* or *mathematics*.
   Compatibility fixes get a new numbered patch in `patches/` with a written
   justification, like the two above. A change that alters a mathematical statement is
   **not** a vendoring patch — it must be taken upstream, not carried here;
4. re-run `--verify` so the committed tree and its provenance agree again;
5. re-check `ShannonInformation/SCOPE.md`: a new upstream version may have relaxed
   hypotheses, which would change what FAF can honestly claim.

## What FAF is and is not claiming

FAF has **not** formalized Shannon information theory. It is consuming a pinned,
kernel-checked formalization produced by the PFR project, vendored so that the dependency
cannot disappear if upstream moves. The mathematics is theirs; the vendoring, the two
compatibility patches, the consumer API and the scope analysis are FAF's.
