# Provenance of the vendored Shannon-information substrate

This directory records where `PFR/` came from, exactly what was changed, and how to
reproduce or update it. **`PFR/` is third-party source. Do not edit it by hand.**

## Upstream

| field | value |
| --- | --- |
| repository | <https://github.com/teorth/pfr> |
| project | Polynomial Freiman–Ruzsa conjecture formalization (Tao et al.) |
| commit | `65691129be2d8ca3e164c0822d95a456b88ee259` |
| commit date | 2026-09-17 |
| commit subject | `chore: bump mathlib to db1c574, fix breaking changes (#306)` |
| upstream toolchain | `leanprover/lean4:v4.34.0` |
| upstream Mathlib pin | `db1c5741da0acf96c97584de6ccf0e3bfbc0ae99` |
| licence | Apache License 2.0 — full text in `LICENSE-PFR` |

### Why this commit

It is the upstream commit on **this repository's toolchain**, `v4.34.0`, closest to the
Mathlib release tag FAF pins (`5ed2965`, the `v4.34.0` tag): upstream moved to `v4.34.0`
with this commit and to a later Mathlib than the tag with it, and nothing in the vendored
closure depends on that later Mathlib — the 27 modules compile against the tag unmodified.
Vendoring from a commit on the same toolchain is what keeps the tree patch-free.

## FAF context at import time

| field | value |
| --- | --- |
| FAF toolchain | `leanprover/lean4:v4.34.0` |
| FAF Mathlib pin | `5ed2965256430c3649e86755f9576b54eca72435` (the v4.34.0 release tag) |

Upstream and FAF share a toolchain and pin Mathlib commits a few weeks apart. At this
pair of pins that drift costs nothing: no patch is needed.

## Module closure

27 PFR-internal modules, 6,085 lines, listed in topological build order in
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
`diff` against an upstream checkout stays readable.

## Local patches

**None.** The committed tree is byte-identical to upstream at the commit above;
`vendor-pfr.sh --verify` re-derives the closure from upstream and diffs it against the
committed tree, reporting `IDENTICAL`. If that ever fails, the committed tree has drifted
from its recorded provenance and the difference must be classified (mathematics vs.
compatibility) before anything is merged.

Earlier vendorings (from `01c9b66`, on `v4.31.0`) carried two compatibility patches —
dropping a `positivity` extension whose `Mathlib.Meta.Positivity` signature had moved,
and a `funext` before a `MeasurableEquiv.map_symm` rewrite. Both drifts are resolved
upstream at this commit, so the patches are retired rather than carried forward. Should a
future bump need one again, it goes in `patches/` as a numbered unified diff with a
written justification, and `vendor-pfr.sh` applies whatever that directory holds.

## Reproducing and updating

```sh
# regenerate PFR/ from upstream (+ any patches; overwrites the committed tree)
ShannonInformation/vendor/vendor-pfr.sh

# audit only: regenerate into a temp dir and diff against the committed tree
ShannonInformation/vendor/vendor-pfr.sh --verify
```

To move to a newer upstream commit:

1. bump `PFR_REV` in `vendor-pfr.sh` and the tables above (prefer a commit on FAF's
   toolchain: that is what makes the tree patch-free);
2. run the script without `--verify` and rebuild (`lake build PFR ShannonInformation`);
3. for each new breakage, decide whether the fix is *compatibility* or *mathematics*.
   Compatibility fixes get a numbered patch in `patches/` with a written justification. A
   change that alters a mathematical statement is **not** a vendoring patch — it must be
   taken upstream, not carried here;
4. re-run `--verify` so the committed tree and its provenance agree again;
5. re-check `ShannonInformation/SCOPE.md`: a new upstream version may have relaxed
   hypotheses, which would change what FAF can honestly claim.

## What FAF is and is not claiming

FAF has **not** formalized Shannon information theory. It is consuming a pinned,
kernel-checked formalization produced by the PFR project, vendored so that the dependency
cannot disappear if upstream moves. The mathematics is theirs; the vendoring, the consumer
API and the scope analysis are FAF's.
