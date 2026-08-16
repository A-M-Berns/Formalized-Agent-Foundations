import CartesianFrames.Categorical

/-!
# Cartesian Frames consumer API

Use the following import for downstream mathematics:

```lean
import CartesianFrames.API
```

It exposes frames and morphisms; image and duality; biextensionality, collapse,
biextensional and homotopy equivalence; world maps and currying; the ordinary,
additive, and multiplicative subagent relations; commit/assume/external/internal
operations; and the categorical characterizations and decomposition results.

The mathematical namespace is `CartesianFrames`; qualify `CartesianFrames.Frame` when
Mathlib's order-theoretic `Frame` is also in scope.  The relation notations require:

```lean
open scoped CartesianFrames.Frame
```

The primary relations are `Subagent` (`◁`), `AddSubagent` (`◁₊`), and `MultSubagent`
(`◁ₓ`).  Curry, covering, categorical, and sub-environment presentations remain supported
because they are genuine paper content, with `*_iff_*` lemmas providing the bridges.
`externalQuot` and `internalSect` are the paper's `/B` and `/F` variants.

This boundary excludes `CartesianFrames.Examples` and its concrete regression fixtures;
import that module explicitly when those witnesses are useful.  Claim 35 remains only
partially formalized by ruling: commit/assume idempotence is supplied at canonical
isomorphism strength, while the ill-typed external/internal half is not claimed here.
-/
