/-
  Parametric diagonalization interface for Critch 2019, §4, Proposition 1.

  Proposition 1 is stated by the paper as an assumption-shaped input ("Suppose S is
  a first-order theory capable of representing all computable functions, as in
  Section 2.4") and consumed by Theorem 1's proof exactly once, at eq. 4.3. Per the
  round-4 ruling on R3-F03 (option (a), diagonal-as-hypothesis), it enters the
  general-`L` interface as one more class, discharged at ℒₒᵣ by Foundation's
  parameterized fixed point (`Critch/ParametricDiagonal.lean`) — the same pattern
  as every other external input to Theorem 1, and the same pattern as Foundation's
  own non-parametric `Diagonalization` class (ProvabilityAbstraction/Basic.lean).

  Design decisions (R3-F03):
  * **Arity `r = 1` only.** The paper states Proposition 1 for arbitrary `r`, but
    Theorem 1 consumes only `r = 1` (`G ∈ L_S(2)`, `ψ ∈ L_S(1)`); Foundation's
    `parameterized_diagonal` covers general `r` at ℒₒᵣ should a later consumer
    appear, at which point this class is extended, not rewritten.
  * **Quote assumption.** The biconditional puts `⌜ψ⌝` in `G`'s code slot, so the
    class assumes exactly that `L` has Gödel-number constants for its own
    one-free-variable formulas — `[Semiterm.Operator.GödelNumber L (Semisentence L 1)]`,
    the `Semisentence L 1` analogue of the `L.ReferenceableBy L` (= `GödelNumber`
    of `Sentence L`) already carried by `BoundedProvability`. Nothing weaker
    expresses the statement; nothing stronger is assumed.
  * **Sentence-level `⊢` only.** Eq. 4.3 uses the biconditional at a bounded
    `⊢_n`; the paper gets `n` from "in some number of characters n", i.e. from the
    mere existence of the proof — in the interface that is `ProofMeasure.complete`
    applied at the consumption site, so a bounded field here would be redundant.
  * **Skolemized fixed point.** The paper says "there exists a formula ψ"; the
    class carries the choice as a function field `fixedpoint`, following
    Foundation's `Diagonalization` precedent (Theorem 1's stronger conclusion
    eq. 4.7 mentions `ψ` itself, so a name for the witness is needed anyway).
-/

import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic

namespace LO

namespace FirstOrder
namespace Critch

variable {L : Language}

/--
Parametric diagonalization (Critch §4, Proposition 1, at the arity `r = 1` that
Theorem 1 consumes): for every `G ∈ L_S(2)` a formula `ψ = fixedpoint G ∈ L_S(1)`
with

`⊢ (∀k)(ψ[k] ↔ G[⌜ψ⌝, k])`,

the internal universal biconditional with `ψ`'s own Gödel number in `G`'s code
slot. The quote hypothesis `[Semiterm.Operator.GödelNumber L (Semisentence L 1)]`
is what "capable of representing all computable functions, as in Section 2.4"
costs at this generality: `L` can name its own one-variable formulas by constants.
The bounded form `⊢_n` used at eq. 4.3 is recovered via `ProofMeasure.complete`.

Discharged at `ℒₒᵣ` (for any `T` with `𝗜𝚺₁ ⪯ T`) by Foundation's
`Arithmetic.parameterized_diagonal₁` in `Critch/ParametricDiagonal.lean`.

Paper node: §4 (Proposition 1).
-/
class ParametricDiagonalization [Semiterm.Operator.GödelNumber L (Semisentence L 1)]
    (T : Theory L) where
  fixedpoint : Semisentence L 2 → Semisentence L 1
  diagonal (G : Semisentence L 2) :
    T ⊢ ∀⁰ (fixedpoint G 🡘 G/[⌜fixedpoint G⌝, #0])

end Critch
end FirstOrder
end LO
