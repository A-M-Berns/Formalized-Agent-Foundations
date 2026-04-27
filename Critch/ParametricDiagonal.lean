/-
  Parametric diagonalization for Critch 2019, §4, Proposition 1.

  This file is a thin re-export of Foundation's parameterized fixed-point
  construction in the notation used by the Critch development. Foundation does
  the substantive diagonalization work.
-/

import Foundation.FirstOrder.Bootstrapping.FixedPoint

namespace LO.FirstOrder.Critch

open LO.Entailment

/--
Critch §4, Proposition 1 fixed point.

This is Foundation's `Arithmetic.parameterizedFixedpoint` with Critch-facing
naming.
-/
noncomputable abbrev parametricFixedpoint {r : Nat} (G : Semisentence ℒₒᵣ (r + 1)) :
    Semisentence ℒₒᵣ r :=
  Arithmetic.parameterizedFixedpoint G

/--
Critch §4, Proposition 1, general parameter arity.

Thin wrapper around Foundation's `Arithmetic.parameterized_diagonal`.
-/
theorem parametric_diagonal {T : Theory ℒₒᵣ} [𝗜𝚺₁ ⪯ T] {r : Nat}
    (G : Semisentence ℒₒᵣ (r + 1)) :
    T ⊢ ∀⁰* (parametricFixedpoint G 🡘 “!G !!(⌜parametricFixedpoint G⌝) ⋯”) := by
  simpa [parametricFixedpoint] using Arithmetic.parameterized_diagonal (T := T) G

/--
Critch §4, Proposition 1 in the single-parameter form used in the proof of
Theorem 1.

Thin wrapper around Foundation's `Arithmetic.parameterized_diagonal₁`.
-/
theorem parametric_diagonal₁ {T : Theory ℒₒᵣ} [𝗜𝚺₁ ⪯ T]
    (G : Semisentence ℒₒᵣ 2) :
    T ⊢ ∀⁰ (parametricFixedpoint G 🡘 G/[⌜parametricFixedpoint G⌝, #0]) := by
  exact Arithmetic.parameterized_diagonal₁ (T := T) G

end LO.FirstOrder.Critch
