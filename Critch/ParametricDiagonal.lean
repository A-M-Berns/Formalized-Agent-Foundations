/-
  ℒₒᵣ instance of the parametric diagonalization interface (Critch 2019, §4,
  Proposition 1).

  The interface class `ParametricDiagonalization` lives in
  `Critch/BoundedProvability/Diagonal.lean`; this file discharges it for any
  theory of `ℒₒᵣ` extending `𝗜𝚺₁`, via Foundation's parameterized fixed-point
  construction under Foundation's own names (`Arithmetic.parameterizedFixedpoint`,
  `Arithmetic.parameterized_diagonal₁`). Foundation does the substantive
  diagonalization work; the round-3 rename wrappers (R3-F08) are gone.
-/

import Foundation.FirstOrder.Bootstrapping.FixedPoint
import Critch.BoundedProvability.Diagonal

namespace LO.FirstOrder.Critch

/--
Critch §4, Proposition 1 at `ℒₒᵣ`: any `T` with `𝗜𝚺₁ ⪯ T` — in particular any
`S` "capable of representing all computable functions, as in Section 2.4" that
extends `𝗜𝚺₁` — admits the parametric diagonal, by Foundation's
`Arithmetic.parameterized_diagonal₁` with `ψ := Arithmetic.parameterizedFixedpoint G`.

Paper node: §4 (Proposition 1, discharged at `ℒₒᵣ`).
-/
noncomputable instance instParametricDiagonalizationLOR
    (T : Theory ℒₒᵣ) [𝗜𝚺₁ ⪯ T] : ParametricDiagonalization T where
  fixedpoint := Arithmetic.parameterizedFixedpoint
  diagonal := Arithmetic.parameterized_diagonal₁ (T := T)

end LO.FirstOrder.Critch
