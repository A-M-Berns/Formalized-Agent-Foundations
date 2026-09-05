import LogicalInduction.Framework.Computable

/-! # Fixed-code `evaln` runs in polynomially many interpreter steps

**Not a paper node.** Nothing here renders a result of arXiv:1609.03543.

`codeEvalSteps c k` counts the interpreter invocations `evaln k c n` performs, by the same
recursion `Nat.Partrec.Code.evaln` itself uses, and `codeEvalSteps_poly` shows that for each
**fixed** code that count is polynomial in the fuel.

**Why the count is structural.** `pair` and `comp` recurse into structurally smaller codes at
*unchanged* fuel, while `prec` and `rfind'` recurse into the *same* code with one less fuel.
The nesting depth of the fuel-consuming clauses is what becomes the polynomial's exponent.

**Where this stands in the development.** It is a calibration fact about
`Nat.Partrec.Code.evaln` alone — no machine, no tape, no complexity class — and it is the
*time* counterpart of the *value* bound `codeEvalBound` (`Framework/Emission.lean`), which is
likewise polynomial in the fuel for each fixed code. It is not the bound a compiled machine's
step count is measured against: that is `codeMachineTime`
(`Framework/Machine/EvalnRegBound.lean`), built from `evalnArithmeticCost`, `codeEvalBound` and
the two window bounds independently of anything here. The chain from a fuel certificate to
membership in the machine class runs through `Framework/MachineEfficiency.lean`.

**Why the statement is over fuel rather than over the day** (`dd:fuel`). `PolyFueled c f`
supplies a polynomial fuel bound in the numeric day `n`, and `EfficientlyComputable` supplies
the explicit clock `a * (n + 1) ^ k + a`; phrasing the step count over fuel is what lets those
polynomials compose. Since the paper presents the day in **unary**, polynomial in `n` is
polynomial in the input length.
-/

namespace LogicalInduction

open Nat.Partrec.Code

/-! ## Polynomial closure under products

`Framework/Computable.lean` carries the `IsPolyBounded` closure algebra; the pointwise product
is added here because it is what the `prec` case below needs — unrolling a fuel-decrementing
recursion multiplies a step count by the fuel. -/

/-- Polynomially bounded functions are closed under pointwise product. -/
lemma IsPolyBounded.mul {f g : ℕ → ℕ} (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded (fun n => f n * g n) := by
  obtain ⟨a₁, k₁, h₁⟩ := hf
  obtain ⟨a₂, k₂, h₂⟩ := hg
  refine ⟨4 * (a₁ + 1) * (a₂ + 1), k₁ + k₂, fun n => ?_⟩
  set X := (n + 1) ^ k₁ with hX
  set Y := (n + 1) ^ k₂ with hY
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hY1 : 1 ≤ Y := Nat.one_le_pow _ _ (by omega)
  have hf' : f n ≤ 2 * a₁ * X := by have := h₁ n; nlinarith
  have hg' : g n ≤ 2 * a₂ * Y := by have := h₂ n; nlinarith
  have hxy : (n + 1) ^ (k₁ + k₂) = X * Y := by rw [hX, hY, pow_add]
  calc f n * g n ≤ (2 * a₁ * X) * (2 * a₂ * Y) := Nat.mul_le_mul hf' hg'
    _ = 4 * a₁ * a₂ * (X * Y) := by ring
    _ ≤ 4 * (a₁ + 1) * (a₂ + 1) * (n + 1) ^ (k₁ + k₂) := by rw [hxy]; nlinarith
    _ ≤ 4 * (a₁ + 1) * (a₂ + 1) * (n + 1) ^ (k₁ + k₂) + 4 * (a₁ + 1) * (a₂ + 1) :=
        Nat.le_add_right _ _

/-! ## The interpreter's step count -/

/-- The number of `evaln` invocations a fixed code performs at a given fuel, counted by the
same recursion `Nat.Partrec.Code.evaln` uses.

`pair` and `comp` recurse into structurally smaller codes at *unchanged* fuel; `prec` and
`rfind'` recurse into the *same* code with one less fuel. That asymmetry is the whole
content of the bound below: nesting depth of the fuel-consuming clauses becomes the
polynomial's exponent. -/
def codeEvalSteps : Nat.Partrec.Code → ℕ → ℕ
  | _, 0 => 1
  | .zero, _ + 1 => 1
  | .succ, _ + 1 => 1
  | .left, _ + 1 => 1
  | .right, _ + 1 => 1
  | .pair cf cg, k + 1 => 1 + codeEvalSteps cf (k + 1) + codeEvalSteps cg (k + 1)
  | .comp cf cg, k + 1 => 1 + codeEvalSteps cg (k + 1) + codeEvalSteps cf (k + 1)
  | .prec cf cg, k + 1 =>
      1 + codeEvalSteps cf (k + 1) + codeEvalSteps cg (k + 1)
        + codeEvalSteps (.prec cf cg) k
  | .rfind' cf, k + 1 => 1 + codeEvalSteps cf (k + 1) + codeEvalSteps (.rfind' cf) k
  termination_by c k => (k, sizeOf c)

/-! ## The step count is polynomial in the fuel

The two fuel-consuming clauses (`prec`, `rfind'`) unroll into a sum over fuel levels. Rather
than proving `codeEvalSteps` itself monotone — which would need the same lexicographic
induction as its definition — the argument below bounds each sub-count by the *monotone
majorant* its polynomial bound supplies, and sums that. -/

/-- The normal-form polynomial majorant is monotone. -/
private lemma polyMajorant_mono (a m : ℕ) :
    Monotone (fun k => a * (k + 1) ^ m + a) := by
  intro i j hij
  have : (i + 1) ^ m ≤ (j + 1) ^ m := Nat.pow_le_pow_left (by omega) m
  simp only
  nlinarith

/-- The normal-form polynomial majorant is itself polynomially bounded, by its own witness. -/
private lemma polyMajorant_isPolyBounded (a m : ℕ) :
    IsPolyBounded (fun k => a * (k + 1) ^ m + a) :=
  ⟨a, m, fun _ => le_rfl⟩

/-- Unrolling a fuel-decrementing recursion against a monotone majorant. -/
private lemma steps_le_of_recur {S C : ℕ → ℕ} (hC : Monotone C)
    (h0 : S 0 ≤ C 0) (hstep : ∀ k, S (k + 1) ≤ C (k + 1) + S k) :
    ∀ k, S k ≤ (k + 1) * C k := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ k ih =>
      have hmono : C k ≤ C (k + 1) := hC (Nat.le_succ k)
      calc S (k + 1) ≤ C (k + 1) + S k := hstep k
        _ ≤ C (k + 1) + (k + 1) * C k := by omega
        _ ≤ C (k + 1) + (k + 1) * C (k + 1) := by nlinarith
        _ = (k + 1 + 1) * C (k + 1) := by ring

/-- **Fixed-code `evaln` takes polynomially many interpreter steps in its fuel.**

The exponent depends on the code — specifically on how deeply `prec`/`rfind'` nest, since
those are the clauses that consume fuel. For each fixed code the count is polynomial, which
is what a polynomial-time simulation of a *fixed* program needs. -/
lemma codeEvalSteps_poly (c : Nat.Partrec.Code) : IsPolyBounded (codeEvalSteps c) := by
  induction c with
  | zero | succ | left | right =>
      exact ⟨1, 0, fun k => by cases k <;> simp [codeEvalSteps]⟩
  | pair cf cg ihf ihg =>
      refine IsPolyBounded.of_le
        (((IsPolyBounded.linear 1).add ihf).add ihg) fun k => ?_
      cases k with
      | zero => simp [codeEvalSteps]
      | succ k => simp only [codeEvalSteps]; omega
  | comp cf cg ihf ihg =>
      refine IsPolyBounded.of_le
        (((IsPolyBounded.linear 1).add ihg).add ihf) fun k => ?_
      cases k with
      | zero => simp [codeEvalSteps]
      | succ k => simp only [codeEvalSteps]; omega
  | prec cf cg ihf ihg =>
      obtain ⟨a₁, m₁, h₁⟩ := ihf
      obtain ⟨a₂, m₂, h₂⟩ := ihg
      set C : ℕ → ℕ :=
        fun k => 1 + (a₁ * (k + 1) ^ m₁ + a₁) + (a₂ * (k + 1) ^ m₂ + a₂) with hC
      have hCmono : Monotone C := by
        intro i j hij
        have : a₁ * (i + 1) ^ m₁ + a₁ ≤ a₁ * (j + 1) ^ m₁ + a₁ := polyMajorant_mono a₁ m₁ hij
        have : a₂ * (i + 1) ^ m₂ + a₂ ≤ a₂ * (j + 1) ^ m₂ + a₂ := polyMajorant_mono a₂ m₂ hij
        simp only [hC]
        omega
      have hbound := steps_le_of_recur (S := codeEvalSteps (.prec cf cg)) hCmono
        (by simp [codeEvalSteps, hC]; omega)
        (fun k => by
          simp only [codeEvalSteps, hC]
          have := h₁ (k + 1)
          have := h₂ (k + 1)
          omega)
      have hconst : IsPolyBounded (fun _ : ℕ => 1) := ⟨1, 0, fun _ => by simp⟩
      exact IsPolyBounded.of_le
        ((IsPolyBounded.linear 1).mul
          ((hconst.add (polyMajorant_isPolyBounded a₁ m₁)).add
            (polyMajorant_isPolyBounded a₂ m₂)))
        hbound
  | rfind' cf ihf =>
      obtain ⟨a₁, m₁, h₁⟩ := ihf
      set C : ℕ → ℕ := fun k => 1 + (a₁ * (k + 1) ^ m₁ + a₁) with hC
      have hCmono : Monotone C := by
        intro i j hij
        have : a₁ * (i + 1) ^ m₁ + a₁ ≤ a₁ * (j + 1) ^ m₁ + a₁ := polyMajorant_mono a₁ m₁ hij
        simp only [hC]
        omega
      have hbound := steps_le_of_recur (S := codeEvalSteps (.rfind' cf)) hCmono
        (by simp [codeEvalSteps, hC])
        (fun k => by
          simp only [codeEvalSteps, hC]
          have := h₁ (k + 1)
          omega)
      have hconst : IsPolyBounded (fun _ : ℕ => 1) := ⟨1, 0, fun _ => by simp⟩
      exact IsPolyBounded.of_le
        ((IsPolyBounded.linear 1).mul (hconst.add (polyMajorant_isPolyBounded a₁ m₁)))
        hbound

end LogicalInduction
