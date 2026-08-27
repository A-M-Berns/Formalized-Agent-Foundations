/-
# Fixed-code `evaln` runs in polynomially many interpreter steps

This file establishes the *time* half of the fuel-model calibration, as a fact about
`Nat.Partrec.Code.evaln` alone — no machine, no tape, no complexity class.

**What the calibration needs, and why this is the load-bearing half.**
`Framework/Emission.lean` already bounds the *values* `evaln` produces: `codeEvalBound` is
polynomial in the fuel for each fixed code (`codeEvalBound_poly`), and every result is under
it (`codeEvaln_result_le`). That controls output size. It says nothing about *runtime*, and
the model card is explicit that the two must not be conflated: a computation can produce a
small answer after enormous work.

`codeEvalSteps` below is the missing half — the number of interpreter invocations
`evaln k c n` performs, counted by the same recursion `evaln` itself uses. The theorem is:

```
codeEvalSteps_poly : ∀ c, IsPolyBounded (codeEvalSteps c)
```

For a **fixed** code, the interpreter's work is polynomial in its fuel. The exponent depends
on `c` — specifically on how deeply `prec`/`rfind'` nest, since those are the clauses that
recurse on the *same* code with one less fuel while `pair`/`comp` recurse on structurally
smaller codes at unchanged fuel. This is the bound the compiled machine's step count is
measured against, so the machine construction downstream works against a settled bound.

**Why this is stated over fuel rather than over the day.** `PolyFueled c f` supplies a
polynomial fuel bound `b` in the numeric day `n`, and `EfficientlyComputable` supplies the
explicit clock `a * (n + 1) ^ k + a`. Composing either with `codeEvalSteps_poly` gives a
polynomial step count in `n` — and since the paper presents the day in **unary**, polynomial
in `n` *is* polynomial in the input length. That is what makes the fuel calculus a sound
*certification device* for the machine class rather than a substitution for it.

**Not a paper node.** Nothing here renders a result of arXiv:1609.03543.
-/
import LogicalInduction.Framework.Computable

namespace LogicalInduction

open Nat.Partrec.Code

/-! ## A missing closure property of `IsPolyBounded`

`Framework/Computable.lean` has `.of_le`, `.linear`, `.max`, `.add_one`, `.pair` and `.comp`,
but no two-function product — which the `prec` case below needs, since unrolling a
fuel-decrementing recursion multiplies a step count by the fuel. -/

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

/-- Polynomially bounded functions are closed under pointwise sum. -/
lemma IsPolyBounded.add' {f g : ℕ → ℕ} (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded (fun n => f n + g n) := by
  obtain ⟨a₁, k₁, h₁⟩ := hf
  obtain ⟨a₂, k₂, h₂⟩ := hg
  refine ⟨a₁ + a₂, Max.max k₁ k₂, fun n => ?_⟩
  have hp₁ : (n + 1) ^ k₁ ≤ (n + 1) ^ Max.max k₁ k₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hp₂ : (n + 1) ^ k₂ ≤ (n + 1) ^ Max.max k₁ k₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have := h₁ n
  have := h₂ n
  nlinarith

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
  | zero =>
      refine ⟨1, 0, fun k => ?_⟩
      cases k <;> simp [codeEvalSteps]
  | succ =>
      refine ⟨1, 0, fun k => ?_⟩
      cases k <;> simp [codeEvalSteps]
  | left =>
      refine ⟨1, 0, fun k => ?_⟩
      cases k <;> simp [codeEvalSteps]
  | right =>
      refine ⟨1, 0, fun k => ?_⟩
      cases k <;> simp [codeEvalSteps]
  | pair cf cg ihf ihg =>
      refine IsPolyBounded.of_le
        (((IsPolyBounded.linear 1).add' ihf).add' ihg) fun k => ?_
      cases k with
      | zero => simp [codeEvalSteps]
      | succ k => simp only [codeEvalSteps]; omega
  | comp cf cg ihf ihg =>
      refine IsPolyBounded.of_le
        (((IsPolyBounded.linear 1).add' ihg).add' ihf) fun k => ?_
      cases k with
      | zero => simp [codeEvalSteps]
      | succ k => simp only [codeEvalSteps]; omega
  | prec cf cg ihf ihg =>
      obtain ⟨a₁, m₁, h₁⟩ := ihf
      obtain ⟨a₂, m₂, h₂⟩ := ihg
      set C : ℕ → ℕ :=
        fun k => 1 + (a₁ * (k + 1) ^ m₁ + a₁) + (a₂ * (k + 1) ^ m₂ + a₂) with hC
      have e1 : ∀ i j : ℕ, i ≤ j →
          a₁ * (i + 1) ^ m₁ + a₁ ≤ a₁ * (j + 1) ^ m₁ + a₁ :=
        fun i j hij => polyMajorant_mono a₁ m₁ hij
      have e2 : ∀ i j : ℕ, i ≤ j →
          a₂ * (i + 1) ^ m₂ + a₂ ≤ a₂ * (j + 1) ^ m₂ + a₂ :=
        fun i j hij => polyMajorant_mono a₂ m₂ hij
      have hCmono : Monotone C := by
        intro i j hij
        have := e1 i j hij
        have := e2 i j hij
        simp only [hC]
        omega
      have hbound := steps_le_of_recur (S := codeEvalSteps (.prec cf cg)) hCmono
        (by simp [codeEvalSteps, hC]; try omega)
        (fun k => by
          simp only [codeEvalSteps, hC]
          have := h₁ (k + 1)
          have := h₂ (k + 1)
          omega)
      have hconst : IsPolyBounded (fun _ : ℕ => 1) := ⟨1, 0, fun k => by simp⟩
      have hA : IsPolyBounded (fun k => a₁ * (k + 1) ^ m₁ + a₁) :=
        ⟨a₁, m₁, fun k => le_refl _⟩
      have hB : IsPolyBounded (fun k => a₂ * (k + 1) ^ m₂ + a₂) :=
        ⟨a₂, m₂, fun k => le_refl _⟩
      exact IsPolyBounded.of_le
        ((IsPolyBounded.linear 1).mul ((hconst.add' hA).add' hB)) hbound
  | rfind' cf ihf =>
      obtain ⟨a₁, m₁, h₁⟩ := ihf
      set C : ℕ → ℕ := fun k => 1 + (a₁ * (k + 1) ^ m₁ + a₁) with hC
      have e1 : ∀ i j : ℕ, i ≤ j →
          a₁ * (i + 1) ^ m₁ + a₁ ≤ a₁ * (j + 1) ^ m₁ + a₁ :=
        fun i j hij => polyMajorant_mono a₁ m₁ hij
      have hCmono : Monotone C := by
        intro i j hij
        have := e1 i j hij
        simp only [hC]
        omega
      have hbound := steps_le_of_recur (S := codeEvalSteps (.rfind' cf)) hCmono
        (by simp [codeEvalSteps, hC]; try omega)
        (fun k => by
          simp only [codeEvalSteps, hC]
          have := h₁ (k + 1)
          omega)
      have hconst : IsPolyBounded (fun _ : ℕ => 1) := ⟨1, 0, fun k => by simp⟩
      have hA : IsPolyBounded (fun k => a₁ * (k + 1) ^ m₁ + a₁) :=
        ⟨a₁, m₁, fun k => le_refl _⟩
      exact IsPolyBounded.of_le
        ((IsPolyBounded.linear 1).mul (hconst.add' hA)) hbound

end LogicalInduction
