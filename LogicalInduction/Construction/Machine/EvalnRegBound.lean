/-
# A register bound for the compiled `evaln` interpreter

`codeEvalBound` (`Framework/Emission.lean`) bounds the value a *successful* `evaln` call
returns. That is not enough for the compiled machine, whose registers also hold
intermediate values larger than any node's own answer:

* `prec`'s body reconstructs `Nat.pair a (Nat.pair j acc)` before invoking `cg`, while
  `codeEvalBound (prec cf cg) k` is only `max (codeEvalBound cf k) (codeEvalBound cg k)`;
* `rfind'`'s body forms `Nat.pair a m` with `m` advancing one per level, so `m` can reach
  `m₀ + fuel` — past the input.

So the machine needs its own structural bound, and it must carry those pairs explicitly.
`codeRegBound c s` is that bound, with the single parameter `s` standing for a common
bound on the node's input *and* fuel registers. It is monotone in `s` and, for each fixed
code, polynomially bounded — which is what the runtime argument consumes.

Nothing here assumes an arbitrary bound is closed under `Nat.pair`: every pair the machine
forms appears in the definition.
-/
import LogicalInduction.Framework.Emission
import LogicalInduction.Construction.Machine.EvalnCompiler

namespace LogicalInduction.EvalnCompiler

open Nat.Partrec (Code)

/-- The value `prec`'s body pairs up before invoking `cg`: `Nat.pair a (Nat.pair j acc)`,
    with `a`, `j` bounded by the node's input and `acc` by either child's answer. -/
def precWindowBound (cf cg : Nat.Partrec.Code) (s : ℕ) : ℕ :=
  Nat.pair s (Nat.pair s (max (codeEvalBound cf s) (codeEvalBound cg s)))

/-- The value `rfind'`'s body pairs up: `Nat.pair a m`, with `m` advancing one level per
    unit of fuel, so bounded by input plus fuel. -/
def rfWindowBound (s : ℕ) : ℕ := Nat.pair s (s + s)

/-- **A bound on every register of a compiled node**, given a common bound `s` on its input
    and fuel registers. -/
def codeRegBound : Nat.Partrec.Code → ℕ → ℕ
  | .zero, s => s + 2
  | .succ, s => s + 2
  | .left, s => s + 2
  | .right, s => s + 2
  | .pair cf cg, s =>
      codeRegBound cf s + codeRegBound cg s
        + Nat.pair (codeEvalBound cf s) (codeEvalBound cg s) + 2
  | .comp cf cg, s =>
      codeRegBound cf (s + codeEvalBound cg s) + codeRegBound cg s + 2
  | .prec cf cg, s =>
      codeRegBound cf s + codeRegBound cg (s + precWindowBound cf cg s)
        + precWindowBound cf cg s + 2
  | .rfind' cf, s =>
      codeRegBound cf (s + rfWindowBound s) + rfWindowBound s + 2

lemma precWindowBound_mono (cf cg : Nat.Partrec.Code) :
    Monotone (precWindowBound cf cg) := by
  intro a b hab
  refine natPair_mono hab (natPair_mono hab ?_)
  exact max_le_max (codeEvalBound_mono cf hab) (codeEvalBound_mono cg hab)

lemma rfWindowBound_mono : Monotone rfWindowBound := by
  intro a b hab
  exact natPair_mono hab (Nat.add_le_add hab hab)

lemma codeRegBound_mono (c : Nat.Partrec.Code) : Monotone (codeRegBound c) := by
  induction c with
  | zero => intro a b hab; simpa [codeRegBound] using hab
  | succ => intro a b hab; simpa [codeRegBound] using hab
  | left => intro a b hab; simpa [codeRegBound] using hab
  | right => intro a b hab; simpa [codeRegBound] using hab
  | pair cf cg ihf ihg =>
      intro a b hab
      simp only [codeRegBound]
      exact Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (ihf hab) (ihg hab))
          (natPair_mono (codeEvalBound_mono cf hab) (codeEvalBound_mono cg hab))) 2
  | comp cf cg ihf ihg =>
      intro a b hab
      simp only [codeRegBound]
      exact Nat.add_le_add_right
        (Nat.add_le_add (ihf (Nat.add_le_add hab (codeEvalBound_mono cg hab))) (ihg hab)) 2
  | prec cf cg ihf ihg =>
      intro a b hab
      simp only [codeRegBound]
      exact Nat.add_le_add_right
        (Nat.add_le_add
          (Nat.add_le_add (ihf hab)
            (ihg (Nat.add_le_add hab (precWindowBound_mono cf cg hab))))
          (precWindowBound_mono cf cg hab)) 2
  | rfind' cf ihf =>
      intro a b hab
      simp only [codeRegBound]
      exact Nat.add_le_add_right
        (Nat.add_le_add (ihf (Nat.add_le_add hab (rfWindowBound_mono hab)))
          (rfWindowBound_mono hab)) 2

lemma precWindowBound_poly (cf cg : Nat.Partrec.Code) :
    IsPolyBounded (precWindowBound cf cg) :=
  (IsPolyBounded.linear 0).pair
    ((IsPolyBounded.linear 0).pair
      ((codeEvalBound_poly cf).max (codeEvalBound_poly cg)))

lemma rfWindowBound_poly : IsPolyBounded rfWindowBound :=
  (IsPolyBounded.linear 0).pair ((IsPolyBounded.linear 0).add (IsPolyBounded.linear 0))

/-- **The register bound is polynomial for each fixed code.** -/
lemma codeRegBound_poly (c : Nat.Partrec.Code) : IsPolyBounded (codeRegBound c) := by
  induction c with
  | zero => exact (IsPolyBounded.linear 2).of_le (fun _ => by simp [codeRegBound])
  | succ => exact (IsPolyBounded.linear 2).of_le (fun _ => by simp [codeRegBound])
  | left => exact (IsPolyBounded.linear 2).of_le (fun _ => by simp [codeRegBound])
  | right => exact (IsPolyBounded.linear 2).of_le (fun _ => by simp [codeRegBound])
  | pair cf cg ihf ihg =>
      refine ((ihf.add ihg).add
        ((codeEvalBound_poly cf).pair (codeEvalBound_poly cg))).add
        (IsPolyBounded.linear 2) |>.of_le (fun s => ?_)
      simp only [codeRegBound, Nat.add_zero]
      omega
  | comp cf cg ihf ihg =>
      refine ((ihf.comp ((IsPolyBounded.linear 0).add (codeEvalBound_poly cg))).add
        ihg).add (IsPolyBounded.linear 2) |>.of_le (fun s => ?_)
      simp only [codeRegBound, Nat.add_zero]
      omega
  | prec cf cg ihf ihg =>
      refine ((ihf.add
        (ihg.comp ((IsPolyBounded.linear 0).add (precWindowBound_poly cf cg)))).add
        (precWindowBound_poly cf cg)).add (IsPolyBounded.linear 2) |>.of_le (fun s => ?_)
      simp only [codeRegBound, Nat.add_zero]
      omega
  | rfind' cf ihf =>
      refine ((ihf.comp ((IsPolyBounded.linear 0).add rfWindowBound_poly)).add
        rfWindowBound_poly).add (IsPolyBounded.linear 2) |>.of_le (fun s => ?_)
      simp only [codeRegBound, Nat.add_zero]
      omega

/-- The bound is at least two more than the size parameter, so it dominates the node's own
    input and fuel registers and leaves room for a flag. -/
lemma le_codeRegBound (c : Nat.Partrec.Code) (s : ℕ) : s + 2 ≤ codeRegBound c s := by
  induction c with
  | zero => simp [codeRegBound]
  | succ => simp [codeRegBound]
  | left => simp [codeRegBound]
  | right => simp [codeRegBound]
  | pair cf cg ihf ihg => simp only [codeRegBound]; omega
  | comp cf cg ihf ihg =>
      simp only [codeRegBound]
      have := ihg
      omega
  | prec cf cg ihf ihg => simp only [codeRegBound]; omega
  | rfind' cf ihf =>
      simp only [codeRegBound]
      have h : s ≤ s + rfWindowBound s := Nat.le_add_right _ _
      have := codeRegBound_mono cf h
      have := ihf
      omega

/-! ## The `prec` loop stays inside the bound

`precRunG`'s value at any level is one of the two children's answers, so the level fuel
bounds it; the counter and the level fuel are bounded by the setup's `m` and `baseFuel`.
Together with `precBodyVals_lt` that gives the loop invariant `precTM_hoareTime` asks for. -/

section PrecLoopBound
variable {af ag : ℕ}

/-- Every level's accumulator is one of the children's answers at a fuel the level bounds. -/
lemma precRunG_val_le (cf cg : Nat.Partrec.Code) (a f₀ s : ℕ) :
    ∀ i, f₀ + i ≤ s →
      resultVal (precRunG cf cg a f₀ i)
        ≤ max (codeEvalBound cf s) (codeEvalBound cg s)
  | 0, h => by
      cases hv : Nat.Partrec.Code.evaln f₀ cf a with
      | none => simp [precRunG, hv]
      | some x =>
          have := codeEvaln_result_le cf (k := f₀) (n := a) (x := x) (by rw [hv]; rfl)
          simp only [precRunG, hv, resultVal]
          exact le_trans (le_trans this (codeEvalBound_mono cf (by omega))) (le_max_left _ _)
  | j + 1, h => by
      rw [precRunG]
      cases hp : precRunG cf cg a f₀ j with
      | none => exact Nat.zero_le _
      | some i =>
          show resultVal (Nat.Partrec.Code.evaln (f₀ + (j + 1)) cg
            (Nat.pair a (Nat.pair j i))) ≤ _
          cases hv : Nat.Partrec.Code.evaln (f₀ + (j + 1)) cg (Nat.pair a (Nat.pair j i)) with
          | none => exact Nat.zero_le _
          | some y =>
              have hle := codeEvaln_result_le cg (k := f₀ + (j + 1))
                (n := Nat.pair a (Nat.pair j i)) (x := y) (by rw [hv]; rfl)
              simp only [resultVal]
              exact le_trans (le_trans hle (codeEvalBound_mono cg (by omega)))
                (le_max_right _ _)

/-! ## The `prec` loop invariant -/

/-- **Every level of the `prec` loop satisfies the body's side conditions**, given a bound
    that dominates the window the body forms. -/
lemma precLoopVals_ok (haf : 16 ≤ af) (hag : 16 ≤ ag) (cf cg : Nat.Partrec.Code)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (hFg : ChildEncodes ag hag cg Fg)
    (V₀ : Fin (32 + af + ag) → ℕ) (a f₀ m s B : ℕ)
    (hB2 : 2 ≤ B) (hms : m ≤ s) (hfs : f₀ + m ≤ s) (has : a ≤ s)
    (hWB : precWindowBound cf cg s + 2 ≤ B)
    (hV₀ : ∀ k, V₀ k < B)
    (h6 : V₀ (precSelf af ag 6) = a) (h9 : V₀ (precSelf af ag 9) = 0)
    (h12 : V₀ (precSelf af ag 12) = f₀)
    (h10 : V₀ (precSelf af ag 10) = resultTag (Nat.Partrec.Code.evaln f₀ cf a))
    (h11 : V₀ (precSelf af ag 11) = resultVal (Nat.Partrec.Code.evaln f₀ cf a))
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) → ∀ k, Fg u k < B)
    (hFgTag : ∀ u : Fin ag → ℕ, Fg u ⟨2, by omega⟩ ≤ 1) :
    ∀ i, i ≤ m → PrecBodyOK af ag B (precLoopVals af ag haf hag Fg V₀ i) := by
  have hsW : s ≤ precWindowBound cf cg s := Nat.left_le_pair _ _
  -- the semantic invariant, specialised and packaged as the five numeric facts
  have key : ∀ i, i ≤ m →
      precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 6) = a ∧
      precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 9) = i ∧
      precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 12) = f₀ + i ∧
      precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 10) ≤ 1 ∧
      precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 11)
        ≤ max (codeEvalBound cf s) (codeEvalBound cg s) := by
    intro i hi
    obtain ⟨e6, e9, e12, e10, e11⟩ :=
      precLoopVals_spec haf hag cf cg Fg hFg V₀ a f₀ h6 h9 h12 h10 h11 i
    refine ⟨e6, e9, e12, ?_, ?_⟩
    · rw [e10]; exact resultTag_le_one _
    · rw [e11]; exact precRunG_val_le cf cg a f₀ s i (by omega)
  -- the arithmetic side conditions at level `i`
  have side : ∀ i, i ≤ m →
      precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 10) ≤ 1 ∧
      precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 9) + 1 < B ∧
      precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 12) + 1 < B ∧
      Nat.pair (precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 9))
        (precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 11)) < B ∧
      Nat.pair (precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 6))
        (Nat.pair (precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 9))
          (precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 11))) < B := by
    intro i hi
    obtain ⟨e6, e9, e12, e10, e11⟩ := key i hi
    have hin : Nat.pair (precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 9))
        (precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 11))
        ≤ Nat.pair s (max (codeEvalBound cf s) (codeEvalBound cg s)) := by
      exact natPair_mono (by rw [e9]; omega) e11
    have hin2 : Nat.pair s (max (codeEvalBound cf s) (codeEvalBound cg s))
        ≤ precWindowBound cf cg s :=
      natPair_mono (le_refl _) (Nat.right_le_pair _ _)
    refine ⟨e10, by rw [e9]; omega, by rw [e12]; omega, by omega, ?_⟩
    calc Nat.pair (precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 6))
            (Nat.pair (precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 9))
              (precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 11)))
        ≤ Nat.pair s (Nat.pair s (max (codeEvalBound cf s) (codeEvalBound cg s))) :=
          natPair_mono (by rw [e6]; exact has)
            (natPair_mono (by rw [e9]; omega) e11)
      _ < B := by
          have : Nat.pair s (Nat.pair s (max (codeEvalBound cf s) (codeEvalBound cg s)))
              = precWindowBound cf cg s := rfl
          omega
  -- the bound itself, by induction
  intro i
  induction i with
  | zero =>
      intro _
      obtain ⟨s10, s9, s12, sp1, sp2⟩ := side 0 (Nat.zero_le _)
      exact ⟨fun k => hV₀ k, s10, s9, s12, sp1, sp2⟩
  | succ k ih =>
      intro hk
      obtain ⟨b, o10, o9, o12, op1, op2⟩ := ih (by omega)
      obtain ⟨s10, s9, s12, sp1, sp2⟩ := side (k + 1) hk
      refine ⟨?_, s10, s9, s12, sp1, sp2⟩
      rw [precLoopVals_succ]
      exact precBodyVals_lt haf hag Fg _ B hB2 b o10 o9 o12 op1 op2 hFgB hFgTag

end PrecLoopBound

end LogicalInduction.EvalnCompiler
