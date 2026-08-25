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

/-! ## The `rfind'` loop stays inside the bound

The search's three registers are constrained by an invariant the pure iterate carries:
`searching` and `found` are mutually exclusive flags, and `result` never exceeds the
current index — because it is only ever written on the single level that hits, and that
level is also the one that clears `searching`. -/

section RfindLoopBound
variable {af : ℕ}

/-- The invariant the search state satisfies at every level. -/
def RfStateOK (st : ℕ × ℕ × ℕ) (m : ℕ) : Prop :=
  st.1 + st.2.1 ≤ 1 ∧ st.2.2 ≤ m ∧ (st.2.1 = 0 → st.2.2 = 0)

lemma rfLevel_ok (cf : Nat.Partrec.Code) (a : ℕ) (st : ℕ × ℕ × ℕ) (f m : ℕ)
    (h : RfStateOK st m) : RfStateOK (rfLevel cf a st f m) (m + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [rfLevel, RfStateOK]
  set o := Nat.Partrec.Code.evaln f cf (Nat.pair a m) with ho
  set g : ℕ := if Nat.pair a m < f then 1 else 0 with hg
  set z : ℕ := if resultVal o = 0 then 1 else 0 with hz
  have hg1 : g ≤ 1 := by rw [hg]; split_ifs <;> omega
  have hz1 : z ≤ 1 := by rw [hz]; split_ifs <;> omega
  have ht1 : resultTag o ≤ 1 := resultTag_le_one o
  have hlive : st.1 * g * resultTag o ≤ st.1 := by
    calc st.1 * g * resultTag o ≤ st.1 * 1 * 1 :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) hg1) ht1
      _ = st.1 := by omega
  have hhit : st.1 * g * resultTag o * z ≤ st.1 * g * resultTag o :=
    calc st.1 * g * resultTag o * z ≤ st.1 * g * resultTag o * 1 :=
          Nat.mul_le_mul (le_refl _) hz1
      _ = st.1 * g * resultTag o := by omega
  have hnz : st.1 * g * resultTag o * (1 - z) ≤ st.1 * g * resultTag o :=
    calc st.1 * g * resultTag o * (1 - z) ≤ st.1 * g * resultTag o * 1 :=
          Nat.mul_le_mul (le_refl _) (by omega)
      _ = st.1 * g * resultTag o := by omega
  refine ⟨?_, ?_, ?_⟩
  · -- the two flags stay mutually exclusive
    rcases Nat.eq_zero_or_pos z with hz0 | hzp
    · have : st.1 * g * resultTag o * z = 0 := by rw [hz0]; omega
      omega
    · have hz1' : z = 1 := by omega
      have : st.1 * g * resultTag o * (1 - z) = 0 := by rw [hz1']; omega
      omega
  · -- the result never passes the current index
    rcases Nat.eq_zero_or_pos (st.1 * g * resultTag o * z) with hh0 | hhp
    · rw [hh0]; omega
    · have hst1 : 1 ≤ st.1 := by
        by_contra hc
        have : st.1 = 0 := by omega
        rw [this] at hhp; omega
      have hfo : st.2.1 = 0 := by omega
      have hr : st.2.2 = 0 := h3 hfo
      have hh1 : st.1 * g * resultTag o * z ≤ 1 := le_trans hhit (by omega)
      calc st.2.2 + st.1 * g * resultTag o * z * m ≤ 0 + 1 * m := by
            rw [hr]; exact Nat.add_le_add (le_refl _) (Nat.mul_le_mul hh1 (le_refl _))
        _ ≤ m + 1 := by omega
  · -- `found = 0` forces `result = 0`
    intro hfo0
    have hh0 : st.1 * g * resultTag o * z = 0 := by omega
    have : st.2.1 = 0 := by omega
    rw [hh0, h3 this]
    omega

lemma rfIter_ok (cf : Nat.Partrec.Code) (a : ℕ) :
    ∀ (t : ℕ) (st : ℕ × ℕ × ℕ) (f m : ℕ), RfStateOK st m →
      RfStateOK (rfIter cf a st f m t) (m + t) := by
  intro t
  induction t with
  | zero => intro st f m h; simpa using h
  | succ k ih =>
      intro st f m h
      rw [rfIter_succ]
      have := ih (rfLevel cf a st f m) (f - 1) (m + 1) (rfLevel_ok cf a st f m h)
      have he : m + 1 + k = m + (k + 1) := by omega
      rwa [he] at this

/-- **Every level of the `rfind'` loop satisfies the body's side conditions**, given a
    bound that dominates twice the window the body forms. -/
lemma rfLoopVals_ok (haf : 16 ≤ af) (cf : Nat.Partrec.Code)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (hFf : ChildEncodes af haf cf Ff)
    (V₀ : Fin (32 + af) → ℕ) (a m₀ fuel s B : ℕ)
    (hB2 : 2 ≤ B) (has : a ≤ s) (hm₀ : m₀ ≤ s) (hfuel : fuel ≤ s)
    (h2W : 2 * rfWindowBound s + 3 ≤ B)
    (hV₀ : ∀ k, V₀ k < B)
    (h6 : V₀ (rfSelf af 6) = a) (h7 : V₀ (rfSelf af 7) = m₀)
    (h8 : V₀ (rfSelf af 8) = fuel) (h9 : V₀ (rfSelf af 9) = 1)
    (h10 : V₀ (rfSelf af 10) = 0) (h11 : V₀ (rfSelf af 11) = 0)
    (h12 : V₀ (rfSelf af 12) = 1)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
    (hFfTag : ∀ u : Fin af → ℕ, Ff u ⟨2, by omega⟩ ≤ 1) :
    ∀ i, i ≤ fuel → RfBodyOK af B haf (rfLoopVals af haf Ff V₀ i) := by
  have hsW : s ≤ rfWindowBound s := Nat.left_le_pair _ _
  have h2sW : s + s ≤ rfWindowBound s := Nat.right_le_pair _ _
  have hstart : RfStateOK (V₀ (rfSelf af 9), V₀ (rfSelf af 10), V₀ (rfSelf af 11))
      (V₀ (rfSelf af 7)) := by
    refine ⟨?_, ?_, ?_⟩
    · show V₀ (rfSelf af 9) + V₀ (rfSelf af 10) ≤ 1
      rw [h9, h10]
    · show V₀ (rfSelf af 11) ≤ V₀ (rfSelf af 7)
      rw [h11]; omega
    · intro _
      show V₀ (rfSelf af 11) = 0
      exact h11
  have side : ∀ i, i ≤ fuel →
      Nat.pair (rfLoopVals af haf Ff V₀ i (rfSelf af 6))
        (rfLoopVals af haf Ff V₀ i (rfSelf af 7)) < B ∧
      rfLoopVals af haf Ff V₀ i (rfSelf af 9) ≤ 1 ∧
      rfLoopVals af haf Ff V₀ i (rfSelf af 7) + 1 < B ∧
      rfLoopVals af haf Ff V₀ i (rfSelf af 11)
        + rfLoopVals af haf Ff V₀ i (rfSelf af 7) < B ∧
      rfLoopVals af haf Ff V₀ i (rfSelf af 10) + 1 < B := by
    intro i hi
    obtain ⟨e6, e7, e8, e12, etriple⟩ :=
      rfLoopVals_spec haf cf Ff hFf V₀ h12 i
    have hok := rfIter_ok cf (V₀ (rfSelf af 6)) i
      (V₀ (rfSelf af 9), V₀ (rfSelf af 10), V₀ (rfSelf af 11))
      (V₀ (rfSelf af 8)) (V₀ (rfSelf af 7)) hstart
    have e9 : rfLoopVals af haf Ff V₀ i (rfSelf af 9)
        = (rfIter cf (V₀ (rfSelf af 6))
            (V₀ (rfSelf af 9), V₀ (rfSelf af 10), V₀ (rfSelf af 11))
            (V₀ (rfSelf af 8)) (V₀ (rfSelf af 7)) i).1 :=
      congrArg (fun p : ℕ × ℕ × ℕ => p.1) etriple
    have e10 : rfLoopVals af haf Ff V₀ i (rfSelf af 10)
        = (rfIter cf (V₀ (rfSelf af 6))
            (V₀ (rfSelf af 9), V₀ (rfSelf af 10), V₀ (rfSelf af 11))
            (V₀ (rfSelf af 8)) (V₀ (rfSelf af 7)) i).2.1 :=
      congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) etriple
    have e11 : rfLoopVals af haf Ff V₀ i (rfSelf af 11)
        = (rfIter cf (V₀ (rfSelf af 6))
            (V₀ (rfSelf af 9), V₀ (rfSelf af 10), V₀ (rfSelf af 11))
            (V₀ (rfSelf af 8)) (V₀ (rfSelf af 7)) i).2.2 :=
      congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) etriple
    obtain ⟨k1, k2, -⟩ := hok
    have hb : V₀ (rfSelf af 7) + i ≤ s + s := by rw [h7]; omega
    have hm : rfLoopVals af haf Ff V₀ i (rfSelf af 7) ≤ s + s := by
      rw [e7]; omega
    have hr : rfLoopVals af haf Ff V₀ i (rfSelf af 11) ≤ s + s := by
      rw [e11]; omega
    refine ⟨?_, by rw [e9]; omega, by omega, by omega, by rw [e10]; omega⟩
    calc Nat.pair (rfLoopVals af haf Ff V₀ i (rfSelf af 6))
            (rfLoopVals af haf Ff V₀ i (rfSelf af 7))
        ≤ Nat.pair s (s + s) := natPair_mono (by rw [e6, h6]; exact has) hm
      _ = rfWindowBound s := rfl
      _ < B := by omega
  intro i
  induction i with
  | zero =>
      intro _
      obtain ⟨sp, s9, s7, s11, s10⟩ := side 0 (Nat.zero_le _)
      exact ⟨fun k => hV₀ k, sp, s9, s7, s11, s10⟩
  | succ k ih =>
      intro hk
      obtain ⟨b, op, o9, o7, o11, o10⟩ := ih (by omega)
      obtain ⟨sp, s9, s7, s11, s10⟩ := side (k + 1) hk
      refine ⟨?_, sp, s9, s7, s11, s10⟩
      rw [rfLoopVals_succ]
      exact rfBodyVals_lt haf Ff _ B hB2 b op o9 o7 o11 o10 hFfB hFfTag

end RfindLoopBound

end LogicalInduction.EvalnCompiler
