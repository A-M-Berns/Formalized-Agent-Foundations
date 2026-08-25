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
import LogicalInduction.Construction.Machine.CodeSteps
import LogicalInduction.Construction.Machine.EvalnCompiler

namespace LogicalInduction.EvalnCompiler

open Nat.Partrec (Code)
open Complexity Complexity.TM

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
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) →
      u ⟨0, by omega⟩ ≤ s + precWindowBound cf cg s →
      u ⟨1, by omega⟩ ≤ s + precWindowBound cf cg s → ∀ k, Fg u k < B)
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
      -- the child's incoming vector at this level is bounded, and its input and fuel
      -- registers are inside the window, so the conditional hypothesis applies
      obtain ⟨e6, e9, e12, e10, e11⟩ := key k (by omega)
      have hpre := precBodyPre_lt haf hag (precLoopVals af ag haf hag Fg V₀ k) B hB2 b
        o9 o12 op1 op2
      have hs1 : 1 ≤ s := by omega
      have hchild0 :
          precChildIn af ag haf hag (precLoopVals af ag haf hag Fg V₀ k) ⟨0, by omega⟩
            ≤ s + precWindowBound cf cg s := by
        rw [precChildIn_zero, e6, e9, ]
        refine le_trans ?_ (Nat.le_add_left _ _)
        calc Nat.pair a (Nat.pair k
              (precLoopVals af ag haf hag Fg V₀ k (precSelf af ag 11)))
            ≤ Nat.pair s (Nat.pair s
                (max (codeEvalBound cf s) (codeEvalBound cg s))) :=
              natPair_mono has (natPair_mono (by omega) e11)
          _ = precWindowBound cf cg s := rfl
      have hchild1 :
          precChildIn af ag haf hag (precLoopVals af ag haf hag Fg V₀ k) ⟨1, by omega⟩
            ≤ s + precWindowBound cf cg s := by
        rw [precChildIn_one, e12]
        have : s ≤ precWindowBound cf cg s := hsW
        omega
      rw [precLoopVals_succ]
      exact precBodyVals_lt haf hag Fg _ B hB2 b o10 o9 o12 op1 op2
        (hFgB _ (fun k' => hpre (precRightSub af ag k')) hchild0 hchild1) hFgTag

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
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) →
      u ⟨0, by omega⟩ ≤ s + rfWindowBound s →
      u ⟨1, by omega⟩ ≤ s + rfWindowBound s → ∀ k, Ff u k < B)
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
      -- the child's incoming vector at this level: bounded, with input and fuel inside
      -- the window
      have hpre := rfPhaseAPre_lt haf (rfLoopVals af haf Ff V₀ k) B hB2 b op
      have hchild0 : rfChildIn af haf (rfLoopVals af haf Ff V₀ k) ⟨0, by omega⟩
          ≤ s + rfWindowBound s := by
        rw [rfChildIn_zero]
        refine le_trans ?_ (Nat.le_add_left _ _)
        obtain ⟨e6, e7, -, -, -⟩ := rfLoopVals_spec haf cf Ff hFf V₀ h12 k
        have hb : V₀ (rfSelf af 7) + k ≤ s + s := by rw [h7]; omega
        calc Nat.pair (rfLoopVals af haf Ff V₀ k (rfSelf af 6))
              (rfLoopVals af haf Ff V₀ k (rfSelf af 7))
            ≤ Nat.pair s (s + s) :=
              natPair_mono (by rw [e6, h6]; exact has) (by rw [e7]; omega)
          _ = rfWindowBound s := rfl
      have hchild1 : rfChildIn af haf (rfLoopVals af haf Ff V₀ k) ⟨1, by omega⟩
          ≤ s + rfWindowBound s := by
        rw [rfChildIn_one]
        obtain ⟨-, -, e8, -, -⟩ := rfLoopVals_spec haf cf Ff hFf V₀ h12 k
        rw [e8, h8]
        omega
      rw [rfLoopVals_succ]
      exact rfBodyVals_lt haf Ff _ B hB2 b op o9 o7 o11 o10
        (hFfB _ (fun k' => hpre (rfSub af k')) hchild0 hchild1) hFfTag

end RfindLoopBound

/-! ## What a compiled node leaves in its answer registers

The tag is a flag and the value is bounded by `codeEvalBound` — both read off the
correctness theorem rather than the machine. -/

section AnswerBounds

lemma resultVal_le_codeEvalBound (c : Nat.Partrec.Code) (k n : ℕ) :
    resultVal (Nat.Partrec.Code.evaln k c n) ≤ codeEvalBound c k := by
  cases hv : Nat.Partrec.Code.evaln k c n with
  | none => simp
  | some x =>
      simp only [resultVal]
      exact codeEvaln_result_le c (by rw [hv]; rfl)

lemma codeVals_tag_le (c : Nat.Partrec.Code) (V : Fin (codeRegs c) → ℕ) :
    codeVals c V ⟨2, by have := codeRegs_ge c; omega⟩ ≤ 1 := by
  rw [(codeVals_encodes c V).1]
  exact resultTag_le_one _

lemma codeVals_value_le (c : Nat.Partrec.Code) (V : Fin (codeRegs c) → ℕ) :
    codeVals c V ⟨3, by have := codeRegs_ge c; omega⟩
      ≤ codeEvalBound c (V ⟨1, by have := codeRegs_ge c; omega⟩) := by
  rw [(codeVals_encodes c V).2]
  exact resultVal_le_codeEvalBound _ _ _

end AnswerBounds

/-! ## The two looping constructors' thirty-three-wide blocks -/

section BlockBounds
variable {af ag : ℕ}

lemma precBlockVals_lt (haf : 16 ≤ af) (hag : 16 ≤ ag)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (v : Fin (33 + af + ag) → ℕ) (B : ℕ) (hv : ∀ k, v k < B)
    (hinner : ∀ k,
      precVals af ag haf hag Ff Fg (fun k => v (precMain af ag k)) k < B)
    (hm : precSetupVals af ag haf hag Ff (fun k => v (precMain af ag k))
      (precSelf af ag 7) < B) :
    ∀ k, precBlockVals af ag haf hag Ff Fg v k < B := by
  intro k
  simp only [precBlockVals, Function.update_apply]
  split_ifs with h
  · exact hm
  · by_cases hk : ∃ j, precMain af ag j = k
    · obtain ⟨j, rfl⟩ := hk
      rw [writeWindow_apply]
      exact hinner j
    · rw [writeWindow_of_ne _ _ _ (fun j e => hk ⟨j, e⟩)]
      exact hv k

lemma rfBlockVals_lt (haf : 16 ≤ af) (Ff : (Fin af → ℕ) → Fin af → ℕ)
    (v : Fin (33 + af) → ℕ) (B : ℕ) (hv : ∀ k, v k < B)
    (hinner : ∀ k, rfindVals af haf Ff (fun k => v (rfMain af k)) k < B)
    (ht : rfSetupVals af haf (fun k => v (rfMain af k)) (rfSelf af 1) < B) :
    ∀ k, rfBlockVals af haf Ff v k < B := by
  intro k
  simp only [rfBlockVals, Function.update_apply]
  split_ifs with h
  · exact ht
  · by_cases hk : ∃ j, rfMain af j = k
    · obtain ⟨j, rfl⟩ := hk
      rw [writeWindow_apply]
      exact hinner j
    · rw [writeWindow_of_ne _ _ _ (fun j e => hk ⟨j, e⟩)]
      exact hv k

end BlockBounds

/-! ## The two looping constructors keep every register inside the bound -/

section NodeBounds
variable {af ag : ℕ}

lemma precVals_lt (haf : 16 ≤ af) (hag : 16 ≤ ag) (cf cg : Nat.Partrec.Code)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (Fg : (Fin ag → ℕ) → Fin ag → ℕ)
    (hFf : ChildEncodes af haf cf Ff) (hFg : ChildEncodes ag hag cg Fg)
    (V : Fin (32 + af + ag) → ℕ) (s B : ℕ)
    (hB2 : 2 ≤ B) (hV : ∀ k, V k < B)
    (h0 : V (precSelf af ag 0) ≤ s) (h1 : V (precSelf af ag 1) ≤ s)
    (hWB : precWindowBound cf cg s + 2 ≤ B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) →
      u ⟨0, by omega⟩ ≤ s → u ⟨1, by omega⟩ ≤ s → ∀ k, Ff u k < B)
    (hFgB : ∀ u : Fin ag → ℕ, (∀ k, u k < B) →
      u ⟨0, by omega⟩ ≤ s + precWindowBound cf cg s →
      u ⟨1, by omega⟩ ≤ s + precWindowBound cf cg s → ∀ k, Fg u k < B)
    (hFgTag : ∀ u : Fin ag → ℕ, Fg u ⟨2, by omega⟩ ≤ 1) :
    ∀ k, precVals af ag haf hag Ff Fg V k < B := by
  -- the base child's incoming vector
  have hpre := precSetupPre_lt haf hag V B hV
  have hb0 : precBaseIn af ag haf hag V ⟨0, by omega⟩ ≤ s := by
    rw [precBaseIn_zero]
    exact le_trans (Nat.unpair_left_le _) h0
  have hb1 : precBaseIn af ag haf hag V ⟨1, by omega⟩ ≤ s := by
    rw [precBaseIn_one]; omega
  have hFfB' : ∀ k, Ff (precBaseIn af ag haf hag V) k < B :=
    hFfB _ (fun k => hpre (precLeftSub af ag k)) hb0 hb1
  have hS := precSetupVals_lt haf hag Ff V B hV hFfB'
  -- the loop
  have hm : (Nat.unpair (V (precSelf af ag 0))).2 ≤ s :=
    le_trans (Nat.unpair_right_le _) h0
  have hOK := precLoopVals_ok haf hag cf cg Fg hFg (precSetupVals af ag haf hag Ff V)
    (Nat.unpair (V (precSelf af ag 0))).1
    (V (precSelf af ag 1) - (Nat.unpair (V (precSelf af ag 0))).2)
    (Nat.unpair (V (precSelf af ag 0))).2 s B hB2 hm (by omega)
    (le_trans (Nat.unpair_left_le _) h0) hWB hS
    (precSetupVals_a haf hag Ff V) (precSetupVals_j haf hag Ff V)
    (precSetupVals_curFuel haf hag Ff V)
    (by
      rw [precSetupVals_alive]
      have h := (hFf (precBaseIn af ag haf hag V)).1
      rw [precBaseIn_zero, precBaseIn_one] at h
      exact h)
    (by
      rw [precSetupVals_acc]
      have h := (hFf (precBaseIn af ag haf hag V)).2
      rw [precBaseIn_zero, precBaseIn_one] at h
      exact h)
    hFgB hFgTag
  obtain ⟨hLb, hLalive, -, -, -, -⟩ := hOK _ le_rfl
  intro k
  rw [precVals, precSetupVals_m]
  exact precFinishVals_lt haf hag _ B hB2 hLb hLalive k

lemma rfindVals_lt {af : ℕ} (haf : 16 ≤ af) (cf : Nat.Partrec.Code)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (hFf : ChildEncodes af haf cf Ff)
    (V : Fin (32 + af) → ℕ) (s B : ℕ)
    (hB2 : 2 ≤ B) (hV : ∀ k, V k < B)
    (h0 : V (rfSelf af 0) ≤ s) (h1 : V (rfSelf af 1) ≤ s)
    (h2W : 2 * rfWindowBound s + 3 ≤ B)
    (hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) →
      u ⟨0, by omega⟩ ≤ s + rfWindowBound s →
      u ⟨1, by omega⟩ ≤ s + rfWindowBound s → ∀ k, Ff u k < B)
    (hFfTag : ∀ u : Fin af → ℕ, Ff u ⟨2, by omega⟩ ≤ 1) :
    ∀ k, rfindVals af haf Ff V k < B := by
  have hS := rfSetupVals_lt haf V B hB2 hV
  have hOK := rfLoopVals_ok haf cf Ff hFf (rfSetupVals af haf V)
    (Nat.unpair (V (rfSelf af 0))).1 (Nat.unpair (V (rfSelf af 0))).2
    (V (rfSelf af 1)) s B hB2 (le_trans (Nat.unpair_left_le _) h0)
    (le_trans (Nat.unpair_right_le _) h0) h1 h2W hS
    (rfSetupVals_a haf V) (rfSetupVals_m haf V) (rfSetupVals_fuel haf V)
    (rfSetupVals_search haf V) (rfSetupVals_found haf V) (rfSetupVals_result haf V)
    (rfSetupVals_one haf V) hFfB hFfTag
  obtain ⟨hLb, -, -, -, -, -⟩ := hOK _ le_rfl
  intro k
  rw [rfindVals, rfSetupVals_count]
  exact rfFinishVals_lt _ B hLb k

end NodeBounds

/-! ## The compiled register vector stays inside the bound

The structural companion to `codeVals_encodes`: a single ambient bound `B` dominating
`codeRegBound c s`, with each child using its own size parameter while sharing `B`. -/

section CodeValsBound

lemma codeVals_lt : ∀ (c : Nat.Partrec.Code) (s B : ℕ) (V : Fin (codeRegs c) → ℕ),
    codeRegBound c s ≤ B → (∀ k, V k < B) →
    V (codeLocal c 0) ≤ s → V (codeLocal c 1) ≤ s →
    ∀ k, codeVals c V k < B
  | .zero, s, B, V, hB, hV, _, _ => by
      simp only [codeRegBound] at hB
      exact zeroVals_lt V B (by omega) hV
  | .succ, s, B, V, hB, hV, h0, _ => by
      simp only [codeRegBound] at hB
      refine succVals_lt V B (by omega) hV ?_
      show V (codeLocal Nat.Partrec.Code.succ 0) + 1 < B
      omega
  | .left, s, B, V, hB, hV, _, _ => by
      simp only [codeRegBound] at hB
      exact projVals_lt V 0 B (by omega) hV
  | .right, s, B, V, hB, hV, _, _ => by
      simp only [codeRegBound] at hB
      exact projVals_lt V 1 B (by omega) hV
  | .pair cf cg, s, B, V, hB, hV, h0, h1 => by
      simp only [codeRegBound] at hB
      have hgef := le_codeRegBound cf s
      have hB2 : 2 ≤ B := by omega
      have hBf : codeRegBound cf s ≤ B := by omega
      have hBg : codeRegBound cg s ≤ B := by omega
      have hpr : Nat.pair (codeEvalBound cf s) (codeEvalBound cg s) < B := by omega
      have h0' : V (selfW (codeRegs cf) (codeRegs cg) 0) ≤ s := h0
      have h1' : V (selfW (codeRegs cf) (codeRegs cg) 1) ≤ s := h1
      -- the first child
      have hLb : ∀ k, pairLeftIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) V k < B := by
        intro k
        simp only [pairLeftIn, Function.update_apply]
        split_ifs <;> exact hV _
      have hFfB := codeVals_lt cf s B (pairLeftIn (codeRegs cf) (codeRegs cg)
        (codeRegs_ge cf) V) hBf hLb
        (by show pairLeftIn _ _ _ V ⟨0, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩ ≤ s
            rw [pairLeftIn_zero]; exact h0')
        (by show pairLeftIn _ _ _ V ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩ ≤ s
            rw [pairLeftIn_one]; exact h1')
      -- the second child
      have hRb : ∀ k, pairRightIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) V k < B := by
        intro k
        simp only [pairRightIn, Function.update_apply]
        split_ifs
        · exact hV _
        · exact hV _
        · refine writeWindow_bounded _ _ _ B (fun j => ?_) (fun j => hFfB j) _
          simp only [Function.update_apply]; split_ifs <;> exact hV _
      have hFgB := codeVals_lt cg s B (pairRightIn (codeRegs cf) (codeRegs cg)
        (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) V) hBg hRb
        (by show pairRightIn _ _ _ _ _ V ⟨0, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cg)⟩ ≤ s
            rw [pairRightIn_zero]; exact h0')
        (by show pairRightIn _ _ _ _ _ V ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cg)⟩ ≤ s
            rw [pairRightIn_one]; exact h1')
      have hA := pairPhaseAVec_lt (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf)
        (codeVals cg) V B hV hFfB hFgB
      have htagF : pairPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
          (leftLoc (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) 2) ≤ 1 := by
        rw [pairPhaseAVec_leftLoc]
        exact codeVals_tag_le cf _
      have htagG : pairPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
          (rightLoc (codeRegs cf) (codeRegs cg) (codeRegs_ge cg) 2) ≤ 1 := by
        rw [pairPhaseAVec_rightLoc]
        exact codeVals_tag_le cg _
      have hvF : pairPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
          (leftLoc (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) 3)
          ≤ codeEvalBound cf s := by
        rw [pairPhaseAVec_leftLoc]
        refine le_trans (codeVals_value_le cf _) (codeEvalBound_mono cf ?_)
        show pairLeftIn _ _ _ V ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩ ≤ s
        rw [pairLeftIn_one]; exact h1'
      have hvG : pairPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
          (rightLoc (codeRegs cf) (codeRegs cg) (codeRegs_ge cg) 3)
          ≤ codeEvalBound cg s := by
        rw [pairPhaseAVec_rightLoc]
        refine le_trans (codeVals_value_le cg _) (codeEvalBound_mono cg ?_)
        show pairRightIn _ _ _ _ _ V ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cg)⟩ ≤ s
        rw [pairRightIn_one]; exact h1'
      exact pairPhaseBVec_lt (codeRegs_ge cf) (codeRegs_ge cg) _ B hB2 hA
        (lt_of_le_of_lt (natPair_mono hvF hvG) hpr) htagF htagG
  | .comp cf cg, s, B, V, hB, hV, h0, h1 => by
      simp only [codeRegBound] at hB
      have hgef := le_codeRegBound cf (s + codeEvalBound cg s)
      have hgeg := le_codeRegBound cg s
      have hB2 : 2 ≤ B := by omega
      have hBf : codeRegBound cf (s + codeEvalBound cg s) ≤ B := by omega
      have hBg : codeRegBound cg s ≤ B := by omega
      have h0' : V (selfW (codeRegs cf) (codeRegs cg) 0) ≤ s := h0
      have h1' : V (selfW (codeRegs cf) (codeRegs cg) 1) ≤ s := h1
      have hRb : ∀ k, compRightIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cg) V k < B := by
        intro k
        simp only [compRightIn, Function.update_apply]
        split_ifs <;> exact hV _
      have hFgB := codeVals_lt cg s B (compRightIn (codeRegs cf) (codeRegs cg)
        (codeRegs_ge cg) V) hBg hRb
        (by show compRightIn _ _ _ V ⟨0, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cg)⟩ ≤ s
            rw [compRightIn_zero]; exact h0')
        (by show compRightIn _ _ _ V ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cg)⟩ ≤ s
            rw [compRightIn_one]; exact h1')
      have hvG : codeVals cg (compRightIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cg) V)
          ⟨3, by have := codeRegs_ge cg; omega⟩ ≤ codeEvalBound cg s := by
        refine le_trans (codeVals_value_le cg _) (codeEvalBound_mono cg ?_)
        show compRightIn _ _ _ V ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cg)⟩ ≤ s
        rw [compRightIn_one]; exact h1'
      have hLb : ∀ k, compLeftIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cg) V k < B := by
        intro k
        simp only [compLeftIn, Function.update_apply]
        split_ifs
        · exact hV _
        · refine writeWindow_bounded _ _ _ B (fun j => ?_) (fun j => hFgB j) _
          simp only [Function.update_apply]; split_ifs <;> exact hV _
        · refine writeWindow_bounded _ _ _ B (fun j => ?_) (fun j => hFgB j) _
          simp only [Function.update_apply]; split_ifs <;> exact hV _
      have hFfB := codeVals_lt cf (s + codeEvalBound cg s) B
        (compLeftIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
          (codeVals cg) V) hBf hLb
        (by show compLeftIn _ _ _ _ _ V ⟨0, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩ ≤ s + codeEvalBound cg s
            rw [compLeftIn_zero]
            exact le_trans hvG (Nat.le_add_left _ _))
        (by show compLeftIn _ _ _ _ _ V ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩ ≤ s + codeEvalBound cg s
            rw [compLeftIn_one]
            exact le_trans h1' (Nat.le_add_right _ _))
      have hA := compPhaseAVec_lt (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf)
        (codeVals cg) V B hV hFfB hFgB
      have htagF : compPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
          (leftLoc (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) 2) ≤ 1 := by
        rw [compPhaseAVec_leftLoc]
        exact codeVals_tag_le cf _
      have htagG : compPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
          (rightLoc (codeRegs cf) (codeRegs cg) (codeRegs_ge cg) 2) ≤ 1 := by
        rw [compPhaseAVec_rightLoc]
        exact codeVals_tag_le cg _
      exact compPhaseBVec_lt (codeRegs_ge cf) (codeRegs_ge cg) _ B hB2 hA htagF htagG
  | .prec cf cg, s, B, V, hB, hV, h0, h1 => by
      simp only [codeRegBound] at hB
      have hgef := le_codeRegBound cf s
      have hgeg := le_codeRegBound cg (s + precWindowBound cf cg s)
      have hB2 : 2 ≤ B := by omega
      have hWB : precWindowBound cf cg s + 2 ≤ B := by omega
      have hBf : codeRegBound cf s ≤ B := by omega
      have hBg : codeRegBound cg (s + precWindowBound cf cg s) ≤ B := by omega
      have hV'b : ∀ k, (fun k => V (precMain (codeRegs cf) (codeRegs cg) k)) k < B :=
        fun k => hV _
      have h0' : V (precMain (codeRegs cf) (codeRegs cg)
          (precSelf (codeRegs cf) (codeRegs cg) 0)) ≤ s := h0
      have h1' : V (precMain (codeRegs cf) (codeRegs cg)
          (precSelf (codeRegs cf) (codeRegs cg) 1)) ≤ s := h1
      have hbase : ∀ k, codeVals cf (precBaseIn (codeRegs cf) (codeRegs cg)
          (codeRegs_ge cf) (codeRegs_ge cg)
          (fun k => V (precMain (codeRegs cf) (codeRegs cg) k))) k < B := by
        refine codeVals_lt cf s B _ hBf (fun k => ?_) ?_ ?_
        · exact precSetupPre_lt (codeRegs_ge cf) (codeRegs_ge cg) _ B hV'b _
        · show precBaseIn _ _ _ _ _
              ⟨0, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩ ≤ s
          rw [precBaseIn_zero]
          exact le_trans (Nat.unpair_left_le _) h0'
        · show precBaseIn _ _ _ _ _
              ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩ ≤ s
          rw [precBaseIn_one]
          omega
      have hinner : ∀ k,
          precVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
            (codeVals cf) (codeVals cg)
            (fun k => V (precMain (codeRegs cf) (codeRegs cg) k)) k < B :=
        precVals_lt (codeRegs_ge cf) (codeRegs_ge cg) cf cg (codeVals cf)
          (codeVals cg) (codeVals_encodes cf) (codeVals_encodes cg) _ s B hB2
          hV'b h0' h1' hWB
          (fun u hu hu0 hu1 => codeVals_lt cf s B u hBf hu hu0 hu1)
          (fun u hu hu0 hu1 => codeVals_lt cg (s + precWindowBound cf cg s) B u hBg
            hu hu0 hu1)
          (fun u => codeVals_tag_le cg u)
      exact precBlockVals_lt (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf)
        (codeVals cg) V B hV hinner
        (precSetupVals_lt (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) _ B hV'b
          hbase _)
  | .rfind' cf, s, B, V, hB, hV, h0, h1 => by
      simp only [codeRegBound] at hB
      have hgef := le_codeRegBound cf (s + rfWindowBound s)
      have hB2 : 2 ≤ B := by omega
      have hW : 2 * rfWindowBound s + 3 ≤ B := by
        have h2 : rfWindowBound s ≤ s + rfWindowBound s := Nat.le_add_left _ _
        omega
      have hBf : codeRegBound cf (s + rfWindowBound s) ≤ B := by omega
      have hV'b : ∀ k, (fun k => V (rfMain (codeRegs cf) k)) k < B := fun k => hV _
      have h0' : V (rfMain (codeRegs cf) (rfSelf (codeRegs cf) 0)) ≤ s := h0
      have h1' : V (rfMain (codeRegs cf) (rfSelf (codeRegs cf) 1)) ≤ s := h1
      have hinner : ∀ k,
          rfindVals (codeRegs cf) (codeRegs_ge cf) (codeVals cf)
            (fun k => V (rfMain (codeRegs cf) k)) k < B :=
        rfindVals_lt (codeRegs_ge cf) cf (codeVals cf) (codeVals_encodes cf) _
          s B hB2 hV'b h0' h1' hW
          (fun u hu hu0 hu1 => codeVals_lt cf (s + rfWindowBound s) B u hBf hu hu0 hu1)
          (fun u => codeVals_tag_le cf u)
      exact rfBlockVals_lt (codeRegs_ge cf) (codeVals cf) V B hV hinner
        (rfSetupVals_lt (codeRegs_ge cf) _ B hB2 hV'b _)

end CodeValsBound

/-! ## A concrete step bound for a compiled code

`codeMachineTime c s A` mirrors the per-constructor Hoare bounds, with `A` the common
arithmetic cost `evalnArithmeticCost B` and `s` a bound on the node's input and fuel. The
two looping constructors run at most `s` levels — the counter is bounded by the input and
the fuel respectively — so `s` stands in for the data-dependent level count. -/

section MachineTime

/-- The step bound a compiled node meets, given a common arithmetic cost `A` and a size
    bound `s` on its input and fuel registers. -/
def codeMachineTime : Nat.Partrec.Code → ℕ → ℕ → ℕ
  | .zero, _, A => 3 * A + 2
  | .succ, _, A => 6 * A + 5
  | .left, _, A => 5 * A + 4
  | .right, _, A => 5 * A + 4
  | .pair cf cg, s, A =>
      14 * A + codeMachineTime cf s A + codeMachineTime cg s A + 15
  | .comp cf cg, s, A =>
      11 * A + codeMachineTime cf (s + codeEvalBound cg s) A
        + codeMachineTime cg s A + 12
  | .prec cf cg, s, A =>
      (12 * A + codeMachineTime cf s A + 12) + 1
        + (s * ((15 * A + codeMachineTime cg (s + precWindowBound cf cg s) A + 15) + 2)
          + (s + 2) + 1 + (5 * A + 4))
  | .rfind' cf, s, A =>
      (9 * A + 8) + 1
        + (s * ((22 * A + codeMachineTime cf (s + rfWindowBound s) A + 22) + 2)
          + (s + 2) + 1 + (2 * A + 1))

lemma codeMachineTime_mono_size (c : Nat.Partrec.Code) (A : ℕ) :
    Monotone (fun s => codeMachineTime c s A) := by
  induction c with
  | zero => exact monotone_const
  | succ => exact monotone_const
  | left => exact monotone_const
  | right => exact monotone_const
  | pair cf cg ihf ihg =>
      intro a b hab
      simp only [codeMachineTime]
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (le_refl _) (ihf hab))
        (ihg hab)) 15
  | comp cf cg ihf ihg =>
      intro a b hab
      simp only [codeMachineTime]
      exact Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (le_refl _)
          (ihf (Nat.add_le_add hab (codeEvalBound_mono cg hab)))) (ihg hab)) 12
  | prec cf cg ihf ihg =>
      intro a b hab
      simp only [codeMachineTime]
      have h1 : codeMachineTime cf a A ≤ codeMachineTime cf b A := ihf hab
      have h2 : codeMachineTime cg (a + precWindowBound cf cg a) A
          ≤ codeMachineTime cg (b + precWindowBound cf cg b) A :=
        ihg (Nat.add_le_add hab (precWindowBound_mono cf cg hab))
      have h3 : a * ((15 * A + codeMachineTime cg (a + precWindowBound cf cg a) A + 15) + 2)
          ≤ b * ((15 * A + codeMachineTime cg (b + precWindowBound cf cg b) A + 15) + 2) :=
        Nat.mul_le_mul hab (by omega)
      omega
  | rfind' cf ihf =>
      intro a b hab
      simp only [codeMachineTime]
      have h2 : codeMachineTime cf (a + rfWindowBound a) A
          ≤ codeMachineTime cf (b + rfWindowBound b) A :=
        ihf (Nat.add_le_add hab (rfWindowBound_mono hab))
      have h3 : a * ((22 * A + codeMachineTime cf (a + rfWindowBound a) A + 22) + 2)
          ≤ b * ((22 * A + codeMachineTime cf (b + rfWindowBound b) A + 22) + 2) :=
        Nat.mul_le_mul hab (by omega)
      omega

lemma codeMachineTime_mono_cost (c : Nat.Partrec.Code) (s : ℕ) :
    Monotone (fun A => codeMachineTime c s A) := by
  induction c generalizing s with
  | zero => intro a b hab; simp only [codeMachineTime]; omega
  | succ => intro a b hab; simp only [codeMachineTime]; omega
  | left => intro a b hab; simp only [codeMachineTime]; omega
  | right => intro a b hab; simp only [codeMachineTime]; omega
  | pair cf cg ihf ihg =>
      intro a b hab
      simp only [codeMachineTime]
      have h1 := ihf s hab
      have h2 := ihg s hab
      simp only at h1 h2
      omega
  | comp cf cg ihf ihg =>
      intro a b hab
      simp only [codeMachineTime]
      have h1 := ihf (s + codeEvalBound cg s) hab
      have h2 := ihg s hab
      simp only at h1 h2
      omega
  | prec cf cg ihf ihg =>
      intro a b hab
      simp only [codeMachineTime]
      have h1 := ihf s hab
      have h2 := ihg (s + precWindowBound cf cg s) hab
      simp only at h1 h2
      have h3 : s * ((15 * a + codeMachineTime cg (s + precWindowBound cf cg s) a + 15) + 2)
          ≤ s * ((15 * b + codeMachineTime cg (s + precWindowBound cf cg s) b + 15) + 2) :=
        Nat.mul_le_mul (le_refl _) (by omega)
      omega
  | rfind' cf ihf =>
      intro a b hab
      simp only [codeMachineTime]
      have h2 := ihf (s + rfWindowBound s) hab
      simp only at h2
      have h3 : s * ((22 * a + codeMachineTime cf (s + rfWindowBound s) a + 22) + 2)
          ≤ s * ((22 * b + codeMachineTime cf (s + rfWindowBound s) b + 22) + 2) :=
        Nat.mul_le_mul (le_refl _) (by omega)
      omega

end MachineTime

/-! ## The step bound is polynomial for each fixed code -/

section MachineTimePoly

lemma IsPolyBounded.const (c : ℕ) : IsPolyBounded (fun _ : ℕ => c) :=
  ⟨c, 0, fun _ => by simp⟩

lemma IsPolyBounded.const_mul {A : ℕ → ℕ} (h : IsPolyBounded A) (c : ℕ) :
    IsPolyBounded (fun n => c * A n) := by
  obtain ⟨a, k, hk⟩ := h
  refine ⟨c * a + c, k, fun n => ?_⟩
  calc c * A n ≤ c * (a * (n + 1) ^ k + a) := Nat.mul_le_mul_left c (hk n)
    _ = c * a * (n + 1) ^ k + c * a := by ring
    _ ≤ (c * a + c) * (n + 1) ^ k + (c * a + c) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (by omega)

lemma isPolyBounded_id : IsPolyBounded (fun n : ℕ => n) :=
  (IsPolyBounded.linear 0).of_le (fun _ => by omega)

lemma evalnArithmeticCost_poly : IsPolyBounded evalnArithmeticCost :=
  ⟨500, 4, fun n => by simp [evalnArithmeticCost]⟩

lemma evalnArithmeticCost_mono : Monotone evalnArithmeticCost := by
  intro a b hab
  simp only [evalnArithmeticCost]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)

/-- The common arithmetic cost at a fixed code's register bound: polynomial and monotone,
    which is everything the step bound's induction needs of it. -/
lemma arith_codeRegBound_poly (c : Nat.Partrec.Code) :
    IsPolyBounded (fun s => evalnArithmeticCost (codeRegBound c s)) :=
  evalnArithmeticCost_poly.comp (codeRegBound_poly c)

lemma arith_codeRegBound_mono (c : Nat.Partrec.Code) :
    Monotone (fun s => evalnArithmeticCost (codeRegBound c s)) :=
  evalnArithmeticCost_mono.comp (codeRegBound_mono c)

/-- **The step bound is polynomial in the size parameter, for each fixed code.** -/
lemma codeMachineTime_poly : ∀ (c : Nat.Partrec.Code) (A : ℕ → ℕ), IsPolyBounded A →
    Monotone A → IsPolyBounded (fun s => codeMachineTime c s (A s))
  | .zero, A, hA, _ => ((IsPolyBounded.const_mul hA 3).add' (IsPolyBounded.const 2)).of_le
      (fun s => by simp only [codeMachineTime]; omega)
  | .succ, A, hA, _ => ((IsPolyBounded.const_mul hA 6).add' (IsPolyBounded.const 5)).of_le
      (fun s => by simp only [codeMachineTime]; omega)
  | .left, A, hA, _ => ((IsPolyBounded.const_mul hA 5).add' (IsPolyBounded.const 4)).of_le
      (fun s => by simp only [codeMachineTime]; omega)
  | .right, A, hA, _ => ((IsPolyBounded.const_mul hA 5).add' (IsPolyBounded.const 4)).of_le
      (fun s => by simp only [codeMachineTime]; omega)
  | .pair cf cg, A, hA, hmA => by
      have hf := codeMachineTime_poly cf A hA hmA
      have hg := codeMachineTime_poly cg A hA hmA
      exact ((((IsPolyBounded.const_mul hA 14).add' hf).add' hg).add'
        (IsPolyBounded.const 15)).of_le (fun s => by simp only [codeMachineTime]; omega)
  | .comp cf cg, A, hA, hmA => by
      have hshift : IsPolyBounded (fun s => s + codeEvalBound cg s) :=
        isPolyBounded_id.add' (codeEvalBound_poly cg)
      have hf : IsPolyBounded
          (fun s => codeMachineTime cf (s + codeEvalBound cg s)
            (A (s + codeEvalBound cg s))) :=
        (codeMachineTime_poly cf A hA hmA).comp hshift
      have hg := codeMachineTime_poly cg A hA hmA
      refine ((((IsPolyBounded.const_mul hA 11).add' hf).add' hg).add'
        (IsPolyBounded.const 12)).of_le (fun s => ?_)
      simp only [codeMachineTime]
      have : codeMachineTime cf (s + codeEvalBound cg s) (A s)
          ≤ codeMachineTime cf (s + codeEvalBound cg s) (A (s + codeEvalBound cg s)) :=
        codeMachineTime_mono_cost cf _ (hmA (Nat.le_add_right _ _))
      omega
  | .prec cf cg, A, hA, hmA => by
      have hshift : IsPolyBounded (fun s => s + precWindowBound cf cg s) :=
        isPolyBounded_id.add' (precWindowBound_poly cf cg)
      have hf := codeMachineTime_poly cf A hA hmA
      have hg : IsPolyBounded
          (fun s => codeMachineTime cg (s + precWindowBound cf cg s)
            (A (s + precWindowBound cf cg s))) :=
        (codeMachineTime_poly cg A hA hmA).comp hshift
      have hloop : IsPolyBounded (fun s => s *
          ((15 * A (s + precWindowBound cf cg s)
            + codeMachineTime cg (s + precWindowBound cf cg s)
                (A (s + precWindowBound cf cg s)) + 15) + 2)) :=
        isPolyBounded_id.mul
          (((IsPolyBounded.const_mul (IsPolyBounded.comp hA hshift) 15).add' hg).add' (IsPolyBounded.const 17))
      refine ((((((IsPolyBounded.const_mul hA 12).add' hf).add' (IsPolyBounded.const 13)).add'
        hloop).add' isPolyBounded_id).add'
        ((IsPolyBounded.const_mul hA 5).add' (IsPolyBounded.const 7))).of_le (fun s => ?_)
      simp only [codeMachineTime]
      have hc : codeMachineTime cg (s + precWindowBound cf cg s) (A s)
          ≤ codeMachineTime cg (s + precWindowBound cf cg s)
              (A (s + precWindowBound cf cg s)) :=
        codeMachineTime_mono_cost cg _ (hmA (Nat.le_add_right _ _))
      have hA' : A s ≤ A (s + precWindowBound cf cg s) := hmA (Nat.le_add_right _ _)
      have hmul : s * ((15 * A s + codeMachineTime cg (s + precWindowBound cf cg s) (A s)
            + 15) + 2)
          ≤ s * ((15 * A (s + precWindowBound cf cg s)
            + codeMachineTime cg (s + precWindowBound cf cg s)
                (A (s + precWindowBound cf cg s)) + 15) + 2) :=
        Nat.mul_le_mul (le_refl _) (by omega)
      omega
  | .rfind' cf, A, hA, hmA => by
      have hshift : IsPolyBounded (fun s => s + rfWindowBound s) :=
        isPolyBounded_id.add' rfWindowBound_poly
      have hf : IsPolyBounded
          (fun s => codeMachineTime cf (s + rfWindowBound s) (A (s + rfWindowBound s))) :=
        (codeMachineTime_poly cf A hA hmA).comp hshift
      have hloop : IsPolyBounded (fun s => s *
          ((22 * A (s + rfWindowBound s)
            + codeMachineTime cf (s + rfWindowBound s) (A (s + rfWindowBound s))
              + 22) + 2)) :=
        isPolyBounded_id.mul
          (((IsPolyBounded.const_mul (IsPolyBounded.comp hA hshift) 22).add' hf).add' (IsPolyBounded.const 24))
      refine (((((IsPolyBounded.const_mul hA 9).add' (IsPolyBounded.const 9)).add' hloop).add'
        isPolyBounded_id).add'
        ((IsPolyBounded.const_mul hA 2).add' (IsPolyBounded.const 4))).of_le (fun s => ?_)
      simp only [codeMachineTime]
      have hc : codeMachineTime cf (s + rfWindowBound s) (A s)
          ≤ codeMachineTime cf (s + rfWindowBound s) (A (s + rfWindowBound s)) :=
        codeMachineTime_mono_cost cf _ (hmA (Nat.le_add_right _ _))
      have hA' : A s ≤ A (s + rfWindowBound s) := hmA (Nat.le_add_right _ _)
      have hmul : s * ((22 * A s + codeMachineTime cf (s + rfWindowBound s) (A s) + 22) + 2)
          ≤ s * ((22 * A (s + rfWindowBound s)
            + codeMachineTime cf (s + rfWindowBound s) (A (s + rfWindowBound s))
              + 22) + 2) :=
        Nat.mul_le_mul (le_refl _) (by omega)
      omega

/-- **The compiled machine's step bound is polynomial in the size parameter, for each
    fixed code.** -/
lemma codeMachineTime_arith_poly (c : Nat.Partrec.Code) :
    IsPolyBounded (fun s => codeMachineTime c s (evalnArithmeticCost (codeRegBound c s))) :=
  codeMachineTime_poly c _ (arith_codeRegBound_poly c) (arith_codeRegBound_mono c)

end MachineTimePoly

/-! ## The compiled machine meets its step bound

The structural timing theorem. The two looping constructors are split off into their own
lemmas: their block is thirty-three wide, so the statement has to be phrased in the
`33 + af + ag` world the loop counter lives in — `rw` will not see through `codeRegs` at
the transparency it matches at — and the induction then reaches them by definitional
unfolding. -/

section MachineTimeHoare
variable {af ag : ℕ}

lemma precChildIn_size_le (haf : 16 ≤ af) (hag : 16 ≤ ag) (cf cg : Nat.Partrec.Code)
    (Fg : (Fin ag → ℕ) → Fin ag → ℕ) (hFg : ChildEncodes ag hag cg Fg)
    (V₀ : Fin (32 + af + ag) → ℕ) (a f₀ m s : ℕ)
    (hms : m ≤ s) (hfs : f₀ + m ≤ s) (has : a ≤ s)
    (h6 : V₀ (precSelf af ag 6) = a) (h9 : V₀ (precSelf af ag 9) = 0)
    (h12 : V₀ (precSelf af ag 12) = f₀)
    (h10 : V₀ (precSelf af ag 10) = resultTag (Nat.Partrec.Code.evaln f₀ cf a))
    (h11 : V₀ (precSelf af ag 11) = resultVal (Nat.Partrec.Code.evaln f₀ cf a)) :
    ∀ i, i < m →
      precChildIn af ag haf hag (precLoopVals af ag haf hag Fg V₀ i) ⟨0, by omega⟩
          ≤ s + precWindowBound cf cg s ∧
      precChildIn af ag haf hag (precLoopVals af ag haf hag Fg V₀ i) ⟨1, by omega⟩
          ≤ s + precWindowBound cf cg s := by
  intro i hi
  have hsW : s ≤ precWindowBound cf cg s := Nat.left_le_pair _ _
  obtain ⟨e6, e9, e12, -, e11⟩ :=
    precLoopVals_spec haf hag cf cg Fg hFg V₀ a f₀ h6 h9 h12 h10 h11 i
  have e11' : precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 11)
      ≤ max (codeEvalBound cf s) (codeEvalBound cg s) := by
    rw [e11]; exact precRunG_val_le cf cg a f₀ s i (by omega)
  constructor
  · rw [precChildIn_zero, e6, e9]
    refine le_trans ?_ (Nat.le_add_left _ _)
    calc Nat.pair a (Nat.pair i
          (precLoopVals af ag haf hag Fg V₀ i (precSelf af ag 11)))
        ≤ Nat.pair s (Nat.pair s (max (codeEvalBound cf s) (codeEvalBound cg s))) :=
          natPair_mono has (natPair_mono (by omega) e11')
      _ = precWindowBound cf cg s := rfl
  · rw [precChildIn_one, e12]
    omega

lemma rfChildIn_size_le (haf : 16 ≤ af) (cf : Nat.Partrec.Code)
    (Ff : (Fin af → ℕ) → Fin af → ℕ) (hFf : ChildEncodes af haf cf Ff)
    (V₀ : Fin (32 + af) → ℕ) (a m₀ fuel s : ℕ)
    (has : a ≤ s) (hm₀ : m₀ ≤ s) (hfuel : fuel ≤ s)
    (h6 : V₀ (rfSelf af 6) = a) (h7 : V₀ (rfSelf af 7) = m₀)
    (h8 : V₀ (rfSelf af 8) = fuel) (h12 : V₀ (rfSelf af 12) = 1) :
    ∀ i, i ≤ fuel →
      rfChildIn af haf (rfLoopVals af haf Ff V₀ i) ⟨0, by omega⟩ ≤ s + rfWindowBound s ∧
      rfChildIn af haf (rfLoopVals af haf Ff V₀ i) ⟨1, by omega⟩ ≤ s + rfWindowBound s := by
  intro i hi
  obtain ⟨e6, e7, e8, -, -⟩ := rfLoopVals_spec haf cf Ff hFf V₀ h12 i
  constructor
  · rw [rfChildIn_zero]
    refine le_trans ?_ (Nat.le_add_left _ _)
    calc Nat.pair (rfLoopVals af haf Ff V₀ i (rfSelf af 6))
          (rfLoopVals af haf Ff V₀ i (rfSelf af 7))
        ≤ Nat.pair s (s + s) :=
          natPair_mono (by rw [e6, h6]; exact has) (by rw [e7, h7]; omega)
      _ = rfWindowBound s := rfl
  · rw [rfChildIn_one, e8, h8]
    omega

lemma precBlock_hoareTime (cf cg : Nat.Partrec.Code) {n : ℕ}
    (R : Regs (33 + codeRegs cf + codeRegs cg) n) (Mf Mg : TM n)
    (V : Fin (33 + codeRegs cf + codeRegs cg) → ℕ) (s B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (hB : codeRegBound (cf.prec cg) s ≤ B) (hV : ∀ k, V k < B)
    (h0 : V (precMain (codeRegs cf) (codeRegs cg)
      (precSelf (codeRegs cf) (codeRegs cg) 0)) ≤ s)
    (h1 : V (precMain (codeRegs cf) (codeRegs cg)
      (precSelf (codeRegs cf) (codeRegs cg) 1)) ≤ s)
    (hMf : ∀ (V₂ : Fin (codeRegs cf) → ℕ) (s₂ : ℕ) (Wb : Fin n → Tape),
      (∀ i, Parked (Wb i)) → codeRegBound cf s₂ ≤ B → (∀ k, V₂ k < B) →
      V₂ (codeLocal cf 0) ≤ s₂ → V₂ (codeLocal cf 1) ≤ s₂ →
      Mf.HoareTime
        (EmitPred inp₀ (regsWork ((precLeftSub (codeRegs cf) (codeRegs cg)).trans
          ((precMain (codeRegs cf) (codeRegs cg)).trans R)) Wb V₂) ys)
        (EmitPred inp₀ (regsWork ((precLeftSub (codeRegs cf) (codeRegs cg)).trans
          ((precMain (codeRegs cf) (codeRegs cg)).trans R)) Wb (codeVals cf V₂)) ys)
        (codeMachineTime cf s₂ (evalnArithmeticCost B)))
    (hMg : ∀ (V₂ : Fin (codeRegs cg) → ℕ) (s₂ : ℕ) (Wb : Fin n → Tape),
      (∀ i, Parked (Wb i)) → codeRegBound cg s₂ ≤ B → (∀ k, V₂ k < B) →
      V₂ (codeLocal cg 0) ≤ s₂ → V₂ (codeLocal cg 1) ≤ s₂ →
      Mg.HoareTime
        (EmitPred inp₀ (regsWork ((precRightSub (codeRegs cf) (codeRegs cg)).trans
          ((precMain (codeRegs cf) (codeRegs cg)).trans R)) Wb V₂) ys)
        (EmitPred inp₀ (regsWork ((precRightSub (codeRegs cf) (codeRegs cg)).trans
          ((precMain (codeRegs cf) (codeRegs cg)).trans R)) Wb (codeVals cg V₂)) ys)
        (codeMachineTime cg s₂ (evalnArithmeticCost B))) :
    (precTM (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
      ((precMain (codeRegs cf) (codeRegs cg)).trans R)
      (R (precLoopIdx (codeRegs cf) (codeRegs cg))) Mf Mg).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀ (regsWork R w₀ (precBlockVals (codeRegs cf) (codeRegs cg)
        (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) (codeVals cg) V)) ys)
      (codeMachineTime (cf.prec cg) s (evalnArithmeticCost B)) := by
  simp only [codeRegBound] at hB
  have hgef := le_codeRegBound cf s
  have hgeg := le_codeRegBound cg (s + precWindowBound cf cg s)
  have hB2 : 2 ≤ B := by omega
  have hWB : precWindowBound cf cg s + 2 ≤ B := by omega
  have hBf : codeRegBound cf s ≤ B := by omega
  have hBg : codeRegBound cg (s + precWindowBound cf cg s) ≤ B := by omega
  -- the block's own view of the register file
  set V' : Fin (32 + codeRegs cf + codeRegs cg) → ℕ :=
    fun k => V (precMain (codeRegs cf) (codeRegs cg) k) with hV'def
  have hV'b : ∀ k, V' k < B := fun k => hV _
  have h0' : V' (precSelf (codeRegs cf) (codeRegs cg) 0) ≤ s := h0
  have h1' : V' (precSelf (codeRegs cf) (codeRegs cg) 1) ≤ s := h1
  have hl : ∀ k, ((precMain (codeRegs cf) (codeRegs cg)).trans R) k
      ≠ R (precLoopIdx (codeRegs cf) (codeRegs cg)) :=
    fun k h => precMain_ne_loopIdx k (R.injective h)
  set l := R (precLoopIdx (codeRegs cf) (codeRegs cg)) with hldef
  set w₁ := Function.update w₀ l (regTape (V (precLoopIdx (codeRegs cf) (codeRegs cg))))
    with hw₁
  have hpark₁ : ∀ i, Parked (w₁ i) := by
    intro i; rw [hw₁]
    by_cases hi : i = l
    · subst hi; rw [Function.update_self]; exact parked_regTape _
    · rw [Function.update_of_ne hi]; exact hpark i
  -- the base child
  have hbaseb : ∀ k, precBaseIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
      (codeRegs_ge cg) V' k < B :=
    fun k => precSetupPre_lt (codeRegs_ge cf) (codeRegs_ge cg) V' B hV'b _
  have hbase0 : precBaseIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
      V' ⟨0, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩ ≤ s := by
    rw [precBaseIn_zero]; exact le_trans (Nat.unpair_left_le _) h0'
  have hbase1 : precBaseIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
      V' ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩ ≤ s := by
    rw [precBaseIn_one]; omega
  have hFfB := codeVals_lt cf s B _ hBf hbaseb hbase0 hbase1
  -- the loop's numeric data
  have hm : (Nat.unpair (V' (precSelf (codeRegs cf) (codeRegs cg) 0))).2 ≤ s :=
    le_trans (Nat.unpair_right_le _) h0'
  have ha : (Nat.unpair (V' (precSelf (codeRegs cf) (codeRegs cg) 0))).1 ≤ s :=
    le_trans (Nat.unpair_left_le _) h0'
  have hSb := precSetupVals_lt (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) V' B
    hV'b hFfB
  have hOK := precLoopVals_ok (codeRegs_ge cf) (codeRegs_ge cg) cf cg (codeVals cg)
    (codeVals_encodes cg) (precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
      (codeRegs_ge cg) (codeVals cf) V')
    (Nat.unpair (V' (precSelf (codeRegs cf) (codeRegs cg) 0))).1
    (V' (precSelf (codeRegs cf) (codeRegs cg) 1)
      - (Nat.unpair (V' (precSelf (codeRegs cf) (codeRegs cg) 0))).2)
    (precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
      (codeVals cf) V' (precSelf (codeRegs cf) (codeRegs cg) 7)) s B hB2
    (by rw [precSetupVals_m]; exact hm)
    (by rw [precSetupVals_m]; omega) ha
    hWB hSb
    (precSetupVals_a (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) V')
    (precSetupVals_j (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) V')
    (precSetupVals_curFuel (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) V')
    (by rw [precSetupVals_alive, ← precBaseIn_one (codeRegs_ge cf) (codeRegs_ge cg) V',
          ← precBaseIn_zero (codeRegs_ge cf) (codeRegs_ge cg) V']
        exact (codeVals_encodes cf (precBaseIn (codeRegs cf) (codeRegs cg)
          (codeRegs_ge cf) (codeRegs_ge cg) V')).1)
    (by rw [precSetupVals_acc, ← precBaseIn_one (codeRegs_ge cf) (codeRegs_ge cg) V',
          ← precBaseIn_zero (codeRegs_ge cf) (codeRegs_ge cg) V']
        exact (codeVals_encodes cf (precBaseIn (codeRegs cf) (codeRegs cg)
          (codeRegs_ge cf) (codeRegs_ge cg) V')).2)
    (fun u hu hu0 hu1 => codeVals_lt cg (s + precWindowBound cf cg s) B u hBg hu hu0 hu1)
    (fun u => codeVals_tag_le cg u)
  have hsize := precChildIn_size_le (codeRegs_ge cf) (codeRegs_ge cg) cf cg (codeVals cg)
    (codeVals_encodes cg) (precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
      (codeRegs_ge cg) (codeVals cf) V')
    (Nat.unpair (V' (precSelf (codeRegs cf) (codeRegs cg) 0))).1
    (V' (precSelf (codeRegs cf) (codeRegs cg) 1)
      - (Nat.unpair (V' (precSelf (codeRegs cf) (codeRegs cg) 0))).2)
    (precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
      (codeVals cf) V' (precSelf (codeRegs cf) (codeRegs cg) 7)) s
    (by rw [precSetupVals_m]; exact hm)
    (by rw [precSetupVals_m]; omega) ha
    (precSetupVals_a (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) V')
    (precSetupVals_j (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) V')
    (precSetupVals_curFuel (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) V')
    (by rw [precSetupVals_alive, ← precBaseIn_one (codeRegs_ge cf) (codeRegs_ge cg) V',
          ← precBaseIn_zero (codeRegs_ge cf) (codeRegs_ge cg) V']
        exact (codeVals_encodes cf (precBaseIn (codeRegs cf) (codeRegs cg)
          (codeRegs_ge cf) (codeRegs_ge cg) V')).1)
    (by rw [precSetupVals_acc, ← precBaseIn_one (codeRegs_ge cf) (codeRegs_ge cg) V',
          ← precBaseIn_zero (codeRegs_ge cf) (codeRegs_ge cg) V']
        exact (codeVals_encodes cf (precBaseIn (codeRegs cf) (codeRegs cg)
          (codeRegs_ge cf) (codeRegs_ge cg) V')).2)
  -- the loop's per-level facts, indexed the way `precTM_hoareTime` asks for them
  have hm7 : precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
      (codeVals cf) V' (precSelf (codeRegs cf) (codeRegs cg) 7)
      = (Nat.unpair (V' (precSelf (codeRegs cf) (codeRegs cg) 0))).2 :=
    precSetupVals_m (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) V'
  have hchildb : ∀ i, i < precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
      (codeRegs_ge cg) (codeVals cf) V' (precSelf (codeRegs cf) (codeRegs cg) 7) →
      ∀ k, precChildIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
        (precLoopVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
          (codeVals cg) (precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
            (codeRegs_ge cg) (codeVals cf) V') i) k < B := by
    intro i hi k
    obtain ⟨b, -, o9, o12, op1, op2⟩ := hOK i (Nat.le_of_lt hi)
    exact precBodyPre_lt (codeRegs_ge cf) (codeRegs_ge cg) _ B hB2 b o9 o12 op1 op2
      (precRightSub (codeRegs cf) (codeRegs cg) k)
  have hFgB : ∀ i, i < precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
      (codeRegs_ge cg) (codeVals cf) V' (precSelf (codeRegs cf) (codeRegs cg) 7) →
      ∀ k, codeVals cg (precChildIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
        (codeRegs_ge cg)
        (precLoopVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
          (codeVals cg) (precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
            (codeRegs_ge cg) (codeVals cf) V') i)) k < B := by
    intro i hi
    obtain ⟨s0, s1⟩ := hsize i hi
    exact codeVals_lt cg (s + precWindowBound cf cg s) B _ hBg (hchildb i hi) s0 s1
  -- the machine facts
  have hMfl : ∀ Wb : Fin n → Tape, (∀ i, Parked (Wb i)) →
      Mf.HoareTime
        (EmitPred inp₀ (regsWork ((precLeftSub (codeRegs cf) (codeRegs cg)).trans
          ((precMain (codeRegs cf) (codeRegs cg)).trans R)) Wb
          (precBaseIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg) V'))
          ys)
        (EmitPred inp₀ (regsWork ((precLeftSub (codeRegs cf) (codeRegs cg)).trans
          ((precMain (codeRegs cf) (codeRegs cg)).trans R)) Wb
          (codeVals cf (precBaseIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
            (codeRegs_ge cg) V'))) ys)
        (codeMachineTime cf s (evalnArithmeticCost B)) :=
    fun Wb hWb => hMf _ s Wb hWb hBf hbaseb hbase0 hbase1
  have hMgl : ∀ i, i < precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
      (codeRegs_ge cg) (codeVals cf) V' (precSelf (codeRegs cf) (codeRegs cg) 7) →
      ∀ Wb : Fin n → Tape, (∀ j, Parked (Wb j)) →
      Mg.HoareTime
        (EmitPred inp₀ (regsWork ((precRightSub (codeRegs cf) (codeRegs cg)).trans
          ((precMain (codeRegs cf) (codeRegs cg)).trans R)) Wb
          (precChildIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
            (precLoopVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
              (codeVals cg) (precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
                (codeRegs_ge cg) (codeVals cf) V') i))) ys)
        (EmitPred inp₀ (regsWork ((precRightSub (codeRegs cf) (codeRegs cg)).trans
          ((precMain (codeRegs cf) (codeRegs cg)).trans R)) Wb
          (codeVals cg (precChildIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
            (codeRegs_ge cg)
            (precLoopVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
              (codeVals cg) (precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
                (codeRegs_ge cg) (codeVals cf) V') i)))) ys)
        (codeMachineTime cg (s + precWindowBound cf cg s) (evalnArithmeticCost B)) := by
    intro i hi Wb hWb
    obtain ⟨s0, s1⟩ := hsize i hi
    exact hMg _ (s + precWindowBound cf cg s) Wb hWb hBg (hchildb i hi) s0 s1
  have main := precTM_hoareTime (af := codeRegs cf) (ag := codeRegs cg)
    (codeRegs_ge cf) (codeRegs_ge cg)
    ((precMain (codeRegs cf) (codeRegs cg)).trans R) l hl
    Mf Mg
    (codeVals cf) (codeVals cg) (codeMachineTime cf s (evalnArithmeticCost B))
    (codeMachineTime cg (s + precWindowBound cf cg s) (evalnArithmeticCost B))
    V' B inp₀ w₁ ys hinp₀ hpark₁ (V (precLoopIdx (codeRegs cf) (codeRegs cg)))
    (by rw [hw₁, Function.update_self]) (Nat.le_of_lt (hV _)) hB2 hV'b hFfB hFgB
    (fun u => codeVals_tag_le cg u) hOK hMfl hMgl
  rw [regsWork_precMain R w₀ V,
    regsWork_precMain R w₀ (precBlockVals (codeRegs cf) (codeRegs cg)
      (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) (codeVals cg) V)]
  have hpost : (fun k => precBlockVals (codeRegs cf) (codeRegs cg)
      (codeRegs_ge cf) (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
      (precMain (codeRegs cf) (codeRegs cg) k))
      = precVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
        (codeVals cf) (codeVals cg) V' :=
    funext (fun k => precBlockVals_main (codeRegs_ge cf) (codeRegs_ge cg) _ _ V k)
  have hpostl : precBlockVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
      (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
      (precLoopIdx (codeRegs cf) (codeRegs cg))
      = precSetupVals (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
        (codeVals cf) V' (precSelf (codeRegs cf) (codeRegs cg) 7) :=
    precBlockVals_loopIdx (codeRegs_ge cf) (codeRegs_ge cg) _ _ V
  rw [hpost, hpostl]
  rw [hw₁, Function.update_idem] at main
  refine main.mono_bound ?_
  rw [hm7]
  simp only [codeMachineTime]
  have hmul : (Nat.unpair (V' (precSelf (codeRegs cf) (codeRegs cg) 0))).2 *
      ((15 * evalnArithmeticCost B
        + codeMachineTime cg (s + precWindowBound cf cg s) (evalnArithmeticCost B)
        + 15) + 2)
      ≤ s * ((15 * evalnArithmeticCost B
        + codeMachineTime cg (s + precWindowBound cf cg s) (evalnArithmeticCost B)
        + 15) + 2) := Nat.mul_le_mul_right _ hm
  omega

lemma rfBlock_hoareTime (cf : Nat.Partrec.Code) {n : ℕ}
    (R : Regs (33 + codeRegs cf) n) (Mf : TM n)
    (V : Fin (33 + codeRegs cf) → ℕ) (s B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (hB : codeRegBound cf.rfind' s ≤ B) (hV : ∀ k, V k < B)
    (h0 : V (rfMain (codeRegs cf) (rfSelf (codeRegs cf) 0)) ≤ s)
    (h1 : V (rfMain (codeRegs cf) (rfSelf (codeRegs cf) 1)) ≤ s)
    (hMf : ∀ (V₂ : Fin (codeRegs cf) → ℕ) (s₂ : ℕ) (Wb : Fin n → Tape),
      (∀ i, Parked (Wb i)) → codeRegBound cf s₂ ≤ B → (∀ k, V₂ k < B) →
      V₂ (codeLocal cf 0) ≤ s₂ → V₂ (codeLocal cf 1) ≤ s₂ →
      Mf.HoareTime
        (EmitPred inp₀ (regsWork ((rfSub (codeRegs cf)).trans
          ((rfMain (codeRegs cf)).trans R)) Wb V₂) ys)
        (EmitPred inp₀ (regsWork ((rfSub (codeRegs cf)).trans
          ((rfMain (codeRegs cf)).trans R)) Wb (codeVals cf V₂)) ys)
        (codeMachineTime cf s₂ (evalnArithmeticCost B))) :
    (rfindTM (codeRegs cf) (codeRegs_ge cf) ((rfMain (codeRegs cf)).trans R)
      (R (rfLoopIdx (codeRegs cf))) Mf).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀ (regsWork R w₀ (rfBlockVals (codeRegs cf) (codeRegs_ge cf)
        (codeVals cf) V)) ys)
      (codeMachineTime cf.rfind' s (evalnArithmeticCost B)) := by
  simp only [codeRegBound] at hB
  have hgef := le_codeRegBound cf (s + rfWindowBound s)
  have hB2 : 2 ≤ B := by omega
  have h2W : 2 * rfWindowBound s + 3 ≤ B := by
    have h2 : rfWindowBound s ≤ s + rfWindowBound s := Nat.le_add_left _ _
    omega
  have hBf : codeRegBound cf (s + rfWindowBound s) ≤ B := by omega
  set V' : Fin (32 + codeRegs cf) → ℕ := fun k => V (rfMain (codeRegs cf) k) with hV'def
  have hV'b : ∀ k, V' k < B := fun k => hV _
  have h0' : V' (rfSelf (codeRegs cf) 0) ≤ s := h0
  have h1' : V' (rfSelf (codeRegs cf) 1) ≤ s := h1
  have hl : ∀ k, ((rfMain (codeRegs cf)).trans R) k ≠ R (rfLoopIdx (codeRegs cf)) :=
    fun k h => rfMain_ne_loopIdx k (R.injective h)
  set l := R (rfLoopIdx (codeRegs cf)) with hldef
  set w₁ := Function.update w₀ l (regTape (V (rfLoopIdx (codeRegs cf)))) with hw₁
  have hpark₁ : ∀ i, Parked (w₁ i) := by
    intro i; rw [hw₁]
    by_cases hi : i = l
    · subst hi; rw [Function.update_self]; exact parked_regTape _
    · rw [Function.update_of_ne hi]; exact hpark i
  have hSb := rfSetupVals_lt (codeRegs_ge cf) V' B hB2 hV'b
  have hfuel : rfSetupVals (codeRegs cf) (codeRegs_ge cf) V' (rfSelf (codeRegs cf) 1)
      ≤ s := by rw [rfSetupVals_count]; exact h1'
  have h8 : rfSetupVals (codeRegs cf) (codeRegs_ge cf) V' (rfSelf (codeRegs cf) 8)
      = rfSetupVals (codeRegs cf) (codeRegs_ge cf) V' (rfSelf (codeRegs cf) 1) := by
    rw [rfSetupVals_fuel, rfSetupVals_count]
  have hOK := rfLoopVals_ok (codeRegs_ge cf) cf (codeVals cf) (codeVals_encodes cf)
    (rfSetupVals (codeRegs cf) (codeRegs_ge cf) V')
    (Nat.unpair (V' (rfSelf (codeRegs cf) 0))).1
    (Nat.unpair (V' (rfSelf (codeRegs cf) 0))).2
    (rfSetupVals (codeRegs cf) (codeRegs_ge cf) V' (rfSelf (codeRegs cf) 1)) s B hB2
    (le_trans (Nat.unpair_left_le _) h0') (le_trans (Nat.unpair_right_le _) h0') hfuel
    h2W hSb
    (rfSetupVals_a (codeRegs_ge cf) V') (rfSetupVals_m (codeRegs_ge cf) V') h8
    (rfSetupVals_search (codeRegs_ge cf) V') (rfSetupVals_found (codeRegs_ge cf) V')
    (rfSetupVals_result (codeRegs_ge cf) V') (rfSetupVals_one (codeRegs_ge cf) V')
    (fun u hu hu0 hu1 => codeVals_lt cf (s + rfWindowBound s) B u hBf hu hu0 hu1)
    (fun u => codeVals_tag_le cf u)
  have hsize := rfChildIn_size_le (codeRegs_ge cf) cf (codeVals cf)
    (codeVals_encodes cf) (rfSetupVals (codeRegs cf) (codeRegs_ge cf) V')
    (Nat.unpair (V' (rfSelf (codeRegs cf) 0))).1
    (Nat.unpair (V' (rfSelf (codeRegs cf) 0))).2
    (rfSetupVals (codeRegs cf) (codeRegs_ge cf) V' (rfSelf (codeRegs cf) 1)) s
    (le_trans (Nat.unpair_left_le _) h0') (le_trans (Nat.unpair_right_le _) h0') hfuel
    (rfSetupVals_a (codeRegs_ge cf) V') (rfSetupVals_m (codeRegs_ge cf) V') h8
    (rfSetupVals_one (codeRegs_ge cf) V')
  have hchildb : ∀ i, i < rfSetupVals (codeRegs cf) (codeRegs_ge cf) V'
      (rfSelf (codeRegs cf) 1) →
      ∀ k, rfChildIn (codeRegs cf) (codeRegs_ge cf)
        (rfLoopVals (codeRegs cf) (codeRegs_ge cf) (codeVals cf)
          (rfSetupVals (codeRegs cf) (codeRegs_ge cf) V') i) k < B := by
    intro i hi k
    obtain ⟨b, op, -, -, -, -⟩ := hOK i (Nat.le_of_lt hi)
    exact rfPhaseAPre_lt (codeRegs_ge cf) _ B hB2 b op (rfSub (codeRegs cf) k)
  have hFfB : ∀ i, i < rfSetupVals (codeRegs cf) (codeRegs_ge cf) V'
      (rfSelf (codeRegs cf) 1) →
      ∀ k, codeVals cf (rfChildIn (codeRegs cf) (codeRegs_ge cf)
        (rfLoopVals (codeRegs cf) (codeRegs_ge cf) (codeVals cf)
          (rfSetupVals (codeRegs cf) (codeRegs_ge cf) V') i)) k < B := by
    intro i hi
    obtain ⟨s0, s1⟩ := hsize i (Nat.le_of_lt hi)
    exact codeVals_lt cf (s + rfWindowBound s) B _ hBf (hchildb i hi) s0 s1
  have hMfl : ∀ i, i < rfSetupVals (codeRegs cf) (codeRegs_ge cf) V'
      (rfSelf (codeRegs cf) 1) →
      ∀ Wb : Fin n → Tape, (∀ j, Parked (Wb j)) →
      Mf.HoareTime
        (EmitPred inp₀ (regsWork ((rfSub (codeRegs cf)).trans
          ((rfMain (codeRegs cf)).trans R)) Wb
          (rfChildIn (codeRegs cf) (codeRegs_ge cf)
            (rfLoopVals (codeRegs cf) (codeRegs_ge cf) (codeVals cf)
              (rfSetupVals (codeRegs cf) (codeRegs_ge cf) V') i))) ys)
        (EmitPred inp₀ (regsWork ((rfSub (codeRegs cf)).trans
          ((rfMain (codeRegs cf)).trans R)) Wb
          (codeVals cf (rfChildIn (codeRegs cf) (codeRegs_ge cf)
            (rfLoopVals (codeRegs cf) (codeRegs_ge cf) (codeVals cf)
              (rfSetupVals (codeRegs cf) (codeRegs_ge cf) V') i)))) ys)
        (codeMachineTime cf (s + rfWindowBound s) (evalnArithmeticCost B)) := by
    intro i hi Wb hWb
    obtain ⟨s0, s1⟩ := hsize i (Nat.le_of_lt hi)
    exact hMf _ (s + rfWindowBound s) Wb hWb hBf (hchildb i hi) s0 s1
  have main := rfindTM_hoareTime (af := codeRegs cf) (codeRegs_ge cf)
    ((rfMain (codeRegs cf)).trans R) l hl Mf (codeVals cf)
    (codeMachineTime cf (s + rfWindowBound s) (evalnArithmeticCost B)) B V' inp₀ w₁ ys
    hinp₀ hpark₁ (V (rfLoopIdx (codeRegs cf))) (by rw [hw₁, Function.update_self])
    (Nat.le_of_lt (hV _)) hB2 hV'b hFfB (fun u => codeVals_tag_le cf u) hOK hMfl
  rw [regsWork_rfMain R w₀ V,
    regsWork_rfMain R w₀ (rfBlockVals (codeRegs cf) (codeRegs_ge cf) (codeVals cf) V)]
  have hpost : (fun k => rfBlockVals (codeRegs cf) (codeRegs_ge cf) (codeVals cf) V
      (rfMain (codeRegs cf) k))
      = rfindVals (codeRegs cf) (codeRegs_ge cf) (codeVals cf) V' :=
    funext (fun k => rfBlockVals_main (codeRegs_ge cf) _ V k)
  have hpostl : rfBlockVals (codeRegs cf) (codeRegs_ge cf) (codeVals cf) V
      (rfLoopIdx (codeRegs cf))
      = rfSetupVals (codeRegs cf) (codeRegs_ge cf) V' (rfSelf (codeRegs cf) 1) :=
    rfBlockVals_loopIdx (codeRegs_ge cf) _ V
  rw [hpost, hpostl]
  rw [hw₁, Function.update_idem] at main
  refine main.mono_bound ?_
  simp only [codeMachineTime]
  have hmul : rfSetupVals (codeRegs cf) (codeRegs_ge cf) V' (rfSelf (codeRegs cf) 1) *
      ((22 * evalnArithmeticCost B
        + codeMachineTime cf (s + rfWindowBound s) (evalnArithmeticCost B) + 22) + 2)
      ≤ s * ((22 * evalnArithmeticCost B
        + codeMachineTime cf (s + rfWindowBound s) (evalnArithmeticCost B) + 22) + 2) :=
    Nat.mul_le_mul_right _ hfuel
  omega

/-- **The compiled machine meets the step bound.** -/
lemma compiledTM_hoareTime (c : Nat.Partrec.Code) :
    ∀ {n : ℕ} (R : Regs (codeRegs c) n) (V : Fin (codeRegs c) → ℕ) (s B : ℕ)
      (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool),
      Parked inp₀ → (∀ i, Parked (w₀ i)) → codeRegBound c s ≤ B → (∀ k, V k < B) →
      V (codeLocal c 0) ≤ s → V (codeLocal c 1) ≤ s →
      (compiledTM c R).HoareTime
        (EmitPred inp₀ (regsWork R w₀ V) ys)
        (EmitPred inp₀ (regsWork R w₀ (codeVals c V)) ys)
        (codeMachineTime c s (evalnArithmeticCost B)) := by
  induction c with
  | zero =>
      intro n R V s B inp₀ w₀ ys hinp₀ hpark hB hV _ _
      have hgeB := le_codeRegBound Nat.Partrec.Code.zero s
      exact compileZero_hoareTime R V B inp₀ w₀ ys hinp₀ hpark hV
  | succ =>
      intro n R V s B inp₀ w₀ ys hinp₀ hpark hB hV _ _
      exact compileSucc_hoareTime R V B inp₀ w₀ ys hinp₀ hpark hV
  | left =>
      intro n R V s B inp₀ w₀ ys hinp₀ hpark hB hV _ _
      exact compileProj_hoareTime R 0 V B inp₀ w₀ ys hinp₀ hpark hV
  | right =>
      intro n R V s B inp₀ w₀ ys hinp₀ hpark hB hV _ _
      exact compileProj_hoareTime R 1 V B inp₀ w₀ ys hinp₀ hpark hV
  | pair cf cg ihf ihg =>
      intro n R V s B inp₀ w₀ ys hinp₀ hpark hB hV h0 h1
      simp only [codeRegBound] at hB
      have hgef := le_codeRegBound cf s
      have hgeg := le_codeRegBound cg s
      have hB2 : 2 ≤ B := by omega
      have hBf : codeRegBound cf s ≤ B := by omega
      have hBg : codeRegBound cg s ≤ B := by omega
      have hpr : Nat.pair (codeEvalBound cf s) (codeEvalBound cg s) < B := by omega
      have h0' : V (selfW (codeRegs cf) (codeRegs cg) 0) ≤ s := h0
      have h1' : V (selfW (codeRegs cf) (codeRegs cg) 1) ≤ s := h1
      have hL0 : pairLeftIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) V
          ⟨0, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩ ≤ s := by
        rw [pairLeftIn_zero]; exact h0'
      have hL1 : pairLeftIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) V
          ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩ ≤ s := by
        rw [pairLeftIn_one]; exact h1'
      have hLb : ∀ k, pairLeftIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) V k < B := by
        intro k
        simp only [pairLeftIn, Function.update_apply]
        split_ifs <;> exact hV _
      have hFfB := codeVals_lt cf s B _ hBf hLb hL0 hL1
      have hR0 : pairRightIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) V
          ⟨0, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cg)⟩ ≤ s := by
        rw [pairRightIn_zero]; exact h0'
      have hR1 : pairRightIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) V
          ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cg)⟩ ≤ s := by
        rw [pairRightIn_one]; exact h1'
      have hRb : ∀ k, pairRightIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) V k < B := by
        intro k
        simp only [pairRightIn, Function.update_apply]
        split_ifs
        · exact hV _
        · exact hV _
        · refine writeWindow_bounded _ _ _ B (fun j => ?_) (fun j => hFfB j) _
          simp only [Function.update_apply]; split_ifs <;> exact hV _
      have hFgB := codeVals_lt cg s B _ hBg hRb hR0 hR1
      have htagF : pairPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
          (leftLoc (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) 2) ≤ 1 := by
        rw [pairPhaseAVec_leftLoc]; exact codeVals_tag_le cf _
      have htagG : pairPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
          (rightLoc (codeRegs cf) (codeRegs cg) (codeRegs_ge cg) 2) ≤ 1 := by
        rw [pairPhaseAVec_rightLoc]; exact codeVals_tag_le cg _
      have hvF : pairPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
          (leftLoc (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) 3)
          ≤ codeEvalBound cf s := by
        rw [pairPhaseAVec_leftLoc]
        exact le_trans (codeVals_value_le cf _) (codeEvalBound_mono cf hL1)
      have hvG : pairPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
          (rightLoc (codeRegs cf) (codeRegs cg) (codeRegs_ge cg) 3)
          ≤ codeEvalBound cg s := by
        rw [pairPhaseAVec_rightLoc]
        exact le_trans (codeVals_value_le cg _) (codeEvalBound_mono cg hR1)
      rw [compiledTM_pair]
      exact compilePairTM_hoareTime (codeRegs_ge cf) (codeRegs_ge cg) R _ _
        (codeVals cf) (codeVals cg) _ _ V B inp₀ w₀ ys hinp₀ hpark hB2 hV hFfB hFgB
        (fun Wb hWb => ihf _ _ s B inp₀ Wb ys hinp₀ hWb hBf hLb hL0 hL1)
        (fun Wb hWb => ihg _ _ s B inp₀ Wb ys hinp₀ hWb hBg hRb hR0 hR1)
        (lt_of_le_of_lt (natPair_mono hvF hvG) hpr) htagF htagG
  | comp cf cg ihf ihg =>
      intro n R V s B inp₀ w₀ ys hinp₀ hpark hB hV h0 h1
      simp only [codeRegBound] at hB
      have hgef := le_codeRegBound cf (s + codeEvalBound cg s)
      have hgeg := le_codeRegBound cg s
      have hB2 : 2 ≤ B := by omega
      have hBf : codeRegBound cf (s + codeEvalBound cg s) ≤ B := by omega
      have hBg : codeRegBound cg s ≤ B := by omega
      have h0' : V (selfW (codeRegs cf) (codeRegs cg) 0) ≤ s := h0
      have h1' : V (selfW (codeRegs cf) (codeRegs cg) 1) ≤ s := h1
      have hR0 : compRightIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cg) V
          ⟨0, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cg)⟩ ≤ s := by
        rw [compRightIn_zero]; exact h0'
      have hR1 : compRightIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cg) V
          ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cg)⟩ ≤ s := by
        rw [compRightIn_one]; exact h1'
      have hRb : ∀ k, compRightIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cg) V k < B := by
        intro k
        simp only [compRightIn, Function.update_apply]
        split_ifs <;> exact hV _
      have hFgB := codeVals_lt cg s B _ hBg hRb hR0 hR1
      have hvG : codeVals cg (compRightIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cg) V)
          ⟨3, by have := codeRegs_ge cg; omega⟩ ≤ codeEvalBound cg s :=
        le_trans (codeVals_value_le cg _) (codeEvalBound_mono cg hR1)
      have hL0 : compLeftIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
          (codeVals cg) V ⟨0, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩
          ≤ s + codeEvalBound cg s := by
        rw [compLeftIn_zero]; exact le_trans hvG (Nat.le_add_left _ _)
      have hL1 : compLeftIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) (codeRegs_ge cg)
          (codeVals cg) V ⟨1, Nat.lt_of_lt_of_le (by norm_num) (codeRegs_ge cf)⟩
          ≤ s + codeEvalBound cg s := by
        rw [compLeftIn_one]; exact le_trans h1' (Nat.le_add_right _ _)
      have hLb : ∀ k, compLeftIn (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cg) V k < B := by
        intro k
        simp only [compLeftIn, Function.update_apply]
        split_ifs
        · exact hV _
        · refine writeWindow_bounded _ _ _ B (fun j => ?_) (fun j => hFgB j) _
          simp only [Function.update_apply]; split_ifs <;> exact hV _
        · refine writeWindow_bounded _ _ _ B (fun j => ?_) (fun j => hFgB j) _
          simp only [Function.update_apply]; split_ifs <;> exact hV _
      have hFfB := codeVals_lt cf (s + codeEvalBound cg s) B _ hBf hLb hL0 hL1
      have htagF : compPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
          (leftLoc (codeRegs cf) (codeRegs cg) (codeRegs_ge cf) 2) ≤ 1 := by
        rw [compPhaseAVec_leftLoc]; exact codeVals_tag_le cf _
      have htagG : compPhaseAVec (codeRegs cf) (codeRegs cg) (codeRegs_ge cf)
          (codeRegs_ge cg) (codeVals cf) (codeVals cg) V
          (rightLoc (codeRegs cf) (codeRegs cg) (codeRegs_ge cg) 2) ≤ 1 := by
        rw [compPhaseAVec_rightLoc]; exact codeVals_tag_le cg _
      rw [compiledTM_comp]
      exact compileCompTM_hoareTime (codeRegs_ge cf) (codeRegs_ge cg) R _ _
        (codeVals cf) (codeVals cg) _ _ V B inp₀ w₀ ys hinp₀ hpark hV hFfB hFgB
        (fun Wb hWb => ihf _ _ (s + codeEvalBound cg s) B inp₀ Wb ys hinp₀ hWb hBf
          hLb hL0 hL1)
        (fun Wb hWb => ihg _ _ s B inp₀ Wb ys hinp₀ hWb hBg hRb hR0 hR1)
        htagG htagF
  | prec cf cg ihf ihg =>
      intro n R V s B inp₀ w₀ ys hinp₀ hpark hB hV h0 h1
      rw [compiledTM_prec]
      exact precBlock_hoareTime cf cg R _ _ V s B inp₀ w₀ ys hinp₀ hpark hB hV h0 h1
        (fun V₂ s₂ Wb hWb hb hv hz ho => ihf _ V₂ s₂ B inp₀ Wb ys hinp₀ hWb hb hv hz ho)
        (fun V₂ s₂ Wb hWb hb hv hz ho => ihg _ V₂ s₂ B inp₀ Wb ys hinp₀ hWb hb hv hz ho)
  | rfind' cf ihf =>
      intro n R V s B inp₀ w₀ ys hinp₀ hpark hB hV h0 h1
      rw [compiledTM_rfind']
      exact rfBlock_hoareTime cf R _ V s B inp₀ w₀ ys hinp₀ hpark hB hV h0 h1
        (fun V₂ s₂ Wb hWb hb hv hz ho => ihf _ V₂ s₂ B inp₀ Wb ys hinp₀ hWb hb hv hz ho)

end MachineTimeHoare

end LogicalInduction.EvalnCompiler
