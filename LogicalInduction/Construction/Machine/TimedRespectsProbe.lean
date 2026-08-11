/-
# Stage-0 de-risk probe — carrying a step count through a Mathlib TM simulation

**This file is a spike, not part of the formalization.**  It is not imported by
`LogicalInduction.lean`, contributes to no endpoint, and carries no paper node.  Its only
purpose is to supply *evidence* for the Stage-0 decision recorded in
`notes/boundary-efficiency-model.md` ("in-repo counted machine vs. Mathlib retrofit").

The question the probe answers: **can a step-count bound be carried through Mathlib's
smallest TM simulation (`Turing.TM1to0`) without re-proving the file from scratch?**

The probe does three things:

1. `ReachesIn` — a *counted* reachability relation, and the two bridge lemmas showing
   exactly what `Turing`'s `Reaches`/`Reaches₁` do and do not retain
   (`reaches_iff_reachesIn`, `reaches₁_iff_reachesIn`): a step count always *exists*, but
   `Reaches₁` is an existential over it, so no bound survives in the statement.
2. `TimedRespects` — the timed refinement Mathlib does not have, with the run-composition
   lemma that is the whole point of a timed simulation theory
   (`TimedRespects.reachesIn`: `m` source steps cost at most `m * cost` target steps).
3. `TM1to0.trCost` / `tr_timed` / `timedRespects_tm1to0` — the timed version of
   `Turing.TM1to0.tr_respects`, proved.

**Finding (the number the Stage-0 decision turns on): reuse of Mathlib's proof is zero.**
`Turing.TM1to0.tr_respects` concludes `Reaches₁`, which is `Relation.TransGen` — a
transitive closure with no length field — so `tr_timed` cannot be derived from it; the
induction is redone here in full, and it additionally needs a statement-size measure
(`trCost`) that Mathlib does not define and a `Fintype Λ` uniformity hypothesis that
`Turing.TM1.Supports` does not supply.  `TM1to0` is the *easiest* of the four simulations
(its per-step cost is a syntactic measure of one statement); `TM1to1` costs scale with the
symbol-encoding width and `TM2to1`'s with the stack contents, i.e. they need the global
size invariant the note flags as the riskiest step.
-/
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Finset.Lattice.Fold

namespace LogicalInduction.MachineSpike

open StateTransition Turing Relation

/-! ## Counted reachability -/

variable {σ σ₁ σ₂ : Type*}

/-- `ReachesIn f k a b`: the state transition function `f` carries `a` to `b` in *exactly*
`k` steps.  This is the datum `Turing`'s `Reaches`/`Reaches₁` discard. -/
def ReachesIn (f : σ → Option σ) : ℕ → σ → σ → Prop
  | 0, a, b => a = b
  | k + 1, a, b => ∃ c, f a = some c ∧ ReachesIn f k c b

lemma ReachesIn.refl (f : σ → Option σ) (a : σ) : ReachesIn f 0 a a := rfl

lemma ReachesIn.trans {f : σ → Option σ} : ∀ {k l : ℕ} {a b c : σ},
    ReachesIn f k a b → ReachesIn f l b c → ReachesIn f (k + l) a c
  | 0, _, a, b, c, h₁, h₂ => by cases h₁; simpa using h₂
  | k + 1, l, a, b, c, ⟨d, hd, h₁⟩, h₂ => by
      have hrec : ReachesIn f (k + l) d c := ReachesIn.trans h₁ h₂
      show ReachesIn f (k + 1 + l) a c
      rw [show k + 1 + l = (k + l) + 1 by omega]
      exact ⟨d, hd, hrec⟩

/-- Weakening along a step-equal state: if `a` and `a'` have the same successor then any
nonempty run out of `a'` is a run out of `a` of the same length.  (Used for the `load` and
`branch` cases of `TM1to0`, which cost zero target steps.) -/
lemma ReachesIn.of_step_eq {f : σ → Option σ} {a a' b : σ} {k : ℕ} (h : f a = f a')
    (hk : ReachesIn f (k + 1) a' b) : ReachesIn f (k + 1) a b := by
  obtain ⟨c, hc, hrest⟩ := hk
  exact ⟨c, h.trans hc, hrest⟩

lemma ReachesIn.single {f : σ → Option σ} {a b : σ} (h : f a = some b) :
    ReachesIn f 1 a b := ⟨b, h, rfl⟩

/-- `Reaches` is exactly "some step count exists". -/
lemma reaches_iff_reachesIn {f : σ → Option σ} {a b : σ} :
    Reaches f a b ↔ ∃ k, ReachesIn f k a b := by
  constructor
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl⟩
    | head hab _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, _, hab, hk⟩
  · rintro ⟨k, hk⟩
    induction k generalizing a with
    | zero => cases hk; exact ReflTransGen.refl
    | succ k ih => obtain ⟨c, hc, hrest⟩ := hk; exact ReflTransGen.head hc (ih hrest)

/-- `Reaches₁` is exactly "some positive step count exists".  This is the precise sense in
which Mathlib's simulation statements are untimed: the count is existentially quantified
inside the relation, so no downstream lemma can recover a bound on it. -/
lemma reaches₁_iff_reachesIn {f : σ → Option σ} {a b : σ} :
    Reaches₁ f a b ↔ ∃ k, ReachesIn f (k + 1) a b := by
  constructor
  · intro h
    have h' : TransGen (fun x y => y ∈ f x) a b := h
    obtain ⟨c, hc, hrest⟩ := TransGen.head'_iff.1 h'
    obtain ⟨k, hk⟩ := reaches_iff_reachesIn.1 hrest
    exact ⟨k, c, hc, hk⟩
  · rintro ⟨k, c, hc, hk⟩
    exact TransGen.head' hc (reaches_iff_reachesIn.2 ⟨k, hk⟩)

/-! ## The timed refinement Mathlib lacks -/

/-- A **timed** refinement: `tr` maps every step of `f₁` to between one and `cost` steps of
`f₂`, and maps halting to halting.  Compare `StateTransition.Respects`, whose `some` branch
concludes `Reaches₁` and therefore keeps no bound. -/
def TimedRespects (f₁ : σ₁ → Option σ₁) (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂) (cost : ℕ) :
    Prop :=
  ∀ a₁ : σ₁, match f₁ a₁ with
    | some b₁ => ∃ k, 0 < k ∧ k ≤ cost ∧ ReachesIn f₂ k (tr a₁) (tr b₁)
    | none => f₂ (tr a₁) = none

/-- The payoff of a timed refinement: an `m`-step source run is simulated by a target run of
at most `m * cost` steps.  This is the statement a machine-class inclusion needs and the one
`StateTransition.tr_reaches₁` cannot provide. -/
lemma TimedRespects.reachesIn {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂}
    {cost : ℕ} (H : TimedRespects f₁ f₂ tr cost) :
    ∀ {m : ℕ} {a b : σ₁}, ReachesIn f₁ m a b → ∃ k ≤ m * cost, ReachesIn f₂ k (tr a) (tr b)
  | 0, a, b, h => by cases h; exact ⟨0, by simp, rfl⟩
  | m + 1, a, b, ⟨c, hc, hrest⟩ => by
      obtain ⟨k₂, hk₂le, hk₂⟩ := TimedRespects.reachesIn H hrest
      have hstep := H a
      rw [hc] at hstep
      obtain ⟨k₁, -, hk₁le, hk₁⟩ := hstep
      have hexp : (m + 1) * cost = m * cost + cost := Nat.succ_mul m cost
      exact ⟨k₁ + k₂, by omega, hk₁.trans hk₂⟩

/-! ## The probe: a timed `Turing.TM1to0` -/

namespace TM1to0Timed

variable {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ] {σ : Type*} [Inhabited σ]

open TM1 (Stmt)

/-- The number of `TM0` steps `Turing.TM1to0.tr` spends simulating one `TM1` step through
the statement `q`.  `move`/`write` each emit one `TM0` step, `load`/`branch` emit none (they
are resolved inside a single `trAux` call), and the terminal `goto`/`halt` emits one.
Mathlib defines no size measure on `TM1.Stmt`, so this is new. -/
def trCost : Stmt Γ Λ σ → ℕ
  | .move _ q => trCost q + 1
  | .write _ q => trCost q + 1
  | .load _ q => trCost q
  | .branch _ q₁ q₂ => max (trCost q₁) (trCost q₂)
  | .goto _ => 1
  | .halt => 1

omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
/-- Every statement costs at least one `TM0` step: the terminal `goto`/`halt` always emits
one. -/
lemma trCost_pos : ∀ q : Stmt Γ Λ σ, 0 < trCost q
  | .move _ _ => Nat.succ_pos _
  | .write _ _ => Nat.succ_pos _
  | .load _ q => trCost_pos q
  | .branch _ q₁ _ => lt_of_lt_of_le (trCost_pos q₁) (le_max_left _ _)
  | .goto _ => Nat.one_pos
  | .halt => Nat.one_pos

/-- **The timed simulation lemma.**  Simulating the `TM1` statement `q` from local state `v`
and tape `T` takes between `1` and `trCost q` steps of the translated `TM0` machine.

This is `Turing.TM1to0.tr_respects` with a count.  Not one line of Mathlib's proof is
reusable: its conclusion is `Reaches₁`, whose `TransGen` carries no length, so the induction
is redone here in full. -/
lemma tr_timed (M : Λ → Stmt Γ Λ σ) : ∀ (q : Stmt Γ Λ σ) (v : σ) (T : Tape Γ),
    ∃ k, 0 < k ∧ k ≤ trCost q ∧
      ReachesIn (TM0.step (Turing.TM1to0.tr M)) k ⟨(some q, v), T⟩
        (Turing.TM1to0.trCfg M (TM1.stepAux q v T))
  | .move d q, v, T => by
      obtain ⟨k, hkpos, hkle, hk⟩ := tr_timed M q v (T.move d)
      refine ⟨k + 1, Nat.succ_pos _, by simpa [trCost] using hkle, ?_⟩
      refine ⟨⟨(some q, v), T.move d⟩, ?_, hk⟩
      simp [TM0.step, Turing.TM1to0.tr, Turing.TM1to0.trAux]
  | .write a q, v, T => by
      obtain ⟨k, hkpos, hkle, hk⟩ := tr_timed M q v (T.write (a T.1 v))
      refine ⟨k + 1, Nat.succ_pos _, by simpa [trCost] using hkle, ?_⟩
      refine ⟨⟨(some q, v), T.write (a T.1 v)⟩, ?_, hk⟩
      simp [TM0.step, Turing.TM1to0.tr, Turing.TM1to0.trAux]
  | .load s q, v, T => by
      obtain ⟨k, hkpos, hkle, hk⟩ := tr_timed M q (s T.1 v) T
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      refine ⟨k' + 1, Nat.succ_pos _, by simpa [trCost] using hkle, ?_⟩
      refine ReachesIn.of_step_eq ?_ hk
      simp [TM0.step, Turing.TM1to0.tr, Turing.TM1to0.trAux]
  | .branch p q₁ q₂, v, T => by
      cases e : p T.1 v
      · obtain ⟨k, hkpos, hkle, hk⟩ := tr_timed M q₂ v T
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        refine ⟨k' + 1, Nat.succ_pos _, le_trans hkle (le_max_right _ _), ?_⟩
        refine ReachesIn.of_step_eq (a' := ⟨(some q₂, v), T⟩) ?_ ?_
        · simp [TM0.step, Turing.TM1to0.tr, Turing.TM1to0.trAux, e]
        · simpa [TM1.stepAux, e] using hk
      · obtain ⟨k, hkpos, hkle, hk⟩ := tr_timed M q₁ v T
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        refine ⟨k' + 1, Nat.succ_pos _, le_trans hkle (le_max_left _ _), ?_⟩
        refine ReachesIn.of_step_eq (a' := ⟨(some q₁, v), T⟩) ?_ ?_
        · simp [TM0.step, Turing.TM1to0.tr, Turing.TM1to0.trAux, e]
        · simpa [TM1.stepAux, e] using hk
  | .goto l, v, T => by
      refine ⟨1, Nat.one_pos, le_rfl, ReachesIn.single ?_⟩
      simp [TM0.step, Turing.TM1to0.tr, Turing.TM1to0.trAux, Turing.TM1to0.trCfg,
        TM1.stepAux, Tape.write_self]
  | .halt, v, T => by
      refine ⟨1, Nat.one_pos, le_rfl, ReachesIn.single ?_⟩
      simp [TM0.step, Turing.TM1to0.tr, Turing.TM1to0.trAux, Turing.TM1to0.trCfg,
        TM1.stepAux, Tape.write_self]

/-- **The probe's conclusion.**  `Turing.TM1to0` *is* a timed refinement, with uniform cost
the largest statement cost over the label type.

Two hypotheses beyond Mathlib's `tr_respects` are load-bearing and neither is free:
`Fintype Λ` (Mathlib's `TM1.Supports` bounds *which* labels are reachable, not how many, so
the uniform `Finset.sup` is not available from it), and the new measure `trCost`. -/
lemma timedRespects_tm1to0 [Fintype Λ] (M : Λ → Stmt Γ Λ σ) :
    TimedRespects (TM1.step M) (TM0.step (Turing.TM1to0.tr M)) (Turing.TM1to0.trCfg M)
      (Finset.univ.sup fun l => trCost (M l)) := by
  rintro ⟨l₁, v, T⟩
  cases l₁ with
  | none => simp [TM1.step, TM0.step, Turing.TM1to0.tr, Turing.TM1to0.trCfg]
  | some l =>
      obtain ⟨k, hkpos, hkle, hk⟩ := tr_timed M (M l) v T
      refine ⟨k, hkpos,
        hkle.trans (Finset.le_sup (f := fun l => trCost (M l)) (Finset.mem_univ l)), ?_⟩
      simpa [Turing.TM1to0.trCfg] using hk

end TM1to0Timed

end LogicalInduction.MachineSpike
