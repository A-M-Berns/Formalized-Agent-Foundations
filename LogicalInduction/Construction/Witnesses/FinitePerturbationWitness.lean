import LogicalInduction.Construction.Witnesses.ComputationDP
import LogicalInduction.Construction.Witnesses.ProductDefinition
import LogicalInduction.Construction.Witnesses.FiniteEntailment
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-!
# The concrete witness for the finite-perturbation counterexample

`Properties/FinitePerturbationCounterexample.lean` develops the refutation of the
unrestricted finite-day perturbation statement abstractly and closes with
`not_overgeneral_ifp_of_advice`, a complete reduction.  This module supplies the witness
that reduction consumes and states the closed refutation.

The split is forced: `theoremDP` and the quotation layer reach the abstract module through
`ComputationSyntax` → `BoundedEvaluation` → `LogicalInduction.Properties`, so the witness
cannot be named there.  It is the same split `lic_paradox_resistance_ofDiagonal` and
`lic_paradox_resistance_ofDiagonal_unconditional` already use.

The market fed to `paradoxResistanceQuoteOfDiagonal` is the **unperturbed** one
(`theoremMarketComputation`): `χ n` asserts a fact about that quote program, and
`advicePerturbed_agree` carries the reflection to the perturbed market on every day `≥ 1`.
`not_overgeneral_ifp` carries `Paper node: thm:ifp` and is a canonical trust-surface
endpoint: a refutation belongs to the node it refutes, and is audited exactly like any
other endpoint.
-/

namespace LogicalInduction
namespace FinitePerturbationCounterexample

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional
open Filter Topology
open Classical

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-! ## Computability of the schedule

The day-`0` advice row is a search.  This section makes each ingredient computable, in the
dependency order recorded on `computableMarket_cxPerturbed`, over an abstract market,
process and diagonal.  Everything here is stated against the *unperturbed* market; the
perturbed one is reached at the end through `sched_congr`.
-/

section Computability

/-- A certified computable process has a computable stage sequence.
Kind `C`; hypotheses `(b)` `Nat.Partrec.Code.eval_part`, `Partrec.of_eq_tot`. -/
lemma computable_stage {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) :
    Computable (fun n => DP.D n) := by
  rw [← Computable.encode_iff]
  have hp : Partrec (fun n : ℕ => c.code.eval n) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const c.code) Computable.id
  exact hp.of_eq_tot (fun n => c.code_spec n)

/-- A certified market program has a computable quote table.
Kind `C`; hypotheses `(b)` as above. -/
lemma computable_quote {P : History} (M : MarketComputation P) :
    Computable (fun z : ℕ => M.quote z.unpair.1 z.unpair.2) := by
  rw [← Computable.encode_iff]
  have hp : Partrec (fun z : ℕ => M.code.eval z) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const M.code) Computable.id
  exact hp.of_eq_tot (fun z => M.code_spec z)

/-- Foundation's code of `∼φ`, read off `Formula.toNat`. -/
lemma encode_sentence_neg (φ : Sentence) :
    Encodable.encode (∼φ) = Nat.pair 2 (Nat.pair (Encodable.encode φ) 1) + 1 := rfl

/-- Negating a computable sentence family stays computable.
Kind `C`; hypotheses `(a)`. -/
lemma computable_neg {χ : ℕ → Sentence} (hχ : Computable χ) :
    Computable (fun m => ∼(χ m)) := by
  rw [← Computable.encode_iff]
  have hcode : Computable (fun m => Encodable.encode (χ m)) :=
    Computable.encode.comp hχ
  have h : Computable
      (fun m : ℕ => Nat.pair 2 (Nat.pair (Encodable.encode (χ m)) 1) + 1) :=
    Computable.succ.comp
      (Primrec₂.natPair.to_comp.comp (Computable.const 2)
        (Primrec₂.natPair.to_comp.comp hcode (Computable.const 1)))
  exact h.of_eq (fun m => (encode_sentence_neg (χ m)).symm)

variable {V : History} {DP : DeductiveProcess} {χ : ℕ → Sentence}

/-- The Boolean settlement test: which side of the diagonal threshold the price falls on
decides which sentence the finite stage must entail. -/
noncomputable def settledTest (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (m k : ℕ) : Bool :=
  if V m (χ m) < 1 / 2 then stageEntails (DP.D k) (χ m)
  else stageEntails (DP.D k) (∼(χ m))

/-- The test decides settlement exactly.
Kind `P`; hypotheses `(b)` `stageEntails_eq_true_iff`, `PCWorld.holds_neg`. -/
lemma settledTest_eq_true_iff (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (m k : ℕ) : settledTest V DP χ m k = true ↔ SettledAt V DP χ m k := by
  rw [settledTest]
  by_cases h : V m (χ m) < 1 / 2
  · rw [if_pos h, stageEntails_eq_true_iff]
    exact ⟨fun hh v hv => iff_of_true (hh v hv) h, fun hh v hv => (hh v hv).2 h⟩
  · rw [if_neg h, stageEntails_eq_true_iff]
    refine ⟨fun hh v hv => iff_of_false ((PCWorld.holds_neg v (χ m)).1 (hh v hv)) h,
      fun hh v hv => (PCWorld.holds_neg v (χ m)).2 (fun hH => h ((hh v hv).1 hH))⟩

/-- The test with day `0` short-circuited, so the unbounded search is total everywhere.
Day `0` is never scheduled, so the short circuit is invisible downstream. -/
noncomputable def settledTestZ (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (m k : ℕ) : Bool :=
  Nat.casesOn (motive := fun _ => Bool) m true (fun _ => settledTest V DP χ m k)

@[simp] lemma settledTestZ_zero (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (k : ℕ) : settledTestZ V DP χ 0 k = true := rfl

lemma settledTestZ_of_ne_zero (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    {m : ℕ} (hm : m ≠ 0) (k : ℕ) :
    settledTestZ V DP χ m k = settledTest V DP χ m k := by
  cases m with
  | zero => exact absurd rfl hm
  | succ m => rfl

/-- The test as a `cond`, so the computability proof never unfolds the `if`. -/
lemma settledTest_eq_cond (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (m k : ℕ) : settledTest V DP χ m k =
      cond (decide (V m (χ m) < 1 / 2)) (stageEntails (DP.D k) (χ m))
        (stageEntails (DP.D k) (∼(χ m))) := by
  by_cases h : V m (χ m) < 1 / 2 <;> simp [settledTest, h]

lemma settledTestZ_eq_casesOn (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (m k : ℕ) : settledTestZ V DP χ m k =
      Nat.casesOn (motive := fun _ => Bool) m true (fun _ => settledTest V DP χ m k) := rfl

section
-- `Nat.sqrt` is locally irreducible here for the reason recorded in `LIACompiler.lean`:
-- `Computable` elaboration over these nested product types otherwise unfolds its
-- well-founded definition during `whnf` and exhausts the heartbeat budget.  The two
-- definitions being reasoned about are blocked alongside it so the bridges below match
-- structurally rather than by reduction.
attribute [local irreducible] Nat.sqrt settledTest settledTestZ

set_option maxHeartbeats 1000000 in
/-- Kind `C`; hypotheses `(a)`. -/
lemma computable_settledTest (hχ : Computable χ)
    (hlt : Computable (fun m => decide (V m (χ m) < 1 / 2)))
    (hD : Computable (fun k => DP.D k)) :
    Computable (fun p : ℕ × ℕ => settledTestZ V DP χ p.1 p.2) := by
  have hpos : Computable (fun p : ℕ × ℕ => stageEntails (DP.D p.2) (χ p.1)) :=
    stageEntails_primrec.to_comp.comp
      ((hD.comp Computable.snd).pair (hχ.comp Computable.fst))
  have hneg : Computable (fun p : ℕ × ℕ => stageEntails (DP.D p.2) (∼(χ p.1))) :=
    stageEntails_primrec.to_comp.comp
      ((hD.comp Computable.snd).pair ((computable_neg hχ).comp Computable.fst))
  have hc : Computable (fun p : ℕ × ℕ => decide (V p.1 (χ p.1) < 1 / 2)) :=
    hlt.comp Computable.fst
  have hbody : Computable (fun p : ℕ × ℕ => settledTest V DP χ p.1 p.2) :=
    (Computable.cond hc hpos hneg).of_eq
      (fun p => (settledTest_eq_cond V DP χ p.1 p.2).symm)
  exact (Computable.nat_casesOn Computable.fst (Computable.const true)
    (hbody.comp Computable.fst).to₂).of_eq
    (fun p => (settledTestZ_eq_casesOn V DP χ p.1 p.2).symm)

end

/-- Every day admits a settling stage, once the dichotomy holds off day `0`.
Kind `C`; hypotheses `(a)`. -/
lemma exists_settledTestZ (hdicho : ∀ m, 1 ≤ m → Dichotomy V DP χ m) (m : ℕ) :
    ∃ k, settledTestZ V DP χ m k = true := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact ⟨0, by rw [hm]; exact settledTestZ_zero V DP χ 0⟩
  · obtain ⟨k, hk⟩ := exists_settled (hdicho m hm)
    refine ⟨k, ?_⟩
    rw [settledTestZ_of_ne_zero V DP χ (by omega) k, settledTest_eq_true_iff]
    exact hk

/-- The least settling stage, total everywhere by the day-`0` short circuit. -/
noncomputable def settleTotal (hdicho : ∀ m, 1 ≤ m → Dichotomy V DP χ m) (m : ℕ) : ℕ :=
  Nat.find (exists_settledTestZ hdicho m)

/-- Off day `0` the total search is the abstract settlement stage.
Kind `P`; hypotheses `(a)`. -/
lemma settleTotal_eq (hdicho : ∀ m, 1 ≤ m → Dichotomy V DP χ m) {m : ℕ} (hm : 1 ≤ m) :
    settleTotal hdicho m = settleStage V DP χ m := by
  have hex : ∃ k, SettledAt V DP χ m k := exists_settled (hdicho m hm)
  have hstage : settleStage V DP χ m = Nat.find hex := by rw [settleStage, dif_pos hex]
  rw [hstage, settleTotal]
  refine le_antisymm (Nat.find_min' _ ?_) (Nat.find_min' _ ?_)
  · rw [settledTestZ_of_ne_zero V DP χ (by omega), settledTest_eq_true_iff]
    exact Nat.find_spec hex
  · have h := Nat.find_spec (exists_settledTestZ hdicho m)
    rw [settledTestZ_of_ne_zero V DP χ (by omega), settledTest_eq_true_iff] at h
    exact h

/-- **Obligation (3).**  The settlement search is computable: `Nat.find` over a computable
Boolean test, which is `Mathlib`'s `Computable.find`.
Kind `C`; hypotheses `(b)` `Computable.find`. -/
lemma computable_settleTotal (hdicho : ∀ m, 1 ≤ m → Dichotomy V DP χ m)
    (hχ : Computable χ) (hlt : Computable (fun m => decide (V m (χ m) < 1 / 2)))
    (hD : Computable (fun k => DP.D k)) :
    Computable (settleTotal hdicho) := by
  have hP : ComputablePred (fun p : ℕ × ℕ => settledTestZ V DP χ p.1 p.2 = true) :=
    ⟨inferInstance, (computable_settledTest hχ hlt hD).of_eq (fun p => by simp)⟩
  exact Computable.find hP (exists_settledTestZ hdicho)

/-- The schedule as an explicit `Nat.rec`, which is the shape `Computable.nat_rec` consumes. -/
noncomputable def schedComp (hdicho : ∀ m, 1 ≤ m → Dichotomy V DP χ m) (j : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 1 (fun _ IH => max IH (settleTotal hdicho IH) + 1) j

/-- Kind `P`; hypotheses `(a)`. -/
lemma schedComp_eq (hdicho : ∀ m, 1 ≤ m → Dichotomy V DP χ m) (j : ℕ) :
    schedComp hdicho j = sched V DP χ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show max (schedComp hdicho j) (settleTotal hdicho (schedComp hdicho j)) + 1 = _
      rw [ih, settleTotal_eq hdicho (one_le_sched V DP χ j)]
      rfl

/-- **Obligation (4).**  The schedule is computable, by recursion on the computable step.
Kind `C`; hypotheses `(b)` `Computable.nat_rec`. -/
lemma computable_sched (hdicho : ∀ m, 1 ≤ m → Dichotomy V DP χ m)
    (hcomp : Computable (settleTotal hdicho)) : Computable (sched V DP χ) := by
  have hstep : Computable₂
      (fun (_ : ℕ) (q : ℕ × ℕ) => max q.2 (settleTotal hdicho q.2) + 1) := by
    have hsnd : Computable (fun r : ℕ × (ℕ × ℕ) => r.2.2) :=
      Computable.snd.comp Computable.snd
    exact (Computable.succ.comp
      (Primrec.nat_max.to_comp.comp hsnd (hcomp.comp hsnd))).to₂
  exact ((Computable.nat_rec Computable.id (Computable.const 1) hstep).of_eq
    (fun j => rfl)).of_eq (schedComp_eq hdicho)

/-! ### The gate bit -/

/-- The schedule never falls below its index, which is what bounds the gate search. -/
lemma le_sched (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (i : ℕ) :
    i ≤ sched V DP χ i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih => have := sched_lt_succ V DP χ i; omega

/-- `∃ i ≤ j, sched i = n`, as an explicit `Nat.rec`. -/
noncomputable def gateAux (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (n : ℕ) : ℕ → Bool :=
  fun j => Nat.rec (motive := fun _ => Bool) (decide (sched V DP χ 0 = n))
    (fun y IH => IH || decide (sched V DP χ (y + 1) = n)) j

/-- Kind `P`; hypotheses `(a)`. -/
lemma gateAux_eq_true_iff (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (n j : ℕ) : gateAux V DP χ n j = true ↔ ∃ i ≤ j, sched V DP χ i = n := by
  induction j with
  | zero =>
      have hz : gateAux V DP χ n 0 = decide (sched V DP χ 0 = n) := rfl
      rw [hz]
      constructor
      · intro h; exact ⟨0, le_refl 0, by simpa using h⟩
      · rintro ⟨i, hi, hs⟩
        have hi0 : i = 0 := Nat.le_zero.mp hi
        subst hi0
        simpa using hs
  | succ j ih =>
      show ((gateAux V DP χ n j) || decide (sched V DP χ (j + 1) = n)) = true ↔ _
      rw [Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, hs⟩ | h)
        · exact ⟨i, by omega, hs⟩
        · exact ⟨j + 1, le_refl _, by simpa using h⟩
      · rintro ⟨i, hi, hs⟩
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact Or.inl ⟨i, by omega, hs⟩
        · have : i = j + 1 := by omega
          subst this
          exact Or.inr (by simpa using hs)

/-- The schedule bit: is day `n` a trading day? -/
noncomputable def gateBool (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (n : ℕ) : Bool := gateAux V DP χ n n

/-- **Obligation (5).**  Strict monotonicity from `sched 0 = 1` bounds the search by `n`.
Kind `C`; hypotheses `(a)`. -/
lemma gateBool_eq_true_iff (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (n : ℕ) : gateBool V DP χ n = true ↔ ∃ j, sched V DP χ j = n := by
  rw [gateBool, gateAux_eq_true_iff]
  refine ⟨fun ⟨i, _, hs⟩ => ⟨i, hs⟩, fun ⟨i, hs⟩ => ⟨i, ?_, hs⟩⟩
  have hle : i ≤ sched V DP χ i := le_sched V DP χ i
  omega

/-- Kind `C`; hypotheses `(b)` `Computable.nat_rec`. -/
lemma computable_gateBool (hs : Computable (sched V DP χ)) :
    Computable (gateBool V DP χ) := by
  have hdec : Computable₂ (fun a b : ℕ => decide (a = b)) :=
    (Primrec.eq (α := ℕ)).decide.to_comp.to₂
  have hbase : Computable (fun n : ℕ => decide (sched V DP χ 0 = n)) :=
    hdec.comp (Computable.const (sched V DP χ 0)) Computable.id
  have hstep : Computable₂
      (fun (n : ℕ) (q : ℕ × Bool) => q.2 || decide (sched V DP χ (q.1 + 1) = n)) := by
    have hIH : Computable (fun r : ℕ × (ℕ × Bool) => r.2.2) :=
      Computable.snd.comp Computable.snd
    have hy : Computable (fun r : ℕ × (ℕ × Bool) => sched V DP χ (r.2.1 + 1)) :=
      hs.comp (Computable.succ.comp (Computable.fst.comp Computable.snd))
    have hcmp : Computable (fun r : ℕ × (ℕ × Bool) =>
        decide (sched V DP χ (r.2.1 + 1) = r.1)) :=
      hdec.comp hy Computable.fst
    exact ((Primrec.dom_bool₂ (· || ·)).to_comp.comp hIH hcmp).to₂
  exact Computable.nat_rec Computable.id hbase hstep

/-! ### Comparing a rational against the diagonal threshold

Neither Mathlib nor this repository exposes a primitive-recursive order on `ℚ`
(`LIACompiler`'s `ratNum_prim`/`ratDen_prim` are `private`), so the one comparison this
construction needs is built here directly from `encode_rat_eq`: the numerator's `ℤ`-code
is even exactly when the numerator is non-negative, which turns the test into two `ℕ`
operations. -/

private lemma int_lt_half_iff_encode (z : ℤ) (d : ℕ) (hd : 0 < d) :
    (z * 2 < (d : ℤ)) ↔ (Encodable.encode z % 2 = 1 ∨ Encodable.encode z < d) := by
  cases z with
  | ofNat n =>
      rw [show Encodable.encode ((Int.ofNat n : ℤ)) = 2 * n from encode_int_natCast n,
        Nat.mul_mod_right 2 n]
      show ((n : ℤ) * 2 < (d : ℤ)) ↔ _
      omega
  | negSucc n =>
      rw [show Encodable.encode (Int.negSucc n) = 2 * n + 1 from rfl]
      simp only [Int.negSucc_eq]
      omega

private lemma rat_lt_half_iff_int (q : ℚ) : q < 1 / 2 ↔ q.num * 2 < (q.den : ℤ) := by
  have hd : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.pos
  have hq : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
  constructor
  · intro h
    rw [← hq, div_lt_div_iff₀ hd (by norm_num : (0 : ℚ) < 2), one_mul] at h
    exact_mod_cast h
  · intro h
    have h' : (q.num : ℚ) * 2 < ((q.den : ℤ) : ℚ) := by exact_mod_cast h
    rw [← hq, div_lt_div_iff₀ hd (by norm_num : (0 : ℚ) < 2), one_mul]
    push_cast at h' ⊢
    linarith

private lemma rat_lt_half_iff_encode (q : ℚ) :
    ((Encodable.encode q).unpair.1 % 2 = 1 ∨
      (Encodable.encode q).unpair.1 < (Encodable.encode q).unpair.2) ↔ q < 1 / 2 := by
  rw [rat_lt_half_iff_int, encode_rat_eq, Nat.unpair_pair]
  exact (int_lt_half_iff_encode q.num q.den q.pos).symm

/-- Casting across the threshold comparison. -/
lemma rat_cast_lt_half (q : ℚ) : ((q : ℝ) < 1 / 2 ↔ q < 1 / 2) := by
  have hhalf : (((1 / 2 : ℚ)) : ℝ) = 1 / 2 := by norm_num
  constructor
  · intro h
    have h' : ((q : ℝ)) < (((1 / 2 : ℚ)) : ℝ) := by rw [hhalf]; exact h
    exact_mod_cast h'
  · intro h
    have h' : ((q : ℝ)) < (((1 / 2 : ℚ)) : ℝ) := by exact_mod_cast h
    rw [hhalf] at h'
    exact h'

/-- The threshold comparison is primitive recursive.
Kind `P`; hypotheses `(b)` `encode_rat_eq`, `encode_int_natCast`. -/
lemma primrec_rat_lt_half : Primrec (fun q : ℚ => decide (q < 1 / 2)) := by
  have hnum : Primrec (fun q : ℚ => (Encodable.encode q).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.encode)
  have hden : Primrec (fun q : ℚ => (Encodable.encode q).unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.encode)
  have hmod : PrimrecPred (fun q : ℚ => (Encodable.encode q).unpair.1 % 2 = 1) :=
    Primrec.eq.comp (Primrec.nat_mod.comp hnum (Primrec.const 2)) (Primrec.const 1)
  have hlt : PrimrecPred (fun q : ℚ =>
      (Encodable.encode q).unpair.1 < (Encodable.encode q).unpair.2) :=
    Primrec.nat_lt.comp hnum hden
  exact (PrimrecPred.or hmod hlt).decide.of_eq
    (fun q => decide_eq_decide.mpr (rat_lt_half_iff_encode q))

/-! ## The diagonal at threshold `1/2` -/

/-- The canonical `p = 1/2` paradox-resistance quotation package over the constructed
`LIA`, built from the **unperturbed** market's own quote program.  The width is the
harmonic family `1/(n+1)`.
Kind `Def`; hypotheses `(b)` `paradoxResistanceQuoteOfDiagonal`,
`harmonicWeight_polyRatCodes`. -/
noncomputable def cxQuote :
    ParadoxResistanceQuote (liaHistory (theoremDP T)) (theoremDP T) (1 / 2) :=
  paradoxResistanceQuoteOfDiagonal (quotationPresentation T)
    (theoremMarketComputation T) (1 / 2) (fun n : ℕ => 1 / ((n : ℚ) + 1))
    harmonicWeight_polyRatCodes
    (PolyRatCodes.inv_of_pos harmonicWeight_polyRatCodes (fun n => by positivity))
    (fun n => by positivity)
    (by
      have h : ∀ n : ℕ, ((1 / ((n : ℚ) + 1) : ℚ) : ℝ) = 1 / ((n : ℝ) + 1) := by
        intro n; push_cast; ring
      simpa only [h] using tendsto_one_div_add_atTop_nhds_zero_nat)

/-- The Boolean quotation code behind that diagonal.  Naming it separately is what makes
the sentence family's *whole-value* code available (`BooleanQuoteCode.sentence_poly`); the
`ParadoxResistanceQuote` above carries only the symbol-metered `RpnSentenceCodes`, which
the day-`0` quote program cannot use. -/
noncomputable def cxQuoteCode := (theoremDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode

/-- The diagonal family: `χ n` holds exactly when its own day-`n` price is below `1/2`. -/
noncomputable def cxDiagonal : ℕ → Sentence := (cxQuoteCode T).sentence

/-- The diagonal family is efficiently codeable as whole values.
Kind `C`; hypotheses `(b)` `BooleanQuoteCode.sentence_poly`. -/
lemma cxDiagonal_poly : PolySentenceCodes (cxDiagonal T) :=
  (cxQuoteCode T).sentence_poly

/-- The paradox-resistance package is stated about exactly this family.
Kind `T`. -/
lemma cxQuote_sentence : (cxQuote T).sentence = cxDiagonal T := rfl

/-- The perturbed market: the constructed `LIA` with day `0` republished as the advice
table. -/
noncomputable def cxPerturbed : History :=
  advicePerturbed (liaHistory (theoremDP T)) (theoremDP T) (cxDiagonal T)

/-! ### The perturbed quote table

The advice atoms are recognised arithmetically off the sentence code — an atom's code is
`⟪1, x⟫ + 1` — so no `Primcodable Sentence` decoding is needed and the recogniser is
plainly primitive recursive. -/

/-- The atom tag carried by a sentence code; `0` when the code is not an atom's. -/
private def advTag (c : ℕ) : ℕ :=
  if (c - 1).unpair.1 = 1 then (c - 1).unpair.2.unpair.1 else 0

/-- The advice index carried by a sentence code. -/
private def advIdx (c : ℕ) : ℕ := (c - 1).unpair.2.unpair.2

private lemma encode_atom_code (x : ℕ) :
    Encodable.encode (LO.Propositional.Formula.atom x : Sentence) = Nat.pair 1 x + 1 := rfl

private lemma advTag_schedAtom (m : ℕ) : advTag (Encodable.encode (schedAtom m)) = 6 := by
  simp [advTag, schedAtom, encode_atom_code, Nat.unpair_pair]

private lemma advIdx_schedAtom (m : ℕ) : advIdx (Encodable.encode (schedAtom m)) = m := by
  simp [advIdx, schedAtom, encode_atom_code, Nat.unpair_pair]

private lemma advTag_signAtom (m : ℕ) : advTag (Encodable.encode (signAtom m)) = 7 := by
  simp [advTag, signAtom, encode_atom_code, Nat.unpair_pair]

private lemma advIdx_signAtom (m : ℕ) : advIdx (Encodable.encode (signAtom m)) = m := by
  simp [advIdx, signAtom, encode_atom_code, Nat.unpair_pair]

/-- A nonzero tag identifies the code as that of a tagged atom. -/
private lemma eq_atom_of_advTag {c t : ℕ} (ht : t ≠ 0) (h : advTag c = t) :
    c = Encodable.encode
      (LO.Propositional.Formula.atom (Nat.pair t (advIdx c)) : Sentence) := by
  by_cases hc : (c - 1).unpair.1 = 1
  · have h6 : (c - 1).unpair.2.unpair.1 = t := by rw [advTag, if_pos hc] at h; exact h
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hz : advTag 0 = 0 := by simp [advTag]
      omega
    have e2 : Nat.pair t (advIdx c) = (Nat.unpair (c - 1)).2 := by
      rw [advIdx, ← h6]; exact Nat.pair_unpair _
    have key : Nat.pair 1 (Nat.pair t (advIdx c)) = c - 1 := by
      rw [e2]
      conv_rhs => rw [← Nat.pair_unpair (c - 1)]
      rw [hc]
    rw [encode_atom_code, key]
    omega
  · rw [advTag, if_neg hc] at h
    exact absurd h.symm ht

private lemma advTag_prim : Primrec advTag := by
  have hpred : Primrec (fun c : ℕ => c - 1) :=
    Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  have h1 : Primrec (fun c : ℕ => (c - 1).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hpred)
  have h2 : Primrec (fun c : ℕ => (c - 1).unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hpred)))
  exact Primrec.ite (Primrec.eq.comp h1 (Primrec.const 1)) h2 (Primrec.const 0)

private lemma advIdx_prim : Primrec advIdx := by
  have hpred : Primrec (fun c : ℕ => c - 1) :=
    Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hpred)))

/-- The day-`0` advice row as a rational quote table. -/
noncomputable def cxRow (c : ℕ) : ℚ :=
  cond (decide (advTag c = 6))
    (cond (gateBool (liaHistory (theoremDP T)) (theoremDP T) (cxDiagonal T) (advIdx c)) 1 0)
    (cond (decide (advTag c = 7))
      (cond (decide ((theoremMarketComputation T).quote (advIdx c)
          (Encodable.encode (cxDiagonal T (advIdx c))) < 1 / 2)) 1 0)
      ((theoremMarketComputation T).quote 0 c))

/-- The perturbed market's quote table: the advice row on day `0`, the original table
after. -/
noncomputable def cxTable (n c : ℕ) : ℚ :=
  if n = 0 then cxRow T c else (theoremMarketComputation T).quote n c

/-- **The table is exact.**
Kind `P`; hypotheses `(a)`. -/
lemma cxPerturbed_eq_cxTable (n : ℕ) (φ : Sentence) :
    cxPerturbed T n φ = ((cxTable T n (Encodable.encode φ) : ℚ) : ℝ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [cxTable, if_pos rfl]
    by_cases hs : ∃ m, φ = schedAtom m
    · obtain ⟨m, rfl⟩ := hs
      rw [cxRow, advTag_schedAtom, advIdx_schedAtom, cxPerturbed, advicePerturbed,
        advicePerturb_zero_schedAtom, gateBit]
      by_cases hg : ∃ j, sched (liaHistory (theoremDP T)) (theoremDP T) (cxDiagonal T) j = m
      · rw [if_pos hg, (gateBool_eq_true_iff _ _ _ m).2 hg]
        norm_num
      · rw [if_neg hg]
        have : gateBool (liaHistory (theoremDP T)) (theoremDP T) (cxDiagonal T) m = false := by
          rcases hb : gateBool (liaHistory (theoremDP T)) (theoremDP T) (cxDiagonal T) m with _ | _
          · rfl
          · exact absurd ((gateBool_eq_true_iff _ _ _ m).1 hb) hg
        rw [this]
        norm_num
    · by_cases hi : ∃ m, φ = signAtom m
      · obtain ⟨m, rfl⟩ := hi
        rw [cxRow, advTag_signAtom, advIdx_signAtom, cxPerturbed, advicePerturbed,
          advicePerturb_zero_signAtom, signBit,
          (theoremMarketComputation T).quote_exact m (cxDiagonal T m)]
        have hcast := rat_cast_lt_half
        by_cases hlt : (theoremMarketComputation T).quote m
            (Encodable.encode (cxDiagonal T m)) < 1 / 2
        · rw [if_pos ((hcast _).2 hlt), decide_eq_true hlt]
          norm_num
        · rw [if_neg (fun hh => hlt ((hcast _).1 hh)), decide_eq_false hlt]
          norm_num
      · push Not at hs hi
        have h6 : advTag (Encodable.encode φ) ≠ 6 := fun h =>
          hs _ (Encodable.encode_injective (eq_atom_of_advTag (by omega) h))
        have h7 : advTag (Encodable.encode φ) ≠ 7 := fun h =>
          hi _ (Encodable.encode_injective (eq_atom_of_advTag (by omega) h))
        rw [cxRow, cxPerturbed, advicePerturbed, advicePerturb, if_pos rfl,
          adviceRow_of_not_advice _ _ _ _ hs hi,
          (theoremMarketComputation T).quote_exact 0 φ]
        simp [h6, h7]
  · rw [cxTable, if_neg (by omega), cxPerturbed, advicePerturbed, advicePerturb,
      if_neg (by omega)]
    exact (theoremMarketComputation T).quote_exact n φ

end Computability

lemma cxTable_eq_cond (n c : ℕ) :
    cxTable T n c = cond (decide (n = 0)) (cxRow T c)
      ((theoremMarketComputation T).quote n c) := by
  by_cases h : n = 0 <;> simp [cxTable, h]

/-- The certified program for the constructed process. -/
noncomputable def cxProcessComputation : DeductiveProcessComputation (theoremDP T) :=
  (theoremDP_computable T).nonemptyComputation.some

/-- Kind `C`; hypotheses `(a)`. -/
lemma computable_cxDiagonal : Computable (cxDiagonal T) := by
  obtain ⟨c, hc⟩ := cxDiagonal_poly T
  exact Computable.encode_iff.mp hc.primrec.to_comp

/-- Kind `C`; hypotheses `(a)`. -/
lemma computable_cxQuoteAt : Computable (fun m : ℕ =>
    (theoremMarketComputation T).quote m (Encodable.encode (cxDiagonal T m))) :=
  ((computable_quote (theoremMarketComputation T)).comp
    (Primrec₂.natPair.to_comp.comp Computable.id
      (Computable.encode.comp (computable_cxDiagonal T)))).of_eq
    (fun _ => by simp [Nat.unpair_pair])

/-- Kind `C`; hypotheses `(a)`. -/
lemma computable_cxLt : Computable
    (fun m => decide (liaHistory (theoremDP T) m (cxDiagonal T m) < 1 / 2)) :=
  (primrec_rat_lt_half.to_comp.comp (computable_cxQuoteAt T)).of_eq (fun m => by
    rw [(theoremMarketComputation T).quote_exact m (cxDiagonal T m)]
    exact decide_eq_decide.mpr (rat_cast_lt_half _).symm)

/-- The diagonal dichotomy for the unperturbed market, at every day. -/
lemma cxDichotomy : ∀ m, 1 ≤ m →
    Dichotomy (liaHistory (theoremDP T)) (theoremDP T) (cxDiagonal T) m :=
  fun m hm => dichotomy_of_paradoxQuote (cxQuote T) (fun _ _ _ => rfl) hm

/-- Kind `C`; hypotheses `(a)`. -/
lemma computable_cxSched :
    Computable (sched (liaHistory (theoremDP T)) (theoremDP T) (cxDiagonal T)) :=
  computable_sched (cxDichotomy T)
    (computable_settleTotal (cxDichotomy T) (computable_cxDiagonal T) (computable_cxLt T)
      (computable_stage (cxProcessComputation T)))

/-- **The perturbed quote table is computable.**
Kind `C`; hypotheses `(a)`. -/
lemma computable_cxTable : Computable (fun z : ℕ => cxTable T z.unpair.1 z.unpair.2) := by
  have hM := computable_quote (theoremMarketComputation T)
  have hgate := computable_gateBool (computable_cxSched T)
  have hidx : Computable advIdx := advIdx_prim.to_comp
  have hrow : Computable (cxRow T) := by
    have h6 : Computable (fun c : ℕ => decide (advTag c = 6)) :=
      (Primrec.eq.comp advTag_prim (Primrec.const 6)).decide.to_comp
    have h7 : Computable (fun c : ℕ => decide (advTag c = 7)) :=
      (Primrec.eq.comp advTag_prim (Primrec.const 7)).decide.to_comp
    have ha : Computable (fun c : ℕ =>
        cond (gateBool (liaHistory (theoremDP T)) (theoremDP T) (cxDiagonal T) (advIdx c))
          (1 : ℚ) 0) :=
      Computable.cond (hgate.comp hidx) (Computable.const 1) (Computable.const 0)
    have hb : Computable (fun c : ℕ =>
        cond (decide ((theoremMarketComputation T).quote (advIdx c)
          (Encodable.encode (cxDiagonal T (advIdx c))) < 1 / 2)) (1 : ℚ) 0) :=
      Computable.cond
        ((primrec_rat_lt_half.to_comp.comp (computable_cxQuoteAt T)).comp hidx)
        (Computable.const 1) (Computable.const 0)
    have hd : Computable (fun c : ℕ => (theoremMarketComputation T).quote 0 c) :=
      (hM.comp (Primrec₂.natPair.to_comp.comp (Computable.const 0) Computable.id)).of_eq
        (fun c => by simp [Nat.unpair_pair])
    exact Computable.cond h6 ha (Computable.cond h7 hb hd)
  have hz : Computable (fun z : ℕ => decide (z.unpair.1 = 0)) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)).decide.to_comp
  have hsnd : Computable (fun z : ℕ => z.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp
  exact (Computable.cond hz (hrow.comp hsnd) (hM.of_eq (fun z => rfl))).of_eq
    (fun z => (cxTable_eq_cond T z.unpair.1 z.unpair.2).symm)

/-! ## Computability of the perturbed market -/

/-- **The perturbed market is computable** (`def:marketprocess`): prices in `[0,1]` from
`advicePerturbed_mem_Icc` over the constructed inductor's own market, the rational table
`cxTable`, and a `Nat.Partrec.Code` for it.

The day-`0` row is a search, and it terminates for the reasons assembled above:
`settleStage` is `Nat.find` over a Boolean test that `stageEntails` decides
(`settledTest_eq_true_iff`), so `Computable.find` applies with the existence supplied by
compactness — no constructive stage bound; `sched` follows by `Computable.nat_rec` on that
step; the gate bit is the bounded search licensed by `le_sched`; and the sign bit is a
rational comparison built from `encode_rat_eq`.  `sched_congr` and `settleStage_congr` are
what make all of it a function of the *unperturbed* market alone, so the day-`0` row does
not refer to itself.
Kind `C`; hypotheses `(a)`. -/
theorem computableMarket_cxPerturbed : ComputableMarket (cxPerturbed T) := by
  refine ⟨fun n φ => advicePerturbed_mem_Icc (theoremDP T) (cxDiagonal T)
    (fun m ψ => (LIA_isMachineLogicalInductor (theoremDP T)
      (theoremDP_computable T)).marketComputable.1 m ψ) n φ, ?_⟩
  have hcomp : Computable (fun z : ℕ =>
      Encodable.encode (cxTable T z.unpair.1 z.unpair.2)) :=
    Computable.encode.comp (computable_cxTable T)
  have hpart : Nat.Partrec (fun z : ℕ =>
      Part.some (Encodable.encode (cxTable T z.unpair.1 z.unpair.2))) :=
    Partrec.nat_iff.mp hcomp.partrec
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hpart
  refine ⟨cxTable T, code, cxPerturbed_eq_cxTable T, fun z => ?_⟩
  rw [hcode]
  simp

/-! ## The witness, and the refutation -/

include T in
/-- The advice perturbation refuting `thm:ifp`, over any Σ₁-sound Δ₁ theory extending
`𝗜𝚺₁`.  Refutes rather than renders, so no `Paper node:` line.
Kind `C`; hypotheses `(a)`. -/
theorem exists_advice_perturbation_ofTheory :
    ∃ (P P' : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (Tr : Trader),
      IsMachineLogicalInductor P DP ∧ ComputableMarket P' ∧
      (∀ n, 1 ≤ n → ∀ φ, P n φ = P' n φ) ∧ MachineEfficientTrader Tr ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) ∧
      (∀ j, Dichotomy P' DP χ (sched P' DP χ j)) ∧
      (∀ (v : PCWorld) i, (∀ j, sched P' DP χ j ≠ i) →
        (Tr.strat i).value P' v.payout = 0) ∧
      (∀ (v : PCWorld) j, (Tr.strat (sched P' DP χ j)).value P' v.payout
        = roundValue P' χ v (sched P' DP χ j)) :=
  ⟨liaHistory (theoremDP T), cxPerturbed T, theoremDP T, cxDiagonal T,
    adviceTrader schedAtom signAtom (cxDiagonal T),
    LIA_isMachineLogicalInductor (theoremDP T) (theoremDP_computable T),
    computableMarket_cxPerturbed T,
    advicePerturbed_agree _ _ _,
    adviceTrader_efficient rpnSentenceCodes_schedAtom rpnSentenceCodes_signAtom
      (RpnSentenceCodes.ofPolySentenceCodes (cxDiagonal_poly T)),
    fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩,
    fun j => dichotomy_of_paradoxQuote (cxQuote T) (advicePerturbed_agree _ _ _)
      (one_le_sched _ _ _ j),
    fun v i hi => adviceTrader_value_off_sched schedAtom signAtom (cxDiagonal T) _ _
      (advicePerturbed_schedAtom_off _ _ _) v i hi,
    fun v j => adviceTrader_value_on_sched schedAtom signAtom (cxDiagonal T) _ _
      (advicePerturbed_schedAtom_on _ _ _) (advicePerturbed_signAtom_on _ _ _) v j⟩

include T in
/-- **The unrestricted finite-day perturbation statement is false**, over any Σ₁-sound Δ₁
theory extending `𝗜𝚺₁` — the negation of the paper's `thm:ifp` as printed, at the paper's
own quantifier.

Fully proved and axiom-clean.  Refutes rather than renders, so no `Paper node:` line.
Kind `C`; hypotheses `(a)`. -/
theorem not_overgeneral_ifp_ofTheory :
    ¬ ∀ (P P' : History) (DP : DeductiveProcess) (N : ℕ),
        IsMachineLogicalInductor P DP → ComputableMarket P' →
        (∀ n, N ≤ n → ∀ φ, P n φ = P' n φ) → IsMachineLogicalInductor P' DP := by
  obtain ⟨P, P', DP, χ, Tr, hLI, hP', hagree, hTr, hworld, hdicho, hzero, hval⟩ :=
    exists_advice_perturbation_ofTheory T
  exact not_overgeneral_ifp_of_advice P P' DP χ Tr hLI hP' hagree hTr hworld hdicho
    hzero hval

/-- The advice perturbation refuting `thm:ifp`, closed at `𝗜𝚺₁` — which is `Δ₁`-definable
(`ISigma1_delta1Definable`), extends itself, and is Σ₁-sound because `ℕ ⊧* 𝗜𝚺₁`.  Refutes
rather than renders, so no `Paper node:` line.
Kind `C`; hypotheses `(a)`. -/
theorem exists_advice_perturbation :
    ∃ (P P' : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (Tr : Trader),
      IsMachineLogicalInductor P DP ∧ ComputableMarket P' ∧
      (∀ n, 1 ≤ n → ∀ φ, P n φ = P' n φ) ∧ MachineEfficientTrader Tr ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) ∧
      (∀ j, Dichotomy P' DP χ (sched P' DP χ j)) ∧
      (∀ (v : PCWorld) i, (∀ j, sched P' DP χ j ≠ i) →
        (Tr.strat i).value P' v.payout = 0) ∧
      (∀ (v : PCWorld) j, (Tr.strat (sched P' DP χ j)).value P' v.payout
        = roundValue P' χ v (sched P' DP χ j)) :=
  exists_advice_perturbation_ofTheory 𝗜𝚺₁

/-- **The unrestricted finite-day perturbation statement is false** — the negation of the
paper's `thm:ifp` as printed, at the paper's own quantifier, with no theory parameter.

Fully proved and axiom-clean.  This declaration *refutes* rather than renders `thm:ifp`,
and it carries the node so that the refutation is on the checked gates and on the
read-through page: `thm:ifp` is the one node whose printed statement is false, and the
canonical public view of it must lead with this theorem and with the corrected
replacement `FreezeOracle.machine_lic_iff_of_recognizableSupport`.  See
`notes/paper-errata.md` PE1.
Kind `C`; hypotheses `(a)`.
Paper node: `thm:ifp` -/
theorem not_overgeneral_ifp :
    ¬ ∀ (P P' : History) (DP : DeductiveProcess) (N : ℕ),
        IsMachineLogicalInductor P DP → ComputableMarket P' →
        (∀ n, N ≤ n → ∀ φ, P n φ = P' n φ) → IsMachineLogicalInductor P' DP :=
  not_overgeneral_ifp_ofTheory 𝗜𝚺₁






#print axioms LogicalInduction.FinitePerturbationCounterexample.computableMarket_cxPerturbed
#print axioms LogicalInduction.FinitePerturbationCounterexample.exists_advice_perturbation
#print axioms LogicalInduction.FinitePerturbationCounterexample.not_overgeneral_ifp

end FinitePerturbationCounterexample
end LogicalInduction
