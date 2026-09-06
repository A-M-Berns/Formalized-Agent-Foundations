import LogicalInduction.Construction.Knowledge.SubstEmission
import LogicalInduction.Framework.Theory.R0Instances
import LogicalInduction.Construction.Quotation.MarketQuoteCodes
import LogicalInduction.Construction.Quotation.ExactProduct

/-!
# The deferred CCEE weight as a literal first-order LUV

`thm:ccee` multiplies a source LUV by a deferred `[0,1]` weight `w (f n)`.  On the
threshold-only `LUV` interface that product is only reachable through a mesh
(`dd:mesh`), because nothing in that interface *names* the weight's value.  The literal
frontend (`PaperLUV`) does name values — by a numerator/denominator pair code — so an
exact same-market product needs the weight itself presented as a `PaperLUVSeq`.

This module builds that presentation, from the paper's own standing hypothesis on the
background theory (`RepresentsComputations`, tex:600-606) and nothing else:

* `deferredWeightPairCode` is the total computable function `n ↦ ⟪num, den⟫` of the
  deferred weight, computable because `w` is P-generable (`def:ece`) and `f` is a
  deferral function;
* `RepresentsComputations` hands back a two-variable formula `γ` whose `T`-provable value
  graph is that function, and `representedPairPaperLUV` reads `γ(n̄, ·)` as a literal paper
  LUV — uniqueness is the representation biconditional, unit-interval membership is the
  standard-natural fact `num ≤ den`, transported into every model of `T` along
  `coe_pair_eq_pair_coe`;
* `representedPairPaperLUV_valuesAt` computes its completed-world value *exactly*, as
  `num / den`, by two unconditional threshold derivations;
* `representedPairPaperLUVSeq` adds the `def:ec` certificate — the defining formulas are
  numeral substitution instances of one fixed `γ`, which is exactly what
  `polyArithmeticFormulaSeq_subst_numeral` meters — and `deferredWeightPaperLUVSeq`
  specialises the whole package to the deferred weight.

`representedPairPaperLUV_valuesAt` and `deferredWeightPaperLUVSeq_valuesAt` are what the
module exists to supply: they are the exact completed-world values that
`lic_no_expected_net_update_conditional_paperLUV_closed`
(`Construction/Quotation/ExactCCEE.lean`) feeds into the generic trading argument at
`slack = 0`.

*Proof kind:* `P`/`C`; hypotheses `(a)` throughout, save the theory-level premise
`RepresentsComputations T`, which is the paper's own `(b)`-style standing assumption and is
realized at `𝗣𝗔⁻`, `𝗜𝚺₁` and `𝗣𝗔` (`Framework/Theory/R0Instances.lean`).  Note that
`RepresentsComputations` is *anti*-monotone in `T`, so it stays an instance binder rather
than being discharged here.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder.Arithmetic

/-! ## The deferred weight's pair code -/

/-- The pair code of the deferred weight at day `n`: numerator absolute value paired with
denominator.  For `w (f n) ∈ [0,1]` this is a faithful name of the value, and it is the
function the background theory is asked to represent. -/
def deferredWeightPairCode (f : DeferralFunction) (w : ℕ → ℚ) (n : ℕ) : ℕ :=
  Nat.pair (w (f n)).num.natAbs (w (f n)).den

private lemma encode_nonneg_rat {q : ℚ} (hq : 0 ≤ q) :
    Encodable.encode q = Nat.pair (2 * q.num.natAbs) q.den := by
  rw [encode_rat_eq]
  congr 1
  have h : q.num = (q.num.natAbs : ℤ) := (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)).symm
  rw [h, encode_int_natCast]
  exact congrArg (2 * ·) (Int.natAbs_natCast q.num.natAbs).symm

private lemma deferredWeightPairCode_eq (f : DeferralFunction) (w : ℕ → ℚ)
    (hw0 : ∀ n, 0 ≤ w n) (n : ℕ) :
    deferredWeightPairCode f w n =
      Nat.pair (Nat.div2 (Encodable.encode (w (f n))).unpair.1)
        (Encodable.encode (w (f n))).unpair.2 := by
  rw [deferredWeightPairCode, encode_nonneg_rat (hw0 _), Nat.unpair_pair]
  simp [Nat.div2_val]

/-- The deferred weight's pair code is total computable, so `RepresentsComputations` applies
to it.  The route is the market's own feature presentation (`PGenerableRat.computable`)
composed with the deferral function's code, followed by the primitive-recursive
numerator/denominator split of the *repo's* `Primcodable ℚ` instance, read off
`encode_rat_eq`: for `0 ≤ q` the code is `⟪2 · |num|, den⟫`, so halving the left component
recovers `|num|`.  Kind `C`; hypotheses `(a)`. -/
lemma deferredWeightPairCode_computable {P : History} (market : MarketComputation P)
    (f : DeferralFunction) (w : ℕ → ℚ) (hw : PGenerableRat P w)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) :
    Computable (deferredWeightPairCode f w) := by
  have hwf : Computable (fun n => w (f n)) := (hw.computable market).comp f.computable
  have henc : Computable (fun n => Encodable.encode (w (f n))) :=
    Primrec.encode.to_comp.comp hwf
  have h1 : Computable (fun n => Nat.div2 (Encodable.encode (w (f n))).unpair.1) :=
    (Primrec.nat_div2.comp (Primrec.fst.comp Primrec.unpair)).to_comp.comp henc
  have h2 : Computable (fun n => (Encodable.encode (w (f n))).unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp henc
  exact (Primrec₂.natPair.to_comp.comp h1 h2).of_eq fun n =>
    (deferredWeightPairCode_eq f w (fun n => (weight_mem n).1) n).symm

private lemma cross_lt_of_lt_div {a b : ℕ} {r : ℚ} (hb : 0 < b) (hr : 0 ≤ r)
    (h : (r : ℝ) < (a : ℝ) / (b : ℝ)) :
    r.num.natAbs * b < a * r.den := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h1 : (r : ℝ) * (b : ℝ) < (a : ℝ) := (lt_div_iff₀ hbR).mp h
  have h2 : r * (b : ℚ) < (a : ℚ) := by exact_mod_cast h1
  have hd : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.den_pos
  have h3 : ((r.num.natAbs : ℚ)) * (b : ℚ) < (a : ℚ) * (r.den : ℚ) := by
    rw [natAbs_num_cast hr]
    calc r * (r.den : ℚ) * (b : ℚ) = (r * (b : ℚ)) * (r.den : ℚ) := by ring
      _ < (a : ℚ) * (r.den : ℚ) := mul_lt_mul_of_pos_right h2 hd
  exact_mod_cast h3

private lemma cross_le_of_div_lt {a b : ℕ} {r : ℚ} (hb : 0 < b)
    (h : (a : ℝ) / (b : ℝ) < (r : ℝ)) :
    a * r.den ≤ r.num.natAbs * b := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hnn : (0 : ℝ) ≤ (a : ℝ) / (b : ℝ) := div_nonneg (by positivity) hbR.le
  have hr0 : 0 ≤ r := by
    have : (0 : ℝ) < (r : ℝ) := lt_of_le_of_lt hnn h
    exact_mod_cast this.le
  have h1 : (a : ℝ) < (r : ℝ) * (b : ℝ) := (div_lt_iff₀ hbR).mp h
  have h2 : (a : ℚ) < r * (b : ℚ) := by exact_mod_cast h1
  have hd : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.den_pos
  have h3 : (a : ℚ) * (r.den : ℚ) < ((r.num.natAbs : ℚ)) * (b : ℚ) := by
    rw [natAbs_num_cast hr0]
    calc (a : ℚ) * (r.den : ℚ) < (r * (b : ℚ)) * (r.den : ℚ) := mul_lt_mul_of_pos_right h2 hd
      _ = r * (r.den : ℚ) * (b : ℚ) := by ring
  exact le_of_lt (by exact_mod_cast h3)

/-- Every model of `T` is a model of `𝗜𝗢𝗽𝗲𝗻`, along `𝗜𝗢𝗽𝗲𝗻 ⪯ 𝗜𝚺₁ ⪯ T`.  This is the
opening move of each completeness argument below. -/
private lemma models_iOpen_of_models (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T]
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] :
    M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
    Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance

/-! ## A represented pair code as a literal paper LUV -/

section Represented

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- **A represented pair code read as a literal paper LUV.**  If `T` proves the value graph
of `g` in the representation form, and each `g n` is a pair code of a fraction in `[0,1]`,
then `γ(n̄, ·)` *is* a literal paper LUV: unique existence is the representation
biconditional itself, and unit-interval membership is the standard-natural fact
`(g n).unpair.1 ≤ (g n).unpair.2` transported into every model of `T`.  No soundness
assumption is used — only `T`-derivations and completeness over models of `T`.
Kind `C`; hypotheses `(a)`.
Paper node: `def:luv` -/
noncomputable def representedPairPaperLUV
    (γ : ArithmeticSemisentence 2) (g : ℕ → ℕ)
    (hγ : ∀ n y : ℕ, y = g n ↔
      T ⊢ (∀⁰ (Semiformula.subst γ ![‘↑n’, #0] 🡘 (“#0 = ↑y” : ArithmeticSemisentence 1))))
    (hmem : ∀ n, (g n).unpair.1 ≤ (g n).unpair.2 ∧ 0 < (g n).unpair.2)
    (n : ℕ) : PaperLUV T where
  formula := Semiformula.subst γ ![‘↑n’, #0]
  unique := by
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    haveI := models_iOpen_of_models T M
    have hrep := models_of_provable hM ((hγ n (g n)).mp rfl)
    simp [models_iff] at hrep ⊢
    exact ⟨_, (hrep _).mpr rfl, fun y hy => (hrep y).mp hy⟩
  unit := by
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    haveI := models_iOpen_of_models T M
    have hrep := models_of_provable hM ((hγ n (g n)).mp rfl)
    simp [models_iff, LO.FirstOrder.Arithmetic.numeral_eq_natCast] at hrep ⊢
    simp [paperRatUnitDef, pairDef, ← pair_graph]
    intro x hx
    rw [(hrep x).mp hx]
    obtain ⟨hle, hpos⟩ := hmem n
    refine ⟨((g n).unpair.1 : M), ((g n).unpair.2 : M), ?_, ?_, ?_⟩
    · conv_lhs => rw [← Nat.pair_unpair (g n)]
      exact LO.FirstOrder.Arithmetic.coe_pair_eq_pair_coe _ _
    · exact_mod_cast hpos
    · exact_mod_cast hle

/-- The defining formula of a represented paper LUV is the numeral substitution instance. -/
@[simp] lemma representedPairPaperLUV_formula
    (γ : ArithmeticSemisentence 2) (g : ℕ → ℕ)
    (hγ : ∀ n y : ℕ, y = g n ↔
      T ⊢ (∀⁰ (Semiformula.subst γ ![‘↑n’, #0] 🡘 (“#0 = ↑y” : ArithmeticSemisentence 1))))
    (hmem : ∀ n, (g n).unpair.1 ≤ (g n).unpair.2 ∧ 0 < (g n).unpair.2)
    (n : ℕ) :
    (representedPairPaperLUV T γ g hγ hmem n).formula = Semiformula.subst γ ![‘↑n’, #0] := rfl

/-! ## Threshold provability and the exact completed-world value -/

/-- Below the represented value, the threshold sentence is a theorem of `T`.  For a negative
threshold this is well-formedness alone; otherwise it is cross multiplication against the
represented pair, decided among the standard naturals and cast into the model.
Kind `P`; hypotheses `(a)`. -/
lemma representedPairPaperLUV_threshold_provable
    (γ : ArithmeticSemisentence 2) (g : ℕ → ℕ)
    (hγ : ∀ n y : ℕ, y = g n ↔
      T ⊢ (∀⁰ (Semiformula.subst γ ![‘↑n’, #0] 🡘 (“#0 = ↑y” : ArithmeticSemisentence 1))))
    (hmem : ∀ n, (g n).unpair.1 ≤ (g n).unpair.2 ∧ 0 < (g n).unpair.2)
    (n : ℕ) {r : ℚ}
    (hlt : (r : ℝ) < ((g n).unpair.1 : ℝ) / ((g n).unpair.2 : ℝ)) :
    T ⊢ (representedPairPaperLUV T γ g hγ hmem n).thresholdFormula r := by
  by_cases hr : r < 0
  · exact PaperLUV.threshold_provable_of_neg _ r hr
  · have hr0 : 0 ≤ r := not_lt.mp hr
    have hcross : r.num.natAbs * (g n).unpair.2 < (g n).unpair.1 * r.den :=
      cross_lt_of_lt_div (hmem n).2 hr0 hlt
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    haveI := models_iOpen_of_models T M
    have hrep := models_of_provable hM ((hγ n (g n)).mp rfl)
    simp [models_iff, LO.FirstOrder.Arithmetic.numeral_eq_natCast] at hrep
    simp only [models_iff, PaperLUV.thresholdFormula, representedPairPaperLUV_formula]
    simp [paperRatGtDef, hr, pairDef, ← pair_graph,
      LO.FirstOrder.Arithmetic.numeral_eq_natCast]
    intro x hx
    rw [(hrep x).mp hx]
    refine ⟨((g n).unpair.1 : M), ((g n).unpair.2 : M), ?_, ?_, ?_⟩
    · conv_lhs => rw [← Nat.pair_unpair (g n)]
      exact LO.FirstOrder.Arithmetic.coe_pair_eq_pair_coe _ _
    · exact_mod_cast (hmem n).2
    · exact_mod_cast hcross

/-- Above the represented value, the negated threshold sentence is a theorem of `T`.
Kind `P`; hypotheses `(a)`. -/
lemma representedPairPaperLUV_threshold_refutable
    (γ : ArithmeticSemisentence 2) (g : ℕ → ℕ)
    (hγ : ∀ n y : ℕ, y = g n ↔
      T ⊢ (∀⁰ (Semiformula.subst γ ![‘↑n’, #0] 🡘 (“#0 = ↑y” : ArithmeticSemisentence 1))))
    (hmem : ∀ n, (g n).unpair.1 ≤ (g n).unpair.2 ∧ 0 < (g n).unpair.2)
    (n : ℕ) {r : ℚ}
    (hgt : ((g n).unpair.1 : ℝ) / ((g n).unpair.2 : ℝ) < (r : ℝ)) :
    T ⊢ ∼(representedPairPaperLUV T γ g hγ hmem n).thresholdFormula r := by
  have hcross : (g n).unpair.1 * r.den ≤ r.num.natAbs * (g n).unpair.2 :=
    cross_le_of_div_lt (hmem n).2 hgt
  have hr : ¬ r < 0 := by
    have hbR : (0 : ℝ) < (((g n).unpair.2 : ℕ) : ℝ) := by exact_mod_cast (hmem n).2
    have hnn : (0 : ℝ) ≤ ((g n).unpair.1 : ℝ) / ((g n).unpair.2 : ℝ) :=
      div_nonneg (by positivity) hbR.le
    have : (0 : ℝ) < (r : ℝ) := lt_of_le_of_lt hnn hgt
    exact not_lt.mpr (by exact_mod_cast this.le)
  apply LO.FirstOrder.Arithmetic.complete T
  intro (M : Type) _ hM
  haveI := models_iOpen_of_models T M
  have hrep := models_of_provable hM ((hγ n (g n)).mp rfl)
  simp [models_iff, LO.FirstOrder.Arithmetic.numeral_eq_natCast] at hrep
  simp only [models_iff, PaperLUV.thresholdFormula, representedPairPaperLUV_formula]
  simp [paperRatGtDef, hr, pairDef, ← pair_graph,
    LO.FirstOrder.Arithmetic.numeral_eq_natCast]
  have hpaircast : ((g n : ℕ) : M) =
      LO.FirstOrder.Arithmetic.pair ((g n).unpair.1 : M) ((g n).unpair.2 : M) := by
    conv_lhs => rw [← Nat.pair_unpair (g n)]
    exact LO.FirstOrder.Arithmetic.coe_pair_eq_pair_coe _ _
  refine ⟨((g n : ℕ) : M), (hrep _).mpr rfl, ?_⟩
  intro c d hcd _
  rw [hpaircast] at hcd
  obtain ⟨rfl, rfl⟩ := LO.FirstOrder.Arithmetic.pair_ext_iff.mp hcd
  exact_mod_cast hcross

/-- **The exact completed-world value of a represented paper LUV.**  Every completed world of
the canonical first-order theorem process values it at exactly `num / den` — no mesh, no
slack.  Kind `C`; hypotheses `(a)`.
Paper node: `def:luv` -/
lemma representedPairPaperLUV_valuesAt
    (γ : ArithmeticSemisentence 2) (g : ℕ → ℕ)
    (hγ : ∀ n y : ℕ, y = g n ↔
      T ⊢ (∀⁰ (Semiformula.subst γ ![‘↑n’, #0] 🡘 (“#0 = ↑y” : ArithmeticSemisentence 1))))
    (hmem : ∀ n, (g n).unpair.1 ≤ (g n).unpair.2 ∧ 0 < (g n).unpair.2)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperTheoryDP T)) :
    v.ValuesAt (representedPairPaperLUV T γ g hγ hmem n).toLUV
      (((g n).unpair.1 : ℝ) / ((g n).unpair.2 : ℝ)) := by
  have hb : (0 : ℝ) < (((g n).unpair.2 : ℕ) : ℝ) := by exact_mod_cast (hmem n).2
  refine ⟨div_nonneg (by positivity) hb.le, ?_, fun r => ⟨?_, ?_⟩⟩
  · rw [div_le_one hb]; exact_mod_cast (hmem n).1
  · intro hlt
    exact PCWorld.holds_paperPrimeDecompose_of_provable T v hv _
      (representedPairPaperLUV_threshold_provable T γ g hγ hmem n hlt)
  · intro hgt hHolds
    have h0 := PCWorld.holds_paperPrimeDecompose_of_provable T v hv _
      (representedPairPaperLUV_threshold_refutable T γ g hγ hmem n hgt)
    have h1 : v.Holds (paperPrimeDecompose
        (∼(((representedPairPaperLUV T γ g hγ hmem n).thresholdFormula r :
          ArithmeticSentence) : ArithmeticProposition))) := by
      simpa [LogicalConnective.HomClass.map_neg] using h0
    exact (v.holds_paperPrimeDecompose_neg _).mp h1 hHolds

/-- **The represented family, with its `def:ec` certificate.**  All the defining formulas are
numeral substitution instances of the *one* formula `γ` that `RepresentsComputations`
supplied, so the emitted source run is the fixed skeleton of `γ` plus the day numeral —
which is precisely what `polyArithmeticFormulaSeq_subst_numeral` meters.
Kind `C`; hypotheses `(a)`.
Paper node: `def:luv` -/
noncomputable def representedPairPaperLUVSeq
    (γ : ArithmeticSemisentence 2) (g : ℕ → ℕ)
    (hγ : ∀ n y : ℕ, y = g n ↔
      T ⊢ (∀⁰ (Semiformula.subst γ ![‘↑n’, #0] 🡘 (“#0 = ↑y” : ArithmeticSemisentence 1))))
    (hmem : ∀ n, (g n).unpair.1 ≤ (g n).unpair.2 ∧ 0 < (g n).unpair.2) :
    PaperLUVSeq T where
  luv n := representedPairPaperLUV T γ g hγ hmem n
  source n := ArithSource.ofNNF
    (((Semiformula.subst γ ![‘↑n’, #0] : ArithmeticSemisentence 1) :
      ArithmeticSemiformula ℕ 1))
  compiles _ := rfl
  structural := (polyArithmeticFormulaSeq_subst_numeral γ).toSource

end Represented

/-! ## The deferred weight family -/

section Deferred

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

private lemma numNatAbs_le_den {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : q.num.natAbs ≤ q.den := by
  have hd : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.den_pos
  have h : ((q.num.natAbs : ℚ)) ≤ (q.den : ℚ) := by
    rw [natAbs_num_cast h0]
    calc q * (q.den : ℚ) ≤ 1 * (q.den : ℚ) := mul_le_mul_of_nonneg_right h1 hd.le
      _ = (q.den : ℚ) := one_mul _
  exact_mod_cast h

private lemma natAbs_div_den {q : ℚ} (h0 : 0 ≤ q) :
    ((q.num.natAbs : ℝ)) / ((q.den : ℝ)) = (q : ℝ) := by
  have h := natAbs_num_cast h0
  have hd : ((q.den : ℝ)) ≠ 0 := by exact_mod_cast q.den_nz
  field_simp
  rw [mul_comm]
  exact_mod_cast h

/-- The pair code unpairs to the numerator/denominator it was built from. -/
@[simp] lemma deferredWeightPairCode_unpair (f : DeferralFunction) (w : ℕ → ℚ) (n : ℕ) :
    (deferredWeightPairCode f w n).unpair = ((w (f n)).num.natAbs, (w (f n)).den) :=
  Nat.unpair_pair _ _

/-- A `[0,1]` weight's pair code names a fraction in `[0,1]`: `|num| ≤ den` and `0 < den`.
Kind `C`; hypotheses `(a)`. -/
lemma deferredWeightPairCode_mem (f : DeferralFunction) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (n : ℕ) :
    (deferredWeightPairCode f w n).unpair.1 ≤ (deferredWeightPairCode f w n).unpair.2 ∧
      0 < (deferredWeightPairCode f w n).unpair.2 := by
  refine ⟨?_, ?_⟩
  · simpa using numNatAbs_le_den (weight_mem (f n)).1 (weight_mem (f n)).2
  · simpa using (w (f n)).den_pos

/-- **The deferred CCEE weight as a literal paper-LUV family.**  The formula is the one the
paper's own standing hypothesis on `Θ` supplies for the computable pair-code function; the
`def:ec` certificate and the completed-world semantics come with it.  This is the object a
same-market *exact* CCEE endpoint multiplies its source `PaperLUVSeq` by.
Kind `C`; hypotheses `(a)`, over the paper's standing premise `RepresentsComputations T`.
Paper node: `def:luv` -/
noncomputable def deferredWeightPaperLUVSeq [RepresentsComputations T]
    {P : History} (market : MarketComputation P)
    (f : DeferralFunction) (w : ℕ → ℚ) (hw : PGenerableRat P w)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) : PaperLUVSeq T :=
  representedPairPaperLUVSeq T
    (RepresentsComputations.repr (T := T) _
      (deferredWeightPairCode_computable market f w hw weight_mem)).choose
    (deferredWeightPairCode f w)
    (RepresentsComputations.repr (T := T) _
      (deferredWeightPairCode_computable market f w hw weight_mem)).choose_spec
    (deferredWeightPairCode_mem f w weight_mem)

/-- **The deferred weight family is valued at the weight.**  Every completed world of the
canonical theorem process values the day-`n` member at exactly `w (f n)`; the pair code's
`|num| / den` is that rational because the weight is nonnegative.
Kind `C`; hypotheses `(a)`.
Paper node: `def:luv` -/
lemma deferredWeightPaperLUVSeq_valuesAt [RepresentsComputations T]
    {P : History} (market : MarketComputation P)
    (f : DeferralFunction) (w : ℕ → ℚ) (hw : PGenerableRat P w)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperTheoryDP T)) :
    v.ValuesAt ((deferredWeightPaperLUVSeq T market f w hw weight_mem).luv n).toLUV
      ((w (f n) : ℝ)) := by
  have h := representedPairPaperLUV_valuesAt T
    (RepresentsComputations.repr (T := T) _
      (deferredWeightPairCode_computable market f w hw weight_mem)).choose
    (deferredWeightPairCode f w)
    (RepresentsComputations.repr (T := T) _
      (deferredWeightPairCode_computable market f w hw weight_mem)).choose_spec
    (deferredWeightPairCode_mem f w weight_mem) n v hv
  have hval : ((deferredWeightPairCode f w n).unpair.1 : ℝ) /
      ((deferredWeightPairCode f w n).unpair.2 : ℝ) = (w (f n) : ℝ) := by
    simp only [deferredWeightPairCode_unpair]
    exact natAbs_div_den (weight_mem (f n)).1
  rw [← hval]
  exact h

end Deferred

end LogicalInduction
