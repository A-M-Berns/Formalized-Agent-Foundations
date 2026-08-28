/-
# §4.1 Limit coherence (`thm:lc`, appendix `app:lc`)

The Gaifman-extension step: the limiting prices define coherent probabilities on every
finite Boolean cylinder, and compactness of `ℕ → Bool` makes the resulting cylinder content
countably additive, hence it extends to an actual probability measure on worlds.  The
paper-facing statement is `lic_limitCoherence`.
-/
import LogicalInduction.Properties.Relationships
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import LogicalInduction.Framework.WriteOut

namespace LogicalInduction

open Filter Topology Set MeasureTheory

/-- Propositions carry the discrete measurable structure, so proposition-valued worlds inherit
the usual countable product measurable space. -/
instance propMeasurableSpace : MeasurableSpace Prop := ⊤

instance propMeasurableSingletonClass : MeasurableSingletonClass Prop :=
  ⟨fun _ => trivial⟩

instance pcWorldMeasurableSpace : MeasurableSpace PCWorld :=
  inferInstanceAs (MeasurableSpace (ℕ → Prop))

namespace BoolProjectiveLimit

/-- Every measurable cylinder in Boolean product space is closed. -/
lemma isClosed_of_mem_measurableCylinders
    {s : Set (ℕ → Bool)} (hs : s ∈ measurableCylinders (fun _ : ℕ => Bool)) :
    IsClosed s := by
  obtain ⟨I, S, _, rfl⟩ := (mem_measurableCylinders s).mp hs
  have hc : Continuous (Finset.restrict I : (ℕ → Bool) → (I → Bool)) :=
    continuous_pi fun i => by
      simpa [Finset.restrict] using
        (continuous_apply (i : ℕ) : Continuous (fun v : ℕ → Bool => v i))
  simpa [cylinder] using (isClosed_discrete S).preimage hc

/-- A decreasing sequence of Boolean cylinders with empty intersection is eventually empty. -/
lemma eventually_eq_empty_of_antitone
    {s : ℕ → Set (ℕ → Bool)}
    (hs : ∀ n, s n ∈ measurableCylinders (fun _ : ℕ => Bool))
    (hanti : Antitone s) (hinter : (⋂ n, s n) = ∅) :
    ∀ᶠ n in atTop, s n = ∅ := by
  have hempty : ∃ n, s n = ∅ := by
    by_contra h
    push_neg at h
    have hnonempty : ∀ n, (s n).Nonempty := h
    have hi := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed s
      (fun n => hanti (Nat.le_succ n)) hnonempty
      (isCompact_univ.of_isClosed_subset (isClosed_of_mem_measurableCylinders (hs 0))
        (subset_univ _))
      (fun n => isClosed_of_mem_measurableCylinders (hs n))
    rw [hinter] at hi
    exact Set.not_nonempty_empty hi
  obtain ⟨n, hn⟩ := hempty
  exact Filter.eventually_atTop.2 ⟨n, fun m hnm =>
    Set.Subset.antisymm (fun x hx => by simpa [hn] using hanti hnm hx) (empty_subset _)⟩

variable {Q : ∀ I : Finset ℕ, Measure (∀ _ : I, Bool)}

/-- On compact Boolean product space, every projective family of finite measures has a
countably additive cylinder content. -/
lemma projectiveFamilyContent_isSigmaSubadditive
    (hQ : IsProjectiveMeasureFamily (α := fun _ : ℕ => Bool) Q)
    [∀ I, IsFiniteMeasure (Q I)] :
    (projectiveFamilyContent hQ).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hfUnion hdisj => ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (projectiveFamilyContent hQ) (fun _ _ => projectiveFamilyContent_ne_top hQ)
    (fun s hs hanti hinter => by
      apply (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [eventually_eq_empty_of_antitone hs hanti hinter] with n hn
      simp [hn]) hf hfUnion hdisj

/-- The projective-limit measure associated to a finite-dimensional Boolean law. -/
noncomputable def measure
    (hQ : IsProjectiveMeasureFamily (α := fun _ : ℕ => Bool) Q)
    [∀ I, IsFiniteMeasure (Q I)] :
    Measure (ℕ → Bool) :=
  (projectiveFamilyContent hQ).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge (projectiveFamilyContent_isSigmaSubadditive hQ)

/-- The constructed measure has the prescribed value on every finite cylinder. -/
lemma measure_cylinder
    (hQ : IsProjectiveMeasureFamily (α := fun _ : ℕ => Bool) Q)
    [∀ I, IsFiniteMeasure (Q I)]
    (I : Finset ℕ) (S : Set (∀ _ : I, Bool)) (hS : MeasurableSet S) :
    measure (Q := Q) hQ (cylinder I S) = Q I S := by
  rw [measure, AddContent.measure_eq, projectiveFamilyContent_cylinder hQ hS]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders (α := fun _ : ℕ => Bool) I S hS

/-- The constructed measure is the projective limit of the supplied finite laws. -/
lemma isProjectiveLimit_measure
    (hQ : IsProjectiveMeasureFamily (α := fun _ : ℕ => Bool) Q)
    [∀ I, IsFiniteMeasure (Q I)] :
    IsProjectiveLimit (α := fun _ : ℕ => Bool) (measure (Q := Q) hQ) Q := by
  intro I
  ext S hS
  calc
    (Measure.map I.restrict (measure (Q := Q) hQ)) S =
        measure (Q := Q) hQ (I.restrict ⁻¹' S) :=
      Measure.map_apply (μ := measure (Q := Q) hQ) (measurable_restrict I) hS
    _ = measure (Q := Q) hQ (cylinder I S) := by rfl
    _ = Q I S := measure_cylinder hQ I S hS

instance measure_isProbabilityMeasure
    (hQ : IsProjectiveMeasureFamily (α := fun _ : ℕ => Bool) Q)
    [∀ I, IsProbabilityMeasure (Q I)] :
    IsProbabilityMeasure (measure (Q := Q) hQ) :=
  (isProjectiveLimit_measure hQ).isProbabilityMeasure

end BoolProjectiveLimit

/-! ## Gaifman coherence of the limiting valuation -/

/-- The finite Gaifman conditions needed to extend a valuation on sentences to a measure.
The semantic clauses range over all propositional worlds, so they factor through the Boolean
algebra of sentence events rather than through syntax. -/
structure GaifmanCoherent (L : Valuation) : Prop where
  mem_Icc : ∀ φ, L φ ∈ Set.Icc 0 1
  top_eq_one : L (⊤ : Sentence) = 1
  congr : ∀ {φ ψ : Sentence},
    (∀ v : PCWorld, v.Holds φ ↔ v.Holds ψ) → L φ = L ψ
  disjoint_add : ∀ {φ ψ : Sentence},
    (∀ v : PCWorld, ¬(v.Holds φ ∧ v.Holds ψ)) → L (φ ⋎ ψ) = L φ + L ψ

/-- A fixed finite exactly-one family has limiting probabilities summing to one.  This is
the completed-theory form used below: the semantic premise is only about worlds satisfying
all sentences that ever appear in the deductive process. -/
lemma lic_limitingBelief_exactlyOne
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (k : ℕ) (hk : 0 < k) (φ : ℕ → Sentence)
    (hcodes : ∀ j < k, BigSentenceCodes (fun _ => φ j))
    (hexact : ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ((List.range k).map (fun j => v.payout (φ j))).sum = 1) :
    ((List.range k).map (fun j => limitingBelief P (φ j))).sum = 1 := by
  let family : ℕ → ℕ → Sentence := fun j _ => φ j
  have hsem : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ((List.range k).map (fun j => v.payout (family j n))).sum = 1 := by
    intro n v hv
    simpa [family] using hexact v hv
  have hlex := lic_learning_exclusive_exhaustive P DP k hk family hcodes
    hworld hsem
  have hsum : ∀ l : List ℕ,
      ConvergesTo (fun n => (l.map (fun j => P n (family j n))).sum)
        ((l.map (fun j => limitingBelief P (family j 0))).sum) := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih =>
        simpa using (lic_limitingBelief_tendsto P DP hworld (family j 0)).add ih
  have hone : ConvergesTo
      (fun n => ((List.range k).map (fun j => P n (family j n))).sum) 1 :=
    convergesTo_iff_asympEq_const.mpr hlex
  have hlimit := tendsto_nhds_unique (hsum (List.range k)) hone
  simpa [family] using hlimit

/-- Complementarity of a sentence and its negation at the limiting valuation. -/
lemma lic_limitingBelief_add_neg'
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (φ : Sentence) :
    limitingBelief P φ + limitingBelief P (∼φ) = 1 := by
  let pair : ℕ → Sentence := fun j => if j = 0 then φ else ∼φ
  have hcodes : ∀ j < 2, BigSentenceCodes (fun _ => pair j) := by
    intro j hj
    exact BigSentenceCodes.ofPolySentenceCodes
      ⟨_, PolyFueled.const (Encodable.encode (pair j))⟩
  have h := lic_limitingBelief_exactlyOne P DP hworld 2 (by omega) pair hcodes (by
    intro v hv
    have hrange : List.range 2 = [0, 1] := by decide
    rw [hrange]
    by_cases hp : v.Holds φ <;>
      simp [pair, PCWorld.payout, PCWorld.holds_neg, hp])
  have hrange : List.range 2 = [0, 1] := by decide
  simpa [hrange, pair] using h

/-- Semantically equivalent sentences receive the same limiting probability. -/
lemma lic_limitingBelief_congr
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {φ ψ : Sentence} (heq : ∀ v : PCWorld, v.Holds φ ↔ v.Holds ψ) :
    limitingBelief P φ = limitingBelief P ψ := by
  let pair : ℕ → Sentence := fun j => if j = 0 then φ else ∼ψ
  have hcodes : ∀ j < 2, BigSentenceCodes (fun _ => pair j) := by
    intro j hj
    exact BigSentenceCodes.ofPolySentenceCodes
      ⟨_, PolyFueled.const (Encodable.encode (pair j))⟩
  have hpair0 := lic_limitingBelief_exactlyOne P DP hworld 2 (by omega) pair hcodes (by
    intro v hv
    have hrange : List.range 2 = [0, 1] := by decide
    rw [hrange]
    by_cases hp : v.Holds φ
    · have hψ : v.Holds ψ := (heq v).mp hp
      simp [pair, PCWorld.payout, PCWorld.holds_neg, hp, hψ]
    · have hψ : ¬v.Holds ψ := fun h => hp ((heq v).mpr h)
      simp [pair, PCWorld.payout, PCWorld.holds_neg, hp, hψ])
  have hrange : List.range 2 = [0, 1] := by decide
  have hpair : limitingBelief P φ + limitingBelief P (∼ψ) = 1 := by
    simpa [hrange, pair] using hpair0
  have hcomp := lic_limitingBelief_add_neg' P DP hworld ψ
  linarith

/-- Finite additivity for semantically disjoint sentences at the limiting valuation. -/
lemma lic_limitingBelief_disjoint_add
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {φ ψ : Sentence} (hdisj : ∀ v : PCWorld, ¬(v.Holds φ ∧ v.Holds ψ)) :
    limitingBelief P (φ ⋎ ψ) = limitingBelief P φ + limitingBelief P ψ := by
  let triple : ℕ → Sentence := fun j => if j = 0 then φ else if j = 1 then ψ else ∼(φ ⋎ ψ)
  have hcodes : ∀ j < 3, BigSentenceCodes (fun _ => triple j) := by
    intro j hj
    exact BigSentenceCodes.ofPolySentenceCodes
      ⟨_, PolyFueled.const (Encodable.encode (triple j))⟩
  have htriple0 := lic_limitingBelief_exactlyOne P DP hworld 3 (by omega) triple hcodes (by
    intro v hv
    have hrange : List.range 3 = [0, 1, 2] := by decide
    rw [hrange]
    by_cases hφ : v.Holds φ <;> by_cases hψ : v.Holds ψ <;>
      simp_all [triple, PCWorld.payout, PCWorld.holds_neg, PCWorld.holds_or])
  have hrange : List.range 3 = [0, 1, 2] := by decide
  have htriple : limitingBelief P φ + limitingBelief P ψ +
      limitingBelief P (∼(φ ⋎ ψ)) = 1 := by
    simpa [hrange, triple, add_assoc] using htriple0
  have hcomp := lic_limitingBelief_add_neg' P DP hworld (φ ⋎ ψ)
  linarith

/-- The limiting belief state satisfies all finite Gaifman conditions.  In particular the
theorem does not require theoremhood or inconsistency at every stage of the deductive process.
Paper node: `thm:lc` -/
theorem lic_limitingBelief_gaifman
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    GaifmanCoherent (limitingBelief P) := by
  refine {
    mem_Icc := fun φ => ?_
    top_eq_one := ?_
    congr := fun heq => lic_limitingBelief_congr P DP hworld heq
    disjoint_add := fun hdisj => lic_limitingBelief_disjoint_add P DP hworld hdisj }
  · exact isClosed_Icc.mem_of_tendsto (lic_limitingBelief_tendsto P DP hworld φ)
      (Filter.Eventually.of_forall fun n =>
        IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ)
  · let singleton : ℕ → Sentence := fun _ => ⊤
    have hcodes : ∀ j < 1, BigSentenceCodes (fun _ => singleton j) := by
      intro j hj
      exact BigSentenceCodes.ofPolySentenceCodes
        ⟨_, PolyFueled.const (Encodable.encode (⊤ : Sentence))⟩
    have h := lic_limitingBelief_exactlyOne P DP hworld 1 (by omega) singleton hcodes (by
      intro v hv
      have hrange : List.range 1 = [0] := by decide
      rw [hrange]
      simp [singleton, PCWorld.payout, PCWorld.Holds,
        LO.Propositional.Formula.Boolean.val])
    simpa [singleton] using h

namespace GaifmanCoherent

variable {L : Valuation} (hL : GaifmanCoherent L)

include hL

lemma bot_eq_zero : L (⊥ : Sentence) = 0 := by
  have hadd := GaifmanCoherent.disjoint_add hL (φ := (⊥ : Sentence)) (ψ := ⊥) (by
    intro v
    simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val])
  have hcongr : L ((⊥ : Sentence) ⋎ ⊥) = L ⊥ := GaifmanCoherent.congr hL (by
    intro v
    simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val])
  linarith

end GaifmanCoherent

/-! ## Finite Boolean laws

`sentenceConjunction` / `sentenceDisjunction` and their `Holds` characterizations live
upstream in `Framework/Criterion.lean`, beside `PCWorld.Holds`. -/

namespace GaifmanCoherent

variable {L : Valuation} (hL : GaifmanCoherent L)

include hL

/-- Finite additivity for a pairwise-disjoint list of sentence events. -/
lemma disjoint_sum (l : List Sentence)
    (hdisj : l.Pairwise fun φ ψ =>
      ∀ v : PCWorld, ¬(v.Holds φ ∧ v.Holds ψ)) :
    L (sentenceDisjunction l) = (l.map L).sum := by
  induction l with
  | nil => simpa [sentenceDisjunction] using GaifmanCoherent.bot_eq_zero hL
  | cons φ l ih =>
      rw [sentenceDisjunction, GaifmanCoherent.disjoint_add hL]
      · rw [ih hdisj.tail]
        rfl
      · intro v hv
        rcases hv with ⟨hvφ, hvl⟩
        obtain ⟨ψ, hψl, hvψ⟩ := (holds_sentenceDisjunction v l).mp hvl
        exact (List.pairwise_cons.mp hdisj).1 ψ hψl v ⟨hvφ, hvψ⟩

/-- Monotonicity along semantic implication. -/
lemma mono {φ ψ : Sentence} (himp : ∀ v : PCWorld, v.Holds φ → v.Holds ψ) :
    L φ ≤ L ψ := by
  have hsplit : L (φ ⋎ (ψ ⋏ ∼φ)) = L φ + L (ψ ⋏ ∼φ) :=
    GaifmanCoherent.disjoint_add hL (by
      intro v hv
      exact (PCWorld.holds_and v ψ (∼φ)).mp hv.2 |>.2
        |> fun h => ((PCWorld.holds_neg v φ).mp h) hv.1)
  have hcongr : L (φ ⋎ (ψ ⋏ ∼φ)) = L ψ :=
    GaifmanCoherent.congr hL (by
      intro v
      simp only [PCWorld.holds_or, PCWorld.holds_and, PCWorld.holds_neg]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact himp v h
        · exact h
      · intro h
        by_cases hφ : v.Holds φ
        · exact Or.inl hφ
        · exact Or.inr ⟨h, hφ⟩)
  have hnonneg : 0 ≤ L (ψ ⋏ ∼φ) := (GaifmanCoherent.mem_Icc hL _).1
  rw [hcongr] at hsplit
  linarith

/-- Subadditivity on a binary disjunction. -/
lemma or_le (φ ψ : Sentence) : L (φ ⋎ ψ) ≤ L φ + L ψ := by
  have hcongr : L (φ ⋎ ψ) = L (φ ⋎ (ψ ⋏ ∼φ)) :=
    GaifmanCoherent.congr hL (by
      intro v
      simp only [PCWorld.holds_or, PCWorld.holds_and, PCWorld.holds_neg]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · by_cases hφ : v.Holds φ
          · exact Or.inl hφ
          · exact Or.inr ⟨h, hφ⟩
      · rintro (h | ⟨h, -⟩)
        · exact Or.inl h
        · exact Or.inr h)
  have hsplit : L (φ ⋎ (ψ ⋏ ∼φ)) = L φ + L (ψ ⋏ ∼φ) :=
    GaifmanCoherent.disjoint_add hL (by
      intro v hv
      exact ((PCWorld.holds_neg v φ).mp ((PCWorld.holds_and v ψ (∼φ)).mp hv.2).2) hv.1)
  have hmono : L (ψ ⋏ ∼φ) ≤ L ψ :=
    GaifmanCoherent.mono hL (fun v hv => ((PCWorld.holds_and v ψ (∼φ)).mp hv).1)
  rw [hcongr, hsplit]
  linarith

/-- Finite subadditivity: a sentence covered by a finite list of sentence events has
valuation at most the sum of theirs.  No disjointness is required. -/
lemma le_sum_of_covers {φ : Sentence} {l : List Sentence}
    (hcov : ∀ v : PCWorld, v.Holds φ → ∃ ψ ∈ l, v.Holds ψ) :
    L φ ≤ (l.map L).sum := by
  have hmono : L φ ≤ L (sentenceDisjunction l) :=
    GaifmanCoherent.mono hL (fun v hv => (holds_sentenceDisjunction v l).mpr (hcov v hv))
  refine hmono.trans ?_
  clear hmono hcov
  induction l with
  | nil => simp [sentenceDisjunction, GaifmanCoherent.bot_eq_zero hL]
  | cons ψ l ih =>
      rw [sentenceDisjunction, List.map_cons, List.sum_cons]
      exact (GaifmanCoherent.or_le hL ψ (sentenceDisjunction l)).trans (by linarith)

end GaifmanCoherent

/-- The sentence asserting that atom `i` has Boolean value `b`. -/
def booleanLiteral (i : ℕ) (b : Bool) : Sentence :=
  if b then .atom i else ∼(.atom i)

/-- The conjunction describing one assignment on a finite set of atoms. -/
noncomputable def booleanCube (I : Finset ℕ) (x : I → Bool) : Sentence :=
  sentenceConjunction (I.attach.toList.map fun i : I => booleanLiteral i (x i))

@[simp] lemma holds_booleanLiteral (v : BoolPCWorld) (i : ℕ) (b : Bool) :
    v.toPCWorld.Holds (booleanLiteral i b) ↔ v i = b := by
  cases b <;> simp [booleanLiteral, BoolPCWorld.toPCWorld, PCWorld.Holds,
    LO.Propositional.Formula.Boolean.val]

@[simp] lemma holds_booleanCube (v : BoolPCWorld) (I : Finset ℕ) (x : I → Bool) :
    v.toPCWorld.Holds (booleanCube I x) ↔ I.restrict v = x := by
  classical
  simp only [booleanCube, holds_sentenceConjunction, List.mem_map, Finset.mem_toList]
  constructor
  · intro h
    funext i
    have hi := h (booleanLiteral i (x i)) ⟨i, by simp⟩
    exact (holds_booleanLiteral v i (x i)).mp hi
  · intro h φ hφ
    obtain ⟨i, hi, rfl⟩ := hφ
    apply (holds_booleanLiteral v i (x i)).mpr
    exact congrFun h i

lemma booleanCube_disjoint (I : Finset ℕ) {x y : I → Bool} (hxy : x ≠ y)
    (v : PCWorld) : ¬(v.Holds (booleanCube I x) ∧ v.Holds (booleanCube I y)) := by
  intro h
  have hx := (holds_booleanCube (BoolPCWorld.ofPCWorld v) I x).mp (by simpa using h.1)
  have hy := (holds_booleanCube (BoolPCWorld.ofPCWorld v) I y).mp (by simpa using h.2)
  exact hxy (hx.symm.trans hy)

/-- The finite-dimensional PMF induced by a Gaifman-coherent valuation. -/
noncomputable def gaifmanFinitePMF (L : Valuation) (hL : GaifmanCoherent L)
    (I : Finset ℕ) : PMF (I → Bool) := by
  classical
  let f : (I → Bool) → ENNReal := fun x => ENNReal.ofReal (L (booleanCube I x))
  apply PMF.ofFintype f
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => (GaifmanCoherent.mem_Icc hL _).1)]
  let assignments := (Finset.univ : Finset (I → Bool)).toList
  let cubes := assignments.map fun x => booleanCube I x
  have hp : cubes.Pairwise fun φ ψ =>
      ∀ v : PCWorld, ¬(v.Holds φ ∧ v.Holds ψ) := by
    dsimp only [cubes]
    rw [List.pairwise_map]
    have hn : assignments.Pairwise (· ≠ ·) := by
      exact Finset.nodup_toList _
    exact hn.imp fun hxy => booleanCube_disjoint I hxy
  have hsum := GaifmanCoherent.disjoint_sum hL cubes hp
  have htop : L (sentenceDisjunction cubes) = L (⊤ : Sentence) :=
    GaifmanCoherent.congr hL (by
      intro v
      constructor
      · intro hv
        simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
      · intro hv
        let x : I → Bool := I.restrict (BoolPCWorld.ofPCWorld v)
        apply (holds_sentenceDisjunction v cubes).mpr
        refine ⟨booleanCube I x, ?_, ?_⟩
        · simp [cubes, assignments]
        · rw [show v = (BoolPCWorld.ofPCWorld v).toPCWorld by
            exact (BoolPCWorld.ofPCWorld_toPCWorld v).symm]
          rw [holds_booleanCube])
  have hreal : ∑ x : I → Bool, L (booleanCube I x) = 1 := by
    calc
      ∑ x : I → Bool, L (booleanCube I x) = (cubes.map L).sum := by
        simp [cubes, assignments]
      _ = L (sentenceDisjunction cubes) := hsum.symm
      _ = 1 := htop.trans (GaifmanCoherent.top_eq_one hL)
  simp [hreal]

/-- The corresponding finite-dimensional probability measure. -/
noncomputable def gaifmanFiniteMeasure (L : Valuation) (hL : GaifmanCoherent L)
    (I : Finset ℕ) : Measure (I → Bool) :=
  (gaifmanFinitePMF L hL I).toMeasure

instance gaifmanFiniteMeasure_isProbabilityMeasure (L : Valuation) (hL : GaifmanCoherent L)
    (I : Finset ℕ) : IsProbabilityMeasure (gaifmanFiniteMeasure L hL I) :=
  PMF.toMeasure.isProbabilityMeasure (gaifmanFinitePMF L hL I)

/-- A sentence whose models are exactly the finite assignments in `S`. -/
noncomputable def booleanEvent (I : Finset ℕ) (S : Set (I → Bool)) : Sentence :=
  by
    classical
    exact sentenceDisjunction
      (((Finset.univ.filter fun x : I → Bool => x ∈ S).toList).map (booleanCube I))

@[simp] lemma holds_booleanEvent (v : BoolPCWorld) (I : Finset ℕ) (S : Set (I → Bool)) :
    v.toPCWorld.Holds (booleanEvent I S) ↔ I.restrict v ∈ S := by
  classical
  constructor
  · intro hv
    obtain ⟨φ, hφ, hvφ⟩ := (holds_sentenceDisjunction v.toPCWorld _).mp hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hφ
    have hxS : x ∈ S := by simpa [booleanEvent] using hx
    exact (holds_booleanCube v I x).mp hvφ ▸ hxS
  · intro hv
    apply (holds_sentenceDisjunction v.toPCWorld _).mpr
    refine ⟨booleanCube I (I.restrict v), ?_, (holds_booleanCube v I _).mpr rfl⟩
    exact List.mem_map.mpr ⟨I.restrict v, by simp [hv], rfl⟩

@[simp] lemma gaifmanFinitePMF_apply (L : Valuation) (hL : GaifmanCoherent L)
    (I : Finset ℕ) (x : I → Bool) :
    gaifmanFinitePMF L hL I x = ENNReal.ofReal (L (booleanCube I x)) := by
  simp [gaifmanFinitePMF]

/-- A finite law assigns an arbitrary finite-coordinate event the coherent value of its
representing sentence. -/
lemma gaifmanFiniteMeasure_apply (L : Valuation) (hL : GaifmanCoherent L)
    (I : Finset ℕ) (S : Set (I → Bool)) :
    gaifmanFiniteMeasure L hL I S = ENNReal.ofReal (L (booleanEvent I S)) := by
  classical
  rw [gaifmanFiniteMeasure, PMF.toMeasure_apply_fintype]
  let assignments := (Finset.univ.filter fun x : I → Bool => x ∈ S).toList
  let cubes := assignments.map (booleanCube I)
  have hp : cubes.Pairwise fun φ ψ =>
      ∀ v : PCWorld, ¬(v.Holds φ ∧ v.Holds ψ) := by
    dsimp only [cubes]
    rw [List.pairwise_map]
    have hn : assignments.Pairwise (· ≠ ·) := by
      exact Finset.nodup_toList _
    exact hn.imp fun hxy => booleanCube_disjoint I hxy
  have hsum := GaifmanCoherent.disjoint_sum hL cubes hp
  have hreal : ∑ x : I → Bool, S.indicator (fun x => L (booleanCube I x)) x =
      L (booleanEvent I S) := by
    calc
      ∑ x : I → Bool, S.indicator (fun x => L (booleanCube I x)) x =
          Finset.sum (Finset.univ.filter (fun x : I → Bool => x ∈ S))
            (fun x => L (booleanCube I x)) := by
        rw [Finset.sum_filter]
        rfl
      _ = (cubes.map L).sum := by simp [cubes, assignments]
      _ = L (sentenceDisjunction cubes) := hsum.symm
      _ = L (booleanEvent I S) := by rfl
  calc
    ∑ x : I → Bool, S.indicator (gaifmanFinitePMF L hL I) x =
        ∑ x : I → Bool, ENNReal.ofReal
          (S.indicator (fun x => L (booleanCube I x)) x) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxs : x ∈ S <;>
        simp [Set.indicator, hxs, gaifmanFinitePMF_apply]
    _ = ENNReal.ofReal
        (∑ x : I → Bool, S.indicator (fun x => L (booleanCube I x)) x) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro x hx
      by_cases hxs : x ∈ S <;>
        simp [Set.indicator, hxs, (GaifmanCoherent.mem_Icc hL _).1]
    _ = ENNReal.ofReal (L (booleanEvent I S)) := congrArg ENNReal.ofReal hreal

set_option maxHeartbeats 800000 in
/-- The coherent finite-dimensional laws form a projective family. -/
lemma gaifmanFiniteMeasure_isProjective (L : Valuation) (hL : GaifmanCoherent L) :
    IsProjectiveMeasureFamily (α := fun _ : ℕ => Bool) (gaifmanFiniteMeasure L hL) := by
  intro I J hJI
  ext S hS
  have hevent : L (booleanEvent J S) =
      L (booleanEvent I
        ((Finset.restrict₂ (π := fun _ : ℕ => Bool) hJI) ⁻¹' S)) := by
    apply GaifmanCoherent.congr hL
    intro v
    rw [show v = (BoolPCWorld.ofPCWorld v).toPCWorld by
      exact (BoolPCWorld.ofPCWorld_toPCWorld v).symm]
    simp only [holds_booleanEvent, Set.mem_preimage]
    have hr : J.restrict (BoolPCWorld.ofPCWorld v) =
        Finset.restrict₂ (π := fun _ : ℕ => Bool) hJI
          (I.restrict (BoolPCWorld.ofPCWorld v)) := by
      funext j
      rfl
    rw [hr]
  calc
    gaifmanFiniteMeasure L hL J S = ENNReal.ofReal (L (booleanEvent J S)) :=
      gaifmanFiniteMeasure_apply L hL J S
    _ = ENNReal.ofReal (L (booleanEvent I
        ((Finset.restrict₂ (π := fun _ : ℕ => Bool) hJI) ⁻¹' S))) :=
      congrArg ENNReal.ofReal hevent
    _ = gaifmanFiniteMeasure L hL I
        ((Finset.restrict₂ (π := fun _ : ℕ => Bool) hJI) ⁻¹' S) :=
      (gaifmanFiniteMeasure_apply L hL I _).symm
    _ = (gaifmanFiniteMeasure L hL I).map
        (Finset.restrict₂ (π := fun _ : ℕ => Bool) hJI) S :=
      (Measure.map_apply (μ := gaifmanFiniteMeasure L hL I)
        (Finset.measurable_restrict₂ (X := fun _ : ℕ => Bool) hJI) hS).symm

/-! ## The Gaifman measure on Boolean worlds -/

/-- The countably additive probability measure extending a coherent sentence valuation. -/
noncomputable def gaifmanMeasure (L : Valuation) (hL : GaifmanCoherent L) :
    Measure BoolPCWorld :=
  BoolProjectiveLimit.measure (gaifmanFiniteMeasure_isProjective L hL)

instance gaifmanMeasure_isProbabilityMeasure (L : Valuation) (hL : GaifmanCoherent L) :
    IsProbabilityMeasure (gaifmanMeasure L hL) := by
  unfold gaifmanMeasure
  infer_instance

/-- The Gaifman measure has the prescribed law on every finite Boolean cylinder. -/
lemma gaifmanMeasure_cylinder (L : Valuation) (hL : GaifmanCoherent L)
    (I : Finset ℕ) (S : Set (I → Bool)) (hS : MeasurableSet S) :
    gaifmanMeasure L hL (cylinder I S) = ENNReal.ofReal (L (booleanEvent I S)) := by
  rw [gaifmanMeasure]
  rw [BoolProjectiveLimit.measure_cylinder
    (gaifmanFiniteMeasure_isProjective L hL) I S hS]
  exact gaifmanFiniteMeasure_apply L hL I S

/-- The finite set of atoms on which a sentence depends. -/
def sentenceAtoms : Sentence → Finset ℕ
  | .atom a => {a}
  | ⊥ => ∅
  | φ 🡒 ψ => sentenceAtoms φ ∪ sentenceAtoms ψ
  | φ ⋏ ψ => sentenceAtoms φ ∪ sentenceAtoms ψ
  | φ ⋎ ψ => sentenceAtoms φ ∪ sentenceAtoms ψ

/-- Extend an assignment on `I` by `false` outside `I`. -/
def extendFiniteAssignment (I : Finset ℕ) (x : I → Bool) : BoolPCWorld :=
  fun a => if h : a ∈ I then x ⟨a, h⟩ else false

lemma eval_eq_of_eq_on_atoms (v w : BoolPCWorld) (φ : Sentence)
    (h : ∀ a ∈ sentenceAtoms φ, v a = w a) :
    BoolPCWorld.eval v φ = BoolPCWorld.eval w φ := by
  induction φ with
  | atom a => exact h a (by simp [sentenceAtoms])
  | falsum => rfl
  | imp φ ψ ihφ ihψ =>
      have hφ : ∀ a ∈ sentenceAtoms φ, v a = w a := by
        intro a ha
        exact h a (Finset.mem_union_left _ ha)
      have hψ : ∀ a ∈ sentenceAtoms ψ, v a = w a := by
        intro a ha
        exact h a (Finset.mem_union_right _ ha)
      simp only [BoolPCWorld.eval]
      rw [ihφ hφ, ihψ hψ]
  | and φ ψ ihφ ihψ =>
      have hφ : ∀ a ∈ sentenceAtoms φ, v a = w a := by
        intro a ha
        exact h a (Finset.mem_union_left _ ha)
      have hψ : ∀ a ∈ sentenceAtoms ψ, v a = w a := by
        intro a ha
        exact h a (Finset.mem_union_right _ ha)
      simp only [BoolPCWorld.eval]
      rw [ihφ hφ, ihψ hψ]
  | or φ ψ ihφ ihψ =>
      have hφ : ∀ a ∈ sentenceAtoms φ, v a = w a := by
        intro a ha
        exact h a (Finset.mem_union_left _ ha)
      have hψ : ∀ a ∈ sentenceAtoms ψ, v a = w a := by
        intro a ha
        exact h a (Finset.mem_union_right _ ha)
      simp only [BoolPCWorld.eval]
      rw [ihφ hφ, ihψ hψ]

lemma eval_extend_restrict (v : BoolPCWorld) (φ : Sentence) :
    BoolPCWorld.eval
      (extendFiniteAssignment (sentenceAtoms φ) ((sentenceAtoms φ).restrict v)) φ =
      BoolPCWorld.eval v φ := by
  apply eval_eq_of_eq_on_atoms
  intro a ha
  simp [extendFiniteAssignment, ha]

/-- Every sentence event is a measurable finite cylinder. -/
lemma sentenceEvent_eq_cylinder (φ : Sentence) :
    {v : BoolPCWorld | v.toPCWorld.Holds φ} =
      cylinder (sentenceAtoms φ)
        {x | (extendFiniteAssignment (sentenceAtoms φ) x).toPCWorld.Holds φ} := by
  ext v
  simp only [cylinder, Set.mem_preimage, Set.mem_setOf_eq]
  rw [← BoolPCWorld.eval_eq_true_iff_holds, ← BoolPCWorld.eval_eq_true_iff_holds,
    eval_extend_restrict]

/-- Sentence events receive exactly their coherent probabilities.
Paper node: `thm:lc` -/
theorem gaifmanMeasure_sentence (L : Valuation) (hL : GaifmanCoherent L) (φ : Sentence) :
    gaifmanMeasure L hL {v : BoolPCWorld | v.toPCWorld.Holds φ} =
      ENNReal.ofReal (L φ) := by
  rw [sentenceEvent_eq_cylinder]
  rw [gaifmanMeasure_cylinder L hL _ _ (Set.toFinite _).measurableSet]
  apply congrArg ENNReal.ofReal
  apply GaifmanCoherent.congr hL
  intro v
  rw [show v = (BoolPCWorld.ofPCWorld v).toPCWorld by
    exact (BoolPCWorld.ofPCWorld_toPCWorld v).symm]
  rw [holds_booleanEvent]
  change ((sentenceAtoms φ).restrict (BoolPCWorld.ofPCWorld v) ∈
    {x | (extendFiniteAssignment (sentenceAtoms φ) x).toPCWorld.Holds φ}) ↔ _
  simp only [Set.mem_setOf_eq]
  rw [← BoolPCWorld.eval_eq_true_iff_holds, ← BoolPCWorld.eval_eq_true_iff_holds,
    eval_extend_restrict]

/-- The Boolean presentation maps measurably to the proposition-valued worlds. -/
lemma BoolPCWorld.measurable_toPCWorld : Measurable BoolPCWorld.toPCWorld := by
  apply measurable_pi_lambda
  intro a
  exact (measurable_of_countable (fun b : Bool => b = true)).comp (measurable_pi_apply a)

/-- Truth of a fixed sentence is measurable on proposition-valued worlds. -/
lemma measurable_pcWorld_holds (φ : Sentence) :
    Measurable (fun v : PCWorld => v.Holds φ) := by
  induction φ with
  | atom a => exact measurable_pi_apply a
  | falsum => exact measurable_const
  | imp φ ψ ihφ ihψ => exact ihφ.imp ihψ
  | and φ ψ ihφ ihψ => exact ihφ.and ihψ
  | or φ ψ ihφ ihψ => exact ihφ.or ihψ

/-- Consistency with the completed deductive process is a measurable world predicate. -/
lemma measurable_consistentWithTheory (DP : DeductiveProcess) :
    Measurable (fun v : PCWorld => v.ConsistentWithTheory DP) := by
  apply Measurable.forall
  intro n
  apply Measurable.forall
  intro φ
  exact measurable_const.imp (measurable_pcWorld_holds φ)

/-- The Gaifman measure transported to the proposition-valued `PCWorld` type. -/
noncomputable def gaifmanWorldMeasure (L : Valuation) (hL : GaifmanCoherent L) :
    Measure PCWorld :=
  (gaifmanMeasure L hL).map BoolPCWorld.toPCWorld

instance gaifmanWorldMeasure_isProbabilityMeasure (L : Valuation) (hL : GaifmanCoherent L) :
    IsProbabilityMeasure (gaifmanWorldMeasure L hL) := by
  unfold gaifmanWorldMeasure
  exact Measure.isProbabilityMeasure_map BoolPCWorld.measurable_toPCWorld.aemeasurable

/-- On actual `PCWorld`s, sentence events still have exactly the coherent probability.
Paper node: `thm:lc` -/
theorem gaifmanWorldMeasure_sentence (L : Valuation) (hL : GaifmanCoherent L) (φ : Sentence) :
    gaifmanWorldMeasure L hL {v : PCWorld | v.Holds φ} = ENNReal.ofReal (L φ) := by
  rw [gaifmanWorldMeasure, Measure.map_apply BoolPCWorld.measurable_toPCWorld
    (measurable_pcWorld_holds φ).setOf]
  exact gaifmanMeasure_sentence L hL φ

/-! ## Paper-facing limit coherence -/

/-- A theorem of the completed deductive process has limiting probability one.  The theorem
may first appear at any finite stage. -/
lemma lic_limitingBelief_theorem
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : Sentence) (hthm : ∃ k, φ ∈ DP.D k) : limitingBelief P φ = 1 := by
  have hcodes : BigSentenceCodes (fun _ => φ) := BigSentenceCodes.const φ
  have hone := lic_provind_true P DP (fun _ => φ) hcodes (fun _ => hthm) hworld
  have ht : ConvergesTo (fun n => P n φ) 1 :=
    convergesTo_iff_asympEq_const.mpr hone
  exact tendsto_nhds_unique (lic_limitingBelief_tendsto P DP hworld φ) ht

/-- A refutable sentence has limiting probability zero, again under completed-theory rather
than all-stage theoremhood. -/
lemma lic_limitingBelief_refutable
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (φ : Sentence) (hdis : ∃ k, (∼φ) ∈ DP.D k) : limitingBelief P φ = 0 := by
  have hcodes : BigSentenceCodes (fun _ => φ) := BigSentenceCodes.const φ
  have hzero := lic_provind_false P DP (fun _ => φ) hcodes (fun _ => hdis) hworld
  have ht : ConvergesTo (fun n => P n φ) 0 :=
    convergesTo_iff_asympEq_const.mpr hzero
  exact tendsto_nhds_unique (lic_limitingBelief_tendsto P DP hworld φ) ht

/-- The Gaifman measure induced by limiting beliefs is concentrated on worlds satisfying
the completed deductive process.
Paper node: `thm:lc` -/
theorem lic_gaifmanMeasure_supported
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ᵐ v ∂gaifmanMeasure (limitingBelief P) (lic_limitingBelief_gaifman P DP hworld),
      v.toPCWorld.ConsistentWithTheory DP := by
  let hG := lic_limitingBelief_gaifman P DP hworld
  have hone (n : ℕ) (φ : Sentence) (hφ : φ ∈ DP.D n) :
      limitingBelief P φ = 1 :=
    lic_limitingBelief_theorem P DP hworld φ ⟨n, hφ⟩
  have hae (n : ℕ) (φ : Sentence) (hφ : φ ∈ DP.D n) :
      ∀ᵐ v ∂gaifmanMeasure (limitingBelief P) hG, v.toPCWorld.Holds φ := by
    apply (mem_ae_iff_prob_eq_one
      (BoolPCWorld.isClopen_holds φ).1.measurableSet).2
    rw [gaifmanMeasure_sentence, hone n φ hφ]
    simp
  have hall : ∀ᵐ v ∂gaifmanMeasure (limitingBelief P) hG,
      ∀ n φ, φ ∈ DP.D n → v.toPCWorld.Holds φ := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro φ
    by_cases hφ : φ ∈ DP.D n
    · exact (hae n φ hφ).mono fun v hv _ => hv
    · exact Filter.Eventually.of_forall fun v hv => (hφ hv).elim
  exact hall.mono fun v hv n φ hφ => hv n φ hφ

/-- The transported measure is concentrated on completed-theory `PCWorld`s.
Paper node: `thm:lc` -/
theorem lic_gaifmanWorldMeasure_supported
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ᵐ v ∂gaifmanWorldMeasure (limitingBelief P) (lic_limitingBelief_gaifman P DP hworld),
      v.ConsistentWithTheory DP := by
  let hG := lic_limitingBelief_gaifman P DP hworld
  apply (ae_map_iff BoolPCWorld.measurable_toPCWorld.aemeasurable
    (measurable_consistentWithTheory DP).setOf).2
  exact lic_gaifmanMeasure_supported P DP hworld

/-- **Limit Coherence** (`thm:lc`): limiting prices are the sentence-event probabilities of
an actual countably additive probability measure concentrated on completed-theory worlds.
The conclusion is the measure itself, not just finite additivity.
Paper node: `thm:lc` -/
theorem lic_limitCoherence
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ μ : Measure PCWorld,
      IsProbabilityMeasure μ ∧
      (∀ φ : Sentence,
        μ {v : PCWorld | v.Holds φ} =
          ENNReal.ofReal (limitingBelief P φ)) ∧
      (∀ᵐ v ∂μ, v.ConsistentWithTheory DP) := by
  let hG := lic_limitingBelief_gaifman P DP hworld
  refine ⟨gaifmanWorldMeasure (limitingBelief P) hG, inferInstance, ?_, ?_⟩
  · exact fun φ => gaifmanWorldMeasure_sentence (limitingBelief P) hG φ
  · exact lic_gaifmanWorldMeasure_supported P DP hworld

#print axioms lic_limitCoherence

end LogicalInduction
