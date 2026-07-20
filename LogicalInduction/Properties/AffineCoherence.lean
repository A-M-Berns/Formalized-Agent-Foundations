/-
# Affine coherence (`thm:affcoh`)

This file supplies the compactness bridge that the thin finite-stage plausible-world
substrate does not otherwise expose.  Boolean worlds are represented topologically as
`ℕ → Bool`; formula evaluation is continuous, so nested finite-stage model sets and every
fixed affine sublevel set are closed in a compact product space.
-/
import LogicalInduction.Properties.AffinePersistence
import LogicalInduction.Properties.AffineProvability
import LogicalInduction.Properties.TimelyLearning

namespace LogicalInduction

open Filter Topology

/-- A Boolean-valued presentation of a propositionally consistent world, used only for
the compactness proof. -/
abbrev BoolPCWorld := ℕ → Bool

namespace BoolPCWorld

/-- Interpret a Boolean assignment as the proposition-valued assignment used by `PCWorld`. -/
def toPCWorld (v : BoolPCWorld) : PCWorld := fun a => v a = true

/-- Convert a proposition-valued assignment back to Booleans. -/
noncomputable def ofPCWorld (v : PCWorld) : BoolPCWorld := fun a =>
  @decide (v a) (Classical.propDecidable _)

@[simp] theorem ofPCWorld_toPCWorld (v : PCWorld) :
    (ofPCWorld v).toPCWorld = v := by
  funext a
  apply propext
  simp [ofPCWorld, toPCWorld]

/-- Boolean evaluation of a sentence. -/
def eval (v : BoolPCWorld) : Sentence → Bool
  | .atom a => v a
  | ⊥ => false
  | φ 🡒 ψ => !(eval v φ) || eval v ψ
  | φ ⋏ ψ => eval v φ && eval v ψ
  | φ ⋎ ψ => eval v φ || eval v ψ

/-- One above the largest atom index occurring in a sentence.  This supplies the finite
support bound used by executable maturity certificates. -/
def atomBound : Sentence → ℕ
  | .atom a => a + 1
  | ⊥ => 0
  | φ 🡒 ψ => max (atomBound φ) (atomBound ψ)
  | φ ⋏ ψ => max (atomBound φ) (atomBound ψ)
  | φ ⋎ ψ => max (atomBound φ) (atomBound ψ)

/-- A valuation of exactly the first `B` atoms.  The type is finite and has a computable
enumeration, unlike an unrestricted Boolean world. -/
abbrev FiniteWorld (B : ℕ) := Fin B → Bool

/-- Extend a finite assignment by `false` outside its certified support. -/
def FiniteWorld.toBoolPCWorld {B : ℕ} (u : FiniteWorld B) : BoolPCWorld :=
  fun a => if h : a < B then u ⟨a, h⟩ else false

/-- Restrict an arbitrary Boolean world to its first `B` atoms. -/
def FiniteWorld.restrict (v : BoolPCWorld) (B : ℕ) : FiniteWorld B :=
  fun a => v a

/-- The Boolean world denoted by a bit list; atoms past the end read `false`.

This is the non-dependent cousin of `FiniteWorld.toBoolPCWorld`, and it exists for
compilation rather than for the mathematics.  `BoolPCWorld` is `ℕ → Bool`, a *function*
type, which admits no `Primcodable` instance — so `Primrec (eval v)` cannot even be stated
for a world `v`.  Routing through a `List Bool` keeps every compiled quantity a function of
`Primcodable` arguments (`List Bool × Sentence`), with the world appearing only as a
beta-reduced intermediate.  `bitsWorld_eq_toBoolPCWorld` bridges back. -/
def bitsWorld (l : List Bool) : BoolPCWorld := fun a => l.getD a false

/-- Rational payout under a bit list: the non-dependent form of `FiniteWorld.payoutRat`. -/
def bitsPayoutRat (l : List Bool) (φ : Sentence) : ℚ :=
  if eval (bitsWorld l) φ then 1 else 0

/-- Evaluation of a bounded-support sentence is unchanged by finite restriction and
extension.  Consequently every universal payout check over finitely many sentences can
be reduced to the finite type `FiniteWorld B`. -/
lemma eval_toBoolPCWorld_restrict (v : BoolPCWorld) (B : ℕ) (φ : Sentence)
    (hφ : atomBound φ ≤ B) :
    eval ((FiniteWorld.restrict v B).toBoolPCWorld) φ = eval v φ := by
  induction φ with
  | atom a =>
      simp only [atomBound] at hφ
      have ha : a < B := by omega
      simp [eval, FiniteWorld.toBoolPCWorld, FiniteWorld.restrict, ha]
  | falsum => simp [eval]
  | imp φ ψ ihφ ihψ =>
      simp only [atomBound, max_le_iff] at hφ
      simp [eval, ihφ hφ.1, ihψ hφ.2]
  | and φ ψ ihφ ihψ =>
      simp only [atomBound, max_le_iff] at hφ
      simp [eval, ihφ hφ.1, ihψ hφ.2]
  | or φ ψ ihφ ihψ =>
      simp only [atomBound, max_le_iff] at hφ
      simp [eval, ihφ hφ.1, ihψ hφ.2]

/-- Executable rational payout under a finite Boolean assignment. -/
def FiniteWorld.payoutRat {B : ℕ} (u : FiniteWorld B) (φ : Sentence) : ℚ :=
  if eval u.toBoolPCWorld φ then 1 else 0

@[simp] theorem eval_eq_true_iff_holds (v : BoolPCWorld) (φ : Sentence) :
    eval v φ = true ↔ v.toPCWorld.Holds φ := by
  induction φ with
  | atom a => simp [eval, toPCWorld, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | falsum => simp [eval, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | imp φ ψ ihφ ihψ =>
      cases hφ : eval v φ <;> cases hψ : eval v ψ <;>
        simp_all [eval, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | and φ ψ ihφ ihψ =>
      simp [eval, PCWorld.Holds, LO.Propositional.Formula.Boolean.val, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [eval, PCWorld.Holds, LO.Propositional.Formula.Boolean.val, ihφ, ihψ]

/-- The executable finite-world payout is the exact rational payout of its extended
proposition-valued world. -/
lemma FiniteWorld.payoutRat_eq_toPCWorld {B : ℕ} (u : FiniteWorld B)
    (φ : Sentence) :
    u.payoutRat φ = u.toBoolPCWorld.toPCWorld.payoutRat φ := by
  classical
  unfold payoutRat PCWorld.payoutRat
  rw [← eval_eq_true_iff_holds]
  by_cases h : eval u.toBoolPCWorld φ = true <;> simp [h]

/-- On every sentence inside the support bound, the finite rational payout obtained by
restricting a world is exactly that world's rational payout. -/
lemma FiniteWorld.payoutRat_restrict_ofPCWorld (v : PCWorld) (B : ℕ)
    (φ : Sentence) (hφ : atomBound φ ≤ B) :
    payoutRat (restrict (ofPCWorld v) B) φ = v.payoutRat φ := by
  classical
  unfold payoutRat
  rw [eval_toBoolPCWorld_restrict (ofPCWorld v) B φ hφ]
  have heval := eval_eq_true_iff_holds (ofPCWorld v) φ
  rw [ofPCWorld_toPCWorld] at heval
  by_cases hh : v.Holds φ
  · have : eval (ofPCWorld v) φ = true := heval.mpr hh
    simp [this, PCWorld.payoutRat, hh]
  · have : eval (ofPCWorld v) φ = false := by
      apply Bool.eq_false_of_not_eq_true
      exact fun he => hh (heval.mp he)
    simp [this, PCWorld.payoutRat, hh]

/-- Sentence evaluation depends continuously on its finitely many atoms. -/
lemma continuous_eval (φ : Sentence) : Continuous (fun v : BoolPCWorld => eval v φ) := by
  induction φ with
  | atom a => exact continuous_apply a
  | falsum => exact continuous_const
  | imp φ ψ ihφ ihψ =>
      exact (continuous_of_discreteTopology : Continuous
        (fun z : Bool × Bool => (!z.1) || z.2)).comp (ihφ.prodMk ihψ)
  | and φ ψ ihφ ihψ =>
      exact (continuous_of_discreteTopology : Continuous
        (fun z : Bool × Bool => z.1 && z.2)).comp (ihφ.prodMk ihψ)
  | or φ ψ ihφ ihψ =>
      exact (continuous_of_discreteTopology : Continuous
        (fun z : Bool × Bool => z.1 || z.2)).comp (ihφ.prodMk ihψ)

/-- The model set of one sentence is clopen in the Boolean product space. -/
lemma isClopen_holds (φ : Sentence) :
    IsClopen {v : BoolPCWorld | v.toPCWorld.Holds φ} := by
  have heq : {v : BoolPCWorld | v.toPCWorld.Holds φ} =
      (fun v => eval v φ) ⁻¹' {true} := by
    ext v
    simp [eval_eq_true_iff_holds]
  rw [heq]
  exact ⟨isClosed_singleton.preimage (continuous_eval φ),
    (continuous_eval φ).isOpen_preimage _ (isOpen_discrete _)⟩

@[simp] theorem payout_toPCWorld (v : BoolPCWorld) (φ : Sentence) :
    v.toPCWorld.payout φ = if eval v φ = true then 1 else 0 := by
  rw [PCWorld.payout]
  by_cases h : eval v φ = true
  · rw [if_pos h, if_pos ((eval_eq_true_iff_holds v φ).mp h)]
  · rw [if_neg h, if_neg (fun hh => h ((eval_eq_true_iff_holds v φ).mpr hh))]

/-- The real payout of a fixed sentence is continuous on Boolean worlds. -/
lemma continuous_payout (φ : Sentence) :
    Continuous (fun v : BoolPCWorld => v.toPCWorld.payout φ) := by
  rw [show (fun v : BoolPCWorld => v.toPCWorld.payout φ) =
      (fun b : Bool => if b = true then (1 : ℝ) else 0) ∘ (fun v => eval v φ) by
    funext v
    simp [Function.comp_apply]]
  exact (continuous_of_discreteTopology : Continuous
    (fun b : Bool => if b = true then (1 : ℝ) else 0)).comp (continuous_eval φ)

/-- A fixed affine combination's value is continuous as its Boolean world varies. -/
lemma continuous_affineValue (A : AffineCombination) (P : History) :
    Continuous (fun v : BoolPCWorld => A.value P v.toPCWorld.payout) := by
  have hterms : ∀ l : List (EF × Sentence), Continuous (fun v : BoolPCWorld =>
      (l.map (fun p => p.1.denote P * v.toPCWorld.payout p.2)).sum) := by
    intro l
    induction l with
    | nil => simpa using (continuous_const : Continuous (fun _ : BoolPCWorld => (0 : ℝ)))
    | cons p ps ih =>
        simpa using (continuous_const.mul (continuous_payout p.2)).add ih
  exact continuous_const.add (hterms A.terms)

/-- Boolean worlds plausible at one finite deductive stage form a closed set. -/
lemma isClosed_consistentWith (DP : DeductiveProcess) (n : ℕ) :
    IsClosed {v : BoolPCWorld | v.toPCWorld.ConsistentWith (DP.D n)} := by
  have heq : {v : BoolPCWorld | v.toPCWorld.ConsistentWith (DP.D n)} =
      ⋂ φ : {φ // φ ∈ DP.D n}, {v : BoolPCWorld | v.toPCWorld.Holds φ.1} := by
    ext v
    simp [PCWorld.ConsistentWith]
  rw [heq]
  exact isClosed_iInter (fun φ => (isClopen_holds φ.1).1)

/-- A fixed affine sublevel set is closed. -/
lemma isClosed_affineValue_le (A : AffineCombination) (P : History) (q : ℝ) :
    IsClosed {v : BoolPCWorld | A.value P v.toPCWorld.payout ≤ q} := by
  exact isClosed_Iic.preimage (continuous_affineValue A P)

end BoolPCWorld

/-- Closed constraints used in the compactness argument: `none` is the fixed affine
sublevel set and `some n` is finite-stage plausibility. -/
def affineCompactConstraint (DP : DeductiveProcess) (A : AffineCombination)
    (P : History) (q : ℝ) : Option ℕ → Set BoolPCWorld
  | none => {v | A.value P v.toPCWorld.payout ≤ q}
  | some n => {v | v.toPCWorld.ConsistentWith (DP.D n)}

lemma affineCompactConstraint_isClosed (DP : DeductiveProcess) (A : AffineCombination)
    (P : History) (q : ℝ) (i : Option ℕ) :
    IsClosed (affineCompactConstraint DP A P q i) := by
  cases i with
  | none => exact BoolPCWorld.isClosed_affineValue_le A P q
  | some n => exact BoolPCWorld.isClosed_consistentWith DP n

/-- Propositional compactness in the precise uniform form needed by `thm:affcoh`: if a
fixed affine combination is strictly above `q` in every world consistent with the
completed theory, then after some finite stage it is above `q` in every plausible world.

The proof is a genuine compact-product argument. If bad finite-stage worlds existed
arbitrarily late, the closed finite-stage model sets together with the fixed affine
sublevel set would have the finite intersection property, hence a completed-theory bad
world. -/
theorem eventually_affineValue_gt_of_theory
    (DP : DeductiveProcess) (A : AffineCombination) (P : History) (q : ℝ)
    (hall : ∀ v : PCWorld, v.ConsistentWithTheory DP → q < A.value P v.payout) :
    ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) → q < A.value P v.payout := by
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  have hbad : ∃ᶠ n in atTop, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ A.value P v.payout ≤ q := by
    refine hnot.mono (fun n hn => ?_)
    rcases not_forall.mp hn with ⟨v, hv⟩
    rcases Classical.not_imp.mp hv with ⟨hcons, hvalue⟩
    exact ⟨v, hcons, le_of_not_gt hvalue⟩
  have hfip : ∀ u : Finset (Option ℕ),
      (Set.univ ∩ ⋂ i ∈ u, affineCompactConstraint DP A P q i).Nonempty := by
    intro u
    let K := u.sup (fun i => i.getD 0)
    obtain ⟨m, hmK, v, hv, hvalue⟩ := Filter.frequently_atTop.mp hbad K
    refine ⟨BoolPCWorld.ofPCWorld v, ?_⟩
    constructor
    · exact Set.mem_univ _
    simp only [Set.mem_iInter]
    intro i hi
    cases i with
    | none =>
        simpa [affineCompactConstraint] using hvalue
    | some n =>
        have hnK : n ≤ K := by
          exact Finset.le_sup (s := u) (f := fun i => i.getD 0) hi
        have hnm : n ≤ m := hnK.trans hmK
        have hsub : DP.D n ⊆ DP.D m := Finset.le_iff_subset.mp
          (monotone_nat_of_le_succ (fun k => Finset.le_iff_subset.mpr (DP.mono k)) hnm)
        simpa [affineCompactConstraint] using
          (show (BoolPCWorld.ofPCWorld v).toPCWorld.ConsistentWith (DP.D n) from
            fun φ hφ => by
              rw [BoolPCWorld.ofPCWorld_toPCWorld]
              exact hv φ (hsub hφ))
  obtain ⟨b, _, hb⟩ := isCompact_univ.inter_iInter_nonempty
    (affineCompactConstraint DP A P q)
    (affineCompactConstraint_isClosed DP A P q) hfip
  have hbtheory : b.toPCWorld.ConsistentWithTheory DP := by
    intro n
    have hn := Set.mem_iInter.mp hb (some n)
    simpa [affineCompactConstraint] using hn
  have hbvalue : A.value P b.toPCWorld.payout ≤ q := by
    have hnone := Set.mem_iInter.mp hb none
    simpa [affineCompactConstraint] using hnone
  have := hall b.toPCWorld hbtheory
  exact (not_lt_of_ge hbvalue) this

/-- Nonempty finite-stage plausible sets have a world in their nested intersection, i.e.
a world consistent with the completed theory. -/
lemma exists_consistentWithTheory (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ v : PCWorld, v.ConsistentWithTheory DP := by
  have hfip : ∀ u : Finset ℕ,
      (Set.univ ∩ ⋂ n ∈ u,
        {v : BoolPCWorld | v.toPCWorld.ConsistentWith (DP.D n)}).Nonempty := by
    intro u
    let K := u.sup id
    obtain ⟨v, hv⟩ := hworld K
    refine ⟨BoolPCWorld.ofPCWorld v, ?_⟩
    constructor
    · exact Set.mem_univ _
    simp only [Set.mem_iInter]
    intro n hn
    have hnK : n ≤ K := Finset.le_sup (s := u) (f := id) hn
    have hsub : DP.D n ⊆ DP.D K := Finset.le_iff_subset.mp
      (monotone_nat_of_le_succ (fun k => Finset.le_iff_subset.mpr (DP.mono k)) hnK)
    simpa using (show (BoolPCWorld.ofPCWorld v).toPCWorld.ConsistentWith (DP.D n) from
      fun φ hφ => by
        rw [BoolPCWorld.ofPCWorld_toPCWorld]
        exact hv φ (hsub hφ))
  obtain ⟨b, _, hb⟩ := isCompact_univ.inter_iInter_nonempty
    (fun n => {v : BoolPCWorld | v.toPCWorld.ConsistentWith (DP.D n)})
    (BoolPCWorld.isClosed_consistentWith DP) hfip
  exact ⟨b.toPCWorld, fun n => Set.mem_iInter.mp hb n⟩

/-- Values of `A` over all worlds consistent with the completed theory. -/
def completedAffineValues (DP : DeductiveProcess) (A : AffineCombination)
    (P : History) : Set ℝ :=
  {x | ∃ v : PCWorld, v.ConsistentWithTheory DP ∧ x = A.value P v.payout}

/-- Completed-theory affine values are nonempty when every finite stage is plausible. -/
lemma completedAffineValues_nonempty (DP : DeductiveProcess) (A : AffineCombination)
    (P : History) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (completedAffineValues DP A P).Nonempty := by
  obtain ⟨v, hv⟩ := exists_consistentWithTheory DP hworld
  exact ⟨A.value P v.payout, v, hv, rfl⟩

namespace AffineCombination

/-- The empty affine combination used before a fixed member's coefficients become
rank-legal. -/
def empty : AffineCombination where
  const := .const 0
  terms := []

/-- Member `i` of a polynomial affine sequence, padded by zero until day `i`. -/
def eventualMember (As : ℕ → AffineCombination) (i n : ℕ) : AffineCombination :=
  if i ≤ n then As i else empty

@[simp] theorem eventualMember_eq (As : ℕ → AffineCombination) (i n : ℕ) (h : i ≤ n) :
    eventualMember As i n = As i := by simp [eventualMember, h]

@[simp] theorem eventualMember_eq_empty (As : ℕ → AffineCombination) (i n : ℕ)
    (h : ¬i ≤ n) : eventualMember As i n = empty := by simp [eventualMember, h]

/-- A fixed threshold between two fixed natural outputs is polynomially fueled. -/
lemma polyFueled_if_lt_const (i a b : ℕ) :
    ∃ c, PolyFueled c (fun n => if n < i then a else b) := by
  have htest := subc_polyFueled.comp ((PolyFueled.const i).pair PolyFueled.id)
  have hpick := ifzSel_polyFueled.comp
    (((PolyFueled.const b).pair (PolyFueled.const a)).pair htest)
  exact ⟨_, hpick.of_eq (fun n => by
    simp only [Nat.unpair_pair, ifzSelFn]
    by_cases h : n < i
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega)])⟩

/-- A polynomial affine sequence can uniformly emit any one of its members forever after
that member's own index. This is the legal fixed-portfolio progression used by the first
half of affine coherence. -/
noncomputable def PolySequence.eventualMember {As : ℕ → AffineCombination}
    (h : PolySequence As) (i : ℕ) : PolySequence (eventualMember As i) := by
  let idx : ℕ → ℕ := fun z => Nat.pair i z.unpair.2
  have hidx : ∃ c, PolyFueled c idx :=
    ⟨_, (PolyFueled.const i).pair PolyFueled.right⟩
  let cidx := Classical.choose hidx
  have hcidx := Classical.choose_spec hidx
  let hconst := h.const_poly.comp (PolyFueled.const i)
  let hconstGated := PolySegStream.gateFeature hconst i
  let hcoeff := h.coefficient_poly.comp hcidx
  let cs := Classical.choose h.sentence_poly
  have hcs := Classical.choose_spec h.sentence_poly
  exact {
    termCount := fun n => if n < i then 0 else h.termCount i
    coefficient := fun z => h.coefficient (idx z)
    sentence := fun z => h.sentence (idx z)
    termCount_poly := polyFueled_if_lt_const i 0 (h.termCount i)
    const_poly := by
      refine PolySegStream.of_eq hconstGated ?_
      intro n
      by_cases hin : i ≤ n
      · simp [AffineCombination.eventualMember, hin, gateFeature]
      · simp [AffineCombination.eventualMember, hin, gateFeature, AffineCombination.empty]
    coefficient_poly := hcoeff
    sentence_poly := ⟨cs.comp cidx, hcs.comp hcidx⟩
    terms_eq := by
      intro n
      by_cases hin : i ≤ n
      · simp only [AffineCombination.eventualMember, hin, if_true, not_lt.mpr hin]
        rw [h.terms_eq]
        apply List.map_congr_left
        intro j hj
        simp [idx]
      · have hni : n < i := Nat.lt_of_not_ge hin
        simp [AffineCombination.eventualMember, hin, hni, AffineCombination.empty]
    const_rank := by
      intro n
      by_cases hin : i ≤ n
      · simpa [AffineCombination.eventualMember, hin] using (h.const_rank i).trans hin
      · simp [AffineCombination.eventualMember, hin, AffineCombination.empty]
    coefficient_rank := by
      intro n j hj
      have hin : i ≤ n := by
        by_contra hni
        have hlt : n < i := Nat.lt_of_not_ge hni
        simp [hlt] at hj
      simpa [idx] using (h.coefficient_rank i j (by simpa [not_lt.mpr hin] using hj)).trans hin
    const_closed := by
      intro n ρ V
      by_cases hin : i ≤ n
      · simpa [AffineCombination.eventualMember, hin] using h.const_closed i ρ V
      · simp [AffineCombination.eventualMember, hin, AffineCombination.empty]
    coefficient_closed := by
      intro z ρ V
      exact h.coefficient_closed (idx z) ρ V
  }

/-- Completed-theory values of a normalized bounded affine family have uniform real
bounds. -/
lemma PolySequence.completedAffineValues_bdd {As : ℕ → AffineCombination}
    (h : PolySequence As) (P : History) (DP : DeductiveProcess)
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    BddBelow (completedAffineValues DP (As n) P) ∧
      BddAbove (completedAffineValues DP (As n) P) := by
  obtain ⟨B, hB0, hB⟩ := hbounded
  obtain ⟨C, hC⟩ := hmag
  have hC0 : 0 ≤ C := (As 0).magnitude_nonneg P |>.trans (hC 0)
  have hvalue : ∀ v : PCWorld, |(As n).value P v.payout| ≤ B + C := by
    intro v
    have hdifference := (As n).abs_value_sub_price_le_magnitude P v.payout n
      (h.terms_rank n)
      (fun φ => by
        by_cases hφ : v.Holds φ
        · exact Or.inr (by simp [PCWorld.payout, hφ])
        · exact Or.inl (by simp [PCWorld.payout, hφ]))
      (hP n)
    have hprice := hB n n
    have hmagnitude := hC n
    rw [abs_le] at hdifference hprice ⊢
    constructor <;> linarith
  constructor
  · refine ⟨-(B + C), ?_⟩
    rintro x ⟨v, _, rfl⟩
    exact (abs_le.mp (hvalue v)).1
  · refine ⟨B + C, ?_⟩
    rintro x ⟨v, _, rfl⟩
    exact (abs_le.mp (hvalue v)).2

/-- Pointwise first bridge of affine coherence: the infimum over completed-theory worlds
is no greater than the limiting-belief value of each fixed member. -/
lemma PolySequence.completedTheoryLow_le_limitingValue
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (i : ℕ) :
    sInf (completedAffineValues DP (As i) P) ≤
      (As i).value P (limitingBelief P) := by
  by_contra hnot
  have hlt : (As i).value P (limitingBelief P) <
      sInf (completedAffineValues DP (As i) P) := lt_of_not_ge hnot
  obtain ⟨q, hLq, qhInf⟩ := exists_between hlt
  have hbdd := h.completedAffineValues_bdd P DP hbounded hmag hP i
  have hcompact := eventually_affineValue_gt_of_theory DP (As i) P q (fun v hv => by
    have hinf : sInf (completedAffineValues DP (As i) P) ≤ (As i).value P v.payout := by
      apply csInf_le hbdd.1
      exact ⟨v, hv, rfl⟩
    linarith)
  have hfixedVal : ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) →
        q ≤ (AffineCombination.eventualMember As i n).value P v.payout := by
    filter_upwards [hcompact, Filter.eventually_ge_atTop i] with n hn hni
    intro v hv
    rw [eventualMember_eq As i n hni]
    exact (hn v hv).le
  have hfixedPoly := h.eventualMember i
  have hprov := hfixedPoly.affine_provind P DP hworld q hfixedVal
  let L := (As i).value P (limitingBelief P)
  let ε := (q - L) / 4
  have hε : 0 < ε := by dsimp [ε, L]; linarith
  have hprovNear := hprov ε hε
  have htend := (As i).price_tendsto_limitingValue P DP hP hworld
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend ε hε
  have hpriceNear : ∀ᶠ n in atTop, |(As i).price P n - L| < ε :=
    Filter.eventually_atTop.mpr ⟨N, fun n hn => by
      simpa [Real.dist_eq, L] using hN n hn⟩
  obtain ⟨Np, hNp⟩ := Filter.eventually_atTop.mp hprovNear
  obtain ⟨Nx, hNx⟩ := Filter.eventually_atTop.mp hpriceNear
  let n := max i (max Np Nx)
  have hni : i ≤ n := by simp [n]
  have hnNp : Np ≤ n := by simp [n]
  have hnNx : Nx ≤ n := by simp [n]
  have hnprov := hNp n hnNp
  have hnprice := hNx n hnNx
  change q ≤ (AffineCombination.eventualMember As i n).price P n + ε at hnprov
  rw [AffineCombination.eventualMember_eq As i n hni] at hnprov
  rw [abs_lt] at hnprice
  dsimp [ε, L] at hnprov hnprice
  linarith

/-- Negating an affine combination negates its completed-theory value set. -/
lemma completedAffineValues_neg (DP : DeductiveProcess) (A : AffineCombination)
    (P : History) :
    completedAffineValues DP A.neg P = -(completedAffineValues DP A P) := by
  ext x
  simp only [completedAffineValues, Set.mem_setOf_eq, neg_value, Set.mem_neg]
  constructor
  · rintro ⟨v, hv, hx⟩
    exact ⟨v, hv, by linarith⟩
  · rintro ⟨v, hv, hx⟩
    exact ⟨v, hv, by linarith⟩

/-- Pointwise upper bridge, by applying the lower bridge to the uniformly emitted
negated progression. -/
lemma PolySequence.limitingValue_le_completedTheoryHigh
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (i : ℕ) :
    (As i).value P (limitingBelief P) ≤
      sSup (completedAffineValues DP (As i) P) := by
  have hnegBound : BoundedAffinePrices (fun n => (As n).neg) P := by
    obtain ⟨B, hB0, hB⟩ := hbounded
    exact ⟨B, hB0, fun n m => by simpa [neg_price] using hB n m⟩
  have hnegMag : ∃ C : ℝ, ∀ n, ((As n).neg).magnitude P ≤ C := by
    obtain ⟨C, hC⟩ := hmag
    exact ⟨C, fun n => by simpa [neg_magnitude] using hC n⟩
  have hneg := h.neg.completedTheoryLow_le_limitingValue P DP hnegBound
    hnegMag hP hworld i
  rw [completedAffineValues_neg, Real.sInf_neg, neg_value] at hneg
  linarith

end AffineCombination

/-- Completed-theory lower affine value at index `n`. -/
noncomputable def completedAffineLow (As : ℕ → AffineCombination)
    (P : History) (DP : DeductiveProcess) (n : ℕ) : ℝ :=
  sInf (completedAffineValues DP (As n) P)

/-- Completed-theory upper affine value at index `n`. -/
noncomputable def completedAffineHigh (As : ℕ → AffineCombination)
    (P : History) (DP : DeductiveProcess) (n : ℕ) : ℝ :=
  sSup (completedAffineValues DP (As n) P)

namespace AffineCombination

/-- Uniform bounds on the completed-theory extrema of a normalized bounded family. -/
lemma PolySequence.completedAffineExtrema_filterBounds
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess)
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    IsBoundedUnder (· ≥ ·) atTop (completedAffineLow As P DP) ∧
      IsBoundedUnder (· ≤ ·) atTop (completedAffineLow As P DP) ∧
      IsBoundedUnder (· ≥ ·) atTop (completedAffineHigh As P DP) ∧
      IsBoundedUnder (· ≤ ·) atTop (completedAffineHigh As P DP) := by
  obtain ⟨B, hB0, hB⟩ := hbounded
  obtain ⟨C, hC⟩ := hmag
  have hvalue : ∀ n (v : PCWorld), |(As n).value P v.payout| ≤ B + C := by
    intro n v
    have hdifference := (As n).abs_value_sub_price_le_magnitude P v.payout n
      (h.terms_rank n)
      (fun φ => by
        by_cases hφ : v.Holds φ
        · exact Or.inr (by simp [PCWorld.payout, hφ])
        · exact Or.inl (by simp [PCWorld.payout, hφ]))
      (hP n)
    have hprice := hB n n
    have hmagnitude := hC n
    rw [abs_le] at hdifference hprice ⊢
    constructor <;> linarith
  have hextrema : ∀ n,
      -(B + C) ≤ completedAffineLow As P DP n ∧
        completedAffineLow As P DP n ≤ B + C ∧
        -(B + C) ≤ completedAffineHigh As P DP n ∧
        completedAffineHigh As P DP n ≤ B + C := by
    intro n
    have hnonempty := completedAffineValues_nonempty DP (As n) P hworld
    have hbdd := h.completedAffineValues_bdd P DP
      (show BoundedAffinePrices As P from ⟨B, hB0, hB⟩) ⟨C, hC⟩ hP n
    have hmem : ∀ x ∈ completedAffineValues DP (As n) P,
        -(B + C) ≤ x ∧ x ≤ B + C := by
      rintro x ⟨v, _, rfl⟩
      exact abs_le.mp (hvalue n v)
    constructor
    · apply le_csInf hnonempty
      intro x hx
      exact (hmem x hx).1
    constructor
    · obtain ⟨x, hx⟩ := hnonempty
      exact (csInf_le hbdd.1 hx).trans (hmem x hx).2
    constructor
    · obtain ⟨x, hx⟩ := hnonempty
      exact (hmem x hx).1.trans (le_csSup hbdd.2 hx)
    · apply csSup_le hnonempty
      intro x hx
      exact (hmem x hx).2
  exact ⟨
    isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => (hextrema n).1)),
    isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n => (hextrema n).2.1)),
    isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => (hextrema n).2.2.1)),
    isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n => (hextrema n).2.2.2))⟩

/-- Paper-facing **Affine Coherence** (`thm:affcoh`). The limiting affine value lies
between completed-theory extrema in liminf/limsup, and persistence transports it to the
main diagonal. -/
theorem PolySequence.affcoh {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (liminf (completedAffineLow As P DP) atTop ≤
        liminf (fun n => (As n).value P (limitingBelief P)) atTop ∧
      liminf (fun n => (As n).value P (limitingBelief P)) atTop ≤
        liminf (fun n => (As n).price P n) atTop) ∧
      (limsup (fun n => (As n).price P n) atTop ≤
          limsup (fun n => (As n).value P (limitingBelief P)) atTop ∧
        limsup (fun n => (As n).value P (limitingBelief P)) atTop ≤
          limsup (completedAffineHigh As P DP) atTop) := by
  obtain ⟨hdlo, hdhi, hhlo, hhhi, hllo, hlhi⟩ := hbounded.filterBounds
  obtain ⟨hlimlo, hlimhi⟩ :=
    AffineCombination.BoundedAffinePrices.limitingValue_filterBounds
      hbounded DP hP hworld
  obtain ⟨htllo, htlhi, hthlo, hthhi⟩ :=
    h.completedAffineExtrema_filterBounds P DP hbounded hmag hP hworld
  have hper := h.peraffkno P DP hbounded hmag hP hworld
  have htheoryLow : ∀ n, completedAffineLow As P DP n ≤
      (As n).value P (limitingBelief P) :=
    fun n => h.completedTheoryLow_le_limitingValue P DP hbounded hmag hP hworld n
  have htheoryHigh : ∀ n, (As n).value P (limitingBelief P) ≤
      completedAffineHigh As P DP n :=
    fun n => h.limitingValue_le_completedTheoryHigh P DP hbounded hmag hP hworld n
  have hfutureLowDiag : ∀ n,
      affineFutureLow As P n ≤ (As n).price P n :=
    hbounded.futureLow_le_diagonal
  have hdiagFutureHigh : ∀ n,
      (As n).price P n ≤ affineFutureHigh As P n :=
    hbounded.diagonal_le_futureHigh
  constructor
  · constructor
    · exact liminf_le_liminf (Eventually.of_forall htheoryLow)
        htllo hlimhi.isCobounded_flip
    · calc
        liminf (fun n => (As n).value P (limitingBelief P)) atTop =
            liminf (affineFutureLow As P) atTop := hper.1.symm
        _ ≤ liminf (fun n => (As n).price P n) atTop :=
          liminf_le_liminf (Eventually.of_forall hfutureLowDiag)
            hllo hdhi.isCobounded_flip
  · constructor
    · calc
        limsup (fun n => (As n).price P n) atTop ≤
            limsup (affineFutureHigh As P) atTop :=
          limsup_le_limsup (Eventually.of_forall hdiagFutureHigh)
            hdlo.isCobounded_flip hhhi
        _ = limsup (fun n => (As n).value P (limitingBelief P)) atTop := hper.2
    · exact limsup_le_limsup (Eventually.of_forall htheoryHigh)
        hlimlo.isCobounded_flip hthhi

/-- Paper-facing lower form of **Affine Provability Induction** (`thm:affprovind`): a
uniform lower bound in every completed-theory world is learned on the main diagonal. -/
theorem PolySequence.affine_provind_theory_ge
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      b ≤ (As n).value P v.payout) :
    (fun n => (As n).price P n) ≳ₙ fun _ => b := by
  obtain ⟨_, hdhi, _, _, _, _⟩ := hbounded.filterBounds
  obtain ⟨_, htlhi, _, _⟩ :=
    h.completedAffineExtrema_filterBounds P DP hbounded hmag hP hworld
  have hlow : ∀ n, b ≤ completedAffineLow As P DP n := by
    intro n
    apply le_csInf (completedAffineValues_nonempty DP (As n) P hworld)
    rintro x ⟨v, hv, rfl⟩
    exact hval n v hv
  have hcoh := h.affcoh P DP hbounded hmag hP hworld
  have hbTheory : b ≤ liminf (completedAffineLow As P DP) atTop :=
    le_liminf_of_le htlhi.isCobounded_flip (Eventually.of_forall hlow)
  have hbDiag : b ≤ liminf (fun n => (As n).price P n) atTop :=
    hbTheory.trans (hcoh.1.1.trans hcoh.1.2)
  intro ε hε
  have hevent := eventually_lt_of_lt_liminf
    (show b - ε < liminf (fun n => (As n).price P n) atTop by linarith)
    (by
      obtain ⟨hdlo, _, _, _, _, _⟩ := hbounded.filterBounds
      exact hdlo)
  filter_upwards [hevent] with n hn
  linarith

/-- Upper form of paper-facing affine provability induction. -/
lemma PolySequence.affine_provind_theory_le
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      (As n).value P v.payout ≤ b) :
    (fun n => (As n).price P n) ≲ₙ fun _ => b := by
  have hnegBound : BoundedAffinePrices (fun n => (As n).neg) P := by
    obtain ⟨B, hB0, hB⟩ := hbounded
    exact ⟨B, hB0, fun n m => by simpa [neg_price] using hB n m⟩
  have hnegMag : ∃ C : ℝ, ∀ n, ((As n).neg).magnitude P ≤ C := by
    obtain ⟨C, hC⟩ := hmag
    exact ⟨C, fun n => by simpa [neg_magnitude] using hC n⟩
  have hneg := h.neg.affine_provind_theory_ge P DP hnegBound
    hnegMag hP hworld (-b)
    (fun n v hv => by rw [neg_value]; linarith [hval n v hv])
  intro ε hε
  filter_upwards [hneg ε hε] with n hn
  rw [neg_price] at hn
  linarith

/-- Equality form of paper-facing affine provability induction. -/
lemma PolySequence.affine_provind_theory_eq
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      (As n).value P v.payout = b) :
    (fun n => (As n).price P n) ≈ₙ fun _ => b := by
  rw [asympEq_iff_asympLE_asympGE]
  exact ⟨h.affine_provind_theory_le P DP hbounded hmag hP hworld b
      (fun n v hv => (hval n v hv).le),
    h.affine_provind_theory_ge P DP hbounded hmag hP hworld b
      (fun n v hv => (hval n v hv).ge)⟩

/-- Vanishing-error form of paper-facing affine provability induction.  This is the form
needed by quoted `[0,1]` values: the finite threshold sum approximates its represented real
value within `O(1/n)`, so completed-theory values tend uniformly to zero rather than being
definitionally zero on every index. -/
lemma PolySequence.affine_provind_theory_tendsto_zero
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWithTheory DP → |(As n).value P v.payout| ≤ ε) :
    (fun n => (As n).price P n) ≈ₙ fun _ => 0 := by
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  obtain ⟨hdlo, hdhi, _, _, _, _⟩ := hbounded.filterBounds
  obtain ⟨_, htlhi, hthlo, _⟩ :=
    h.completedAffineExtrema_filterBounds P DP hbounded hmag hP hworld
  have hcoh := h.affcoh P DP hbounded hmag hP hworld
  have hnear := hval (ε / 2) (by linarith)
  have hlow : ∀ᶠ n in atTop, -ε / 2 ≤ completedAffineLow As P DP n := by
    filter_upwards [hnear] with n hn
    apply le_csInf (completedAffineValues_nonempty DP (As n) P hworld)
    rintro x ⟨v, hv, rfl⟩
    have hx := hn v hv
    rw [abs_le] at hx
    linarith
  have hhigh : ∀ᶠ n in atTop, completedAffineHigh As P DP n ≤ ε / 2 := by
    filter_upwards [hnear] with n hn
    apply csSup_le (completedAffineValues_nonempty DP (As n) P hworld)
    rintro x ⟨v, hv, rfl⟩
    have hx := hn v hv
    rw [abs_le] at hx
    linarith
  have hliminfLow : -ε / 2 ≤ liminf (completedAffineLow As P DP) atTop :=
    le_liminf_of_le htlhi.isCobounded_flip hlow
  have hliminfPrice : -ε / 2 ≤ liminf (fun n => (As n).price P n) atTop :=
    hliminfLow.trans (hcoh.1.1.trans hcoh.1.2)
  have hlower : ∀ᶠ n in atTop, -ε < (As n).price P n :=
    eventually_lt_of_lt_liminf (by linarith) hdlo
  have hlimsupHigh : limsup (completedAffineHigh As P DP) atTop ≤ ε / 2 :=
    limsup_le_of_le hthlo.isCobounded_flip hhigh
  have hlimsupPrice : limsup (fun n => (As n).price P n) atTop ≤ ε / 2 :=
    (hcoh.2.1.trans hcoh.2.2).trans hlimsupHigh
  have hupper : ∀ᶠ n in atTop, (As n).price P n < ε :=
    eventually_lt_of_limsup_lt (by linarith) hdhi
  filter_upwards [hlower, hupper] with n hnlo hnhi
  rw [sub_zero, abs_le]
  exact ⟨hnlo.le, hnhi.le⟩

#print axioms eventually_affineValue_gt_of_theory
#print axioms AffineCombination.PolySequence.eventualMember
#print axioms AffineCombination.PolySequence.completedTheoryLow_le_limitingValue
#print axioms AffineCombination.PolySequence.affcoh
#print axioms AffineCombination.PolySequence.affine_provind_theory_eq
#print axioms AffineCombination.PolySequence.affine_provind_theory_tendsto_zero

end AffineCombination

/-- One-sided paper-facing provability induction for an efficiently codeable sequence of
completed-theory theorems. Individual proofs may appear arbitrarily later than their
sequence indices.
Paper node: `thm:affprovind` -/
theorem lic_provind_true (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ)
    (hthm : ∀ n, ∃ k, φ n ∈ DP.D k)
    (hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (φ n)) ≈ₙ fun _ => 1 := by
  have hφpoly := AffineCombination.sentenceAffine_polySequence φ hφ
  have hφeq := hφpoly.affine_provind_theory_eq P DP
    (AffineCombination.sentenceAffine_bounded φ P hP)
    ⟨1, fun n => by simp⟩ hP hworld 1 (fun n v hv => by
      obtain ⟨k, hk⟩ := hthm n
      have hholds := hv k (φ n) hk
      simp [AffineCombination.sentenceAffine, AffineCombination.value,
        PCWorld.payout, hholds])
  simpa using hφeq

/-- One-sided paper-facing provability induction for an efficiently codeable sequence
whose negations are completed-theory theorems.
Paper node: `thm:affprovind` -/
theorem lic_provind_false (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (ψ : ℕ → Sentence) (hψ : PolySentenceCodes ψ)
    (hdis : ∀ n, ∃ k, (∼ψ n) ∈ DP.D k)
    (hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (ψ n)) ≈ₙ fun _ => 0 := by
  have hψpoly := AffineCombination.sentenceAffine_polySequence ψ hψ
  have hψeq := hψpoly.affine_provind_theory_eq P DP
    (AffineCombination.sentenceAffine_bounded ψ P hP)
    ⟨1, fun n => by simp⟩ hP hworld 0 (fun n v hv => by
      obtain ⟨k, hk⟩ := hdis n
      have hneg := hv k (∼ψ n) hk
      have hfalse : ¬v.Holds (ψ n) := (PCWorld.holds_neg v (ψ n)).mp hneg
      simp [AffineCombination.sentenceAffine, AffineCombination.value,
        PCWorld.payout, hfalse])
  simpa using hψeq

/-- Faithful paper-facing **Provability Induction** (`thm:provind`). Efficient theorem
and disprovable-sentence sequences need only appear somewhere in the completed deductive
process; they need not be present by their own index.
Paper node: `thm:provind` -/
theorem lic_provind (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ ψ : ℕ → Sentence)
    (hφ : PolySentenceCodes φ) (hψ : PolySentenceCodes ψ)
    (hthm : ∀ n, ∃ k, φ n ∈ DP.D k)
    (hdis : ∀ n, ∃ k, (∼ψ n) ∈ DP.D k)
    (hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ((fun n => P n (φ n)) ≈ₙ fun _ => 1) ∧
      ((fun n => P n (ψ n)) ≈ₙ fun _ => 0) := by
  exact ⟨lic_provind_true P DP φ hφ hthm hP hworld,
    lic_provind_false P DP ψ hψ hdis hP hworld⟩

#print axioms lic_provind_true
#print axioms lic_provind_false

#print axioms lic_provind
#print axioms BoolPCWorld.eval_toBoolPCWorld_restrict
#print axioms BoolPCWorld.FiniteWorld.payoutRat_eq_toPCWorld
#print axioms BoolPCWorld.FiniteWorld.payoutRat_restrict_ofPCWorld

end LogicalInduction
