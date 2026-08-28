import LogicalInduction.Construction.Witnesses.QuotationAffine
import LogicalInduction.Properties.ExpectationProperties
import LogicalInduction.Framework.WriteOut

/-!
# Concrete syntax for polynomial LUV-combination sequences

The paper's expectations material (`sec:expectations`) works with `[0,1]`-LUVs (`def:luv`)
and finite rational combinations of them, approximating their expectations by a threshold
mesh (`lem:mesh`).  This file supplies the syntactic side of that machinery: a compact sequence
presentation naming the constants, coefficients, LUVs, and threshold sentences occurring
in a sequence of LUV combinations, from which the diagonal threshold mesh is emitted
directly — term `j * n + i` is coefficient `a_j / n` on the literal sentence `X_j > i/n`.

The presentation carries no prices, convergence, exploitation, or logical-inductor
conclusion.  Its semantic companion states only the represented threshold facts in finite
and completed stages; the public `WorldValued`, `ConvergencePresentation`, and
`ExactTheoryPresentation` packages are derived from those below.
-/

namespace LogicalInduction

/-! ## Compact combination syntax -/

/-- Operational syntax for a sequence of LUV combinations.  The LUV and coefficient at
`z = ⟨n,j⟩` are the `j`th term of member `n`.
Paper node: `def:luv` -/
structure LUVCombinationSyntax (As : ℕ → LUVCombination) where
  termCount : ℕ → ℕ
  coefficient : ℕ → EF
  luv : ℕ → LUV
  termCount_poly : ∃ c, PolyFueled c termCount
  const_poly : BigSpliceStream (fun n ↦ (As n).const.serialize)
  coefficient_poly : BigSpliceStream (fun z ↦ (coefficient z).serialize)
  threshold_poly : LUV.RpnThresholdCodeSeq luv
  terms_eq : ∀ n, (As n).terms = (List.range (termCount n)).map (fun j ↦
    (coefficient (Nat.pair n j), luv (Nat.pair n j)))
  const_rank : ∀ n, (As n).const.rank ≤ n
  coefficient_rank : ∀ n j, j < termCount n →
    (coefficient (Nat.pair n j)).rank ≤ n
  const_closed : ∀ n ρ V, (As n).const.denoteWith ρ V = (As n).const.denote V
  coefficient_closed : ∀ z ρ V,
    (coefficient z).denoteWith ρ V = (coefficient z).denote V

namespace LUVCombinationSyntax

/-- Number of threshold shares in the diagonal mesh. -/
def meshTermCount {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (n : ℕ) : ℕ :=
  S.termCount n * (n + 1)

/-- Source term containing a flattened diagonal-mesh term. -/
def meshMember {As : ℕ → LUVCombination}
    (_S : LUVCombinationSyntax As) (z : ℕ) : ℕ :=
  z.unpair.2 / (z.unpair.1 + 1)

/-- Threshold numerator within a flattened diagonal-mesh term. -/
def meshOffset {As : ℕ → LUVCombination}
    (_S : LUVCombinationSyntax As) (z : ℕ) : ℕ :=
  z.unpair.2 % (z.unpair.1 + 1)

/-- Literal coefficient `a_j / (n+1)` of a flattened threshold share. -/
def meshCoefficient {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (z : ℕ) : EF :=
  .mul (S.coefficient (Nat.pair z.unpair.1 (S.meshMember z)))
    (.const (1 / ((z.unpair.1 + 1 : ℕ) : ℚ)))

/-- Literal sentence `X_j > i/(n+1)` of a flattened threshold share. -/
def meshSentence {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (z : ℕ) : Sentence :=
  (S.luv (Nat.pair z.unpair.1 (S.meshMember z))).gt
    ((S.meshOffset z : ℚ) / ((z.unpair.1 + 1 : ℕ) : ℚ))

lemma meshTermCount_poly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) :
    ∃ c, PolyFueled c S.meshTermCount := by
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  obtain ⟨ccount, hcount⟩ := S.termCount_poly
  exact ⟨_, (hmul.comp (hcount.pair PolyFueled.id.succ_comp)).of_eq (fun n ↦ by
      simp [meshTermCount])⟩

attribute [local irreducible] Nat.sqrt in
private lemma meshDivMod_poly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) :
    ∃ c, PolyFueled c (fun z ↦ Nat.pair (S.meshMember z) (S.meshOffset z)) := by
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  have hinput : PolyFueled _ (fun z : ℕ ↦
      Nat.pair z.unpair.1 z.unpair.2) :=
    (PolyFueled.left.pair PolyFueled.right)
  refine ⟨cdm.comp _, (hdm.comp hinput).of_eq (fun z ↦ ?_)⟩
  simp [meshMember, meshOffset]

lemma meshMember_poly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) :
    ∃ c, PolyFueled c S.meshMember := by
  obtain ⟨c, h⟩ := S.meshDivMod_poly
  exact ⟨Nat.Partrec.Code.left.comp c,
    (PolyFueled.left.comp h).of_eq (fun z ↦ by simp)⟩

lemma meshOffset_poly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) :
    ∃ c, PolyFueled c S.meshOffset := by
  obtain ⟨c, h⟩ := S.meshDivMod_poly
  exact ⟨Nat.Partrec.Code.right.comp c,
    (PolyFueled.right.comp h).of_eq (fun z ↦ by simp)⟩

lemma getD_flatMap_const_width_any {α : Type*} (f : ℕ → List α)
    (d : α) (W : ℕ) (hW0 : 0 < W) :
    ∀ c i, (∀ j < c, (f j).length = W) → i < c * W →
      ((List.range c).flatMap f).getD i d = (f (i / W)).getD (i % W) d := by
  intro c
  induction c with
  | zero => intro i _ hi; simp at hi
  | succ c ih =>
      intro i hlen hi
      have hprefix : ((List.range c).flatMap f).length = c * W :=
        length_flatMap_const_width f W c (fun j hj ↦ hlen j (by omega))
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      rcases Nat.lt_or_ge i (c * W) with hleft | hright
      · rw [List.getD_append _ _ _ _ (by simpa [hprefix] using hleft)]
        exact ih i (fun j hj ↦ hlen j (by omega)) hleft
      · have hic : i / W = c := by
          apply Nat.le_antisymm
          · have := (Nat.div_lt_iff_lt_mul hW0).2 hi
            omega
          · exact (Nat.le_div_iff_mul_le hW0).2 hright
        rw [List.getD_append_right _ _ _ _ (by simpa [hprefix] using hright), hprefix,
          hic]
        congr 1
        have hqr := Nat.div_add_mod i W
        have heq : c * W + i % W = i := by
          simpa [hic, Nat.mul_comm] using hqr
        omega

lemma flatMap_threshold_terms (l : List (EF × LUV)) (n : ℕ) :
    l.flatMap (fun p ↦ ((p.2.expectAffine n).scale p.1).terms) =
      (List.range (l.length * n)).map (fun t ↦
        let p := l.getD (t / n) (EF.const 0, (⟨fun _ ↦ ⊤⟩ : LUV))
        (.mul p.1 (.const (1 / (n : ℚ))),
          p.2.gt (((t % n : ℕ) : ℚ) / (n : ℚ)))) := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_range]
    induction l with
    | nil => simp
    | cons p l ih =>
        simp [LUV.expectAffine, AffineCombination.scale, Nat.add_mul,
          Nat.add_comm]
  · intro t ht htright
    have hn : 0 < n := by
      by_contra hzero
      simp only [Nat.not_lt, Nat.le_zero] at hzero
      subst n
      simp at htright
    rw [← List.getD_eq_getElem (l := l.flatMap
      (fun p ↦ ((p.2.expectAffine n).scale p.1).terms))
      (d := (EF.const 0, (⊤ : Sentence))) ht]
    have hlist : l = (List.range l.length).map (fun j ↦
        l.getD j (EF.const 0, (⟨fun _ ↦ ⊤⟩ : LUV))) := by
      apply List.ext_getElem
      · simp
      · intro j hj₁ hj₂
        rw [List.getElem_map, List.getElem_range]
        exact (List.getD_eq_getElem (l := l)
          (d := (EF.const 0, (⟨fun _ ↦ ⊤⟩ : LUV))) hj₁).symm
    have hflat : l.flatMap (fun p ↦ ((p.2.expectAffine n).scale p.1).terms) =
        (List.range l.length).flatMap (fun j ↦
          let p := l.getD j (EF.const 0, (⟨fun _ ↦ ⊤⟩ : LUV))
          ((p.2.expectAffine n).scale p.1).terms) := by
      calc
        l.flatMap (fun p ↦ ((p.2.expectAffine n).scale p.1).terms) =
            ((List.range l.length).map (fun j ↦
              l.getD j (EF.const 0, (⟨fun _ ↦ ⊤⟩ : LUV)))).flatMap
              (fun p ↦ ((p.2.expectAffine n).scale p.1).terms) :=
          congrArg (fun q ↦ q.flatMap
            (fun p ↦ ((p.2.expectAffine n).scale p.1).terms)) hlist
        _ = _ := by rw [List.flatMap_map]
    rw [hflat]
    have htotal : t < l.length * n := by simpa using htright
    rw [getD_flatMap_const_width_any
      (α := EF × Sentence) _ _ n hn l.length t (fun j hj ↦ by
      simp [LUV.expectAffine, AffineCombination.scale]) htotal]
    have hmember : t / n < l.length := (Nat.div_lt_iff_lt_mul hn).2 htotal
    have hoffset : t % n < n := Nat.mod_lt t hn
    let p := l.getD (t / n) (EF.const 0, (⟨fun _ ↦ ⊤⟩ : LUV))
    have hblock : (((p.2.expectAffine n).scale p.1).terms).length = n := by
      simp [LUV.expectAffine, AffineCombination.scale]
    have hboff : t % n < (((p.2.expectAffine n).scale p.1).terms).length := by
      rw [hblock]
      exact hoffset
    rw [List.getD_eq_getElem (l := ((p.2.expectAffine n).scale p.1).terms)
      (d := (EF.const 0, (⊤ : Sentence))) hboff]
    simp [p, LUV.expectAffine, AffineCombination.scale]

/-- The compact LUV syntax emits the exact diagonal threshold mesh consumed by the affine
property theorems. -/
noncomputable def diagonalMeshPoly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) :
    AffineCombination.PolySequence (fun n ↦ (As n).meshAffine (n + 1)) := by
  let cmember := Classical.choose S.meshMember_poly
  have hmember := Classical.choose_spec S.meshMember_poly
  let coffset := Classical.choose S.meshOffset_poly
  have hoffset := Classical.choose_spec S.meshOffset_poly
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  have hthreshold := S.threshold_poly
  have hsource : PolyFueled _ (fun z ↦
      Nat.pair z.unpair.1 (S.meshMember z)) :=
    PolyFueled.left.pair hmember
  have hcoeffSource := S.coefficient_poly.comp hsource
  have hinvSource := BigSpliceStream.serialize_const_comp
    ⟨_, hinv.comp PolyFueled.left.succ_comp⟩
  have hquery : PolyFueled _ (fun z : ℕ ↦
      Nat.pair (Nat.pair z.unpair.1 (S.meshMember z))
        (Nat.pair (z.unpair.1 + 1) (S.meshOffset z))) :=
    hsource.pair (PolyFueled.left.succ_comp.pair hoffset)
  refine {
    termCount := S.meshTermCount
    coefficient := S.meshCoefficient
    sentence := S.meshSentence
    termCount_poly := S.meshTermCount_poly
    const_poly := S.const_poly
    coefficient_poly := BigSpliceStream.of_eq
      (BigSpliceStream.serialize_mul hcoeffSource hinvSource) (fun z ↦ by
        simp [meshCoefficient])
    sentence_poly :=
      (BigSentenceCodes.ofRpnSentenceCodes (hthreshold.comp hquery)).of_eq (fun z ↦ by
        simp [meshSentence])
    terms_eq := ?_
    const_rank := S.const_rank
    coefficient_rank := ?_
    const_closed := S.const_closed
    coefficient_closed := ?_
  }
  · intro n
    rw [LUVCombination.meshAffine, S.terms_eq]
    rw [flatMap_threshold_terms]
    simp only [List.length_map, List.length_range]
    rw [meshTermCount]
    apply List.map_congr_left
    intro t ht
    simp only [List.mem_range] at ht
    have hj : t / (n + 1) < S.termCount n :=
      (Nat.div_lt_iff_lt_mul n.succ_pos).2 ht
    have hidx : t / (n + 1) < ((List.range (S.termCount n)).map fun j ↦
        (S.coefficient (Nat.pair n j), S.luv (Nat.pair n j))).length := by
      simpa using hj
    rw [List.getD_eq_getElem (l := (List.range (S.termCount n)).map fun j ↦
      (S.coefficient (Nat.pair n j), S.luv (Nat.pair n j)))
      (d := (EF.const 0, (⟨fun _ ↦ ⊤⟩ : LUV))) hidx]
    simp [meshCoefficient, meshSentence, meshMember, meshOffset]
  · intro n t ht
    simp only [meshCoefficient, Nat.unpair_pair, EF.rank]
    apply Nat.max_le.mpr
    refine ⟨?_, by simp⟩
    have hj : t / (n + 1) < S.termCount n :=
      (Nat.div_lt_iff_lt_mul n.succ_pos).2 (by simpa [meshTermCount] using ht)
    simpa [meshMember] using S.coefficient_rank n (t / (n + 1)) hj
  · intro z ρ V
    simp only [meshCoefficient, EF.denoteWith, EF.denote_mul, EF.denote_const,
      Pi.mul_apply]
    rw [S.coefficient_closed]

/-- Public polynomial-sequence boundary discharged from compact component syntax. -/
noncomputable def polySequence {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) : LUVCombination.PolySequence As where
  mesh_poly := S.diagonalMeshPoly

/-! ## Exact represented semantics -/

/-- Completed-theory truth laws for the threshold families named by a compact syntax
presentation.  These are representation facts only, and they are quantified over
`cworlds(Θ)` alone — no stage-indexed valuation is assumed. -/
structure TheorySemantics {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (DP : DeductiveProcess) where
  value : ℕ → LUV → ℝ
  value_mem : ∀ n j, j < S.termCount n →
    0 ≤ value n (S.luv (Nat.pair n j)) ∧
      value n (S.luv (Nat.pair n j)) ≤ 1
  completed_threshold_iff : ∀ n j, j < S.termCount n →
    ∀ (v : PCWorld), v.ConsistentWithTheory DP → ∀ r : ℚ,
      v.Holds ((S.luv (Nat.pair n j)).gt r) ↔
        (r : ℝ) < value n (S.luv (Nat.pair n j))

lemma threshold_code {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (n : ℕ) (p : EF × LUV)
    (hp : p ∈ (As n).terms) : p.2.RpnThresholdCodes := by
  rw [S.terms_eq] at hp
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  have hquery : PolyFueled _ (fun m : ℕ ↦
      Nat.pair (Nat.pair n j) m) := (PolyFueled.const (Nat.pair n j)).pair PolyFueled.id
  exact (S.threshold_poly.comp hquery).of_eq (fun m ↦ by simp)

/-- Compact syntax plus completed-theory representation discharges the exact presentation. -/
def exactTheoryPresentation {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) {DP : DeductiveProcess}
    (H : S.TheorySemantics DP) : LUVCombination.ExactTheoryPresentation As DP where
  value := H.value
  value_mem := by
    intro n p hp
    rw [S.terms_eq] at hp
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    exact H.value_mem n j hj
  threshold_iff := by
    intro n v hv p hp r
    rw [S.terms_eq] at hp
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    exact H.completed_threshold_iff n j hj v hv r

/-- The completed-world valuation boundary follows from the exact presentation. -/
def worldValued {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) {DP : DeductiveProcess}
    (H : S.TheorySemantics DP) : LUVCombination.WorldValued As DP :=
  (S.exactTheoryPresentation H).toWorldValued

end LUVCombinationSyntax


/-! ## Generic triangular softmax compiler

The mesh selector on day `m` scans a triangular family `G m 0, …, G m (m-1)`.
We encode a member at the strictly positive paired index `⟨m,i+1⟩`; this keeps every
member's feature rank below its `AffineCombination.PolySequence` index, including the
corner at day zero. -/

namespace AffineCombination

open LUVCombination

def triangularIndex (m i : ℕ) : ℕ := Nat.pair m (i + 1)

def triangularGaps (G : ℕ → AffineCombination) (m : ℕ) : List AffineCombination :=
  (List.range m).map (fun i ↦ G (triangularIndex m i))

private lemma triangularGaps_take (G : ℕ → AffineCombination) (m i : ℕ)
    (hi : i ≤ m) :
    (triangularGaps G m).take i =
      (List.range i).map (fun j ↦ G (triangularIndex m j)) := by
  rw [triangularGaps, ← List.map_take, List.take_range, Nat.min_eq_left hi]

@[simp] private theorem take_map_triangular_range (G : ℕ → AffineCombination)
    (m i : ℕ) (hi : i ≤ m) :
    ((List.range m).map (fun j ↦ G (triangularIndex m j))).take i =
      (List.range i).map (fun j ↦ G (triangularIndex m j)) := by
  exact triangularGaps_take G m i hi

/-- Remaining first-active mass before triangular member `i`. -/
def triangularRemainder (G : ℕ → AffineCombination) (m i : ℕ)
    (threshold pad : ℚ) : EF :=
  match i with
  | 0 => .const 1
  | i + 1 => .mul (triangularRemainder G m i threshold pad)
      (oneMinus (sellIndF ((G (triangularIndex m i)).priceFeature m) threshold pad))

def triangularSignal (G : ℕ → AffineCombination) (m i : ℕ)
    (threshold pad : ℚ) : EF :=
  sellIndF ((G (triangularIndex m i)).priceFeature m) threshold pad

def triangularWeight (G : ℕ → AffineCombination) (m i : ℕ)
    (threshold pad : ℚ) : EF :=
  .mul (triangularRemainder G m i threshold pad)
    (triangularSignal G m i threshold pad)

private lemma softmaxRemainder_take_succ
    (gaps : List AffineCombination) (day i : ℕ) (threshold pad : ℚ)
    (remaining : EF) (hi : i < gaps.length) :
    softmaxRemainder (gaps.take (i + 1)) day threshold pad remaining =
      .mul (softmaxRemainder (gaps.take i) day threshold pad remaining)
        (oneMinus (sellIndF ((gaps.get ⟨i, hi⟩).priceFeature day) threshold pad)) := by
  induction i generalizing gaps remaining with
  | zero =>
      cases gaps with
      | nil => simp at hi
      | cons A rest => simp [softmaxRemainder]
  | succ i ih =>
      cases gaps with
      | nil => simp at hi
      | cons A rest =>
          have hi' : i < rest.length := by simpa using hi
          simp only [List.take_succ_cons, softmaxRemainder]
          rw [ih rest (.mul remaining
            (oneMinus (sellIndF (A.priceFeature day) threshold pad))) hi']
          rfl

private lemma foldr_congr_mem {α β : Type*} (l : List α)
    (f g : α → β → β) (init : β)
    (h : ∀ x ∈ l, ∀ acc, f x acc = g x acc) :
    l.foldr f init = l.foldr g init := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldr_cons]
      rw [ih]
      · exact h x (by simp) _
      · intro y hy acc
        exact h y (by simp [hy]) acc

lemma triangularRemainder_succ (G : ℕ → AffineCombination)
    (m i : ℕ) (threshold pad : ℚ) (_hi : i < m) :
    triangularRemainder G m (i + 1) threshold pad =
      .mul (triangularRemainder G m i threshold pad)
        (oneMinus (triangularSignal G m i threshold pad)) := by
  rfl

private lemma softmaxRemainder_append
    (xs ys : List AffineCombination) (day : ℕ) (threshold pad : ℚ)
    (remaining : EF) :
    softmaxRemainder (xs ++ ys) day threshold pad remaining =
      softmaxRemainder ys day threshold pad
        (softmaxRemainder xs day threshold pad remaining) := by
  induction xs generalizing remaining with
  | nil => rfl
  | cons A rest ih =>
      simp only [List.cons_append, softmaxRemainder]
      exact ih _

@[simp] theorem softmaxRemainder_triangular_prefix
    (G : ℕ → AffineCombination) (m i : ℕ) (threshold pad : ℚ) :
    softmaxRemainder ((List.range i).map (fun j ↦ G (triangularIndex m j)))
        m threshold pad (.const 1) =
      triangularRemainder G m i threshold pad := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [List.range_succ, List.map_append, softmaxRemainder_append]
      simp only [List.map_singleton, softmaxRemainder]
      rw [ih]
      rfl

private lemma softmaxAffine_terms_eq_flatten
    (gaps : List AffineCombination) (day : ℕ) (threshold pad : ℚ)
    (remaining : EF) :
    (softmaxAffine gaps day threshold pad remaining).terms =
      (List.range gaps.length).flatMap (fun i ↦
        let rem := softmaxRemainder (gaps.take i) day threshold pad remaining
        let signal := sellIndF ((gaps.getD i empty).priceFeature day) threshold pad
        ((gaps.getD i empty).scale (.mul rem signal)).terms) := by
  induction gaps generalizing remaining with
  | nil => simp [softmaxAffine, empty]
  | cons A rest ih =>
      simp only [softmaxAffine, AffineCombination.add, List.length_cons]
      rw [List.range_succ_eq_map, List.flatMap_cons]
      simp only [List.take_zero, softmaxRemainder]
      congr 1
      rw [ih]
      rw [List.flatMap_map]
      apply List.flatMap_congr
      intro i hi
      simp only [List.mem_range] at hi
      simp [hi, List.take_succ_cons, softmaxRemainder, Nat.succ_eq_add_one]

private lemma softmaxAffine_const_eq_fold
    (gaps : List AffineCombination) (day : ℕ) (threshold pad : ℚ)
    (remaining : EF) :
    (softmaxAffine gaps day threshold pad remaining).const =
      (List.range gaps.length).foldr (fun i acc ↦
        let rem := softmaxRemainder (gaps.take i) day threshold pad remaining
        let signal := sellIndF ((gaps.getD i empty).priceFeature day) threshold pad
        .add (.mul (.mul rem signal) (gaps.getD i empty).const) acc)
        (.const 0) := by
  induction gaps generalizing remaining with
  | nil => simp [softmaxAffine, AffineCombination.empty]
  | cons A rest ih =>
      simp only [softmaxAffine, AffineCombination.add, AffineCombination.scale,
        List.length_cons]
      rw [List.range_succ_eq_map, List.foldr_cons]
      simp only [List.take_zero, softmaxRemainder]
      congr 1
      rw [ih]
      rw [List.foldr_map]
      apply foldr_congr_mem
      intro i hi acc
      simp only [List.mem_range] at hi
      simp [hi, List.take_succ_cons, softmaxRemainder, Nat.succ_eq_add_one]

lemma softmaxAffine_triangular_terms (G : ℕ → AffineCombination)
    (m : ℕ) (threshold pad : ℚ) :
    (softmaxAffine (triangularGaps G m) m threshold pad (.const 1)).terms =
      (List.range m).flatMap (fun i ↦
        ((G (triangularIndex m i)).scale
          (triangularWeight G m i threshold pad)).terms) := by
  rw [softmaxAffine_terms_eq_flatten]
  simp only [triangularGaps, List.length_map, List.length_range]
  apply List.flatMap_congr
  intro i hi
  simp only [List.mem_range] at hi
  simp [triangularWeight, triangularSignal, hi, Nat.le_of_lt hi]

lemma softmaxAffine_triangular_const (G : ℕ → AffineCombination)
    (m : ℕ) (threshold pad : ℚ) :
    (softmaxAffine (triangularGaps G m) m threshold pad (.const 1)).const =
      (List.range m).foldr (fun i acc ↦
        .add (.mul (triangularWeight G m i threshold pad)
          (G (triangularIndex m i)).const) acc) (.const 0) := by
  rw [softmaxAffine_const_eq_fold]
  simp only [triangularGaps, List.length_map, List.length_range]
  apply foldr_congr_mem
  intro i hi acc
  simp only [List.mem_range] at hi
  simp [triangularWeight, triangularSignal, hi, Nat.le_of_lt hi]

/-! ### Polynomial emission of the triangular selector -/

def triangularMemberLength {G : ℕ → AffineCombination}
    (hG : PolySequence G) (z : ℕ) : ℕ :=
  hG.termCount (triangularIndex z.unpair.1 z.unpair.2)

def triangularTermCount {G : ℕ → AffineCombination}
    (hG : PolySequence G) (m : ℕ) : ℕ :=
  segPrefix (triangularMemberLength hG) m m

def triangularMember {G : ℕ → AffineCombination}
    (hG : PolySequence G) (z : ℕ) : ℕ :=
  segLocate (triangularMemberLength hG) z.unpair.1 z.unpair.2 z.unpair.1

def triangularOffset {G : ℕ → AffineCombination}
    (hG : PolySequence G) (z : ℕ) : ℕ :=
  z.unpair.2 - segPrefix (triangularMemberLength hG) z.unpair.1
    (triangularMember hG z)

def triangularCoefficient {G : ℕ → AffineCombination}
    (hG : PolySequence G) (threshold pad : ℚ) (z : ℕ) : EF :=
  .mul (triangularWeight G z.unpair.1 (triangularMember hG z) threshold pad)
    (hG.coefficient (Nat.pair
      (triangularIndex z.unpair.1 (triangularMember hG z)) (triangularOffset hG z)))

def triangularSentence {G : ℕ → AffineCombination}
    (hG : PolySequence G) (z : ℕ) : Sentence :=
  hG.sentence (Nat.pair
    (triangularIndex z.unpair.1 (triangularMember hG z)) (triangularOffset hG z))

private lemma triangularMemberLength_poly {G : ℕ → AffineCombination}
    (hG : PolySequence G) :
    ∃ c, PolyFueled c (triangularMemberLength hG) := by
  obtain ⟨c, hc⟩ := hG.termCount_poly
  have hindex : PolyFueled _ (fun z : ℕ ↦ triangularIndex z.unpair.1 z.unpair.2) :=
    (PolyFueled.left.pair PolyFueled.right.succ_comp).of_eq (fun z ↦ by
      simp [triangularIndex])
  exact ⟨c.comp _, hc.comp hindex⟩

private lemma triangularTermCount_poly {G : ℕ → AffineCombination}
    (hG : PolySequence G) :
    ∃ c, PolyFueled c (triangularTermCount hG) := by
  obtain ⟨_, hlen⟩ := triangularMemberLength_poly hG
  obtain ⟨c, hc⟩ := segPrefix_polyFueled hlen
  exact ⟨c.comp _, (hc.comp (PolyFueled.id.pair PolyFueled.id)).of_eq (fun m ↦ by
    simp [triangularTermCount])⟩

private lemma triangularMember_poly {G : ℕ → AffineCombination}
    (hG : PolySequence G) :
    ∃ c, PolyFueled c (triangularMember hG) := by
  obtain ⟨_, hlen⟩ := triangularMemberLength_poly hG
  obtain ⟨c, hc⟩ := segLocate_polyFueled hlen
  exact ⟨c.comp _, (hc.comp (PolyFueled.id.pair PolyFueled.left)).of_eq (fun z ↦ by
    simp [triangularMember])⟩

private lemma triangularOffset_poly {G : ℕ → AffineCombination}
    (hG : PolySequence G) :
    ∃ c, PolyFueled c (triangularOffset hG) := by
  obtain ⟨_, hlen⟩ := triangularMemberLength_poly hG
  obtain ⟨_, hmember⟩ := triangularMember_poly hG
  obtain ⟨_, hprefix⟩ := segPrefix_polyFueled hlen
  have hp := hprefix.comp (PolyFueled.left.pair hmember)
  exact ⟨_, (subc_polyFueled.comp (PolyFueled.right.pair hp)).of_eq (fun z ↦ by
    simp [triangularOffset])⟩

private lemma triangularRemainder_serialize (G : ℕ → AffineCombination)
    (m i : ℕ) (threshold pad : ℚ) :
    (triangularRemainder G m i threshold pad).serialize =
      (EF.const 1).serialize ++ (List.range i).flatMap (fun k ↦
        (oneMinus (triangularSignal G m k threshold pad)).serialize ++ [3]) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [triangularRemainder, EF.serialize, List.range_succ,
        List.flatMap_append, List.flatMap_singleton, ih]
      simp [triangularSignal, List.append_assoc]

private lemma foldr_add_serialize { α : Type* } (l : List α) (f : α → EF) :
    (l.foldr (fun i acc ↦ EF.add (f i) acc) (EF.const 0)).serialize =
      l.flatMap (fun i ↦ (f i).serialize) ++
        (EF.const 0).serialize ++ List.replicate l.length 2 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldr_cons, List.flatMap_cons, EF.serialize, ih,
        List.length_cons, List.replicate_succ']
      simp [List.append_assoc]

private lemma triangularFold_serialize (G : ℕ → AffineCombination)
    (m : ℕ) (threshold pad : ℚ) :
    ((List.range m).foldr (fun i acc ↦
      EF.add (EF.mul (triangularWeight G m i threshold pad)
        (G (triangularIndex m i)).const) acc) (EF.const 0)).serialize =
      (List.range m).flatMap (fun i ↦
        (EF.mul (triangularWeight G m i threshold pad)
          (G (triangularIndex m i)).const).serialize) ++
        (EF.const 0).serialize ++ List.replicate m 2 := by
  simpa using foldr_add_serialize (List.range m) (fun i ↦
    EF.mul (triangularWeight G m i threshold pad) (G (triangularIndex m i)).const)

private lemma triangularSignal_polySeg {G : ℕ → AffineCombination}
    (hG : PolySequence G) (threshold pad : ℚ) :
    BigSpliceStream (fun z ↦
      (triangularSignal G z.unpair.1 z.unpair.2 threshold pad).serialize) := by
  have hquery : PolyFueled _ (fun z : ℕ ↦
      Nat.pair (triangularIndex z.unpair.1 z.unpair.2) z.unpair.1) :=
    ((PolyFueled.left.pair PolyFueled.right.succ_comp).pair
      PolyFueled.left).of_eq (fun z ↦ by simp [triangularIndex])
  refine BigSpliceStream.of_eq
    (BigSpliceStream.serialize_sellIndF (hG.priceFeature_polySeg.comp hquery)
      threshold pad) ?_
  intro z
  simp [triangularSignal]

private lemma triangularRemainder_polySeg {G : ℕ → AffineCombination}
    (hG : PolySequence G) (threshold pad : ℚ) :
    BigSpliceStream (fun z ↦
      (triangularRemainder G z.unpair.1 z.unpair.2 threshold pad).serialize) := by
  have hsig := triangularSignal_polySeg hG threshold pad
  have hone : BigSpliceStream (fun _ : ℕ ↦ (EF.const 1).serialize) :=
    BigSpliceStream.serialize_const 1
  have hneg : BigSpliceStream (fun _ : ℕ ↦ (EF.const (-1)).serialize) :=
    BigSpliceStream.serialize_const (-1)
  have honeMinus := BigSpliceStream.serialize_add hone
    (BigSpliceStream.serialize_mul hneg hsig)
  have hblock := honeMinus.append (BigSpliceStream.tag 3 (by norm_num))
  have hreindex : PolyFueled _ (fun q : ℕ ↦
      Nat.pair q.unpair.1.unpair.1 q.unpair.2) :=
    (PolyFueled.left.comp PolyFueled.left).pair PolyFueled.right
  have hblocks := BigSpliceStream.concatVar (hblock.comp hreindex) PolyFueled.right
  refine BigSpliceStream.of_eq (hone.append hblocks) ?_
  intro z
  rw [triangularRemainder_serialize]
  simp [oneMinus]

private lemma triangularWeight_polySeg {G : ℕ → AffineCombination}
    (hG : PolySequence G) (threshold pad : ℚ) :
    BigSpliceStream (fun z ↦
      (triangularWeight G z.unpair.1 z.unpair.2 threshold pad).serialize) :=
  BigSpliceStream.serialize_mul (triangularRemainder_polySeg hG threshold pad)
    (triangularSignal_polySeg hG threshold pad)

private lemma triangularMember_lt {G : ℕ → AffineCombination}
    (hG : PolySequence G) {m j : ℕ} (hj : j < triangularTermCount hG m) :
    triangularMember hG (Nat.pair m j) < m := by
  let lenFn := triangularMemberLength hG
  let i := triangularMember hG (Nat.pair m j)
  have hile : i ≤ m := by
    simpa [i, triangularMember] using segLocate_le lenFn m j m
  rcases Nat.eq_or_lt_of_le hile with heq | hi
  · have hlo := (segLocate_spec lenFn m j m).1
    have hid : segLocate lenFn m j m = i := by
      simp [i, triangularMember, lenFn]
    rw [hid, heq] at hlo
    exact absurd hlo (by simpa [triangularTermCount, lenFn] using hj)
  · exact hi

private lemma triangularOffset_lt {G : ℕ → AffineCombination}
    (hG : PolySequence G) {m j : ℕ} (hj : j < triangularTermCount hG m) :
    triangularOffset hG (Nat.pair m j) <
      hG.termCount (triangularIndex m (triangularMember hG (Nat.pair m j))) := by
  let lenFn := triangularMemberLength hG
  let i := triangularMember hG (Nat.pair m j)
  have hi := triangularMember_lt hG hj
  have hlo := (segLocate_spec lenFn m j m).1
  have hhi : j < segPrefix lenFn m (i + 1) := by
    by_contra hnot
    have hle : segPrefix lenFn m (i + 1) ≤ j := le_of_not_gt hnot
    have hmax := (segLocate_spec lenFn m j m).2
    have := hmax (i + 1) (by omega) hle
    have hid : segLocate lenFn m j m = i := by
      simp [i, triangularMember, lenFn]
    rw [hid] at this
    omega
  rw [segPrefix_succ] at hhi
  have hlo' : segPrefix lenFn m i ≤ j := by
    have hid : segLocate lenFn m j m = i := by
      simp [i, triangularMember, lenFn]
    simpa [hid] using hlo
  have hoff : j - segPrefix lenFn m i < lenFn (Nat.pair m i) := by omega
  simpa [triangularOffset, i, lenFn, triangularMemberLength] using hoff

private lemma triangularRemainder_rank_le (G : ℕ → AffineCombination)
    (m i : ℕ) (threshold pad : ℚ)
    (hconst : ∀ k, k < i → (G (triangularIndex m k)).const.rank ≤ m)
    (hterms : ∀ k, k < i → ∀ p ∈ (G (triangularIndex m k)).terms,
      p.1.rank ≤ m) :
    (triangularRemainder G m i threshold pad).rank ≤ m := by
  induction i with
  | zero => simp [triangularRemainder]
  | succ i ih =>
      simp only [triangularRemainder, EF.rank, oneMinus_rank, sellIndF_rank]
      apply Nat.max_le.mpr
      constructor
      · exact ih (fun k hk ↦ hconst k (by omega))
          (fun k hk ↦ hterms k (by omega))
      · exact (G (triangularIndex m i)).priceFeature_rank le_rfl
          (hconst i (by omega)) (hterms i (by omega))

private lemma triangularWeight_rank_le (G : ℕ → AffineCombination)
    (m i : ℕ) (threshold pad : ℚ)
    (hconst : ∀ k, k ≤ i → (G (triangularIndex m k)).const.rank ≤ m)
    (hterms : ∀ k, k ≤ i → ∀ p ∈ (G (triangularIndex m k)).terms,
      p.1.rank ≤ m) :
    (triangularWeight G m i threshold pad).rank ≤ m := by
  simp only [triangularWeight, triangularSignal, EF.rank, sellIndF_rank]
  exact Nat.max_le.mpr ⟨
    triangularRemainder_rank_le G m i threshold pad
      (fun k hk ↦ hconst k (by omega)) (fun k hk ↦ hterms k (by omega)),
    (G (triangularIndex m i)).priceFeature_rank le_rfl
      (hconst i le_rfl) (hterms i le_rfl)⟩

private lemma triangularRemainder_closed {G : ℕ → AffineCombination}
    (hG : PolySequence G) (m i : ℕ) (threshold pad : ℚ) (ρ : List ℝ)
    (V : History) :
    (triangularRemainder G m i threshold pad).denoteWith ρ V =
      (triangularRemainder G m i threshold pad).denote V := by
  induction i with
  | zero => simp [triangularRemainder]
  | succ i ih =>
      simp only [triangularRemainder, EF.denoteWith, EF.denote_mul, Pi.mul_apply]
      rw [ih]
      exact congrArg ((triangularRemainder G m i threshold pad).denote V * ·)
        (oneMinus_closed (sellIndF_closed threshold pad
          (hG.priceFeature_closed (triangularIndex m i) m ρ V)))

private lemma triangularWeight_closed {G : ℕ → AffineCombination}
    (hG : PolySequence G) (m i : ℕ) (threshold pad : ℚ) (ρ : List ℝ)
    (V : History) :
    (triangularWeight G m i threshold pad).denoteWith ρ V =
      (triangularWeight G m i threshold pad).denote V := by
  simp only [triangularWeight, triangularSignal, EF.denoteWith, EF.denote_mul,
    Pi.mul_apply]
  rw [triangularRemainder_closed hG, sellIndF_closed threshold pad
    (hG.priceFeature_closed (triangularIndex m i) m ρ V)]

/-- A polynomial triangular affine family has a polynomial first-active softmax.
The two rank hypotheses are the necessary cross-index legality condition: although member
`i` is stored at a paired global index, it is priced and traded on the enclosing day `m`. -/
noncomputable def triangularSoftmaxPoly {G : ℕ → AffineCombination}
    (hG : PolySequence G) (threshold pad : ℚ)
    (hconstRank : ∀ m i, i < m → (G (triangularIndex m i)).const.rank ≤ m)
    (htermsRank : ∀ m i, i < m → ∀ p ∈ (G (triangularIndex m i)).terms,
      p.1.rank ≤ m) :
    PolySequence (fun m ↦
      softmaxAffine (triangularGaps G m) m threshold pad (.const 1)) := by
  let cmember := Classical.choose (triangularMember_poly hG)
  have hmember := Classical.choose_spec (triangularMember_poly hG)
  let coffset := Classical.choose (triangularOffset_poly hG)
  have hoffset := Classical.choose_spec (triangularOffset_poly hG)
  have hcanonical : PolyFueled _ (fun z : ℕ ↦ Nat.pair
      (triangularIndex z.unpair.1 (triangularMember hG z))
      (triangularOffset hG z)) :=
    ((PolyFueled.left.pair hmember.succ_comp).pair hoffset).of_eq (fun z ↦ by
      simp [triangularIndex])
  have hweight := triangularWeight_polySeg hG threshold pad
  have hweightMember := hweight.comp (PolyFueled.left.pair hmember)
  have hcoefficient := BigSpliceStream.serialize_mul hweightMember
    (hG.coefficient_poly.comp hcanonical)
  have hsourceIndex : PolyFueled _ (fun z : ℕ ↦
      triangularIndex z.unpair.1 z.unpair.2) :=
    (PolyFueled.left.pair PolyFueled.right.succ_comp).of_eq (fun z ↦ by
      simp [triangularIndex])
  have hconstBlock := BigSpliceStream.serialize_mul hweight
    (hG.const_poly.comp hsourceIndex)
  have hconstTerms := BigSpliceStream.concatVar hconstBlock PolyFueled.id
  have hzero : BigSpliceStream (fun _ : ℕ ↦ (EF.const 0).serialize) :=
    BigSpliceStream.serialize_const 0
  have htags := BigSpliceStream.repeatTag 2 (by norm_num) PolyFueled.id
  have hconstRaw := (hconstTerms.append hzero).append htags
  have hconst : BigSpliceStream (fun m ↦
      (softmaxAffine (triangularGaps G m) m threshold pad (.const 1)).const.serialize) := by
    refine BigSpliceStream.of_eq hconstRaw ?_
    intro m
    rw [softmaxAffine_triangular_const, triangularFold_serialize]
    simp
  refine {
    termCount := triangularTermCount hG
    coefficient := triangularCoefficient hG threshold pad
    sentence := triangularSentence hG
    termCount_poly := triangularTermCount_poly hG
    const_poly := hconst
    coefficient_poly := BigSpliceStream.of_eq hcoefficient (fun z ↦ by
      simp [triangularCoefficient])
    sentence_poly := ?_
    terms_eq := ?_
    const_rank := ?_
    coefficient_rank := ?_
    const_closed := ?_
    coefficient_closed := ?_
  }
  · exact (hG.sentence_poly.comp hcanonical).of_eq (fun z ↦ by
      simp [triangularSentence])
  · intro m
    rw [softmaxAffine_triangular_terms]
    let lenFn := triangularMemberLength hG
    let seg : ℕ → List (EF × Sentence) := fun z ↦
      ((G (triangularIndex z.unpair.1 z.unpair.2)).scale
        (triangularWeight G z.unpair.1 z.unpair.2 threshold pad)).terms
    have hlen : ∀ i, (seg (Nat.pair m i)).length = lenFn (Nat.pair m i) := by
      intro i
      simp [seg, lenFn, triangularMemberLength, AffineCombination.scale, hG.terms_eq]
    have hlength :
        ((List.range m).flatMap (fun i ↦ seg (Nat.pair m i))).length =
          triangularTermCount hG m := by
      simpa [triangularTermCount, lenFn] using
        length_flatMap_eq_segPrefix_any seg lenFn m hlen m
    symm
    change (List.range (triangularTermCount hG m)).map (fun j ↦
      (triangularCoefficient hG threshold pad (Nat.pair m j),
        triangularSentence hG (Nat.pair m j))) = _
    rw [show (List.range m).flatMap (fun i ↦
        ((G (triangularIndex m i)).scale
          (triangularWeight G m i threshold pad)).terms) =
        (List.range m).flatMap (fun i ↦ seg (Nat.pair m i)) by simp [seg]]
    apply List.ext_get
    · simpa using hlength.symm
    · intro j hjleft hjright
      have hj : j < triangularTermCount hG m := by simpa using hjleft
      let i := triangularMember hG (Nat.pair m j)
      let r := triangularOffset hG (Nat.pair m j)
      have hilt : i < m := by simpa [i] using triangularMember_lt hG hj
      have hrlt : r < hG.termCount (triangularIndex m i) := by
        simpa [i, r] using triangularOffset_lt hG hj
      have hlo : segPrefix lenFn m i ≤ j := by
        simpa [i, triangularMember] using
          (segLocate_spec lenFn m j m).1
      have hhi : j < segPrefix lenFn m (i + 1) := by
        by_contra hnot
        have hle := le_of_not_gt hnot
        have hmax := (segLocate_spec lenFn m j m).2
        have := hmax (i + 1) (by omega) hle
        have hid : segLocate lenFn m j m = i := by
          simp [i, triangularMember, lenFn]
        rw [hid] at this
        omega
      let d : EF × Sentence := (EF.const 0, hG.sentence 0)
      have hget := getD_flatMap_of_prefix_any seg lenFn d m m j i
        hlen hilt hlo hhi
      have hright :
          ((List.range m).flatMap (fun q ↦ seg (Nat.pair m q))).getD j d =
            (seg (Nat.pair m i)).getD r d := by
        simpa [r, triangularOffset, i, lenFn] using hget
      have hgetD := List.getD_eq_get
        (l := (List.range m).flatMap (fun q ↦ seg (Nat.pair m q)))
        (d := d) ⟨j, hjright⟩
      rw [← hgetD, hright]
      rw [show (seg (Nat.pair m i)).getD r d =
          (EF.mul (triangularWeight G m i threshold pad)
            (hG.coefficient (Nat.pair (triangularIndex m i) r)),
            hG.sentence (Nat.pair (triangularIndex m i) r)) by
        simp only [seg, Nat.unpair_pair, AffineCombination.scale, hG.terms_eq]
        rw [List.getD_eq_getElem]
        · rw [List.getElem_map, List.getElem_map, List.getElem_range]
        · simpa using hrlt]
      simp [triangularCoefficient, triangularSentence, i, r]
  · intro m
    rw [softmaxAffine_triangular_const]
    have hfold : ∀ l : List ℕ, (∀ i ∈ l, i < m) →
        (l.foldr (fun i acc ↦ EF.add
          (EF.mul (triangularWeight G m i threshold pad)
            (G (triangularIndex m i)).const) acc) (EF.const 0)).rank ≤ m := by
      intro l hl
      induction l with
      | nil => simp
      | cons i rest ih =>
          simp only [List.foldr_cons, EF.rank]
          apply Nat.max_le.mpr
          have hi := hl i (by simp)
          exact ⟨Nat.max_le.mpr ⟨
              triangularWeight_rank_le G m i threshold pad
                (fun k hk ↦ hconstRank m k (lt_of_le_of_lt hk hi))
                (fun k hk ↦ htermsRank m k (lt_of_le_of_lt hk hi)),
              hconstRank m i hi⟩,
            ih (fun k hk ↦ hl k (by simp [hk]))⟩
    exact hfold (List.range m) (by simp)
  · intro m j hj
    simp only [triangularCoefficient, Nat.unpair_pair, EF.rank]
    let i := triangularMember hG (Nat.pair m j)
    let r := triangularOffset hG (Nat.pair m j)
    have hi : i < m := by simpa [i] using triangularMember_lt hG hj
    have hr : r < hG.termCount (triangularIndex m i) := by
      simpa [i, r] using triangularOffset_lt hG hj
    have hcoeffMem :
        (hG.coefficient (Nat.pair (triangularIndex m i) r),
          hG.sentence (Nat.pair (triangularIndex m i) r)) ∈
            (G (triangularIndex m i)).terms := by
      rw [hG.terms_eq]
      exact List.mem_map.mpr ⟨r, by simp [hr], rfl⟩
    exact Nat.max_le.mpr ⟨
      triangularWeight_rank_le G m i threshold pad
        (fun k hk ↦ hconstRank m k (lt_of_le_of_lt hk hi))
        (fun k hk ↦ htermsRank m k (lt_of_le_of_lt hk hi)),
      htermsRank m i hi _ hcoeffMem⟩
  · intro m ρ V
    rw [softmaxAffine_triangular_const]
    induction List.range m with
    | nil => simp
    | cons i rest ih =>
        simp only [List.foldr_cons, EF.denoteWith, EF.denote_add, EF.denote_mul,
          Pi.add_apply, Pi.mul_apply]
        rw [triangularWeight_closed hG, hG.const_closed, ih]
  · intro z ρ V
    simp only [triangularCoefficient, EF.denoteWith, EF.denote_mul, Pi.mul_apply]
    rw [triangularWeight_closed hG, hG.coefficient_closed]

end AffineCombination

/-! ## Cross-index threshold meshes and concrete mesh gaps -/

namespace LUVCombinationSyntax

/-- Emit `(As (source n)).meshAffine (precision n)` from compact syntax.  This is the
cross-index form of `diagonalMeshPoly`; `source n ≤ n` is exactly the feature-rank
condition needed by the affine sequence interface. -/
noncomputable def meshFamilyPoly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (source precision : ℕ → ℕ)
    (hsource : ∃ c, PolyFueled c source)
    (hprecision : ∃ c, PolyFueled c precision)
    (hsource_le : ∀ n, source n ≤ n) :
    AffineCombination.PolySequence (fun n ↦ (As (source n)).meshAffine (precision n)) := by
  let csource := Classical.choose hsource
  have hsourcePF := Classical.choose_spec hsource
  let cprecision := Classical.choose hprecision
  have hprecisionPF := Classical.choose_spec hprecision
  let ccount := Classical.choose S.termCount_poly
  have hcount := Classical.choose_spec S.termCount_poly
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  have hthreshold := S.threshold_poly
  let cmul := Classical.choose mul_polyFueled
  have hmul := Classical.choose_spec mul_polyFueled
  let cdm := Classical.choose divmod1_polyFueled
  have hdm := Classical.choose_spec divmod1_polyFueled
  let count : ℕ → ℕ := fun n ↦ S.termCount (source n) * precision n
  let member : ℕ → ℕ := fun z ↦
    z.unpair.2 / (precision z.unpair.1 - 1 + 1)
  let offset : ℕ → ℕ := fun z ↦
    z.unpair.2 % (precision z.unpair.1 - 1 + 1)
  have hcountPF : PolyFueled
      (cmul.comp ((ccount.comp csource).pair cprecision)) count :=
    (hmul.comp ((hcount.comp hsourcePF).pair hprecisionPF)).of_eq
      (fun n ↦ by simp [count])
  let cinput := (subc.comp
    ((cprecision.comp Nat.Partrec.Code.left).pair (Nat.Partrec.Code.const 1))).pair
      Nat.Partrec.Code.right
  have hdivmod : PolyFueled (cdm.comp cinput) (fun z ↦
      Nat.pair (member z) (offset z)) := by
    have hinput : PolyFueled _ (fun z : ℕ ↦
        Nat.pair (precision z.unpair.1 - 1) z.unpair.2) :=
      ((subc_polyFueled.comp
        ((hprecisionPF.comp PolyFueled.left).pair (PolyFueled.const 1))).pair
        PolyFueled.right).of_eq (fun z ↦ by simp)
    exact (hdm.comp hinput).of_eq (fun z ↦ by
      simp [member, offset])
  have hmember : PolyFueled (Nat.Partrec.Code.left.comp (cdm.comp cinput)) member :=
    (PolyFueled.left.comp hdivmod).of_eq (fun z ↦ by simp)
  have hoffset : PolyFueled (Nat.Partrec.Code.right.comp (cdm.comp cinput)) offset :=
    (PolyFueled.right.comp hdivmod).of_eq (fun z ↦ by simp)
  have hsourceTerm : PolyFueled _ (fun z : ℕ ↦
      Nat.pair (source z.unpair.1) (member z)) :=
    (hsourcePF.comp PolyFueled.left).pair hmember
  have hcoeffSource := S.coefficient_poly.comp hsourceTerm
  have hinvPrecision : BigSpliceStream (fun z ↦
      (EF.const (1 / (precision z.unpair.1 : ℚ))).serialize) :=
    BigSpliceStream.serialize_const_comp
      ⟨cinv.comp (cprecision.comp Nat.Partrec.Code.left),
        hinv.comp (hprecisionPF.comp PolyFueled.left)⟩
  have hthresholdQuery : PolyFueled _ (fun z : ℕ ↦
      Nat.pair (Nat.pair (source z.unpair.1) (member z))
        (Nat.pair (precision z.unpair.1) (offset z))) :=
    hsourceTerm.pair ((hprecisionPF.comp PolyFueled.left).pair hoffset)
  refine {
    termCount := count
    coefficient := fun z ↦ EF.mul
      (S.coefficient (Nat.pair (source z.unpair.1) (member z)))
      (EF.const (1 / (precision z.unpair.1 : ℚ)))
    sentence := fun z ↦
      (S.luv (Nat.pair (source z.unpair.1) (member z))).gt
        ((offset z : ℚ) / (precision z.unpair.1 : ℚ))
    termCount_poly := ⟨_, hcountPF⟩
    const_poly := S.const_poly.comp hsourcePF
    coefficient_poly := BigSpliceStream.serialize_mul hcoeffSource hinvPrecision
    sentence_poly :=
      (BigSentenceCodes.ofRpnSentenceCodes (hthreshold.comp hthresholdQuery)).of_eq
        (fun z ↦ by simp)
    terms_eq := ?_
    const_rank := ?_
    coefficient_rank := ?_
    const_closed := ?_
    coefficient_closed := ?_
  }
  · intro n
    rw [LUVCombination.meshAffine, S.terms_eq]
    rw [flatMap_threshold_terms]
    simp only [List.length_map, List.length_range]
    change (List.range (count n)).map _ = _
    apply List.map_congr_left
    intro t ht
    simp only [List.mem_range] at ht
    have hp : 0 < precision n := by
      by_contra hz
      have : precision n = 0 := Nat.eq_zero_of_not_pos hz
      simp [count, this] at ht
    have hj : t / precision n < S.termCount (source n) :=
      (Nat.div_lt_iff_lt_mul hp).2 (by simpa [count] using ht)
    have hidx : t / precision n <
        ((List.range (S.termCount (source n))).map fun j ↦
          (S.coefficient (Nat.pair (source n) j),
            S.luv (Nat.pair (source n) j))).length := by simpa using hj
    rw [List.getD_eq_getElem (l :=
      (List.range (S.termCount (source n))).map fun j ↦
        (S.coefficient (Nat.pair (source n) j), S.luv (Nat.pair (source n) j)))
      (d := (EF.const 0, (⟨fun _ ↦ ⊤⟩ : LUV))) hidx]
    simp [member, offset, Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr hp.ne')]
  · intro n
    exact (S.const_rank (source n)).trans (hsource_le n)
  · intro n t ht
    simp only [EF.rank, Nat.unpair_pair]
    apply Nat.max_le.mpr
    refine ⟨?_, by simp⟩
    have hp : 0 < precision n := by
      by_contra hz
      have : precision n = 0 := Nat.eq_zero_of_not_pos hz
      simp [count, this] at ht
    have hj : t / precision n < S.termCount (source n) :=
      (Nat.div_lt_iff_lt_mul hp).2 (by simpa [count] using ht)
    simpa [member, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne')] using
      (S.coefficient_rank (source n) (t / precision n) hj).trans (hsource_le n)
  · intro n ρ V
    exact S.const_closed (source n) ρ V
  · intro z ρ V
    simp only [EF.denoteWith, EF.denote_mul, EF.denote_const, Pi.mul_apply]
    rw [S.coefficient_closed]

end LUVCombinationSyntax

namespace AffineCombination

/-- Add a uniformly generated feature to the affine constant coordinate. -/
noncomputable def PolySequence.addConstEF {As : ℕ → AffineCombination}
    (hA : PolySequence As) (e : ℕ → EF) (he : PGenerableWeighting e) :
    PolySequence (fun n ↦ LUVCombination.addConstEF (As n) (e n)) where
  termCount := hA.termCount
  coefficient := hA.coefficient
  sentence := hA.sentence
  termCount_poly := hA.termCount_poly
  const_poly := BigSpliceStream.serialize_add hA.const_poly he.polySeg
  coefficient_poly := hA.coefficient_poly
  sentence_poly := hA.sentence_poly
  terms_eq := hA.terms_eq
  const_rank := by
    intro n
    simp only [LUVCombination.addConstEF, EF.rank]
    exact Nat.max_le.mpr ⟨hA.const_rank n, he.rank_le n⟩
  coefficient_rank := hA.coefficient_rank
  const_closed := by
    intro n ρ V
    simp only [LUVCombination.addConstEF, EF.denoteWith, EF.denote_add, Pi.add_apply]
    rw [hA.const_closed n ρ V, he.closed n ρ V]
  coefficient_closed := hA.coefficient_closed

end AffineCombination

namespace LUVCombinationSyntax

private def upperGapFamily (As : ℕ → LUVCombination) (b : ℚ) (q : ℕ) :
    AffineCombination :=
  (As q.unpair.2).meshGap (q.unpair.2 + 1) (q.unpair.1 + 1) b

private def lowerGapFamily (As : ℕ → LUVCombination) (b : ℚ) (q : ℕ) :
    AffineCombination :=
  (As q.unpair.2).meshGapLower (q.unpair.2 + 1) (q.unpair.1 + 1) b

private lemma meshAffine_terms_rank_of_syntax {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) {n k m : ℕ} (hnm : n ≤ m) :
    ∀ p ∈ (As n).meshAffine k |>.terms, p.1.rank ≤ m := by
  intro p hp
  simp only [LUVCombination.meshAffine, List.mem_flatMap] at hp
  obtain ⟨src, hsrc, hp⟩ := hp
  rw [S.terms_eq] at hsrc
  simp only [List.mem_map, List.mem_range] at hsrc
  obtain ⟨j, hj, rfl⟩ := hsrc
  exact AffineCombination.scale_terms_rank_le _ _
    ((S.coefficient_rank n j hj).trans hnm)
    (by
      intro q hq
      simp only [LUV.expectAffine, List.mem_map, List.mem_range] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      simp [EF.rank]) p hp

private lemma upperGap_rank_legal {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (b : ℚ) (m i : ℕ) (hi : i < m) :
    (upperGapFamily As b (AffineCombination.triangularIndex m i)).const.rank ≤ m ∧
      ∀ p ∈ (upperGapFamily As b
        (AffineCombination.triangularIndex m i)).terms, p.1.rank ≤ m := by
  have hn : i + 1 ≤ m := by omega
  constructor
  · simp [upperGapFamily, AffineCombination.triangularIndex, LUVCombination.meshGap,
      LUVCombination.addConstEF, AffineCombination.sub, AffineCombination.add,
      AffineCombination.neg, AffineCombination.scale, LUVCombination.meshAffine,
      LUVCombination.meshErrorFeature, EF.rank]
    exact (S.const_rank (i + 1)).trans hn
  · intro p hp
    simp only [upperGapFamily, AffineCombination.triangularIndex, Nat.unpair_pair,
      LUVCombination.meshGap, LUVCombination.addConstEF, AffineCombination.sub,
      AffineCombination.add, List.mem_append] at hp
    rcases hp with hp | hp
    · exact meshAffine_terms_rank_of_syntax S hn p hp
    · exact AffineCombination.neg_terms_rank_le _
        (meshAffine_terms_rank_of_syntax S hn) p hp

private lemma lowerGap_rank_legal {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (b : ℚ) (m i : ℕ) (hi : i < m) :
    (lowerGapFamily As b (AffineCombination.triangularIndex m i)).const.rank ≤ m ∧
      ∀ p ∈ (lowerGapFamily As b
        (AffineCombination.triangularIndex m i)).terms, p.1.rank ≤ m := by
  have hn : i + 1 ≤ m := by omega
  constructor
  · simp [lowerGapFamily, AffineCombination.triangularIndex,
      LUVCombination.meshGapLower, LUVCombination.addConstEF,
      AffineCombination.sub, AffineCombination.add, AffineCombination.neg,
      AffineCombination.scale, LUVCombination.meshAffine,
      LUVCombination.meshErrorFeature, EF.rank]
    exact (S.const_rank (i + 1)).trans hn
  · intro p hp
    simp only [lowerGapFamily, AffineCombination.triangularIndex, Nat.unpair_pair,
      LUVCombination.meshGapLower, LUVCombination.addConstEF,
      AffineCombination.sub, AffineCombination.add, List.mem_append] at hp
    rcases hp with hp | hp
    · exact meshAffine_terms_rank_of_syntax S hn p hp
    · exact AffineCombination.neg_terms_rank_le _
        (meshAffine_terms_rank_of_syntax S hn) p hp

/-- Polynomial syntax for every upper cross-precision gap, stored at paired indices. -/
noncomputable def upperGapPoly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (b : ℚ) :
    AffineCombination.PolySequence (upperGapFamily As b) := by
  have hright : ∀ q : ℕ, q.unpair.2 ≤ q := Nat.unpair_right_le
  have hlow := S.meshFamilyPoly (fun q ↦ q.unpair.2) (fun q ↦ q.unpair.2 + 1)
    ⟨_, PolyFueled.right⟩ ⟨_, PolyFueled.right.succ_comp⟩ hright
  have hhigh := S.meshFamilyPoly (fun q ↦ q.unpair.2) (fun q ↦ q.unpair.1 + 1)
    ⟨_, PolyFueled.right⟩ ⟨_, PolyFueled.left.succ_comp⟩ hright
  have hbase := hlow.add hhigh.neg
  let e : ℕ → EF := fun q ↦ LUVCombination.meshErrorFeature (q.unpair.2 + 1) b
  have he : PGenerableWeighting e := {
    polySeg := BigSpliceStream.serialize_mul
      (BigSpliceStream.serialize_const (-(2 * b)))
      (BigSpliceStream.serialize_const_comp
        ⟨_, (Classical.choose_spec encode_inv_nat_polyFueled).comp
          PolyFueled.right.succ_comp⟩)
    rank_le := by intro q; simp [e, LUVCombination.meshErrorFeature, EF.rank]
    closed := by intro q ρ V; simp [e, LUVCombination.meshErrorFeature, EF.denoteWith]
  }
  exact hbase.addConstEF e he

/-- Polynomial syntax for every lower cross-precision gap, stored at paired indices. -/
noncomputable def lowerGapPoly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (b : ℚ) :
    AffineCombination.PolySequence (lowerGapFamily As b) := by
  have hright : ∀ q : ℕ, q.unpair.2 ≤ q := Nat.unpair_right_le
  have hlow := S.meshFamilyPoly (fun q ↦ q.unpair.2) (fun q ↦ q.unpair.2 + 1)
    ⟨_, PolyFueled.right⟩ ⟨_, PolyFueled.right.succ_comp⟩ hright
  have hhigh := S.meshFamilyPoly (fun q ↦ q.unpair.2) (fun q ↦ q.unpair.1 + 1)
    ⟨_, PolyFueled.right⟩ ⟨_, PolyFueled.left.succ_comp⟩ hright
  have hbase := hhigh.add hlow.neg
  let e : ℕ → EF := fun q ↦ LUVCombination.meshErrorFeature (q.unpair.2 + 1) b
  have he : PGenerableWeighting e := {
    polySeg := BigSpliceStream.serialize_mul
      (BigSpliceStream.serialize_const (-(2 * b)))
      (BigSpliceStream.serialize_const_comp
        ⟨_, (Classical.choose_spec encode_inv_nat_polyFueled).comp
          PolyFueled.right.succ_comp⟩)
    rank_le := by intro q; simp [e, LUVCombination.meshErrorFeature, EF.rank]
    closed := by intro q ρ V; simp [e, LUVCombination.meshErrorFeature, EF.denoteWith]
  }
  exact hbase.addConstEF e he

/-- Exact polynomial emitter for the upper mesh softmax consumed by `mesh_upper_eventually`. -/
noncomputable def meshSoftmaxPoly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (b ε : ℚ) :
    AffineCombination.PolySequence (LUVCombination.meshSoftmax As b ε) := by
  have h := AffineCombination.triangularSoftmaxPoly (S.upperGapPoly b)
    (ε / 2) (ε / 4)
    (fun m i hi ↦ (upperGap_rank_legal S b m i hi).1)
    (fun m i hi ↦ (upperGap_rank_legal S b m i hi).2)
  have hfun : (fun m => LUVCombination.softmaxAffine
      (AffineCombination.triangularGaps (upperGapFamily As b) m) m (ε / 2) (ε / 4)
      (EF.const 1)) = LUVCombination.meshSoftmax As b ε := by
    funext m
    simp [LUVCombination.meshSoftmax, LUVCombination.meshGaps,
      AffineCombination.triangularGaps, upperGapFamily,
      AffineCombination.triangularIndex]
  exact hfun ▸ h

/-- Exact polynomial emitter for the lower mesh softmax consumed by `mesh_lower_eventually`. -/
noncomputable def meshSoftmaxLowerPoly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (b ε : ℚ) :
    AffineCombination.PolySequence (LUVCombination.meshSoftmaxLower As b ε) := by
  have h := AffineCombination.triangularSoftmaxPoly (S.lowerGapPoly b)
    (ε / 2) (ε / 4)
    (fun m i hi ↦ (lowerGap_rank_legal S b m i hi).1)
    (fun m i hi ↦ (lowerGap_rank_legal S b m i hi).2)
  have hfun : (fun m => LUVCombination.softmaxAffine
      (AffineCombination.triangularGaps (lowerGapFamily As b) m) m (ε / 2) (ε / 4)
      (EF.const 1)) = LUVCombination.meshSoftmaxLower As b ε := by
    funext m
    simp [LUVCombination.meshSoftmaxLower, LUVCombination.meshGapsLower,
      AffineCombination.triangularGaps, lowerGapFamily,
      AffineCombination.triangularIndex]
  exact hfun ▸ h

/-- Compact LUV syntax and the sequence's `L¹` bound together discharge the operational
witness — polynomial emission of the mesh softmax, plus a uniform price bound on it — that
the mesh lemma consumes.
Paper node: `lem:mesh`, `thm:wubexp` -/
noncomputable def meshSoftmaxOperationalWitness
    {As : ℕ → LUVCombination} {P : History}
    (S : LUVCombinationSyntax As) (h : LUVCombination.BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) :
    LUVCombination.MeshSoftmaxOperationalWitness As P where
  poly := S.meshSoftmaxPoly
  bounded := by
    intro b ε
    obtain ⟨B, hB⟩ := h.bounded
    have hB0 : 0 ≤ B := (As 0).l1Norm_nonneg P |>.trans (hB 0)
    refine ⟨2 * B + 2 * |(b : ℝ)|, by positivity, fun m day ↦ ?_⟩
    simpa only [LUVCombination.meshSoftmax, EF.denote_const, Rat.cast_one, one_mul] using
      LUVCombination.abs_softmaxAffine_price_le
        (LUVCombination.meshGaps As m b) P m day (ε / 2) (ε / 4) (.const 1)
          (2 * B + 2 * |(b : ℝ)|) (by simp) (by positivity) (by
            intro A hA
            simp only [LUVCombination.meshGaps, List.mem_map, List.mem_range] at hA
            obtain ⟨i, hi, rfl⟩ := hA
            exact LUVCombination.abs_meshGap_price_le (As (i + 1)) P (by omega)
              b B (hB (i + 1)) (hP day))
  magnitude := by
    intro b ε
    obtain ⟨B, hB⟩ := h.bounded
    have hB0 : 0 ≤ B := (As 0).l1Norm_nonneg P |>.trans (hB 0)
    refine ⟨2 * B, by
      intro m
      have hgaps : ∀ A ∈ LUVCombination.meshGaps As m b,
          A.magnitude P ≤ 2 * B := by
        intro A hA
        simp only [LUVCombination.meshGaps, List.mem_map, List.mem_range] at hA
        obtain ⟨i, hi, rfl⟩ := hA
        have hshare : (As (i + 1)).shareNorm P ≤ B := by
          calc
            (As (i + 1)).shareNorm P ≤ (As (i + 1)).l1Norm P := by
              simp only [LUVCombination.l1Norm]
              exact le_add_of_nonneg_left (abs_nonneg _)
            _ ≤ B := hB (i + 1)
        exact (LUVCombination.meshGap_magnitude_le (As (i + 1)) P
          (i + 2) (m + 1) b).trans (by linarith)
      simpa only [LUVCombination.meshSoftmax, EF.denote_const, Rat.cast_one, one_mul] using
        LUVCombination.softmaxAffine_magnitude_le
          (LUVCombination.meshGaps As m b) P m (ε / 2) (ε / 4) (.const 1)
            (2 * B) (by simp) (by positivity) hgaps
    ⟩
  lower_poly := S.meshSoftmaxLowerPoly
  lower_bounded := by
    intro b ε
    obtain ⟨B, hB⟩ := h.bounded
    have hB0 : 0 ≤ B := (As 0).l1Norm_nonneg P |>.trans (hB 0)
    refine ⟨2 * B + 2 * |(b : ℝ)|, by positivity, fun m day ↦ ?_⟩
    simpa only [LUVCombination.meshSoftmaxLower, EF.denote_const, Rat.cast_one, one_mul] using
      LUVCombination.abs_softmaxAffine_price_le
        (LUVCombination.meshGapsLower As m b) P m day (ε / 2) (ε / 4) (.const 1)
          (2 * B + 2 * |(b : ℝ)|) (by simp) (by positivity) (by
            intro A hA
            simp only [LUVCombination.meshGapsLower, List.mem_map, List.mem_range] at hA
            obtain ⟨i, hi, rfl⟩ := hA
            exact LUVCombination.abs_meshGapLower_price_le (As (i + 1)) P (by omega)
              b B (hB (i + 1)) (hP day))
  lower_magnitude := by
    intro b ε
    obtain ⟨B, hB⟩ := h.bounded
    have hB0 : 0 ≤ B := (As 0).l1Norm_nonneg P |>.trans (hB 0)
    refine ⟨2 * B, by
      intro m
      have hgaps : ∀ A ∈ LUVCombination.meshGapsLower As m b,
          A.magnitude P ≤ 2 * B := by
        intro A hA
        simp only [LUVCombination.meshGapsLower, List.mem_map, List.mem_range] at hA
        obtain ⟨i, hi, rfl⟩ := hA
        have hshare : (As (i + 1)).shareNorm P ≤ B := by
          calc
            (As (i + 1)).shareNorm P ≤ (As (i + 1)).l1Norm P := by
              simp only [LUVCombination.l1Norm]
              exact le_add_of_nonneg_left (abs_nonneg _)
            _ ≤ B := hB (i + 1)
        exact (LUVCombination.meshGapLower_magnitude_le (As (i + 1)) P
          (i + 2) (m + 1) b).trans (by linarith)
      simpa only [LUVCombination.meshSoftmaxLower, EF.denote_const, Rat.cast_one,
          one_mul] using
        LUVCombination.softmaxAffine_magnitude_le
          (LUVCombination.meshGapsLower As m b) P m (ε / 2) (ε / 4) (.const 1)
            (2 * B) (by simp) (by positivity) hgaps
    ⟩

end LUVCombinationSyntax

/-! ## Expectation endpoints with the mesh-softmax witness discharged

`Properties/ExpectationProperties.lean` states the four mesh-driven expectation theorems
against `MeshSoftmaxOperationalWitness`, the operational package certifying that the
compiled threshold-mesh softmax is polynomially emitted and uniformly price-bounded.  That
package is *derivable*, but only here: `meshSoftmaxOperationalWitness` needs the compact
syntax `LUVCombinationSyntax`, which lives downstream of the properties layer.  The
`_ofSyntax` endpoints below therefore restate the four theorems with the operational
witness replaced by the paper's own efficient-computability premise on the sequence —
the syntax naming its constants, coefficients, LUVs, and threshold sentences — the `def:blcp`
bound already present in `BoundedSequence`, and the market's own `[0,1]` price range. -/

namespace LUVCombination.BoundedSequence

open Filter Topology

/-- Appendix `lem:mesh` with the mesh-softmax operational witness discharged from the
compact LUV syntax.  Proof kind `C`; every hypothesis is type `(a)`.
Paper node: `lem:mesh` -/
theorem mesh_independence_ofSyntax
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (S : LUVCombinationSyntax As)
    (hvalued : LUVCombination.WorldValued As DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (LUVCombination.meshTailError As P) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := h.bounded
  obtain ⟨b, hbB⟩ := exists_rat_gt (max B 0)
  have hb : (0 : ℝ) ≤ (b : ℝ) := (le_max_right B 0).trans hbB.le
  have hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ) := fun n => by
    have h1 : (As n).shareNorm P ≤ (As n).l1Norm P :=
      le_add_of_nonneg_left (abs_nonneg _)
    exact h1.trans ((hB n).trans ((le_max_left B 0).trans hbB.le))
  exact h.mesh_independence (S.meshSoftmaxOperationalWitness h
      (fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ))
    hvalued b hb hshare hworld

/-- `thm:exppolymax` with the mesh-softmax operational witness discharged from the compact
LUV syntax.  Proof kind `C`; every hypothesis is type `(a)`.
Paper node: `thm:exppolymax` -/
theorem exppolymax_ofSyntax
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (S : LUVCombinationSyntax As)
    (hvalued : LUVCombination.WorldValued As DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (fun n => (As n).expect P n) atTop =
        liminf (futureHigh As P) atTop ∧
      limsup (fun n => (As n).expect P n) atTop =
        limsup (futureLow As P) atTop := by
  obtain ⟨B, hB⟩ := h.bounded
  obtain ⟨b, hbB⟩ := exists_rat_gt (max B 0)
  have hb : (0 : ℝ) ≤ (b : ℝ) := (le_max_right B 0).trans hbB.le
  have hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ) := fun n => by
    have h1 : (As n).shareNorm P ≤ (As n).l1Norm P :=
      le_add_of_nonneg_left (abs_nonneg _)
    exact h1.trans ((hB n).trans ((le_max_left B 0).trans hbB.le))
  exact h.exppolymax (S.meshSoftmaxOperationalWitness h
      (fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ))
    hvalued b hb hshare hworld

/-- `thm:expcoh` with the mesh-softmax operational witness discharged from the compact LUV
syntax.  Proof kind `C`; every hypothesis is type `(a)`.
Paper node: `thm:expcoh` -/
theorem expcoh_ofSyntax
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (S : LUVCombinationSyntax As)
    (hvalued : LUVCombination.WorldValued As DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (liminf (completedLow As P DP) atTop ≤
        liminf (fun n => (As n).expectInf P) atTop ∧
      liminf (fun n => (As n).expectInf P) atTop ≤
        liminf (fun n => (As n).expect P n) atTop) ∧
      (limsup (fun n => (As n).expect P n) atTop ≤
          limsup (fun n => (As n).expectInf P) atTop ∧
        limsup (fun n => (As n).expectInf P) atTop ≤
          limsup (completedHigh As P DP) atTop) := by
  obtain ⟨B, hB⟩ := h.bounded
  obtain ⟨b, hbB⟩ := exists_rat_gt (max B 0)
  have hb : (0 : ℝ) ≤ (b : ℝ) := (le_max_right B 0).trans hbB.le
  have hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ) := fun n => by
    have h1 : (As n).shareNorm P ≤ (As n).l1Norm P :=
      le_add_of_nonneg_left (abs_nonneg _)
    exact h1.trans ((hB n).trans ((le_max_left B 0).trans hbB.le))
  exact h.expcoh (S.meshSoftmaxOperationalWitness h
      (fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ))
    hvalued S.threshold_code b hb hshare hworld

/-- `thm:perexpkno` with the mesh-softmax operational witness discharged from the compact
LUV syntax.  Proof kind `C`; every hypothesis is type `(a)`.
Paper node: `thm:perexpkno` -/
theorem perexpkno_ofSyntax
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (S : LUVCombinationSyntax As)
    (hvalued : LUVCombination.WorldValued As DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (futureLow As P) atTop =
        liminf (fun n => (As n).expectInf P) atTop ∧
      limsup (futureHigh As P) atTop =
        limsup (fun n => (As n).expectInf P) atTop := by
  obtain ⟨B, hB⟩ := h.bounded
  obtain ⟨b, hbB⟩ := exists_rat_gt (max B 0)
  have hb : (0 : ℝ) ≤ (b : ℝ) := (le_max_right B 0).trans hbB.le
  have hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ) := fun n => by
    have h1 : (As n).shareNorm P ≤ (As n).l1Norm P :=
      le_add_of_nonneg_left (abs_nonneg _)
    exact h1.trans ((hB n).trans ((le_max_left B 0).trans hbB.le))
  exact h.perexpkno (S.meshSoftmaxOperationalWitness h
      (fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ))
    hvalued S.threshold_code b hb hshare hworld

end LUVCombination.BoundedSequence

#print axioms LUVCombinationSyntax.diagonalMeshPoly
#print axioms LUVCombinationSyntax.polySequence
#print axioms LUVCombinationSyntax.threshold_code
#print axioms LUVCombinationSyntax.exactTheoryPresentation
#print axioms LUVCombinationSyntax.worldValued
#print axioms LUVCombinationSyntax.meshSoftmaxPoly
#print axioms LUVCombinationSyntax.meshSoftmaxLowerPoly
#print axioms LUVCombinationSyntax.meshSoftmaxOperationalWitness
#print axioms LUVCombination.BoundedSequence.mesh_independence_ofSyntax
#print axioms LUVCombination.BoundedSequence.exppolymax_ofSyntax
#print axioms LUVCombination.BoundedSequence.expcoh_ofSyntax
#print axioms LUVCombination.BoundedSequence.perexpkno_ofSyntax

end LogicalInduction
