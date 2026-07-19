import LogicalInduction.Construction.QuotationAffine
import LogicalInduction.Properties.ExpectationProperties

/-!
# Concrete syntax for polynomial LUV-combination sequences

This file constructs the non-statistical part of `M7-LUV-SYNTAX`.  A compact sequence
presentation names the constants, coefficients, LUVs, and threshold sentences occurring
in a sequence of LUV combinations.  The diagonal threshold mesh is then emitted directly:
term `j * n + i` is coefficient `a_j / n` on the literal sentence `X_j > i/n`.

The presentation contains no prices, convergence, exploitation, or logical-inductor
conclusion.  Its semantic companion states only the represented threshold facts in finite
and completed stages; the public `WorldValued`, `ConvergencePresentation`, and
`ExactTheoryPresentation` packages are derived below.
-/

namespace LogicalInduction

/-! ## Compact combination syntax -/

/-- Operational syntax for a sequence of LUV combinations.  The LUV and coefficient at
`z = ⟨n,j⟩` are the `j`th term of member `n`. -/
structure LUVCombinationSyntax (As : ℕ → LUVCombination) where
  termCount : ℕ → ℕ
  coefficient : ℕ → EF
  luv : ℕ → LUV
  termCount_poly : ∃ c, PolyFueled c termCount
  const_poly : PolySegStream (fun n ↦ (As n).const.serialize)
  coefficient_poly : PolySegStream (fun z ↦ (coefficient z).serialize)
  threshold_poly : LUV.PolyThresholdCodeSeq luv
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
  S.termCount n * n

/-- Source term containing a flattened diagonal-mesh term. -/
def meshMember {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (z : ℕ) : ℕ :=
  z.unpair.2 / (z.unpair.1 - 1 + 1)

/-- Threshold numerator within a flattened diagonal-mesh term. -/
def meshOffset {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (z : ℕ) : ℕ :=
  z.unpair.2 % (z.unpair.1 - 1 + 1)

/-- Literal coefficient `a_j / n` of a flattened threshold share. -/
def meshCoefficient {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (z : ℕ) : EF :=
  .mul (S.coefficient (Nat.pair z.unpair.1 (S.meshMember z)))
    (.const (1 / (z.unpair.1 : ℚ)))

/-- Literal sentence `X_j > i/n` of a flattened threshold share. -/
def meshSentence {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (z : ℕ) : Sentence :=
  (S.luv (Nat.pair z.unpair.1 (S.meshMember z))).gt
    ((S.meshOffset z : ℚ) / (z.unpair.1 : ℚ))

theorem meshTermCount_poly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) :
    ∃ c, PolyFueled c S.meshTermCount := by
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  obtain ⟨ccount, hcount⟩ := S.termCount_poly
  exact ⟨cmul.comp (ccount.pair Nat.Partrec.Code.id),
    (hmul.comp (hcount.pair PolyFueled.id)).of_eq (fun n ↦ by
      simp [meshTermCount])⟩

set_option maxHeartbeats 800000 in
private theorem meshDivMod_poly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) :
    ∃ c, PolyFueled c (fun z ↦ Nat.pair (S.meshMember z) (S.meshOffset z)) := by
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  have hinput : PolyFueled _ (fun z : ℕ ↦
      Nat.pair (z.unpair.1 - 1) z.unpair.2) :=
    ((subc_polyFueled.comp
      (PolyFueled.left.pair (PolyFueled.const 1))).pair
      PolyFueled.right).of_eq (fun z ↦ by simp)
  refine ⟨cdm.comp _, (hdm.comp hinput).of_eq (fun z ↦ ?_)⟩
  simp [meshMember, meshOffset]

theorem meshMember_poly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) :
    ∃ c, PolyFueled c S.meshMember := by
  obtain ⟨c, h⟩ := S.meshDivMod_poly
  exact ⟨Nat.Partrec.Code.left.comp c,
    (PolyFueled.left.comp h).of_eq (fun z ↦ by simp)⟩

theorem meshOffset_poly {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) :
    ∃ c, PolyFueled c S.meshOffset := by
  obtain ⟨c, h⟩ := S.meshDivMod_poly
  exact ⟨Nat.Partrec.Code.right.comp c,
    (PolyFueled.right.comp h).of_eq (fun z ↦ by simp)⟩

private theorem getD_flatMap_const_width_any {α : Type*} (f : ℕ → List α)
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

private theorem flatMap_threshold_terms (l : List (EF × LUV)) (n : ℕ) :
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
    AffineCombination.PolySequence (fun n ↦ (As n).meshAffine n) := by
  let cmember := Classical.choose S.meshMember_poly
  have hmember := Classical.choose_spec S.meshMember_poly
  let coffset := Classical.choose S.meshOffset_poly
  have hoffset := Classical.choose_spec S.meshOffset_poly
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  let cthreshold := Classical.choose S.threshold_poly
  have hthreshold := Classical.choose_spec S.threshold_poly
  have hsource : PolyFueled _ (fun z ↦
      Nat.pair z.unpair.1 (S.meshMember z)) :=
    PolyFueled.left.pair hmember
  have hcoeffSource := S.coefficient_poly.comp hsource
  have hinvSource := PolySegStream.ofTokenStream
    (PolyTokenStream.serialize_const_comp
      ⟨cinv.comp Nat.Partrec.Code.left, hinv.comp PolyFueled.left⟩)
  have hquery : PolyFueled _ (fun z : ℕ ↦
      Nat.pair (Nat.pair z.unpair.1 (S.meshMember z))
        (Nat.pair z.unpair.1 (S.meshOffset z))) :=
    hsource.pair (PolyFueled.left.pair hoffset)
  refine {
    termCount := S.meshTermCount
    coefficient := S.meshCoefficient
    sentence := S.meshSentence
    termCount_poly := S.meshTermCount_poly
    const_poly := S.const_poly
    coefficient_poly := PolySegStream.of_eq
      (PolySegStream.serialize_mul hcoeffSource hinvSource) (fun z ↦ by
        simp [meshCoefficient])
    sentence_poly := ⟨cthreshold.comp _,
      (hthreshold.comp hquery).of_eq (fun z ↦ by
        simp [meshSentence])⟩
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
    have hn : 0 < n := by
      by_contra hzero
      simp only [Nat.not_lt, Nat.le_zero] at hzero
      subst n
      simp at ht
    have hj : t / n < S.termCount n := (Nat.div_lt_iff_lt_mul hn).2 ht
    have hidx : t / n < ((List.range (S.termCount n)).map fun j ↦
        (S.coefficient (Nat.pair n j), S.luv (Nat.pair n j))).length := by
      simpa using hj
    rw [List.getD_eq_getElem (l := (List.range (S.termCount n)).map fun j ↦
      (S.coefficient (Nat.pair n j), S.luv (Nat.pair n j)))
      (d := (EF.const 0, (⟨fun _ ↦ ⊤⟩ : LUV))) hidx]
    simp [meshCoefficient, meshSentence, meshMember, meshOffset,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')]
  · intro n t ht
    simp only [meshCoefficient, Nat.unpair_pair, EF.rank]
    apply Nat.max_le.mpr
    refine ⟨?_, by simp⟩
    have hn : 0 < n := by
      by_contra hzero
      have : n = 0 := Nat.eq_zero_of_not_pos hzero
      subst n
      simp [meshTermCount] at ht
    have hj : t / n < S.termCount n :=
      (Nat.div_lt_iff_lt_mul hn).2 (by simpa [meshTermCount] using ht)
    simpa [meshMember, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')]
      using S.coefficient_rank n (t / n) hj
  · intro z ρ V
    simp only [meshCoefficient, EF.denoteWith, EF.denote_mul, EF.denote_const,
      Pi.mul_apply]
    rw [S.coefficient_closed]

/-- Public polynomial-sequence boundary discharged from compact component syntax. -/
noncomputable def polySequence {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) : LUVCombination.PolySequence As where
  mesh_poly := S.diagonalMeshPoly

/-! ## Exact represented semantics -/

/-- Stagewise and completed-theory truth laws for the threshold families named by a
compact syntax presentation.  These are representation facts only. -/
structure TheorySemantics {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (DP : DeductiveProcess) where
  value : ℕ → LUV → ℝ
  value_mem : ∀ n j, j < S.termCount n →
    0 ≤ value n (S.luv (Nat.pair n j)) ∧
      value n (S.luv (Nat.pair n j)) ≤ 1
  stage_values : ∀ n j, j < S.termCount n → ∀ m (v : PCWorld),
    v.ConsistentWith (DP.D m) →
      v.ValuesAt (S.luv (Nat.pair n j))
        (value n (S.luv (Nat.pair n j)))
  completed_threshold_iff : ∀ n j, j < S.termCount n →
    ∀ (v : PCWorld), v.ConsistentWithTheory DP → ∀ r : ℚ,
      v.Holds ((S.luv (Nat.pair n j)).gt r) ↔
        (r : ℝ) < value n (S.luv (Nat.pair n j))

theorem threshold_code {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) (n : ℕ) (p : EF × LUV)
    (hp : p ∈ (As n).terms) : p.2.PolyThresholdCodes := by
  rw [S.terms_eq] at hp
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  obtain ⟨c, hc⟩ := S.threshold_poly
  have hquery : PolyFueled _ (fun m : ℕ ↦
      Nat.pair (Nat.pair n j) m) := (PolyFueled.const (Nat.pair n j)).pair PolyFueled.id
  exact ⟨c.comp _, (hc.comp hquery).of_eq (fun m ↦ by simp)⟩

/-- Compact syntax plus stagewise representation discharges the convergence presentation. -/
def convergencePresentation {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) {DP : DeductiveProcess}
    (H : S.TheorySemantics DP) : LUVCombination.ConvergencePresentation As DP where
  threshold_code := S.threshold_code
  daily_value := by
    intro n p hp m v hv
    rw [S.terms_eq] at hp
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    exact ⟨H.value n (S.luv (Nat.pair n j)), H.stage_values n j hj m v hv⟩

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

#print axioms LUVCombinationSyntax.diagonalMeshPoly
#print axioms LUVCombinationSyntax.polySequence
#print axioms LUVCombinationSyntax.threshold_code
#print axioms LUVCombinationSyntax.convergencePresentation
#print axioms LUVCombinationSyntax.exactTheoryPresentation
#print axioms LUVCombinationSyntax.worldValued

end LogicalInduction
