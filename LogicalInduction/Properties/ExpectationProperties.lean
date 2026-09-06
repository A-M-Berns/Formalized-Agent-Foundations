import LogicalInduction.Properties.ExpectationAffine
import LogicalInduction.Properties.ExpectationConvergence
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.Pseudorandomness
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Expectations of LUV combinations (paper §4.8)

Renders §4.8 (`sec:expectations`): LUV combinations (`def:luv`), bounded
LUV-combination sequences (`def:blcp`), and the expectation theorems that follow from
the affine tail.

This is the last of the three §4.8 modules and the only one about *combinations*.  It imports
`Properties/ExpectationAffine.lean` (the affine presentation of a single LUV's expectation,
carrying `thm:ei`, `thm:loe` and `thm:expprovind`) and
`Properties/ExpectationConvergence.lean` (`thm:ec` and `lem:conluvapprox`); the cut between
the three is stated in the first of them.

`LUVCombination` is a constant `EF` together with `EF`-weighted `[0,1]`-LUV terms.  Its
market evaluation is `expectAt` / `expect` (`def:e`: Lean day `n` is paper day `n + 1`,
so the diagonal grid is `n + 1`), `value` evaluates it under an abstract LUV valuation,
and `shareNorm` / `l1Norm` are `def:blcp`'s `‖·‖₁` — the latter including the trailing
constant, the former omitting it exactly as affine trader magnitude does.

`meshAffine A k` expands each term into its `k` threshold shares, so the affine theorems
price the paper's actual traded sentences and no synthetic LUV is introduced.
`meshAffine_price`, `meshAffine_value`, `meshAffine_value_near` (error `shareNorm / k`)
and `meshAffine_magnitude_eq_shareNorm` are the bridge.

The representation boundaries are `WorldValued` (each completed-theory world values the
component LUVs somehow — the `def:luv` fact at `cworlds(Θ)`), `DeterminedViaTheory`
(`def:affthmval`, on the combination only), `ExactTheoryPresentation` (strictly stronger
than either, produced by the arithmetic layer and consumed by no statement) and
`ConvergencePresentation` (threshold codes plus per-LUV world values, the `thm:ec` input).

`lem:mesh` is proved by an explicit first-active softmax portfolio over the
cross-precision gaps (`softmaxAffine`, `meshGaps`, `meshSoftmax`) fed to affine
provability induction; `MeshSoftmaxOperationalWitness` is the only operational boundary,
and it is discharged by `LUVCombinationSyntax.meshSoftmaxOperationalWitness`.
`lem:limexpapprox` (`mesh_limitingValue_near_expectInf`, `limexpapprox`) identifies the
limiting-belief value of the diagonal mesh with the true limiting expectation
`expectInf`.

The mesh is only *approximately* determined — `def:affthmval` fixes the combination, not
its components — so the statistical lane goes through `ApproxDeterminedViaTheory` with
the vanishing `meshErrorBound` (`lem:conluvapprox`); there is deliberately no exact
mesh-determination lemma.

Main results: `mesh_independence` (`lem:mesh`), `exppolymax`, `perexpkno`, `expcoh`,
`wubexp`, `recurringunbiasednessexp_of_historicalVerifiers` and the three
`prandexp_*_of_historicalVerifiers` forms.  They are consumed by
`Construction/LUV/Syntax.lean` (the `_ofSyntax` forms),
`Construction/Statistics/HistoricalMaturity.lean` and
`Construction/LUV/Endpoints.lean` (the `_arith` forms,
`dd:luv-arith`), and are axiom-checked in `AxiomAudit.lean`.

The limit vocabulary `≈ₙ` / `≳ₙ` / `≲ₙ` is `Framework/Asymptotics`'s (`dd:asymp`), and
coefficients are reified features rather than Lean functions (`dd:dsl`).
-/

namespace LogicalInduction

open Filter Topology

/-! ## LUV combinations -/

namespace LUV

/-- Cross-day version of `expectAffine_price`: precision is `k`, while the threshold
bundle is priced on market day `m`. -/
lemma expectAffine_priceAt (X : LUV) (P : History) (k m : ℕ) :
    (X.expectAffine k).price P m = X.expectApprox (P m) k := by
  rw [expectAffine, AffineCombination.price, AffineCombination.value,
    LUV.expectApprox]
  simp only [EF.denote, EF.denoteWith, List.map_map, Function.comp_def]
  push_cast
  rw [zero_add, List.sum_map_mul_left, one_div]
  congr 1

end LUV

/-- An affine combination of `[0,1]`-LUVs with expressible-feature coefficients.  This is
the direct propositional rendering of the paper's LUV combinations.
Paper node: `def:luv` -/
structure LUVCombination where
  const : EF
  terms : List (EF × LUV)

namespace LUVCombination

/-- Evaluate a LUV combination using precision `k` and prices from market day `m`. -/
noncomputable def expectAt (A : LUVCombination) (P : History) (k m : ℕ) : ℝ :=
  A.const.denote P +
    (A.terms.map (fun p => p.1.denote P * p.2.expectApprox (P m) k)).sum

/-- The paper's diagonal expectation of a LUV combination: day `n` prices, at the grid
`n + 1` the day-index convention attaches to Lean day `n` (`def:e`). -/
noncomputable def expect (A : LUVCombination) (P : History) (n : ℕ) : ℝ :=
  A.expectAt P (n + 1) n

/-- Evaluate the combination under an arbitrary LUV valuation. -/
noncomputable def value (A : LUVCombination) (P : History) (ν : LUV → ℝ) : ℝ :=
  A.const.denote P + (A.terms.map (fun p => p.1.denote P * ν p.2)).sum

/-- A possible world assigns the advertised value to every LUV occurring in the
combination.  This is the collected-LUV analogue of `PCWorld.ValuesAt`. -/
def ValuesAt (v : PCWorld) (A : LUVCombination) (ν : LUV → ℝ) : Prop :=
  ∀ p ∈ A.terms, v.ValuesAt p.2 (ν p.2)

/-- Representation-of-computations premise: each completed-theory world coherently
values every LUV appearing in every sequence member. -/
def WorldValued (As : ℕ → LUVCombination) (DP : DeductiveProcess) : Prop :=
  ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    ∃ ν : LUV → ℝ, (As n).ValuesAt v ν

/-- Strong, first-order-style representation boundary: every completed world agrees on
the strict-threshold truth of each LUV in a sequence member, relative to one canonical
value assignment for that member.  Unlike `WorldValued`, this records that the represented
computations are individually determined.

That strength is *not* a premise of any paper node here — it is strictly more than
`def:affthmval`, which determines only the combination.  It is the shape in which an
arithmetic presentation *produces* `WorldValued` (`exactTheoryPresentation_ofArithmetic`
then `toWorldValued`), where per-LUV determinedness comes free from `Θ` deciding each
threshold; no statement consumes it as a hypothesis.
Paper node: `def:luv` -/
structure ExactTheoryPresentation (As : ℕ → LUVCombination)
    (DP : DeductiveProcess) where
  value : ℕ → LUV → ℝ
  value_mem : ∀ n p, p ∈ (As n).terms → 0 ≤ value n p.2 ∧ value n p.2 ≤ 1
  threshold_iff : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    ∀ p, p ∈ (As n).terms → ∀ r : ℚ,
      v.Holds (p.2.gt r) ↔ (r : ℝ) < value n p.2

lemma ExactTheoryPresentation.valuesAt
    {As : ℕ → LUVCombination} {DP : DeductiveProcess}
    (h : ExactTheoryPresentation As DP) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory DP) : (As n).ValuesAt v (h.value n) := by
  intro p hp
  refine ⟨(h.value_mem n p hp).1, (h.value_mem n p hp).2, ?_⟩
  intro r
  constructor
  · intro hr
    exact (h.threshold_iff n v hv p hp r).2 hr
  · intro hr hholds
    have hlt := (h.threshold_iff n v hv p hp r).1 hholds
    linarith

lemma ExactTheoryPresentation.toWorldValued
    {As : ℕ → LUVCombination} {DP : DeductiveProcess}
    (h : ExactTheoryPresentation As DP) : WorldValued As DP := by
  intro n v hv
  exact ⟨h.value n, h.valuesAt n v hv⟩

/-- A canonical completed world, used only to name the common mesh truth stream. -/
noncomputable def theoryWorld (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) : PCWorld :=
  Classical.choose (exists_consistentWithTheory DP hworld)

lemma theoryWorld_consistent (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (theoryWorld DP hworld).ConsistentWithTheory DP :=
  Classical.choose_spec (exists_consistentWithTheory DP hworld)

/-- Share-coefficient norm, omitting the trailing constant exactly as affine trader
magnitude does. -/
noncomputable def shareNorm (A : LUVCombination) (P : History) : ℝ :=
  (A.terms.map (fun p => |p.1.denote P|)).sum

/-- The paper's LUV-combination `L¹` norm, including the trailing constant. -/
noncomputable def l1Norm (A : LUVCombination) (P : History) : ℝ :=
  |A.const.denote P| + A.shareNorm P

/-! ## The threshold mesh -/

/-- Expand every LUV term into its precision-`k` threshold bundle. -/
def meshAffine (A : LUVCombination) (k : ℕ) : AffineCombination where
  const := A.const
  terms := A.terms.flatMap (fun p =>
    ((p.2.expectAffine k).scale p.1).terms)

/-- Positive rational normalization used to feed an arbitrary bounded LUV mesh into
the unit-magnitude statistical affine hubs. -/
def meshNormScale (b : ℚ) : ℚ := 1 / (|b| + 1)

lemma meshNormScale_cast (b : ℚ) :
    ((meshNormScale b : ℚ) : ℝ) = 1 / (|(b : ℝ)| + 1) := by
  simp [meshNormScale]

lemma meshNormScale_pos (b : ℚ) : 0 < ((meshNormScale b : ℚ) : ℝ) := by
  rw [meshNormScale_cast]
  positivity

lemma meshNormScale_mul_le_one (b : ℚ) :
    ((meshNormScale b : ℚ) : ℝ) * (b : ℝ) ≤ 1 := by
  rw [meshNormScale_cast]
  have hden : 0 < |(b : ℝ)| + 1 := by positivity
  calc
    1 / (|(b : ℝ)| + 1) * (b : ℝ) ≤
        1 / (|(b : ℝ)| + 1) * |(b : ℝ)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ = |(b : ℝ)| / (|(b : ℝ)| + 1) := by ring
    _ ≤ 1 := (div_le_one hden).2 (by linarith [abs_nonneg (b : ℝ)])

/-- The normalized diagonal threshold mesh. -/
def normalizedMesh (As : ℕ → LUVCombination) (b : ℚ) (n : ℕ) :
    AffineCombination :=
  ((As n).meshAffine (n + 1)).scale (.const (meshNormScale b))

private lemma meshBlock_price
    (α : EF) (X : LUV) (P : History) (k m : ℕ) :
    ((((X.expectAffine k).scale α).terms.map
      (fun p => p.1.denote P * P m p.2)).sum) =
      α.denote P * X.expectApprox (P m) k := by
  have h := AffineCombination.scale_price α (X.expectAffine k) P m
  rw [LUV.expectAffine_priceAt] at h
  rw [AffineCombination.price, AffineCombination.value] at h
  simpa [AffineCombination.scale, LUV.expectAffine] using h

private lemma meshBlock_value
    (α : EF) (X : LUV) (P : History) (w : Valuation) (k : ℕ) :
    ((((X.expectAffine k).scale α).terms.map
      (fun p => p.1.denote P * w p.2)).sum) =
      α.denote P * X.expectApprox w k := by
  have h := AffineCombination.scale_value α (X.expectAffine k) P w
  rw [LUV.expectAffine_value] at h
  rw [AffineCombination.value] at h
  simpa [AffineCombination.scale, LUV.expectAffine] using h

/-- The lifted affine price is exactly the cross-day approximate expectation. -/
lemma meshAffine_price (A : LUVCombination) (P : History) (k m : ℕ) :
    (A.meshAffine k).price P m = A.expectAt P k m := by
  rw [AffineCombination.price, AffineCombination.value]
  simp only [meshAffine, expectAt]
  congr 1
  induction A.terms with
  | nil => simp
  | cons p rest ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, meshBlock_price, ih]

@[simp] lemma meshAffine_price_diagonal
    (A : LUVCombination) (P : History) (n : ℕ) :
    (A.meshAffine (n + 1)).price P n = A.expect P n := by
  rw [meshAffine_price]
  rfl

/-- In a world, the lifted affine value is the combination evaluated at the precision-`k`
threshold-bundle valuations. -/
lemma meshAffine_value (A : LUVCombination) (P : History)
    (w : Valuation) (k : ℕ) :
    (A.meshAffine k).value P w =
      A.value P (fun X => X.expectApprox w k) := by
  rw [AffineCombination.value]
  simp only [meshAffine, value]
  congr 1
  induction A.terms with
  | nil => simp
  | cons p rest ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, meshBlock_value, ih]

/-- The common completed-theory value of the diagonal threshold mesh. -/
noncomputable def meshTheoryTruth (As : ℕ → LUVCombination) (P : History)
    (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) : ℝ :=
  ((As n).meshAffine (n + 1)).value P (theoryWorld DP hworld).payout

private lemma meshValue_near_list
    (l : List (EF × LUV)) (P : History) (v : PCWorld) (ν : LUV → ℝ)
    {k : ℕ} (hk : 0 < k)
    (hvals : ∀ p ∈ l, v.ValuesAt p.2 (ν p.2)) :
    |(l.map (fun p => p.1.denote P * p.2.expectApprox v.payout k)).sum -
        (l.map (fun p => p.1.denote P * ν p.2)).sum| ≤
      (l.map (fun p => |p.1.denote P|)).sum * (1 / (k : ℝ)) := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      have hp := (hvals p (by simp)).expectApprox_near hk
      have hrest : ∀ q ∈ rest, v.ValuesAt q.2 (ν q.2) := by
        intro q hq
        exact hvals q (by simp [hq])
      have ht := ih hrest
      simp only [List.map_cons, List.sum_cons]
      calc
        |p.1.denote P * p.2.expectApprox v.payout k +
              (rest.map (fun q => q.1.denote P * q.2.expectApprox v.payout k)).sum -
            (p.1.denote P * ν p.2 +
              (rest.map (fun q => q.1.denote P * ν q.2)).sum)| =
            |p.1.denote P * (p.2.expectApprox v.payout k - ν p.2) +
              ((rest.map (fun q => q.1.denote P * q.2.expectApprox v.payout k)).sum -
                (rest.map (fun q => q.1.denote P * ν q.2)).sum)| := by ring_nf
        _ ≤ |p.1.denote P * (p.2.expectApprox v.payout k - ν p.2)| +
              |(rest.map (fun q => q.1.denote P * q.2.expectApprox v.payout k)).sum -
                (rest.map (fun q => q.1.denote P * ν q.2)).sum| := abs_add_le _ _
        _ = |p.1.denote P| * |p.2.expectApprox v.payout k - ν p.2| +
              |(rest.map (fun q => q.1.denote P * q.2.expectApprox v.payout k)).sum -
                (rest.map (fun q => q.1.denote P * ν q.2)).sum| := by rw [abs_mul]
        _ ≤ |p.1.denote P| * (1 / (k : ℝ)) +
              (rest.map (fun q => |q.1.denote P|)).sum * (1 / (k : ℝ)) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hp (abs_nonneg _)) ht
        _ = (|p.1.denote P| +
              (rest.map (fun q => |q.1.denote P|)).sum) * (1 / (k : ℝ)) := by ring

/-- Quantitative bridge from completed-world LUV values to the affine threshold mesh.
The approximation error is the share norm divided by the mesh precision. -/
lemma meshAffine_value_near (A : LUVCombination) (P : History)
    (v : PCWorld) (ν : LUV → ℝ) {k : ℕ} (hk : 0 < k)
    (hvals : A.ValuesAt v ν) :
    |(A.meshAffine k).value P v.payout - A.value P ν| ≤
      A.shareNorm P * (1 / (k : ℝ)) := by
  rw [meshAffine_value]
  simpa only [value, shareNorm, add_sub_add_left_eq_sub] using
    meshValue_near_list A.terms P v ν hk hvals

lemma shareNorm_nonneg (A : LUVCombination) (P : History) :
    0 ≤ A.shareNorm P :=
  List.sum_nonneg (fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨p, _, rfl⟩ := hx
    exact abs_nonneg _)

lemma l1Norm_nonneg (A : LUVCombination) (P : History) :
    0 ≤ A.l1Norm P :=
  add_nonneg (abs_nonneg _) (A.shareNorm_nonneg P)

/-! ## Cross-precision gaps -/

/-- The closed feature denoting `-(2b/n)`: `lem:mesh`'s completed-world error allowance
at precision `n` for a sequence of share norm at most `b`. -/
def meshErrorFeature (n : ℕ) (b : ℚ) : EF :=
  EF.mul (EF.const (-(2 * b))) (EF.const (1 / (n : ℚ)))

@[simp] lemma meshErrorFeature_denote (n : ℕ) (b : ℚ) (P : History) :
    (meshErrorFeature n b).denote P = (-(2 * b / n) : ℚ) := by
  simp [meshErrorFeature]
  ring

/-- The oriented cross-precision gap of `lem:mesh`: the precision-`i` threshold mesh
minus the precision-`j` one, less the completed-world error allowance `2b/n`.  The two
halves of `lem:mesh` are its two orientations, `meshGap` and `meshGapLower`, and the
facts they need are proved once here. -/
def meshGapAt (A : LUVCombination) (i j n : ℕ) (b : ℚ) : AffineCombination :=
  AffineCombination.addConstEF ((A.meshAffine i).sub (A.meshAffine j)) (meshErrorFeature n b)

lemma meshGapAt_price (A : LUVCombination) (P : History)
    (i j n : ℕ) (b : ℚ) (day : ℕ) :
    (A.meshGapAt i j n b).price P day =
      A.expectAt P i day - A.expectAt P j day - (2 * (b : ℝ) / n) := by
  rw [meshGapAt, AffineCombination.addConstEF_price, AffineCombination.sub_price,
    meshAffine_price, meshAffine_price]
  rw [meshErrorFeature_denote]
  push_cast
  ring

/-- Every completed world values an oriented gap nonpositively, once the error allowance
is taken at a precision `n` no finer than either of the two compared meshes. -/
lemma meshGapAt_value_nonpos
    (A : LUVCombination) (P : History) (v : PCWorld) (ν : LUV → ℝ)
    {i j n : ℕ} (hn : 0 < n) (hi : n ≤ i) (hj : n ≤ j) {b : ℚ}
    (hshare : A.shareNorm P ≤ (b : ℝ)) (hvals : A.ValuesAt v ν) :
    (A.meshGapAt i j n b).value P v.payout ≤ 0 := by
  have hinear := A.meshAffine_value_near P v ν (hn.trans_le hi) hvals
  have hjnear := A.meshAffine_value_near P v ν (hn.trans_le hj) hvals
  rw [abs_le] at hinear hjnear
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hshare0 := A.shareNorm_nonneg P
  have hinvN : 0 ≤ 1 / (n : ℝ) := (one_div_pos.mpr hnR).le
  have hnerr : A.shareNorm P * (1 / (n : ℝ)) ≤ (b : ℝ) / n := by
    simpa [div_eq_mul_inv] using (mul_le_mul_of_nonneg_right hshare hinvN)
  have hcoarser : ∀ k : ℕ, n ≤ k →
      A.shareNorm P * (1 / (k : ℝ)) ≤ (b : ℝ) / n := by
    intro k hk
    have hkR : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    calc
      A.shareNorm P * (1 / (k : ℝ)) ≤ A.shareNorm P * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hnR hkR) hshare0
      _ ≤ (b : ℝ) / n := hnerr
  have hierr := hcoarser i hi
  have hjerr := hcoarser j hj
  have hgap :
      (A.meshAffine i).value P v.payout - (A.meshAffine j).value P v.payout ≤
        2 * ((b : ℝ) / n) := by
    linarith [hinear.2, hjnear.1]
  rw [meshGapAt, AffineCombination.addConstEF_value, AffineCombination.sub_value]
  rw [meshErrorFeature_denote]
  push_cast
  ring_nf at hgap ⊢
  linarith

/-- Appendix `lem:mesh`'s cross-precision gap.  It compares precision `n` with precision
`m` and subtracts the completed-world error allowance `2b/n`. -/
def meshGap (A : LUVCombination) (n m : ℕ) (b : ℚ) : AffineCombination :=
  AffineCombination.addConstEF ((A.meshAffine n).sub (A.meshAffine m)) (meshErrorFeature n b)

/-- Reverse cross-precision gap for the lower half of `lem:mesh`. -/
def meshGapLower (A : LUVCombination) (n m : ℕ) (b : ℚ) : AffineCombination :=
  AffineCombination.addConstEF ((A.meshAffine m).sub (A.meshAffine n)) (meshErrorFeature n b)

lemma meshGap_price (A : LUVCombination) (P : History)
    (n m : ℕ) (b : ℚ) (day : ℕ) :
    (A.meshGap n m b).price P day =
      A.expectAt P n day - A.expectAt P m day - (2 * (b : ℝ) / n) :=
  A.meshGapAt_price P n m n b day

lemma meshGap_value_nonpos
    (A : LUVCombination) (P : History) (v : PCWorld) (ν : LUV → ℝ)
    {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) {b : ℚ}
    (hshare : A.shareNorm P ≤ (b : ℝ)) (hvals : A.ValuesAt v ν) :
    (A.meshGap n m b).value P v.payout ≤ 0 :=
  A.meshGapAt_value_nonpos P v ν hn le_rfl hnm hshare hvals

lemma meshGapLower_price (A : LUVCombination) (P : History)
    (n m : ℕ) (b : ℚ) (day : ℕ) :
    (A.meshGapLower n m b).price P day =
      A.expectAt P m day - A.expectAt P n day - (2 * (b : ℝ) / n) :=
  A.meshGapAt_price P m n n b day

lemma meshGapLower_value_nonpos
    (A : LUVCombination) (P : History) (v : PCWorld) (ν : LUV → ℝ)
    {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) {b : ℚ}
    (hshare : A.shareNorm P ≤ (b : ℝ)) (hvals : A.ValuesAt v ν) :
    (A.meshGapLower n m b).value P v.payout ≤ 0 :=
  A.meshGapAt_value_nonpos P v ν hn hnm le_rfl hshare hvals

/-! ## The first-active softmax

The concrete portfolio that proves `lem:mesh`: each cross-precision gap receives its
threshold signal times the mass no earlier gap claimed.  The signal vocabulary it is
built from — `oneMinus`, `sellIndF`, `clip01` and their denotation lemmas — is
`Properties/Support/Exploitation.lean`'s. -/

/-- Remaining unallocated softmax mass after scanning a list of affine gaps. -/
def softmaxRemainder (gaps : List AffineCombination) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) : EF :=
  match gaps with
  | [] => remaining
  | A :: rest =>
      let signal := sellIndF (A.priceFeature day) threshold pad
      softmaxRemainder rest day threshold pad (.mul remaining (oneMinus signal))

/-- Continuous first-active softmax portfolio.  Each gap receives its threshold signal
times the mass not allocated to earlier gaps. -/
def softmaxAffine (gaps : List AffineCombination) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) : AffineCombination :=
  match gaps with
  | [] => AffineCombination.empty
  | A :: rest =>
      let signal := sellIndF (A.priceFeature day) threshold pad
      let weight := EF.mul remaining signal
      (A.scale weight).add
        (softmaxAffine rest day threshold pad (.mul remaining (oneMinus signal)))

/-- Total allocated mass, stated semantically to keep the recursive syntax transparent. -/
noncomputable def softmaxMass (gaps : List AffineCombination) (P : History)
    (day : ℕ) (threshold pad : ℚ) (remaining : EF) : ℝ :=
  match gaps with
  | [] => 0
  | A :: rest =>
      let signal := sellIndF (A.priceFeature day) threshold pad
      remaining.denote P * signal.denote P +
        softmaxMass rest P day threshold pad (.mul remaining (oneMinus signal))

lemma softmax_mass_add_remainder
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) :
    softmaxMass gaps P day threshold pad remaining +
        (softmaxRemainder gaps day threshold pad remaining).denote P =
      remaining.denote P := by
  induction gaps generalizing remaining with
  | nil => simp [softmaxMass, softmaxRemainder]
  | cons A rest ih =>
      simp only [softmaxMass, softmaxRemainder]
      rw [add_assoc, ih]
      simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
      ring

/-- A first-active softmax of uniformly magnitude-bounded inputs has the same magnitude
bound: its nonnegative allocation weights have total mass at most the initial mass. -/
lemma softmaxAffine_magnitude_le
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) (C : ℝ)
    (hrem : 0 ≤ remaining.denote P) (hC : 0 ≤ C)
    (hgaps : ∀ A ∈ gaps, A.magnitude P ≤ C) :
    (softmaxAffine gaps day threshold pad remaining).magnitude P ≤
      remaining.denote P * C := by
  induction gaps generalizing remaining with
  | nil =>
      simp only [softmaxAffine, AffineCombination.empty, AffineCombination.magnitude,
        List.map_nil, List.sum_nil]
      exact mul_nonneg hrem hC
  | cons A rest ih =>
      let signal := sellIndF (A.priceFeature day) threshold pad
      have hsig := sellIndF_mem (A.priceFeature day) threshold pad P
      have hnew : 0 ≤ (EF.mul remaining (oneMinus signal)).denote P := by
        simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
        exact mul_nonneg hrem (sub_nonneg.mpr hsig.2)
      have htail := ih (.mul remaining (oneMinus signal)) hnew
        (fun B hB ↦ hgaps B (by simp [hB]))
      have hA := hgaps A (by simp)
      have hweight :
          |(EF.mul remaining signal).denote P| =
            remaining.denote P * signal.denote P := by
        rw [EF.denote_mul, Pi.mul_apply,
          abs_of_nonneg (mul_nonneg hrem hsig.1)]
      simp only [softmaxAffine]
      rw [AffineCombination.add_magnitude, AffineCombination.scale_magnitude, hweight]
      simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote] at htail
      have hheadMul := mul_le_mul_of_nonneg_left hA
        (mul_nonneg hrem hsig.1)
      have htailMul := mul_le_mul_of_nonneg_left hC
        (mul_nonneg hrem (sub_nonneg.mpr hsig.2))
      nlinarith

/-- Price analogue of `softmaxAffine_magnitude_le`. -/
lemma abs_softmaxAffine_price_le
    (gaps : List AffineCombination) (P : History) (day priceDay : ℕ)
    (threshold pad : ℚ) (remaining : EF) (C : ℝ)
    (hrem : 0 ≤ remaining.denote P) (hC : 0 ≤ C)
    (hgaps : ∀ A ∈ gaps, |A.price P priceDay| ≤ C) :
    |(softmaxAffine gaps day threshold pad remaining).price P priceDay| ≤
      remaining.denote P * C := by
  induction gaps generalizing remaining with
  | nil =>
      simp only [softmaxAffine, AffineCombination.empty, AffineCombination.price,
        AffineCombination.value, List.map_nil, List.sum_nil, add_zero, EF.denote_const,
        Rat.cast_zero, abs_zero]
      exact mul_nonneg hrem hC
  | cons A rest ih =>
      let signal := sellIndF (A.priceFeature day) threshold pad
      have hsig := sellIndF_mem (A.priceFeature day) threshold pad P
      have hnew : 0 ≤ (EF.mul remaining (oneMinus signal)).denote P := by
        simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
        exact mul_nonneg hrem (sub_nonneg.mpr hsig.2)
      have htail := ih (.mul remaining (oneMinus signal)) hnew
        (fun B hB ↦ hgaps B (by simp [hB]))
      have hA := hgaps A (by simp)
      simp only [softmaxAffine, AffineCombination.add_price,
        AffineCombination.scale_price, EF.denote_mul, Pi.mul_apply]
      calc
        |remaining.denote P * signal.denote P * A.price P priceDay +
            (softmaxAffine rest day threshold pad
              (remaining.mul (oneMinus signal))).price P priceDay| ≤
            |remaining.denote P * signal.denote P * A.price P priceDay| +
              |(softmaxAffine rest day threshold pad
                (remaining.mul (oneMinus signal))).price P priceDay| := by
          exact abs_add_le _ _
        _ = remaining.denote P * signal.denote P * |A.price P priceDay| +
              |(softmaxAffine rest day threshold pad
                (remaining.mul (oneMinus signal))).price P priceDay| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hrem, abs_of_nonneg hsig.1]
        _ ≤ remaining.denote P * signal.denote P * C +
              (remaining.mul (oneMinus signal)).denote P * C :=
          add_le_add
            (mul_le_mul_of_nonneg_left hA (mul_nonneg hrem hsig.1)) htail
        _ = remaining.denote P * C := by
          simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
          ring

lemma softmaxAffine_value_nonpos
    (gaps : List AffineCombination) (P : History) (w : Valuation) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) (hrem : 0 ≤ remaining.denote P)
    (hgaps : ∀ A ∈ gaps, A.value P w ≤ 0) :
    (softmaxAffine gaps day threshold pad remaining).value P w ≤ 0 := by
  induction gaps generalizing remaining with
  | nil => simp [softmaxAffine, AffineCombination.empty, AffineCombination.value]
  | cons A rest ih =>
      simp only [softmaxAffine, AffineCombination.add_value,
        AffineCombination.scale_value]
      have hsig := sellIndF_mem (A.priceFeature day) threshold pad P
      have hweight : 0 ≤ remaining.denote P *
          (sellIndF (A.priceFeature day) threshold pad).denote P :=
        mul_nonneg hrem hsig.1
      have hnew : 0 ≤ (EF.mul remaining
          (oneMinus (sellIndF (A.priceFeature day) threshold pad))).denote P := by
        simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
        exact mul_nonneg hrem (sub_nonneg.mpr hsig.2)
      have htail := ih _ hnew (fun B hB => hgaps B (by simp [hB]))
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hweight (hgaps A (by simp))) htail

lemma softmaxRemainder_eq_zero_of_signal_one
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF)
    (hdet : ∃ A ∈ gaps,
      (sellIndF (A.priceFeature day) threshold pad).denote P = 1) :
    (softmaxRemainder gaps day threshold pad remaining).denote P = 0 := by
  induction gaps generalizing remaining with
  | nil => simp at hdet
  | cons A rest ih =>
      obtain ⟨B, hB, hsignal⟩ := hdet
      simp only [List.mem_cons] at hB
      simp only [softmaxRemainder]
      rcases hB with hBA | hB
      · subst B
        have hzero : (EF.mul remaining
            (oneMinus (sellIndF (A.priceFeature day) threshold pad))).denote P = 0 := by
          rw [EF.denote_mul, Pi.mul_apply, oneMinus_denote, hsignal]
          ring
        have hz : ∀ l : List AffineCombination, ∀ e : EF, e.denote P = 0 →
            (softmaxRemainder l day threshold pad e).denote P = 0 := by
          intro l
          induction l with
          | nil => intro e he; simpa [softmaxRemainder] using he
          | cons C tail iht =>
              intro e he
              simp only [softmaxRemainder]
              apply iht
              simp [EF.denote_mul, he]
        exact hz rest _ hzero
      · exact ih _ ⟨B, hB, hsignal⟩

lemma softmaxMass_eq_remaining_of_signal_one
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF)
    (hdet : ∃ A ∈ gaps,
      (sellIndF (A.priceFeature day) threshold pad).denote P = 1) :
    softmaxMass gaps P day threshold pad remaining = remaining.denote P := by
  have hzero := softmaxRemainder_eq_zero_of_signal_one
    gaps P day threshold pad remaining hdet
  have hid := softmax_mass_add_remainder gaps P day threshold pad remaining
  linarith

lemma softmaxAffine_price_ge_mass
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) (hrem : 0 ≤ remaining.denote P)
    (q : ℝ)
    (hactive : ∀ A ∈ gaps,
      0 < (sellIndF (A.priceFeature day) threshold pad).denote P →
        q ≤ A.price P day) :
    q * softmaxMass gaps P day threshold pad remaining ≤
      (softmaxAffine gaps day threshold pad remaining).price P day := by
  induction gaps generalizing remaining with
  | nil => simp [softmaxMass, softmaxAffine, AffineCombination.empty,
      AffineCombination.price, AffineCombination.value]
  | cons A rest ih =>
      simp only [softmaxMass, softmaxAffine, AffineCombination.add_price,
        AffineCombination.scale_price, EF.denote_mul, Pi.mul_apply]
      let signal := sellIndF (A.priceFeature day) threshold pad
      have hsig := sellIndF_mem (A.priceFeature day) threshold pad P
      have hweight : 0 ≤ remaining.denote P * signal.denote P :=
        mul_nonneg hrem hsig.1
      have hhead : q * (remaining.denote P * signal.denote P) ≤
          remaining.denote P * signal.denote P * A.price P day := by
        by_cases hz : signal.denote P = 0
        · simp [hz]
        · have hspos : 0 < signal.denote P := lt_of_le_of_ne hsig.1 (Ne.symm hz)
          simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left (hactive A (by simp) hspos) hweight)
      have hnew : 0 ≤ (EF.mul remaining (oneMinus signal)).denote P := by
        simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
        exact mul_nonneg hrem (sub_nonneg.mpr hsig.2)
      have htail := ih (.mul remaining (oneMinus signal)) hnew
        (fun B hB hs => hactive B (by simp [hB]) hs)
      dsimp only [signal] at hhead hnew htail ⊢
      linarith

lemma softmaxAffine_price_ge_threshold_sub_pad_of_detected
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (hpad : 0 < (pad : ℝ))
    (hdet : ∃ A ∈ gaps, (threshold : ℝ) < A.price P day) :
    (threshold : ℝ) - pad ≤
      (softmaxAffine gaps day threshold pad (.const 1)).price P day := by
  have hsignal : ∃ A ∈ gaps,
      (sellIndF (A.priceFeature day) threshold pad).denote P = 1 := by
    obtain ⟨A, hA, hprice⟩ := hdet
    refine ⟨A, hA, ?_⟩
    apply sellIndF_eq_one hpad
    rw [A.priceFeature_denote]
    exact hprice
  have hmass := softmaxMass_eq_remaining_of_signal_one
    gaps P day threshold pad (.const 1) hsignal
  have hlower := softmaxAffine_price_ge_mass gaps P day threshold pad (.const 1)
    (by simp) ((threshold : ℝ) - pad) (by
      intro A hA hpos
      have h := sellIndF_pos_imp hpad hpos
      rw [A.priceFeature_denote] at h
      exact h.le)
  simp only [EF.denote_const] at hmass hlower
  rw [hmass] at hlower
  simpa using hlower

/-- All cross-precision gaps considered by the day-`m` softmax (`n = 1, …, m`): day `n`'s
own grid `n + 1` against day `m`'s grid `m + 1`. -/
def meshGaps (As : ℕ → LUVCombination) (m : ℕ) (b : ℚ) :
    List AffineCombination :=
  (List.range m).map (fun i => (As (i + 1)).meshGap (i + 2) (m + 1) b)

/-- The actual Appendix softmax sequence for the upper half of `lem:mesh`. -/
def meshSoftmax (As : ℕ → LUVCombination) (b ε : ℚ) (m : ℕ) :
    AffineCombination :=
  softmaxAffine (meshGaps As m b) m (ε / 2) (ε / 4) (.const 1)

/-- `meshGaps` with the two precisions exchanged, for the lower half of `lem:mesh`. -/
def meshGapsLower (As : ℕ → LUVCombination) (m : ℕ) (b : ℚ) :
    List AffineCombination :=
  (List.range m).map (fun i => (As (i + 1)).meshGapLower (i + 2) (m + 1) b)

/-- Reverse-gap softmax for the lower half of `lem:mesh`. -/
def meshSoftmaxLower (As : ℕ → LUVCombination) (b ε : ℚ) (m : ℕ) :
    AffineCombination :=
  softmaxAffine (meshGapsLower As m b) m (ε / 2) (ε / 4) (.const 1)

lemma meshSoftmax_value_nonpos
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (hvalued : WorldValued As DP) {b ε : ℚ}
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    (meshSoftmax As b ε m).value P v.payout ≤ 0 := by
  apply softmaxAffine_value_nonpos
  · simp
  · intro A hA
    simp only [meshGaps, List.mem_map, List.mem_range] at hA
    obtain ⟨i, hi, rfl⟩ := hA
    obtain ⟨ν, hvals⟩ := hvalued (i + 1) v hv
    apply meshGap_value_nonpos (As (i + 1)) P v ν (by omega) (by omega)
      (hshare (i + 1)) hvals

lemma meshSoftmax_detects_upper_gap
    {As : ℕ → LUVCombination} {P : History} {b ε : ℚ}
    (hε : 0 < (ε : ℝ)) {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (hgap : (ε : ℝ) <
      (As n).expectAt P (n + 1) m - (As n).expectAt P (m + 1) m -
        2 * (b : ℝ) / ((n : ℝ) + 1)) :
    (ε : ℝ) / 4 ≤ (meshSoftmax As b ε m).price P m := by
  have hdet : ∃ A ∈ meshGaps As m b,
      (((ε / 2 : ℚ) : ℝ)) < A.price P m := by
    let i := n - 1
    have hi : i < m := by dsimp [i]; omega
    have hin : i + 1 = n := by dsimp [i]; omega
    refine ⟨(As n).meshGap (n + 1) (m + 1) b, ?_, ?_⟩
    · simp only [meshGaps, List.mem_map, List.mem_range]
      exact ⟨i, hi, by rw [show i + 2 = n + 1 by omega, hin]⟩
    · rw [meshGap_price]
      push_cast
      linarith
  have hsoft := softmaxAffine_price_ge_threshold_sub_pad_of_detected
    (meshGaps As m b) P m (ε / 2) (ε / 4) (by
      push_cast
      linarith) hdet
  dsimp only [meshSoftmax]
  push_cast at hsoft ⊢
  linarith

lemma meshSoftmaxLower_value_nonpos
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (hvalued : WorldValued As DP) {b ε : ℚ}
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    (meshSoftmaxLower As b ε m).value P v.payout ≤ 0 := by
  apply softmaxAffine_value_nonpos
  · simp
  · intro A hA
    simp only [meshGapsLower, List.mem_map, List.mem_range] at hA
    obtain ⟨i, hi, rfl⟩ := hA
    obtain ⟨ν, hvals⟩ := hvalued (i + 1) v hv
    apply meshGapLower_value_nonpos (As (i + 1)) P v ν (by omega) (by omega)
      (hshare (i + 1)) hvals

lemma meshSoftmaxLower_detects_gap
    {As : ℕ → LUVCombination} {P : History} {b ε : ℚ}
    (hε : 0 < (ε : ℝ)) {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (hgap : (ε : ℝ) <
      (As n).expectAt P (m + 1) m - (As n).expectAt P (n + 1) m -
        2 * (b : ℝ) / ((n : ℝ) + 1)) :
    (ε : ℝ) / 4 ≤ (meshSoftmaxLower As b ε m).price P m := by
  have hdet : ∃ A ∈ meshGapsLower As m b,
      (((ε / 2 : ℚ) : ℝ)) < A.price P m := by
    let i := n - 1
    have hi : i < m := by dsimp [i]; omega
    have hin : i + 1 = n := by dsimp [i]; omega
    refine ⟨(As n).meshGapLower (n + 1) (m + 1) b, ?_, ?_⟩
    · simp only [meshGapsLower, List.mem_map, List.mem_range]
      exact ⟨i, hi, by rw [show i + 2 = n + 1 by omega, hin]⟩
    · rw [meshGapLower_price]
      push_cast
      linarith
  have hsoft := softmaxAffine_price_ge_threshold_sub_pad_of_detected
    (meshGapsLower As m b) P m (ε / 2) (ε / 4) (by
      push_cast
      linarith) hdet
  dsimp only [meshSoftmaxLower]
  push_cast at hsoft ⊢
  linarith

/-- Narrow operational boundary for the concrete softmax syntax.  It certifies only
uniform emission and structural boundedness of `meshSoftmax`; all completed-world
semantics, gap detection, and market conclusions are proved outside this structure.
Paper node: `thm:wubexp` -/
structure MeshSoftmaxOperationalWitness
    (As : ℕ → LUVCombination) (P : History) where
  poly : ∀ b ε : ℚ,
    AffineCombination.PolySequence (meshSoftmax As b ε)
  bounded : ∀ b ε : ℚ,
    BoundedAffinePrices (meshSoftmax As b ε) P
  magnitude : ∀ b ε : ℚ,
    ∃ C : ℝ, ∀ m, (meshSoftmax As b ε m).magnitude P ≤ C
  lower_poly : ∀ b ε : ℚ,
    AffineCombination.PolySequence (meshSoftmaxLower As b ε)
  lower_bounded : ∀ b ε : ℚ,
    BoundedAffinePrices (meshSoftmaxLower As b ε) P
  lower_magnitude : ∀ b ε : ℚ,
    ∃ C : ℝ, ∀ m, (meshSoftmaxLower As b ε m).magnitude P ≤ C

/-- Upper half of Appendix `lem:mesh`: after the softmax compiler has emitted the
concrete sequence, no cross-precision upper discrepancy can exceed `2b/n + ε`
infinitely often. -/
lemma mesh_upper_eventually
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP) (b ε : ℚ) (hε : 0 < (ε : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ᶠ m in atTop, ∀ n, 0 < n → n ≤ m →
      (As n).expectAt P (n + 1) m - (As n).expectAt P (m + 1) m ≤
        2 * (b : ℝ) / ((n : ℝ) + 1) + (ε : ℝ) := by
  have hlearn := (ops.poly b ε).affine_provind_theory_le P DP
    (ops.bounded b ε) (ops.magnitude b ε) hworld 0
    (fun m v hv => meshSoftmax_value_nonpos hvalued hshare m v hv)
  have hevent := hlearn ((ε : ℝ) / 8) (by positivity)
  filter_upwards [hevent] with m hm
  intro n hn hnm
  by_contra hnot
  have hgap : (ε : ℝ) <
      (As n).expectAt P (n + 1) m - (As n).expectAt P (m + 1) m -
        2 * (b : ℝ) / ((n : ℝ) + 1) := by
    push_neg at hnot
    linarith
  have hdetect := meshSoftmax_detects_upper_gap hε hn hnm hgap
  change (meshSoftmax As b ε m).price P m ≤ 0 + (ε : ℝ) / 8 at hm
  linarith

lemma mesh_lower_eventually
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP) (b ε : ℚ) (hε : 0 < (ε : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ᶠ m in atTop, ∀ n, 0 < n → n ≤ m →
      (As n).expectAt P (m + 1) m - (As n).expectAt P (n + 1) m ≤
        2 * (b : ℝ) / ((n : ℝ) + 1) + (ε : ℝ) := by
  have hlearn := (ops.lower_poly b ε).affine_provind_theory_le P DP
    (ops.lower_bounded b ε) (ops.lower_magnitude b ε) hworld 0
    (fun m v hv => meshSoftmaxLower_value_nonpos hvalued hshare m v hv)
  have hevent := hlearn ((ε : ℝ) / 8) (by positivity)
  filter_upwards [hevent] with m hm
  intro n hn hnm
  by_contra hnot
  have hgap : (ε : ℝ) <
      (As n).expectAt P (m + 1) m - (As n).expectAt P (n + 1) m -
        2 * (b : ℝ) / ((n : ℝ) + 1) := by
    push_neg at hnot
    linarith
  have hdetect := meshSoftmaxLower_detects_gap hε hn hnm hgap
  change (meshSoftmaxLower As b ε m).price P m ≤ 0 + (ε : ℝ) / 8 at hm
  linarith

/-- Two-sided finite form of Appendix `lem:mesh`. -/
lemma mesh_close_eventually
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP) (b ε : ℚ) (hε : 0 < (ε : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ᶠ m in atTop, ∀ n, 0 < n → n ≤ m →
      |(As n).expectAt P (n + 1) m - (As n).expectAt P (m + 1) m| ≤
        2 * (b : ℝ) / ((n : ℝ) + 1) + (ε : ℝ) := by
  filter_upwards [mesh_upper_eventually ops hvalued b ε hε hshare hworld,
    mesh_lower_eventually ops hvalued b ε hε hshare hworld] with m hu hl
  intro n hn hnm
  rw [abs_le]
  constructor
  · linarith [hl n hn hnm]
  · exact hu n hn hnm

/-- Operational certificate for a polynomial LUV-combination sequence.  The field is
the exact compiled threshold mesh consumed by the affine theorems; it contains no market,
world-value, convergence, or learning conclusion.
Paper node: `def:ec`, `def:luv` -/
structure PolySequence (As : ℕ → LUVCombination) where
  mesh_poly : AffineCombination.PolySequence (fun n => (As n).meshAffine (n + 1))

/-- `def:blcp`: a polynomially generated LUV-combination sequence with one uniform full
coefficient `L¹` bound.
Paper node: `def:blcp` -/
structure BoundedSequence (As : ℕ → LUVCombination) (P : History) where
  poly : PolySequence As
  bounded : ∃ B : ℝ, ∀ n, (As n).l1Norm P ≤ B

/-- A `def:blcp` sequence has a nonnegative *rational* share bound.  The `L¹` bound of
`def:blcp` is a real, while the mesh constructions ask for a rational `b` — it is written
into the closed feature `meshErrorFeature` and into the scaling `meshNormScale` — and
`l1Norm = |const| + shareNorm` turns the one into the other.  Every endpoint below that
asks a client for `b`, `hb` and `hshare` can therefore obtain all three from the
`BoundedSequence` it already has; the `_ofBounded` forms do exactly that. -/
lemma BoundedSequence.exists_rat_shareBound {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) :
    ∃ b : ℚ, 0 ≤ (b : ℝ) ∧ ∀ n, (As n).shareNorm P ≤ (b : ℝ) := by
  obtain ⟨B, hB⟩ := h.bounded
  obtain ⟨b, hb⟩ := exists_rat_gt (max B 0)
  have hB' : B ≤ (b : ℝ) := (le_max_left B 0).trans hb.le
  refine ⟨b, (le_max_right B 0).trans hb.le, fun n => ?_⟩
  have hshare : (As n).shareNorm P ≤ (As n).l1Norm P := by
    simp only [l1Norm]
    linarith [abs_nonneg ((As n).const.denote P)]
  exact hshare.trans ((hB n).trans hB')

/-- Propositional representation boundary needed to invoke `thm:ec` on every LUV
appearing in a combination sequence.  It records only compact threshold codeability and
completed-theory world valuation; it does not assume convergence or any expectation
theorem.

`world_value` sits at the paper's `def:luv` quantifier — `v ∈ cworlds(Θ)`, i.e.
`PCWorld.ConsistentWithTheory` — matching `thm:ec`'s own `hval`.  It is exactly the
per-LUV content of `WorldValued` (see `WorldValued.convergencePresentation`); no
stage-indexed valuation is assumed. -/
structure ConvergencePresentation (As : ℕ → LUVCombination)
    (DP : DeductiveProcess) where
  threshold_code : ∀ n p, p ∈ (As n).terms → p.2.RpnThresholdCodes
  world_value : ∀ n p, p ∈ (As n).terms → ∀ v : PCWorld,
    v.ConsistentWithTheory DP → ∃ x : ℝ, v.ValuesAt p.2 x

/-- `WorldValued` — the completed-world valuation boundary the mesh theorems already
carry — supplies a `ConvergencePresentation` outright once threshold codes are given.
`thm:expcoh`/`thm:perexpkno` therefore state a single world-value premise, at
`cworlds(Θ)`, and build the presentation internally. -/
def WorldValued.convergencePresentation {As : ℕ → LUVCombination}
    {DP : DeductiveProcess} (hvalued : WorldValued As DP)
    (hcode : ∀ n p, p ∈ (As n).terms → p.2.RpnThresholdCodes) :
    ConvergencePresentation As DP where
  threshold_code := hcode
  world_value n p hp v hv := by
    obtain ⟨ν, hν⟩ := hvalued n v hv
    exact ⟨ν p.2, hν p hp⟩

/-- The paper's future expectation extrema use each future day's own mesh. -/
noncomputable def futureLow (As : ℕ → LUVCombination)
    (P : History) (n : ℕ) : ℝ :=
  sInf (Set.range (fun j => (As n).expect P (n + j)))

/-- The companion of `futureLow`: the supremum, over future days, of the fixed day-`n`
combination's expectation. -/
noncomputable def futureHigh (As : ℕ → LUVCombination)
    (P : History) (n : ℕ) : ℝ :=
  sSup (Set.range (fun j => (As n).expect P (n + j)))

private lemma meshBlock_magnitude_le
    (α : EF) (X : LUV) (P : History) (k : ℕ) :
    ((X.expectAffine k).scale α).magnitude P ≤ |α.denote P| := by
  rw [AffineCombination.scale_magnitude]
  have hX := X.expectAffine_magnitude_le_one P k
  exact mul_le_of_le_one_right (abs_nonneg _) hX

/-- Mesh expansion does not increase share magnitude. -/
lemma meshAffine_magnitude_le_shareNorm
    (A : LUVCombination) (P : History) (k : ℕ) :
    (A.meshAffine k).magnitude P ≤ A.shareNorm P := by
  simp only [AffineCombination.magnitude, meshAffine, shareNorm]
  induction A.terms with
  | nil => simp
  | cons p rest ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      have hp := meshBlock_magnitude_le p.1 p.2 P k
      simp only [AffineCombination.magnitude] at hp
      linarith

private lemma expectAffine_magnitude_eq_one (X : LUV) (P : History) {k : ℕ}
    (hk : 0 < k) : (X.expectAffine k).magnitude P = 1 := by
  simp only [LUV.expectAffine, AffineCombination.magnitude, List.map_map]
  change ((List.range k).map (fun _ => |(((1 / (k : ℚ) : ℚ) : ℝ))|)).sum = 1
  rw [List.map_const', List.sum_replicate, List.length_range, nsmul_eq_mul]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  push_cast
  rw [abs_of_nonneg (by positivity)]
  field_simp

private lemma meshBlock_magnitude_eq
    (α : EF) (X : LUV) (P : History) {k : ℕ} (hk : 0 < k) :
    ((X.expectAffine k).scale α).magnitude P = |α.denote P| := by
  rw [AffineCombination.scale_magnitude, expectAffine_magnitude_eq_one X P hk, mul_one]

/-- At positive precision the mesh expansion has *exactly* the share norm as its
magnitude: each LUV's `k` threshold shares carry coefficient `aᵢ/k`.  The lower half is
what makes the mesh error negligible against the traded magnitude (`ErrorNegligible`). -/
lemma meshAffine_magnitude_eq_shareNorm
    (A : LUVCombination) (P : History) {k : ℕ} (hk : 0 < k) :
    (A.meshAffine k).magnitude P = A.shareNorm P := by
  simp only [AffineCombination.magnitude, meshAffine, shareNorm]
  induction A.terms with
  | nil => simp
  | cons p rest ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      have hp := meshBlock_magnitude_eq p.1 p.2 P hk
      simp only [AffineCombination.magnitude] at hp
      rw [hp, ih]

/-- A gap trades at most twice the share norm, whatever its orientation: the error
allowance is a constant and contributes no magnitude. -/
lemma meshGapAt_magnitude_le (A : LUVCombination) (P : History)
    (i j n : ℕ) (b : ℚ) :
    (A.meshGapAt i j n b).magnitude P ≤ 2 * A.shareNorm P := by
  rw [meshGapAt, AffineCombination.addConstEF_magnitude, AffineCombination.sub_magnitude]
  linarith [A.meshAffine_magnitude_le_shareNorm P i,
    A.meshAffine_magnitude_le_shareNorm P j]

lemma meshGap_magnitude_le (A : LUVCombination) (P : History)
    (n m : ℕ) (b : ℚ) :
    (A.meshGap n m b).magnitude P ≤ 2 * A.shareNorm P :=
  A.meshGapAt_magnitude_le P n m n b

lemma meshGapLower_magnitude_le (A : LUVCombination) (P : History)
    (n m : ℕ) (b : ℚ) :
    (A.meshGapLower n m b).magnitude P ≤ 2 * A.shareNorm P :=
  A.meshGapAt_magnitude_le P m n n b

/-- Mesh expansion does not increase the full `L¹` norm. -/
lemma meshAffine_l1Norm_le (A : LUVCombination) (P : History) (k : ℕ) :
    (A.meshAffine k).l1Norm P ≤ A.l1Norm P := by
  simp only [AffineCombination.l1Norm, l1Norm, meshAffine]
  exact add_le_add le_rfl (A.meshAffine_magnitude_le_shareNorm P k)

lemma abs_expectAt_le_l1Norm
    (A : LUVCombination) (P : History) (k m : ℕ)
    (hP : ∀ φ, 0 ≤ P m φ ∧ P m φ ≤ 1) :
    |A.expectAt P k m| ≤ A.l1Norm P := by
  rw [← meshAffine_price]
  exact ((A.meshAffine k).abs_price_le_l1Norm P m hP).trans
    (A.meshAffine_l1Norm_le P k)

/-- A gap's price is bounded by twice the `L¹` bound plus twice the error allowance's
numerator, whatever its orientation. -/
lemma abs_meshGapAt_price_le (A : LUVCombination) (P : History)
    {i j n day : ℕ} (hn : 0 < n) (b : ℚ) (B : ℝ)
    (hB : A.l1Norm P ≤ B) (hP : ∀ φ, 0 ≤ P day φ ∧ P day φ ≤ 1) :
    |(A.meshGapAt i j n b).price P day| ≤ 2 * B + 2 * |(b : ℝ)| := by
  have hiExp := A.abs_expectAt_le_l1Norm P i day hP
  have hjExp := A.abs_expectAt_le_l1Norm P j day hP
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [abs_of_nonneg (by positivity)]
    exact hnR
  have hz : |2 * (b : ℝ) / n| ≤ 2 * |(b : ℝ)| := by
    rw [abs_div, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    exact div_le_self (mul_nonneg (by norm_num) (abs_nonneg _)) hden
  rw [meshGapAt_price]
  calc
    |A.expectAt P i day - A.expectAt P j day - 2 * (b : ℝ) / n| ≤
        |A.expectAt P i day| + |A.expectAt P j day| + |2 * (b : ℝ) / n| := by
      linarith [abs_sub (A.expectAt P i day) (A.expectAt P j day),
        abs_sub (A.expectAt P i day - A.expectAt P j day) (2 * (b : ℝ) / n)]
    _ ≤ 2 * B + 2 * |(b : ℝ)| := by linarith

lemma abs_meshGap_price_le (A : LUVCombination) (P : History)
    {n m day : ℕ} (hn : 0 < n) (b : ℚ) (B : ℝ)
    (hB : A.l1Norm P ≤ B) (hP : ∀ φ, 0 ≤ P day φ ∧ P day φ ≤ 1) :
    |(A.meshGap n m b).price P day| ≤ 2 * B + 2 * |(b : ℝ)| :=
  A.abs_meshGapAt_price_le (i := n) (j := m) P hn b B hB hP

lemma abs_meshGapLower_price_le (A : LUVCombination) (P : History)
    {n m day : ℕ} (hn : 0 < n) (b : ℚ) (B : ℝ)
    (hB : A.l1Norm P ≤ B) (hP : ∀ φ, 0 ≤ P day φ ∧ P day φ ≤ 1) :
    |(A.meshGapLower n m b).price P day| ≤ 2 * B + 2 * |(b : ℝ)| :=
  A.abs_meshGapAt_price_le (i := m) (j := n) P hn b B hB hP

/-- Tail supremum appearing literally in Appendix `lem:mesh`. -/
noncomputable def meshTailError (As : ℕ → LUVCombination)
    (P : History) (n : ℕ) : ℝ :=
  sSup (Set.range (fun j =>
    |(As n).expectAt P (n + 1) (n + j) - (As n).expectAt P (n + j + 1) (n + j)|))

lemma BoundedSequence.meshTailError_bddAbove
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    BddAbove (Set.range (fun j =>
      |(As n).expectAt P (n + 1) (n + j) - (As n).expectAt P (n + j + 1) (n + j)|)) := by
  obtain ⟨B, hB⟩ := h.bounded
  have hB0 : 0 ≤ B := (As 0).l1Norm_nonneg P |>.trans (hB 0)
  refine ⟨2 * B, ?_⟩
  rintro x ⟨j, rfl⟩
  have hcoarse := (As n).abs_expectAt_le_l1Norm P (n + 1) (n + j) (hP (n + j))
  have hfine := (As n).abs_expectAt_le_l1Norm P (n + j + 1) (n + j) (hP (n + j))
  calc
    |(As n).expectAt P (n + 1) (n + j) - (As n).expectAt P (n + j + 1) (n + j)|
        ≤ |(As n).expectAt P (n + 1) (n + j)| +
          |(As n).expectAt P (n + j + 1) (n + j)| := abs_sub _ _
    _ ≤ B + B := add_le_add (hcoarse.trans (hB n)) (hfine.trans (hB n))
    _ = 2 * B := by ring

lemma BoundedSequence.meshTailError_nonneg
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    0 ≤ meshTailError As P n := by
  apply le_csSup (h.meshTailError_bddAbove hP n)
  exact ⟨0, by simp⟩

lemma meshTailError_le
    {As : ℕ → LUVCombination} {P : History}
    {n : ℕ} {δ : ℝ}
    (hδ : ∀ m, n ≤ m →
      |(As n).expectAt P (n + 1) m - (As n).expectAt P (m + 1) m| ≤ δ) :
    meshTailError As P n ≤ δ := by
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨j, rfl⟩
  exact hδ (n + j) (by omega)

/-! ## Weighted averages and limit transfer

Analysis with no LUV content, used to move a conclusion between two asymptotically
indistinguishable sequences.  What is general is stated outside `LUVCombination`, so a
client reaches it under its own name; `weightedAverage_tendsto_zero_of_tendsto_zero` and
`hasLimitPoint_add_tendsto_zero` stay inside it, beside the weighted-bias endpoints that
consume them. -/

end LUVCombination

/-- `c / (n + 1) → 0`: the day-index-shifted form of
`tendsto_const_div_atTop_nhds_zero_nat`, used wherever a grid error `1/(n+1)` is squeezed
to zero. -/
lemma tendsto_const_div_succ_atTop_nhds_zero (c : ℝ) :
    Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat c).comp (Filter.tendsto_add_atTop_nat 1)
  simpa [Function.comp_def] using h

private lemma abs_sSup_range_sub_sSup_range_le
    (f g : ℕ → ℝ)
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g))
    (he : BddAbove (Set.range (fun j => |f j - g j|))) :
    |sSup (Set.range f) - sSup (Set.range g)| ≤
      sSup (Set.range (fun j => |f j - g j|)) := by
  let E := sSup (Set.range (fun j => |f j - g j|))
  have hfg : sSup (Set.range f) ≤ sSup (Set.range g) + E := by
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    have hgj := le_csSup hg ⟨j, rfl⟩
    have hej := le_csSup he ⟨j, rfl⟩
    dsimp only [E] at hej ⊢
    linarith [le_abs_self (f j - g j)]
  have hgf : sSup (Set.range g) ≤ sSup (Set.range f) + E := by
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    have hfj := le_csSup hf ⟨j, rfl⟩
    have hej := le_csSup he ⟨j, rfl⟩
    dsimp only [E] at hej ⊢
    linarith [neg_le_abs (f j - g j)]
  rw [abs_le]
  constructor <;> dsimp only [E] at * <;> linarith

private lemma abs_sInf_range_sub_sInf_range_le
    (f g : ℕ → ℝ)
    (hf : BddBelow (Set.range f)) (hg : BddBelow (Set.range g))
    (he : BddAbove (Set.range (fun j => |f j - g j|))) :
    |sInf (Set.range f) - sInf (Set.range g)| ≤
      sSup (Set.range (fun j => |f j - g j|)) := by
  let E := sSup (Set.range (fun j => |f j - g j|))
  have hgf : sInf (Set.range g) - E ≤ sInf (Set.range f) := by
    apply le_csInf (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    have hgj := csInf_le hg ⟨j, rfl⟩
    have hej := le_csSup he ⟨j, rfl⟩
    dsimp only [E] at hej ⊢
    linarith [neg_le_abs (f j - g j)]
  have hfg : sInf (Set.range f) - E ≤ sInf (Set.range g) := by
    apply le_csInf (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    have hfj := csInf_le hf ⟨j, rfl⟩
    have hej := le_csSup he ⟨j, rfl⟩
    dsimp only [E] at hej ⊢
    linarith [le_abs_self (f j - g j)]
  rw [abs_le]
  constructor <;> dsimp only [E] at * <;> linarith

private lemma abs_sInf_sub_sInf_le_of_mutually_near
    (S T : Set ℝ) (E : ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSb : BddBelow S) (hTb : BddBelow T)
    (hST : ∀ x ∈ S, ∃ y ∈ T, |x - y| ≤ E)
    (hTS : ∀ y ∈ T, ∃ x ∈ S, |x - y| ≤ E) :
    |sInf S - sInf T| ≤ E := by
  have hTSinf : sInf T - E ≤ sInf S := by
    apply le_csInf hS
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hST x hx
    have hyinf := csInf_le hTb hy
    rw [abs_le] at hxy
    linarith
  have hSTinf : sInf S - E ≤ sInf T := by
    apply le_csInf hT
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hTS y hy
    have hxinf := csInf_le hSb hx
    rw [abs_le] at hxy
    linarith
  rw [abs_le]
  constructor <;> linarith

private lemma abs_sSup_sub_sSup_le_of_mutually_near
    (S T : Set ℝ) (E : ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSb : BddAbove S) (hTb : BddAbove T)
    (hST : ∀ x ∈ S, ∃ y ∈ T, |x - y| ≤ E)
    (hTS : ∀ y ∈ T, ∃ x ∈ S, |x - y| ≤ E) :
    |sSup S - sSup T| ≤ E := by
  have hSTsup : sSup S ≤ sSup T + E := by
    apply csSup_le hS
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hST x hx
    have hysup := le_csSup hTb hy
    rw [abs_le] at hxy
    linarith
  have hTSsup : sSup T ≤ sSup S + E := by
    apply csSup_le hT
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hTS y hy
    have hxsup := le_csSup hSb hx
    rw [abs_le] at hxy
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Bounded real sequences with a vanishing pointwise difference have the same lower
and upper limits.  This is the analytic transfer used after Appendix `lem:mesh`. -/
private lemma liminf_limsup_eq_of_abs_sub_tendsto_zero
    (f g : ℕ → ℝ)
    (hglo : IsBoundedUnder (· ≥ ·) atTop g)
    (hghi : IsBoundedUnder (· ≤ ·) atTop g)
    (hnear : Tendsto (fun n => |f n - g n|) atTop (𝓝 0)) :
    liminf f atTop = liminf g atTop ∧ limsup f atTop = limsup g atTop := by
  let d : ℕ → ℝ := fun n => f n - g n
  have hdabs : Tendsto (abs ∘ d) atTop (𝓝 0) := by
    exact hnear
  have hd : Tendsto d atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero d).2 hdabs
  have hdsmall : ∀ᶠ n in atTop, |d n| < 1 := by
    have hball := hd.eventually (Metric.ball_mem_nhds 0 zero_lt_one)
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hball
  have hdlo : IsBoundedUnder (· ≥ ·) atTop d :=
    isBoundedUnder_of_eventually_ge (a := (-1 : ℝ))
      (hdsmall.mono fun n hn => by linarith [neg_le_abs (d n)])
  have hdhi : IsBoundedUnder (· ≤ ·) atTop d :=
    isBoundedUnder_of_eventually_le (a := (1 : ℝ))
      (hdsmall.mono fun n hn => by linarith [le_abs_self (d n)])
  have hdinf : liminf d atTop = 0 := hd.liminf_eq
  have hdsup : limsup d atTop = 0 := hd.limsup_eq
  constructor
  · have hlo : liminf g atTop + liminf d atTop ≤ liminf f atTop :=
      (le_liminf_add hglo hghi hdlo hdhi.isCobounded_flip).trans_eq
        (liminf_congr (Eventually.of_forall fun n => by
          change g n + d n = f n
          dsimp only [d]
          ring))
    have hhi : liminf f atTop ≤ limsup d atTop + liminf g atTop :=
      (liminf_congr (Eventually.of_forall fun n => by
        change f n = d n + g n
        dsimp only [d]
        ring)).trans_le
        (liminf_add_le hdlo hdhi hglo hghi.isCobounded_flip)
    rw [hdinf, add_zero] at hlo
    rw [hdsup, zero_add] at hhi
    exact le_antisymm hhi hlo
  · have hlo : limsup g atTop + liminf d atTop ≤ limsup f atTop :=
      (le_limsup_add hghi hglo.isCobounded_flip hdhi hdlo).trans_eq
        (limsup_congr (Eventually.of_forall fun n => by
          change g n + d n = f n
          dsimp only [d]
          ring))
    have hhi : limsup f atTop ≤ limsup g atTop + limsup d atTop :=
      (limsup_congr (Eventually.of_forall fun n => by
        change f n = g n + d n
        dsimp only [d]
        ring)).trans_le
        (limsup_add_le hglo hghi hdlo.isCobounded_flip hdhi)
    rw [hdinf, add_zero] at hlo
    rw [hdsup, add_zero] at hhi
    exact le_antisymm hhi hlo

namespace LUVCombination

/-- A Toeplitz-style transfer for the repository's inclusive weighted averages:
nonnegative weights with divergent total mass send every null sequence to zero. -/
lemma weightedAverage_tendsto_zero_of_tendsto_zero
    {w e : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n)
    (hdiv : Tendsto (prefixSum w) atTop atTop)
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (weightedAverage w e) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 he (ε / 2) (half_pos hε)
  let C : ℝ := ∑ i ∈ Finset.range N, w i * |e i|
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hw0 i) (abs_nonneg _)
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (hdiv.eventually (eventually_gt_atTop (2 * C / ε)))
  refine ⟨max N M, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left N M).trans hn
  have hnM : M ≤ n := (le_max_right N M).trans hn
  have hdenLarge : 2 * C / ε < prefixSum w n := hM n hnM
  have hdenPos : 0 < prefixSum w n := by
    have hleft : 0 ≤ 2 * C / ε := div_nonneg (mul_nonneg (by norm_num) hC0) hε.le
    linarith
  have htail : ∀ i ∈ Finset.Ico N (n + 1), |e i| < ε / 2 := by
    intro i hi
    simpa only [Real.dist_eq, sub_zero] using hN i (Finset.mem_Ico.mp hi).1
  have habsNum : |prefixSum (fun i => w i * e i) n| ≤
      C + (ε / 2) * prefixSum w n := by
    calc
      |prefixSum (fun i => w i * e i) n| ≤
          ∑ i ∈ Finset.range (n + 1), |w i * e i| := by
        rw [prefixSum]
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range (n + 1), w i * |e i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (hw0 i)]
      _ = C + ∑ i ∈ Finset.Ico N (n + 1), w i * |e i| := by
        dsimp only [C]
        exact (Finset.sum_range_add_sum_Ico
          (fun i => w i * |e i|) (by omega : N ≤ n + 1)).symm
      _ ≤ C + ∑ i ∈ Finset.Ico N (n + 1), w i * (ε / 2) := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (le_of_lt (htail i hi)) (hw0 i)
      _ ≤ C + ∑ i ∈ Finset.range (n + 1), w i * (ε / 2) := by
        apply add_le_add_right
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
        · intro i hi hnot
          exact mul_nonneg (hw0 i) (half_pos hε).le
      _ = C + (ε / 2) * prefixSum w n := by
        rw [prefixSum]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [Real.dist_eq, sub_zero, weightedAverage_eq_div (ne_of_gt hdenPos),
    abs_div, abs_of_pos hdenPos]
  have hCsmall : C / prefixSum w n < ε / 2 := by
    rw [div_lt_iff₀ hdenPos]
    rw [div_lt_iff₀ hε] at hdenLarge
    nlinarith
  calc
    |prefixSum (fun i => w i * e i) n| / prefixSum w n ≤
        (C + (ε / 2) * prefixSum w n) / prefixSum w n :=
      div_le_div_of_nonneg_right habsNum hdenPos.le
    _ = C / prefixSum w n + ε / 2 := by field_simp
    _ < ε := by linarith

/-- A null perturbation of a sequence does not disturb `0` as a limit point. -/
lemma hasLimitPoint_add_tendsto_zero
    {f d : ℕ → ℝ} (hf : HasLimitPoint f 0)
    (hd : Tendsto d atTop (𝓝 0)) :
    HasLimitPoint (fun n => f n + d n) 0 := by
  obtain ⟨ψ, hψmono, hfψ⟩ := hf.exists_subseq
  have hdψ : Tendsto (d ∘ ψ) atTop (𝓝 0) := hd.comp hψmono.tendsto_atTop
  have hsum : Tendsto ((fun n => f n + d n) ∘ ψ) atTop (𝓝 0) := by
    convert hfψ.add hdψ using 1
    · rfl
    · simp
  exact MapClusterPt.of_comp hψmono.tendsto_atTop hsum.mapClusterPt

/-! ## Mesh independence (`lem:mesh`) -/

lemma BoundedSequence.futureHigh_mesh_near
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    |affineFutureHigh (fun i => (As i).meshAffine (i + 1)) P n - futureHigh As P n| ≤
      meshTailError As P n := by
  obtain ⟨B, hB⟩ := h.bounded
  have hcoarse : BddAbove (Set.range (fun j => (As n).expectAt P (n + 1) (n + j))) := by
    refine ⟨B, ?_⟩
    rintro x ⟨j, rfl⟩
    exact (le_abs_self _).trans
      ((As n).abs_expectAt_le_l1Norm P (n + 1) (n + j) (hP (n + j)) |>.trans (hB n))
  have hfine : BddAbove (Set.range (fun j => (As n).expectAt P (n + j + 1) (n + j))) := by
    refine ⟨B, ?_⟩
    rintro x ⟨j, rfl⟩
    exact (le_abs_self _).trans
      ((As n).abs_expectAt_le_l1Norm P (n + j + 1) (n + j) (hP (n + j)) |>.trans (hB n))
  simpa only [affineFutureHigh, meshAffine_price, futureHigh, meshTailError, expect] using
    abs_sSup_range_sub_sSup_range_le
      (fun j => (As n).expectAt P (n + 1) (n + j))
      (fun j => (As n).expectAt P (n + j + 1) (n + j)) hcoarse hfine
      (h.meshTailError_bddAbove hP n)

lemma BoundedSequence.futureLow_mesh_near
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    |affineFutureLow (fun i => (As i).meshAffine (i + 1)) P n - futureLow As P n| ≤
      meshTailError As P n := by
  obtain ⟨B, hB⟩ := h.bounded
  have hcoarse : BddBelow (Set.range (fun j => (As n).expectAt P (n + 1) (n + j))) := by
    refine ⟨-B, ?_⟩
    rintro x ⟨j, rfl⟩
    exact (neg_le_neg ((As n).abs_expectAt_le_l1Norm P (n + 1) (n + j)
      (hP (n + j)) |>.trans (hB n))).trans (neg_abs_le _)
  have hfine : BddBelow (Set.range (fun j => (As n).expectAt P (n + j + 1) (n + j))) := by
    refine ⟨-B, ?_⟩
    rintro x ⟨j, rfl⟩
    exact (neg_le_neg ((As n).abs_expectAt_le_l1Norm P (n + j + 1) (n + j)
      (hP (n + j)) |>.trans (hB n))).trans (neg_abs_le _)
  simpa only [affineFutureLow, meshAffine_price, futureLow, meshTailError, expect] using
    abs_sInf_range_sub_sInf_range_le
      (fun j => (As n).expectAt P (n + 1) (n + j))
      (fun j => (As n).expectAt P (n + j + 1) (n + j)) hcoarse hfine
      (h.meshTailError_bddAbove hP n)

/-- A BLCS uniformly bounds both future expectation extrema, supplying the finite
liminf/limsup hypotheses used by the mesh transfer. -/
lemma BoundedSequence.futureExtrema_filterBounds
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) :
    IsBoundedUnder (· ≥ ·) atTop (futureHigh As P) ∧
    IsBoundedUnder (· ≤ ·) atTop (futureHigh As P) ∧
    IsBoundedUnder (· ≥ ·) atTop (futureLow As P) ∧
    IsBoundedUnder (· ≤ ·) atTop (futureLow As P) := by
  obtain ⟨B, hB⟩ := h.bounded
  have habs : ∀ n m, |(As n).expect P m| ≤ B := fun n m =>
    ((As n).abs_expectAt_le_l1Norm P (m + 1) m (hP m)).trans (hB n)
  have hhighLo : ∀ n, -B ≤ futureHigh As P n := fun n => by
    have hdiagLo : -B ≤ (As n).expect P n := by
      linarith [neg_le_abs ((As n).expect P n), habs n n]
    exact hdiagLo.trans (le_csSup (by
      refine ⟨B, ?_⟩
      rintro x ⟨j, rfl⟩
      exact (le_abs_self _).trans (habs n (n + j))) ⟨0, by simp⟩)
  have hhighHi : ∀ n, futureHigh As P n ≤ B := fun n => by
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    exact (le_abs_self _).trans (habs n (n + j))
  have hlowLo : ∀ n, -B ≤ futureLow As P n := fun n => by
    apply le_csInf (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    linarith [neg_le_abs ((As n).expect P (n + j)), habs n (n + j)]
  have hlowHi : ∀ n, futureLow As P n ≤ B := fun n => by
    have hbdd : BddBelow (Set.range (fun j => (As n).expect P (n + j))) := by
      refine ⟨-B, ?_⟩
      rintro x ⟨j, rfl⟩
      linarith [neg_le_abs ((As n).expect P (n + j)), habs n (n + j)]
    exact (csInf_le hbdd (show (As n).expect P n ∈
      Set.range (fun j => (As n).expect P (n + j)) from ⟨0, by simp⟩)).trans
        ((le_abs_self _).trans (habs n n))
  exact ⟨isBoundedUnder_of_eventually_ge (Eventually.of_forall hhighLo),
    isBoundedUnder_of_eventually_le (Eventually.of_forall hhighHi),
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hlowLo),
    isBoundedUnder_of_eventually_le (Eventually.of_forall hlowHi)⟩

/-- Appendix `lem:mesh`: uniformly over all future market days, the fixed day-`n`
threshold mesh and the future day's own mesh become indistinguishable.
Paper node: `lem:mesh` -/
theorem BoundedSequence.mesh_independence
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (b : ℚ) (hb : 0 ≤ (b : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (meshTailError As P) atTop (𝓝 0) := by
  have hP := IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  apply Metric.tendsto_atTop.2
  intro δ hδ
  obtain ⟨ε, hε0, hεδ⟩ : ∃ ε : ℚ,
      (0 : ℝ) < ε ∧ (ε : ℝ) < δ / 2 := exists_rat_btwn (half_pos hδ)
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (b : ℝ) / δ)
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (mesh_close_eventually ops hvalued b ε hε0 hshare hworld)
  refine ⟨max 1 (max N M), fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hNn : 4 * (b : ℝ) / δ < (n : ℝ) :=
    hN.trans_le (by exact_mod_cast (le_trans (le_max_left N M)
      (le_trans (le_max_right 1 (max N M)) hn)))
  have hsmall : 2 * (b : ℝ) / ((n : ℝ) + 1) < δ / 2 := by
    have hmono : 2 * (b : ℝ) / ((n : ℝ) + 1) ≤ 2 * (b : ℝ) / n :=
      div_le_div_of_nonneg_left (by linarith) hnR (by linarith)
    refine hmono.trans_lt ?_
    by_cases hb0 : (b : ℝ) = 0
    · rw [hb0]
      simp [hδ]
    · have hbpos : 0 < (b : ℝ) := lt_of_le_of_ne hb (Ne.symm hb0)
      have hδ0 := hδ
      rw [div_lt_iff₀ hδ] at hNn
      rw [div_lt_iff₀ hnR]
      nlinarith
  have hnM : M ≤ n :=
    (le_max_right N M).trans (le_max_right 1 (max N M) |>.trans hn)
  have hpair : ∀ m, n ≤ m →
      |(As n).expectAt P (n + 1) m - (As n).expectAt P (m + 1) m| ≤
        2 * (b : ℝ) / ((n : ℝ) + 1) + (ε : ℝ) := by
    intro m hnm
    rcases Nat.lt_or_ge n m with hlt | hge
    · exact hM m (hnM.trans hnm) n hn0 hnm
    · have hmn : m = n := le_antisymm hge hnm
      subst hmn
      have hb' : 0 ≤ 2 * (b : ℝ) / ((m : ℝ) + 1) := by positivity
      simp only [sub_self, abs_zero]
      linarith
  have hsup := meshTailError_le hpair
  have hnonneg := h.meshTailError_nonneg hP n
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact hsup.trans_lt (by linarith)

/-- `mesh_independence` with the rational share bound obtained from the
`BoundedSequence` itself (`exists_rat_shareBound`) rather than asked of the client. -/
lemma BoundedSequence.mesh_independence_ofBounded
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (meshTailError As P) atTop (𝓝 0) := by
  obtain ⟨b, hb, hshare⟩ := h.exists_rat_shareBound
  exact h.mesh_independence ops hvalued b hb hshare hworld

/-! ## Polynomial and bounded LUV-combination consequences -/

/-- Rank preservation for the mesh lift: an emitter of `meshAffine A k` inherits the
source combination's rank bound, which is what `Strategy.rank_le` obliges a compiled
trader to establish.  It is the API fact a client compiling a LUV combination needs, and
is stated once here rather than at each emitter. -/
lemma meshAffine_rank
    (A : LUVCombination) {day k : ℕ}
    (hconst : A.const.rank ≤ day)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ day) :
    (A.meshAffine k).const.rank ≤ day ∧
      ∀ p ∈ (A.meshAffine k).terms, p.1.rank ≤ day := by
  refine ⟨hconst, ?_⟩
  intro p hp
  simp only [meshAffine, List.mem_flatMap] at hp
  obtain ⟨q, hq, hp⟩ := hp
  simp only [AffineCombination.scale, List.mem_map] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  simp only [EF.rank_mul]
  apply Nat.max_le.mpr
  refine ⟨hterms q hq, ?_⟩
  simp only [LUV.expectAffine, List.mem_map] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  simp [EF.rank]

/-- A BLCS compiles to the paper's affine BCS at the diagonal mesh precision. -/
def BoundedSequence.affineBCS {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) :
    AffineCombination.BoundedCombinationSequence
      (fun n => (As n).meshAffine (n + 1)) P where
  poly := h.poly.mesh_poly
  bounded := by
    obtain ⟨B, hB⟩ := h.bounded
    exact ⟨B, fun n => ((As n).meshAffine_l1Norm_le P (n + 1)).trans (hB n)⟩

lemma BoundedSequence.mesh_magnitudeBounded
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) :
    ∃ B : ℝ, ∀ n, ((As n).meshAffine (n + 1)).magnitude P ≤ B :=
  h.affineBCS.magnitudeBounded

lemma BoundedSequence.mesh_boundedPrices
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) :
    BoundedAffinePrices (fun n => (As n).meshAffine (n + 1)) P :=
  h.affineBCS.boundedPrices hP

/-- `PolySequence.mesh_poly` transported along the rational scaling `meshNormScale b`. -/
noncomputable def BoundedSequence.normalizedMesh_poly
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) (b : ℚ) :
    AffineCombination.PolySequence (normalizedMesh As b) := by
  exact h.poly.mesh_poly.scaleRat (meshNormScale b)

lemma BoundedSequence.normalizedMesh_boundedPrices
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) (b : ℚ)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) :
    BoundedAffinePrices (normalizedMesh As b) P := by
  exact (h.mesh_boundedPrices hP).scaleRat (meshNormScale b)

lemma normalizedMesh_magnitude_le_one
    {As : ℕ → LUVCombination} {P : History}
    (b : ℚ)
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ)) (n : ℕ) :
    (normalizedMesh As b n).magnitude P ≤ 1 := by
  have hq0 : 0 ≤ ((meshNormScale b : ℚ) : ℝ) := (meshNormScale_pos b).le
  rw [normalizedMesh, AffineCombination.scale_magnitude, EF.denote_const,
    abs_of_nonneg hq0]
  exact (mul_le_mul_of_nonneg_left
    ((As n).meshAffine_magnitude_le_shareNorm P (n + 1)) hq0).trans
    ((mul_le_mul_of_nonneg_left (hshare n) hq0).trans
      (meshNormScale_mul_le_one b))

/-! ## Limiting expectations (`lem:limexpapprox`) -/

/-- Canonical limiting expectation of a fixed combination.  Subsequent mesh-independence
theorems identify this limsup with the actual limit. -/
noncomputable def expectInf (A : LUVCombination) (P : History) : ℝ :=
  limsup (fun m => A.expect P m) atTop

private lemma expectTerms_converge
    (l : List (EF × LUV)) (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hcode : ∀ p ∈ l, p.2.RpnThresholdCodes)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ p ∈ l, ∀ v : PCWorld,
      v.ConsistentWithTheory DP → ∃ x : ℝ, v.ValuesAt p.2 x) :
    ∃ L : ℝ, Tendsto (fun m =>
      (l.map (fun p => p.1.denote P * p.2.expect P m)).sum) atTop (𝓝 L) := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons p rest ih =>
      obtain ⟨LX, hLX⟩ := p.2.expect_converges P DP (hcode p (by simp)) hworld
        (hval p (by simp))
      have hcodeRest : ∀ q ∈ rest, q.2.RpnThresholdCodes := by
        intro q hq
        exact hcode q (by simp [hq])
      have hvalRest : ∀ q ∈ rest, ∀ v : PCWorld,
          v.ConsistentWithTheory DP → ∃ x : ℝ, v.ValuesAt q.2 x := by
        intro q hq
        exact hval q (by simp [hq])
      obtain ⟨LR, hLR⟩ := ih hcodeRest hvalRest
      refine ⟨p.1.denote P * LX + LR, ?_⟩
      exact (tendsto_const_nhds.mul hLX).add hLR

/-- Each represented fixed LUV combination really converges to the canonical
`expectInf`; the definition by `limsup` merely avoids carrying a chosen witness. -/
lemma ConvergencePresentation.expect_tendsto_expectInf
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (hc : ConvergencePresentation As DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    Tendsto (fun m => (As n).expect P m) atTop (𝓝 ((As n).expectInf P)) := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  obtain ⟨L, hL⟩ := expectTerms_converge (As n).terms P DP
    (hc.threshold_code n) hworld (hc.world_value n)
  have hfull : Tendsto (fun m => (As n).expect P m) atTop
      (𝓝 ((As n).const.denote P + L)) := by
    exact tendsto_const_nhds.add hL
  have heq : (As n).expectInf P = (As n).const.denote P + L := by
    simpa only [expectInf] using hfull.limsup_eq
  simpa only [heq] using hfull

/-- `lem:limexpapprox`, pointwise quantitative form: the fixed precision-`n` affine
valuation at the market's limiting beliefs differs from the actual limiting expectation
by at most the literal mesh-tail error. -/
theorem BoundedSequence.mesh_limitingValue_near_expectInf
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hc : ConvergencePresentation As DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    |((As n).meshAffine (n + 1)).value P (limitingBelief P) - (As n).expectInf P| ≤
      meshTailError As P n := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  have hmeshLim := ((As n).meshAffine (n + 1)).price_tendsto_limitingValue P DP hworld
  have hexpectLim := hc.expect_tendsto_expectInf (P := P) hworld n
  have hdiffLim := (hmeshLim.sub hexpectLim).abs
  apply le_of_tendsto hdiffLim
  apply eventually_atTop.2
  refine ⟨n, fun m hnm => ?_⟩
  have hrange : |(As n).expectAt P (n + 1) m - (As n).expectAt P (m + 1) m| ≤
      meshTailError As P n := by
    apply le_csSup (h.meshTailError_bddAbove hP n)
    refine ⟨m - n, ?_⟩
    simp only [Nat.add_sub_of_le hnm]
  simpa only [meshAffine_price, expect] using hrange

/-- `lem:limexpapprox`: limiting-belief evaluation of the diagonal threshold mesh and
the true limiting expectation are asymptotically equal. -/
theorem BoundedSequence.limexpapprox
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (hcode : ∀ n p, p ∈ (As n).terms → p.2.RpnThresholdCodes)
    (b : ℚ) (hb : 0 ≤ (b : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n =>
      |((As n).meshAffine (n + 1)).value P (limitingBelief P) - (As n).expectInf P|)
      atTop (𝓝 0) := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  exact squeeze_zero (fun n => abs_nonneg _)
    (fun n =>
      h.mesh_limitingValue_near_expectInf (hvalued.convergencePresentation hcode) hworld n)
    (h.mesh_independence ops hvalued b hb hshare hworld)

/-- `limexpapprox` with the rational share bound obtained from the `BoundedSequence`
itself (`exists_rat_shareBound`) rather than asked of the client. -/
lemma BoundedSequence.limexpapprox_ofBounded
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (hcode : ∀ n p, p ∈ (As n).terms → p.2.RpnThresholdCodes)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n =>
      |((As n).meshAffine (n + 1)).value P (limitingBelief P) - (As n).expectInf P|)
      atTop (𝓝 0) := by
  obtain ⟨b, hb, hshare⟩ := h.exists_rat_shareBound
  exact h.limexpapprox ops hvalued hcode b hb hshare hworld

/-! ## Approximate determination and the mesh error budget -/

/-- A LUV-combination sequence is determined when every completed-theory world and every
coherent assignment to its LUVs gives the same advertised value. -/
def DeterminedViaTheory (As : ℕ → LUVCombination) (P : History)
    (DP : DeductiveProcess) (truth : ℕ → ℝ) : Prop :=
  ∀ n (v : PCWorld) (ν : LUV → ℝ), v.ConsistentWithTheory DP →
    (As n).ValuesAt v ν → (As n).value P ν = truth n

/-- `meshTheoryTruth` scaled by `meshNormScale b`: the truth stream the normalized mesh
`normalizedMesh` is compared against. -/
noncomputable def normalizedMeshTruth (As : ℕ → LUVCombination) (P : History)
    (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℚ) (n : ℕ) : ℝ :=
  ((meshNormScale b : ℚ) : ℝ) * meshTheoryTruth As P DP hworld n

/-! ### The mesh is only *approximately* determined

The paper's `def:affthmval` determines a LUV *combination*, not its component LUVs, so
completed worlds may disagree about the individual threshold sentences the mesh trades.
What holds is quantitative: two completed worlds each reproduce the determined
combination value to within `shareNorm/n`, hence agree with each other to within twice
that — and trivially to within the mesh's own coefficient sum.  That is exactly the
`ApproxDeterminedViaTheory` + `ErrorNegligible` input of the affine bias-run economics, and
(via `meshErrorBound_tendsto_zero`) of the `thm:wubexp` feedback bridge.

There is deliberately no *exact* mesh-determination lemma.  Exact mesh determination is
available only from `ExactTheoryPresentation`, which fixes a value for each component LUV
and so demands strictly more than `def:affthmval`; anything proved through it would carry
that strengthening.  Nothing needs it — affine provability induction accepts a vanishing
residual (`affine_provind_theory_tendsto_zero`). -/

/-- Diagonal mesh-error budget for the normalized threshold mesh. -/
noncomputable def meshErrorBound (As : ℕ → LUVCombination) (P : History) (b : ℚ)
    (n : ℕ) : ℝ :=
  min ((normalizedMesh As b n).magnitude P)
    (2 * ((meshNormScale b : ℚ) : ℝ) * (As n).shareNorm P / ((n : ℝ) + 1))

private lemma payout_eq_zero_or_one (u : PCWorld) (φ : Sentence) :
    u.payout φ = 0 ∨ u.payout φ = 1 := by
  by_cases hφ : u.Holds φ
  · exact Or.inr (by simp [PCWorld.payout, hφ])
  · exact Or.inl (by simp [PCWorld.payout, hφ])

lemma normalizedMesh_errorNegligible (As : ℕ → LUVCombination) (P : History) (b : ℚ) :
    AffineCombination.ErrorNegligible (normalizedMesh As b) P (meshErrorBound As P b) := by
  have hq := (meshNormScale_pos b).le
  refine ⟨fun n => ?_, fun n => min_le_left _ _, fun c hc => ?_⟩
  · refine le_min ((normalizedMesh As b n).magnitude_nonneg P) ?_
    have := (As n).shareNorm_nonneg P
    positivity
  · obtain ⟨N, hN⟩ := exists_nat_gt (2 / c)
    refine ⟨N, fun i hi => ?_⟩
    have hiR : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hmagEq : (normalizedMesh As b i).magnitude P =
        ((meshNormScale b : ℚ) : ℝ) * (As i).shareNorm P := by
      rw [normalizedMesh, AffineCombination.scale_magnitude, EF.denote_const,
        abs_of_pos (meshNormScale_pos b),
        (As i).meshAffine_magnitude_eq_shareNorm P i.succ_pos]
    have hmag0 : 0 ≤ (normalizedMesh As b i).magnitude P :=
      (normalizedMesh As b i).magnitude_nonneg P
    have hci : 2 / ((i : ℝ) + 1) ≤ c := by
      have hNi : ((N : ℕ) : ℝ) ≤ i := by exact_mod_cast hi
      rw [div_le_iff₀ hiR]
      nlinarith [(div_lt_iff₀ hc).1 hN]
    refine le_trans (min_le_right _ _) ?_
    have hrewrite : 2 * ((meshNormScale b : ℚ) : ℝ) * (As i).shareNorm P / ((i : ℝ) + 1) =
        (2 / ((i : ℝ) + 1)) * (normalizedMesh As b i).magnitude P := by
      rw [hmagEq]
      field_simp
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_right hci hmag0

/-- The diagonal mesh-error budget vanishes for a share-bounded sequence.  This is
`lem:conluvapprox`'s `O(1/n)` in the form the feedback bridge consumes: the residual by
which completed worlds may disagree about the *mesh* of a combination-determined sequence
tends to zero, which is all affine provability induction needs to learn its price. -/
lemma meshErrorBound_tendsto_zero {As : ℕ → LUVCombination} {P : History} (b : ℚ)
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ)) :
    Tendsto (meshErrorBound As P b) atTop (𝓝 0) := by
  have hq := (meshNormScale_pos b).le
  have h2q : (0 : ℝ) ≤ 2 * ((meshNormScale b : ℚ) : ℝ) := by
    exact mul_nonneg (by norm_num) hq
  refine squeeze_zero (fun n => (normalizedMesh_errorNegligible As P b).1 n)
    (fun n => ?_)
    (tendsto_const_div_succ_atTop_nhds_zero (2 * ((meshNormScale b : ℚ) : ℝ) * (b : ℝ)))
  refine (min_le_right _ _).trans ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  gcongr
  exact hshare n

/-- Combination-level determination (`def:affthmval`) plus per-world LUV values make the
diagonal mesh approximately determined, with the negligible `meshErrorBound`. -/
lemma WorldValued.normalizedMesh_approxDetermined
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (b : ℚ) :
    AffineCombination.ApproxDeterminedViaTheory (normalizedMesh As b) P DP
      (normalizedMeshTruth As P DP hworld b) (meshErrorBound As P b) := by
  intro n v hv
  set tw := theoryWorld DP hworld with htwdef
  have htw : tw.ConsistentWithTheory DP := theoryWorld_consistent DP hworld
  have hdiff : (normalizedMesh As b n).value P v.payout -
      normalizedMeshTruth As P DP hworld b n =
      (normalizedMesh As b n).value P v.payout -
        (normalizedMesh As b n).value P tw.payout := by
    rw [normalizedMeshTruth, meshTheoryTruth, normalizedMesh,
      AffineCombination.scale_value, AffineCombination.scale_value, EF.denote_const]
  have hmagb : |(normalizedMesh As b n).value P v.payout -
      normalizedMeshTruth As P DP hworld b n| ≤
      (normalizedMesh As b n).magnitude P := by
    rw [hdiff]
    exact (normalizedMesh As b n).abs_value_sub_value_le_magnitude P _ _
      (payout_eq_zero_or_one v) (payout_eq_zero_or_one tw)
  rw [meshErrorBound, le_min_iff]
  refine ⟨hmagb, ?_⟩
  obtain ⟨νv, hνv⟩ := h n v hv
  obtain ⟨νw, hνw⟩ := h n tw htw
  have h1 : |((As n).meshAffine (n + 1)).value P v.payout - truth n| ≤
      (As n).shareNorm P * (1 / ((n : ℝ) + 1)) := by
    simpa [hdet n v νv hv hνv] using
      (As n).meshAffine_value_near (k := n + 1) P v νv n.succ_pos hνv
  have h2 : |((As n).meshAffine (n + 1)).value P tw.payout - truth n| ≤
      (As n).shareNorm P * (1 / ((n : ℝ) + 1)) := by
    simpa [hdet n tw νw htw hνw] using
      (As n).meshAffine_value_near (k := n + 1) P tw νw n.succ_pos hνw
  have hsum : |((As n).meshAffine (n + 1)).value P v.payout -
      ((As n).meshAffine (n + 1)).value P tw.payout| ≤
      2 * ((As n).shareNorm P * (1 / ((n : ℝ) + 1))) := by
    have htri := abs_add_le
      (((As n).meshAffine (n + 1)).value P v.payout - truth n)
      (truth n - ((As n).meshAffine (n + 1)).value P tw.payout)
    have hrw : (((As n).meshAffine (n + 1)).value P v.payout - truth n) +
        (truth n - ((As n).meshAffine (n + 1)).value P tw.payout) =
        ((As n).meshAffine (n + 1)).value P v.payout -
          ((As n).meshAffine (n + 1)).value P tw.payout := by ring
    rw [hrw] at htri
    rw [abs_sub_comm (truth n)] at htri
    linarith
  have hnR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [hdiff, normalizedMesh, AffineCombination.scale_value,
    AffineCombination.scale_value, EF.denote_const, ← mul_sub, abs_mul,
    abs_of_pos (meshNormScale_pos b)]
  have hstep := mul_le_mul_of_nonneg_left hsum (meshNormScale_pos b).le
  refine hstep.trans ?_
  rw [le_div_iff₀ hnR]
  field_simp
  exact le_refl _

/-- The mesh's common completed-theory truth differs from the determined
LUV-combination truth by at most `shareNorm / n`.

Only `WorldValued` is needed: the mesh-error identity requires each completed world to
give the component LUVs *some* coherent values, and `DeterminedViaTheory` then pins the
value of the *combination* — which is exactly the paper's `def:affthmval` premise.  No
per-component agreement across worlds is used. -/
lemma WorldValued.meshTheoryTruth_near
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (n : ℕ) :
    |meshTheoryTruth As P DP hworld n - truth n| ≤
      (As n).shareNorm P * (1 / ((n : ℝ) + 1)) := by
  let v := theoryWorld DP hworld
  have hv : v.ConsistentWithTheory DP := theoryWorld_consistent DP hworld
  obtain ⟨ν, hvals⟩ := h n v hv
  have hnear := (As n).meshAffine_value_near (k := n + 1) P v ν n.succ_pos hvals
  have htruth := hdet n v ν hv hvals
  simpa only [meshTheoryTruth, v, htruth, Nat.cast_add, Nat.cast_one] using hnear

lemma WorldValued.meshTheoryTruth_sub_truth_tendsto
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ)) :
    Tendsto (fun n => meshTheoryTruth As P DP hworld n - truth n)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
    (Eventually.of_forall fun n => ?_) (tendsto_const_div_succ_atTop_nhds_zero (b : ℝ))
  refine (h.meshTheoryTruth_near hdet hworld n).trans ?_
  rw [div_eq_mul_inv, one_mul]
  exact mul_le_mul_of_nonneg_right (hshare n) (by positivity)

/-! ## Completed-world extrema -/

/-- The completed-theory values of a LUV combination, using actual coherent LUV values
rather than its finite threshold mesh. -/
def completedValues (DP : DeductiveProcess) (A : LUVCombination)
    (P : History) : Set ℝ :=
  {x | ∃ (v : PCWorld) (ν : LUV → ℝ), v.ConsistentWithTheory DP ∧
      A.ValuesAt v ν ∧ A.value P ν = x}

/-- The infimum of `completedValues`. -/
noncomputable def completedLow (As : ℕ → LUVCombination)
    (P : History) (DP : DeductiveProcess) (n : ℕ) : ℝ :=
  sInf (completedValues DP (As n) P)

/-- The supremum of `completedValues`. -/
noncomputable def completedHigh (As : ℕ → LUVCombination)
    (P : History) (DP : DeductiveProcess) (n : ℕ) : ℝ :=
  sSup (completedValues DP (As n) P)

lemma completedValues_to_mesh
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (n : ℕ) {x : ℝ}
    (hx : x ∈ completedValues DP (As n) P) :
    ∃ y ∈ completedAffineValues DP ((As n).meshAffine (n + 1)) P,
      |y - x| ≤ (As n).shareNorm P * (1 / ((n : ℝ) + 1)) := by
  obtain ⟨v, ν, hv, hvals, rfl⟩ := hx
  refine ⟨((As n).meshAffine (n + 1)).value P v.payout, ⟨v, hv, rfl⟩, ?_⟩
  simpa using (As n).meshAffine_value_near (k := n + 1) P v ν n.succ_pos hvals

lemma mesh_completedValue_to_exact
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (hvalued : WorldValued As DP) (n : ℕ) {y : ℝ}
    (hy : y ∈ completedAffineValues DP ((As n).meshAffine (n + 1)) P) :
    ∃ x ∈ completedValues DP (As n) P,
      |y - x| ≤ (As n).shareNorm P * (1 / ((n : ℝ) + 1)) := by
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨ν, hvals⟩ := hvalued n v hv
  refine ⟨(As n).value P ν, ⟨v, ν, hv, hvals, rfl⟩, ?_⟩
  simpa using (As n).meshAffine_value_near (k := n + 1) P v ν n.succ_pos hvals

/-- Completed-world extrema of the finite threshold mesh approximate the exact
LUV-combination extrema within the same `shareNorm / (n+1)` bound. -/
lemma BoundedSequence.completedExtrema_mesh_near
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : BoundedSequence As P)
    (hvalued : WorldValued As DP)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (n : ℕ) :
    |completedAffineLow (fun i => (As i).meshAffine (i + 1)) P DP n -
        completedLow As P DP n| ≤ (As n).shareNorm P * (1 / ((n : ℝ) + 1)) ∧
      |completedAffineHigh (fun i => (As i).meshAffine (i + 1)) P DP n -
        completedHigh As P DP n| ≤ (As n).shareNorm P * (1 / ((n : ℝ) + 1)) := by
  let S := completedAffineValues DP ((As n).meshAffine (n + 1)) P
  let T := completedValues DP (As n) P
  let E := (As n).shareNorm P * (1 / ((n : ℝ) + 1))
  have hS : S.Nonempty := completedAffineValues_nonempty DP ((As n).meshAffine (n + 1)) P hworld
  have hST : ∀ y ∈ S, ∃ x ∈ T, |y - x| ≤ E := by
    intro y hy
    exact mesh_completedValue_to_exact hvalued n hy
  have hTS : ∀ x ∈ T, ∃ y ∈ S, |y - x| ≤ E := by
    intro x hx
    exact completedValues_to_mesh n hx
  have hT : T.Nonempty := by
    obtain ⟨y, hy⟩ := hS
    obtain ⟨x, hx, _⟩ := hST y hy
    exact ⟨x, hx⟩
  obtain ⟨hSb, hSa⟩ := h.poly.mesh_poly.completedAffineValues_bdd P DP
    (h.mesh_boundedPrices hP) h.mesh_magnitudeBounded hP n
  have hTb : BddBelow T := by
    obtain ⟨L, hL⟩ := hSb
    refine ⟨L - E, ?_⟩
    intro x hx
    obtain ⟨y, hy, hnear⟩ := hTS x hx
    have hyL := hL hy
    rw [abs_le] at hnear
    linarith
  have hTa : BddAbove T := by
    obtain ⟨U, hU⟩ := hSa
    refine ⟨U + E, ?_⟩
    intro x hx
    obtain ⟨y, hy, hnear⟩ := hTS x hx
    have hyU := hU hy
    rw [abs_le] at hnear
    linarith
  change |sInf S - sInf T| ≤ E ∧ |sSup S - sSup T| ≤ E
  exact ⟨abs_sInf_sub_sInf_le_of_mutually_near S T E hS hT hSb hTb hST hTS,
    abs_sSup_sub_sSup_le_of_mutually_near S T E hS hT hSa hTa hST hTS⟩

/-- Exact and mesh completed-world extrema have identical asymptotic lower and upper
limits because their Hausdorff error is bounded by `b / n`. -/
lemma BoundedSequence.completedExtrema_mesh_tendsto
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : BoundedSequence As P)
    (hvalued : WorldValued As DP)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n =>
        |completedAffineLow (fun i => (As i).meshAffine (i + 1)) P DP n -
          completedLow As P DP n|) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        |completedAffineHigh (fun i => (As i).meshAffine (i + 1)) P DP n -
          completedHigh As P DP n|) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun n : ℕ => (b : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_div_succ_atTop_nhds_zero (b : ℝ)
  constructor
  · apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
      (Eventually.of_forall fun n => ?_) hdiv
    refine (h.completedExtrema_mesh_near hvalued hP hworld n).1.trans ?_
    rw [div_eq_mul_inv, one_mul]
    exact mul_le_mul_of_nonneg_right (hshare n) (by positivity)
  · apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
      (Eventually.of_forall fun n => ?_) hdiv
    refine (h.completedExtrema_mesh_near hvalued hP hworld n).2.trans ?_
    rw [div_eq_mul_inv, one_mul]
    exact mul_le_mul_of_nonneg_right (hshare n) (by positivity)

/-! ## The affine master theorems on the diagonal mesh

The three affine master theorems applied to the literal diagonal threshold mesh.  The
remaining expectation-specific step is `lem:mesh`, which replaces fixed precision `n` at
future market days by each future day's own precision. -/

/-- Affine preemptive learning (`thm:affpolymax`) applied to the diagonal threshold mesh:
the market's diagonal mesh price has the same lower and upper limits as the mesh's own
future-day extrema.  This is the form `exppolymax` consumes, before `lem:mesh` replaces
the fixed precision `n` at future market days by each future day's own precision. -/
theorem BoundedSequence.mesh_affpolymax
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (fun n => (As n).expect P n) atTop =
        liminf (affineFutureHigh (fun n => (As n).meshAffine (n + 1)) P) atTop ∧
      limsup (fun n => (As n).expect P n) atTop =
        limsup (affineFutureLow (fun n => (As n).meshAffine (n + 1)) P) atTop := by
  simpa only [meshAffine_price_diagonal] using
    h.affineBCS.affpolymax DP hworld

/-- Persistence of affine knowledge (`thm:peraffkno`) on the diagonal threshold mesh: the
mesh's future-day extrema and its limiting-belief value share their lower and upper
limits.  This is the form `perexpkno` consumes. -/
lemma BoundedSequence.mesh_peraffkno
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (affineFutureLow (fun n => (As n).meshAffine (n + 1)) P) atTop =
        liminf (fun n => ((As n).meshAffine (n + 1)).value P (limitingBelief P)) atTop ∧
      limsup (affineFutureHigh (fun n => (As n).meshAffine (n + 1)) P) atTop =
        limsup (fun n => ((As n).meshAffine (n + 1)).value P (limitingBelief P)) atTop :=
  h.poly.mesh_poly.peraffkno P DP
    (h.mesh_boundedPrices
      (fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ))
    h.mesh_magnitudeBounded hworld

/-- Affine coherence (`thm:affcoh`) on the diagonal threshold mesh: the mesh's
completed-world extrema sandwich its limiting-belief value, which in turn sandwiches the
market's diagonal price.  This is the form `expcoh` consumes. -/
lemma BoundedSequence.mesh_affcoh
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (liminf (completedAffineLow (fun n => (As n).meshAffine (n + 1)) P DP) atTop ≤
        liminf (fun n => ((As n).meshAffine (n + 1)).value P (limitingBelief P)) atTop ∧
      liminf (fun n => ((As n).meshAffine (n + 1)).value P (limitingBelief P)) atTop ≤
        liminf (fun n => (As n).expect P n) atTop) ∧
      (limsup (fun n => (As n).expect P n) atTop ≤
          limsup (fun n => ((As n).meshAffine (n + 1)).value P (limitingBelief P)) atTop ∧
        limsup (fun n => ((As n).meshAffine (n + 1)).value P (limitingBelief P)) atTop ≤
          limsup (completedAffineHigh (fun n => (As n).meshAffine (n + 1)) P DP) atTop) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  simpa only [meshAffine_price_diagonal] using
    h.poly.mesh_poly.affcoh P DP (h.mesh_boundedPrices hP) h.mesh_magnitudeBounded
      hworld

/-! ## The expectation theorems -/

/-- `thm:exppolymax`: the market's diagonal expectation has the same lower/upper
limits as the corresponding future-day expectation extrema.  The only operational
boundary is the concrete mesh-softmax compiler certificate used by `lem:mesh`.
Paper node: `thm:exppolymax` -/
theorem BoundedSequence.exppolymax
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (b : ℚ) (hb : 0 ≤ (b : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (fun n => (As n).expect P n) atTop =
        liminf (futureHigh As P) atTop ∧
      limsup (fun n => (As n).expect P n) atTop =
        limsup (futureLow As P) atTop := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  have hmesh := h.mesh_independence ops hvalued b hb hshare hworld
  have hhighNear : Tendsto (fun n =>
      |affineFutureHigh (fun i => (As i).meshAffine (i + 1)) P n - futureHigh As P n|)
      atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _)
      (fun n => h.futureHigh_mesh_near hP n) hmesh
  have hlowNear : Tendsto (fun n =>
      |affineFutureLow (fun i => (As i).meshAffine (i + 1)) P n - futureLow As P n|)
      atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _)
      (fun n => h.futureLow_mesh_near hP n) hmesh
  obtain ⟨hhlo, hhhi, hllo, hlhi⟩ := h.futureExtrema_filterBounds hP
  have hhighLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (affineFutureHigh (fun i => (As i).meshAffine (i + 1)) P)
    (futureHigh As P) hhlo hhhi hhighNear
  have hlowLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (affineFutureLow (fun i => (As i).meshAffine (i + 1)) P)
    (futureLow As P) hllo hlhi hlowNear
  have haff := h.mesh_affpolymax DP hworld
  exact ⟨haff.1.trans hhighLimits.1, haff.2.trans hlowLimits.2⟩

/-- `exppolymax` with the rational share bound obtained from the `BoundedSequence` itself
(`exists_rat_shareBound`) rather than asked of the client. -/
lemma BoundedSequence.exppolymax_ofBounded
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (fun n => (As n).expect P n) atTop =
        liminf (futureHigh As P) atTop ∧
      limsup (fun n => (As n).expect P n) atTop =
        limsup (futureLow As P) atTop := by
  obtain ⟨b, hb, hshare⟩ := h.exists_rat_shareBound
  exact h.exppolymax ops hvalued b hb hshare hworld

/-- `thm:perexpkno`: persistence of expectation knowledge for represented bounded
LUV-combination sequences.
Paper node: `thm:perexpkno` -/
theorem BoundedSequence.perexpkno
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (hcode : ∀ n p, p ∈ (As n).terms → p.2.RpnThresholdCodes)
    (b : ℚ) (hb : 0 ≤ (b : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (futureLow As P) atTop =
        liminf (fun n => (As n).expectInf P) atTop ∧
      limsup (futureHigh As P) atTop =
        limsup (fun n => (As n).expectInf P) atTop := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let Ms : ℕ → AffineCombination := fun n => (As n).meshAffine (n + 1)
  let Mlim : ℕ → ℝ := fun n => (Ms n).value P (limitingBelief P)
  have hmesh := h.mesh_independence ops hvalued b hb hshare hworld
  have hlowNear : Tendsto (fun n =>
      |futureLow As P n - affineFutureLow Ms P n|) atTop (𝓝 0) := by
    simpa only [abs_sub_comm] using squeeze_zero (fun n => abs_nonneg _)
      (fun n => h.futureLow_mesh_near hP n) hmesh
  have hhighNear : Tendsto (fun n =>
      |futureHigh As P n - affineFutureHigh Ms P n|) atTop (𝓝 0) := by
    simpa only [abs_sub_comm] using squeeze_zero (fun n => abs_nonneg _)
      (fun n => h.futureHigh_mesh_near hP n) hmesh
  obtain ⟨_, _, hhlo, hhhi, hllo, hlhi⟩ := (h.mesh_boundedPrices hP).filterBounds
  have hlowLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (futureLow As P) (affineFutureLow Ms P) hllo hlhi hlowNear
  have hhighLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (futureHigh As P) (affineFutureHigh Ms P) hhlo hhhi hhighNear
  have hlimNear : Tendsto (fun n => |(As n).expectInf P - Mlim n|)
      atTop (𝓝 0) := by
    simpa only [Mlim, Ms, abs_sub_comm] using
      h.limexpapprox ops hvalued hcode b hb hshare hworld
  obtain ⟨hmlLo, hmlHi⟩ :=
    AffineCombination.BoundedAffinePrices.limitingValue_filterBounds
      (h.mesh_boundedPrices hP) DP hworld
  have hlimLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (fun n => (As n).expectInf P) Mlim hmlLo hmlHi hlimNear
  have hper := h.mesh_peraffkno DP hworld
  change liminf (futureLow As P) atTop =
      liminf (fun n => (As n).expectInf P) atTop ∧
    limsup (futureHigh As P) atTop =
      limsup (fun n => (As n).expectInf P) atTop
  exact ⟨hlowLimits.1.trans (hper.1.trans hlimLimits.1.symm),
    hhighLimits.2.trans (hper.2.trans hlimLimits.2.symm)⟩

/-- `perexpkno` with the rational share bound obtained from the `BoundedSequence` itself
(`exists_rat_shareBound`) rather than asked of the client. -/
lemma BoundedSequence.perexpkno_ofBounded
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (hcode : ∀ n p, p ∈ (As n).terms → p.2.RpnThresholdCodes)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (futureLow As P) atTop =
        liminf (fun n => (As n).expectInf P) atTop ∧
      limsup (futureHigh As P) atTop =
        limsup (fun n => (As n).expectInf P) atTop := by
  obtain ⟨b, hb, hshare⟩ := h.exists_rat_shareBound
  exact h.perexpkno ops hvalued hcode b hb hshare hworld

/-- `thm:expcoh`: exact completed-world LUV values bound the true limiting expectation,
which in turn coheres with the market's diagonal expectations.
Paper node: `thm:expcoh` -/
theorem BoundedSequence.expcoh
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (hcode : ∀ n p, p ∈ (As n).terms → p.2.RpnThresholdCodes)
    (b : ℚ) (hb : 0 ≤ (b : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (liminf (completedLow As P DP) atTop ≤
        liminf (fun n => (As n).expectInf P) atTop ∧
      liminf (fun n => (As n).expectInf P) atTop ≤
        liminf (fun n => (As n).expect P n) atTop) ∧
      (limsup (fun n => (As n).expect P n) atTop ≤
          limsup (fun n => (As n).expectInf P) atTop ∧
        limsup (fun n => (As n).expectInf P) atTop ≤
          limsup (completedHigh As P DP) atTop) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let Ms : ℕ → AffineCombination := fun n => (As n).meshAffine (n + 1)
  let Mlim : ℕ → ℝ := fun n => (Ms n).value P (limitingBelief P)
  have hcompNear := h.completedExtrema_mesh_tendsto hvalued b hshare hP hworld
  obtain ⟨hallo, halhi, hahlo, hahhi⟩ :=
    h.poly.mesh_poly.completedAffineExtrema_filterBounds P DP
      (h.mesh_boundedPrices hP) h.mesh_magnitudeBounded hP hworld
  have hlowLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (completedLow As P DP) (completedAffineLow Ms P DP) hallo halhi (by
      simpa only [Ms, abs_sub_comm] using hcompNear.1)
  have hhighLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (completedHigh As P DP) (completedAffineHigh Ms P DP) hahlo hahhi (by
      simpa only [Ms, abs_sub_comm] using hcompNear.2)
  have hlimNear : Tendsto (fun n => |(As n).expectInf P - Mlim n|)
      atTop (𝓝 0) := by
    simpa only [Mlim, Ms, abs_sub_comm] using
      h.limexpapprox ops hvalued hcode b hb hshare hworld
  obtain ⟨hmlLo, hmlHi⟩ :=
    AffineCombination.BoundedAffinePrices.limitingValue_filterBounds
      (h.mesh_boundedPrices hP) DP hworld
  have hlimLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (fun n => (As n).expectInf P) Mlim hmlLo hmlHi hlimNear
  have haff := h.mesh_affcoh DP hworld
  change (liminf (completedLow As P DP) atTop ≤
      liminf (fun n => (As n).expectInf P) atTop ∧
    liminf (fun n => (As n).expectInf P) atTop ≤
      liminf (fun n => (As n).expect P n) atTop) ∧
    (limsup (fun n => (As n).expect P n) atTop ≤
      limsup (fun n => (As n).expectInf P) atTop ∧
    limsup (fun n => (As n).expectInf P) atTop ≤
      limsup (completedHigh As P DP) atTop)
  constructor
  · constructor
    · calc
        liminf (completedLow As P DP) atTop =
            liminf (completedAffineLow Ms P DP) atTop := hlowLimits.1
        _ ≤ liminf Mlim atTop := haff.1.1
        _ = liminf (fun n => (As n).expectInf P) atTop := hlimLimits.1.symm
    · calc
        liminf (fun n => (As n).expectInf P) atTop =
            liminf Mlim atTop := hlimLimits.1
        _ ≤ liminf (fun n => (As n).expect P n) atTop := haff.1.2
  · constructor
    · calc
        limsup (fun n => (As n).expect P n) atTop ≤ limsup Mlim atTop := haff.2.1
        _ = limsup (fun n => (As n).expectInf P) atTop := hlimLimits.2.symm
    · calc
        limsup (fun n => (As n).expectInf P) atTop =
            limsup Mlim atTop := hlimLimits.2
        _ ≤ limsup (completedAffineHigh Ms P DP) atTop := haff.2.2
        _ = limsup (completedHigh As P DP) atTop := hhighLimits.2.symm

/-- `expcoh` with the rational share bound obtained from the `BoundedSequence` itself
(`exists_rat_shareBound`) rather than asked of the client. -/
lemma BoundedSequence.expcoh_ofBounded
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (hcode : ∀ n p, p ∈ (As n).terms → p.2.RpnThresholdCodes)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (liminf (completedLow As P DP) atTop ≤
        liminf (fun n => (As n).expectInf P) atTop ∧
      liminf (fun n => (As n).expectInf P) atTop ≤
        liminf (fun n => (As n).expect P n) atTop) ∧
      (limsup (fun n => (As n).expect P n) atTop ≤
          limsup (fun n => (As n).expectInf P) atTop ∧
        limsup (fun n => (As n).expectInf P) atTop ≤
          limsup (completedHigh As P DP) atTop) := by
  obtain ⟨b, hb, hshare⟩ := h.exists_rat_shareBound
  exact h.expcoh ops hvalued hcode b hb hshare hworld

/-! ## Statistical expectation lifts -/

end LUVCombination

/-- Splitting a null perturbation off an inclusive weighted average: eventually the
average of `y` is the average of `x` plus the average of `y - x`, and that correction is
below `ε / 2`.  This is everything the two sign directions of
`congr_of_sub_tendsto_zero` share. -/
private lemma weightedAverage_split_of_sub_tendsto_zero
    {w x y : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n)
    (hdiv : Tendsto (prefixSum w) atTop atTop)
    (hpos : ∀ᶠ n in atTop, 0 < prefixSum w n)
    (hsub : Tendsto (fun n => y n - x n) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      weightedAverage w y n =
          weightedAverage w x n + weightedAverage w (fun i => y i - x i) n ∧
        |weightedAverage w (fun i => y i - x i) n| < ε / 2 := by
  have havg : Tendsto (weightedAverage w (fun i => y i - x i)) atTop (𝓝 0) :=
    LUVCombination.weightedAverage_tendsto_zero_of_tendsto_zero hw0 hdiv hsub
  have herr : ∀ᶠ n in atTop, |weightedAverage w (fun i => y i - x i) n| < ε / 2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 havg (ε / 2) (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    simpa only [Real.dist_eq, sub_zero] using hN n hn
  filter_upwards [herr, hpos] with n he hnpos
  refine ⟨?_, he⟩
  rw [← weightedAverage_add w x (fun i => y i - x i) (ne_of_gt hnpos)]
  congr 1
  funext i
  ring

namespace PseudorandomAbove

/-- A pointwise null perturbation is invisible to every legal divergent weighted
average, so it preserves pseudorandom nonnegativity. -/
lemma congr_of_sub_tendsto_zero
    {x y : ℕ → ℝ} {f : DeferralFunction} {P : History}
    (hx : PseudorandomAbove x f P)
    (hsub : Tendsto (fun n => y n - x n) atTop (𝓝 0)) :
    PseudorandomAbove y f P := by
  intro W hWgen hWdiv hpatient ε hε
  filter_upwards [hx W hWgen hWdiv hpatient (ε / 2) (half_pos hε),
    weightedAverage_split_of_sub_tendsto_zero (w := fun i => (W i).denote P)
      (fun n => (hWdiv.1 n).1) hWdiv.2 hWdiv.eventually_prefixSum_pos hsub hε]
    with n hn hsplit
  rw [hsplit.1]
  linarith [neg_abs_le
    (weightedAverage (fun i => (W i).denote P) (fun i => y i - x i) n), hsplit.2]

end PseudorandomAbove

namespace PseudorandomBelow

/-- The corresponding null-perturbation transfer for pseudorandom nonpositivity. -/
lemma congr_of_sub_tendsto_zero
    {x y : ℕ → ℝ} {f : DeferralFunction} {P : History}
    (hx : PseudorandomBelow x f P)
    (hsub : Tendsto (fun n => y n - x n) atTop (𝓝 0)) :
    PseudorandomBelow y f P := by
  intro W hWgen hWdiv hpatient ε hε
  filter_upwards [hx W hWgen hWdiv hpatient (ε / 2) (half_pos hε),
    weightedAverage_split_of_sub_tendsto_zero (w := fun i => (W i).denote P)
      (fun n => (hWdiv.1 n).1) hWdiv.2 hWdiv.eventually_prefixSum_pos hsub hε]
    with n hn hsplit
  rw [hsplit.1]
  linarith [le_abs_self
    (weightedAverage (fun i => (W i).denote P) (fun i => y i - x i) n), hsplit.2]

end PseudorandomBelow

namespace LUVCombination

/-- The mesh truth stream differs from the rescaled LUV truth by a null sequence: this is
`meshTheoryTruth_sub_truth_tendsto` scaled by `meshNormScale b`, and it is the
perturbation the two pseudorandomness transfers below absorb. -/
private lemma WorldValued.normalizedMeshTruth_sub_scaled_tendsto
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ)) :
    Tendsto (fun n => normalizedMeshTruth As P DP hworld b n -
      ((meshNormScale b : ℚ) : ℝ) * truth n) atTop (𝓝 0) := by
  have herr := (h.meshTheoryTruth_sub_truth_tendsto hdet hworld b hshare).const_mul
    ((meshNormScale b : ℚ) : ℝ)
  simpa only [normalizedMeshTruth, mul_sub, mul_zero] using herr

/-- Exact LUV truth pseudorandomness transfers to the normalized threshold mesh used by
the affine statistical hubs. -/
lemma WorldValued.normalizedMeshTruth_pseudorandomAbove
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {f : DeferralFunction} (hpseudo : PseudorandomAbove truth f P) :
    PseudorandomAbove (normalizedMeshTruth As P DP hworld b) f P :=
  PseudorandomAbove.congr_of_sub_tendsto_zero
    (hpseudo.const_mul_pos (meshNormScale_pos b))
    (h.normalizedMeshTruth_sub_scaled_tendsto hdet hworld b hshare)

/-- The nonpositive direction of the same transfer. -/
lemma WorldValued.normalizedMeshTruth_pseudorandomBelow
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {f : DeferralFunction} (hpseudo : PseudorandomBelow truth f P) :
    PseudorandomBelow (normalizedMeshTruth As P DP hworld b) f P :=
  PseudorandomBelow.congr_of_sub_tendsto_zero
    (hpseudo.const_mul_pos (meshNormScale_pos b))
    (h.normalizedMeshTruth_sub_scaled_tendsto hdet hworld b hshare)

/-- `thm:recurringunbiasednessexp`: determined LUV-combination truth is recurrently
unbiased under every represented divergent weighting.  The two verifier premises are
the same conclusion-free historical-maturity boundaries exposed by `recunbiasedaff`,
instantiated on the concretely normalized threshold mesh.

Determination is the paper's `def:affthmval` premise on the *combination*; `hvalued` only
asks that each completed world value the component LUVs somehow.  The mesh they trade is
therefore only approximately determined, and the bias-run economics absorbs the
(negligible-against-magnitude) mesh error.

*One printed premise is deliberately dropped.*  The printed
`thm:recurringunbiasednessexp` (tex:1812-1820) additionally asks that the support of `w`
lie in the image of `f` — a clause referring to a deferral function the statement never
introduces.  It is a transposition: the clause belongs on `thm:wubexp` (tex:1822-1832),
where the affine twins place it (`thm:wubaff` has it, `thm:recurringunbiasedness` does
not), and it is carried there, on `wubexp`'s `hsupport`.  This endpoint therefore takes a
bare generable divergent weighting, with no deferral function at all.  Recorded as `PE2`
in `notes/paper-errata.md`.

The rational share bound `b` occurs in the *types* of `hverify` and `hverifyNeg`, through
`normalizedMesh As b`, so there is no `_ofBounded` form of this statement: a client has
to choose `b` (`BoundedSequence.exists_rat_shareBound` supplies one) before it can even
state the verifier premises. -/
theorem BoundedSequence.recurringunbiasednessexp_of_historicalVerifiers
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hvalued : WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hverify : AffineCombination.BiasRunHistoricallyVerifiable
      (normalizedMesh As b) (h.normalizedMesh_poly b) W hWgen P DP)
    (hverifyNeg : AffineCombination.BiasRunHistoricallyVerifiable
      (fun n => (normalizedMesh As b n).neg)
      (h.normalizedMesh_poly b).neg W hWgen P DP) :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote P)
        (fun i => (As i).expect P i) truth) 0 := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let w : ℕ → ℝ := fun i => (W i).denote P
  let market : ℕ → ℝ := fun i => (As i).expect P i
  let meshTruth : ℕ → ℝ := meshTheoryTruth As P DP hworld
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hq : q ≠ 0 := ne_of_gt (meshNormScale_pos b)
  have haff := (hvalued.normalizedMesh_approxDetermined hdet hworld
      b).recunbiasedaff_of_historicalVerifiers
    (h.normalizedMesh_poly b) hWgen (normalizedMesh_errorNegligible As P b) hWdiv
      (normalizedMesh_magnitude_le_one b hshare) hworld hverify hverifyNeg
  have hscaled : HasLimitPoint
      (fun n => q * weightedBias w market meshTruth n) 0 := by
    have haff' : HasLimitPoint
        (weightedBias w (fun i => q * market i) (fun i => q * meshTruth i)) 0 := by
      have h1 : (fun i => q * market i) =
          fun i => (normalizedMesh As b i).price P i := by
        funext i
        simp [normalizedMesh, market, q, AffineCombination.scale_price,
          EF.denote_const, meshAffine_price_diagonal]
      have h2 : (fun i => q * meshTruth i) =
          normalizedMeshTruth As P DP hworld b := rfl
      rw [h1, h2]
      exact haff
    have heq : weightedBias w (fun i => q * market i) (fun i => q * meshTruth i) =
        fun n => q * weightedBias w market meshTruth n := by
      funext n
      exact weightedBias_const_mul w market meshTruth q n
    rwa [heq] at haff'
  have hmeshBias : HasLimitPoint (weightedBias w market meshTruth) 0 :=
    hasLimitPoint_zero_of_const_mul hq hscaled
  let d : ℕ → ℝ := fun n => weightedAverage w (fun i => meshTruth i - truth i) n
  have herr : Tendsto (fun n => meshTruth n - truth n) atTop (𝓝 0) := by
    simpa only [meshTruth] using
      hvalued.meshTheoryTruth_sub_truth_tendsto hdet hworld b hshare
  have hd : Tendsto d atTop (𝓝 0) := by
    exact weightedAverage_tendsto_zero_of_tendsto_zero
      (fun n => (hWdiv.1 n).1) hWdiv.2 herr
  have hsum : HasLimitPoint (fun n => weightedBias w market meshTruth n + d n) 0 :=
    hasLimitPoint_add_tendsto_zero hmeshBias hd
  apply hsum.congrFun
  filter_upwards [hWdiv.eventually_prefixSum_pos] with n hn
  dsimp only [d]
  rw [weightedBias, weightedBias]
  rw [← weightedAverage_add w (fun i => market i - meshTruth i)
    (fun i => meshTruth i - truth i) (ne_of_gt hn)]
  congr 1
  funext i
  ring

/-- `thm:wubexp`: determined LUV-combination truth is weighted-unbiased under
every represented divergent weighting supported on a strictly increasing feedback
schedule.  The two operational premises are the ones `lic_wubaff` takes, instantiated on
the normalized threshold mesh: `emit` supplies the concrete feedback-trader family in
both sign orientations, and `bridge` supplies the delayed-quote-error affine sequence
that every completed-theory world values at zero.  Neither carries a bias or convergence
claim.

Determination is the paper's own `def:affthmval` premise — all completed worlds agree on
the value of the *combination*.  `hvalued` only asks that each completed world value the
component LUVs somehow (paper LUVs always do, `W(X)` being a supremum); the components
are free to differ between worlds, so `Z = X + (1 - X)` is covered.

*One premise this statement carries is not printed at this node.*  `hsupport`
(`WeightingSupportedOnDeferralImage`: the support of `w` lies in the image of `f`) is
absent from the printed `thm:wubexp` (tex:1822-1832) and appears instead, spuriously, on
`thm:recurringunbiasednessexp` (tex:1812-1820) — whose statement never introduces a
deferral function `f` for it to refer to.  The affine twins settle the intended
placement: `thm:wubaff` (tex:1480-1490) carries the clause and
`thm:recurringunbiasedness` (tex:1225-1233) does not.  The clause belongs on the feedback
theorem, so it is stated here; the mirror half of the same correction is
`recurringunbiasednessexp_of_historicalVerifiers`, which drops it.  Recorded as `PE2` in
`notes/paper-errata.md`.

The rational share bound `b` occurs in the *types* of `emit` and `bridge`, through
`normalizedMesh As b`, so there is no `_ofBounded` form of this statement: a client has
to choose `b` (`BoundedSequence.exists_rat_shareBound` supplies one) before it can even
state the operational premises.
Paper node: `thm:wubexp` -/
theorem BoundedSequence.wubexp
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hvalued : WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    (hWdiv : DivergentWeighting W P)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (emit : AffineCombination.FeedbackTraderEmissionSigns
      (h.normalizedMesh_poly b) hWgen hstrict)
    (bridge : AffineCombination.FeedbackTruthSequence
      (normalizedMesh As b) (normalizedMeshTruth As P DP hworld b) P DP f) :
    weightedBias (fun i => (W i).denote P)
      (fun i => (As i).expect P i) truth ≈ₙ (fun _ => 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let w : ℕ → ℝ := fun i => (W i).denote P
  let market : ℕ → ℝ := fun i => (As i).expect P i
  let meshTruth : ℕ → ℝ := meshTheoryTruth As P DP hworld
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hq : q ≠ 0 := ne_of_gt (meshNormScale_pos b)
  have haff := AffineCombination.lic_wubaff
    (h.normalizedMesh_poly b) hWgen hstrict hsupport emit bridge hWdiv
      (normalizedMesh_magnitude_le_one b hshare) hworld
  have hscaled : (fun n => q * weightedBias w market meshTruth n) ≈ₙ
      (fun _ => 0) := by
    have haff' : weightedBias w (fun i => q * market i) (fun i => q * meshTruth i) ≈ₙ
        (fun _ => 0) := by
      have h1 : (fun i => q * market i) =
          fun i => (normalizedMesh As b i).price P i := by
        funext i
        simp [normalizedMesh, market, q, AffineCombination.scale_price,
          EF.denote_const, meshAffine_price_diagonal]
      have h2 : (fun i => q * meshTruth i) =
          normalizedMeshTruth As P DP hworld b := rfl
      rw [h1, h2]
      exact haff
    have heq : weightedBias w (fun i => q * market i) (fun i => q * meshTruth i) =
        fun n => q * weightedBias w market meshTruth n := by
      funext n
      exact weightedBias_const_mul w market meshTruth q n
    rwa [heq] at haff'
  have hscaledT : Tendsto (fun n => q * weightedBias w market meshTruth n)
      atTop (𝓝 0) := by
    simpa only [AsympEq, sub_zero] using hscaled
  have hmeshT : Tendsto (weightedBias w market meshTruth) atTop (𝓝 0) := by
    have hu := hscaledT.const_mul q⁻¹
    convert hu using 1 <;> simp [hq]
  let d : ℕ → ℝ := fun n => weightedAverage w (fun i => meshTruth i - truth i) n
  have herr : Tendsto (fun n => meshTruth n - truth n) atTop (𝓝 0) := by
    simpa only [meshTruth] using
      hvalued.meshTheoryTruth_sub_truth_tendsto hdet hworld b hshare
  have hd : Tendsto d atTop (𝓝 0) := by
    exact weightedAverage_tendsto_zero_of_tendsto_zero
      (fun n => (hWdiv.1 n).1) hWdiv.2 herr
  have hsum : Tendsto (fun n => weightedBias w market meshTruth n + d n)
      atTop (𝓝 0) := by
    simpa using hmeshT.add hd
  have hfinal : Tendsto (weightedBias w market truth) atTop (𝓝 0) := by
    apply hsum.congr'
    filter_upwards [hWdiv.eventually_prefixSum_pos] with n hn
    dsimp only [d]
    rw [weightedBias, weightedBias]
    rw [← weightedAverage_add w (fun i => market i - meshTruth i)
      (fun i => meshTruth i - truth i) (ne_of_gt hn)]
    congr 1
    funext i
    ring
  simpa only [AsympEq, sub_zero, w, market] using hfinal

/-- The nonnegative comparison direction of `thm:prandexp`, taking the bias-run
historical-verifiability premises for the normalized threshold mesh.

The rational share bound `b` occurs in the *types* of `clock`, `hverify` and `hverifyNeg`,
through `normalizedMesh As b`, so this statement and its two siblings have no `_ofBounded`
form: a client has to choose `b` (`BoundedSequence.exists_rat_shareBound` supplies one)
before it can state the premises. -/
theorem BoundedSequence.prandexp_of_historicalVerifiers
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hvalued : WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) {err : ℕ → ℝ}
    (clock : PatientSettlementClock (normalizedMesh As b) P DP
      (normalizedMeshTruth As P DP hworld b) err f)
    (hpseudo : PseudorandomAbove truth f P)
    (hverify : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (normalizedMesh As b) (h.normalizedMesh_poly b) W hWgen P DP)
    (hverifyNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => (normalizedMesh As b n).neg)
        (h.normalizedMesh_poly b).neg W hWgen P DP) :
    (fun n => (As n).expect P n) ≳ₙ (fun _ => 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hq : 0 < q := meshNormScale_pos b
  have hpseudoMesh := hvalued.normalizedMeshTruth_pseudorandomAbove
    hdet hworld b hshare hpseudo
  have haff :=
    AffineCombination.ApproxDeterminedViaTheory.lic_prandaff_above_of_historicalVerifiers
      (h.normalizedMesh_poly b) (hvalued.normalizedMesh_approxDetermined hdet hworld b)
      (normalizedMesh_errorNegligible As P b)
      (h.normalizedMesh_boundedPrices b hP)
      (normalizedMesh_magnitude_le_one b hshare) hworld f clock
      hpseudoMesh hverify hverifyNeg
  have hscaled : (fun n => q * (As n).expect P n) ≳ₙ (fun _ => 0) := by
    simpa only [q, normalizedMesh, AffineCombination.scale_price, EF.denote_const,
      meshAffine_price_diagonal] using haff
  exact asympGE_zero_of_const_mul_pos hq hscaled

/-- The nonpositive comparison direction of `thm:prandexp`. -/
theorem BoundedSequence.prandexp_below_of_historicalVerifiers
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hvalued : WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) {err : ℕ → ℝ}
    (clock : PatientSettlementClock (normalizedMesh As b) P DP
      (normalizedMeshTruth As P DP hworld b) err f)
    (hpseudo : PseudorandomBelow truth f P)
    (hverifyNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => (normalizedMesh As b n).neg)
        (h.normalizedMesh_poly b).neg W hWgen P DP)
    (hverifyNegNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => ((normalizedMesh As b n).neg).neg)
        (h.normalizedMesh_poly b).neg.neg W hWgen P DP) :
    (fun n => (As n).expect P n) ≲ₙ (fun _ => 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hq : 0 < q := meshNormScale_pos b
  have hpseudoMesh := hvalued.normalizedMeshTruth_pseudorandomBelow
    hdet hworld b hshare hpseudo
  have haff :=
    AffineCombination.ApproxDeterminedViaTheory.lic_prandaff_below_of_historicalVerifiers
      (h.normalizedMesh_poly b) (hvalued.normalizedMesh_approxDetermined hdet hworld b)
      (normalizedMesh_errorNegligible As P b)
      (h.normalizedMesh_boundedPrices b hP)
      (normalizedMesh_magnitude_le_one b hshare) hworld f clock
      hpseudoMesh hverifyNeg hverifyNegNeg
  have hscaled : (fun n => q * (As n).expect P n) ≲ₙ (fun _ => 0) := by
    simpa only [q, normalizedMesh, AffineCombination.scale_price, EF.denote_const,
      meshAffine_price_diagonal] using haff
  exact asympLE_zero_of_const_mul_pos hq hscaled

/-- The equality direction mentioned in the paper immediately after `thm:prandexp`. -/
theorem BoundedSequence.prandexp_eq_of_historicalVerifiers
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hvalued : WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) {err : ℕ → ℝ}
    (clock : PatientSettlementClock (normalizedMesh As b) P DP
      (normalizedMeshTruth As P DP hworld b) err f)
    (hpseudo : Pseudorandom truth f P)
    (hverify : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (normalizedMesh As b) (h.normalizedMesh_poly b) W hWgen P DP)
    (hverifyNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => (normalizedMesh As b n).neg)
        (h.normalizedMesh_poly b).neg W hWgen P DP)
    (hverifyNegNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => ((normalizedMesh As b n).neg).neg)
        (h.normalizedMesh_poly b).neg.neg W hWgen P DP) :
    (fun n => (As n).expect P n) ≈ₙ (fun _ => 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  rw [asympEq_iff_asympLE_asympGE]
  exact ⟨
    h.prandexp_below_of_historicalVerifiers hvalued hdet b hshare hworld f clock hpseudo.2
      hverifyNeg hverifyNegNeg,
    h.prandexp_of_historicalVerifiers hvalued hdet b hshare hworld f clock hpseudo.1
      hverify hverifyNeg⟩

end LUVCombination

end LogicalInduction
