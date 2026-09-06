import LogicalInduction.Construction.LUV.ArithmeticSource

/-!
# Exact literal products of paper LUVs

This module renders the **exact** product of two literal paper LUVs, the object that lets
`thm:ccee` be stated at zero slack.  The abstract threshold-only `LUV` interface can only
approximate a product — nothing in it names the two factors' values, so the product has to
be reconstructed from thresholds to within a mesh (`dd:mesh`).  A `PaperLUV` names its
value inside arithmetic by a numerator/denominator pair code, and arithmetic multiplies
pairs exactly.

Given literal LUVs `X` and `W`, the formula

```text
Z(q) := ∃ qx qw a b c d,
          X(qx) ∧ W(qw) ∧ qx = ⟪a,b⟫ ∧ qw = ⟪c,d⟫ ∧ q = ⟪a·c, b·d⟫
```

names the **unreduced** product code `(a·c)/(b·d)`.  No gcd normalisation is performed and
none is needed: a paper LUV's semantics is the rational cut of its thresholds, never its
code.

Objects defined: `paperProductPairing`, `paperProductFormula`,
`PaperLUV.paperProductPaperLUV`, the source presentation `paperProductSource`, and the
family `paperExactProductLUVSeq`.  The main results are
`paperProduct_threshold_provable` / `_refutable`, the two object-level `T`-derivations
obtained by completeness over models of `T`, and `paperProductPaperLUV_valuesAt`: in every
completed world of the canonical theorem process the product LUV is valued at exactly the
product of the factors' values, no mesh and no slack.

The product nests `exs` under `Rew.castLE` rather than using a flat six-binder prefix
because `castLE` is index preserving, so both symbol encoders and the source-token run are
literally unchanged and a factor family's `def:ec` certificate transports to the product
with no new emission induction (`ArithSource.castLE`, `Construction/LUV/ArithmeticSource.lean`).

The arithmetic caution, as a design fact: never form `p * s` as a rational inside a
derivation — `(p * s).num` is the *reduced* numerator, whereas the object-level code is
deliberately unreduced.  That is the shape `rat_cross_prod_le` / `_ge` are built around.
Both threshold directions are strict one-sided clauses because `ValuesAt` leaves the
threshold *at* the value undecided (`PCWorld.RationalCutAt`), so there is no biconditional
to prove at `r = x·c`.

Consumers: `Construction/Quotation/ExactCCEE.lean` (`paperExactProductLUVSeq`,
`paperProductPaperLUV_valuesAt`) and `Construction/Quotation/RepresentedWeight.lean`
(`natAbs_num_cast`);
`AxiomAudit.lean` inventories `paperProductPaperLUV`, `paperProductPaperLUV_valuesAt` and
`paperExactProductLUVSeq`.

*Proof kind:* `P`; hypotheses `(a)` throughout — the two threshold derivations are
genuine `T`-derivations obtained by completeness over models of `T`, not Lean-level side
conditions.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder.Arithmetic

/-! ## The product formula -/

/-- The pairing clause of the exact product, read in the arity-3 context the product
formula puts it in: `#0` is the `W`-witness, `#1` the `X`-witness, `#2` the product code.
The product of `a/b` and `c/d` is named by the *unreduced* pair `(a·c)/(b·d)`. -/
def paperProductPairing : ArithmeticSemisentence 3 :=
  “qw qx q. ∃ a, ∃ b, ∃ c, ∃ d,
     !pairDef qx a b ∧ !pairDef qw c d ∧ !pairDef q (a * c) (b * d)”

/-- The exact product of two literal paper-LUV formulas.  The two factor formulas occur
only under `Rew.castLE`, which is index-preserving, so the emitted symbol run of the
product is the two factors' runs plus a fixed constant prefix — that is what keeps the
sequence layer's `def:ec` certificate cheap. -/
def paperProductFormula (Xf Wf : ArithmeticSemisentence 1) : ArithmeticSemisentence 1 :=
  ∃⁰ ((Rew.castLE (by omega) ▹ Xf) ⋏
    (∃⁰ ((Rew.castLE (by omega) ▹ Wf) ⋏ paperProductPairing)))

/-- The intended reading of the product formula in any model. -/
lemma paperProductFormula_eval {M : Type} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (Xf Wf : ArithmeticSemisentence 1) (q : M) :
    Semiformula.Eval ![q] Empty.elim (paperProductFormula Xf Wf) ↔
      ∃ a b, Semiformula.Eval ![pair a b] Empty.elim Xf ∧
        ∃ c d, Semiformula.Eval ![pair c d] Empty.elim Wf ∧ q = pair (a * c) (b * d) := by
  simp [paperProductFormula, paperProductPairing, pairDef, ← pair_graph,
    Matrix.constant_eq_singleton]

/-! ## The rational cross-multiplication facts

Both threshold derivations need one arithmetic fact each, and both are facts about `ℚ`
rather than about the model: the model side only ever sees them cast in.  **Never form
`p * s` as a rational inside a derivation** — `(p * s).num` is the *reduced* numerator and
is not `p.num * s.num`, whereas the object-level code is deliberately unreduced. -/

/-- A nonnegative rational's numerator, read through `Int.natAbs`, is the rational scaled
by its denominator.  Shared by the product derivations here and by the literal
representation of the deferred weight (`Construction/Quotation/RepresentedWeight.lean`). -/
lemma natAbs_num_cast {t : ℚ} (ht : 0 ≤ t) :
    ((t.num.natAbs : ℚ)) = t * (t.den : ℚ) := by
  have hnum : (0 : ℤ) ≤ t.num := Rat.num_nonneg.mpr ht
  have h1 : ((t.num.natAbs : ℚ)) = (t.num : ℚ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hnum]
  have hd : ((t.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr t.den_nz
  rw [h1]
  exact (div_eq_iff hd).mp (Rat.num_div_den t)

/-- If `r ≤ p·s` then the unreduced cross-multiplication holds between `r` and the
unreduced product code of `p` and `s`. -/
private lemma rat_cross_prod_le {p s r : ℚ} (hp : 0 ≤ p) (hs : 0 ≤ s) (hr : 0 ≤ r)
    (h : r ≤ p * s) :
    r.num.natAbs * (p.den * s.den) ≤ (p.num.natAbs * s.num.natAbs) * r.den := by
  have key : ((r.num.natAbs : ℚ)) * ((p.den : ℚ) * (s.den : ℚ)) ≤
      ((p.num.natAbs : ℚ) * (s.num.natAbs : ℚ)) * (r.den : ℚ) := by
    rw [natAbs_num_cast hp, natAbs_num_cast hs, natAbs_num_cast hr]
    have hpos : (0 : ℚ) < (r.den : ℚ) * ((p.den : ℚ) * (s.den : ℚ)) := by
      have := r.den_pos; have := p.den_pos; have := s.den_pos
      positivity
    calc r * (r.den : ℚ) * ((p.den : ℚ) * (s.den : ℚ))
        = r * ((r.den : ℚ) * ((p.den : ℚ) * (s.den : ℚ))) := by ring
      _ ≤ (p * s) * ((r.den : ℚ) * ((p.den : ℚ) * (s.den : ℚ))) :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = p * (p.den : ℚ) * (s * (s.den : ℚ)) * (r.den : ℚ) := by ring
  exact_mod_cast key

/-- If `p·s ≤ r` then the unreduced cross-multiplication holds in the other direction. -/
private lemma rat_cross_prod_ge {p s r : ℚ} (hp : 0 ≤ p) (hs : 0 ≤ s)
    (h : p * s ≤ r) :
    (p.num.natAbs * s.num.natAbs) * r.den ≤ r.num.natAbs * (p.den * s.den) := by
  have hr : 0 ≤ r := le_trans (mul_nonneg hp hs) h
  have key : ((p.num.natAbs : ℚ) * (s.num.natAbs : ℚ)) * (r.den : ℚ) ≤
      ((r.num.natAbs : ℚ)) * ((p.den : ℚ) * (s.den : ℚ)) := by
    rw [natAbs_num_cast hp, natAbs_num_cast hs, natAbs_num_cast hr]
    have hpos : (0 : ℚ) < (r.den : ℚ) * ((p.den : ℚ) * (s.den : ℚ)) := by
      have := r.den_pos; have := p.den_pos; have := s.den_pos
      positivity
    calc p * (p.den : ℚ) * (s * (s.den : ℚ)) * (r.den : ℚ)
        = (p * s) * ((r.den : ℚ) * ((p.den : ℚ) * (s.den : ℚ))) := by ring
      _ ≤ r * ((r.den : ℚ) * ((p.den : ℚ) * (s.den : ℚ))) :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = r * (r.den : ℚ) * ((p.den : ℚ) * (s.den : ℚ)) := by ring
  exact_mod_cast key

/-! ## The model-side cross-multiplication chains

Both chains live in an arbitrary model of `T`, whose arithmetic is an ordered commutative
semiring with no subtraction, so everything is arranged as products of nonnegative terms.
The rational data enters only as the cast `ℕ`-level cross-multiplication `hcross`. -/

private lemma prod_cross_lt {M : Type} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] {P Pd S Sd R Rd : ℕ} {a b c d : M}
    (hX : (P : M) * b < a * (Pd : M)) (hW : (S : M) * d < c * (Sd : M))
    (hRd : 0 < Rd)
    (hcross : R * (Pd * Sd) ≤ (P * S) * Rd) :
    (R : M) * (b * d) < (a * c) * (Rd : M) := by
  have hRd' : (0 : M) < (Rd : M) := by exact_mod_cast hRd
  have hapos : (0 : M) < a * (Pd : M) :=
    lt_of_le_of_lt (LO.FirstOrder.Arithmetic.zero_le _) hX
  have h3 : ((P : M) * (S : M)) * (b * d) < (a * c) * ((Pd : M) * (Sd : M)) := calc
    ((P : M) * (S : M)) * (b * d) = ((P : M) * b) * ((S : M) * d) := by ac_rfl
    _ ≤ (a * (Pd : M)) * ((S : M) * d) :=
        mul_le_mul_of_nonneg_right hX.le (LO.FirstOrder.Arithmetic.zero_le _)
    _ < (a * (Pd : M)) * (c * (Sd : M)) := mul_lt_mul_of_pos_left hW hapos
    _ = (a * c) * ((Pd : M) * (Sd : M)) := by ac_rfl
  have hcross' : (R : M) * ((Pd : M) * (Sd : M)) ≤ ((P : M) * (S : M)) * (Rd : M) := by
    exact_mod_cast hcross
  have hchain : ((R : M) * (b * d)) * ((Pd : M) * (Sd : M)) <
      ((a * c) * (Rd : M)) * ((Pd : M) * (Sd : M)) := calc
    ((R : M) * (b * d)) * ((Pd : M) * (Sd : M))
        = ((R : M) * ((Pd : M) * (Sd : M))) * (b * d) := by ac_rfl
    _ ≤ (((P : M) * (S : M)) * (Rd : M)) * (b * d) :=
        mul_le_mul_of_nonneg_right hcross' (LO.FirstOrder.Arithmetic.zero_le _)
    _ = (((P : M) * (S : M)) * (b * d)) * (Rd : M) := by ac_rfl
    _ < ((a * c) * ((Pd : M) * (Sd : M))) * (Rd : M) := mul_lt_mul_of_pos_right h3 hRd'
    _ = ((a * c) * (Rd : M)) * ((Pd : M) * (Sd : M)) := by ac_rfl
  exact lt_of_mul_lt_mul_right hchain (LO.FirstOrder.Arithmetic.zero_le _)

private lemma prod_cross_le {M : Type} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] {P Pd S Sd R Rd : ℕ} {a b c d : M}
    (hX : a * (Pd : M) ≤ (P : M) * b) (hW : c * (Sd : M) ≤ (S : M) * d)
    (hPd : 0 < Pd) (hSd : 0 < Sd)
    (hcross : (P * S) * Rd ≤ R * (Pd * Sd)) :
    (a * c) * (Rd : M) ≤ (R : M) * (b * d) := by
  have hPd' : (0 : M) < (Pd : M) := by exact_mod_cast hPd
  have hSd' : (0 : M) < (Sd : M) := by exact_mod_cast hSd
  have hcross' : ((P : M) * (S : M)) * (Rd : M) ≤ (R : M) * ((Pd : M) * (Sd : M)) := by
    exact_mod_cast hcross
  have h3 : (a * c) * ((Pd : M) * (Sd : M)) ≤ ((P : M) * (S : M)) * (b * d) := calc
    (a * c) * ((Pd : M) * (Sd : M)) = (a * (Pd : M)) * (c * (Sd : M)) := by ac_rfl
    _ ≤ ((P : M) * b) * ((S : M) * d) :=
        mul_le_mul hX hW (LO.FirstOrder.Arithmetic.zero_le _)
          (LO.FirstOrder.Arithmetic.zero_le _)
    _ = ((P : M) * (S : M)) * (b * d) := by ac_rfl
  have hchain : ((a * c) * (Rd : M)) * ((Pd : M) * (Sd : M)) ≤
      ((R : M) * (b * d)) * ((Pd : M) * (Sd : M)) := calc
    ((a * c) * (Rd : M)) * ((Pd : M) * (Sd : M))
        = ((a * c) * ((Pd : M) * (Sd : M))) * (Rd : M) := by ac_rfl
    _ ≤ (((P : M) * (S : M)) * (b * d)) * (Rd : M) :=
        mul_le_mul_of_nonneg_right h3 (LO.FirstOrder.Arithmetic.zero_le _)
    _ = (((P : M) * (S : M)) * (Rd : M)) * (b * d) := by ac_rfl
    _ ≤ ((R : M) * ((Pd : M) * (Sd : M))) * (b * d) :=
        mul_le_mul_of_nonneg_right hcross' (LO.FirstOrder.Arithmetic.zero_le _)
    _ = ((R : M) * (b * d)) * ((Pd : M) * (Sd : M)) := by ac_rfl
  exact le_of_mul_le_mul_right hchain (mul_pos hPd' hSd')

/-! ## The exact product paper LUV -/

namespace PaperLUV

variable {T : ArithmeticTheory} [T.Δ₁]

/-- **The exact product of two literal paper LUVs.**  Uniqueness and unit-interval
membership are derived *in `T`*, by completeness over its models, from the corresponding
derivations for the two factors.  The value named is the unreduced pair `(a·c)/(b·d)`;
that is a different *code* from the reduced one, and deliberately so — a paper LUV's
semantics is the rational cut of its thresholds, never its code.
Kind `C`; hypotheses `(a)`.
Paper node: `def:luv` -/
def paperProductPaperLUV [𝗜𝚺₁ ⪯ T] (X W : PaperLUV T) : PaperLUV T where
  formula := paperProductFormula X.formula W.formula
  unique := by
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
      Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
      ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
    have hexX := models_of_provable hM X.unique
    have hunitX := models_of_provable hM X.unit
    have hexW := models_of_provable hM W.unique
    have hunitW := models_of_provable hM W.unit
    simp [models_iff, paperRatUnitDef] at hexX hunitX hexW hunitW
    simp [models_iff, paperProductFormula_eval]
    obtain ⟨qx, hqx, huqx⟩ := hexX
    obtain ⟨qw, hqw, huqw⟩ := hexW
    obtain ⟨a, b, hab, _, _⟩ := by simpa using hunitX qx hqx
    obtain ⟨c, d, hcd, _, _⟩ := by simpa using hunitW qw hqw
    subst hab; subst hcd
    refine ⟨pair (a * c) (b * d), ⟨a, b, hqx, c, d, hqw, rfl⟩, ?_⟩
    rintro q ⟨a', b', ha', c', d', hc', rfl⟩
    have h1 := huqx _ ha'
    have h2 := huqw _ hc'
    rw [pair_ext_iff] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    rfl
  unit := by
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
      Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
      ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
    have hunitX := models_of_provable hM X.unit
    have hunitW := models_of_provable hM W.unit
    simp [models_iff, paperRatUnitDef] at hunitX hunitW
    simp [models_iff, paperProductFormula_eval, paperRatUnitDef]
    rintro q a b ha c d hc rfl
    obtain ⟨a', b', hab, hb, hab'⟩ := hunitX _ ha
    obtain ⟨c', d', hcd, hd, hcd'⟩ := hunitW _ hc
    rw [pair_ext_iff] at hab hcd
    obtain ⟨rfl, rfl⟩ := hab
    obtain ⟨rfl, rfl⟩ := hcd
    exact ⟨a * c, b * d, rfl, mul_pos hb hd,
      mul_le_mul hab' hcd' (LO.FirstOrder.Arithmetic.zero_le _)
        (LO.FirstOrder.Arithmetic.zero_le _)⟩

/-- The defining formula of the product LUV is the product formula of the factors'
defining formulas — the field projection, in `simp` normal form. -/
@[simp] lemma paperProductPaperLUV_formula [𝗜𝚺₁ ⪯ T] (X W : PaperLUV T) :
    (paperProductPaperLUV X W).formula = paperProductFormula X.formula W.formula := rfl

/-- **The positive threshold derivation**: if `r ≤ p·s` then `T` proves
`X > p 🡒 (W > s 🡒 XW > r)`.  Obtained by completeness over models of `T`; the
cross-multiplication is on the *unreduced* product code. -/
lemma paperProduct_threshold_provable [𝗜𝚺₁ ⪯ T] (X W : PaperLUV T) {p s r : ℚ}
    (hp : 0 ≤ p) (hs : 0 ≤ s) (hr : r ≤ p * s) :
    T ⊢ (X.thresholdFormula p 🡒 (W.thresholdFormula s 🡒
      (paperProductPaperLUV X W).thresholdFormula r)) := by
  apply LO.FirstOrder.Arithmetic.complete T
  intro (M : Type) _ hM
  letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
    Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
    ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
  have hunitX := models_of_provable hM X.unit
  have hunitW := models_of_provable hM W.unit
  simp [models_iff, paperRatUnitDef] at hunitX hunitW
  simp only [models_iff, thresholdFormula, paperProductPaperLUV_formula]
  simp [paperProductFormula_eval, paperRatGtDef, not_lt.mpr hp, not_lt.mpr hs,
    LO.FirstOrder.Arithmetic.numeral_eq_natCast]
  intro hP hS q a b ha c d hc hq
  obtain ⟨a₁, b₁, hab, hb, hltp⟩ := hP _ ha
  obtain ⟨c₁, d₁, hcd, hd, hlts⟩ := hS _ hc
  rw [pair_ext_iff] at hab hcd
  obtain ⟨rfl, rfl⟩ := hab
  obtain ⟨rfl, rfl⟩ := hcd
  subst hq
  by_cases hr0 : r < 0
  · simp [hr0, paperRatDef, pairDef, ← pair_graph]
    exact ⟨hb, hd⟩
  · have hr0' : 0 ≤ r := not_lt.mp hr0
    simp [hr0, pairDef, ← pair_graph, LO.FirstOrder.Arithmetic.numeral_eq_natCast]
    exact ⟨⟨hb, hd⟩,
      prod_cross_lt hltp hlts r.den_pos (rat_cross_prod_le hp hs hr0' hr)⟩

/-- **The refutation dual**: if `p·s ≤ r` then `T` proves
`∼(X > p) 🡒 (∼(W > s) 🡒 ∼(XW > r))`.  Same route, same unreduced codes. -/
lemma paperProduct_threshold_refutable [𝗜𝚺₁ ⪯ T] (X W : PaperLUV T) {p s r : ℚ}
    (hp : 0 ≤ p) (hs : 0 ≤ s) (hr : p * s ≤ r) :
    T ⊢ (∼X.thresholdFormula p 🡒 (∼W.thresholdFormula s 🡒
      ∼(paperProductPaperLUV X W).thresholdFormula r)) := by
  have hr0 : ¬ r < 0 := not_lt.mpr (le_trans (mul_nonneg hp hs) hr)
  apply LO.FirstOrder.Arithmetic.complete T
  intro (M : Type) _ hM
  letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
    Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
    ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
  have hunitX := models_of_provable hM X.unit
  have hunitW := models_of_provable hM W.unit
  simp [models_iff, paperRatUnitDef] at hunitX hunitW
  simp only [models_iff, thresholdFormula, paperProductPaperLUV_formula]
  simp [paperProductFormula_eval, paperRatGtDef, not_lt.mpr hp, not_lt.mpr hs, hr0,
    pairDef, ← pair_graph, LO.FirstOrder.Arithmetic.numeral_eq_natCast]
  intro qx hqx hnp qw hqw hns
  obtain ⟨a, b, hab, hb, -⟩ := hunitX _ hqx
  obtain ⟨c, d, hcd, hd, -⟩ := hunitW _ hqw
  subst hab
  subst hcd
  refine ⟨a, b, hqx, c, d, hqw, fun _ _ => ?_⟩
  exact prod_cross_le (hnp a b rfl hb) (hns c d rfl hd) p.den_pos s.den_pos
    (rat_cross_prod_ge hp hs hr)

/-! ## Exact completed-world semantics

The cut of the product is the product of the cuts.  Both directions are *strict*
one-sided clauses: `ValuesAt` deliberately leaves the threshold *at* the value undecided
(`PCWorld.RationalCutAt`), so there is no biconditional to prove at `r = x·c`. -/

/-- Below a strict product bound there are rational factors witnessing it. -/
private lemma exists_rat_factors_lt {x c : ℝ} {r : ℚ} (_hx : 0 ≤ x) (hc : 0 ≤ c)
    (hr : 0 ≤ r) (hlt : (r : ℝ) < x * c) :
    ∃ p s : ℚ, 0 ≤ p ∧ 0 ≤ s ∧ (p : ℝ) < x ∧ (s : ℝ) < c ∧ r ≤ p * s := by
  have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hxc : (0 : ℝ) < x * c := lt_of_le_of_lt hr' hlt
  have hc0 : (0 : ℝ) < c := by
    rcases hc.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hxc; simp at hxc
  have hδ : (0 : ℝ) < (x * c - r) / (2 * (c + 1)) := by
    apply div_pos (by linarith) (by linarith)
  obtain ⟨p, hp1, hp2⟩ :=
    exists_rat_btwn (show x - (x * c - r) / (2 * (c + 1)) < x by linarith)
  have hpc : (r : ℝ) < (p : ℝ) * c := by
    have h1 : (x - (x * c - r) / (2 * (c + 1))) * c ≤ (p : ℝ) * c :=
      mul_le_mul_of_nonneg_right hp1.le hc
    have h2 : (x * c - r) / (2 * (c + 1)) * c ≤ (x * c - r) / (2 * (c + 1)) * (c + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ.le
    have h3 : (x * c - r) / (2 * (c + 1)) * (c + 1) = (x * c - r) / 2 := by
      field_simp
    nlinarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by nlinarith
  have hlt2 : (r : ℝ) / (p : ℝ) < c := by rw [div_lt_iff₀ hp0]; linarith
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn hlt2
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := le_trans (by positivity) ht1.le
  have hps : (r : ℝ) ≤ (p : ℝ) * (t : ℝ) := by
    rw [div_lt_iff₀ hp0] at ht1
    nlinarith
  exact ⟨p, t, by exact_mod_cast hp0.le, by exact_mod_cast ht0, hp2, ht2,
    by exact_mod_cast hps⟩

/-- Above a strict product bound there are rational factors witnessing it. -/
private lemma exists_rat_factors_gt {x c : ℝ} {r : ℚ} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hgt : x * c < (r : ℝ)) :
    ∃ p s : ℚ, 0 ≤ p ∧ 0 ≤ s ∧ x < (p : ℝ) ∧ c < (s : ℝ) ∧ p * s ≤ r := by
  have hδ : (0 : ℝ) < ((r : ℝ) - x * c) / (2 * (c + 1)) := by
    apply div_pos (by linarith) (by linarith)
  obtain ⟨p, hp1, hp2⟩ :=
    exists_rat_btwn (show x < x + ((r : ℝ) - x * c) / (2 * (c + 1)) by linarith)
  have hpc : (p : ℝ) * c < (r : ℝ) := by
    have h1 : (p : ℝ) * c ≤ (x + ((r : ℝ) - x * c) / (2 * (c + 1))) * c :=
      mul_le_mul_of_nonneg_right hp2.le hc
    have h2 : ((r : ℝ) - x * c) / (2 * (c + 1)) * c ≤
        ((r : ℝ) - x * c) / (2 * (c + 1)) * (c + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ.le
    have h3 : ((r : ℝ) - x * c) / (2 * (c + 1)) * (c + 1) = ((r : ℝ) - x * c) / 2 := by
      field_simp
    nlinarith
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_le_of_lt hx hp1
  have hlt2 : c < (r : ℝ) / (p : ℝ) := by rw [lt_div_iff₀ hp0]; linarith
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn hlt2
  have hps : (p : ℝ) * (t : ℝ) ≤ (r : ℝ) := by
    rw [lt_div_iff₀ hp0] at ht2
    nlinarith
  exact ⟨p, t, by exact_mod_cast hp0.le, by exact_mod_cast le_trans hc ht1.le,
    hp1, ht1, by exact_mod_cast hps⟩

/-- Transport a two-premise `T`-derivation across the prime decomposition. -/
private lemma holds_imp₂ (T : ArithmeticTheory) [T.Δ₁] (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperTheoryDP T))
    (A B C : ArithmeticSentence) (h : T ⊢ (A 🡒 (B 🡒 C)))
    (hA : v.Holds (paperPrimeDecompose (A : ArithmeticProposition)))
    (hB : v.Holds (paperPrimeDecompose (B : ArithmeticProposition))) :
    v.Holds (paperPrimeDecompose (C : ArithmeticProposition)) := by
  have h0 := PCWorld.holds_paperPrimeDecompose_of_provable T v hv _ h
  have h1 : v.Holds (paperPrimeDecompose
      ((A : ArithmeticProposition) 🡒
        ((B : ArithmeticProposition) 🡒 (C : ArithmeticProposition)))) := by
    simpa [LogicalConnective.HomClass.map_imply] using h0
  exact (v.holds_paperPrimeDecompose_imp _ _).mp
    ((v.holds_paperPrimeDecompose_imp _ _).mp h1 hA) hB

/-- **The exact product semantics.**  In every completed world of the canonical
first-order theorem process, the product LUV is valued at exactly the product of the two
factors' values — no mesh, no slack.
Kind `P`; hypotheses `(a)`.
Paper node: `def:luv` -/
lemma paperProductPaperLUV_valuesAt [𝗜𝚺₁ ⪯ T] (X W : PaperLUV T)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperTheoryDP T)) {x c : ℝ}
    (hx : v.ValuesAt X.toLUV x) (hc : v.ValuesAt W.toLUV c) :
    v.ValuesAt (paperProductPaperLUV X W).toLUV (x * c) := by
  refine ⟨mul_nonneg hx.1 hc.1, ?_, fun r => ⟨?_, ?_⟩⟩
  · exact mul_le_one₀ hx.2.1 hc.1 hc.2.1
  · intro hlt
    by_cases hr0 : (r : ℝ) < 0
    · exact PCWorld.holds_paperPrimeDecompose_of_provable T v hv _
        ((paperProductPaperLUV X W).threshold_provable_of_neg r (by exact_mod_cast hr0))
    · have hr0' : (0 : ℚ) ≤ r := by exact_mod_cast not_lt.mp hr0
      obtain ⟨p, s, hp, hs, hpx, hsc, hps⟩ :=
        exists_rat_factors_lt hx.1 hc.1 hr0' hlt
      exact holds_imp₂ T v hv _ _ _
        (paperProduct_threshold_provable X W hp hs hps)
        ((hx.2.2 p).1 hpx) ((hc.2.2 s).1 hsc)
  · intro hgt hHolds
    obtain ⟨p, s, hp, hs, hxp, hcs, hps⟩ := exists_rat_factors_gt hx.1 hc.1 hgt
    have hnp := (hx.2.2 p).2 hxp
    have hns := (hc.2.2 s).2 hcs
    have hd := paperProduct_threshold_refutable X W hp hs hps
    have h0 := PCWorld.holds_paperPrimeDecompose_of_provable T v hv _ hd
    have h1 : v.Holds (paperPrimeDecompose
        ((∼(X.thresholdFormula p : ArithmeticProposition)) 🡒
          ((∼(W.thresholdFormula s : ArithmeticProposition)) 🡒
            ∼((paperProductPaperLUV X W).thresholdFormula r :
              ArithmeticProposition)))) := by
      simpa [LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_neg] using h0
    have hA : v.Holds (paperPrimeDecompose
        (∼(X.thresholdFormula p : ArithmeticProposition))) :=
      (v.holds_paperPrimeDecompose_neg _).mpr hnp
    have hB : v.Holds (paperPrimeDecompose
        (∼(W.thresholdFormula s : ArithmeticProposition))) :=
      (v.holds_paperPrimeDecompose_neg _).mpr hns
    have hC := (v.holds_paperPrimeDecompose_imp _ _).mp
      ((v.holds_paperPrimeDecompose_imp _ _).mp h1 hA) hB
    exact (v.holds_paperPrimeDecompose_neg _).mp hC hHolds

end PaperLUV

/-! ## The exact product family -/

/-- `Rew.emb` and `Rew.castLE` commute: the arity coercion of a sentence-level formula is
the sentence-level coercion of its arity coercion. -/
private lemma emb_castLE_comm {k k' : ℕ} (h : k ≤ k') (φ : ArithmeticSemisentence k) :
    (((Rew.castLE h ▹ φ : ArithmeticSemisentence k') : ArithmeticSemiformula ℕ k')) =
      Rew.castLE h ▹ ((φ : ArithmeticSemisentence k) : ArithmeticSemiformula ℕ k) := by
  have hc : ((Rew.emb : Rew ℒₒᵣ Empty k' ℕ k').comp (Rew.castLE h)) =
      ((Rew.castLE h : Rew ℒₒᵣ ℕ k ℕ k').comp
        (Rew.emb : Rew ℒₒᵣ Empty k ℕ k)) := by
    ext x
    · rfl
    · exact IsEmpty.elim inferInstance x
  rw [← TransitiveRewriting.comp_app, hc, TransitiveRewriting.comp_app]

/-- The source presentation of the exact product: the two factor sources under an
index-preserving arity coercion, plus a fixed pairing leaf. -/
def paperProductSource (sx sw : ArithSource 1) : ArithSource 1 :=
  .exs (.and (ArithSource.castLE (by omega) sx)
    (.exs (.and (ArithSource.castLE (by omega) sw)
      (.leaf ((paperProductPairing : ArithmeticSemisentence 3) :
        ArithmeticSemiformula ℕ 3)))))

/-- The product source compiles to the product formula, so the exact product of two
literal paper-LUV *families* is again one. -/
lemma compile_paperProductSource (Xf Wf : ArithmeticSemisentence 1)
    (sx sw : ArithSource 1)
    (hx : ArithSource.compile sx = ((Xf : ArithmeticSemisentence 1) :
      ArithmeticSemiformula ℕ 1))
    (hw : ArithSource.compile sw = ((Wf : ArithmeticSemisentence 1) :
      ArithmeticSemiformula ℕ 1)) :
    ArithSource.compile (paperProductSource sx sw) =
      ((paperProductFormula Xf Wf : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1) := by
  simp [paperProductSource, ArithSource.compile, ArithSource.compile_castLE, hx, hw,
    paperProductFormula, emb_castLE_comm]
  rfl

variable {T : ArithmeticTheory} [T.Δ₁]

/-- **The exact product family.**  Pointwise the exact product LUV, with the source-level
`def:ec` certificate assembled from the two factors' certificates and a constant pairing
leaf.  No mesh, no slack, and the deductive process is untouched.
Kind `C`; hypotheses `(a)`.
Paper node: `def:ec` -/
def paperExactProductLUVSeq [𝗜𝚺₁ ⪯ T] (X W : PaperLUVSeq T) : PaperLUVSeq T where
  luv n := PaperLUV.paperProductPaperLUV (X.luv n) (W.luv n)
  source n := paperProductSource (X.source n) (W.source n)
  compiles n :=
    compile_paperProductSource (X.luv n).formula (W.luv n).formula _ _
      (X.compiles n) (W.compiles n)
  structural :=
    PolyArithmeticSourceSeq.exs
      (PolyArithmeticSourceSeq.and
        (PolyArithmeticSourceSeq.castLE (by omega) X.structural)
        (PolyArithmeticSourceSeq.exs
          (PolyArithmeticSourceSeq.and
            (PolyArithmeticSourceSeq.castLE (by omega) W.structural)
            (PolySegStream.constList _))))

/-- The `n`-th member of the exact product family is the pointwise product LUV — the
field projection, in `simp` normal form. -/
@[simp] lemma paperExactProductLUVSeq_luv [𝗜𝚺₁ ⪯ T] (X W : PaperLUVSeq T) (n : ℕ) :
    (paperExactProductLUVSeq X W).luv n =
      PaperLUV.paperProductPaperLUV (X.luv n) (W.luv n) := rfl

end LogicalInduction
