module

public import ProvabilityLogic.LabelledGentzen.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
meta import ProvabilityLogic.LabelledGentzen.Basic -- shake: keep

/-!
Saturation for proof search in the labelled sequent calculus (`ProofLabelledGentzen`/`⊢ˡ`).

`saturate` exhaustively applies the propositional rules (`impL`/`impR`), the
relational rule `Trans` and the modal rule `L□` (each keeping its principal
formula, so that every step only *adds* labelled formulas or relational atoms),
until either the sequent is closed by `axm`/`botL`/`Irref`, or a fixed point is
reached.  Saturated open sequents satisfy the Hintikka-style closure conditions
recorded in `LabelledSequent.Saturated`; the remaining boxed formulas in the
succedent are exactly the targets for `R□^Löb` in the outer proof search.

Termination is measured by the number of facts still missing from the finite
universe determined by the labels and the subformula closure of the sequent,
both of which are invariant under saturation steps.
-/

@[expose]
public section

open scoped Formula

namespace LabelledGentzen

variable {α : Type u} [DecidableEq α]

namespace LabelledSequent

variable {S : LabelledSequent α} {Rf : Finset LabelRel} {Γf Δf : Finset (LabelledFormula α)}
variable {lf : LabelledFormula α} {p : LabelRel} {x y z : Label} {A B : Formula α}

/-- The subformula closure of all formulas occurring in `S`. -/
@[grind]
def sf (S : LabelledSequent α) : FormulaFinset α := (S.ant ∪ S.suc).biUnion (·.formula.subfmls)

@[grind =>]
lemma mem_sf_of_mem_ant (h : lf ∈ S.ant) : lf.formula ∈ S.sf := by
  apply Finset.mem_biUnion.mpr;
  use lf;
  and_intros <;> grind;

@[grind =>]
lemma mem_sf_of_mem_suc (h : lf ∈ S.suc) : lf.formula ∈ S.sf := by
  apply Finset.mem_biUnion.mpr;
  use lf;
  and_intros <;> grind;

@[grind =>]
lemma subfmls_subset_sf (h : A ∈ S.sf) : A.subfmls ⊆ S.sf := by
  intro C hC;
  simp only [sf, Finset.mem_biUnion] at h ⊢;
  obtain ⟨lf, hlf, hA⟩ := h;
  exact ⟨lf, hlf, Formula.subfmls_trans hA hC⟩;

@[grind =>]
lemma mem_sf_of_imp_left (h : (A 🡒 B) ∈ S.sf) : A ∈ S.sf :=
  subfmls_subset_sf h Formula.mem_subfmls_imp_left

@[grind =>]
lemma mem_sf_of_imp_right (h : (A 🡒 B) ∈ S.sf) : B ∈ S.sf :=
  subfmls_subset_sf h Formula.mem_subfmls_imp_right

@[grind =>]
lemma mem_sf_of_box (h : (□A) ∈ S.sf) : A ∈ S.sf :=
  subfmls_subset_sf h Formula.mem_subfmls_box

omit [DecidableEq α] in
@[grind =>]
lemma mem_labels_of_mem_ant (h : lf ∈ S.ant) : lf.label ∈ S.labels := by
  simp only [labels, Finset.mem_union, Finset.mem_image];
  grind;

omit [DecidableEq α] in
@[grind =>]
lemma mem_labels_of_mem_suc (h : lf ∈ S.suc) : lf.label ∈ S.labels := by
  simp only [labels, Finset.mem_union, Finset.mem_image];
  grind;

omit [DecidableEq α] in
@[grind =>]
lemma fst_mem_labels_of_mem_rel (h : p ∈ S.rel) : p.1 ∈ S.labels := by
  simp only [labels, Finset.mem_union, Finset.mem_image];
  grind;

omit [DecidableEq α] in
@[grind =>]
lemma snd_mem_labels_of_mem_rel (h : p ∈ S.rel) : p.2 ∈ S.labels := by
  simp only [labels, Finset.mem_union, Finset.mem_image];
  grind;

/-- The finite universe of labelled formulas available to saturation. -/
@[grind]
def lfUniv (S : LabelledSequent α) : Finset (LabelledFormula α) :=
  S.labels.biUnion (fun x => S.sf.image (x ∶ ·))

lemma mem_lfUniv (hl : x ∈ S.labels) (hf : A ∈ S.sf) : (x ∶ A) ∈ S.lfUniv := by
  simp only [lfUniv, Finset.mem_biUnion, Finset.mem_image];
  exact ⟨x, hl, A, hf, rfl⟩;

lemma ant_subset_lfUniv : S.ant ⊆ S.lfUniv :=
  fun _ h => mem_lfUniv (mem_labels_of_mem_ant h) (mem_sf_of_mem_ant h)

lemma suc_subset_lfUniv : S.suc ⊆ S.lfUniv :=
  fun _ h => mem_lfUniv (mem_labels_of_mem_suc h) (mem_sf_of_mem_suc h)

omit [DecidableEq α] in
lemma rel_subset_labelsProduct : S.rel ⊆ S.labels ×ˢ S.labels := fun _ h =>
  Finset.mem_product.mpr ⟨fst_mem_labels_of_mem_rel h, snd_mem_labels_of_mem_rel h⟩

/-- Termination measure for `saturate`: the number of labelled formulas and
relational atoms still missing from the finite universe of the sequent. -/
def saturationMeasure (S : LabelledSequent α) : ℕ :=
  (S.lfUniv.card - S.ant.card) + (S.lfUniv.card - S.suc.card) +
  ((S.labels ×ˢ S.labels).card - S.rel.card)

/-! ### Invariance of `labels` and `sf` under saturation steps -/

lemma labels_insert_ant :
  (Rf ⸴ insert lf Γf ⟹ˡ Δf).labels = insert lf.label (Rf ⸴ Γf ⟹ˡ Δf).labels := by
  ext w;
  simp only [labels, Finset.image_insert, Finset.mem_union, Finset.mem_insert];
  tauto;

lemma labels_insert_suc :
  (Rf ⸴ Γf ⟹ˡ insert lf Δf).labels = insert lf.label (Rf ⸴ Γf ⟹ˡ Δf).labels := by
  ext w;
  simp only [labels, Finset.image_insert, Finset.mem_union, Finset.mem_insert];
  tauto;

omit [DecidableEq α] in
lemma labels_insert_rel :
  (insert p Rf ⸴ Γf ⟹ˡ Δf).labels = insert p.1 (insert p.2 (Rf ⸴ Γf ⟹ˡ Δf).labels) := by
  ext w;
  simp only [labels, Finset.image_insert, Finset.mem_union, Finset.mem_insert];
  tauto;

lemma labels_insert_ant_of_mem (h : lf.label ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) :
  (Rf ⸴ insert lf Γf ⟹ˡ Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels := by
  rw [labels_insert_ant, Finset.insert_eq_self.mpr h];

lemma labels_insert_suc_of_mem (h : lf.label ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) :
  (Rf ⸴ Γf ⟹ˡ insert lf Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels := by
  rw [labels_insert_suc, Finset.insert_eq_self.mpr h];

omit [DecidableEq α] in
lemma labels_insert_rel_of_mem (h1 : p.1 ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (h2 : p.2 ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) :
  (insert p Rf ⸴ Γf ⟹ˡ Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels := by
  rw [labels_insert_rel, Finset.insert_eq_self.mpr h2, Finset.insert_eq_self.mpr h1];

lemma sf_insert_ant :
  (Rf ⸴ insert lf Γf ⟹ˡ Δf).sf = lf.formula.subfmls ∪ (Rf ⸴ Γf ⟹ˡ Δf).sf := by
  simp [sf, Finset.insert_union, Finset.biUnion_insert];

lemma sf_insert_suc :
  (Rf ⸴ Γf ⟹ˡ insert lf Δf).sf = lf.formula.subfmls ∪ (Rf ⸴ Γf ⟹ˡ Δf).sf := by
  simp [sf, Finset.union_insert, Finset.biUnion_insert];

lemma sf_insert_rel : (insert p Rf ⸴ Γf ⟹ˡ Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf := rfl

lemma sf_insert_ant_of_mem (h : lf.formula ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf) :
  (Rf ⸴ insert lf Γf ⟹ˡ Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf := by
  rw [sf_insert_ant, Finset.union_eq_right.mpr (subfmls_subset_sf h)];

lemma sf_insert_suc_of_mem (h : lf.formula ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf) :
  (Rf ⸴ Γf ⟹ˡ insert lf Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf := by
  rw [sf_insert_suc, Finset.union_eq_right.mpr (subfmls_subset_sf h)];

lemma lfUniv_congr {S S' : LabelledSequent α} (hlab : S.labels = S'.labels) (hsf : S.sf = S'.sf) :
  S.lfUniv = S'.lfUniv := by
  rw [lfUniv, lfUniv, hlab, hsf];

/-! ### Decrease of `saturationMeasure` under saturation steps -/

lemma saturationMeasure_insert_ant_lt
  (hl : lf.label ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (hf : lf.formula ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf) (hnew : lf ∉ Γf) :
  (Rf ⸴ insert lf Γf ⟹ˡ Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure := by
  have hlab := labels_insert_ant_of_mem (Δf := Δf) hl;
  have hsf := sf_insert_ant_of_mem hf;
  have hU := lfUniv_congr hlab hsf;
  have hsub : insert lf Γf ⊆ (Rf ⸴ Γf ⟹ˡ Δf).lfUniv :=
    hU ▸ ant_subset_lfUniv (S := Rf ⸴ insert lf Γf ⟹ˡ Δf);
  have hcard := Finset.card_le_card hsub;
  simp only [saturationMeasure, hU, hlab, Finset.card_insert_of_notMem hnew] at hcard ⊢;
  omega;

lemma saturationMeasure_insert_ant_le
  (hl : lf.label ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (hf : lf.formula ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf) :
  (Rf ⸴ insert lf Γf ⟹ˡ Δf).saturationMeasure ≤ (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure := by
  by_cases hnew : lf ∈ Γf;
  · rw [Finset.insert_eq_self.mpr hnew];
  · exact (saturationMeasure_insert_ant_lt hl hf hnew).le;

lemma saturationMeasure_insert_suc_lt
  (hl : lf.label ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (hf : lf.formula ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf) (hnew : lf ∉ Δf) :
  (Rf ⸴ Γf ⟹ˡ insert lf Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure := by
  have hlab := labels_insert_suc_of_mem (Γf := Γf) hl;
  have hsf := sf_insert_suc_of_mem hf;
  have hU := lfUniv_congr hlab hsf;
  have hsub : insert lf Δf ⊆ (Rf ⸴ Γf ⟹ˡ Δf).lfUniv :=
    hU ▸ suc_subset_lfUniv (S := Rf ⸴ Γf ⟹ˡ insert lf Δf);
  have hcard := Finset.card_le_card hsub;
  simp only [saturationMeasure, hU, hlab, Finset.card_insert_of_notMem hnew] at hcard ⊢;
  omega;

lemma saturationMeasure_insert_suc_le
  (hl : lf.label ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (hf : lf.formula ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf) :
  (Rf ⸴ Γf ⟹ˡ insert lf Δf).saturationMeasure ≤ (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure := by
  by_cases hnew : lf ∈ Δf;
  · rw [Finset.insert_eq_self.mpr hnew];
  · exact (saturationMeasure_insert_suc_lt hl hf hnew).le;

lemma saturationMeasure_insert_rel_lt
  (h1 : p.1 ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (h2 : p.2 ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (hnew : p ∉ Rf) :
  (insert p Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure := by
  have hlab := labels_insert_rel_of_mem (Γf := Γf) (Δf := Δf) h1 h2;
  have hU := lfUniv_congr hlab (sf_insert_rel (p := p));
  have hsub : insert p Rf ⊆ (Rf ⸴ Γf ⟹ˡ Δf).labels ×ˢ (Rf ⸴ Γf ⟹ˡ Δf).labels := by
    have := rel_subset_labelsProduct (S := insert p Rf ⸴ Γf ⟹ˡ Δf);
    rwa [hlab] at this;
  have hcard := Finset.card_le_card hsub;
  simp only [saturationMeasure, hU, hlab, Finset.card_insert_of_notMem hnew] at hcard ⊢;
  omega;

/-! ### Rule-level measure lemmas -/

lemma saturationMeasure_impR (h : (x ∶ A 🡒 B) ∈ Δf) (hnew : (x ∶ A) ∉ Γf ∨ (x ∶ B) ∉ Δf) :
  (Rf ⸴ insert (x ∶ A) Γf ⟹ˡ insert (x ∶ B) Δf).saturationMeasure <
  (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure := by
  have hAB : (A 🡒 B) ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf := mem_sf_of_mem_suc (lf := x ∶ A 🡒 B) h;
  have hABm : (A 🡒 B) ∈ (Rf ⸴ Γf ⟹ˡ insert (x ∶ B) Δf).sf :=
    mem_sf_of_mem_suc (lf := x ∶ A 🡒 B) (Finset.mem_insert_of_mem h);
  have hx : x ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels := mem_labels_of_mem_suc (lf := x ∶ A 🡒 B) h;
  have hxm : x ∈ (Rf ⸴ Γf ⟹ˡ insert (x ∶ B) Δf).labels :=
    mem_labels_of_mem_suc (lf := x ∶ A 🡒 B) (Finset.mem_insert_of_mem h);
  rcases hnew with hA | hB;
  · exact lt_of_lt_of_le
      (saturationMeasure_insert_ant_lt hxm (mem_sf_of_imp_left hABm) hA)
      (saturationMeasure_insert_suc_le hx (mem_sf_of_imp_right hAB));
  · exact lt_of_le_of_lt
      (saturationMeasure_insert_ant_le hxm (mem_sf_of_imp_left hABm))
      (saturationMeasure_insert_suc_lt hx (mem_sf_of_imp_right hAB) hB);

lemma saturationMeasure_impL_left (h : (x ∶ A 🡒 B) ∈ Γf) (hnew : (x ∶ A) ∉ Δf) :
  (Rf ⸴ Γf ⟹ˡ insert (x ∶ A) Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure :=
  saturationMeasure_insert_suc_lt
    (mem_labels_of_mem_ant (lf := x ∶ A 🡒 B) h)
    (mem_sf_of_imp_left (mem_sf_of_mem_ant (lf := x ∶ A 🡒 B) h)) hnew

lemma saturationMeasure_impL_right (h : (x ∶ A 🡒 B) ∈ Γf) (hnew : (x ∶ B) ∉ Γf) :
  (Rf ⸴ insert (x ∶ B) Γf ⟹ˡ Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure :=
  saturationMeasure_insert_ant_lt
    (mem_labels_of_mem_ant (lf := x ∶ A 🡒 B) h)
    (mem_sf_of_imp_right (mem_sf_of_mem_ant (lf := x ∶ A 🡒 B) h)) hnew

lemma saturationMeasure_boxL (hR : (x, y) ∈ Rf) (h : (x ∶ □A) ∈ Γf) (hnew : (y ∶ A) ∉ Γf) :
  (Rf ⸴ insert (y ∶ A) Γf ⟹ˡ Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure :=
  saturationMeasure_insert_ant_lt
    (snd_mem_labels_of_mem_rel (p := (x, y)) hR)
    (mem_sf_of_box (mem_sf_of_mem_ant (lf := x ∶ □A) h)) hnew

lemma saturationMeasure_trans (hxy : (x, y) ∈ Rf) (hyz : (y, z) ∈ Rf) (hnew : (x, z) ∉ Rf) :
  (insert (x, z) Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure :=
  saturationMeasure_insert_rel_lt
    (fst_mem_labels_of_mem_rel (p := (x, y)) hxy)
    (snd_mem_labels_of_mem_rel (p := (y, z)) hyz) hnew

/-! ### Rule-level invariance lemmas (for propagating `labels`/`sf` through `saturate`) -/

lemma labels_impR (h : (x ∶ A 🡒 B) ∈ Δf) :
  (Rf ⸴ insert (x ∶ A) Γf ⟹ˡ insert (x ∶ B) Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels := by
  have hxm : x ∈ (Rf ⸴ Γf ⟹ˡ insert (x ∶ B) Δf).labels :=
    mem_labels_of_mem_suc (lf := x ∶ A 🡒 B) (Finset.mem_insert_of_mem h);
  have hx : x ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels := mem_labels_of_mem_suc (lf := x ∶ A 🡒 B) h;
  rw [labels_insert_ant_of_mem (lf := x ∶ A) hxm, labels_insert_suc_of_mem (lf := x ∶ B) hx];

lemma sf_impR (h : (x ∶ A 🡒 B) ∈ Δf) :
  (Rf ⸴ insert (x ∶ A) Γf ⟹ˡ insert (x ∶ B) Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf := by
  have hABm : (A 🡒 B) ∈ (Rf ⸴ Γf ⟹ˡ insert (x ∶ B) Δf).sf :=
    mem_sf_of_mem_suc (lf := x ∶ A 🡒 B) (Finset.mem_insert_of_mem h);
  have hAB : (A 🡒 B) ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf := mem_sf_of_mem_suc (lf := x ∶ A 🡒 B) h;
  rw [sf_insert_ant_of_mem (lf := x ∶ A) (mem_sf_of_imp_left hABm),
    sf_insert_suc_of_mem (lf := x ∶ B) (mem_sf_of_imp_right hAB)];

lemma labels_impL_left (h : (x ∶ A 🡒 B) ∈ Γf) :
  (Rf ⸴ Γf ⟹ˡ insert (x ∶ A) Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels :=
  labels_insert_suc_of_mem (lf := x ∶ A) (mem_labels_of_mem_ant (lf := x ∶ A 🡒 B) h)

lemma sf_impL_left (h : (x ∶ A 🡒 B) ∈ Γf) :
  (Rf ⸴ Γf ⟹ˡ insert (x ∶ A) Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf :=
  sf_insert_suc_of_mem (lf := x ∶ A) (mem_sf_of_imp_left (mem_sf_of_mem_ant (lf := x ∶ A 🡒 B) h))

lemma labels_impL_right (h : (x ∶ A 🡒 B) ∈ Γf) :
  (Rf ⸴ insert (x ∶ B) Γf ⟹ˡ Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels :=
  labels_insert_ant_of_mem (lf := x ∶ B) (mem_labels_of_mem_ant (lf := x ∶ A 🡒 B) h)

lemma sf_impL_right (h : (x ∶ A 🡒 B) ∈ Γf) :
  (Rf ⸴ insert (x ∶ B) Γf ⟹ˡ Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf :=
  sf_insert_ant_of_mem (lf := x ∶ B) (mem_sf_of_imp_right (mem_sf_of_mem_ant (lf := x ∶ A 🡒 B) h))

lemma labels_boxL (hR : (x, y) ∈ Rf) :
  (Rf ⸴ insert (y ∶ A) Γf ⟹ˡ Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels :=
  labels_insert_ant_of_mem (lf := y ∶ A) (snd_mem_labels_of_mem_rel (p := (x, y)) hR)

lemma sf_boxL (h : (x ∶ □A) ∈ Γf) :
  (Rf ⸴ insert (y ∶ A) Γf ⟹ˡ Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf :=
  sf_insert_ant_of_mem (lf := y ∶ A) (mem_sf_of_box (mem_sf_of_mem_ant (lf := x ∶ □A) h))

omit [DecidableEq α] in
lemma labels_trans (hxy : (x, y) ∈ Rf) (hyz : (y, z) ∈ Rf) :
  (insert (x, z) Rf ⸴ Γf ⟹ˡ Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels :=
  labels_insert_rel_of_mem
    (fst_mem_labels_of_mem_rel (p := (x, y)) hxy)
    (snd_mem_labels_of_mem_rel (p := (y, z)) hyz)

/-- A labelled sequent is *saturated* when it is not closed by `axm`/`botL`/`Irref` and
it satisfies the Hintikka-style closure conditions for `impL`, `impR`, `Trans` and `L□`
(principal formulas are kept, so implications may still occur, but they are decomposed). -/
structure Saturated (S : LabelledSequent α) : Prop where
  not_axm : ∀ lf ∈ S.ant, lf ∉ S.suc
  not_bot : ∀ x : Label, (x ∶ (⊥ : Formula α)) ∉ S.ant
  not_irref : ∀ x : Label, (x, x) ∉ S.rel
  imp_ant : ∀ x A B, (x ∶ A 🡒 B) ∈ S.ant → (x ∶ A) ∈ S.suc ∨ (x ∶ B) ∈ S.ant
  imp_suc : ∀ x A B, (x ∶ A 🡒 B) ∈ S.suc → (x ∶ A) ∈ S.ant ∧ (x ∶ B) ∈ S.suc
  rel_trans : ∀ x y z, (x, y) ∈ S.rel → (y, z) ∈ S.rel → (x, z) ∈ S.rel
  box_ant : ∀ x y A, (x, y) ∈ S.rel → (x ∶ □A) ∈ S.ant → (y ∶ A) ∈ S.ant

/-! ### Termination measure for the outer proof search (`lobMeasure`)

The outer search (`search`/`searchLeaves`) records `R□^Löb` applications *per label*
in `processed : Finset (LabelledFormula α)`. Its termination relies on the fact that,
along a single ancestry chain of labels, the same `□A` is treated at most once (a
second occurrence closes by `axm` or by `loop` before `R□^Löb` is consulted), so only
sibling chains count independently, and the length of every chain is bounded by the
number of boxed subformulas. This is implemented by the weighted measure
`lobMeasure`: each label `x` carries the *blocked* boxed subformulas `blockedBoxes x`
(present in the antecedent at `x` itself or at a direct `R`-predecessor of `x`), and
a `R□^Löb` step at `x` creates one fresh label whose blocked set strictly contains
the one of `x`, so its exponential weight drops by a factor that dominates the (at
most `boxSf.card`) new pending boxes it brings.

- [Neg14, Theorem 5.5]
-/

/-- The boxed formulas in the subformula closure of `S`. -/
def boxSf (S : LabelledSequent α) : FormulaFinset α := S.sf.filter Formula.IsBox

/--
The boxed subformulas that can no longer become `R□^Löb` targets at the label `x`:
those in the antecedent at `x` itself (the sequent closes by `axm`) or at a direct
`R`-predecessor of `x` (the sequent closes by `loop`).

- [Neg14, Lemma 5.2]
-/
def blockedBoxes (S : LabelledSequent α) (x : Label) : FormulaFinset α :=
  S.boxSf.filter (fun B => (x ∶ B) ∈ S.ant ∨ ∃ p ∈ S.rel, p.2 = x ∧ (p.1 ∶ B) ∈ S.ant)

/-- The boxed subformulas still available as `R□^Löb` targets at the label `x`:
not yet processed there and not blocked. -/
def pendingBoxes (S : LabelledSequent α) (P : Finset (LabelledFormula α)) (x : Label) :
  FormulaFinset α :=
  S.boxSf.filter (fun B => (x ∶ B) ∉ P ∧ B ∉ S.blockedBoxes x)

/-- Exponential weight of the label `x` in `lobMeasure`. -/
def lobWeight (S : LabelledSequent α) (x : Label) : ℕ :=
  (S.boxSf.card + 1) ^ (S.boxSf.card - (S.blockedBoxes x).card)

/-- Termination measure for `search`/`searchLeaves`: the weighted number of pending
`R□^Löb` targets over all labels of `S`. -/
def lobMeasure (S : LabelledSequent α) (P : Finset (LabelledFormula α)) : ℕ :=
  ∑ x ∈ S.labels, (S.pendingBoxes P x).card * S.lobWeight x

section lobMeasure

variable {P : Finset (LabelledFormula α)} {S' : LabelledSequent α}

lemma blockedBoxes_subset_boxSf : S.blockedBoxes x ⊆ S.boxSf := Finset.filter_subset _ _

lemma boxSf_congr (h : S.sf = S'.sf) : S.boxSf = S'.boxSf := by rw [boxSf, boxSf, h];

lemma blockedBoxes_mono (hsf : S.sf = S'.sf) (hrel : S.rel ⊆ S'.rel) (hant : S.ant ⊆ S'.ant) :
  S.blockedBoxes x ⊆ S'.blockedBoxes x := by
  intro B hB;
  simp only [blockedBoxes, Finset.mem_filter] at hB ⊢;
  refine ⟨boxSf_congr hsf ▸ hB.1, ?_⟩;
  rcases hB.2 with h | ⟨p, hp, h1, h2⟩;
  · exact Or.inl (hant h);
  · exact Or.inr ⟨p, hrel hp, h1, hant h2⟩;

/-- `lobMeasure` does not increase along a step that keeps `labels` and `sf` and only
adds relational atoms and antecedent formulas (as every saturation step does). -/
lemma lobMeasure_le (hlab : S'.labels = S.labels) (hsf : S'.sf = S.sf)
  (hrel : S.rel ⊆ S'.rel) (hant : S.ant ⊆ S'.ant) :
  S'.lobMeasure P ≤ S.lobMeasure P := by
  -- Every `blockedBoxes x` grows and every summand of `lobMeasure` shrinks.
  rw [lobMeasure, lobMeasure, hlab];
  apply Finset.sum_le_sum;
  intro z _;
  have hbox : S'.boxSf = S.boxSf := boxSf_congr hsf;
  have hbl : S.blockedBoxes z ⊆ S'.blockedBoxes z := blockedBoxes_mono hsf.symm hrel hant;
  apply Nat.mul_le_mul;
  · apply Finset.card_le_card;
    intro B hB;
    simp only [pendingBoxes, Finset.mem_filter] at hB ⊢;
    exact ⟨hbox ▸ hB.1, hB.2.1, fun h => hB.2.2 (hbl h)⟩;
  · rw [lobWeight, lobWeight, hbox];
    exact Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_left (Finset.card_le_card hbl) _);

/--
Key decrease lemma for the termination of `search`/`searchLeaves`:
applying `R□^Löb` at an unblocked, unprocessed target `x ∶ □A` with a fresh label `y` —
adding, besides `(x, y)`, the relational atoms `(w, y)` for every direct predecessor `w`
of `x` (which `Trans`-saturation would add anyway) — strictly decreases `lobMeasure`.

- [Neg14, Theorem 5.5]
-/
lemma lobMeasure_lob_lt
  (hΔ : (x ∶ □A) ∈ Δf) (hP : (x ∶ □A) ∉ P) (hΓ : (x ∶ □A) ∉ Γf)
  (hpred : ∀ w, (w, x) ∈ Rf → (w ∶ □A) ∉ Γf)
  (hy : y ∉ (Rf ⸴ Γf ⟹ˡ Δf).labels) :
  (insert (x, y) ((Rf.filter (fun p => p.2 = x)).image (fun p => (p.1, y)) ∪ Rf) ⸴
    insert (y ∶ □A) Γf ⟹ˡ insert (y ∶ A) Δf).lobMeasure (insert (x ∶ □A) P) <
  (Rf ⸴ Γf ⟹ˡ Δf).lobMeasure P := by
  set L := Rf ⸴ Γf ⟹ˡ Δf with hL;
  set N : Finset LabelRel :=
    insert (x, y) ((Rf.filter (fun p => p.2 = x)).image (fun p => (p.1, y)) ∪ Rf) with hN;
  set S' := N ⸴ insert (y ∶ □A) Γf ⟹ˡ insert (y ∶ A) Δf with hS';
  set P' : Finset (LabelledFormula α) := insert (x ∶ □A) P with hP';
  have hxlab : x ∈ L.labels := mem_labels_of_mem_suc (lf := x ∶ □A) hΔ;
  have hboxA : (□A) ∈ L.sf := mem_sf_of_mem_suc (lf := x ∶ □A) hΔ;
  have hsf' : S'.sf = L.sf := by
    have h1 : (□A) ∈ (N ⸴ Γf ⟹ˡ insert (y ∶ A) Δf).sf :=
      mem_sf_of_mem_suc (lf := x ∶ □A) (Finset.mem_insert_of_mem hΔ);
    have h2 : A ∈ (N ⸴ Γf ⟹ˡ Δf).sf := mem_sf_of_box (mem_sf_of_mem_suc (lf := x ∶ □A) hΔ);
    calc S'.sf = (N ⸴ Γf ⟹ˡ insert (y ∶ A) Δf).sf := sf_insert_ant_of_mem (lf := y ∶ □A) h1
    _ = (N ⸴ Γf ⟹ˡ Δf).sf := sf_insert_suc_of_mem (lf := y ∶ A) h2
    _ = L.sf := rfl;
  have hAbox : (□A) ∈ L.boxSf := Finset.mem_filter.mpr ⟨hboxA, by grind⟩;
  have hfsty : ∀ p ∈ Rf, p.1 ≠ y := fun p hp h => hy (h ▸ fst_mem_labels_of_mem_rel hp);
  have hsndy : ∀ p ∈ Rf, p.2 ≠ y := fun p hp h => hy (h ▸ snd_mem_labels_of_mem_rel hp);
  have hlab' : S'.labels = insert y L.labels := by
    ext w;
    simp only [labels, hS', hN, hL, Finset.mem_union, Finset.mem_insert, Finset.mem_image,
      Finset.mem_filter];
    grind;
  have hylab : y ∉ L.labels := hy;
  have hblock_old : ∀ z ∈ L.labels, S'.blockedBoxes z = L.blockedBoxes z := by
    intro z hz;
    have hzy : z ≠ y := fun h => hy (h ▸ hz);
    rw [blockedBoxes, blockedBoxes, boxSf_congr hsf'];
    apply Finset.filter_congr;
    intro B _;
    show ((z ∶ B) ∈ insert (y ∶ □A) Γf ∨ ∃ p ∈ N, p.2 = z ∧ (p.1 ∶ B) ∈ insert (y ∶ □A) Γf) ↔
      ((z ∶ B) ∈ Γf ∨ ∃ p ∈ Rf, p.2 = z ∧ (p.1 ∶ B) ∈ Γf);
    simp only [hN, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter];
    grind;
  have hblocky : insert (□A) (L.blockedBoxes x) ⊆ S'.blockedBoxes y := by
    intro B hB;
    simp only [Finset.mem_insert] at hB;
    simp only [blockedBoxes, Finset.mem_filter, boxSf_congr hsf'];
    rcases hB with rfl | hB;
    · exact ⟨hAbox, Or.inl (Finset.mem_insert_self _ _)⟩;
    · obtain ⟨hBbox, h⟩ := Finset.mem_filter.mp hB;
      refine ⟨hBbox, Or.inr ?_⟩;
      rcases h with h | ⟨p, hp, hp2, hp1⟩;
      · exact ⟨(x, y), by grind, rfl, Finset.mem_insert_of_mem h⟩;
      · exact ⟨(p.1, y), by grind, rfl, Finset.mem_insert_of_mem hp1⟩;
  have hAnb : (□A) ∉ L.blockedBoxes x := by
    simp only [blockedBoxes, Finset.mem_filter, hL];
    grind;
  set b := L.boxSf.card with hb;
  have hbx_lt : (L.blockedBoxes x).card < b :=
    Finset.card_lt_card ((Finset.ssubset_iff_of_subset blockedBoxes_subset_boxSf).mpr
      ⟨□A, hAbox, hAnb⟩);
  have hby : (L.blockedBoxes x).card + 1 ≤ (S'.blockedBoxes y).card := by
    calc (L.blockedBoxes x).card + 1 = (insert (□A) (L.blockedBoxes x)).card :=
      (Finset.card_insert_of_notMem hAnb).symm
    _ ≤ _ := Finset.card_le_card hblocky;
  have hpend_old : ∀ z ∈ L.labels, z ≠ x → S'.pendingBoxes P' z = L.pendingBoxes P z := by
    intro z hz hzx;
    ext B;
    simp only [pendingBoxes, Finset.mem_filter, boxSf_congr hsf', hblock_old z hz, hP',
      Finset.mem_insert];
    grind;
  have hpend_x : S'.pendingBoxes P' x = (L.pendingBoxes P x).erase (□A) := by
    ext B;
    simp only [pendingBoxes, Finset.mem_filter, Finset.mem_erase, boxSf_congr hsf',
      hblock_old x hxlab, hP', Finset.mem_insert];
    grind;
  have hApend : (□A) ∈ L.pendingBoxes P x := Finset.mem_filter.mpr ⟨hAbox, hP, hAnb⟩;
  have hw_old : ∀ z ∈ L.labels, S'.lobWeight z = L.lobWeight z := by
    intro z hz;
    rw [lobWeight, lobWeight, boxSf_congr hsf', hblock_old z hz];
  have hpendy_le : (S'.pendingBoxes P' y).card ≤ b := by
    calc (S'.pendingBoxes P' y).card ≤ S'.boxSf.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = b := by rw [boxSf_congr hsf'];
  -- The fresh label's contribution is strictly dominated by the weight freed at `x`.
  have hstrict : (S'.pendingBoxes P' y).card * S'.lobWeight y < L.lobWeight x := by
    have hwy : S'.lobWeight y ≤ (b + 1) ^ (b - ((L.blockedBoxes x).card + 1)) := by
      rw [lobWeight, boxSf_congr hsf'];
      exact Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_left hby _);
    have h1 : (S'.pendingBoxes P' y).card * S'.lobWeight y ≤
      b * (b + 1) ^ (b - ((L.blockedBoxes x).card + 1)) := Nat.mul_le_mul hpendy_le hwy;
    have h2 : (b + 1) * (b + 1) ^ (b - ((L.blockedBoxes x).card + 1)) =
      (b + 1) ^ (b - (L.blockedBoxes x).card) := by
      rw [← pow_succ'];
      congr 1;
      omega;
    have h3 : b * (b + 1) ^ (b - ((L.blockedBoxes x).card + 1)) <
      (b + 1) * (b + 1) ^ (b - ((L.blockedBoxes x).card + 1)) :=
      Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl (Nat.pow_pos (by omega));
    calc (S'.pendingBoxes P' y).card * S'.lobWeight y
        ≤ b * (b + 1) ^ (b - ((L.blockedBoxes x).card + 1)) := h1
    _ < (b + 1) * (b + 1) ^ (b - ((L.blockedBoxes x).card + 1)) := h3
    _ = (b + 1) ^ (b - (L.blockedBoxes x).card) := h2
    _ = L.lobWeight x := rfl;
  -- Assemble: split the fresh label `y` and the target label `x` out of both sums.
  have hsum' : S'.lobMeasure P' =
    (S'.pendingBoxes P' y).card * S'.lobWeight y +
    ∑ z ∈ L.labels, (S'.pendingBoxes P' z).card * S'.lobWeight z := by
    rw [lobMeasure, hlab', Finset.sum_insert hylab];
  have hx_term : (S'.pendingBoxes P' x).card * S'.lobWeight x + L.lobWeight x =
    (L.pendingBoxes P x).card * L.lobWeight x := by
    rw [hpend_x, Finset.card_erase_of_mem hApend, hw_old x hxlab];
    have hpos : 1 ≤ (L.pendingBoxes P x).card := Finset.card_pos.mpr ⟨□A, hApend⟩;
    calc ((L.pendingBoxes P x).card - 1) * L.lobWeight x + L.lobWeight x
        = (((L.pendingBoxes P x).card - 1) + 1) * L.lobWeight x := by rw [Nat.succ_mul]
    _ = (L.pendingBoxes P x).card * L.lobWeight x := by rw [Nat.sub_add_cancel hpos];
  have hsum_rest : ∑ z ∈ L.labels.erase x, (S'.pendingBoxes P' z).card * S'.lobWeight z =
    ∑ z ∈ L.labels.erase x, (L.pendingBoxes P z).card * L.lobWeight z := by
    apply Finset.sum_congr rfl;
    intro z hz;
    have hz' : z ∈ L.labels := Finset.mem_of_mem_erase hz;
    rw [hpend_old z hz' (Finset.ne_of_mem_erase hz), hw_old z hz'];
  have hsplit' : (S'.pendingBoxes P' x).card * S'.lobWeight x +
    ∑ z ∈ L.labels.erase x, (S'.pendingBoxes P' z).card * S'.lobWeight z =
    ∑ z ∈ L.labels, (S'.pendingBoxes P' z).card * S'.lobWeight z :=
    Finset.add_sum_erase _ (fun z => (S'.pendingBoxes P' z).card * S'.lobWeight z) hxlab;
  have hsplit : (L.pendingBoxes P x).card * L.lobWeight x +
    ∑ z ∈ L.labels.erase x, (L.pendingBoxes P z).card * L.lobWeight z = L.lobMeasure P :=
    Finset.add_sum_erase _ (fun z => (L.pendingBoxes P z).card * L.lobWeight z) hxlab;
  -- abbreviate the nonlinear atoms so that `omega` can finish
  set a₁ := (S'.pendingBoxes P' y).card * S'.lobWeight y with ha₁;
  set a₂ := (S'.pendingBoxes P' x).card * S'.lobWeight x with ha₂;
  set a₃ := (L.pendingBoxes P x).card * L.lobWeight x with ha₃;
  set a₄ := ∑ z ∈ L.labels.erase x, (S'.pendingBoxes P' z).card * S'.lobWeight z with ha₄;
  set a₅ := ∑ z ∈ L.labels.erase x, (L.pendingBoxes P z).card * L.lobWeight z with ha₅;
  set a₆ := ∑ z ∈ L.labels, (S'.pendingBoxes P' z).card * S'.lobWeight z with ha₆;
  omega;

end lobMeasure

end LabelledSequent


namespace ProofLabelledGentzen

variable {R : Finset LabelRel} {Γ Δ : Finset (LabelledFormula α)} {x : Label} {A B : Formula α}

/-- `impR` with the principal formula kept in the succedent. -/
def impR_mem (h : (x ∶ A 🡒 B) ∈ Δ)
  (p : ⊢ˡ! (R ⸴ insert (x ∶ A) Γ ⟹ˡ insert (x ∶ B) Δ)) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) := by
  rw [show Δ = insert (x ∶ A 🡒 B) Δ by grind];
  exact impR p;

/-- `impL` with the principal formula kept in the antecedent. -/
def impL_mem (h : (x ∶ A 🡒 B) ∈ Γ)
  (p : ⊢ˡ! (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ)) (q : ⊢ˡ! (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ)) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) := by
  rw [show Γ = insert (x ∶ A 🡒 B) Γ by grind];
  exact impL p q;

/-- Iterated `Trans`: discharges the relational atoms `(w, y)` for a list of labels `ws`
whose members are all `R`-predecessors of `x`, given `(x, y) ∈ R`.  Used by the proof
search to justify the eagerly added transitive pairs of a `R□^Löb` step. -/
def transMany (x y : Label) :
  (ws : List Label) → (hws : ∀ w ∈ ws, (w, x) ∈ R) → (hxy : (x, y) ∈ R) →
  ⊢ˡ! ((ws.map (fun w => (w, y))).toFinset ∪ R ⸴ Γ ⟹ˡ Δ) → ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ)
  | [], _, _, π => by simpa using π
  | w :: ws, hws, hxy, π =>
    transMany x y ws (fun v hv => hws v (List.mem_cons_of_mem _ hv)) hxy
      (ProofLabelledGentzen.trans w x y
        (hxy := Finset.mem_union_right _ (hws w List.mem_cons_self))
        (hyz := Finset.mem_union_right _ hxy)
        (by simpa [Finset.insert_union] using π))

end ProofLabelledGentzen


/-- The labelled sequent determined by list-representations of its components.
Used to keep the leaves of `saturate` computably enumerable (extracting elements
from a `Finset` is noncomputable). -/
abbrev LabelledSequent.ofLists
  (L : List LabelRel × List (LabelledFormula α) × List (LabelledFormula α)) : LabelledSequent α :=
  L.1.toFinset ⸴ L.2.1.toFinset ⟹ˡ L.2.2.toFinset

/-- The result of saturating a labelled sequent `S`: either a proof of `S`, or a
finite list of saturated open sequents (the leaves of the saturation tree, given by
list-representations of their components for computability) together with a way of
recovering a proof of `S` from proofs of all of them.  The leaves have the same
labels and the same subformula closure as `S`, and extend `S` componentwise
(saturation only ever *adds* relational atoms and labelled formulas). -/
inductive SaturationResult (S : LabelledSequent α) : Type u
  | closed (π : ⊢ˡ! S) : SaturationResult S
  | stuck (leaves : List (List LabelRel × List (LabelledFormula α) × List (LabelledFormula α)))
      (hsat : ∀ L ∈ leaves, (LabelledSequent.ofLists L).Saturated)
      (hlab : ∀ L ∈ leaves, (LabelledSequent.ofLists L).labels = S.labels)
      (hsf : ∀ L ∈ leaves, (LabelledSequent.ofLists L).sf = S.sf)
      (hmono : ∀ L ∈ leaves,
        S.rel ⊆ (LabelledSequent.ofLists L).rel ∧
        S.ant ⊆ (LabelledSequent.ofLists L).ant ∧
        S.suc ⊆ (LabelledSequent.ofLists L).suc)
      (k : (∀ L ∈ leaves, ⊢ˡ! (LabelledSequent.ofLists L)) → ⊢ˡ! S) : SaturationResult S

namespace SaturationResult

variable {S S' S₁ S₂ : LabelledSequent α}

/-- Transports a `SaturationResult` along a one-premise derivation step whose premise
`S` extends the conclusion `S'` componentwise. -/
def map (f : ⊢ˡ! S → ⊢ˡ! S') (hlab : S.labels = S'.labels) (hsf : S.sf = S'.sf)
  (hrel : S'.rel ⊆ S.rel) (hant : S'.ant ⊆ S.ant) (hsuc : S'.suc ⊆ S.suc) :
  SaturationResult S → SaturationResult S'
  | closed π => closed (f π)
  | stuck leaves hsat hl hs hm k =>
      stuck leaves hsat
        (fun T hT => (hl T hT).trans hlab)
        (fun T hT => (hs T hT).trans hsf)
        (fun T hT => ⟨hrel.trans (hm T hT).1, hant.trans (hm T hT).2.1, hsuc.trans (hm T hT).2.2⟩)
        (fun ps => f (k ps))

/-- Transports two `SaturationResult`s along a two-premise derivation step whose premises
`S₁`/`S₂` extend the conclusion `S'` componentwise. -/
def map₂ (f : ⊢ˡ! S₁ → ⊢ˡ! S₂ → ⊢ˡ! S')
  (hlab₁ : S₁.labels = S'.labels) (hsf₁ : S₁.sf = S'.sf)
  (hlab₂ : S₂.labels = S'.labels) (hsf₂ : S₂.sf = S'.sf)
  (hrel₁ : S'.rel ⊆ S₁.rel) (hant₁ : S'.ant ⊆ S₁.ant) (hsuc₁ : S'.suc ⊆ S₁.suc)
  (hrel₂ : S'.rel ⊆ S₂.rel) (hant₂ : S'.ant ⊆ S₂.ant) (hsuc₂ : S'.suc ⊆ S₂.suc) :
  SaturationResult S₁ → SaturationResult S₂ → SaturationResult S'
  | closed π₁, closed π₂ => closed (f π₁ π₂)
  | closed π₁, stuck l₂ hsat₂ hl₂ hs₂ hm₂ k₂ =>
      stuck l₂ hsat₂
        (fun T hT => (hl₂ T hT).trans hlab₂)
        (fun T hT => (hs₂ T hT).trans hsf₂)
        (fun T hT =>
          ⟨hrel₂.trans (hm₂ T hT).1, hant₂.trans (hm₂ T hT).2.1, hsuc₂.trans (hm₂ T hT).2.2⟩)
        (fun ps => f π₁ (k₂ ps))
  | stuck l₁ hsat₁ hl₁ hs₁ hm₁ k₁, closed π₂ =>
      stuck l₁ hsat₁
        (fun T hT => (hl₁ T hT).trans hlab₁)
        (fun T hT => (hs₁ T hT).trans hsf₁)
        (fun T hT =>
          ⟨hrel₁.trans (hm₁ T hT).1, hant₁.trans (hm₁ T hT).2.1, hsuc₁.trans (hm₁ T hT).2.2⟩)
        (fun ps => f (k₁ ps) π₂)
  | stuck l₁ hsat₁ hl₁ hs₁ hm₁ k₁, stuck l₂ hsat₂ hl₂ hs₂ hm₂ k₂ =>
      stuck (l₁ ++ l₂)
        (fun T hT => (List.mem_append.mp hT).elim (hsat₁ T) (hsat₂ T))
        (fun T hT => (List.mem_append.mp hT).elim
          (fun h => (hl₁ T h).trans hlab₁) (fun h => (hl₂ T h).trans hlab₂))
        (fun T hT => (List.mem_append.mp hT).elim
          (fun h => (hs₁ T h).trans hsf₁) (fun h => (hs₂ T h).trans hsf₂))
        (fun T hT => (List.mem_append.mp hT).elim
          (fun h =>
            ⟨hrel₁.trans (hm₁ T h).1, hant₁.trans (hm₁ T h).2.1, hsuc₁.trans (hm₁ T h).2.2⟩)
          (fun h =>
            ⟨hrel₂.trans (hm₂ T h).1, hant₂.trans (hm₂ T h).2.1, hsuc₂.trans (hm₂ T h).2.2⟩))
        (fun ps => f
          (k₁ (fun T hT => ps T (List.mem_append_left _ hT)))
          (k₂ (fun T hT => ps T (List.mem_append_right _ hT))))

end SaturationResult


/-! ### Finders for applicable saturation steps -/

section finders

variable (R : List LabelRel) (Γ Δ : List (LabelledFormula α))

/-- Finds an implication in the succedent whose `impR`-decomposition is still missing. -/
def impRTarget? : Option (Label × Formula α × Formula α) :=
  Δ.findSome? fun lf =>
    match lf with
    | ⟨x, A 🡒 B⟩ => if (x ∶ A) ∈ Γ ∧ (x ∶ B) ∈ Δ then none else some (x, A, B)
    | _ => none

/-- Finds an implication in the antecedent whose `impL`-decomposition is still missing. -/
def impLTarget? : Option (Label × Formula α × Formula α) :=
  Γ.findSome? fun lf =>
    match lf with
    | ⟨x, A 🡒 B⟩ => if (x ∶ A) ∈ Δ ∨ (x ∶ B) ∈ Γ then none else some (x, A, B)
    | _ => none

/-- Finds a relational atom `(x, y)` and a boxed formula `x : □A` whose `L□`-instance `y : A`
is still missing. -/
def boxLTarget? : Option (Label × Label × Formula α) :=
  R.findSome? fun p =>
    Γ.findSome? fun lf =>
      match lf with
      | ⟨x, □A⟩ => if x = p.1 ∧ (p.2 ∶ A) ∉ Γ then some (p.1, p.2, A) else none
      | _ => none

/-- Finds relational atoms `(x, y)` and `(y, z)` whose transitive consequence `(x, z)`
is still missing. -/
def transTarget? : Option (Label × Label × Label) :=
  R.findSome? fun p =>
    R.findSome? fun q =>
      if q.1 = p.2 ∧ (p.1, q.2) ∉ R then some (p.1, p.2, q.2) else none

end finders

section finders

variable {R : List LabelRel} {Γ Δ : List (LabelledFormula α)} {x y z : Label} {A B : Formula α}

lemma impRTarget?_some (h : impRTarget? Γ Δ = some (x, A, B)) :
  (x ∶ A 🡒 B) ∈ Δ.toFinset ∧ ((x ∶ A) ∉ Γ.toFinset ∨ (x ∶ B) ∉ Δ.toFinset) := by
  obtain ⟨lf, hmem, hlf⟩ := List.exists_of_findSome?_eq_some h;
  obtain ⟨x', F⟩ := lf;
  cases F <;> grind [List.mem_toFinset];

lemma impRTarget?_none (h : impRTarget? Γ Δ = none) (hm : (x ∶ A 🡒 B) ∈ Δ.toFinset) :
  (x ∶ A) ∈ Γ.toFinset ∧ (x ∶ B) ∈ Δ.toFinset := by
  unfold impRTarget? at h;
  rw [List.findSome?_eq_none_iff] at h;
  have := h (x ∶ A 🡒 B) (List.mem_toFinset.mp hm);
  grind [List.mem_toFinset];

lemma impLTarget?_some (h : impLTarget? Γ Δ = some (x, A, B)) :
  (x ∶ A 🡒 B) ∈ Γ.toFinset ∧ (x ∶ A) ∉ Δ.toFinset ∧ (x ∶ B) ∉ Γ.toFinset := by
  obtain ⟨lf, hmem, hlf⟩ := List.exists_of_findSome?_eq_some h;
  obtain ⟨x', F⟩ := lf;
  cases F <;> grind [List.mem_toFinset];

lemma impLTarget?_none (h : impLTarget? Γ Δ = none) (hm : (x ∶ A 🡒 B) ∈ Γ.toFinset) :
  (x ∶ A) ∈ Δ.toFinset ∨ (x ∶ B) ∈ Γ.toFinset := by
  unfold impLTarget? at h;
  rw [List.findSome?_eq_none_iff] at h;
  have := h (x ∶ A 🡒 B) (List.mem_toFinset.mp hm);
  grind [List.mem_toFinset];

lemma boxLTarget?_some (h : boxLTarget? R Γ = some (x, y, A)) :
  (x, y) ∈ R.toFinset ∧ (x ∶ □A) ∈ Γ.toFinset ∧ (y ∶ A) ∉ Γ.toFinset := by
  obtain ⟨p, hp, h1⟩ := List.exists_of_findSome?_eq_some h;
  obtain ⟨lf, hlf, h2⟩ := List.exists_of_findSome?_eq_some h1;
  obtain ⟨x', F⟩ := lf;
  cases F <;> grind [List.mem_toFinset];

lemma boxLTarget?_none (h : boxLTarget? R Γ = none)
  (hR : (x, y) ∈ R.toFinset) (hm : (x ∶ □A) ∈ Γ.toFinset) : (y ∶ A) ∈ Γ.toFinset := by
  unfold boxLTarget? at h;
  rw [List.findSome?_eq_none_iff] at h;
  have h1 := h (x, y) (List.mem_toFinset.mp hR);
  rw [List.findSome?_eq_none_iff] at h1;
  have h2 := h1 (x ∶ □A) (List.mem_toFinset.mp hm);
  grind [List.mem_toFinset];

lemma transTarget?_some (h : transTarget? R = some (x, y, z)) :
  (x, y) ∈ R.toFinset ∧ (y, z) ∈ R.toFinset ∧ (x, z) ∉ R.toFinset := by
  obtain ⟨p, hp, h1⟩ := List.exists_of_findSome?_eq_some h;
  obtain ⟨q, hq, h2⟩ := List.exists_of_findSome?_eq_some h1;
  grind [List.mem_toFinset];

lemma transTarget?_none (h : transTarget? R = none)
  (hxy : (x, y) ∈ R.toFinset) (hyz : (y, z) ∈ R.toFinset) : (x, z) ∈ R.toFinset := by
  unfold transTarget? at h;
  rw [List.findSome?_eq_none_iff] at h;
  have h1 := h (x, y) (List.mem_toFinset.mp hxy);
  rw [List.findSome?_eq_none_iff] at h1;
  have h2 := h1 (y, z) (List.mem_toFinset.mp hyz);
  grind [List.mem_toFinset];

end finders


/-! ### The saturation procedure -/

/-- Saturates the labelled sequent `R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset`, exhaustively
applying `impL`/`impR`/`L□`/`Trans` (keeping principal formulas) until the sequent is
closed by `axm`/`botL`/`Irref` or saturated. -/
def saturate (R : List LabelRel) (Γ Δ : List (LabelledFormula α)) :
  SaturationResult (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset) :=
  match h₁ : Γ.find? (fun lf => decide (lf ∈ Δ)) with
  | some lf =>
    .closed <| ProofLabelledGentzen.union lf.label lf.formula
      (List.mem_toFinset.mpr (List.mem_of_find?_eq_some h₁))
      (by
        have h := List.find?_some h₁;
        simp only [decide_eq_true_eq] at h;
        exact List.mem_toFinset.mpr h)
  | none =>
  match h₂ : Γ.find? (fun lf : LabelledFormula α => decide (lf.formula = (⊥ : Formula α))) with
  | some lf =>
    .closed <| ProofLabelledGentzen.botL_mem lf.label
      (by
        have h := List.find?_some h₂;
        simp only [decide_eq_true_eq] at h;
        have hm : (lf.label ∶ lf.formula) ∈ Γ.toFinset :=
          List.mem_toFinset.mpr (List.mem_of_find?_eq_some h₂);
        rwa [h] at hm)
  | none =>
  match h₃ : R.find? (fun p => decide (p.1 = p.2)) with
  | some p =>
    .closed <| ProofLabelledGentzen.irref p.1
      (by
        have h := List.find?_some h₃;
        simp only [decide_eq_true_eq] at h;
        have hm : (p.1, p.2) ∈ R.toFinset := List.mem_toFinset.mpr (List.mem_of_find?_eq_some h₃);
        rwa [← h] at hm)
  | none =>
  match h₄ : impRTarget? Γ Δ with
  | some (x, A, B) =>
    (saturate R ((x ∶ A) :: Γ) ((x ∶ B) :: Δ)).map
      (fun π => ProofLabelledGentzen.impR_mem (impRTarget?_some h₄).1 (by simpa using π))
      (by simp only [List.toFinset_cons]; exact LabelledSequent.labels_impR (impRTarget?_some h₄).1)
      (by simp only [List.toFinset_cons]; exact LabelledSequent.sf_impR (impRTarget?_some h₄).1)
      (by exact subset_rfl)
      (by simp only [List.toFinset_cons]; exact Finset.subset_insert _ _)
      (by simp only [List.toFinset_cons]; exact Finset.subset_insert _ _)
  | none =>
  match h₅ : impLTarget? Γ Δ with
  | some (x, A, B) =>
    SaturationResult.map₂
      (fun π₁ π₂ => ProofLabelledGentzen.impL_mem (impLTarget?_some h₅).1
        (by simpa using π₁) (by simpa using π₂))
      (by simp only [List.toFinset_cons]; exact LabelledSequent.labels_impL_left (impLTarget?_some h₅).1)
      (by simp only [List.toFinset_cons]; exact LabelledSequent.sf_impL_left (impLTarget?_some h₅).1)
      (by simp only [List.toFinset_cons]; exact LabelledSequent.labels_impL_right (impLTarget?_some h₅).1)
      (by simp only [List.toFinset_cons]; exact LabelledSequent.sf_impL_right (impLTarget?_some h₅).1)
      (by exact subset_rfl) (by exact subset_rfl)
      (by simp only [List.toFinset_cons]; exact Finset.subset_insert _ _)
      (by exact subset_rfl)
      (by simp only [List.toFinset_cons]; exact Finset.subset_insert _ _)
      (by exact subset_rfl)
      (saturate R Γ ((x ∶ A) :: Δ))
      (saturate R ((x ∶ B) :: Γ) Δ)
  | none =>
  match h₆ : boxLTarget? R Γ with
  | some (x, y, A) =>
    (saturate R ((y ∶ A) :: Γ) Δ).map
      (fun π => ProofLabelledGentzen.boxL x y A
        (boxLTarget?_some h₆).1 (boxLTarget?_some h₆).2.1 (by simpa using π))
      (by simp only [List.toFinset_cons]; exact LabelledSequent.labels_boxL (boxLTarget?_some h₆).1)
      (by simp only [List.toFinset_cons]; exact LabelledSequent.sf_boxL (boxLTarget?_some h₆).2.1)
      (by exact subset_rfl)
      (by simp only [List.toFinset_cons]; exact Finset.subset_insert _ _)
      (by exact subset_rfl)
  | none =>
  match h₇ : transTarget? R with
  | some (x, y, z) =>
    (saturate ((x, z) :: R) Γ Δ).map
      (fun π => ProofLabelledGentzen.trans x y z
        (transTarget?_some h₇).1 (transTarget?_some h₇).2.1 (by simpa using π))
      (by
        simp only [List.toFinset_cons];
        exact LabelledSequent.labels_trans (transTarget?_some h₇).1 (transTarget?_some h₇).2.1)
      (by simp only [List.toFinset_cons]; exact LabelledSequent.sf_insert_rel)
      (by simp only [List.toFinset_cons]; exact Finset.subset_insert _ _)
      (by exact subset_rfl) (by exact subset_rfl)
  | none =>
    .stuck [(R, Γ, Δ)]
      (by
        intro T hT;
        rw [List.mem_singleton] at hT;
        subst hT;
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩;
        · have := List.find?_eq_none.mp h₁; grind [List.mem_toFinset];
        · have := List.find?_eq_none.mp h₂; grind [List.mem_toFinset];
        · have := List.find?_eq_none.mp h₃; grind [List.mem_toFinset];
        · exact fun x A B hm => impLTarget?_none h₅ hm;
        · exact fun x A B hm => impRTarget?_none h₄ hm;
        · exact fun x y z hxy hyz => transTarget?_none h₇ hxy hyz;
        · exact fun x y A hR hm => boxLTarget?_none h₆ hR hm)
      (by intro T hT; rw [List.mem_singleton] at hT; subst hT; rfl)
      (by intro T hT; rw [List.mem_singleton] at hT; subst hT; rfl)
      (by
        intro T hT;
        rw [List.mem_singleton] at hT;
        subst hT;
        exact ⟨subset_rfl, subset_rfl, subset_rfl⟩)
      (fun ps => ps _ (List.mem_singleton_self _))
termination_by (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).saturationMeasure
decreasing_by
  · simp only [List.toFinset_cons];
    exact LabelledSequent.saturationMeasure_impR (impRTarget?_some h₄).1 (impRTarget?_some h₄).2;
  · simp only [List.toFinset_cons];
    exact LabelledSequent.saturationMeasure_impL_left (impLTarget?_some h₅).1 (impLTarget?_some h₅).2.1;
  · simp only [List.toFinset_cons];
    exact LabelledSequent.saturationMeasure_impL_right (impLTarget?_some h₅).1 (impLTarget?_some h₅).2.2;
  · simp only [List.toFinset_cons];
    exact LabelledSequent.saturationMeasure_boxL
      (boxLTarget?_some h₆).1 (boxLTarget?_some h₆).2.1 (boxLTarget?_some h₆).2.2;
  · simp only [List.toFinset_cons];
    exact LabelledSequent.saturationMeasure_trans
      (transTarget?_some h₇).1 (transTarget?_some h₇).2.1 (transTarget?_some h₇).2.2;


/-! ### The outer proof search -/

section finders

variable (processed : Finset (LabelledFormula α)) (R : List LabelRel) (Γ Δ : List (LabelledFormula α))

/--
Finds a *looping* boxed formula: some `x ∶ □A` in the
succedent together with a predecessor `w` of `x` carrying `w ∶ □A` in the antecedent.

- [Neg14, Lemma 5.2]
-/
def loopTarget? : Option (Label × Label × Formula α) :=
  Δ.findSome? fun lf =>
    match lf with
    | ⟨x, □A⟩ => R.findSome? fun p =>
        if p.2 = x ∧ (p.1 ∶ □A) ∈ Γ then some (p.1, x, A) else none
    | _ => none

/-- Finds a boxed formula in the succedent that is still a `R□^Löb` candidate: not yet
processed *at its label* on the current branch, not closable by `axm` (`x ∶ □A ∉ Γ`)
and not closable by `loop` (no direct `R`-predecessor of `x` carries `□A` in the
antecedent).  The latter two checks are vacuous on saturated, loop-free leaves, but
provide the computable evidence needed by the termination measure `lobMeasure`. -/
def lobTarget? : Option (Label × Formula α) :=
  Δ.findSome? fun lf =>
    match lf with
    | ⟨x, □A⟩ =>
      if (x ∶ □A) ∈ processed ∨ (x ∶ □A) ∈ Γ ∨ ∃ p ∈ R, p.2 = x ∧ (p.1 ∶ □A) ∈ Γ then none
      else some (x, A)
    | _ => none

end finders

section finders

variable {processed : Finset (LabelledFormula α)} {R : List LabelRel} {Γ Δ : List (LabelledFormula α)}
variable {w x : Label} {A : Formula α}

lemma loopTarget?_some (h : loopTarget? R Γ Δ = some (w, x, A)) :
  (w, x) ∈ R.toFinset ∧ (w ∶ □A) ∈ Γ.toFinset ∧ (x ∶ □A) ∈ Δ.toFinset := by
  obtain ⟨lf, hlf, h1⟩ := List.exists_of_findSome?_eq_some h;
  obtain ⟨x', F⟩ := lf;
  cases F <;> try grind;
  case box B =>
    obtain ⟨p, hp, h2⟩ := List.exists_of_findSome?_eq_some h1;
    grind [List.mem_toFinset];

lemma lobTarget?_some (h : lobTarget? processed R Γ Δ = some (x, A)) :
  (x ∶ □A) ∈ Δ.toFinset ∧ (x ∶ □A) ∉ processed ∧ (x ∶ □A) ∉ Γ.toFinset ∧
  ∀ w, (w, x) ∈ R.toFinset → (w ∶ □A) ∉ Γ.toFinset := by
  obtain ⟨lf, hlf, h1⟩ := List.exists_of_findSome?_eq_some h;
  obtain ⟨x', F⟩ := lf;
  cases F <;> grind [List.mem_toFinset];

lemma loopTarget?_none (h : loopTarget? R Γ Δ = none)
  (hΔ : (x ∶ □A) ∈ Δ.toFinset) (hR : (w, x) ∈ R.toFinset) : (w ∶ □A) ∉ Γ.toFinset := by
  unfold loopTarget? at h;
  rw [List.findSome?_eq_none_iff] at h;
  have h1 := h (x ∶ □A) (List.mem_toFinset.mp hΔ);
  simp only [List.findSome?_eq_none_iff] at h1;
  have h2 := h1 (w, x) (List.mem_toFinset.mp hR);
  grind [List.mem_toFinset];

lemma lobTarget?_none (h : lobTarget? processed R Γ Δ = none) (hΔ : (x ∶ □A) ∈ Δ.toFinset) :
  (x ∶ □A) ∈ processed ∨ (x ∶ □A) ∈ Γ.toFinset ∨
  ∃ w, (w, x) ∈ R.toFinset ∧ (w ∶ □A) ∈ Γ.toFinset := by
  unfold lobTarget? at h;
  rw [List.findSome?_eq_none_iff] at h;
  have h1 := h (x ∶ □A) (List.mem_toFinset.mp hΔ);
  grind [List.mem_toFinset];

end finders


/-- Extends a family of values over the elements of a list by a value for a new head. -/
def consAllMem {β : Type v} [DecidableEq β] {f : β → Type w} {b : β} {l : List β}
  (p : f b) (ps : ∀ c ∈ l, f c) : ∀ c ∈ b :: l, f c :=
  fun c hc => if h : c = b then h ▸ p else ps c ((List.mem_cons.mp hc).resolve_left h)

mutual

/--
Proof search for `ProvableLabelledGentzen`:
saturate, then solve every stuck leaf (`searchLeaves`).  The parameter `processed` records,
*per label*, the boxed formulas already treated by `R□^Löb` on the current branch.

- [Neg14, Theorem 5.5]
-/
def search (processed : Finset (LabelledFormula α)) (R : List LabelRel)
  (Γ Δ : List (LabelledFormula α)) :
  Option (⊢ˡ! (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset)) :=
  -- Termination: every `R□^Löb` step strictly decreases the weighted measure
  -- `LabelledSequent.lobMeasure` (`lobMeasure_lob_lt`), which saturation never
  -- increases (`lobMeasure_le`).
  match saturate R Γ Δ with
  | .closed π => some π
  | .stuck leaves _ hlab hsf hmono k =>
    match searchLeaves processed ((R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).lobMeasure processed)
      leaves
      (fun L hL => LabelledSequent.lobMeasure_le (hlab L hL) (hsf L hL)
        (hmono L hL).1 (hmono L hL).2.1) with
    | some ps => some (k ps)
    | none => none
termination_by ((R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).lobMeasure processed, 1, 0)
decreasing_by
  apply Prod.Lex.right;
  exact Prod.Lex.left _ _ Nat.zero_lt_one;

/--
Solves every stuck leaf produced by `saturate`: a leaf is closed either by a looping
sequent (via `ProofLabelledGentzen.loop`), or by applying `R□^Löb`
(keeping the principal formula) to a boxed succedent formula not yet processed at its
label and recursing with `search`.  The parameter `m` bounds the `lobMeasure` of every
leaf (`hbound`).

- [Neg14, Lemma 5.2]
-/
def searchLeaves (processed : Finset (LabelledFormula α)) (m : ℕ)
  (leaves : List (List LabelRel × List (LabelledFormula α) × List (LabelledFormula α)))
  (hbound : ∀ L ∈ leaves, (LabelledSequent.ofLists L).lobMeasure processed ≤ m) :
  Option (∀ L ∈ leaves, ⊢ˡ! (LabelledSequent.ofLists L)) :=
  -- `m` together with `leaves.length` drives the lexicographic termination measure.
  match leaves, hbound with
  | [], _ => some (fun _ hL => nomatch hL)
  | ⟨Rl, Γl, Δl⟩ :: rest, hbound =>
    match h₁ : loopTarget? Rl Γl Δl with
    | some (w, x, A) =>
      match searchLeaves processed m rest (fun L hL => hbound L (List.mem_cons_of_mem _ hL)) with
      | some ps =>
        some (consAllMem
          (ProofLabelledGentzen.loop w x (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset).freshLabel A
            LabelledSequent.freshLabel_notMem
            (loopTarget?_some h₁).1 (loopTarget?_some h₁).2.1 (loopTarget?_some h₁).2.2)
          ps)
      | none => none
    | none =>
    match h₂ : lobTarget? processed Rl Γl Δl with
    | some (x, A) =>
      have hΔ : (x ∶ □A) ∈ Δl.toFinset := (lobTarget?_some h₂).1;
      have hP : (x ∶ □A) ∉ processed := (lobTarget?_some h₂).2.1;
      have hΓ : (x ∶ □A) ∉ Γl.toFinset := (lobTarget?_some h₂).2.2.1;
      have hpred : ∀ w, (w, x) ∈ Rl.toFinset → (w ∶ □A) ∉ Γl.toFinset :=
        (lobTarget?_some h₂).2.2.2;
      let y : Label := (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset).freshLabel;
      -- eagerly added transitive pairs (`Trans`-saturation would add them anyway)
      let preds : List Label := (Rl.filter (fun p => p.2 = x)).map Prod.fst;
      let R' : List LabelRel := preds.map (fun w => (w, y)) ++ (x, y) :: Rl;
      have hrelEq : R'.toFinset =
        insert (x, y)
          ((Rl.toFinset.filter (fun p => p.2 = x)).image (fun p => (p.1, y)) ∪ Rl.toFinset) := by
        ext p;
        simp only [R', preds, List.mem_toFinset, List.mem_append, List.mem_cons, List.mem_map,
          List.mem_filter, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
          Finset.mem_filter, decide_eq_true_eq];
        grind;
      have hlt : (R'.toFinset ⸴ ((y ∶ □A) :: Γl).toFinset ⟹ˡ ((y ∶ A) :: Δl).toFinset).lobMeasure
        (insert (x ∶ □A) processed) < m := by
        apply lt_of_lt_of_le ?_ (hbound (Rl, Γl, Δl) (by simp));
        rw [List.toFinset_cons, List.toFinset_cons, hrelEq];
        exact LabelledSequent.lobMeasure_lob_lt hΔ hP hΓ hpred LabelledSequent.freshLabel_notMem;
      match search (insert (x ∶ □A) processed) R' ((y ∶ □A) :: Γl) ((y ∶ A) :: Δl) with
      | some π =>
        match searchLeaves processed m rest (fun L hL => hbound L (List.mem_cons_of_mem _ hL)) with
        | some ps =>
          have hlab0 : x ∈ (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset).labels :=
            LabelledSequent.mem_labels_of_mem_suc (lf := x ∶ □A) hΔ;
          have hfresh : y ∉ (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ insert (x ∶ □A) Δl.toFinset).labels := by
            rw [LabelledSequent.labels_insert_suc_of_mem (lf := x ∶ □A) hlab0];
            exact LabelledSequent.freshLabel_notMem;
          some (consAllMem
            (by
              show ⊢ˡ! (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset);
              -- strip the eager transitive pairs by iterated `Trans`
              have π' : ⊢ˡ! ((preds.map (fun w => (w, y))).toFinset ∪ ((x, y) :: Rl).toFinset ⸴
                insert (y ∶ □A) Γl.toFinset ⟹ˡ insert (y ∶ A) Δl.toFinset) := by
                have hR' : R'.toFinset =
                  (preds.map (fun w => (w, y))).toFinset ∪ ((x, y) :: Rl).toFinset :=
                  List.toFinset_append;
                simpa only [List.toFinset_cons, hR'] using π;
              have hpreds : ∀ w ∈ preds, (w, x) ∈ ((x, y) :: Rl).toFinset := by
                intro w hw;
                simp only [preds, List.mem_map, List.mem_filter, decide_eq_true_eq] at hw;
                obtain ⟨p, ⟨hp, hpx⟩, rfl⟩ := hw;
                simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset];
                right;
                rwa [← hpx, Prod.mk.eta];
              have π'' : ⊢ˡ! (((x, y) :: Rl).toFinset ⸴
                insert (y ∶ □A) Γl.toFinset ⟹ˡ insert (y ∶ A) Δl.toFinset) :=
                ProofLabelledGentzen.transMany x y preds hpreds (by simp) π';
              rw [show Δl.toFinset = insert (x ∶ □A) Δl.toFinset
                from (Finset.insert_eq_self.mpr hΔ).symm];
              exact ProofLabelledGentzen.boxRLob x y A hfresh
                (by simpa only [List.toFinset_cons] using π''))
            ps)
        | none => none
      | none => none
    | none => none
termination_by (m, 0, leaves.length)
decreasing_by
  · apply Prod.Lex.right;
    apply Prod.Lex.right;
    simp;
  · exact Prod.Lex.left _ _ hlt;
  · apply Prod.Lex.right;
    apply Prod.Lex.right;
    simp;

end

/-- Entry point of the proof search: no boxed formula has been processed yet. -/
def search0 (R : List LabelRel) (Γ Δ : List (LabelledFormula α)) :
  Option (⊢ˡ! (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset)) :=
  search ∅ R Γ Δ

/-- Whether `search0` succeeds is decidable: it is a computable `Bool`-valued function
of its (finite, decidable) inputs. -/
instance search0.decidableIsSome (R : List LabelRel) (Γ Δ : List (LabelledFormula α)) :
  Decidable (search0 R Γ Δ).isSome := inferInstance

/-! Sanity checks: the Löb axiom `□(□a 🡒 a) 🡒 □a` and the `K` axiom are found
automatically; the `T` axiom `□a 🡒 a` and `□a` itself, which are not theorems of
`GL`, are rejected. -/

#guard (search0 (α := ℕ) [] [] [0 ∶ (□(□#0 🡒 #0) 🡒 □#0)]).isSome
#guard (search0 (α := ℕ) [] [] [0 ∶ (□(#0 🡒 #1) 🡒 □#0 🡒 □#1)]).isSome
#guard (search0 (α := ℕ) [] [] [0 ∶ (□#0 🡒 □□#0)]).isSome
#guard (search0 (α := ℕ) [] [] [0 ∶ (□#0 🡒 #0)]).isNone
#guard (search0 (α := ℕ) [] [] [0 ∶ (□#0)]).isNone

/-! Phase 0 checks (completeness plan for `search`/`searchLeaves`): sanity checks that
probed whether the earlier formula-only `processed : Finset (Formula α)` tracking
(ignoring which label a boxed formula sits at) could cause spurious failure — kept as
regression tests for the label-aware redesign. -/

-- Two-level nested Löb-processing chain (root 0 → fresh y1 → fresh y2): still found.
#guard (search0 (α := ℕ) [] [] [0 ∶ (□(□(□#0 🡒 #0) 🡒 □#0))]).isSome

-- Same box content `□#0` needed at label `0` on *both* sides of a conjunction
-- (distinct Löb instances sharing the atom `#0`, but staying at the same label): still found.
#guard (search0 (α := ℕ) [] [] [0 ∶ ((□(□#0 🡒 #0) 🡒 □#0) ⋏ (□(□#0 🡒 #0) 🡒 □#0))]).isSome

-- Distinct atoms, both needing their own Löb-processing at the same label: still found.
#guard (search0 (α := ℕ) [] [] [0 ∶ ((□(□#0 🡒 #0) 🡒 □#0) ⋏ (□(□#1 🡒 #1) 🡒 □#1))]).isSome

-- Adversarial *direct* multi-label input: two unrelated root labels `0`, `1`, both carrying
-- the same theorem `□(□a 🡒 a) 🡒 □a` in the succedent (a disjunctive goal, individually
-- closable at either label): still found (does not require touching the other label).
#guard (search0 (α := ℕ) [] [] [0 ∶ (□(□#0 🡒 #0) 🡒 □#0), 1 ∶ (□(□#0 🡒 #0) 🡒 □#0)]).isSome

-- Adversarial direct multi-label input with *no* supporting structure: two unrelated labels
-- both claiming `□a` in the succedent, with empty antecedent. This is genuinely GL-invalid
-- (no shared witness world), so rejection here is the *correct* answer, not evidence of a bug.
#guard (search0 (α := ℕ) [] [] [0 ∶ (□#0 : Formula ℕ), 1 ∶ (□#0 : Formula ℕ)]).isNone

/-! ### Why `processed` must be label-aware

Recording processed `R□^Löb` targets merely as `processed : Finset (Formula α)`, ignoring
at *which label* a boxed formula was treated, is unsound: two `R□^Löb` applications can
create sibling labels that are incomparable in the transitive closure, so a witness
recorded for one label may be unreachable from the other, and the boxed formula must be
processed again at the sibling. `search0` therefore tracks
`processed : Finset (LabelledFormula α)`, with the Negri-style termination measure
`LabelledSequent.lobMeasure` accounting for this repeated processing across sibling
labels. The example below, `□□⊥ 🡒 (∼□a 🡒 □□a)`, exercises exactly this pattern.

- [Neg14, Theorem 5.5]
-/

section incompleteness

/-- A formula provable as `ProvableLabelledGentzen` whose derivation needs a boxed
formula processed at two sibling labels (see the section documentation):
`□□⊥ 🡒 (∼□a 🡒 □□a)`. -/
def lobProcessedCounterexample : Formula ℕ := □□⊥ 🡒 (∼□#0 🡒 □□#0)

/-- `lobProcessedCounterexample` is provable as `ProvableLabelledGentzen`. -/
lemma provable_lobProcessedCounterexample :
  ⊢ˡ ((∅ : Finset LabelRel) ⸴ (∅ : Finset (LabelledFormula ℕ)) ⟹ˡ {0 ∶ lobProcessedCounterexample}) := by
  -- Two `impR`s and `R□^Löb` at `0 ∶ □□a` (fresh label `1`), the antecedent `□□⊥` yields
  -- `1 ∶ □⊥` by `L□`, so a second `R□^Löb` at `1 ∶ □a` (fresh label `2`) closes by `L□`
  -- (giving `2 ∶ ⊥`) and `botL`.
  rw [show ({0 ∶ lobProcessedCounterexample} : Finset (LabelledFormula ℕ)) =
    insert (0 ∶ (□□⊥ 🡒 (∼□#0 🡒 □□#0))) ∅ by rfl];
  apply ProvableLabelledGentzen.impR (x := 0);
  apply ProvableLabelledGentzen.impR (x := 0);
  apply ProvableLabelledGentzen.boxRLob (x := 0) (y := 1) (A := □#0) (hfresh := by decide);
  apply ProvableLabelledGentzen.boxL (x := 0) (y := 1) (A := □⊥) (hxy := by grind) (hxA := by grind);
  apply ProvableLabelledGentzen.boxRLob (x := 1) (y := 2) (A := #0) (hfresh := by decide);
  apply ProvableLabelledGentzen.boxL (x := 1) (y := 2) (A := ⊥) (hxy := by grind) (hxA := by grind);
  exact ProvableLabelledGentzen.botL_mem 2 (by grind);

-- ... and `search0` finds it.
#guard (search0 [] [] [0 ∶ lobProcessedCounterexample]).isSome

/-! The mechanism, machine-checked step by step on the subformula `∼□a 🡒 □□a`
(a non-theorem, whose search tree exhibits the sibling branching): the sibling
labels `1`, `2` still arise, but the orphaned `2 ∶ □a` is now a fresh `R□^Löb`
target at label `2`. -/

/-- The stuck leaves of `saturate` (empty if the sequent was closed); test-only. -/
private def stuckLeaves (R : List LabelRel) (Γ Δ : List (LabelledFormula ℕ)) :
  List (List LabelRel × List (LabelledFormula ℕ) × List (LabelledFormula ℕ)) :=
  match saturate R Γ Δ with
  | .closed _ => []
  | .stuck leaves _ _ _ _ _ => leaves

-- Saturating the root puts `0 ∶ □a` *before* `0 ∶ □□a` in the succedent list.
#guard stuckLeaves [] [] [0 ∶ (∼□#0 🡒 □□#0)] =
  [([], [0 ∶ ∼□#0], [0 ∶ □#0, 0 ∶ □□#0, 0 ∶ (∼□#0 🡒 □□#0)])]

-- Hence the first `R□^Löb` processes `□a` at label `0` (not `□□a`) ...
#guard lobTarget? (∅ : Finset (LabelledFormula ℕ)) [] [0 ∶ ∼□#0]
    [0 ∶ □#0, 0 ∶ □□#0, 0 ∶ (∼□#0 🡒 □□#0)] =
  some (0, #0)

-- ... creating the fresh child `1`; the resulting sequent is already saturated ...
#guard stuckLeaves [(0, 1)] [1 ∶ □#0, 0 ∶ ∼□#0]
    [1 ∶ #0, 0 ∶ □#0, 0 ∶ □□#0, 0 ∶ (∼□#0 🡒 □□#0)] =
  [([(0, 1)], [1 ∶ □#0, 0 ∶ ∼□#0], [1 ∶ #0, 0 ∶ □#0, 0 ∶ □□#0, 0 ∶ (∼□#0 🡒 □□#0)])]

-- ... and the second `R□^Löb` processes `□□a` again at label `0` (not at `1`),
-- creating the fresh child `2` as a *sibling* of `1` ...
#guard lobTarget? ({0 ∶ □#0} : Finset (LabelledFormula ℕ)) [(0, 1)] [1 ∶ □#0, 0 ∶ ∼□#0]
    [1 ∶ #0, 0 ∶ □#0, 0 ∶ □□#0, 0 ∶ (∼□#0 🡒 □□#0)] =
  some (0, □#0)

-- ... reaching a leaf with `2 ∶ □a` in the succedent whose only would-be witness
-- (`1 ∶ a`) is unreachable from `2` (`R = {(0,2), (0,1)}` is not a chain):
#guard stuckLeaves [(0, 2), (0, 1)] [2 ∶ □□#0, 1 ∶ □#0, 0 ∶ ∼□#0]
    [2 ∶ □#0, 1 ∶ #0, 0 ∶ □#0, 0 ∶ □□#0, 0 ∶ (∼□#0 🡒 □□#0)] =
  [([(0, 2), (0, 1)], [2 ∶ □□#0, 1 ∶ □#0, 0 ∶ ∼□#0],
    [2 ∶ □#0, 1 ∶ #0, 0 ∶ □#0, 0 ∶ □□#0, 0 ∶ (∼□#0 🡒 □□#0)])]

-- `loopTarget?` does not fire on this leaf; the formula-only bookkeeping used to
-- also block `lobTarget?` here (`□a ∈ processed`), abandoning the leaf ...
#guard loopTarget? [(0, 2), (0, 1)] [2 ∶ □□#0, 1 ∶ □#0, 0 ∶ ∼□#0]
    [2 ∶ □#0, 1 ∶ #0, 0 ∶ □#0, 0 ∶ □□#0, 0 ∶ (∼□#0 🡒 □□#0)] = none

-- ... but the label-aware `lobTarget?` now correctly reprocesses `□a` at label `2`.
#guard lobTarget? ({0 ∶ □#0, 0 ∶ □□#0} : Finset (LabelledFormula ℕ)) [(0, 2), (0, 1)]
    [2 ∶ □□#0, 1 ∶ □#0, 0 ∶ ∼□#0]
    [2 ∶ □#0, 1 ∶ #0, 0 ∶ □#0, 0 ∶ □□#0, 0 ∶ (∼□#0 🡒 □□#0)] =
  some (2, #0)

end incompleteness

end LabelledGentzen
