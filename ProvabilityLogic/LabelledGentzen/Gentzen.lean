module

public import ProvabilityLogic.Gentzen.Kripke
public import ProvabilityLogic.LabelledGentzen.Kripke

@[expose]
public section

open scoped Formula

/-!
Syntactic embedding of the label-free Gentzen calculus (`ProvableGentzen`/`⊢ᵍ`) into
Negri's labelled sequent calculus (`ProvableLabelledGentzen`/`⊢ˡ`).

The embedding is by structural induction on `ProvableGentzen` (via `ProvableGentzen.rec`),
through the generalized statement `ProvableGentzen.toLabelledGentzenAux`: each antecedent
formula `B` of the label-free sequent is represented in the labelled antecedent either
directly as `z ∶ B`, or (for `B = □C`) as `x ∶ □C` at some `R`-predecessor `x` of `z`.
The latter representation is what makes the `boxGL` case go through: after `R□^Löb`
introduces a fresh label `y`, the boxed context `Γ.box` stays at `z`, and is transferred to
`y` on demand by `Trans` (`ProvableLabelledGentzen.transMany`) and `L□`
(`ProvableLabelledGentzen.boxLMany`), while a boxed formula meeting its succedent copy across
a relational atom is closed by `loop`.
-/

open LabelledGentzen

variable {α : Type u} [DecidableEq α]

/-- Translation of a label-free sequent into a labelled sequent: every formula
is labelled with `z`, and the relational context is empty. -/
def Sequent.toLabelled (z : Label) (S : Sequent α) : LabelledSequent α :=
  ∅ ⸴ S.ant.image (z ∶ ·) ⟹ˡ S.suc.image (z ∶ ·)


namespace LabelledGentzen

variable {R : Finset LabelRel} {Γ Δ Θ : Finset (LabelledFormula α)}
         {x y z : Label} {A B : Formula α}

namespace ProvableLabelledGentzen

/-- Iterated `Trans`: relational atoms `(x, y)` for all `x ∈ T` may be assumed,
provided `(z, y) ∈ R` and `(x, z) ∈ R` for each `x ∈ T`. -/
lemma transMany (T : Finset Label) (hzy : (z, y) ∈ R) (hT : ∀ x ∈ T, (x, z) ∈ R)
  (π : ⊢ˡ ((R ∪ T.image (·, y)) ⸴ Γ ⟹ˡ Δ)) : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) := by
  induction T using Finset.induction generalizing R with
  | empty => simpa using π;
  | insert x T hxT ih =>
    apply trans (hxy := hT x (by simp)) (hyz := hzy);
    apply ih (by grind) (by grind);
    apply wkRel π;
    intro p hp;
    simp only [Finset.image_insert, Finset.mem_union, Finset.mem_insert] at hp ⊢;
    grind;

/-- Iterated `L□`: labelled formulas `y ∶ B` for all `(x, B) ∈ T` may be assumed,
provided `(x, y) ∈ R` and `x ∶ □B ∈ Γ` for each `(x, B) ∈ T`. -/
lemma boxLMany (T : Finset (Label × Formula α)) (hT : ∀ p ∈ T, (p.1, y) ∈ R ∧ (p.1 ∶ □p.2) ∈ Γ)
  (π : ⊢ˡ (R ⸴ (Γ ∪ T.image (fun p => y ∶ p.2)) ⟹ˡ Δ)) : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) := by
  induction T using Finset.induction generalizing Γ with
  | empty => simpa using π;
  | insert p T hpT ih =>
    apply boxL (hT p (by simp)).1 (hT p (by simp)).2;
    apply ih (fun q hq =>
      ⟨(hT q (Finset.mem_insert_of_mem hq)).1,
        Finset.mem_insert_of_mem (hT q (Finset.mem_insert_of_mem hq)).2⟩);
    apply wkAnt π;
    intro f hf;
    simp only [Finset.image_insert, Finset.mem_union, Finset.mem_insert] at hf ⊢;
    grind;

end ProvableLabelledGentzen

/-- The boxed formula of `f` that can be unfolded at `y`: `some (x, B)` when
`f = x ∶ □B` with `(x, y) ∈ R`, and `none` otherwise. -/
def LabelledFormula.boxTarget (y : Label) (R : Finset LabelRel) :
  LabelledFormula α → Option (Label × Formula α)
  | ⟨x, □B⟩ => if (x, y) ∈ R then some (x, B) else none
  | _ => none

omit [DecidableEq α] in
@[grind =]
lemma LabelledFormula.boxTarget_eq_some {f : LabelledFormula α} {p : Label × Formula α} :
  f.boxTarget y R = some p ↔ f = (p.1 ∶ □p.2) ∧ (p.1, y) ∈ R := by
  obtain ⟨x', A'⟩ := f;
  obtain ⟨x, B⟩ := p;
  (cases A' <;> simp [LabelledFormula.boxTarget]);
  grind;

/-- All pairs `(x, B)` with `x ∶ □B ∈ Θ` and `(x, y) ∈ R`: the boxed formulas of `Θ`
that can be unfolded at `y` by `L□`. -/
def boxTargets (y : Label) (R : Finset LabelRel) (Θ : Finset (LabelledFormula α)) :
  Finset (Label × Formula α) :=
  Θ.filterMap (LabelledFormula.boxTarget y R) (by
    intro f f' p hf hf';
    rw [Option.mem_def, LabelledFormula.boxTarget_eq_some] at hf hf';
    grind)

omit [DecidableEq α] in
@[simp, grind =]
lemma mem_boxTargets : (x, B) ∈ boxTargets y R Θ ↔ (x, y) ∈ R ∧ (x ∶ □B) ∈ Θ := by
  simp only [boxTargets, Finset.mem_filterMap, LabelledFormula.boxTarget_eq_some];
  grind;

end LabelledGentzen


namespace ProvableGentzen

/--
  Generalized embedding statement: if `S` is `ProvableGentzen` and every antecedent
  formula `B` of `S` is represented in `Θ` either as `z ∶ B`, or (for `B = □C`)
  as `x ∶ □C` at some `R`-predecessor `x` of `z`, then the labelled sequent
  `R ⸴ Θ ⟹ˡ S.suc.image (z ∶ ·)` is `ProvableLabelledGentzen`.
-/
lemma toLabelledGentzenAux {S : Sequent α} (h : ⊢ᵍ S) :
  ∀ (z : Label) (R : Finset LabelRel) (Θ : Finset (LabelledFormula α)),
  (∀ B ∈ S.ant, (z ∶ B) ∈ Θ ∨ ∃ x C, B = □C ∧ (x, z) ∈ R ∧ (x ∶ □C) ∈ Θ) →
  ⊢ˡ (R ⸴ Θ ⟹ˡ S.suc.image (z ∶ ·)) := by
  induction h using ProvableGentzen.rec with
  | axm A =>
    intro z R Θ H;
    simp only [Finset.image_singleton];
    if hzA : (z ∶ A) ∈ Θ then
      exact ProvableLabelledGentzen.union z A hzA (by simp);
    else
      have hA : ∃ x C, A = □C ∧ (x, z) ∈ R ∧ (x ∶ □C) ∈ Θ := (H A (by simp)).resolve_left hzA;
      clear hzA H;
      cases A with
      | box C =>
        have hex : ∃ x : Label, (x, z) ∈ R ∧ (x ∶ □C) ∈ Θ := by grind;
        obtain ⟨w, hwz, hwC⟩ := hex;
        exact ProvableLabelledGentzen.loop w z C hwz hwC (by simp);
      | atom a => simp at hA;
      | bot => simp at hA;
      | imp B C => simp at hA;
  | botL =>
    intro z R Θ H;
    have hz : (z ∶ (⊥ : Formula α)) ∈ Θ := by have := H ⊥ (by simp); grind;
    exact ProvableLabelledGentzen.botL_mem z hz;
  | wkL h h' ih =>
    intro z R Θ H;
    exact ih z R Θ (fun B hB => H B (h' hB));
  | wkR h h' ih =>
    intro z R Θ H;
    exact ProvableLabelledGentzen.wkSuc (ih z R Θ H) (Finset.image_subset_image h');
  | @impL Γ Δ A B h₁ h₂ ih₁ ih₂ =>
    intro z R Θ H;
    have hAB : (z ∶ A 🡒 B) ∈ Θ := by have := H (A 🡒 B) (by simp); grind;
    have h₁ := ih₁ z R Θ (fun C hC => H C (Finset.mem_insert_of_mem hC));
    have h₂ := ih₂ z R (insert (z ∶ B) Θ) (fun C hC => by
      rcases Finset.mem_insert.mp hC with rfl | hC;
      . exact Or.inl (by simp);
      . have := H C (Finset.mem_insert_of_mem hC); grind;
    );
    rw [(show Θ = insert (z ∶ A 🡒 B) Θ by grind)];
    simp only [Finset.image_insert] at h₁;
    exact ProvableLabelledGentzen.impL h₁ h₂;
  | @impR Γ Δ A B h ih =>
    intro z R Θ H;
    have h := ih z R (insert (z ∶ A) Θ) (fun C hC => by
      rcases Finset.mem_insert.mp hC with rfl | hC;
      . exact Or.inl (by simp);
      . have := H C hC; grind;
    );
    simp only [Finset.image_insert] at h ⊢;
    exact ProvableLabelledGentzen.impR h;
  | @boxGL Γ A h ih =>
    intro z R Θ H;
    simp only [Finset.image_singleton];
    rw [← insert_empty_eq];
    apply ProvableLabelledGentzen.boxRLob (x := z) (A := A)
      (y := (R ⸴ Θ ⟹ˡ insert (z ∶ □A) ∅).freshLabel) (hfresh := LabelledSequent.freshLabel_notMem);
    generalize (R ⸴ Θ ⟹ˡ insert (z ∶ □A) ∅).freshLabel = y;
    -- transfer the relational atoms `(x, z) ∈ R` to `(x, y)` by `Trans`
    apply ProvableLabelledGentzen.transMany (z := z) (y := y)
      (T := (R.filter (fun p => p.2 = z)).image Prod.fst)
      (by grind) (by intro x hx; simp at hx; grind);
    set R' := insert (z, y) R ∪ ((R.filter (fun p => p.2 = z)).image Prod.fst).image (·, y)
      with hR';
    -- unfold every available boxed formula at `y` by `L□`
    apply ProvableLabelledGentzen.boxLMany (y := y) (T := boxTargets y R' (insert (y ∶ □A) Θ))
      (by rintro ⟨x, B⟩ hp; exact mem_boxTargets.mp hp);
    have hzy : (z, y) ∈ R' := by grind;
    have hsat : ∀ x, (x, z) ∈ R → (x, y) ∈ R' := by
      intro x hxz;
      apply Finset.mem_union_right;
      have h₁ : (x, z) ∈ R.filter (fun p => p.2 = z) := Finset.mem_filter.mpr ⟨hxz, rfl⟩;
      have h₂ : x ∈ (R.filter (fun p => p.2 = z)).image Prod.fst := Finset.mem_image_of_mem _ h₁;
      exact Finset.mem_image_of_mem _ h₂;
    have h := ih y R'
      (insert (y ∶ □A) Θ ∪ (boxTargets y R' (insert (y ∶ □A) Θ)).image (fun p => y ∶ p.2))
      (fun E hE => by
        rcases Finset.mem_insert.mp hE with rfl | hE;
        . exact Or.inl (by grind);
        . rcases Finset.mem_union.mp hE with hEΓ | hEbox;
          . -- `E ∈ Γ` is unfolded at `y` by `boxLMany`
            left;
            apply Finset.mem_union_right;
            rcases H (□E) (Finset.mem_image_of_mem _ hEΓ) with hzE | ⟨x, C, hEC, hxz, hxC⟩;
            . exact Finset.mem_image_of_mem _ (mem_boxTargets.mpr ⟨hzy, by grind⟩);
            . obtain rfl : E = C := by grind;
              exact Finset.mem_image_of_mem _ (mem_boxTargets.mpr ⟨hsat x hxz, by grind⟩);
          . -- `□B ∈ Γ.box` stays represented at its old label
            obtain ⟨B, hBΓ, rfl⟩ := Finset.mem_image.mp hEbox;
            right;
            rcases H (□B) hEbox with hzB | ⟨x, C, hBC, hxz, hxC⟩;
            . exact ⟨z, B, rfl, hzy, by grind⟩;
            . obtain rfl : B = C := by grind;
              exact ⟨x, B, rfl, hsat x hxz, by grind⟩;
      );
    simp only [Finset.image_singleton] at h;
    rw [insert_empty_eq];
    exact h;

/-- Embedding of `ProvableGentzen` into `ProvableLabelledGentzen`: a proof of `S` yields a proof
of `S.toLabelled z` for any label `z`. -/
lemma toLabelledGentzen (z : Label) {S : Sequent α} (h : ⊢ᵍ S) : ⊢ˡ (S.toLabelled z) :=
  toLabelledGentzenAux h z ∅ (S.ant.image (z ∶ ·)) (fun _ hB => Or.inl (Finset.mem_image_of_mem _ hB))

end ProvableGentzen


/-- Embedding of `ProvableGentzen` into `ProvableLabelledGentzen`. -/
theorem ProvableGentzen.toLabelled (z : Label) {S : Sequent α} (h : ⊢ᵍ S) : ⊢ˡ (S.toLabelled z) :=
  ProvableGentzen.toLabelledGentzen z h


/-- Converse embedding: a proof of `A` at label `x` in `ProvableLabelledGentzen`
yields a proof of `A` in `ProvableGentzen`. -/
theorem ProvableLabelledGentzen.toGentzen {x : Label} {A : Formula α}
  (h : ⊢ˡ (∅ ⸴ ∅ ⟹ˡ {x ∶ A})) : ⊢ᵍ (∅ ⟹ {A}) := by
  -- via Kripke semantics: soundness of `ProvableLabelledGentzen` on `GL` models
  -- (`LabelledGentzen.ProvableLabelledGentzen.Kripke.soundness_formula`) specialized to finite
  -- `GL` models, composed with completeness of `ProvableGentzen` for finite `GL` models
  -- (`ProvableGentzen.Kripke.completeness`)
  apply ProvableGentzen.Kripke.completeness;
  intro κ _ M _ w;
  exact Model.World.forces_singleton_sequent.mpr
    (LabelledGentzen.ProvableLabelledGentzen.Kripke.soundness_formula h M w);

/-- `ProvableGentzen` and `ProvableLabelledGentzen` agree, for a formula `A` at any label `x`. -/
theorem iff_provableGentzen_provableLabelledGentzen {x : Label} {A : Formula α} :
  ⊢ᵍ (∅ ⟹ {A}) ↔ ⊢ˡ (∅ ⸴ ∅ ⟹ˡ {x ∶ A}) := by
  constructor;
  . intro h;
    simpa [Sequent.toLabelled] using ProvableGentzen.toLabelled x h;
  . exact ProvableLabelledGentzen.toGentzen;

end
