module

public import ProvabilityLogic.Gentzen.Kripke

@[expose]
public section

open scoped Formula

variable {α : Type u} [DecidableEq α]

inductive GentzenWithCutProof : Sequent α → Type u
| axm (A) : GentzenWithCutProof ({A} ⟹ {A})
| botL : GentzenWithCutProof ({⊥} ⟹ ∅)
| wkL  {Γ Γ' Δ}  : GentzenWithCutProof (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → GentzenWithCutProof (Γ' ⟹ Δ)
| wkR  {Γ Δ Δ'}  : GentzenWithCutProof (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → GentzenWithCutProof (Γ ⟹ Δ')
| impL {Γ Δ A B} : GentzenWithCutProof (Γ ⟹ (insert A Δ)) → GentzenWithCutProof (insert B Γ ⟹ Δ) → GentzenWithCutProof ((insert (A 🡒 B) Γ) ⟹ Δ)
| impR {Γ Δ A B} : GentzenWithCutProof ((insert A Γ) ⟹ (insert B Δ)) → GentzenWithCutProof (Γ ⟹ (insert (A 🡒 B) Δ))
| boxGL {Γ A} : GentzenWithCutProof ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) → GentzenWithCutProof (Γ.box ⟹ {□A})
| cut {Γ₁ Γ₂ Δ₁ Δ₂ A} : GentzenWithCutProof (Γ₁ ⟹ insert A Δ₁) → GentzenWithCutProof (insert A Γ₂ ⟹ Δ₂) → GentzenWithCutProof (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂)
prefix:120 "⊢ᵍᶜ! " => GentzenWithCutProof

abbrev GentzenWithCutProvable (S : Sequent α) : Prop := Nonempty (⊢ᵍᶜ! S)
prefix:120 "⊢ᵍᶜ " => GentzenWithCutProvable


def GentzenWithCutProof.ofGentzenProof {S : Sequent α} : ⊢ᵍ! S → ⊢ᵍᶜ! S
| .axm A => .axm A
| .botL => .botL
| .wkL h h' => .wkL (ofGentzenProof h) h'
| .wkR h h' => .wkR (ofGentzenProof h) h'
| .impL h₁ h₂ => .impL (ofGentzenProof h₁) (ofGentzenProof h₂)
| .impR h => .impR (ofGentzenProof h)
| .boxGL h => .boxGL (ofGentzenProof h)

namespace GentzenWithCutProvable

variable {S : Sequent α} {A B : Formula α} {Γ Γ' Γ₁ Γ₂ Δ Δ' Δ₁ Δ₂ : FormulaFinset α}

theorem of_without_cut : ⊢ᵍ S → ⊢ᵍᶜ S := λ ⟨p⟩ => ⟨GentzenWithCutProof.ofGentzenProof p⟩

lemma axm (A : Formula α) : ⊢ᵍᶜ ({A} ⟹ {A}) := ⟨GentzenWithCutProof.axm A⟩
lemma botL : ⊢ᵍᶜ ({⊥} ⟹ ∅ : Sequent α) := ⟨GentzenWithCutProof.botL⟩
lemma wkL (h : ⊢ᵍᶜ (Γ ⟹ Δ)) (h' : Γ ⊆ Γ') : ⊢ᵍᶜ (Γ' ⟹ Δ) := ⟨GentzenWithCutProof.wkL h.some h'⟩
lemma wkR (h : ⊢ᵍᶜ (Γ ⟹ Δ)) (h' : Δ ⊆ Δ') : ⊢ᵍᶜ (Γ ⟹ Δ') := ⟨GentzenWithCutProof.wkR h.some h'⟩
lemma impL (h₁ : ⊢ᵍᶜ (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍᶜ (insert B Γ ⟹ Δ)) : ⊢ᵍᶜ ((insert (A 🡒 B) Γ) ⟹ Δ) := ⟨GentzenWithCutProof.impL h₁.some h₂.some⟩
lemma impR (h : ⊢ᵍᶜ ((insert A Γ) ⟹ (insert B Δ))) : ⊢ᵍᶜ (Γ ⟹ (insert (A 🡒 B) Δ)) := ⟨GentzenWithCutProof.impR h.some⟩
lemma boxGL (h : ⊢ᵍᶜ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})) : ⊢ᵍᶜ (Γ.box ⟹ {□A}) := ⟨GentzenWithCutProof.boxGL h.some⟩
lemma cut (h₁ : ⊢ᵍᶜ (Γ₁ ⟹ insert A Δ₁)) (h₂ : ⊢ᵍᶜ (insert A Γ₂ ⟹ Δ₂)) : ⊢ᵍᶜ (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂) := ⟨GentzenWithCutProof.cut h₁.some h₂.some⟩

lemma rec
  {motive : (S : Sequent α) → ⊢ᵍᶜ S → Prop}
  (axm : ∀ A : Formula α, motive ({A} ⟹ {A}) (GentzenWithCutProvable.axm A))
  (botL : motive ({⊥} ⟹ ∅ : Sequent α) GentzenWithCutProvable.botL)
  (wkL : ∀ {Γ Γ' Δ} (h : ⊢ᵍᶜ (Γ ⟹ Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹ Δ) h → motive (Γ' ⟹ Δ) (wkL h h'))
  (wkR : ∀ {Γ Δ Δ'} (h : ⊢ᵍᶜ (Γ ⟹ Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹ Δ) h → motive (Γ ⟹ Δ') (wkR h h'))
  (impL : ∀ {Γ Δ A B} (h₁ : ⊢ᵍᶜ (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍᶜ (insert B Γ ⟹ Δ)),
    motive (Γ ⟹ insert A Δ) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive ((insert (A 🡒 B) Γ) ⟹ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {Γ Δ A B} (h : ⊢ᵍᶜ ((insert A Γ) ⟹ (insert B Δ))),
    motive ((insert A Γ) ⟹ (insert B Δ)) h → motive (Γ ⟹ (insert (A 🡒 B) Δ)) (impR h)
  )
  (boxGL : ∀ {Γ A} (h : ⊢ᵍᶜ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})),
    motive ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) h → motive (Γ.box ⟹ {□A}) (boxGL h)
  )
  (cut : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A}
    (h₁ : ⊢ᵍᶜ (Γ₁ ⟹ insert A Δ₁)) (h₂ : ⊢ᵍᶜ (insert A Γ₂ ⟹ Δ₂)),
    (motive (Γ₁ ⟹ insert A Δ₁) h₁) → (motive (insert A Γ₂ ⟹ Δ₂) h₂) →
    motive (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂) (GentzenWithCutProvable.cut h₁ h₂)
  )
  : ∀ {S : Sequent α} (h : ⊢ᵍᶜ S), motive S h := by
    rintro S ⟨h⟩;
    induction h with
    | axm A => apply axm;
    | botL => apply botL;
    | wkL h h' ih => apply wkL ⟨h⟩ h' ih;
    | wkR h h' ih => apply wkR ⟨h⟩ h' ih;
    | cut h₁ h₂ ih₁ ih₂ => apply cut ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;
    | impL h₁ h₂ ih₁ ih₂ => apply impL ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;
    | impR h ih => apply impR ⟨h⟩ ih;
    | boxGL h ih => apply boxGL ⟨h⟩ ih;

end GentzenWithCutProvable


namespace ProvableGentzen

variable {S : Sequent α} {A B : Formula α}

/-- Cut-elimination: any sequent provable with the cut rule (`⊢ᵍᶜ`) is also provable without it (`⊢ᵍ`). -/
theorem of_with_cut {S : Sequent α} : ⊢ᵍᶜ S → ⊢ᵍ S := by
  intro h;
  induction h using GentzenWithCutProvable.rec with
  | axm A => exact ProvableGentzen.axm A
  | botL => exact ProvableGentzen.botL
  | wkL _ h ih => exact ProvableGentzen.wkL ih h
  | wkR _ h ih => exact ProvableGentzen.wkR ih h
  | impL _ _ ih₁ ih₂ => exact ProvableGentzen.impL ih₁ ih₂
  | impR _ ih => exact ProvableGentzen.impR ih
  | boxGL _ ih => exact ProvableGentzen.boxGL ih
  | cut _ _ ih₁ ih₂ =>
    -- The cut rule has no direct syntactic elimination here; instead we argue
    -- semantically via completeness, using soundness of both cut premises.
    apply Kripke.completeness;
    rintro κ _ M _ x;
    have := Kripke.finite_soundness ih₁ M x;
    have := Kripke.finite_soundness ih₂ M x;
    grind;
alias cut_elimination := of_with_cut

theorem mdp : ⊢ᵍ (∅ ⟹ {A 🡒 B}) → ⊢ᵍ (∅ ⟹ {A}) → ⊢ᵍ (∅ ⟹ {B}) := λ p q => by
  replace p : ⊢ᵍᶜ (insert A ∅ ⟹ {B}) := GentzenWithCutProvable.of_without_cut $ deduction_theorem.mpr p;
  replace q : ⊢ᵍᶜ (∅ ⟹ insert A ∅) := GentzenWithCutProvable.of_without_cut q;
  exact cut_elimination $ GentzenWithCutProvable.cut q p;

end ProvableGentzen

end
