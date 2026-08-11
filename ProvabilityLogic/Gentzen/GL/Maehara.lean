module

public import ProvabilityLogic.Logic.GL.Basic

@[expose]
public section

open scoped Formula

variable {α : Type u} [DecidableEq α]

namespace LogicGL

namespace FormulaFinset

variable {Γ Δ : FormulaFinset α} {A B : Formula α}

@[simp, grind =]
lemma box_insert (A : Formula α) (Γ : FormulaFinset α) : (insert A Γ).box = insert (□A) Γ.box := Finset.image_insert _ _ _

end FormulaFinset



structure PartitionOf (S : Sequent α) where
  Γ₁ : FormulaFinset α
  Γ₂ : FormulaFinset α
  Δ₁ : FormulaFinset α
  Δ₂ : FormulaFinset α
  Γ_ant : S.ant = Γ₁ ∪ Γ₂
  Δ_suc : S.suc = Δ₁ ∪ Δ₂
  Γ_disj : Disjoint Γ₁ Γ₂
  Δ_disj : Disjoint Δ₁ Δ₂

namespace PartitionOf

variable {A B : Formula α}

attribute [grind .]
  PartitionOf.Γ_ant
  PartitionOf.Δ_suc
  PartitionOf.Γ_disj
  PartitionOf.Δ_disj

protected abbrev singleton (A : Formula α) : PartitionOf (∅ ⟹ {A}) where
  Γ₁ := ∅
  Γ₂ := ∅
  Δ₁ := {A}
  Δ₂ := ∅
  Γ_ant := by simp
  Δ_suc := by simp
  Γ_disj := by simp
  Δ_disj := by simp

protected abbrev ss (A B : Formula α) : PartitionOf ({A} ⟹ {B}) where
  Γ₁ := {A}
  Γ₂ := ∅
  Δ₁ := ∅
  Δ₂ := {B}
  Γ_ant := by simp
  Δ_suc := by simp
  Γ_disj := by simp
  Δ_disj := by simp

@[simp, grind .]
lemma ss_atoms : ((PartitionOf.ss A B).Γ₁.atoms ∪ (PartitionOf.ss A B).Γ₂.atoms) ∩ ((PartitionOf.ss A B).Δ₁.atoms ∪ (PartitionOf.ss A B).Δ₂.atoms) = A.atoms ∩ B.atoms := by
  simp;

end PartitionOf



namespace PartitionOf

variable {S : Sequent α} {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α}

def restrictAnt {Γ Γ' Δ : FormulaFinset α} (P : PartitionOf (Γ' ⟹ Δ)) (h : Γ ⊆ Γ') : PartitionOf (Γ ⟹ Δ) where
  Γ₁ := P.Γ₁ ∩ Γ
  Γ₂ := P.Γ₂ ∩ Γ
  Δ₁ := P.Δ₁
  Δ₂ := P.Δ₂
  Γ_ant := by
    have : Γ' = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant;
    grind;
  Δ_suc := P.Δ_suc
  Γ_disj := P.Γ_disj.mono Finset.inter_subset_left Finset.inter_subset_left
  Δ_disj := P.Δ_disj

def restrictSuc (P : PartitionOf (Γ ⟹ Δ')) (h : Δ ⊆ Δ') : PartitionOf (Γ ⟹ Δ) where
  Γ₁ := P.Γ₁
  Γ₂ := P.Γ₂
  Δ₁ := P.Δ₁ ∩ Δ
  Δ₂ := P.Δ₂ ∩ Δ
  Γ_ant := P.Γ_ant
  Δ_suc := by
    have hd : Δ' = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
    show Δ = P.Δ₁ ∩ Δ ∪ P.Δ₂ ∩ Δ
    rw [← Finset.union_inter_distrib_right, ← hd, Finset.inter_eq_right.mpr h]
  Γ_disj := P.Γ_disj
  Δ_disj := P.Δ_disj.mono Finset.inter_subset_left Finset.inter_subset_left

def impRSplitL (P : PartitionOf (Γ ⟹ insert (A 🡒 B) Δ)) : PartitionOf (insert A Γ ⟹ insert B Δ) where
  Γ₁ := insert A P.Γ₁
  Γ₂ := insert A Γ \ insert A P.Γ₁
  Δ₁ := insert B (P.Δ₁ ∩ Δ)
  Δ₂ := insert B Δ \ insert B (P.Δ₁ ∩ Δ)
  Γ_ant := by
    have hsub : insert A P.Γ₁ ⊆ insert A Γ := by
      apply Finset.insert_subset_insert
      have hg : Γ = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant; grind
    show insert A Γ = insert A P.Γ₁ ∪ (insert A Γ \ insert A P.Γ₁)
    exact (Finset.union_sdiff_of_subset hsub).symm
  Δ_suc := by
    have hsub : insert B (P.Δ₁ ∩ Δ) ⊆ insert B Δ :=
      Finset.insert_subset_insert _ Finset.inter_subset_right
    show insert B Δ = insert B (P.Δ₁ ∩ Δ) ∪ (insert B Δ \ insert B (P.Δ₁ ∩ Δ))
    exact (Finset.union_sdiff_of_subset hsub).symm
  Γ_disj := Finset.disjoint_sdiff
  Δ_disj := Finset.disjoint_sdiff

def impRSplitR (P : PartitionOf (Γ ⟹ insert (A 🡒 B) Δ)) : PartitionOf (insert A Γ ⟹ insert B Δ) where
  Γ₁ := insert A Γ \ insert A P.Γ₂
  Γ₂ := insert A P.Γ₂
  Δ₁ := insert B Δ \ insert B (P.Δ₂ ∩ Δ)
  Δ₂ := insert B (P.Δ₂ ∩ Δ)
  Γ_ant := by
    have hsub : insert A P.Γ₂ ⊆ insert A Γ := by
      apply Finset.insert_subset_insert
      have hg : Γ = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant; grind
    show insert A Γ = (insert A Γ \ insert A P.Γ₂) ∪ insert A P.Γ₂
    exact (Finset.sdiff_union_of_subset hsub).symm
  Δ_suc := by
    have hsub : insert B (P.Δ₂ ∩ Δ) ⊆ insert B Δ :=
      Finset.insert_subset_insert _ Finset.inter_subset_right
    show insert B Δ = (insert B Δ \ insert B (P.Δ₂ ∩ Δ)) ∪ insert B (P.Δ₂ ∩ Δ)
    exact (Finset.sdiff_union_of_subset hsub).symm
  Γ_disj := Finset.sdiff_disjoint
  Δ_disj := Finset.sdiff_disjoint

def impLSplit₁L (P : PartitionOf (insert (A 🡒 B) Γ ⟹ Δ)) : PartitionOf (Γ ⟹ insert A Δ) where
  Γ₁ := P.Γ₁ ∩ Γ
  Γ₂ := P.Γ₂ ∩ Γ
  Δ₁ := insert A P.Δ₁
  Δ₂ := insert A Δ \ insert A P.Δ₁
  Γ_ant := by
    have h : insert (A 🡒 B) Γ = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
    show Γ = P.Γ₁ ∩ Γ ∪ P.Γ₂ ∩ Γ
    rw [← Finset.union_inter_distrib_right, ← h, Finset.inter_eq_right.mpr (Finset.subset_insert _ _)]
  Δ_suc := by
    have hsub : insert A P.Δ₁ ⊆ insert A Δ :=
      Finset.insert_subset_insert _ (by have hd : Δ = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc; grind)
    show insert A Δ = insert A P.Δ₁ ∪ (insert A Δ \ insert A P.Δ₁)
    exact (Finset.union_sdiff_of_subset hsub).symm
  Γ_disj := P.Γ_disj.mono Finset.inter_subset_left Finset.inter_subset_left
  Δ_disj := Finset.disjoint_sdiff

def impLSplit₂L (P : PartitionOf (insert (A 🡒 B) Γ ⟹ Δ)) : PartitionOf (insert B Γ ⟹ Δ) where
  Γ₁ := insert B (P.Γ₁ ∩ Γ)
  Γ₂ := insert B Γ \ insert B (P.Γ₁ ∩ Γ)
  Δ₁ := P.Δ₁
  Δ₂ := P.Δ₂
  Γ_ant := by
    have hsub : insert B (P.Γ₁ ∩ Γ) ⊆ insert B Γ :=
      Finset.insert_subset_insert _ Finset.inter_subset_right
    show insert B Γ = insert B (P.Γ₁ ∩ Γ) ∪ (insert B Γ \ insert B (P.Γ₁ ∩ Γ))
    exact (Finset.union_sdiff_of_subset hsub).symm
  Δ_suc := P.Δ_suc
  Γ_disj := Finset.disjoint_sdiff
  Δ_disj := P.Δ_disj

def impLSplit₁R (P : PartitionOf (insert (A 🡒 B) Γ ⟹ Δ)) : PartitionOf (Γ ⟹ insert A Δ) where
  Γ₁ := P.Γ₁ ∩ Γ
  Γ₂ := P.Γ₂ ∩ Γ
  Δ₁ := insert A Δ \ insert A P.Δ₂
  Δ₂ := insert A P.Δ₂
  Γ_ant := by
    have h : insert (A 🡒 B) Γ = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
    show Γ = P.Γ₁ ∩ Γ ∪ P.Γ₂ ∩ Γ
    rw [← Finset.union_inter_distrib_right, ← h, Finset.inter_eq_right.mpr (Finset.subset_insert _ _)]
  Δ_suc := by
    have hsub : insert A P.Δ₂ ⊆ insert A Δ :=
      Finset.insert_subset_insert _ (by have hd : Δ = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc; grind)
    show insert A Δ = (insert A Δ \ insert A P.Δ₂) ∪ insert A P.Δ₂
    exact (Finset.sdiff_union_of_subset hsub).symm
  Γ_disj := P.Γ_disj.mono Finset.inter_subset_left Finset.inter_subset_left
  Δ_disj := Finset.sdiff_disjoint

def impLSplit₂R (P : PartitionOf (insert (A 🡒 B) Γ ⟹ Δ)) : PartitionOf (insert B Γ ⟹ Δ) where
  Γ₁ := insert B Γ \ insert B (P.Γ₂ ∩ Γ)
  Γ₂ := insert B (P.Γ₂ ∩ Γ)
  Δ₁ := P.Δ₁
  Δ₂ := P.Δ₂
  Γ_ant := by
    have hsub : insert B (P.Γ₂ ∩ Γ) ⊆ insert B Γ :=
      Finset.insert_subset_insert _ Finset.inter_subset_right
    show insert B Γ = (insert B Γ \ insert B (P.Γ₂ ∩ Γ)) ∪ insert B (P.Γ₂ ∩ Γ)
    exact (Finset.sdiff_union_of_subset hsub).symm
  Δ_suc := P.Δ_suc
  Γ_disj := Finset.sdiff_disjoint
  Δ_disj := P.Δ_disj

def boxGLSplitL {Γ : FormulaFinset α} {A : Formula α} (P : PartitionOf (Γ.box ⟹ {□A})) :
    PartitionOf (insert (□A) (Γ ∪ Γ.box) ⟹ {A}) where
  Γ₁ := insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₁) ∪ P.Γ₁)
  Γ₂ := insert (□A) (Γ ∪ Γ.box) \ insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₁) ∪ P.Γ₁)
  Δ₁ := {A}
  Δ₂ := ∅
  Γ_ant := by
    have hb : Γ.box = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
    have hsub : insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₁) ∪ P.Γ₁) ⊆ insert (□A) (Γ ∪ Γ.box) := by
      grind [Finset.filter_subset]
    simpa using (Finset.union_sdiff_of_subset hsub).symm
  Δ_suc := by simp
  Γ_disj := Finset.disjoint_sdiff
  Δ_disj := by simp

def boxGLSplitR {Γ : FormulaFinset α} {A : Formula α} (P : PartitionOf (Γ.box ⟹ {□A})) :
    PartitionOf (insert (□A) (Γ ∪ Γ.box) ⟹ {A}) where
  Γ₁ := insert (□A) (Γ ∪ Γ.box) \ insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₂) ∪ P.Γ₂)
  Γ₂ := insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₂) ∪ P.Γ₂)
  Δ₁ := ∅
  Δ₂ := {A}
  Γ_ant := by
    have hb : Γ.box = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
    have hsub : insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₂) ∪ P.Γ₂) ⊆ insert (□A) (Γ ∪ Γ.box) := by
      grind [Finset.filter_subset]
    simpa using (Finset.sdiff_union_of_subset hsub).symm
  Δ_suc := by simp
  Γ_disj := Finset.sdiff_disjoint
  Δ_disj := by simp

end PartitionOf


private lemma insert_sdiff_subset {a : Formula α} {Γ G H : FormulaFinset α}
  (h : ∀ x ∈ Γ, x ∉ G → x ∈ H) : insert a Γ \ insert a G ⊆ H := by
  intro x hx
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_insert] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hxa : x ≠ a := fun he => hx2 (Or.inl he)
  exact h x (hx1.resolve_left hxa) (fun he => hx2 (Or.inr he))

private lemma boxGL_compl {Γ : FormulaFinset α} {a : Formula α} {S S' : FormulaFinset α}
  (hΓ : Γ.box = S ∪ S') :
  insert a (Γ ∪ Γ.box) \ insert a (Γ.filter (fun B => □B ∈ S') ∪ S') ⊆ Γ.filter (fun B => □B ∈ S) ∪ S := by
  apply insert_sdiff_subset
  intro x hxM hxn
  have hxnF : x ∉ Γ.filter (fun B => □B ∈ S') := fun he => hxn (Finset.mem_union_left _ he)
  have hxnS' : x ∉ S' := fun he => hxn (Finset.mem_union_right _ he)
  rcases Finset.mem_union.mp hxM with hxΓ | hxbox
  · have hbox : □x ∈ Γ.box := by
      simp only [FormulaFinset.box, Finset.mem_image]; exact ⟨x, hxΓ, rfl⟩
    have hxS' : □x ∉ S' := fun he => hxnF (Finset.mem_filter.mpr ⟨hxΓ, he⟩)
    exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hxΓ, (Finset.mem_union.mp (hΓ ▸ hbox)).resolve_right hxS'⟩)
  · exact Finset.mem_union_right _ ((Finset.mem_union.mp (hΓ ▸ hxbox)).resolve_right hxnS')


namespace ProofGentzen

variable {S : Sequent α}

def interpolant {S : Sequent α} (P : PartitionOf S) : ⊢ᵍ[GL]! S → Formula α
| .botL     => if ⊥ ∈ P.Γ₁ then ⊥ else ⊤
| .axm A    =>
  if A ∈ P.Γ₁ then (if A ∈ P.Δ₁ then ⊥ else A)
  else (if A ∈ P.Δ₁ then ∼A else ⊤)
| @wkL _ _ _ _ _ p h' => interpolant (P.restrictAnt h') p
| @wkR _ _ _ _ _ p h' => interpolant (P.restrictSuc h') p
| @impL _ _ _ _ A B p₁ p₂ =>
  if A 🡒 B ∈ P.Γ₁ then interpolant P.impLSplit₁L p₁ ⋎ interpolant P.impLSplit₂L p₂
  else interpolant P.impLSplit₁R p₁ ⋏ interpolant P.impLSplit₂R p₂
| @impR _ _ _ _ A B p =>
  if A 🡒 B ∈ P.Δ₁ then interpolant P.impRSplitL p
  else interpolant P.impRSplitR p
| @boxGL _ _ Γ A p =>
  if □A ∈ P.Δ₁ then ∼□(∼(interpolant P.boxGLSplitL p))
  else □(interpolant P.boxGLSplitR p)

theorem interpolant_provable_ant (P : PartitionOf S) (p : ⊢ᵍ[GL]! S) : ⊢ᵍ[GL] (P.Γ₁ ⟹ insert (interpolant P p) P.Δ₁) := by
  induction p with
  | botL =>
    dsimp only [interpolant];
    split_ifs;
    · exact ProvableGentzen.botL_mem (by grind)
    · exact ProvableGentzen.impR (ProvableGentzen.botL_mem (by grind))
  | axm A =>
    have hΓ : ({A} : FormulaFinset α) = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
    have hΔ : ({A} : FormulaFinset α) = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
    have memΓ : A ∈ P.Γ₁ ∪ P.Γ₂ := hΓ ▸ Finset.mem_singleton_self _
    have memΔ : A ∈ P.Δ₁ ∪ P.Δ₂ := hΔ ▸ Finset.mem_singleton_self _
    dsimp only [interpolant];
    split_ifs with hg hd
    · exact ProvableGentzen.union A
    · exact ProvableGentzen.union A
    · exact ⟨ProofGentzen.negR (ProofGentzen.union A)⟩
    · exact ProvableGentzen.impR (ProvableGentzen.botL_mem (by grind))
  | @wkL Γ Γ' Δ q h' ih =>
    apply ProvableGentzen.wkL (ih (P.restrictAnt h'));
    exact Finset.inter_subset_left;
  | @wkR Γ Δ Δ' q h' ih =>
    apply ProvableGentzen.wkR $ ih (P.restrictSuc h');
    exact Finset.insert_subset_insert _ Finset.inter_subset_left;
  | @impL Γ Δ A B p₁ p₂ ih₁ ih₂ =>
    dsimp only [interpolant]
    split_ifs with hg
    ·
      have ha1 := ih₁ P.impLSplit₁L
      have ha2 := ih₂ P.impLSplit₂L
      set C1 := interpolant P.impLSplit₁L p₁ with hC1
      set C2 := interpolant P.impLSplit₂L p₂ with hC2
      simp only [PartitionOf.impLSplit₁L] at ha1
      simp only [PartitionOf.impLSplit₂L] at ha2
      have key : ⊢ᵍ[GL] (insert (A 🡒 B) P.Γ₁ ⟹ insert (C1 ⋎ C2) P.Δ₁) := by
        apply ProvableGentzen.impL
        · have t1 : ⊢ᵍ[GL] (P.Γ₁ ∩ Γ ⟹ insert C1 (insert C2 (insert A P.Δ₁))) :=
            ProvableGentzen.wkR ha1 (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
          have t2 := ProvableGentzen.orR t1
          rw [Finset.insert_comm] at t2
          exact ProvableGentzen.wkL t2 Finset.inter_subset_left
        · have t1 : ⊢ᵍ[GL] (insert B (P.Γ₁ ∩ Γ) ⟹ insert C1 (insert C2 P.Δ₁)) :=
            ProvableGentzen.wkR ha2 (Finset.subset_insert _ _)
          have t2 := ProvableGentzen.orR t1
          exact ProvableGentzen.wkL t2 (Finset.insert_subset_insert _ Finset.inter_subset_left)
      rwa [Finset.insert_eq_self.mpr hg] at key
    ·
      have hg' : insert (A 🡒 B) Γ = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
      have hd : Δ = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
      have ha1 := ih₁ P.impLSplit₁R
      have ha2 := ih₂ P.impLSplit₂R
      set C1 := interpolant P.impLSplit₁R p₁ with hC1
      set C2 := interpolant P.impLSplit₂R p₂ with hC2
      simp only [PartitionOf.impLSplit₁R] at ha1
      simp only [PartitionOf.impLSplit₂R] at ha2
      apply ProvableGentzen.andR
      ·
        refine ProvableGentzen.wk ha1 Finset.inter_subset_left (Finset.insert_subset_insert _ ?_)
        exact insert_sdiff_subset fun x hxΔ hxn => (Finset.mem_union.mp (hd ▸ hxΔ)).resolve_right hxn
      ·
        refine ProvableGentzen.wkL ha2 ?_
        exact insert_sdiff_subset fun x hxΓ hxn => by
          have hx2 : x ∉ P.Γ₂ := fun he => hxn (Finset.mem_inter.mpr ⟨he, hxΓ⟩)
          exact (Finset.mem_union.mp (hg' ▸ Finset.mem_insert_of_mem hxΓ : x ∈ P.Γ₁ ∪ P.Γ₂)).resolve_right hx2
  | @impR Γ Δ A B q ih =>
    dsimp only [interpolant]
    split_ifs with hd
    · have ha := ih P.impRSplitL
      set C := interpolant P.impRSplitL q with hC
      simp only [PartitionOf.impRSplitL] at ha
      rw [Finset.insert_comm] at ha
      apply ProvableGentzen.wkR (ProvableGentzen.impR ha);
      grind;
    · have hd2 : A 🡒 B ∈ P.Δ₂ := by
        have hδ : insert (A 🡒 B) Δ = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
        have hmem : A 🡒 B ∈ insert (A 🡒 B) Δ := Finset.mem_insert_self _ _
        grind
      have ha := ih P.impRSplitR
      set C := interpolant P.impRSplitR q with hC
      simp only [PartitionOf.impRSplitR] at ha
      have hg : Γ = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
      have hδ : insert (A 🡒 B) Δ = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
      have h1 : insert A Γ \ insert A P.Γ₂ ⊆ P.Γ₁ :=
        insert_sdiff_subset fun x hxΓ hxn => (Finset.mem_union.mp (hg ▸ hxΓ)).resolve_right hxn
      have h2 : insert B Δ \ insert B (P.Δ₂ ∩ Δ) ⊆ P.Δ₁ :=
        insert_sdiff_subset fun x hxΔ hxn => by
          rcases Finset.mem_union.mp (hδ ▸ Finset.mem_insert_of_mem hxΔ : x ∈ P.Δ₁ ∪ P.Δ₂) with h | h
          · exact h
          · exact absurd (Finset.mem_inter.mpr ⟨h, hxΔ⟩) hxn
      exact ProvableGentzen.wk ha h1 (Finset.insert_subset_insert _ h2)
  | @boxGL Γ A p ih =>
    have hb : Γ.box = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
    have hΔ : ({□A} : FormulaFinset α) = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
    have hsub1 : P.Γ₁ ⊆ Γ.box := by grind
    have hbF1 : FormulaFinset.box (Γ.filter (fun B => □B ∈ P.Γ₁)) = P.Γ₁ :=
      FormulaFinset.box_filter hsub1
    dsimp only [interpolant]
    split_ifs with hd
    ·
      have hΔ1 : P.Δ₁ = {□A} := by grind
      have ha := ih P.boxGLSplitL
      set C := interpolant P.boxGLSplitL p with hC
      simp only [PartitionOf.boxGLSplitL] at ha
      have t1 : ⊢ᵍ[GL] (insert (∼C) (insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₁) ∪ P.Γ₁)) ⟹
          ({A} : FormulaFinset α)) := ProvableGentzen.negL ha
      have t2 := ProvableGentzen.wkL t1
        (Finset.subset_insert (□(∼C)) (insert (∼C) (insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₁) ∪ P.Γ₁))))
      have boxed : ⊢ᵍ[GL] (FormulaFinset.box (insert (∼C) (Γ.filter (fun B => □B ∈ P.Γ₁))) ⟹
          ({□A} : FormulaFinset α)) := by
        apply ProvableGentzen.boxGL
        have heq : insert (□A) (insert (∼C) (Γ.filter (fun B => □B ∈ P.Γ₁))
                      ∪ FormulaFinset.box (insert (∼C) (Γ.filter (fun B => □B ∈ P.Γ₁))))
                 = insert (□(∼C)) (insert (∼C) (insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₁) ∪ P.Γ₁))) := by
          rw [FormulaFinset.box_insert, hbF1]
          ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
        rw [heq]; exact t2
      rw [FormulaFinset.box_insert, hbF1] at boxed
      rw [hΔ1]
      exact ProvableGentzen.negR boxed
    ·
      have hΔ1 : P.Δ₁ = ∅ := by
        by_contra hne
        obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne
        have hxs : x ∈ ({□A} : FormulaFinset α) := hΔ.symm ▸ Finset.mem_union_left _ hx
        rw [Finset.mem_singleton] at hxs
        subst hxs
        exact hd hx
      have ha := ih P.boxGLSplitR
      set C := interpolant P.boxGLSplitR p with hC
      simp only [PartitionOf.boxGLSplitR] at ha
      have boxed : ⊢ᵍ[GL] (FormulaFinset.box (Γ.filter (fun B => □B ∈ P.Γ₁)) ⟹ ({□C} : FormulaFinset α)) := by
        apply ProvableGentzen.boxGL
        rw [hbF1]
        refine ProvableGentzen.wkL ?_ ((boxGL_compl (a := □A) hb).trans (Finset.subset_insert _ _))
        simpa using ha
      rw [hbF1] at boxed
      rw [hΔ1]
      simpa using boxed


theorem interpolant_provable_suc (P : PartitionOf S) (p : ⊢ᵍ[GL]! S) :
  ⊢ᵍ[GL] (insert (interpolant P p) P.Γ₂ ⟹ P.Δ₂) := by
  induction p with
  | botL =>
    show ⊢ᵍ[GL] (insert (if ⊥ ∈ P.Γ₁ then ⊥ else ⊤) P.Γ₂ ⟹ P.Δ₂)
    by_cases h : ⊥ ∈ P.Γ₁
    · rw [if_pos h]; exact ProvableGentzen.botL_mem (by grind)
    · rw [if_neg h]
      have hΓ : ({⊥} : FormulaFinset α) = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
      have h₂ : ⊥ ∈ P.Γ₂ := by
        have hmem : ⊥ ∈ P.Γ₁ ∪ P.Γ₂ := hΓ ▸ Finset.mem_singleton_self _
        grind
      exact ProvableGentzen.botL_mem (by grind)
  | axm A =>
    have hΓ : ({A} : FormulaFinset α) = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
    have hΔ : ({A} : FormulaFinset α) = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
    have memΓ : A ∈ P.Γ₁ ∪ P.Γ₂ := hΓ ▸ Finset.mem_singleton_self _
    have memΔ : A ∈ P.Δ₁ ∪ P.Δ₂ := hΔ ▸ Finset.mem_singleton_self _
    dsimp only [interpolant]
    split_ifs with hg hd
    · exact ProvableGentzen.botL_mem (by grind)
    · exact ProvableGentzen.union A
    · have hg2 : A ∈ P.Γ₂ := by grind
      exact ⟨ProofGentzen.negL (ProofGentzen.union A)⟩
    · exact ProvableGentzen.union A
  | @wkL Γ Γ' Δ q h' ih =>
    have hs := ih (P.restrictAnt h')
    simp only [PartitionOf.restrictAnt] at hs
    exact ProvableGentzen.wkL hs (Finset.insert_subset_insert _ Finset.inter_subset_left)
  | @wkR Γ Δ Δ' q h' ih =>
    have hs := ih (P.restrictSuc h')
    simp only [PartitionOf.restrictSuc] at hs
    exact ProvableGentzen.wkR hs Finset.inter_subset_left
  | @impL Γ Δ A B p₁ p₂ ih₁ ih₂ =>
    have hg' : insert (A 🡒 B) Γ = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
    have hd : Δ = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
    dsimp only [interpolant]
    split_ifs with hg
    · have hs1 := ih₁ P.impLSplit₁L
      have hs2 := ih₂ P.impLSplit₂L
      set C1 := interpolant P.impLSplit₁L p₁ with hC1
      set C2 := interpolant P.impLSplit₂L p₂ with hC2
      simp only [PartitionOf.impLSplit₁L] at hs1
      simp only [PartitionOf.impLSplit₂L] at hs2
      apply ProvableGentzen.orL
      · refine ProvableGentzen.wk hs1 (Finset.insert_subset_insert _ Finset.inter_subset_left) ?_
        exact insert_sdiff_subset fun x hxΔ hxn => (Finset.mem_union.mp (hd ▸ hxΔ)).resolve_left hxn
      · refine ProvableGentzen.wkL hs2 (Finset.insert_subset_insert _ ?_)
        exact insert_sdiff_subset fun x hxΓ hxn => by
          have hx1 : x ∉ P.Γ₁ := fun he => hxn (Finset.mem_inter.mpr ⟨he, hxΓ⟩)
          exact (Finset.mem_union.mp (hg' ▸ Finset.mem_insert_of_mem hxΓ : x ∈ P.Γ₁ ∪ P.Γ₂)).resolve_left hx1
    ·
      have hprin2 : A 🡒 B ∈ P.Γ₂ := by
        have hmem : A 🡒 B ∈ insert (A 🡒 B) Γ := Finset.mem_insert_self _ _
        grind
      have hs1 := ih₁ P.impLSplit₁R
      have hs2 := ih₂ P.impLSplit₂R
      set C1 := interpolant P.impLSplit₁R p₁ with hC1
      set C2 := interpolant P.impLSplit₂R p₂ with hC2
      simp only [PartitionOf.impLSplit₁R] at hs1;
      unfold PartitionOf.impLSplit₂R at hs2;
      have key : ⊢ᵍ[GL] (insert (A 🡒 B) (insert C1 (insert C2 P.Γ₂)) ⟹ P.Δ₂) := by
        apply ProvableGentzen.impL
        · exact ProvableGentzen.wkL hs1
            (Finset.insert_subset_insert _ (Finset.inter_subset_left.trans (Finset.subset_insert _ _)))
        · refine ProvableGentzen.wkL hs2 ?_
          intro x
          simp only [Finset.mem_insert, Finset.mem_inter]
          tauto
      rw [Finset.insert_eq_self.mpr
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hprin2))] at key
      exact ProvableGentzen.andL key
  | @impR Γ Δ A B q ih =>
    dsimp only [interpolant]
    split_ifs with hd
    · have hs := ih P.impRSplitL
      set C := interpolant P.impRSplitL q with hC
      simp only [PartitionOf.impRSplitL] at hs
      have hg : Γ = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
      have hδ : insert (A 🡒 B) Δ = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
      have h1 : insert A Γ \ insert A P.Γ₁ ⊆ P.Γ₂ :=
        insert_sdiff_subset fun x hxΓ hxn => (Finset.mem_union.mp (hg ▸ hxΓ)).resolve_left hxn
      have h2 : insert B Δ \ insert B (P.Δ₁ ∩ Δ) ⊆ P.Δ₂ :=
        insert_sdiff_subset fun x hxΔ hxn => by
          rcases Finset.mem_union.mp (hδ ▸ Finset.mem_insert_of_mem hxΔ : x ∈ P.Δ₁ ∪ P.Δ₂) with h | h
          · exact absurd (Finset.mem_inter.mpr ⟨h, hxΔ⟩) hxn
          · exact h
      exact ProvableGentzen.wk hs (Finset.insert_subset_insert _ h1) h2
    · have hd2 : A 🡒 B ∈ P.Δ₂ := by
        have hδ : insert (A 🡒 B) Δ = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
        have hmem : A 🡒 B ∈ insert (A 🡒 B) Δ := Finset.mem_insert_self _ _
        grind
      have hs := ih P.impRSplitR
      set C := interpolant P.impRSplitR q with hC
      simp only [PartitionOf.impRSplitR] at hs
      rw [Finset.insert_comm] at hs
      exact ProvableGentzen.wkR (ProvableGentzen.impR hs)
        (Finset.insert_subset hd2 Finset.inter_subset_left)
  | @boxGL Γ A p ih =>
    have hb : Γ.box = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
    have hΔ : ({□A} : FormulaFinset α) = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
    have hsub2 : P.Γ₂ ⊆ Γ.box := by grind
    have hbF2 : FormulaFinset.box (Γ.filter (fun B => □B ∈ P.Γ₂)) = P.Γ₂ :=
      FormulaFinset.box_filter hsub2
    dsimp only [interpolant]
    split_ifs with hd
    ·
      have hΔ2 : P.Δ₂ = ∅ := by
        by_contra hne
        obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne
        have hxs : x ∈ ({□A} : FormulaFinset α) := hΔ.symm ▸ Finset.mem_union_right _ hx
        rw [Finset.mem_singleton] at hxs
        subst hxs
        exact Finset.disjoint_left.mp P.Δ_disj hd hx
      have ha := ih P.boxGLSplitL
      set C := interpolant P.boxGLSplitL p with hC
      simp only [PartitionOf.boxGLSplitL] at ha
      have t1 : ⊢ᵍ[GL] (insert (□A) (Γ ∪ Γ.box) \ insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₁) ∪ P.Γ₁)
          ⟹ ({∼C} : FormulaFinset α)) := by simpa using ProvableGentzen.negR ha
      have boxed : ⊢ᵍ[GL] (FormulaFinset.box (Γ.filter (fun B => □B ∈ P.Γ₂)) ⟹ ({□(∼C)} : FormulaFinset α)) := by
        apply ProvableGentzen.boxGL
        rw [hbF2]
        exact ProvableGentzen.wkL t1
          ((boxGL_compl (a := □A) (hb.trans (Finset.union_comm _ _))).trans (Finset.subset_insert _ _))
      rw [hbF2] at boxed
      rw [hΔ2]
      have boxed' : ⊢ᵍ[GL] (P.Γ₂ ⟹ insert (□(∼C)) ∅) := by simpa using boxed
      exact ProvableGentzen.negL boxed'
    ·
      have hd2 : □A ∈ P.Δ₂ := by
        have hmem : □A ∈ ({□A} : FormulaFinset α) := Finset.mem_singleton_self _
        grind
      have hΔ2 : P.Δ₂ = {□A} := by grind
      have ha := ih P.boxGLSplitR
      set C := interpolant P.boxGLSplitR p with hC
      simp only [PartitionOf.boxGLSplitR] at ha
      have boxed : ⊢ᵍ[GL] (FormulaFinset.box (insert C (Γ.filter (fun B => □B ∈ P.Γ₂))) ⟹ ({□A} : FormulaFinset α)) := by
        apply ProvableGentzen.boxGL
        have heq : insert (□A) (insert C (Γ.filter (fun B => □B ∈ P.Γ₂))
                      ∪ FormulaFinset.box (insert C (Γ.filter (fun B => □B ∈ P.Γ₂))))
                 = insert (□C) (insert C (insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₂) ∪ P.Γ₂))) := by
          rw [FormulaFinset.box_insert, hbF2]
          ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
        rw [heq]
        exact ProvableGentzen.wkL ha (Finset.subset_insert _ _)
      rw [FormulaFinset.box_insert, hbF2] at boxed
      rw [hΔ2]
      exact boxed

theorem interpolant_atoms {S : Sequent α} (P : PartitionOf S) (p : ⊢ᵍ[GL]! S) :
  (interpolant P p).atoms ⊆ (P.Γ₁.atoms ∪ P.Δ₁.atoms) ∩ (P.Γ₂.atoms ∪ P.Δ₂.atoms) := by
  induction p with
  | botL =>
    dsimp only [interpolant];
    split_ifs <;> simp [Formula.atoms]
  | axm A =>
    dsimp only [interpolant];
    have hΓ : ({A} : FormulaFinset α) = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
    have hΔ : ({A} : FormulaFinset α) = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
    have memΓ : A ∈ P.Γ₁ ∪ P.Γ₂ := hΓ ▸ Finset.mem_singleton_self _
    have memΔ : A ∈ P.Δ₁ ∪ P.Δ₂ := hΔ ▸ Finset.mem_singleton_self _
    split_ifs with hg hd
    · simp [Formula.atoms]
    · exact Finset.subset_inter
        ((FormulaFinset.atoms_subset_of_mem hg).trans Finset.subset_union_left)
        ((FormulaFinset.atoms_subset_of_mem (by grind)).trans Finset.subset_union_right)
    · have hg2 : A ∈ P.Γ₂ := by grind
      simp only [Formula.atoms, Finset.union_empty]
      exact Finset.subset_inter
        ((FormulaFinset.atoms_subset_of_mem ‹A ∈ P.Δ₁›).trans Finset.subset_union_right)
        ((FormulaFinset.atoms_subset_of_mem hg2).trans Finset.subset_union_left)
    · simp [Formula.atoms]
  | @wkL Γ Γ' Δ q h' ih =>
    dsimp only [interpolant];
    have hat := ih (P.restrictAnt h')
    simp only [PartitionOf.restrictAnt] at hat
    exact hat.trans (Finset.inter_subset_inter
      (Finset.union_subset_union (FormulaFinset.atoms_mono Finset.inter_subset_left) (Finset.Subset.refl _))
      (Finset.union_subset_union (FormulaFinset.atoms_mono Finset.inter_subset_left) (Finset.Subset.refl _)))
  | @wkR Γ Δ Δ' q h' ih =>
    dsimp only [interpolant];
    have hat := ih (P.restrictSuc h')
    simp only [PartitionOf.restrictSuc] at hat
    exact hat.trans (Finset.inter_subset_inter
      (Finset.union_subset_union (Finset.Subset.refl _) (FormulaFinset.atoms_mono Finset.inter_subset_left))
      (Finset.union_subset_union (Finset.Subset.refl _) (FormulaFinset.atoms_mono Finset.inter_subset_left)))
  | @impL Γ Δ A B p₁ p₂ ih₁ ih₂ =>
    have hg' : insert (A 🡒 B) Γ = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
    have hd : Δ = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
    dsimp only [interpolant]
    split_ifs with hg
    ·
      have hP : (A 🡒 B).atoms ⊆ P.Γ₁.atoms := FormulaFinset.atoms_subset_of_mem hg
      simp only [Formula.atoms] at hP
      have hA : A.atoms ⊆ P.Γ₁.atoms := Finset.subset_union_left.trans hP
      have hB : B.atoms ⊆ P.Γ₁.atoms := Finset.subset_union_right.trans hP
      have h_Δ2 : insert A Δ \ insert A P.Δ₁ ⊆ P.Δ₂ :=
        insert_sdiff_subset fun x hxΔ hxn => (Finset.mem_union.mp (hd ▸ hxΔ)).resolve_left hxn
      have h_Γ2 : insert B Γ \ insert B (P.Γ₁ ∩ Γ) ⊆ P.Γ₂ :=
        insert_sdiff_subset fun x hxΓ hxn => by
          have hx1 : x ∉ P.Γ₁ := fun he => hxn (Finset.mem_inter.mpr ⟨he, hxΓ⟩)
          exact (Finset.mem_union.mp (hg' ▸ Finset.mem_insert_of_mem hxΓ : x ∈ P.Γ₁ ∪ P.Γ₂)).resolve_left hx1
      have ha1 := ih₁ P.impLSplit₁L
      have ha2 := ih₂ P.impLSplit₂L
      set C1 := interpolant P.impLSplit₁L p₁ with hC1
      set C2 := interpolant P.impLSplit₂L p₂ with hC2
      simp only [PartitionOf.impLSplit₁L] at ha1
      simp only [PartitionOf.impLSplit₂L] at ha2
      simp only [Formula.atoms, Finset.union_empty]
      apply Finset.union_subset
      · refine ha1.trans (Finset.inter_subset_inter ?_ ?_)
        · simp only [FormulaFinset.atoms_insert]
          exact Finset.union_subset
            ((FormulaFinset.atoms_mono Finset.inter_subset_left).trans Finset.subset_union_left)
            (Finset.union_subset (hA.trans Finset.subset_union_left) Finset.subset_union_right)
        · exact Finset.union_subset
            ((FormulaFinset.atoms_mono Finset.inter_subset_left).trans Finset.subset_union_left)
            ((FormulaFinset.atoms_mono h_Δ2).trans Finset.subset_union_right)
      · refine ha2.trans (Finset.inter_subset_inter ?_ ?_)
        · simp only [FormulaFinset.atoms_insert]
          exact Finset.union_subset
            (Finset.union_subset (hB.trans Finset.subset_union_left)
              ((FormulaFinset.atoms_mono Finset.inter_subset_left).trans Finset.subset_union_left))
            Finset.subset_union_right
        · exact Finset.union_subset
            ((FormulaFinset.atoms_mono h_Γ2).trans Finset.subset_union_left)
            Finset.subset_union_right
    ·
      have hprin2 : A 🡒 B ∈ P.Γ₂ := by
        have hmem : A 🡒 B ∈ insert (A 🡒 B) Γ := Finset.mem_insert_self _ _
        grind
      have hP : (A 🡒 B).atoms ⊆ P.Γ₂.atoms := FormulaFinset.atoms_subset_of_mem hprin2
      simp only [Formula.atoms] at hP
      have hA : A.atoms ⊆ P.Γ₂.atoms := Finset.subset_union_left.trans hP
      have hB : B.atoms ⊆ P.Γ₂.atoms := Finset.subset_union_right.trans hP
      have h_Δ1 : insert A Δ \ insert A P.Δ₂ ⊆ P.Δ₁ :=
        insert_sdiff_subset fun x hxΔ hxn => (Finset.mem_union.mp (hd ▸ hxΔ)).resolve_right hxn
      have h_Γ1 : insert B Γ \ insert B (P.Γ₂ ∩ Γ) ⊆ P.Γ₁ :=
        insert_sdiff_subset fun x hxΓ hxn => by
          have hx2 : x ∉ P.Γ₂ := fun he => hxn (Finset.mem_inter.mpr ⟨he, hxΓ⟩)
          exact (Finset.mem_union.mp (hg' ▸ Finset.mem_insert_of_mem hxΓ : x ∈ P.Γ₁ ∪ P.Γ₂)).resolve_right hx2
      have ha1 := ih₁ P.impLSplit₁R
      have ha2 := ih₂ P.impLSplit₂R
      set C1 := interpolant P.impLSplit₁R p₁ with hC1
      set C2 := interpolant P.impLSplit₂R p₂ with hC2
      simp only [PartitionOf.impLSplit₁R] at ha1
      simp only [PartitionOf.impLSplit₂R] at ha2
      simp only [Formula.atoms, Finset.union_empty]
      apply Finset.union_subset
      · refine ha1.trans (Finset.inter_subset_inter ?_ ?_)
        · exact Finset.union_subset
            ((FormulaFinset.atoms_mono Finset.inter_subset_left).trans Finset.subset_union_left)
            ((FormulaFinset.atoms_mono h_Δ1).trans Finset.subset_union_right)
        · simp only [FormulaFinset.atoms_insert]
          exact Finset.union_subset
            ((FormulaFinset.atoms_mono Finset.inter_subset_left).trans Finset.subset_union_left)
            (Finset.union_subset (hA.trans Finset.subset_union_left) Finset.subset_union_right)
      · refine ha2.trans (Finset.inter_subset_inter ?_ ?_)
        · exact Finset.union_subset
            ((FormulaFinset.atoms_mono h_Γ1).trans Finset.subset_union_left)
            Finset.subset_union_right
        · simp only [FormulaFinset.atoms_insert]
          exact Finset.union_subset
            (Finset.union_subset (hB.trans Finset.subset_union_left)
              ((FormulaFinset.atoms_mono Finset.inter_subset_left).trans Finset.subset_union_left))
            Finset.subset_union_right
  | @impR Γ Δ A B q ih =>
    dsimp only [interpolant];
    split_ifs with hd
    · have hat := ih P.impRSplitL
      set C := interpolant P.impRSplitL q with hC
      simp only [PartitionOf.impRSplitL] at hat
      have hg : Γ = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
      have hδ : insert (A 🡒 B) Δ = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
      have h1 : insert A Γ \ insert A P.Γ₁ ⊆ P.Γ₂ :=
        insert_sdiff_subset fun x hxΓ hxn => (Finset.mem_union.mp (hg ▸ hxΓ)).resolve_left hxn
      have h2 : insert B Δ \ insert B (P.Δ₁ ∩ Δ) ⊆ P.Δ₂ :=
        insert_sdiff_subset fun x hxΔ hxn => by
          rcases Finset.mem_union.mp (hδ ▸ Finset.mem_insert_of_mem hxΔ : x ∈ P.Δ₁ ∪ P.Δ₂) with h | h
          · exact absurd (Finset.mem_inter.mpr ⟨h, hxΔ⟩) hxn
          · exact h
      refine hat.trans (Finset.inter_subset_inter ?_ ?_)
      · have hAB : (A 🡒 B).atoms ⊆ P.Δ₁.atoms := FormulaFinset.atoms_subset_of_mem hd
        simp only [Formula.atoms] at hAB
        have hA : A.atoms ⊆ P.Δ₁.atoms := Finset.subset_union_left.trans hAB
        have hB : B.atoms ⊆ P.Δ₁.atoms := Finset.subset_union_right.trans hAB
        have hPD : (P.Δ₁ ∩ Δ).atoms ⊆ P.Δ₁.atoms := FormulaFinset.atoms_mono Finset.inter_subset_left
        simp only [FormulaFinset.atoms_insert]
        exact Finset.union_subset
          (Finset.union_subset (hA.trans Finset.subset_union_right) Finset.subset_union_left)
          (Finset.union_subset (hB.trans Finset.subset_union_right) (hPD.trans Finset.subset_union_right))
      · exact Finset.union_subset
          ((FormulaFinset.atoms_mono h1).trans Finset.subset_union_left)
          ((FormulaFinset.atoms_mono h2).trans Finset.subset_union_right)
    · have hd2 : A 🡒 B ∈ P.Δ₂ := by
        have hδ : insert (A 🡒 B) Δ = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
        have hmem : A 🡒 B ∈ insert (A 🡒 B) Δ := Finset.mem_insert_self _ _
        grind
      have hat := ih P.impRSplitR
      set C := interpolant P.impRSplitR q with hC
      simp only [PartitionOf.impRSplitR] at hat
      have hg : Γ = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
      have hδ : insert (A 🡒 B) Δ = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
      have h1 : insert A Γ \ insert A P.Γ₂ ⊆ P.Γ₁ :=
        insert_sdiff_subset fun x hxΓ hxn => (Finset.mem_union.mp (hg ▸ hxΓ)).resolve_right hxn
      have h2 : insert B Δ \ insert B (P.Δ₂ ∩ Δ) ⊆ P.Δ₁ :=
        insert_sdiff_subset fun x hxΔ hxn => by
          rcases Finset.mem_union.mp (hδ ▸ Finset.mem_insert_of_mem hxΔ : x ∈ P.Δ₁ ∪ P.Δ₂) with h | h
          · exact h
          · exact absurd (Finset.mem_inter.mpr ⟨h, hxΔ⟩) hxn
      refine hat.trans (Finset.inter_subset_inter ?_ ?_)
      · exact Finset.union_subset
          ((FormulaFinset.atoms_mono h1).trans Finset.subset_union_left)
          ((FormulaFinset.atoms_mono h2).trans Finset.subset_union_right)
      · have hAB : (A 🡒 B).atoms ⊆ P.Δ₂.atoms := FormulaFinset.atoms_subset_of_mem hd2
        simp only [Formula.atoms] at hAB
        have hA : A.atoms ⊆ P.Δ₂.atoms := Finset.subset_union_left.trans hAB
        have hB : B.atoms ⊆ P.Δ₂.atoms := Finset.subset_union_right.trans hAB
        have hPD : (P.Δ₂ ∩ Δ).atoms ⊆ P.Δ₂.atoms := FormulaFinset.atoms_mono Finset.inter_subset_left
        simp only [FormulaFinset.atoms_insert]
        exact Finset.union_subset
          (Finset.union_subset (hA.trans Finset.subset_union_right) Finset.subset_union_left)
          (Finset.union_subset (hB.trans Finset.subset_union_right) (hPD.trans Finset.subset_union_right))
  | @boxGL Γ A p ih =>
    have hb : Γ.box = P.Γ₁ ∪ P.Γ₂ := P.Γ_ant
    have hsub1 : P.Γ₁ ⊆ Γ.box := by grind
    have hsub2 : P.Γ₂ ⊆ Γ.box := by grind
    have hbF1 : FormulaFinset.box (Γ.filter (fun B => □B ∈ P.Γ₁)) = P.Γ₁ :=
      FormulaFinset.box_filter hsub1
    have hbF2 : FormulaFinset.box (Γ.filter (fun B => □B ∈ P.Γ₂)) = P.Γ₂ :=
      FormulaFinset.box_filter hsub2
    have hF1at : FormulaFinset.atoms (Γ.filter (fun B => □B ∈ P.Γ₁)) = P.Γ₁.atoms := by
      rw [← FormulaFinset.box_atoms (Γ.filter (fun B => □B ∈ P.Γ₁)), hbF1]
    have hF2at : FormulaFinset.atoms (Γ.filter (fun B => □B ∈ P.Γ₂)) = P.Γ₂.atoms := by
      rw [← FormulaFinset.box_atoms (Γ.filter (fun B => □B ∈ P.Γ₂)), hbF2]
    dsimp only [interpolant]
    split_ifs with hd
    ·
      have hAD : A.atoms ⊆ P.Δ₁.atoms := by
        have := FormulaFinset.atoms_subset_of_mem hd; simpa [Formula.atoms] using this
      have hcompat : FormulaFinset.atoms (insert (□A) (Γ ∪ Γ.box)
          \ insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₁) ∪ P.Γ₁)) ⊆ P.Γ₂.atoms := by
        refine (FormulaFinset.atoms_mono
          (boxGL_compl (a := □A) (hb.trans (Finset.union_comm _ _)))).trans ?_
        simp [FormulaFinset.atoms_union, hF2at]
      have ha := ih P.boxGLSplitL
      set C := interpolant P.boxGLSplitL p with hC
      simp only [PartitionOf.boxGLSplitL] at ha
      simp only [Formula.atoms, Finset.union_empty]
      refine ha.trans (Finset.inter_subset_inter ?_ ?_)
      · apply Finset.union_subset
        · simp only [FormulaFinset.atoms_insert, FormulaFinset.atoms_union, hF1at, Formula.atoms]
          exact Finset.union_subset (hAD.trans Finset.subset_union_right)
            (Finset.union_subset Finset.subset_union_left Finset.subset_union_left)
        · rw [FormulaFinset.atoms_singleton]
          exact hAD.trans Finset.subset_union_right
      · simp only [FormulaFinset.atoms_empty, Finset.union_empty]
        exact hcompat.trans Finset.subset_union_left
    ·
      have hd2 : □A ∈ P.Δ₂ := by
        have hΔ : ({□A} : FormulaFinset α) = P.Δ₁ ∪ P.Δ₂ := P.Δ_suc
        have hmem : □A ∈ ({□A} : FormulaFinset α) := Finset.mem_singleton_self _
        grind
      have hAD : A.atoms ⊆ P.Δ₂.atoms := by
        have := FormulaFinset.atoms_subset_of_mem hd2; simpa [Formula.atoms] using this
      have hcompat : FormulaFinset.atoms (insert (□A) (Γ ∪ Γ.box)
          \ insert (□A) (Γ.filter (fun B => □B ∈ P.Γ₂) ∪ P.Γ₂)) ⊆ P.Γ₁.atoms := by
        refine (FormulaFinset.atoms_mono (boxGL_compl (a := □A) hb)).trans ?_
        simp [FormulaFinset.atoms_union, hF1at]
      have ha := ih P.boxGLSplitR
      set C := interpolant P.boxGLSplitR p with hC
      simp only [PartitionOf.boxGLSplitR] at ha
      simp only [Formula.atoms]
      refine ha.trans (Finset.inter_subset_inter ?_ ?_)
      · simp only [FormulaFinset.atoms_empty, Finset.union_empty]
        exact hcompat.trans Finset.subset_union_left
      · apply Finset.union_subset
        · simp only [FormulaFinset.atoms_insert, FormulaFinset.atoms_union, hF2at, Formula.atoms]
          exact Finset.union_subset (hAD.trans Finset.subset_union_right)
            (Finset.union_subset Finset.subset_union_left Finset.subset_union_left)
        · rw [FormulaFinset.atoms_singleton]
          exact hAD.trans Finset.subset_union_right

end ProofGentzen



namespace ProvableGentzen

variable {S : Sequent α} {P : PartitionOf S} {h : ⊢ᵍ[GL] S}

noncomputable def interpolant (P : PartitionOf S) (h : ⊢ᵍ[GL] S) := ProofGentzen.interpolant P h.some

lemma interpolant_provable_ant : ⊢ᵍ[GL] (P.Γ₁ ⟹ insert (interpolant P h) P.Δ₁)
  := ProofGentzen.interpolant_provable_ant P h.some

lemma interpolant_provable_suc : ⊢ᵍ[GL] (insert (interpolant P h) P.Γ₂ ⟹ P.Δ₂)
  := ProofGentzen.interpolant_provable_suc P h.some

lemma interpolant_atoms : (interpolant P h).atoms ⊆ (P.Γ₁.atoms ∪ P.Δ₁.atoms) ∩ (P.Γ₂.atoms ∪ P.Δ₂.atoms)
  := ProofGentzen.interpolant_atoms P h.some

end ProvableGentzen


end LogicGL

end
