import FactoredSpaces.Basic

/-!
# Disintegration, generation and history (§4.2, Appendix A, Lemma C.4)

Definition 4.5's `C = C_J × C_{I∖J}` is stated literally (`prodSplit`), and the working
form — closure of `C` under splicing two of its members at `J`, i.e. under
`J.piecewise a b` — is the proved equivalence `disintegrates_iff_splice` (`dd:splice`).
Every appendix-A argument then becomes a rewrite of `piecewise`.
-/

namespace FactoredSpaces

universe u v

variable {I : Type u} [DecidableEq I] {Ω : I → Type v}

/-- `S_J × T_{I∖J}` for two events `S`, `T`, rendered by splicing: the points
`J.piecewise a b = a_J · b_{I∖J}` with `a ∈ S`, `b ∈ T`.  `prodSplit J C = splice J C C`
(`splice_self`). -/
def splice (J : Finset I) (S T : Set (Pt Ω)) : Set (Pt Ω) :=
  {ω | ∃ a ∈ S, ∃ b ∈ T, ω = J.piecewise a b}

/-- `Finset.piecewise_same` at `Pt Ω`, retained only for the call site in
`Completeness.lean`; use `Finset.piecewise_same` directly. -/
lemma piecewise_self (J : Finset I) (a : Pt Ω) : J.piecewise a a = a :=
  Finset.piecewise_same J a

lemma mem_splice_iff {J : Finset I} {S T : Set (Pt Ω)} {ω : Pt Ω} :
    ω ∈ splice J S T ↔ (∃ a ∈ S, ∀ i ∈ J, ω i = a i) ∧ (∃ b ∈ T, ∀ i ∉ J, ω i = b i) := by
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨⟨a, ha, fun i hi => by simp [Finset.piecewise, hi]⟩,
           ⟨b, hb, fun i hi => by simp [Finset.piecewise, hi]⟩⟩
  · rintro ⟨⟨a, ha, hJa⟩, ⟨b, hb, hJb⟩⟩
    refine ⟨a, ha, b, hb, ?_⟩
    funext i
    by_cases hi : i ∈ J
    · simp [Finset.piecewise, hi, hJa i hi]
    · simp [Finset.piecewise, hi, hJb i hi]

variable [Fintype I]

/-- Splicing at `Jᶜ` swaps the two factors: `S_{I∖J} × T_J = T_J × S_{I∖J}` (the paper's
"commutativity of the Cartesian product over indexed families"). -/
lemma splice_compl (J : Finset I) (S T : Set (Pt Ω)) : splice Jᶜ S T = splice J T S := by
  ext ω
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, Finset.piecewise_compl J a b⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, (Finset.piecewise_compl J b a).symm⟩

/-- The paper's product `C_J × C_{I∖J}` of the two projections of `C`, read back inside
`Ω = Ω_J × Ω_{I∖J}`: the points whose `J`-part is the `J`-part of some member of `C` and
whose `(I∖J)`-part is the `(I∖J)`-part of some member of `C` (`dd:splice`). -/
def prodSplit (J : Finset I) (C : Set (Pt Ω)) : Set (Pt Ω) :=
  {ω | proj J ω ∈ projSet J C ∧ proj Jᶜ ω ∈ projSet Jᶜ C}

/-- **Disintegration.** `J` disintegrates the event `C` if `C = C_J × C_{I∖J}`.

Paper node: Definition 4.5 (§4.2). -/
def Disintegrates (J : Finset I) (C : Set (Pt Ω)) : Prop :=
  C = prodSplit J C

lemma prodSplit_eq_splice (J : Finset I) (C : Set (Pt Ω)) : prodSplit J C = splice J C C := by
  ext ω
  rw [mem_splice_iff]
  simp only [prodSplit, projSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨a, ha, hJa⟩, ⟨b, hb, hJb⟩⟩
    refine ⟨⟨a, ha, fun i hi => ?_⟩, ⟨b, hb, fun i hi => ?_⟩⟩
    · exact (congrFun hJa ⟨i, hi⟩).symm
    · exact (congrFun hJb ⟨i, Finset.mem_compl.mpr hi⟩).symm
  · rintro ⟨⟨a, ha, hJa⟩, ⟨b, hb, hJb⟩⟩
    refine ⟨⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩⟩
    · exact proj_eq_iff.mpr fun i hi => (hJa i hi).symm
    · exact proj_eq_iff.mpr fun i hi => (hJb i (Finset.mem_compl.mp hi)).symm

/-- **The load-bearing equivalence of the encoding** (`dd:splice`): `J` disintegrates
`C` iff `C` is closed under splicing two of its members at `J`.  Everything downstream
uses this form. -/
lemma disintegrates_iff_splice (J : Finset I) (C : Set (Pt Ω)) :
    Disintegrates J C ↔ ∀ a ∈ C, ∀ b ∈ C, J.piecewise a b ∈ C := by
  rw [Disintegrates, prodSplit_eq_splice]
  constructor
  · intro h a ha b hb
    rw [h]
    exact ⟨a, ha, b, hb, rfl⟩
  · intro h
    apply Set.Subset.antisymm
    · exact fun ω hω => ⟨ω, hω, ω, hω, (Finset.piecewise_same J ω).symm⟩
    · rintro ω ⟨a, ha, b, hb, rfl⟩
      exact h a ha b hb

lemma Disintegrates.splice_mem {J : Finset I} {C : Set (Pt Ω)} (h : Disintegrates J C)
    {a b : Pt Ω} (ha : a ∈ C) (hb : b ∈ C) : J.piecewise a b ∈ C :=
  (disintegrates_iff_splice J C).mp h a ha b hb

/-- **Disintegration is closed under union** (the union half of Lemma A.1).

Paper node: Lemma A.1 (§A.1). -/
theorem Disintegrates.union {J K : Finset I} {C : Set (Pt Ω)}
    (hJ : Disintegrates J C) (hK : Disintegrates K C) : Disintegrates (J ∪ K) C := by
  rw [disintegrates_iff_splice] at *
  intro a ha b hb
  rw [Finset.piecewise_union]
  exact hJ a ha _ (hK a ha b hb)

/-- **Disintegration is closed under intersection** (the intersection half of Lemma A.1).

Paper node: Lemma A.1 (§A.1). -/
theorem Disintegrates.inter {J K : Finset I} {C : Set (Pt Ω)}
    (hJ : Disintegrates J C) (hK : Disintegrates K C) : Disintegrates (J ∩ K) C := by
  rw [disintegrates_iff_splice] at *
  intro a ha b hb
  rw [Finset.piecewise_inter]
  exact hJ _ (hK a ha b hb) b hb

/-- The complement of a disintegrating set disintegrates (used in Lemma 6.3's proof). -/
lemma Disintegrates.compl {J : Finset I} {C : Set (Pt Ω)} (hJ : Disintegrates J C) :
    Disintegrates Jᶜ C := by
  rw [disintegrates_iff_splice] at *
  intro a ha b hb
  rw [Finset.piecewise_compl]
  exact hJ b hb a ha

lemma disintegrates_univ (C : Set (Pt Ω)) : Disintegrates (Finset.univ : Finset I) C := by
  rw [disintegrates_iff_splice]
  intro a ha b _
  simpa [Finset.piecewise] using ha

lemma disintegrates_empty (C : Set (Pt Ω)) : Disintegrates (∅ : Finset I) C := by
  rw [disintegrates_iff_splice]
  intro a _ b hb
  simpa [Finset.piecewise] using hb

/-- The disintegration condition is vacuous for the unconditional history: every `J`
disintegrates `Ω` (§4.2, remark after Definition 4.6). -/
lemma disintegrates_univ_set (J : Finset I) : Disintegrates J (Set.univ : Set (Pt Ω)) := by
  rw [disintegrates_iff_splice]
  intros; trivial

/-! ## Generation and history (Definition 4.6) -/

section Generation

variable {α β : Type*}

/-- **Generation.** `J` generates `X` given `C` if `U_J ▷_C X` and `J` disintegrates `C`.

Paper node: Definition 4.6 (§4.2). -/
def Generates (J : Finset I) (X : Pt Ω → α) (C : Set (Pt Ω)) : Prop :=
  DerivedOn C (proj J) X ∧ Disintegrates J C

/-- The working form of generation, obtained from Lemma C.3: `J` disintegrates `C` and
`X` is constant on the members of `C` that agree on `J`. -/
lemma generates_iff [Nonempty α] (J : Finset I) (X : Pt Ω → α) (C : Set (Pt Ω)) :
    Generates J X C ↔
      Disintegrates J C ∧ ∀ a ∈ C, ∀ b ∈ C, (∀ i ∈ J, a i = b i) → X a = X b := by
  rw [Generates, derivedOn_iff]
  constructor
  · rintro ⟨h, hd⟩
    exact ⟨hd, fun a ha b hb hab => h a ha b hb (proj_eq_iff.mpr hab)⟩
  · rintro ⟨hd, h⟩
    exact ⟨fun a ha b hb hab => h a ha b hb (proj_eq_iff.mp hab), hd⟩

/-- **Generation is closed under intersection.**

Paper node: Lemma A.2 (§A.1). -/
theorem Generates.inter [Nonempty α] {J K : Finset I} {X : Pt Ω → α}
    {C : Set (Pt Ω)} (hJ : Generates J X C) (hK : Generates K X C) :
    Generates (J ∩ K) X C := by
  rw [generates_iff] at hJ hK ⊢
  obtain ⟨hJd, hJf⟩ := hJ
  obtain ⟨hKd, hKf⟩ := hK
  refine ⟨hJd.inter hKd, fun a ha b hb hab => ?_⟩
  set c := J.piecewise a b with hc
  have hcC : c ∈ C := hJd.splice_mem ha hb
  have h1 : X c = X a := by
    refine hJf c hcC a ha fun i hi => ?_
    simp [hc, hi]
  have h2 : X c = X b := by
    refine hKf c hcC b hb fun i hi => ?_
    by_cases hJi : i ∈ J
    · simpa [hc, hJi] using hab i (Finset.mem_inter.mpr ⟨hJi, hi⟩)
    · simp [hc, hJi]
  exact h1 ▸ h2

/-- `I` generates every variable given every event (§4.2, remark after Definition 4.6). -/
lemma generates_univ (X : Pt Ω → α) (C : Set (Pt Ω)) :
    Generates (Finset.univ : Finset I) X C :=
  ⟨⟨fun a => X (fun i => a ⟨i, Finset.mem_univ i⟩), fun _ _ => rfl⟩, disintegrates_univ C⟩

lemma Generates.mono_left {J : Finset I} {X : Pt Ω → α} {Y : Pt Ω → β} {C : Set (Pt Ω)}
    (h : Generates J X C) (hXY : DerivedOn C X Y) : Generates J Y C :=
  ⟨h.1.trans hXY, h.2⟩

/-- **History.** `H(X | C)` is the intersection of all `J ⊆ I` that generate `X` given
`C`, i.e. the `Finset` infimum of the (finite) family of generating sets.  The
unconditional history `H(X)` is `history X Set.univ`.

Paper node: Definition 4.6 (§4.2). -/
noncomputable def history (X : Pt Ω → α) (C : Set (Pt Ω)) : Finset I := by
  classical
  exact (Finset.univ.filter (fun J : Finset I => Generates J X C)).inf id

/-- **History is the minimal generating set** — the history generates.

Paper node: Lemma 4.7 (§4.2). -/
theorem generates_history [Nonempty α] (X : Pt Ω → α) (C : Set (Pt Ω)) :
    Generates (history X C) X C := by
  classical
  have hne : (Finset.univ.filter (fun J : Finset I => Generates J X C)).Nonempty :=
    ⟨Finset.univ, by simp [generates_univ X C]⟩
  have hcl : ∀ J ∈ Finset.univ.filter (fun J : Finset I => Generates J X C),
      ∀ K ∈ Finset.univ.filter (fun J : Finset I => Generates J X C),
      J ∩ K ∈ Finset.univ.filter (fun J : Finset I => Generates J X C) := by
    intro J hJ K hK
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ hK ⊢
    exact hJ.inter hK
  -- a nonempty `⊓`-closed family of `Finset I` contains its infimum
  have hmem := Finset.inf'_mem
    (↑(Finset.univ.filter (fun J : Finset I => Generates J X C)) : Set (Finset I))
    (fun x hx y hy => hcl x hx y hy) _ hne id fun i hi => hi
  rw [Finset.inf'_eq_inf] at hmem
  simpa [history] using (Finset.mem_filter.mp hmem).2

/-- **History is the minimal generating set** — every generating set contains the history.

Paper node: Lemma 4.7 (§4.2). -/
theorem history_subset_of_generates {J : Finset I} {X : Pt Ω → α} {C : Set (Pt Ω)}
    (hJ : Generates J X C) : history X C ⊆ J := by
  classical
  have hmem : J ∈ Finset.univ.filter (fun J : Finset I => Generates J X C) := by simp [hJ]
  exact Finset.inf_le (f := (id : Finset I → Finset I)) hmem

/-- **History is the minimal generating set** — packaged as uniqueness: `H(X | C)` is the
unique generating set contained in every generating set.

Paper node: Lemma 4.7 (§4.2). -/
theorem history_unique_minimal [Nonempty α] (X : Pt Ω → α) (C : Set (Pt Ω)) :
    ∃! J : Finset I, Generates J X C ∧ ∀ K, Generates K X C → J ⊆ K := by
  refine ⟨history X C, ⟨generates_history X C, fun _ hK => history_subset_of_generates hK⟩,
    fun J ⟨hJ, hmin⟩ => ?_⟩
  exact Finset.Subset.antisymm (hmin _ (generates_history X C)) (history_subset_of_generates hJ)

lemma generates_iff_history_subset [Nonempty α] {J : Finset I} {X : Pt Ω → α}
    {C : Set (Pt Ω)} (hJ : Disintegrates J C) : Generates J X C ↔ history X C ⊆ J := by
  refine ⟨history_subset_of_generates, fun h => ?_⟩
  -- `U_J ▷_C U_{H} ▷_C X` whenever `H ⊆ J`
  have hJH : DerivedOn C (proj J) (proj (history X C)) :=
    ⟨fun a i => a ⟨i, h i.2⟩, fun _ _ => rfl⟩
  exact ⟨hJH.trans (generates_history X C).1, hJ⟩

lemma history_mono_of_derived [Nonempty α] [Nonempty β] {X : Pt Ω → α} {Y : Pt Ω → β}
    {C : Set (Pt Ω)} (h : DerivedOn C X Y) : history Y C ⊆ history X C :=
  history_subset_of_generates ((generates_history X C).mono_left h)

/-- **History of a joint variable.** `H((X, Y) | C) = H(X | C) ∪ H(Y | C)`.

Paper node: Lemma 4.8 (§4.2). -/
theorem history_pair [Nonempty α] [Nonempty β] (X : Pt Ω → α) (Y : Pt Ω → β)
    (C : Set (Pt Ω)) : history (pair X Y) C = history X C ∪ history Y C := by
  apply Finset.Subset.antisymm
  · refine history_subset_of_generates ?_
    rw [generates_iff]
    have hX := generates_history X C
    have hY := generates_history Y C
    rw [generates_iff] at hX hY
    refine ⟨hX.1.union hY.1, fun a ha b hb hab => ?_⟩
    have h1 : X a = X b := hX.2 a ha b hb fun i hi => hab i (Finset.mem_union_left _ hi)
    have h2 : Y a = Y b := hY.2 a ha b hb fun i hi => hab i (Finset.mem_union_right _ hi)
    simp [pair, h1, h2]
  · have hP := generates_history (pair X Y) C
    exact Finset.union_subset
      (history_subset_of_generates (hP.mono_left (DerivedOn.comp_left Prod.fst)))
      (history_subset_of_generates (hP.mono_left (DerivedOn.comp_left Prod.snd)))

/-- The history of an event `A` given `C`: `H(A | C) = H(1_A | C)` (`dd:event-indicator`). -/
noncomputable abbrev eventHistory (A C : Set (Pt Ω)) : Finset I := history (indic A) C

/-! ## Lemma C.4: generation of an event as a product identity -/

/-- **Alternative characterization of generation** for events, (i) ⟺ (ii): given that `J`
disintegrates `C`, `J` generates `A` given `C` iff members of `C` agreeing on `J` agree on
membership in `A`.

Paper node: Lemma C.4 (§C.1). -/
theorem generates_indic_iff_agree {J : Finset I} {A C : Set (Pt Ω)} (hd : Disintegrates J C) :
    Generates J (indic A) C ↔
      ∀ a ∈ C, ∀ b ∈ C, (∀ i ∈ J, a i = b i) → (a ∈ A ↔ b ∈ A) := by
  rw [generates_iff]
  constructor
  · rintro ⟨-, h⟩ a ha b hb hab
    exact propext_iff.mp (h a ha b hb hab)
  · intro h
    exact ⟨hd, fun a ha b hb hab => propext (h a ha b hb hab)⟩

/-- **Alternative characterization of generation** for events, (i) ⟺ (iii): given that `J`
disintegrates `C`, `J` generates `A` given `C` iff `A ∩ C = (A ∩ C)_J × C_{I∖J}`.

Paper node: Lemma C.4 (§C.1). -/
theorem generates_indic_iff_splice {J : Finset I} {A C : Set (Pt Ω)} (hd : Disintegrates J C) :
    Generates J (indic A) C ↔ A ∩ C = splice J (A ∩ C) C := by
  rw [generates_indic_iff_agree hd]
  constructor
  · intro hf
    apply Set.Subset.antisymm
    · exact fun ω hω => ⟨ω, hω, ω, hω.2, (Finset.piecewise_same J ω).symm⟩
    · rintro ω ⟨a, ⟨haA, haC⟩, b, hbC, rfl⟩
      have hmem : J.piecewise a b ∈ C := hd.splice_mem haC hbC
      refine ⟨?_, hmem⟩
      exact (hf (J.piecewise a b) hmem a haC (fun i hi => by simp [Finset.piecewise, hi])).mpr haA
  · intro h a ha b hb hab
    have key : ∀ x ∈ C, ∀ y ∈ C, (∀ i ∈ J, x i = y i) → (x ∈ A → y ∈ A) := by
      intro x hx y hy hxy hxA
      have : y = J.piecewise x y := by
        funext i
        by_cases hi : i ∈ J
        · simp [Finset.piecewise, hi, hxy i hi]
        · simp [Finset.piecewise, hi]
      have : y ∈ splice J (A ∩ C) C := ⟨x, ⟨hxA, hx⟩, y, hy, this⟩
      exact ((h ▸ this : y ∈ A ∩ C)).1
    exact ⟨key a ha b hb hab, key b hb a ha (fun i hi => (hab i hi).symm)⟩

/-- **Lemma C.4, final clause**: `H(A | C)` is the smallest `J` that disintegrates `C` and
satisfies `A ∩ C = (A ∩ C)_J × C_{I∖J}`.

Paper node: Lemma C.4 (§C.1). -/
theorem eventHistory_minimal_splice (A C : Set (Pt Ω)) :
    (Disintegrates (eventHistory A C) C ∧
        A ∩ C = splice (eventHistory A C) (A ∩ C) C) ∧
      ∀ J : Finset I, Disintegrates J C → A ∩ C = splice J (A ∩ C) C →
        eventHistory A C ⊆ J := by
  have hH := generates_history (indic A) C
  refine ⟨⟨hH.2, (generates_indic_iff_splice hH.2).mp hH⟩, fun J hJ hA => ?_⟩
  exact history_subset_of_generates ((generates_indic_iff_splice hJ).mpr hA)

/-- **History of a variable is the union of the histories of its events.**
`H(X | C) = ⋃_{x ∈ Val(X)} H(x | C)`, where `H(x | C)` is the history of the event
`{X = x}`.  The paper assumes `Val(X)` finite; the union is stated over the whole
codomain (as a set), which needs no finiteness of `Val(X)` — the histories of the
unattained values are empty (`dd:variable`).

Paper node: Lemma 4.9 (§4.2). -/
theorem history_eq_iUnion_fibers [Nonempty α] (X : Pt Ω → α) (C : Set (Pt Ω)) :
    (history X C : Set I) = ⋃ x : α, (eventHistory (fiber X x) C : Set I) := by
  classical
  -- `1_{X = x}` is derived from `X`, so each `H(x | C) ⊆ H(X | C)`
  have hsub : ∀ x : α, eventHistory (fiber X x) C ⊆ history X C := fun x =>
    history_mono_of_derived (DerivedOn.comp_left (fun v : α => v = x))
  -- the union of the (finitely many distinct) histories `H(x | C)` generates `X` given `C`
  set S : Finset (Finset I) := (Set.range fun x : α => eventHistory (fiber X x) C).toFinset
  set U : Finset I := S.sup id
  have hmemU : ∀ x : α, eventHistory (fiber X x) C ⊆ U := fun x => by
    have hx : eventHistory (fiber X x) C ∈ S := Set.mem_toFinset.mpr ⟨x, rfl⟩
    exact Finset.le_sup (f := (id : Finset I → Finset I)) hx
  have hUgen : Generates U X C := by
    rw [generates_iff]
    refine ⟨?_, fun a ha b hb hab => ?_⟩
    · refine Finset.sup_induction (p := fun J => Disintegrates J C) (disintegrates_empty C)
        (fun J hJ K hK => hJ.union hK) ?_
      intro J hJ
      obtain ⟨x, rfl⟩ := Set.mem_toFinset.mp hJ
      exact (generates_history (indic (fiber X x)) C).2
    · have hg := generates_history (indic (fiber X (X a))) C
      rw [generates_indic_iff_agree hg.2] at hg
      have := (hg a ha b hb fun i hi => hab i (hmemU (X a) hi)).mp rfl
      exact this.symm
  apply Set.Subset.antisymm
  · intro i hi
    have hiU : i ∈ U := history_subset_of_generates hUgen hi
    obtain ⟨J, hJ, hiJ⟩ := Finset.mem_sup.mp hiU
    obtain ⟨x, rfl⟩ := Set.mem_toFinset.mp hJ
    exact Set.mem_iUnion.mpr ⟨x, hiJ⟩
  · intro i hi
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hi
    exact hsub x hx

/-- **History of a variable is the union of the histories of its events**, in `Finset`
form for a finite value space `Val(X)` (the paper's hypothesis).

Paper node: Lemma 4.9 (§4.2). -/
theorem history_eq_biUnion_fibers [Nonempty α] [Fintype α] (X : Pt Ω → α) (C : Set (Pt Ω)) :
    history X C = Finset.univ.biUnion fun x : α => eventHistory (fiber X x) C := by
  apply Finset.coe_injective
  rw [history_eq_iUnion_fibers, Finset.coe_biUnion]
  simp

omit [Fintype I] in
/-- The set-theoretic content of Lemma 6.3: if `J` generates `A` given `C` and `I∖J`
generates `B` given `C`, then `A ∩ B ∩ C = (A ∩ C)_J × (B ∩ C)_{I∖J}`. -/
lemma inter_eq_splice {J : Finset I} {A B C : Set (Pt Ω)}
    (hA : A ∩ C = splice J (A ∩ C) C) (hB : B ∩ C = splice J C (B ∩ C)) :
    A ∩ B ∩ C = splice J (A ∩ C) (B ∩ C) := by
  apply Set.Subset.antisymm
  · rintro ω ⟨⟨hA', hB'⟩, hC⟩
    exact ⟨ω, ⟨hA', hC⟩, ω, ⟨hB', hC⟩, (Finset.piecewise_same J ω).symm⟩
  · rintro ω ⟨a, ⟨haA, haC⟩, b, ⟨hbB, hbC⟩, rfl⟩
    have h1 : J.piecewise a b ∈ A ∩ C := hA ▸ ⟨a, ⟨haA, haC⟩, b, hbC, rfl⟩
    have h2 : J.piecewise a b ∈ B ∩ C := hB ▸ ⟨a, haC, b, ⟨hbB, hbC⟩, rfl⟩
    exact ⟨⟨h1.1, h2.1⟩, h1.2⟩

/-! ## Membership criteria for the history (used by the §5.2 development) -/

/-- **Relevance criterion for membership in a history.**  If two members of `C` differ only
at `i` and are separated by `X`, then `i ∈ H(X | C)`.  (The conditional form of the
`←` direction of `mem_history_iff_exists_ne`, which is this lemma at `C = Ω`.) -/
lemma mem_history_of_sep [Nonempty α] {X : Pt Ω → α} {C : Set (Pt Ω)} {i : I} {a b : Pt Ω}
    (ha : a ∈ C) (hb : b ∈ C) (hagree : ∀ j, j ≠ i → a j = b j) (hne : X a ≠ X b) :
    i ∈ history X C := by
  by_contra hi
  have hg := generates_history X C
  rw [generates_iff] at hg
  exact hne (hg.2 a ha b hb fun j hj => hagree j fun h => hi (h ▸ hj))

/-- A factor lies in the (unconditional) history of `X` exactly when `X` is sensitive to
it: two points agreeing off `i` with different `X`-values exist.  The `←` direction is
`mem_history_of_sep` at `C = Ω`. -/
lemma mem_history_iff_exists_ne [Nonempty α] (X : Pt Ω → α) (i : I) :
    i ∈ history X (Set.univ : Set (Pt Ω)) ↔
      ∃ a b : Pt Ω, (∀ j, j ≠ i → a j = b j) ∧ X a ≠ X b := by
  refine ⟨fun hi => ?_, fun ⟨a, b, hab, hne⟩ =>
    mem_history_of_sep (Set.mem_univ a) (Set.mem_univ b) hab hne⟩
  by_contra hcon
  push Not at hcon
  have hgen : Generates (Finset.univ.erase i) X (Set.univ : Set (Pt Ω)) := by
    rw [generates_iff]
    refine ⟨disintegrates_univ_set _, fun a _ b _ hab => ?_⟩
    exact hcon a b fun j hj => hab j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  exact (Finset.mem_erase.mp (history_subset_of_generates hgen hi)).1 rfl

/-- **The mixing criterion.**  If two members of `C` differ only inside `{i, k}` and one of
their two mixed points falls outside `C`, then no set disintegrating `C` separates `i`
from `k`. -/
lemma mem_iff_mem_of_mix {C : Set (Pt Ω)} {J : Finset I} (hJ : Disintegrates J C) {i k : I}
    {a b : Pt Ω} (ha : a ∈ C) (hb : b ∈ C) (hagree : ∀ j, j ≠ i → j ≠ k → a j = b j)
    (hmix : Function.update a k (b k) ∉ C) : i ∈ J ↔ k ∈ J := by
  constructor
  · intro hi
    by_contra hk
    refine hmix ?_
    have heq : J.piecewise a b = Function.update a k (b k) := by
      funext j
      by_cases hj : j ∈ J
      · have hjk : j ≠ k := fun h => hk (h ▸ hj)
        simp [Finset.piecewise, hj, Function.update_of_ne hjk]
      · have hji : j ≠ i := fun h => hj (h ▸ hi)
        by_cases hjk : j = k
        · subst hjk; simp [Finset.piecewise, hj]
        · simp [Finset.piecewise, hj, Function.update_of_ne hjk, (hagree j hji hjk).symm]
    exact heq ▸ hJ.splice_mem ha hb
  · intro hk
    by_contra hi
    refine hmix ?_
    have heq : J.piecewise b a = Function.update a k (b k) := by
      funext j
      by_cases hj : j ∈ J
      · by_cases hjk : j = k
        · subst hjk; simp [Finset.piecewise, hj]
        · have hji : j ≠ i := fun h => hi (h ▸ hj)
          simp [Finset.piecewise, hj, Function.update_of_ne hjk, hagree j hji hjk]
      · have hjk : j ≠ k := fun h => hj (h ▸ hk)
        simp [Finset.piecewise, hj, Function.update_of_ne hjk]
    exact heq ▸ hJ.splice_mem hb ha

end Generation

end FactoredSpaces
