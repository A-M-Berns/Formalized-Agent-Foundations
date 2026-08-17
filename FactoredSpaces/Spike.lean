/-
# Spike: Factored Space Models (Garrabrant, Mayer, Wache, Lang, Eisenstat, Dell,
  arXiv:2412.02579) — feasibility probe, NOT a formalization.

Purpose: settle the single load-bearing modeling question for this paper — how to
render `Ω = ×_{i∈I} Ω_i`, projections `π_J`, the merge `a · b`, and the Cartesian
product `C_J × C_{I∖J}` in Lean — and then measure how much of §4 and Appendix A
falls out of that choice.

The finding is in `Disintegrates` below: the paper's `C = C_J × C_{I∖J}` is
equivalent to closure under *splicing* two members of `C` at `J`, which is
`Finset.piecewise`. That eliminates every dependent-subtype projection
(`(∀ i : ↥J, Ω i)`) and every transport across `↥(J ∪ K) ≃ ↥J ⊕ ↥K` from the
development.
-/
import Mathlib

namespace FSMSpike

/- One classical decidability instance for the whole file, so that the `Finset.filter`
in `history` and the instances used inside its lemmas are literally the same term.
(Spike finding: with a per-proof `classical`, `history_le` fails with a stuck instance
problem — worth knowing before the real development picks its `history` encoding.) -/
attribute [local instance] Classical.propDecidable

universe u v

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v}

/-- A point of the factored space `Ω = ×_{i∈I} Ω_i`. -/
abbrev Pt (Ω : I → Type v) := ∀ i, Ω i

section Derived

variable {α β γ : Type*}

/-- **Definition 4.1** (Derived Variable): `X ▷_C Y`. -/
def DerivedOn (C : Set (Pt Ω)) (X : Pt Ω → α) (Y : Pt Ω → β) : Prop :=
  ∃ f : α → β, ∀ ω ∈ C, Y ω = f (X ω)

/-- **Lemma C.3**: the alternative characterization of `▷_C`.

NOTE (spike finding, faithfulness): the paper's Lemma C.3 needs `Val(Y)` inhabited,
which it gets implicitly from "let `f(x)` be arbitrary". It fails in the corner
`C = ∅`, `Val(X)` nonempty, `Val(Y)` empty: (ii) is vacuous but no `f` exists.
Formalizing it needs `[Nonempty β]` (harmless — a variable's value space is the
codomain of a function out of a nonempty `Ω`) and that hypothesis must be disclosed. -/
theorem derivedOn_iff [Nonempty β] {C : Set (Pt Ω)} (X : Pt Ω → α) (Y : Pt Ω → β) :
    DerivedOn C X Y ↔ ∀ ω ∈ C, ∀ ω' ∈ C, X ω = X ω' → Y ω = Y ω' := by
  classical
  constructor
  · rintro ⟨f, hf⟩ ω hω ω' hω' hx
    rw [hf ω hω, hf ω' hω', hx]
  · intro h
    refine ⟨fun x => if hx : ∃ ω ∈ C, X ω = x then Y hx.choose else Classical.arbitrary β, ?_⟩
    intro ω hω
    have hx : ∃ ω' ∈ C, X ω' = X ω := ⟨ω, hω, rfl⟩
    show Y ω = if hx : ∃ ω' ∈ C, X ω' = X ω then Y hx.choose else Classical.arbitrary β
    rw [dif_pos hx]
    obtain ⟨hmem, heq⟩ := hx.choose_spec
    exact (h _ hmem _ hω heq).symm

end Derived

/-! ## The modeling decision

`J.piecewise a b` is the point agreeing with `a` on `J` and with `b` off `J`.
It *is* the paper's merge `a_J · b_{I∖J}`, with no subtypes involved. -/

/-- **Definition 4.5** (Disintegration), splice form: `C = C_J × C_{I∖J}`.

The paper's statement is an equality of sets of indexed families; the splice form
below is equivalent (`disintegrates_iff_prod`, sketched in the report) and is what
the whole development actually uses. -/
def Disintegrates (J : Finset I) (C : Set (Pt Ω)) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, J.piecewise a b ∈ C

/-- The paper's `C_J × C_{I∖J}`, rendered back inside `Ω` (which *is* canonically
`Ω_J × Ω_{I∖J}`): the points whose `J`-part is realized by some member of `C` and
whose `(I∖J)`-part is realized by some member of `C`.  No subtypes, no transport. -/
def prodSplit (J : Finset I) (C : Set (Pt Ω)) : Set (Pt Ω) :=
  {ω | (∃ a ∈ C, ∀ i ∈ J, ω i = a i) ∧ (∃ b ∈ C, ∀ i ∉ J, ω i = b i)}

/-- **The load-bearing check of this spike.**  The splice form of Definition 4.5 is
literally the paper's `C = C_J × C_{I∖J}`.  Everything downstream inherits its
faithfulness from this one equivalence. -/
theorem disintegrates_iff_prod (J : Finset I) (C : Set (Pt Ω)) :
    Disintegrates J C ↔ C = prodSplit J C := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · exact fun ω hω => ⟨⟨ω, hω, fun _ _ => rfl⟩, ⟨ω, hω, fun _ _ => rfl⟩⟩
    · rintro ω ⟨⟨a, ha, hJa⟩, ⟨b, hb, hJb⟩⟩
      have : J.piecewise a b = ω := by
        funext i
        by_cases hi : i ∈ J
        · simp [Finset.piecewise, hi, (hJa i hi).symm]
        · simp [Finset.piecewise, hi, (hJb i hi).symm]
      exact this ▸ h a ha b hb
  · intro h a ha b hb
    rw [h]
    exact ⟨⟨a, ha, fun i hi => by simp [Finset.piecewise, hi]⟩,
           ⟨b, hb, fun i hi => by simp [Finset.piecewise, hi]⟩⟩

/-- **Definition 4.6** (Generation): `J` generates `X` given `C`.

Stated with `DerivedOn` so it reads against the paper; `generates_iff` below is the
working form obtained from Lemma C.3. -/
def Generates (J : Finset I) {α : Type*} (X : Pt Ω → α) (C : Set (Pt Ω)) : Prop :=
  DerivedOn C (fun ω i => if i ∈ J then some (ω i) else none) X ∧ Disintegrates J C

theorem generates_iff {α : Type*} [Nonempty α] (J : Finset I) (X : Pt Ω → α)
    (C : Set (Pt Ω)) :
    Generates J X C ↔
      Disintegrates J C ∧ ∀ a ∈ C, ∀ b ∈ C, (∀ i ∈ J, a i = b i) → X a = X b := by
  classical
  rw [Generates, derivedOn_iff]
  constructor
  · rintro ⟨h, hd⟩
    refine ⟨hd, fun a ha b hb hab => h a ha b hb ?_⟩
    funext i
    by_cases hi : i ∈ J <;> simp [hi, hab i]
  · rintro ⟨hd, h⟩
    refine ⟨fun a ha b hb hab => h a ha b hb fun i hi => ?_, hd⟩
    have := congrFun hab i
    simpa [hi] using this

/-! ## Appendix A: the closure lemmas

The paper proves Lemma A.1 with an auxiliary four-fold product `C^×` over about a
page. In splice form both halves are one rewrite of `piecewise` each. -/

theorem piecewise_union (J K : Finset I) (a b : Pt Ω) :
    (J ∪ K).piecewise a b = J.piecewise a (K.piecewise a b) := by
  classical
  funext i
  by_cases hJ : i ∈ J <;> by_cases hK : i ∈ K <;>
    simp [Finset.piecewise, hJ, hK]

theorem piecewise_inter (J K : Finset I) (a b : Pt Ω) :
    (J ∩ K).piecewise a b = J.piecewise (K.piecewise a b) b := by
  classical
  funext i
  by_cases hJ : i ∈ J <;> by_cases hK : i ∈ K <;>
    simp [Finset.piecewise, hJ, hK]

/-- **Lemma A.1** (Disintegration closed under intersection and union). -/
theorem Disintegrates.union {J K : Finset I} {C : Set (Pt Ω)}
    (hJ : Disintegrates J C) (hK : Disintegrates K C) : Disintegrates (J ∪ K) C := by
  intro a ha b hb
  rw [piecewise_union]
  exact hJ a ha _ (hK a ha b hb)

theorem Disintegrates.inter {J K : Finset I} {C : Set (Pt Ω)}
    (hJ : Disintegrates J C) (hK : Disintegrates K C) : Disintegrates (J ∩ K) C := by
  intro a ha b hb
  rw [piecewise_inter]
  exact hJ _ (hK a ha b hb) b hb

/-- **Lemma A.2** (Generation closed under intersection). -/
theorem Generates.inter {α : Type*} [Nonempty α] {J K : Finset I} {X : Pt Ω → α}
    {C : Set (Pt Ω)} (hJ : Generates J X C) (hK : Generates K X C) :
    Generates (J ∩ K) X C := by
  classical
  rw [generates_iff] at hJ hK ⊢
  obtain ⟨hJd, hJf⟩ := hJ
  obtain ⟨hKd, hKf⟩ := hK
  refine ⟨hJd.inter hKd, fun a ha b hb hab => ?_⟩
  -- the splice `c` agrees with `a` on `J` and with `b` on `K`
  set c := J.piecewise a b with hc
  have hcC : c ∈ C := hJd a ha b hb
  have h1 : X c = X a := by
    refine hJf c hcC a ha fun i hi => ?_
    simp [hc, Finset.piecewise, hi]
  have h2 : X c = X b := by
    refine hKf c hcC b hb fun i hi => ?_
    by_cases hJi : i ∈ J
    · simpa [hc, Finset.piecewise, hJi] using hab i (Finset.mem_inter.mpr ⟨hJi, hi⟩)
    · simp [hc, Finset.piecewise, hJi]
  exact h1 ▸ h2

/-! ## Definition 4.6 / Lemma 4.7: the history -/

/-- **Definition 4.6**, the history `H(X | C)` as the intersection of all generating
sets, rendered as the `Finset` infimum over the (finite) family of generating sets. -/
noncomputable def history {α : Type*} (X : Pt Ω → α) (C : Set (Pt Ω)) : Finset I :=
  (Finset.univ.filter (fun J : Finset I => Generates J X C)).inf id

/-- `Finset.univ` always generates (Definition 4.6's remark). -/
theorem generates_univ {α : Type*} [Nonempty α] (X : Pt Ω → α) (C : Set (Pt Ω)) :
    Generates (Finset.univ : Finset I) X C := by
  classical
  rw [generates_iff]
  refine ⟨fun a ha b _ => by simpa [Finset.piecewise] using ha, fun a _ b _ hab => ?_⟩
  have : a = b := funext fun i => hab i (Finset.mem_univ i)
  rw [this]

/-- A nonempty `⊓`-closed family of `Finset I` contains its infimum.  This is the
one piece of genuine (if routine) infrastructure Lemma 4.7 needs. -/
theorem inf_mem_of_inter_closed {S : Finset (Finset I)} (hne : S.Nonempty)
    (hcl : ∀ J ∈ S, ∀ K ∈ S, J ∩ K ∈ S) : S.inf id ∈ S := by
  obtain ⟨M, hM, hmin⟩ := S.exists_min_image Finset.card hne
  have hle : ∀ J ∈ S, M ⊆ J := by
    intro J hJ
    have h1 : M ∩ J ∈ S := hcl M hM J hJ
    have h2 : M.card ≤ (M ∩ J).card := hmin _ h1
    have h3 : M ∩ J = M :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left h2
    exact h3 ▸ Finset.inter_subset_right
  have hEq : S.inf id = M :=
    le_antisymm (Finset.inf_le hM) (Finset.le_inf fun J hJ => hle J hJ)
  rw [hEq]; exact hM

/-- **Lemma 4.7** (History is the minimal generating set) — the `Generates` half. -/
theorem generates_history {α : Type*} [Nonempty α] (X : Pt Ω → α) (C : Set (Pt Ω)) :
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
  have := inf_mem_of_inter_closed hne hcl
  simpa [history] using (Finset.mem_filter.mp this).2

/-- **Lemma 4.7**, the minimality half. -/
theorem history_le {α : Type*} {J : Finset I} {X : Pt Ω → α} {C : Set (Pt Ω)}
    (hJ : Generates J X C) : history X C ⊆ J := by
  have hmem : J ∈ Finset.univ.filter (fun J : Finset I => Generates J X C) := by
    simp [hJ]
  exact Finset.inf_le (f := (id : Finset I → Finset I)) hmem

/-! ## Lemma 4.8, Definition 4.10/4.11, Lemma 4.12 -/

/-- **Lemma 4.8** (History of joint variable). -/
theorem history_pair {α β : Type*} [Nonempty α] [Nonempty β]
    (X : Pt Ω → α) (Y : Pt Ω → β) (C : Set (Pt Ω)) :
    history (fun ω => (X ω, Y ω)) C = history X C ∪ history Y C := by
  classical
  apply Finset.Subset.antisymm
  · -- `H(X|C) ∪ H(Y|C)` generates the pair, so the pair's history is below it
    refine history_le ?_
    rw [generates_iff]
    have hX := generates_history X C
    have hY := generates_history Y C
    rw [generates_iff] at hX hY
    refine ⟨hX.1.union hY.1, fun a ha b hb hab => ?_⟩
    have h1 : X a = X b := hX.2 a ha b hb fun i hi => hab i (Finset.mem_union_left _ hi)
    have h2 : Y a = Y b := hY.2 a ha b hb fun i hi => hab i (Finset.mem_union_right _ hi)
    rw [h1, h2]
  · -- the pair's history generates each component
    have hP := generates_history (fun ω => (X ω, Y ω)) C
    rw [generates_iff] at hP
    refine Finset.union_subset (history_le ?_) (history_le ?_) <;> rw [generates_iff]
    · exact ⟨hP.1, fun a ha b hb hab => congrArg Prod.fst (hP.2 a ha b hb hab)⟩
    · exact ⟨hP.1, fun a ha b hb hab => congrArg Prod.snd (hP.2 a ha b hb hab)⟩

/-! ## Probe of the §6 / Appendix C core

Lemma 6.3 (soundness for events) has two halves: a set-theoretic identity
(`A ∩ B ∩ C = (A∩C)_J × (B∩C)_{I∖J}`) and a measure computation on top of it.  The
set-theoretic half is what the splice encoding is supposed to make cheap; it is proved
here.  The measure half is *not* probed — see the report. -/

/-- `S_J × T_{I∖J}`, rendered in `Ω` by splicing.  Note `prodSplit J C = splice J C C`. -/
def splice (J : Finset I) (S T : Set (Pt Ω)) : Set (Pt Ω) :=
  {ω | ∃ a ∈ S, ∃ b ∈ T, ω = J.piecewise a b}

theorem piecewise_self (J : Finset I) (a : Pt Ω) : J.piecewise a a = a := by
  funext i; by_cases hi : i ∈ J <;> simp [Finset.piecewise, hi]

/-- The indicator variable `1_A` of Definition 4.6's shorthand. -/
def indic (A : Set (Pt Ω)) : Pt Ω → Prop := fun ω => ω ∈ A

/-- **Lemma C.4**, (i) ⟺ (iii): generation of an event is the product identity. -/
theorem generates_indic_iff {J : Finset I} {A C : Set (Pt Ω)} (hd : Disintegrates J C) :
    Generates J (indic A) C ↔ A ∩ C = splice J (A ∩ C) C := by
  rw [generates_iff]
  constructor
  · rintro ⟨-, hf⟩
    apply Set.Subset.antisymm
    · exact fun ω hω => ⟨ω, hω, ω, hω.2, (piecewise_self J ω).symm⟩
    · rintro ω ⟨a, ⟨haA, haC⟩, b, hbC, rfl⟩
      have hmem : J.piecewise a b ∈ C := hd a haC b hbC
      refine ⟨?_, hmem⟩
      have := hf (J.piecewise a b) hmem a haC (fun i hi => by simp [Finset.piecewise, hi])
      exact (propext_iff.mp this).mpr haA
  · intro h
    refine ⟨hd, fun a ha b hb hab => ?_⟩
    have key : ∀ x ∈ C, ∀ y ∈ C, (∀ i ∈ J, x i = y i) → (x ∈ A → y ∈ A) := by
      intro x hx y hy hxy hxA
      have : y = J.piecewise x y := by
        funext i
        by_cases hi : i ∈ J
        · simp [Finset.piecewise, hi, hxy i hi]
        · simp [Finset.piecewise, hi]
      have : y ∈ splice J (A ∩ C) C := ⟨x, ⟨hxA, hx⟩, y, hy, this⟩
      exact ((h ▸ this : y ∈ A ∩ C)).1
    exact propext ⟨fun h1 => key a ha b hb hab h1,
                   fun h2 => key b hb a ha (fun i hi => (hab i hi).symm) h2⟩

/-- The set-theoretic content of **Lemma 6.3** (soundness for events): if `J` generates
`A` given `C` and `I∖J` generates `B` given `C`, then
`A ∩ B ∩ C = (A∩C)_J × (B∩C)_{I∖J}`.  In the paper this is the displayed four-line
computation; here it is the two inclusions below. -/
theorem inter_eq_splice {J : Finset I} {A B C : Set (Pt Ω)}
    (hA : A ∩ C = splice J (A ∩ C) C) (hB : B ∩ C = splice J C (B ∩ C)) :
    A ∩ B ∩ C = splice J (A ∩ C) (B ∩ C) := by
  apply Set.Subset.antisymm
  · rintro ω ⟨⟨hA', hB'⟩, hC⟩
    exact ⟨ω, ⟨hA', hC⟩, ω, ⟨hB', hC⟩, (piecewise_self J ω).symm⟩
  · rintro ω ⟨a, ⟨haA, haC⟩, b, ⟨hbB, hbC⟩, rfl⟩
    have h1 : J.piecewise a b ∈ A ∩ C := hA ▸ ⟨a, ⟨haA, haC⟩, b, hbC, rfl⟩
    have h2 : J.piecewise a b ∈ B ∩ C := hB ▸ ⟨a, haC, b, ⟨hbB, hbC⟩, rfl⟩
    exact ⟨⟨h1.1, h2.1⟩, h1.2⟩

/-- **Definition 4.10** (Structural Independence), unconditional. -/
def StructIndep {α β : Type*} (X : Pt Ω → α) (Y : Pt Ω → β) : Prop :=
  Disjoint (history X (Set.univ : Set (Pt Ω))) (history Y Set.univ)

/-- **Definition 4.11** (Structural Time). -/
def Before {α β : Type*} (X : Pt Ω → α) (Y : Pt Ω → β) : Prop :=
  history X (Set.univ : Set (Pt Ω)) ⊆ history Y Set.univ

/-- The background variable `U_i`. -/
def bg (i : I) : Pt Ω → Ω i := fun ω => ω i

/-- `H(U_i) = {i}` whenever the factor `Ω i` genuinely varies — the witness Lemma 4.12's
"⇐" direction needs.  (Stated as the two inclusions it is used through.) -/
theorem history_bg_subset (i : I) [∀ j, Nonempty (Ω j)] :
    history (bg (Ω := Ω) i) (Set.univ : Set (Pt Ω)) ⊆ {i} := by
  classical
  refine history_le ?_
  rw [generates_iff]
  exact ⟨fun a _ b _ => Set.mem_univ _, fun a _ b _ hab => hab i (Finset.mem_singleton_self i)⟩

/-- **Lemma 4.12** (Structural time and structural independence), the easy direction. -/
theorem structIndep_of_before {α β γ : Type*} {X : Pt Ω → α} {Y : Pt Ω → β}
    (h : Before X Y) (Z : Pt Ω → γ) (hYZ : StructIndep Y Z) : StructIndep X Z :=
  Finset.disjoint_left.mpr fun i hi hiZ =>
    (Finset.disjoint_left.mp hYZ) (h hi) hiZ

end FSMSpike

/-! ## Axiom audit for the spike surface -/

section Audit
variable {I : Type} [DecidableEq I] [Fintype I] {Ω : I → Type}
#print axioms FSMSpike.disintegrates_iff_prod
#print axioms FSMSpike.Disintegrates.union
#print axioms FSMSpike.Disintegrates.inter
#print axioms FSMSpike.Generates.inter
#print axioms FSMSpike.generates_history
#print axioms FSMSpike.history_le
#print axioms FSMSpike.history_pair
#print axioms FSMSpike.generates_indic_iff
#print axioms FSMSpike.inter_eq_splice
#print axioms FSMSpike.structIndep_of_before
end Audit
