import FiniteFactoredSets.Subpartition

/-!
# History of a subpartition

This file is §4.2 of Garrabrant, *Temporal Inference with Finite Factored Sets*
(arXiv:2109.11513): the history of a subpartition (Definition 24), its well-definedness
and agreement with §3.2 on partitions of `S` (Proposition 22), its basic properties
(Proposition 23), and the two "less basic" facts, Lemmas 1 and 2, that drive Theorem 2.

`[Finite F.B]` (finite dimension) is carried exactly where the paper's proofs use it:
Proposition 22 writes the history as a finite intersection of generating sets, and
everything from there on rests on that.  Orientation is `dd:order-flip` throughout
(paper `X ≤_E Y` is `Y ≤ X`; paper `X ∨_E Y` is `X ⊓ Y`); `dd:subpartition` fixes the
carrier of subpartitions.

## The one place §4.2 does not mirror §3.2

Generation of a *subpartition* is not closed under supersets (the paper's remark after
Proposition 21), so `generates_iff_history_subset`'s analogue is false as an iff over
`h^F(X) ⊆ C` alone: over `S = Bool × Bool` with the coordinate factors and
`E = {(0,0), (1,1)}`, the subpartition `Ind_E` has empty history, yet `{fst}` does not
generate it because `χ^F_{fst}((0,0),(1,1)) = (0,1) ∉ E`.  What survives is
`generatesSub_iff_historySub_subset`, which carries the second half of Proposition 20
clause 7 as an explicit conjunct.
-/

universe u

namespace FiniteFactoredSets

variable {S : Type u}

namespace FactoredSet

open scoped Classical
open Subpartition

variable (F : FactoredSet S)

/-! ### Two working forms of Proposition 21

Generation of a subpartition is closed under union but *not* under supersets, so the two
lemmas below are what stand in for `generates_spec`'s monotonicity clause everywhere in
this file. -/

/-- Generating `Ind_E` is exactly the second half of Proposition 20 clause 7,
`χ^F_C(E,E) = E`, in relational form. -/
private lemma generatesSub_indiscrete_iff (C : Set (Setoid S)) (E : Set S) :
    F.GeneratesSub C (indiscrete E) ↔ ∀ s ∈ E, ∀ t ∈ E, F.chimera C s t ∈ E := by
  rw [F.generatesSub_iff_rel]
  simp only [dom_indiscrete]
  exact ⟨fun h s hs t ht => (h s hs t ht).1, fun h s hs t ht => ⟨h s hs t ht, hs⟩⟩

/-- Adjoining to `C` any `D` that generates *some* subpartition of the same domain
preserves generation.  This is the mechanism behind Proposition 21 clause 5's union half,
in the form §4.2 needs: `D` need not generate `X` itself. -/
private lemma generatesSub_union_of_dom_eq {C D : Set (Setoid S)} {X Z : Subpartition S}
    (hE : X.dom = Z.dom) (hX : F.GeneratesSub C X) (hZ : F.GeneratesSub D Z) :
    F.GeneratesSub (C ∪ D) X := by
  rw [F.generatesSub_iff_rel] at hX hZ ⊢
  intro s hs t ht
  rw [F.chimera_union]
  refine hX s hs _ ?_
  have hs' : s ∈ Z.dom := by rw [← hE]; exact hs
  have ht' : t ∈ Z.dom := by rw [← hE]; exact ht
  rw [hE]
  exact mem_dom_of_rel (hZ s hs' t ht')

/-! ## §4.2 History of a subpartition -/

/-- Definition 24: the history `h^F(X)` of a subpartition — the smallest subset of `B`
generating `X`, rendered as the intersection of all generating subsets of `B`; that this
is itself generating is Proposition 22.

Paper node: Definition 24 (§4.2). -/
def historySub (X : Subpartition S) : Set (Setoid S) :=
  ⋂₀ {C | C ⊆ F.B ∧ F.GeneratesSub C X}

lemma historySub_subset (X : Subpartition S) : F.historySub X ⊆ F.B :=
  Set.sInter_subset_of_mem
    (show F.B ∈ {C | C ⊆ F.B ∧ F.GeneratesSub C X} from
      ⟨subset_rfl, (F.generatesSub_spec F.B F.B X X X rfl).2.2.1⟩)

lemma historySub_subset_of_generatesSub {C : Set (Setoid S)} {X : Subpartition S}
    (hC : C ⊆ F.B) (h : F.GeneratesSub C X) : F.historySub X ⊆ C :=
  Set.sInter_subset_of_mem (show C ∈ {C | C ⊆ F.B ∧ F.GeneratesSub C X} from ⟨hC, h⟩)

/-- The paper's "we can express `h^F(X)` as a composition of finitely many binary
intersections", as an induction: a finite family of generating sets, intersected into any
generating `D`, still generates.  Clause 5 of Proposition 21 is the induction step and `D`
carries the nonemptiness the paper's argument needs. -/
private lemma generatesSub_inter_sInter (X : Subpartition S) {𝒞 : Set (Set (Setoid S))}
    (hfin : 𝒞.Finite) :
    (∀ C ∈ 𝒞, F.GeneratesSub C X) →
      ∀ D : Set (Setoid S), F.GeneratesSub D X → F.GeneratesSub (D ∩ ⋂₀ 𝒞) X := by
  induction 𝒞, hfin using Set.Finite.induction_on with
  | empty => intro _ D hD; simpa using hD
  | @insert a s _ _ ih =>
    intro hall D hD
    rw [Set.sInter_insert, ← Set.inter_assoc]
    exact ih (fun C hC => hall C (Set.mem_insert_of_mem _ hC)) (D ∩ a)
      ((F.generatesSub_spec D a X X X rfl).2.2.2.2.1 hD (hall a (Set.mem_insert _ _))).1

lemma generatesSub_historySub [Finite F.B] (X : Subpartition S) :
    F.GeneratesSub (F.historySub X) X := by
  have hfam : {C : Set (Setoid S) | C ⊆ F.B ∧ F.GeneratesSub C X}.Finite :=
    ((Set.toFinite F.B).finite_subsets).subset fun _ hC => hC.1
  have h : F.GeneratesSub (F.B ∩ F.historySub X) X :=
    F.generatesSub_inter_sInter X hfam (fun _ hC => hC.2) F.B
      (F.generatesSub_spec F.B F.B X X X rfl).2.2.1
  rwa [Set.inter_eq_self_of_subset_right (F.historySub_subset X)] at h

/-- **Proposition 22** — the history of a subpartition is well-defined (it is the least
generating subset of `B`), and on a partition of `S` it coincides with Definition 17.

Paper node: Proposition 22 (§4.2). -/
theorem historySub_isLeast_and_eq_history [Finite F.B] :
    (∀ X : Subpartition S, IsLeast {C | C ⊆ F.B ∧ F.GeneratesSub C X} (F.historySub X)) ∧
    ∀ X : Setoid S, F.historySub (ofSetoid X) = F.history X := by
  refine ⟨fun X => ⟨⟨F.historySub_subset X, F.generatesSub_historySub X⟩,
    fun C hC => F.historySub_subset_of_generatesSub hC.1 hC.2⟩, fun X => ?_⟩
  have hfam : {C : Set (Setoid S) | C ⊆ F.B ∧ F.GeneratesSub C (ofSetoid X)}
      = {C : Set (Setoid S) | C ⊆ F.B ∧ F.Generates C X} := by
    ext C
    simp only [Set.mem_setOf_eq, F.generatesSub_ofSetoid]
  show ⋂₀ {C : Set (Setoid S) | C ⊆ F.B ∧ F.GeneratesSub C (ofSetoid X)} = F.history X
  rw [hfam]
  rfl

/-- For `C ⊆ B`, `C` generates `X` exactly when it contains the history **and** satisfies
the second half of Proposition 20 clause 7, `χ^F_C(E,E) = E`.

The second conjunct is not removable, and this is the one point where §4.2 genuinely
departs from `generates_iff_history_subset`: generation of a subpartition is not closed
under supersets, so containing the history does not suffice.  See the counterexample in
this file's module docstring. -/
lemma generatesSub_iff_historySub_subset [Finite F.B] {C : Set (Setoid S)}
    (hC : C ⊆ F.B) (X : Subpartition S) :
    F.GeneratesSub C X ↔
      F.historySub X ⊆ C ∧ ∀ s ∈ X.dom, ∀ t ∈ X.dom, F.chimera C s t ∈ X.dom := by
  constructor
  · intro h
    refine ⟨F.historySub_subset_of_generatesSub hC h, ?_⟩
    rw [F.generatesSub_iff_rel] at h
    exact fun s hs t ht => mem_dom_of_rel (h s hs t ht)
  · rintro ⟨hsub, hchi⟩
    have hind : F.GeneratesSub C (indiscrete X.dom) :=
      (F.generatesSub_indiscrete_iff C X.dom).2 hchi
    have hgen := F.generatesSub_union_of_dom_eq (Z := indiscrete X.dom)
      (dom_indiscrete X.dom).symm (F.generatesSub_historySub X) hind
    rwa [Set.union_eq_right.2 hsub] at hgen

/-- Clause 1 of Proposition 23, isolated: a coarser subpartition of the same domain has a
smaller history (`dd:order-flip` — the paper's `X ≤_E Y` is `Y ≤ X`). -/
private lemma historySub_mono [Finite F.B] {X Y : Subpartition S} (hE : X.dom = Y.dom)
    (hYX : Y ≤ X) : F.historySub X ⊆ F.historySub Y :=
  F.historySub_subset_of_generatesSub (F.historySub_subset Y)
    ((F.generatesSub_spec (F.historySub Y) (F.historySub Y) X Y Y hE).1 hYX
      (F.generatesSub_historySub Y))

/-- **Proposition 23** — the five basic properties of the history of subpartitions, for
`X`, `Y` of the same domain `E` and arbitrary `Z`.  Clause 1's `X ≤_E Y` is `Y ≤ X`,
clause 2's `X ∨_E Y` is `X ⊓ Y`, clause 4's `Ind_E` is `indiscrete E`; clause 3 uses
`Subset` (inclusion as sets of blocks); clause 5 is Proposition 13 clause 4 restated on
`ofSetoid b`.

Paper node: Proposition 23 (§4.2). -/
theorem historySub_spec [Finite F.B] (X Y Z : Subpartition S) (hE : X.dom = Y.dom) :
    (Y ≤ X → F.historySub X ⊆ F.historySub Y) ∧
    F.historySub (X ⊓ Y) = F.historySub X ∪ F.historySub Y ∧
    (X.Subset Z → F.historySub X ⊆ F.historySub Z) ∧
    (F.historySub X = ∅ ↔ X = indiscrete X.dom) ∧
    (Nonempty S → ∀ b ∈ F.B, F.historySub (ofSetoid b) = {b}) := by
  have hdom : (X ⊓ Y).dom = X.dom := by rw [dom_inf, ← hE, Set.inter_self]
  refine ⟨F.historySub_mono hE, ?_, ?_, ?_, ?_⟩
  · refine Set.Subset.antisymm ?_ ?_
    · -- `h^F(X) ∪ h^F(Y)` generates both `X` and `Y`, hence `X ⊓ Y`.
      have hgX : F.GeneratesSub (F.historySub X ∪ F.historySub Y) X :=
        F.generatesSub_union_of_dom_eq hE (F.generatesSub_historySub X)
          (F.generatesSub_historySub Y)
      have hgY : F.GeneratesSub (F.historySub X ∪ F.historySub Y) Y := by
        have h := F.generatesSub_union_of_dom_eq hE.symm (F.generatesSub_historySub Y)
          (F.generatesSub_historySub X)
        rwa [Set.union_comm] at h
      exact F.historySub_subset_of_generatesSub
        (Set.union_subset (F.historySub_subset X) (F.historySub_subset Y))
        ((F.generatesSub_spec (F.historySub X ∪ F.historySub Y)
          (F.historySub X ∪ F.historySub Y) X Y Y hE).2.1 hgX hgY)
    · exact Set.union_subset (F.historySub_mono hdom.symm fun _ _ h => h.1)
        (F.historySub_mono (hE.symm.trans hdom.symm) fun _ _ h => h.2)
  · intro hXZ
    exact F.historySub_subset_of_generatesSub (F.historySub_subset Z)
      ((F.generatesSub_spec (F.historySub Z) (F.historySub Z) X X Z rfl).2.2.2.2.2 hXZ
        (F.generatesSub_historySub Z))
  · constructor
    · intro h
      have hgen : F.GeneratesSub ∅ X := by rw [← h]; exact F.generatesSub_historySub X
      exact (F.generatesSub_spec ∅ ∅ X X X rfl).2.2.2.1.1 hgen
    · intro h
      exact Set.subset_empty_iff.1 (F.historySub_subset_of_generatesSub (Set.empty_subset _)
        ((F.generatesSub_spec ∅ ∅ X X X rfl).2.2.2.1.2 h))
  · intro hS b hb
    rw [F.historySub_isLeast_and_eq_history.2 b]
    exact (F.history_spec b b).2.2.2 hS b hb

/-! ### Lemma 1

The paper's proof opens by showing that the *complement* of one history generates the
other subpartition; the three private lemmas below are its three paragraphs. -/

/-- Lemma 1, first paragraph: if `h^F(X)` and `h^F(Y)` are disjoint then `B ∖ h^F(X)`
generates `Y`.  Both halves of Proposition 20 clause 7 are in play — the containment
`h^F(Y) ⊆ B ∖ h^F(X)`, and `χ^F_{B∖h^F(X)}(E,E) = χ^F_{h^F(X)}(E,E) = E`. -/
private lemma generatesSub_sdiff_historySub [Finite F.B] {X Y : Subpartition S}
    (hE : X.dom = Y.dom) (h : F.historySub X ∩ F.historySub Y = ∅) :
    F.GeneratesSub (F.B \ F.historySub X) Y := by
  have hXrel : ∀ a ∈ X.dom, ∀ b ∈ X.dom, X (F.chimera (F.historySub X) a b) a :=
    (F.generatesSub_iff_rel _ X).1 (F.generatesSub_historySub X)
  have hsub : F.historySub Y ⊆ F.B \ F.historySub X := fun b hb =>
    ⟨F.historySub_subset Y hb, fun hb' => by
      have : b ∈ F.historySub X ∩ F.historySub Y := ⟨hb', hb⟩
      rw [h] at this
      exact this⟩
  have hind : F.GeneratesSub (F.B \ F.historySub X) (indiscrete Y.dom) := by
    refine (F.generatesSub_indiscrete_iff _ _).2 fun a ha b hb => ?_
    rw [F.chimera_sdiff, ← hE] at *
    exact mem_dom_of_rel (hXrel b hb a ha)
  have hgen := F.generatesSub_union_of_dom_eq (Z := indiscrete Y.dom)
    (dom_indiscrete Y.dom).symm (F.generatesSub_historySub Y) hind
  rwa [Set.union_eq_right.2 hsub] at hgen

/-- Lemma 1, second paragraph: `h^F(X) ⊢^F X|y` for every block `y` of `Y`, hence
`h^F(X|y) ⊆ h^F(X)`. -/
private lemma generatesSub_historySub_restrict [Finite F.B] {X Y : Subpartition S}
    (hE : X.dom = Y.dom) (hBX : F.GeneratesSub (F.B \ F.historySub X) Y) {s : S} :
    F.GeneratesSub (F.historySub X) (X.restrict (Y.part s)) := by
  have hXrel : ∀ a ∈ X.dom, ∀ b ∈ X.dom, X (F.chimera (F.historySub X) a b) a :=
    (F.generatesSub_iff_rel _ X).1 (F.generatesSub_historySub X)
  have hBXrel : ∀ a ∈ Y.dom, ∀ b ∈ Y.dom, Y (F.chimera (F.B \ F.historySub X) a b) a :=
    (F.generatesSub_iff_rel _ Y).1 hBX
  refine (F.generatesSub_iff_rel _ _).2 fun a ha b hb => ?_
  rw [dom_restrict] at ha hb
  obtain ⟨haX, hay⟩ := ha
  obtain ⟨hbX, hby⟩ := hb
  refine ⟨?_, hay, hXrel a haX b hbX⟩
  have haY : a ∈ Y.dom := by rw [← hE]; exact haX
  have hbY : b ∈ Y.dom := by rw [← hE]; exact hbX
  have h1 := hBXrel b hbY a haY
  rw [F.chimera_sdiff] at h1
  exact Y.trans' h1 hby

/-- Lemma 1, third paragraph: any `D ⊆ B ∖ h^F(Y)` generating `X|y` already generates `X`.
This is the step the paper spends its displayed equation on; `D` is left abstract because
it is instantiated at `h^F(X|y)`. -/
private lemma generatesSub_of_generatesSub_restrict [Finite F.B] {X Y : Subpartition S}
    (hE : X.dom = Y.dom) {s : S} (hs : s ∈ Y.dom)
    (hBY : F.GeneratesSub (F.B \ F.historySub Y) X)
    {D : Set (Setoid S)} (hDBY : D ⊆ F.B \ F.historySub Y)
    (hD : F.GeneratesSub D (X.restrict (Y.part s))) : F.GeneratesSub D X := by
  have hYrel : ∀ a ∈ Y.dom, ∀ b ∈ Y.dom, Y (F.chimera (F.historySub Y) a b) a :=
    (F.generatesSub_iff_rel _ Y).1 (F.generatesSub_historySub Y)
  have hBYrel : ∀ a ∈ X.dom, ∀ b ∈ X.dom, X (F.chimera (F.B \ F.historySub Y) a b) a :=
    (F.generatesSub_iff_rel _ X).1 hBY
  have hDrel := (F.generatesSub_iff_rel D (X.restrict (Y.part s))).1 hD
  have hsX : s ∈ X.dom := by rw [hE]; exact hs
  refine (F.generatesSub_iff_rel _ X).2 fun s₀ hs₀ t₀ ht₀ => ?_
  have hs₀Y : s₀ ∈ Y.dom := by rw [← hE]; exact hs₀
  have ht₀Y : t₀ ∈ Y.dom := by rw [← hE]; exact ht₀
  -- `p` and `q` are `s₀` and `t₀` transported into the block `y = [s]_Y`.
  have hp : Y (F.chimera (F.historySub Y) s s₀) s := hYrel s hs s₀ hs₀Y
  have hq : Y (F.chimera (F.historySub Y) s t₀) s := hYrel s hs t₀ ht₀Y
  have hpdom : F.chimera (F.historySub Y) s s₀ ∈ (X.restrict (Y.part s)).dom := by
    rw [dom_restrict]
    exact ⟨by rw [hE]; exact mem_dom_of_rel hp, hp⟩
  have hqdom : F.chimera (F.historySub Y) s t₀ ∈ (X.restrict (Y.part s)).dom := by
    rw [dom_restrict]
    exact ⟨by rw [hE]; exact mem_dom_of_rel hq, hq⟩
  -- `s'` is `X`-related to `s₀` …
  have hs' : X (F.chimera D (F.chimera (F.historySub Y) s s₀)
      (F.chimera (F.historySub Y) s t₀)) s₀ := by
    have h1 := hDrel _ hpdom _ hqdom
    have h2 : X (F.chimera (F.historySub Y) s s₀) s₀ := by
      have h3 := hBYrel s₀ hs₀ s hsX
      rwa [F.chimera_sdiff] at h3
    exact X.trans' h1.2.2 h2
  -- … and `χ^F_D(s₀,t₀)` is `χ^F_{B∖h^F(Y)}(s', t₀)`.
  have hmid : F.chimera (F.B \ F.historySub Y) (F.chimera D s₀ t₀) s
      = F.chimera D (F.chimera (F.historySub Y) s s₀)
        (F.chimera (F.historySub Y) s t₀) := by
    rw [F.chimera_sdiff, F.chimera_left_comm]
  have hkey : F.chimera D s₀ t₀
      = F.chimera (F.B \ F.historySub Y)
        (F.chimera D (F.chimera (F.historySub Y) s s₀)
          (F.chimera (F.historySub Y) s t₀)) t₀ := by
    rw [← hmid, F.chimera_left_idem]
    conv_lhs => rw [← Set.inter_eq_right.2 hDBY]
    rw [F.chimera_inter]
  rw [hkey]
  exact X.trans' (hBYrel _ (mem_dom_of_rel hs') t₀ ht₀) hs'

/-- **Lemma 1** — for subpartitions `X`, `Y` of the same domain with disjoint histories,
restricting `X` to any block `y` of `Y` leaves its history unchanged: `h^F(X) = h^F(X|y)`.
The blocks of `Y` are `Y.part s` for `s ∈ Y.dom`.

Paper node: Lemma 1 (§4.2). -/
theorem historySub_restrict_part_eq [Finite F.B] {X Y : Subpartition S} (hE : X.dom = Y.dom)
    (h : F.historySub X ∩ F.historySub Y = ∅) {s : S} (hs : s ∈ Y.dom) :
    F.historySub X = F.historySub (X.restrict (Y.part s)) := by
  have hBX : F.GeneratesSub (F.B \ F.historySub X) Y :=
    F.generatesSub_sdiff_historySub hE h
  have hBY : F.GeneratesSub (F.B \ F.historySub Y) X :=
    F.generatesSub_sdiff_historySub hE.symm (by rw [Set.inter_comm]; exact h)
  have hstepB : F.GeneratesSub (F.historySub X) (X.restrict (Y.part s)) :=
    F.generatesSub_historySub_restrict hE hBX
  have hDX : F.historySub (X.restrict (Y.part s)) ⊆ F.historySub X :=
    F.historySub_subset_of_generatesSub (F.historySub_subset X) hstepB
  have hDBY : F.historySub (X.restrict (Y.part s)) ⊆ F.B \ F.historySub Y := fun b hb =>
    ⟨F.historySub_subset _ hb, fun hb' => by
      have : b ∈ F.historySub X ∩ F.historySub Y := ⟨hDX hb, hb'⟩
      rw [h] at this
      exact this⟩
  exact Set.Subset.antisymm
    (F.historySub_subset_of_generatesSub (F.historySub_subset _)
      (F.generatesSub_of_generatesSub_restrict hE hs hBY hDBY
        (F.generatesSub_historySub _)))
    hDX

/-! ### Lemma 2

The paper proves the case `|X| = 2` and then reduces `|X| ≥ 3` to it through
`X ∨_E Y = ⋁_E {(Y|x) ∪ {E ∖ x} | x ∈ X}`.  The Lean proof instead runs the `|X| = 2`
computation as an *induction step*, adjoining one `h^F(Y|x)` at a time to a set already
generating `X`; the paper's "fix some `r ∈ x₁`" becomes "fix the representative `r` whose
block is `x`", and no case split on `|X|` is needed.  The family of `h^F(Y|x)` is finite
because each is a subset of the finite `B`, even when `X` has infinitely many blocks. -/

/-- The induction step behind Lemma 2 — the paper's `|X| = 2` computation. -/
private lemma generatesSub_union_historySub_restrict [Finite F.B] {X Y : Subpartition S}
    (hE : X.dom = Y.dom) {A : Set (Setoid S)} (hA : F.GeneratesSub A X) {r : S}
    (hr : r ∈ X.dom) :
    F.GeneratesSub (A ∪ F.historySub (Y.restrict (X.part r))) X := by
  have hArel := (F.generatesSub_iff_rel A X).1 hA
  have hCrel := (F.generatesSub_iff_rel (F.historySub (Y.restrict (X.part r)))
    (Y.restrict (X.part r))).1 (F.generatesSub_historySub _)
  refine (F.generatesSub_iff_rel _ X).2 fun s hs t ht => ?_
  have hp : X (F.chimera A r s) r := hArel r hr s hs
  have hq : X (F.chimera A r t) r := hArel r hr t ht
  have hpdom : F.chimera A r s ∈ (Y.restrict (X.part r)).dom := by
    rw [dom_restrict]
    exact ⟨by rw [← hE]; exact mem_dom_of_rel hp, hp⟩
  have hqdom : F.chimera A r t ∈ (Y.restrict (X.part r)).dom := by
    rw [dom_restrict]
    exact ⟨by rw [← hE]; exact mem_dom_of_rel hq, hq⟩
  have hw : F.chimera (F.historySub (Y.restrict (X.part r))) (F.chimera A r s)
      (F.chimera A r t) ∈ X.dom := by
    have h1 := mem_dom_of_rel (hCrel _ hpdom _ hqdom)
    rw [dom_restrict] at h1
    rw [hE]
    exact h1.1
  have hchain : F.chimera (A ∪ F.historySub (Y.restrict (X.part r))) s t
      = F.chimera A s (F.chimera (F.historySub (Y.restrict (X.part r)))
        (F.chimera A r s) (F.chimera A r t)) := by
    rw [F.chimera_union, ← F.chimera_left_comm, F.chimera_right_idem]
  rw [hchain]
  exact hArel s hs _ hw

/-- The induction itself: adjoining a finite family of `h^F(Y|x)`, `x` a block of `X`, to a
set generating `X` still generates `X`. -/
private lemma generatesSub_union_sUnion [Finite F.B] {X Y : Subpartition S}
    (hE : X.dom = Y.dom) {𝒟 : Set (Set (Setoid S))} (hfin : 𝒟.Finite) :
    (∀ a ∈ 𝒟, ∃ r ∈ X.dom, a = F.historySub (Y.restrict (X.part r))) →
      ∀ A : Set (Setoid S), F.GeneratesSub A X → F.GeneratesSub (A ∪ ⋃₀ 𝒟) X := by
  induction 𝒟, hfin using Set.Finite.induction_on with
  | empty => intro _ A hA; simpa using hA
  | @insert a 𝒟' _ _ ih =>
    intro hall A hA
    obtain ⟨r, hr, rfl⟩ := hall a (Set.mem_insert _ _)
    rw [Set.sUnion_insert, ← Set.union_assoc]
    exact ih (fun b hb => hall b (Set.mem_insert_of_mem _ hb)) _
      (F.generatesSub_union_historySub_restrict hE hA hr)

/-- **Lemma 2** — for subpartitions `X`, `Y` of the same domain,
`h^F(X ∨_E Y) = h^F(X) ∪ ⋃_{x ∈ X} h^F(Y|x)`, the blocks `x` of `X` being `X.part s` for
`s ∈ X.dom`.

Paper node: Lemma 2 (§4.2). -/
theorem historySub_inf_eq [Finite F.B] {X Y : Subpartition S} (hE : X.dom = Y.dom) :
    F.historySub (X ⊓ Y) =
      F.historySub X ∪ ⋃ s ∈ X.dom, F.historySub (Y.restrict (X.part s)) := by
  have hdom : (X ⊓ Y).dom = X.dom := by rw [dom_inf, ← hE, Set.inter_self]
  refine Set.Subset.antisymm ?_ ?_
  · -- The right-hand side generates `X ⊓ Y`.
    have hfin : {a : Set (Setoid S) |
        ∃ r ∈ X.dom, a = F.historySub (Y.restrict (X.part r))}.Finite := by
      refine ((Set.toFinite F.B).finite_subsets).subset ?_
      rintro a ⟨r, -, rfl⟩
      exact F.historySub_subset _
    have hsU : ⋃₀ {a : Set (Setoid S) |
        ∃ r ∈ X.dom, a = F.historySub (Y.restrict (X.part r))}
        = ⋃ r ∈ X.dom, F.historySub (Y.restrict (X.part r)) := by
      ext b
      simp only [Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨a, ⟨r, hr, rfl⟩, hb⟩
        exact ⟨r, hr, hb⟩
      · rintro ⟨r, hr, hb⟩
        exact ⟨_, ⟨r, hr, rfl⟩, hb⟩
    have hgenX : F.GeneratesSub (F.historySub X ∪
        ⋃ r ∈ X.dom, F.historySub (Y.restrict (X.part r))) X := by
      rw [← hsU]
      exact F.generatesSub_union_sUnion hE hfin (fun _ ha => ha) _
        (F.generatesSub_historySub X)
    have hXrel := (F.generatesSub_iff_rel _ X).1 hgenX
    refine F.historySub_subset_of_generatesSub
      (Set.union_subset (F.historySub_subset X)
        (Set.iUnion₂_subset fun r _ => F.historySub_subset _)) ?_
    refine (F.generatesSub_iff_rel _ (X ⊓ Y)).2 fun s hs t ht => ?_
    rw [hdom] at hs ht
    have hXst := hXrel s hs t ht
    refine ⟨hXst, ?_⟩
    -- The `Y`-half comes from `h^F(Y|[s]_X)`, which is one of the sets in the union.
    have hsub : F.historySub (Y.restrict (X.part s)) ⊆
        F.historySub X ∪ ⋃ r ∈ X.dom, F.historySub (Y.restrict (X.part r)) := fun b hb =>
      Or.inr (Set.mem_biUnion hs hb)
    have hu : F.chimera (F.historySub X ∪
        ⋃ r ∈ X.dom, F.historySub (Y.restrict (X.part r))) s t
        = F.chimera (F.historySub (Y.restrict (X.part s))) s
          (F.chimera (F.historySub X ∪
            ⋃ r ∈ X.dom, F.historySub (Y.restrict (X.part r))) s t) := by
      conv_lhs => rw [← Set.union_eq_right.2 hsub]
      rw [F.chimera_union]
    have hsdom : s ∈ (Y.restrict (X.part s)).dom := by
      rw [dom_restrict]
      exact ⟨by rw [← hE]; exact hs, hs⟩
    have hudom : F.chimera (F.historySub X ∪
        ⋃ r ∈ X.dom, F.historySub (Y.restrict (X.part r))) s t
        ∈ (Y.restrict (X.part s)).dom := by
      rw [dom_restrict]
      exact ⟨by rw [← hE]; exact mem_dom_of_rel hXst, hXst⟩
    have hY := (F.generatesSub_iff_rel _ (Y.restrict (X.part s))).1
      (F.generatesSub_historySub _) s hsdom _ hudom
    rw [← hu] at hY
    exact hY.2.2
  · refine Set.union_subset (F.historySub_mono hdom.symm fun _ _ h => h.1) ?_
    refine Set.iUnion₂_subset fun r hr => ?_
    exact F.historySub_subset_of_generatesSub (F.historySub_subset _)
      ((F.generatesSub_spec (F.historySub (X ⊓ Y)) (F.historySub (X ⊓ Y))
        (Y.restrict (X.part r)) (Y.restrict (X.part r)) (X ⊓ Y) rfl).2.2.2.2.2
        (restrict_part_subset_inf hE hr) (F.generatesSub_historySub (X ⊓ Y)))

/-- Proposition 22 read as a client would: `IsLeast` is consumed by its two projections —
the history generates, and it is below every generating subset of `B`. -/
example [Finite F.B] {C : Set (Setoid S)} (X : Subpartition S) (hC : C ⊆ F.B)
    (h : F.GeneratesSub C X) :
    F.GeneratesSub (F.historySub X) X ∧ F.historySub X ⊆ C :=
  ⟨(F.historySub_isLeast_and_eq_history.1 X).1.2,
    (F.historySub_isLeast_and_eq_history.1 X).2 ⟨hC, h⟩⟩

/-- Proposition 22's second sentence, as a transport a client would use to move a §3.2
history computation into §4.2's vocabulary. -/
example [Finite F.B] (X : Setoid S) (hX : F.history X = ∅) :
    F.historySub (ofSetoid X) = ∅ := by
  rw [F.historySub_isLeast_and_eq_history.2 X, hX]

/-- Proposition 23 read as a client would: a clause is projected out and applied. -/
example [Finite F.B] (X Y : Subpartition S) (hE : X.dom = Y.dom) :
    F.historySub (X ⊓ Y) = F.historySub X ∪ F.historySub Y :=
  (F.historySub_spec X Y X hE).2.1

/-- `generatesSub_iff_historySub_subset` used the way a client enlarges a generating set:
adjoining `D ⊆ B` to the history still generates, *provided* the chimera condition is
rechecked at the enlarged set.  There is no monotonicity lemma to reach for instead — the
second conjunct is exactly what fails in the module docstring's counterexample. -/
example [Finite F.B] {D : Set (Setoid S)} (X : Subpartition S) (hD : D ⊆ F.B)
    (hχ : ∀ s ∈ X.dom, ∀ t ∈ X.dom, F.chimera (F.historySub X ∪ D) s t ∈ X.dom) :
    F.GeneratesSub (F.historySub X ∪ D) X :=
  (F.generatesSub_iff_historySub_subset
    (Set.union_subset (F.historySub_subset X) hD) X).2 ⟨Set.subset_union_left, hχ⟩

/-- The same lemma read contrapositively, which is how it certifies a *non*-generating
set: containing the history is not enough if some chimera escapes the domain. -/
example [Finite F.B] {C : Set (Setoid S)} (X : Subpartition S) (hC : C ⊆ F.B)
    {s t : S} (hs : s ∈ X.dom) (ht : t ∈ X.dom) (hesc : F.chimera C s t ∉ X.dom) :
    ¬ F.GeneratesSub C X :=
  fun h => hesc (((F.generatesSub_iff_historySub_subset hC X).1 h).2 s hs t ht)

/-- Lemmas 1 and 2 composed the way §4.3 composes them: when `X` and `Y` have disjoint
histories, Lemma 1 collapses every term of Lemma 2's union to `h^F(Y)`. -/
example [Finite F.B] {X Y : Subpartition S} (hE : X.dom = Y.dom)
    (hdisj : F.historySub X ∩ F.historySub Y = ∅) {s : S} (hs : s ∈ X.dom) :
    F.historySub (Y.restrict (X.part s)) = F.historySub Y :=
  (F.historySub_restrict_part_eq hE.symm (by rw [Set.inter_comm]; exact hdisj) hs).symm

end FactoredSet

end FiniteFactoredSets
