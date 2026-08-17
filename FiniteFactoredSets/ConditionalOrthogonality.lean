import FiniteFactoredSets.SubpartitionHistory
import FiniteFactoredSets.Orthogonality

/-!
# Conditional orthogonality

This file is §4.3 of Garrabrant, *Temporal Inference with Finite Factored Sets*
(arXiv:2109.11513): orthogonality and time on subpartitions (Definition 25), conditional
orthogonality given a subset and given a partition (Definitions 26–27), its agreement with
unconditional orthogonality (Proposition 24), the compositional-semigraphoid axioms
(Theorem 2), and the characterization of `X ⊥ X | Y` (Proposition 25).

Orientation is `dd:order-flip` throughout: the paper's `X ∨_S Y` is `X ⊓ Y`, its
`X ≤_S Y` is `Y ≤ X`, and `Ind_S` is `⊤`.  The blocks `z ∈ Z` of a partition of `S` are
`Setoid.classes`, as in Definition 16.  Definition 22's `X|E` for a partition `X` of `S` is
`(Subpartition.ofSetoid X).restrict E`.

## The glue this section runs on

Every proof below is set algebra over `historySub` once the `Subpartition.restrict` glue
of `Subpartition.lean` is available — `restrict_univ`, `restrict_restrict_of_subset`,
`dom_restrict_ofSetoid`, `part_restrict_ofSetoid`, `restrict_ofSetoid_inf` (the identity
`(Y ∨_S W)|z = (Y|z) ∨_z (W|z)` that the paper's proof of Theorem 2 opens with), and
`restrict_inter_subset_restrict_inf` (the block inclusion Proposition 23 clause 3
consumes).  With those, decomposition and composition are Proposition 23 clause 2, weak
union is Lemma 1 plus Proposition 23 clause 3, and contraction is Lemma 2 plus Lemma 1.
`classes_top` — the blocks of `Ind_S`, which Mathlib does not supply — lives with the §2.1
partition material in `Basic.lean` and is what Proposition 24 runs on.

The blocks of `Z ⊓ W` (the paper's `Z ∨_S W`) are exactly the nonempty intersections
`z ∩ w` of a block of `Z` with a block of `W`; in Mathlib's `Setoid.classes` presentation
that is automatic, since a class is `{x | (Z ⊓ W) x s}` for some `s`, and `s` witnesses the
nonemptiness.  This is why the `y ∩ z = {}` case of the paper's contraction argument has
no counterpart here.
-/

universe u

namespace FiniteFactoredSets

variable {S : Type u}

namespace FactoredSet

open scoped Classical
open Subpartition

variable (F : FactoredSet S)

/-! ## §4.3 Orthogonality and time on subpartitions -/

/-- Definition 25, first clause: `X ⊥^F Y` for subpartitions — disjoint histories.

Paper node: Definition 25 (§4.3). -/
def OrthogonalSub (X Y : Subpartition S) : Prop := F.historySub X ∩ F.historySub Y = ∅

/-- Definition 25, second clause: `X ≤^F Y` for subpartitions — history inclusion.

Paper node: Definition 25 (§4.3). -/
def BeforeSub (X Y : Subpartition S) : Prop := F.historySub X ⊆ F.historySub Y

/-- Definition 25, third clause: `X <^F Y` for subpartitions — strict history inclusion.

Paper node: Definition 25 (§4.3). -/
def StrictlyBeforeSub (X Y : Subpartition S) : Prop := F.historySub X ⊂ F.historySub Y

lemma orthogonalSub_def (X Y : Subpartition S) :
    F.OrthogonalSub X Y ↔ F.historySub X ∩ F.historySub Y = ∅ := Iff.rfl

lemma beforeSub_def (X Y : Subpartition S) :
    F.BeforeSub X Y ↔ F.historySub X ⊆ F.historySub Y := Iff.rfl

lemma strictlyBeforeSub_def (X Y : Subpartition S) :
    F.StrictlyBeforeSub X Y ↔ F.historySub X ⊂ F.historySub Y := Iff.rfl

/-- Strictly before implies before, as for partitions (Definition 19). -/
lemma StrictlyBeforeSub.beforeSub {X Y : Subpartition S} (h : F.StrictlyBeforeSub X Y) :
    F.BeforeSub X Y := h.subset

/-- Orthogonality of subpartitions element-wise: no factor lies in both histories. -/
lemma orthogonalSub_iff_forall_notMem (X Y : Subpartition S) :
    F.OrthogonalSub X Y ↔ ∀ b ∈ F.historySub X, b ∉ F.historySub Y :=
  Set.disjoint_iff_inter_eq_empty.symm.trans Set.disjoint_left

/-- Definition 25 restricted to partitions of `S` is Definition 18: on `ofSetoid X` the
subpartition history is the §3.2 history.  No finiteness — `historySub_ofSetoid` is the
identification of two `⋂₀`s over the same family, not Proposition 22's *least*-element
sentence. -/
lemma orthogonalSub_ofSetoid (X Y : Setoid S) :
    F.OrthogonalSub (ofSetoid X) (ofSetoid Y) ↔ F.Orthogonal X Y := by
  rw [orthogonalSub_def, F.historySub_ofSetoid X, F.historySub_ofSetoid Y, orthogonal_def]

/-- Definition 25's `≤^F` restricted to partitions of `S` is Definition 19's, again with no
finiteness. -/
lemma beforeSub_ofSetoid (X Y : Setoid S) :
    F.BeforeSub (ofSetoid X) (ofSetoid Y) ↔ F.Before X Y := by
  rw [beforeSub_def, F.historySub_ofSetoid X, F.historySub_ofSetoid Y, before_def]

/-- Definition 26: `X` and `Y` are orthogonal given the subset `E`, `X ⊥^F Y | E`, when
their restrictions to `E` are orthogonal as subpartitions.

Paper node: Definition 26 (§4.3). -/
def OrthogonalGivenSet (X Y : Setoid S) (E : Set S) : Prop :=
  F.OrthogonalSub ((ofSetoid X).restrict E) ((ofSetoid Y).restrict E)

/-- Definition 27: `X` and `Y` are orthogonal given the partition `Z`, `X ⊥^F Y | Z`, when
they are orthogonal given every block `z ∈ Z`.

Paper node: Definition 27 (§4.3). -/
def OrthogonalGiven (X Y Z : Setoid S) : Prop :=
  ∀ z ∈ Z.classes, F.OrthogonalGivenSet X Y z

lemma orthogonalGivenSet_def (X Y : Setoid S) (E : Set S) :
    F.OrthogonalGivenSet X Y E ↔
      F.historySub ((ofSetoid X).restrict E) ∩ F.historySub ((ofSetoid Y).restrict E) = ∅ :=
  Iff.rfl

lemma orthogonalGiven_def (X Y Z : Setoid S) :
    F.OrthogonalGiven X Y Z ↔ ∀ z ∈ Z.classes, F.OrthogonalGivenSet X Y z := Iff.rfl

/-! ### Corners and symmetries of Definitions 26-27

Four facts that every consumer of §4.3 and §7.3 needs and that no paper node states:
Definition 26 is symmetric; `Ind_S` is orthogonal to everything given anything; and every
partition is orthogonal to everything **given itself**.  The last is the mechanism behind
Definition 48 implying Definition 49, and it is *not* Proposition 25
(`orthogonalGiven_self_iff` covers only `W = X`) nor a one-step consequence of Theorem 2. -/

/-- Definition 26 is symmetric in its two partitions. -/
lemma orthogonalGivenSet_comm (X Y : Setoid S) (E : Set S) :
    F.OrthogonalGivenSet X Y E ↔ F.OrthogonalGivenSet Y X E := by
  rw [F.orthogonalGivenSet_def, F.orthogonalGivenSet_def, Set.inter_comm]

/-- `Ind_S` is orthogonal to everything given any subset: its restricted history is empty. -/
lemma orthogonalGivenSet_top_left [Finite F.B] (X : Setoid S) (E : Set S) :
    F.OrthogonalGivenSet (⊤ : Setoid S) X E := by
  rw [F.orthogonalGivenSet_def, F.historySub_top_restrict E, Set.empty_inter]

/-- The same on the right, by symmetry. -/
lemma orthogonalGivenSet_top_right [Finite F.B] (X : Setoid S) (E : Set S) :
    F.OrthogonalGivenSet X (⊤ : Setoid S) E :=
  (F.orthogonalGivenSet_comm (⊤ : Setoid S) X E).1 (F.orthogonalGivenSet_top_left X E)

/-- Every partition is orthogonal to every other **given itself**: a block of `X` is a
single block of `X|x`, so `h^F(X|x) = {}`.  This is the mechanism behind Definition 49's
being implied by Definition 48. -/
lemma orthogonalGiven_given_self [Finite F.B] (X W : Setoid S) : F.OrthogonalGiven X W X := by
  rintro z ⟨r, rfl⟩
  refine (F.orthogonalGivenSet_def X W _).2 ?_
  have h : F.historySub ((ofSetoid X).restrict {x | X x r}) = ∅ := by
    refine (F.historySub_spec ((ofSetoid X).restrict {x | X x r})
      ((ofSetoid X).restrict {x | X x r}) ((ofSetoid X).restrict {x | X x r})
      rfl).2.2.2.1.2 ?_
    rw [dom_restrict_ofSetoid]
    refine Subpartition.ext fun s t => ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ?_⟩⟩
    exact X.trans' (show X s r from h.1) (X.symm' (show X t r from h.2))
  rw [h, Set.empty_inter]

/-- Client's-eye use: conditioning on `X` itself makes any Definition 27 obligation with
`X` on the left automatic, whatever the world model. -/
example [Finite F.B] (X W : Setoid S) : F.OrthogonalGiven W X X :=
  fun z hz => (F.orthogonalGivenSet_comm X W z).1 (F.orthogonalGiven_given_self X W z hz)

/-! ### Glue: how a restricted common refinement's history splits

`historySub_restrict_inf` is Proposition 23 clause 2 pushed through
`restrict_ofSetoid_inf`; it is the paper's `h^F((Y ∨_S W)|z) = h^F(Y|z) ∪ h^F(W|z)`, from
which decomposition and composition are immediate.  The `Subset` (inclusion as sets of
blocks) that Proposition 23 clause 3 consumes in the weak-union argument is
`Subpartition.restrict_inter_subset_restrict_inf`, in `Subpartition.lean`. -/

lemma historySub_restrict_inf [Finite F.B] (X Y : Setoid S) (E : Set S) :
    F.historySub ((ofSetoid (X ⊓ Y)).restrict E) =
      F.historySub ((ofSetoid X).restrict E) ∪ F.historySub ((ofSetoid Y).restrict E) := by
  rw [restrict_ofSetoid_inf]
  exact (F.historySub_spec ((ofSetoid X).restrict E) ((ofSetoid Y).restrict E)
    ((ofSetoid X).restrict E) (by simp)).2.1

/-- **Proposition 24** — unconditional orthogonality is orthogonality given `Ind_S`.

The paper's Proposition 24 stands under its standing finite-factored-set hypothesis, but the
statement needs none: both cases run on `historySub_ofSetoid`, which is finiteness-free
(`dd:finiteness-minimal`).

Paper node: Proposition 24 (§4.3). -/
theorem orthogonal_iff_orthogonalGiven_top (X Y : Setoid S) :
    F.Orthogonal X Y ↔ F.OrthogonalGiven X Y ⊤ := by
  rcases isEmpty_or_nonempty S with hS | hS
  · -- Over the empty type every partition is `Ind_S`, so the left side holds; and
    -- `Ind_∅ = {}` has no blocks, so the right side holds vacuously.
    constructor
    · rintro - z ⟨y, rfl⟩
      exact (IsEmpty.false y).elim
    · intro _
      have h : F.history X = ∅ := by
        have hmem : (∅ : Set (Setoid S))
            ∈ {C : Set (Setoid S) | C ⊆ F.B ∧ F.Generates C X} := by
          refine ⟨Set.empty_subset _, ?_⟩
          rintro x ⟨y, rfl⟩
          exact (IsEmpty.false y).elim
        exact Set.subset_empty_iff.mp (Set.sInter_subset_of_mem hmem)
      rw [orthogonal_def, h, Set.empty_inter]
  · -- Otherwise `Ind_S` has the single block `S`, and `X|S = X`.
    have hclasses : (⊤ : Setoid S).classes = {Set.univ} := classes_top hS
    constructor
    · intro h z hz
      rw [hclasses, Set.mem_singleton_iff] at hz
      subst hz
      refine (F.orthogonalGivenSet_def X Y Set.univ).2 ?_
      simp only [restrict_univ]
      rw [F.historySub_ofSetoid X, F.historySub_ofSetoid Y]
      exact h
    · intro h
      have hz := h Set.univ (by rw [hclasses]; rfl)
      rw [F.orthogonalGivenSet_def] at hz
      simp only [restrict_univ] at hz
      rwa [F.historySub_ofSetoid X, F.historySub_ofSetoid Y] at hz

/-- **Theorem 2** — conditional orthogonality satisfies the compositional-semigraphoid
axioms: symmetry, decomposition, weak union, contraction, composition.  The paper's
`∨_S` is `⊓` (`dd:order-flip`).

Paper node: Theorem 2 (§4.3). -/
theorem orthogonalGiven_semigraphoid [Finite F.B] (X Y Z W : Setoid S) :
    (F.OrthogonalGiven X Y Z → F.OrthogonalGiven Y X Z) ∧
    (F.OrthogonalGiven X (Y ⊓ W) Z → F.OrthogonalGiven X Y Z ∧ F.OrthogonalGiven X W Z) ∧
    (F.OrthogonalGiven X (Y ⊓ W) Z → F.OrthogonalGiven X Y (Z ⊓ W)) ∧
    (F.OrthogonalGiven X Y Z → F.OrthogonalGiven X W (Z ⊓ Y) → F.OrthogonalGiven X (Y ⊓ W) Z) ∧
    (F.OrthogonalGiven X Y Z → F.OrthogonalGiven X W Z → F.OrthogonalGiven X (Y ⊓ W) Z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Symmetry: the definition is symmetric in `X` and `Y`, block by block.
    intro h z hz
    exact (F.orthogonalGivenSet_def Y X z).2
      (by rw [Set.inter_comm]; exact (F.orthogonalGivenSet_def X Y z).1 (h z hz))
  · -- Decomposition: `h^F((Y ∨_S W)|z)` is the union `h^F(Y|z) ∪ h^F(W|z)`, so a set
    -- disjoint from it is disjoint from each side.
    intro h
    have key : ∀ z ∈ Z.classes,
        F.historySub ((ofSetoid X).restrict z) ∩ F.historySub ((ofSetoid Y).restrict z) = ∅ ∧
        F.historySub ((ofSetoid X).restrict z) ∩
          F.historySub ((ofSetoid W).restrict z) = ∅ := by
      intro z hz
      have hzz := (F.orthogonalGivenSet_def X (Y ⊓ W) z).1 (h z hz)
      rwa [F.historySub_restrict_inf Y W z, Set.inter_union_distrib_left,
        Set.union_empty_iff] at hzz
    exact ⟨fun z hz => (F.orthogonalGivenSet_def X Y z).2 (key z hz).1,
      fun z hz => (F.orthogonalGivenSet_def X W z).2 (key z hz).2⟩
  · -- Weak union: a block of `Z ∨_S W` is `z ∩ w`; Lemma 1 moves `h^F(X|z)` onto it
    -- (the histories of `X|z` and `W|z` being disjoint by decomposition), and
    -- `Y|(z ∩ w) ⊆ (Y ∨_S W)|z` as sets of blocks.
    rintro h u ⟨s, rfl⟩
    have hsz : s ∈ {x | Z x s} := Z.refl' s
    have hzc : {x | Z x s} ∈ Z.classes := Z.mem_classes s
    have hu' : {x | (Z ⊓ W) x s} = {x | Z x s} ∩ {x | W x s} := rfl
    have horig := (F.orthogonalGivenSet_def X (Y ⊓ W) {x | Z x s}).1 (h _ hzc)
    have hzz := horig
    rw [F.historySub_restrict_inf Y W, Set.inter_union_distrib_left,
      Set.union_empty_iff] at hzz
    have hL1 := F.historySub_restrict_part_eq
      (X := (ofSetoid X).restrict {x | Z x s}) (Y := (ofSetoid W).restrict {x | Z x s})
      (by simp) hzz.2 (by rw [dom_restrict_ofSetoid]; exact hsz)
    rw [part_restrict_ofSetoid W hsz,
      restrict_restrict_of_subset _ Set.inter_subset_left] at hL1
    have hsub : F.historySub ((ofSetoid Y).restrict ({x | Z x s} ∩ {x | W x s})) ⊆
        F.historySub ((ofSetoid (Y ⊓ W)).restrict {x | Z x s}) :=
      (F.historySub_spec ((ofSetoid Y).restrict ({x | Z x s} ∩ {x | W x s}))
        ((ofSetoid Y).restrict ({x | Z x s} ∩ {x | W x s}))
        ((ofSetoid (Y ⊓ W)).restrict {x | Z x s}) rfl).2.2.1
        (restrict_inter_subset_restrict_inf Y W {x | Z x s} s)
    refine (F.orthogonalGivenSet_def X Y _).2 ?_
    rw [hu', ← hL1]
    have hmono : F.historySub ((ofSetoid X).restrict {x | Z x s}) ∩
        F.historySub ((ofSetoid Y).restrict ({x | Z x s} ∩ {x | W x s})) ⊆
        F.historySub ((ofSetoid X).restrict {x | Z x s}) ∩
          F.historySub ((ofSetoid (Y ⊓ W)).restrict {x | Z x s}) :=
      Set.inter_subset_inter subset_rfl hsub
    rw [horig] at hmono
    exact Set.subset_empty_iff.1 hmono
  · -- Contraction: Lemma 2 expands `h^F((Y ∨_S W)|z)` as `h^F(Y|z)` together with the
    -- histories of `W|(z ∩ [t]_Y)`; the first is handled by `X ⊥ Y | Z`, and each of the
    -- rest by `X ⊥ W | (Z ∨_S Y)` after Lemma 1 moves `h^F(X|z)` onto `z ∩ [t]_Y`.
    rintro h₁ h₂ z ⟨s₀, rfl⟩
    have hs₀ : s₀ ∈ {x | Z x s₀} := Z.refl' s₀
    have hzc : {x | Z x s₀} ∈ Z.classes := Z.mem_classes s₀
    have hXY : F.historySub ((ofSetoid X).restrict {x | Z x s₀}) ∩
        F.historySub ((ofSetoid Y).restrict {x | Z x s₀}) = ∅ :=
      (F.orthogonalGivenSet_def X Y _).1 (h₁ _ hzc)
    have hL2 := F.historySub_inf_eq (X := (ofSetoid Y).restrict {x | Z x s₀})
      (Y := (ofSetoid W).restrict {x | Z x s₀}) (by simp)
    refine (F.orthogonalGivenSet_def X (Y ⊓ W) _).2 ?_
    rw [restrict_ofSetoid_inf, hL2, Set.eq_empty_iff_forall_notMem]
    rintro b ⟨hb1, hb2⟩
    rw [Set.mem_union] at hb2
    rcases hb2 with hb2 | hb2
    · exact Set.eq_empty_iff_forall_notMem.1 hXY b ⟨hb1, hb2⟩
    · rw [dom_restrict_ofSetoid] at hb2
      simp only [Set.mem_iUnion, exists_prop] at hb2
      obtain ⟨t, ht, hbt⟩ := hb2
      rw [part_restrict_ofSetoid Y ht,
        restrict_restrict_of_subset _ Set.inter_subset_left] at hbt
      have hzt : {x | Z x s₀} ∩ {x | Y x t} = {x | (Z ⊓ Y) x t} := by
        ext a
        exact ⟨fun hh => ⟨Z.trans' hh.1 (Z.symm' ht), hh.2⟩,
          fun hh => ⟨Z.trans' hh.1 ht, hh.2⟩⟩
      have hXW := (F.orthogonalGivenSet_def X W _).1 (h₂ _ ((Z ⊓ Y).mem_classes t))
      have hL1 := F.historySub_restrict_part_eq
        (X := (ofSetoid X).restrict {x | Z x s₀})
        (Y := (ofSetoid Y).restrict {x | Z x s₀}) (by simp) hXY
        (by rw [dom_restrict_ofSetoid]; exact ht)
      rw [part_restrict_ofSetoid Y ht,
        restrict_restrict_of_subset _ Set.inter_subset_left, hzt] at hL1
      rw [hzt] at hbt
      rw [hL1] at hb1
      exact Set.eq_empty_iff_forall_notMem.1 hXW b ⟨hb1, hbt⟩
  · -- Composition: the converse reading of decomposition's union split.
    intro h₁ h₂ z hz
    refine (F.orthogonalGivenSet_def X (Y ⊓ W) z).2 ?_
    rw [F.historySub_restrict_inf Y W z, Set.inter_union_distrib_left,
      (F.orthogonalGivenSet_def X Y z).1 (h₁ z hz),
      (F.orthogonalGivenSet_def X W z).1 (h₂ z hz), Set.union_empty]

/-- **Proposition 25** — `X ⊥^F X | Y` exactly when `X ≤_S Y`, i.e. (Mathlib's order)
`Y ≤ X`.

Paper node: Proposition 25 (§4.3). -/
theorem orthogonalGiven_self_iff [Finite F.B] (X Y : Setoid S) :
    F.OrthogonalGiven X X Y ↔ Y ≤ X := by
  constructor
  · -- Each `X|y` has empty history, hence is `Ind_y` (Proposition 23 clause 4), so any
    -- two `Y`-equivalent points are `X`-equivalent.
    intro h s t hst
    have hy := (F.orthogonalGivenSet_def X X {x | Y x t}).1 (h _ (Y.mem_classes t))
    rw [Set.inter_self] at hy
    have hdom : ((ofSetoid X).restrict {x | Y x t}).dom = {x | Y x t} :=
      dom_restrict_ofSetoid X _
    have hind := (F.historySub_spec ((ofSetoid X).restrict {x | Y x t})
      ((ofSetoid X).restrict {x | Y x t}) ((ofSetoid X).restrict {x | Y x t})
      rfl).2.2.2.1.1 hy
    rw [hdom] at hind
    have hA : ((ofSetoid X).restrict {x | Y x t}) s t := by
      rw [hind]
      exact ⟨hst, Y.refl' t⟩
    exact hA.2.2
  · -- Conversely `Y ≤ X` makes every `X|y` indiscrete outright.
    rintro h z ⟨r, rfl⟩
    refine (F.orthogonalGivenSet_def X X _).2 ?_
    rw [Set.inter_self]
    refine (F.historySub_spec ((ofSetoid X).restrict {x | Y x r})
      ((ofSetoid X).restrict {x | Y x r}) ((ofSetoid X).restrict {x | Y x r})
      rfl).2.2.2.1.2 ?_
    rw [dom_restrict_ofSetoid]
    ext a b
    exact ⟨fun hh => ⟨hh.1, hh.2.1⟩,
      fun hh => ⟨hh.1, hh.2, h (Y.trans' hh.1 (Y.symm' hh.2))⟩⟩

/-! ## Client-side sanity checks

These `example`s use the §4.3 endpoints the way a downstream file will: through the
annotated paper statements, never by unfolding `OrthogonalGiven` or `historySub`. -/

/-- Theorem 2 clauses 1 and 2 chained: from `X ⊥ (Y ∨_S W) | Z` a client gets `W ⊥ X | Z`
without ever naming a block. -/
example (F : FactoredSet S) [Finite F.B] (X Y Z W : Setoid S)
    (h : F.OrthogonalGiven X (Y ⊓ W) Z) : F.OrthogonalGiven W X Z :=
  (F.orthogonalGiven_semigraphoid X W Z Y).1 ((F.orthogonalGiven_semigraphoid X Y Z W).2.1 h).2

/-- Decomposition and composition are inverse to each other (Theorem 2 clauses 2 and 5),
so conditioning on a fixed `Z` makes `⊥ | Z` additive in its second argument. -/
example (F : FactoredSet S) [Finite F.B] (X Y Z W : Setoid S) :
    F.OrthogonalGiven X (Y ⊓ W) Z ↔ (F.OrthogonalGiven X Y Z ∧ F.OrthogonalGiven X W Z) :=
  ⟨(F.orthogonalGiven_semigraphoid X Y Z W).2.1,
   fun h => (F.orthogonalGiven_semigraphoid X Y Z W).2.2.2.2 h.1 h.2⟩

/-- Proposition 24 as a transport: an unconditional orthogonality certified by
Proposition 14's basis split (§3.3) is a conditional one given `Ind_S`. -/
example (F : FactoredSet S) [Finite F.B] (X Y : Setoid S) (C : Set (Setoid S))
    (hC : C ⊆ F.B) (hX : commonRefinement C ≤ X) (hY : commonRefinement (F.B \ C) ≤ Y) :
    F.OrthogonalGiven X Y ⊤ :=
  (F.orthogonal_iff_orthogonalGiven_top X Y).1 ((F.orthogonal_iff_exists X Y).2 ⟨C, hC, hX, hY⟩)

/-- Proposition 25 composed with Theorem 2's weak union: `X ⊥ X | Z` and `Z ∨_S W` a
refinement of `Z` give `X ⊥ X | (Z ∨_S W)` by the order characterization alone. -/
example (F : FactoredSet S) [Finite F.B] (X Z W : Setoid S)
    (h : F.OrthogonalGiven X X Z) : F.OrthogonalGiven X X (Z ⊓ W) :=
  (F.orthogonalGiven_self_iff X (Z ⊓ W)).2 (le_trans inf_le_left
    ((F.orthogonalGiven_self_iff X Z).1 h))

/-- Definition 25 on partitions of `S` is Definition 19: `BeforeSub` on `ofSetoid` is
`Before`, so §3.4's Proposition 18 transitivity is available on subpartition time. -/
example (F : FactoredSet S) [Finite F.B] (X Y Z : Setoid S)
    (h₁ : F.BeforeSub (ofSetoid X) (ofSetoid Y)) (h₂ : F.BeforeSub (ofSetoid Y) (ofSetoid Z)) :
    F.BeforeSub (ofSetoid X) (ofSetoid Z) :=
  (F.beforeSub_ofSetoid X Z).2 ((F.before_spec X Y Z).2.1 ((F.beforeSub_ofSetoid X Y).1 h₁)
    ((F.beforeSub_ofSetoid Y Z).1 h₂))

/-- `OrthogonalSub` and `StrictlyBeforeSub` used as a client would: a strict predecessor of
`Y` inherits `Y`'s subpartition orthogonalities, because both are read off the same
history inclusion. -/
example (F : FactoredSet S) (X Y Z : Subpartition S) (h : F.StrictlyBeforeSub X Y)
    (hYZ : F.OrthogonalSub Y Z) : F.OrthogonalSub X Z :=
  (F.orthogonalSub_iff_forall_notMem X Z).2 fun b hb =>
    (F.orthogonalSub_iff_forall_notMem Y Z).1 hYZ b (StrictlyBeforeSub.beforeSub F h hb)

/-- Definition 26 read directly: orthogonality given the whole of `S` is unconditional
orthogonality, which is Proposition 24 with its single block already supplied. -/
example (F : FactoredSet S) [Finite F.B] (X Y : Setoid S)
    (h : F.OrthogonalGivenSet X Y Set.univ) : F.Orthogonal X Y := by
  rw [F.orthogonalGivenSet_def] at h
  simp only [restrict_univ] at h
  rwa [F.historySub_isLeast_and_eq_history.2 X,
    F.historySub_isLeast_and_eq_history.2 Y] at h

end FactoredSet

end FiniteFactoredSets
