import FiniteFactoredSets.History

/-!
# Subpartitions and generating a subpartition

This file is §4.1 of Garrabrant, *Temporal Inference with Finite Factored Sets*
(arXiv:2109.11513): partitions of *subsets* of `S`, their restriction, and what it means
for a set of factors to generate one.

## Modeling decision — `dd:subpartition`

The paper's Definition 20 takes `SubPart(S) = ⋃_{E ⊆ S} Part(E)`.  Under `dd:partition`
that would be `Σ E : Set S, Setoid E`, and every §4 statement would then carry dependent
subtypes and domain-equality transports.  Instead a subpartition of `S` is modeled as a
**partial equivalence relation** on `S` — a symmetric, transitive relation `r` — whose
domain (Definition 21) is `{s | r s s}`.  The two presentations are in canonical
bijection (a partition of `E` is exactly a PER with domain `E`), and the bijection is
exhibited below: `Subpartition.toSetoid : Setoid X.dom`, `Subpartition.ofSetoidOn E Y`,
and the round-trip lemmas.  Mathlib has no partial-equivalence-relation structure to
reuse, so this one is repo-generic.

Consequences a reader should hold in mind:

* a *partition* of `S` is the special case of a total PER: `Subpartition.ofSetoid`;
* Definition 22's `X|E` is `Subpartition.restrict X E`, with domain `X.dom ∩ E`;
* the paper's order `≤_E` between subpartitions of the same domain is Mathlib's `≤`
  **with the glyphs inverted exactly as in §2–§3** (`dd:order-flip`): the paper's
  `X ≤_E Y` is `Y ≤ X` here, and the paper's `X ∨_E Y` (common refinement) is `X ⊓ Y`;
* `Ind_E` is `Subpartition.indiscrete E`;
* the paper's "`X ⊆ Z`" for subpartitions — inclusion as *sets of blocks* — is
  `Subpartition.Subset`.
-/

universe u

namespace FiniteFactoredSets

variable {S : Type u}

/-! ## §4.1 Subpartitions -/

/-- Definition 20: a subpartition of `S` — a partition of a subset of `S` — modeled as a
partial equivalence relation on `S` (`dd:subpartition`).

Paper node: Definition 20 (§4.1). -/
structure Subpartition (S : Type u) where
  r : S → S → Prop
  symm' : ∀ {s t : S}, r s t → r t s
  trans' : ∀ {s t u : S}, r s t → r t u → r s u

namespace Subpartition

instance : CoeFun (Subpartition S) (fun _ => S → S → Prop) := ⟨Subpartition.r⟩

@[ext] lemma ext {X Y : Subpartition S} (h : ∀ s t, X s t ↔ Y s t) : X = Y := by
  cases X
  cases Y
  congr 1
  funext s t
  exact propext (h s t)

/-- Definition 21: the domain of a subpartition — the subset it partitions.  Under
`dd:subpartition` this is the set of elements related to themselves.

Paper node: Definition 21 (§4.1). -/
def dom (X : Subpartition S) : Set S := {s | X s s}

lemma mem_dom_of_rel {X : Subpartition S} {s t : S} (h : X s t) : s ∈ X.dom :=
  X.trans' h (X.symm' h)

lemma mem_dom_of_rel' {X : Subpartition S} {s t : S} (h : X s t) : t ∈ X.dom :=
  X.trans' (X.symm' h) h

/-- The block of `X` containing `s` (Definition 4 for subpartitions). -/
def part (X : Subpartition S) (s : S) : Set S := {t | X t s}

/-- The blocks of `X`: the set of nonempty classes. -/
def classes (X : Subpartition S) : Set (Set S) := {x | ∃ s ∈ X.dom, x = X.part s}

@[simp] lemma mem_part {X : Subpartition S} {s t : S} : t ∈ X.part s ↔ X t s := Iff.rfl

lemma self_mem_part {X : Subpartition S} {s : S} (hs : s ∈ X.dom) : s ∈ X.part s := hs

lemma part_subset_dom (X : Subpartition S) (s : S) : X.part s ⊆ X.dom :=
  fun _ ht => mem_dom_of_rel ht

lemma part_eq_of_rel {X : Subpartition S} {s t : S} (h : X s t) : X.part s = X.part t :=
  Set.ext fun _ => ⟨fun hu => X.trans' hu h, fun hu => X.trans' hu (X.symm' h)⟩

lemma mem_classes {X : Subpartition S} {s : S} (hs : s ∈ X.dom) : X.part s ∈ X.classes :=
  ⟨s, hs, rfl⟩

lemma classes_subset_dom {X : Subpartition S} {x : Set S} (hx : x ∈ X.classes) : x ⊆ X.dom := by
  obtain ⟨s, -, rfl⟩ := hx
  exact part_subset_dom X s

/-- A partition of `S` is a subpartition with domain `S`. -/
def ofSetoid (X : Setoid S) : Subpartition S :=
  ⟨fun s t => X s t, fun h => X.symm' h, fun h₁ h₂ => X.trans' h₁ h₂⟩

@[simp] lemma ofSetoid_apply (X : Setoid S) (s t : S) : ofSetoid X s t ↔ X s t := Iff.rfl

@[simp] lemma dom_ofSetoid (X : Setoid S) : (ofSetoid X).dom = Set.univ :=
  Set.eq_univ_of_forall fun s => X.refl' s

lemma classes_ofSetoid (X : Setoid S) : (ofSetoid X).classes = X.classes := by
  ext x
  constructor
  · rintro ⟨s, -, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, X.refl' s, rfl⟩

/-- Definition 22: the restriction `X|E`, a partition of `X.dom ∩ E` whose blocks are the
traces `[e]_X ∩ E`.  Stated for subpartitions, so that it also serves Lemmas 1–2, which
restrict a subpartition to a block of another; for a partition of `S` use
`(ofSetoid X).restrict E`.

Paper node: Definition 22 (§4.1). -/
def restrict (X : Subpartition S) (E : Set S) : Subpartition S :=
  ⟨fun s t => s ∈ E ∧ t ∈ E ∧ X s t, fun h => ⟨h.2.1, h.1, X.symm' h.2.2⟩,
    fun h₁ h₂ => ⟨h₁.1, h₂.2.1, X.trans' h₁.2.2 h₂.2.2⟩⟩

@[simp] lemma restrict_apply (X : Subpartition S) (E : Set S) (s t : S) :
    X.restrict E s t ↔ s ∈ E ∧ t ∈ E ∧ X s t := Iff.rfl

@[simp] lemma dom_restrict (X : Subpartition S) (E : Set S) :
    (X.restrict E).dom = X.dom ∩ E :=
  Set.ext fun _ => ⟨fun h => ⟨h.2.2, h.1⟩, fun h => ⟨h.2, h.2, h.1⟩⟩

/-- The block of `X|E` at a point of `E` is the trace of the block of `X`. -/
lemma restrict_part {X : Subpartition S} {E : Set S} {s : S} (hs : s ∈ E) :
    (X.restrict E).part s = X.part s ∩ E :=
  Set.ext fun _ => ⟨fun h => ⟨h.2.2, h.1⟩, fun h => ⟨h.2, hs, h.1⟩⟩

/-- The blocks of `X|E` are the nonempty traces `x ∩ E` of blocks `x` of `X`. -/
lemma classes_restrict (X : Subpartition S) (E : Set S) :
    (X.restrict E).classes = {y | ∃ x ∈ X.classes, y = x ∩ E ∧ (x ∩ E).Nonempty} := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [dom_restrict] at hs
    exact ⟨X.part s, mem_classes hs.1, restrict_part hs.2, ⟨s, hs.1, hs.2⟩⟩
  · rintro ⟨x, ⟨s, -, rfl⟩, rfl, r, hr, hrE⟩
    refine ⟨r, ?_, ?_⟩
    · rw [dom_restrict]
      exact ⟨mem_dom_of_rel hr, hrE⟩
    · rw [restrict_part hrE, part_eq_of_rel hr]

/-- Restricting to all of `S` changes nothing: `X|S = X`. -/
@[simp] lemma restrict_univ (X : Subpartition S) : X.restrict Set.univ = X :=
  ext fun _ _ => ⟨fun h => h.2.2, fun h => ⟨trivial, trivial, h⟩⟩

/-- Nested restrictions collapse: `(X|E)|E' = X|E'` when `E' ⊆ E`. -/
lemma restrict_restrict_of_subset (X : Subpartition S) {E E' : Set S} (h : E' ⊆ E) :
    (X.restrict E).restrict E' = X.restrict E' :=
  ext fun _ _ => ⟨fun hst => ⟨hst.1, hst.2.1, hst.2.2.2.2⟩,
    fun hst => ⟨hst.1, hst.2.1, h hst.1, h hst.2.1, hst.2.2⟩⟩

/-- A partition of `S` restricted to `E` has domain `E`. -/
@[simp] lemma dom_restrict_ofSetoid (X : Setoid S) (E : Set S) :
    ((ofSetoid X).restrict E).dom = E := by
  rw [dom_restrict, dom_ofSetoid, Set.univ_inter]

/-- The block of `X|E` through `s ∈ E` is the trace `E ∩ [s]_X`. -/
lemma part_restrict_ofSetoid (X : Setoid S) {E : Set S} {s : S} (hs : s ∈ E) :
    ((ofSetoid X).restrict E).part s = E ∩ {x | X x s} := by
  ext t
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hs, h.2⟩⟩

/-- The indiscrete partition of `E`, `Ind_E`. -/
def indiscrete (E : Set S) : Subpartition S :=
  ⟨fun s t => s ∈ E ∧ t ∈ E, fun h => ⟨h.2, h.1⟩, fun h₁ h₂ => ⟨h₁.1, h₂.2⟩⟩

@[simp] lemma dom_indiscrete (E : Set S) : (indiscrete E).dom = E :=
  Set.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- The order on subpartitions: Mathlib's orientation, as for `Setoid` (`dd:order-flip`) —
`X ≤ Y` means `X` is finer than `Y` (relation inclusion).  Between subpartitions of the same
domain this is the paper's `≥_E`. -/
instance : PartialOrder (Subpartition S) where
  le X Y := ∀ ⦃s t⦄, X s t → Y s t
  le_refl _ _ _ h := h
  le_trans _ _ _ h₁ h₂ _ _ h := h₂ (h₁ h)
  le_antisymm _ _ h₁ h₂ := ext fun _ _ => ⟨fun h => h₁ h, fun h => h₂ h⟩

lemma le_def {X Y : Subpartition S} : X ≤ Y ↔ ∀ ⦃s t⦄, X s t → Y s t := Iff.rfl

lemma dom_mono {X Y : Subpartition S} (h : X ≤ Y) : X.dom ⊆ Y.dom := fun _ hs => h hs

/-- The common refinement of two subpartitions — the paper's `X ∨_E Y` for subpartitions
of the same domain `E` — is relation intersection, Mathlib's `⊓` (`dd:order-flip`).  Its
domain is `X.dom ∩ Y.dom`. -/
instance : Min (Subpartition S) :=
  ⟨fun X Y => ⟨fun s t => X s t ∧ Y s t, fun h => ⟨X.symm' h.1, Y.symm' h.2⟩,
    fun h₁ h₂ => ⟨X.trans' h₁.1 h₂.1, Y.trans' h₁.2 h₂.2⟩⟩⟩

@[simp] lemma inf_apply (X Y : Subpartition S) (s t : S) : (X ⊓ Y) s t ↔ X s t ∧ Y s t :=
  Iff.rfl

@[simp] lemma dom_inf (X Y : Subpartition S) : (X ⊓ Y).dom = X.dom ∩ Y.dom :=
  Set.ext fun _ => Iff.rfl

instance : SemilatticeInf (Subpartition S) where
  inf X Y := X ⊓ Y
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ h, h₂ h⟩

/-- Restriction distributes over the common refinement: `(X ∨_S Y)|E = (X|E) ∨_E (Y|E)`,
which under `dd:order-flip` is `(ofSetoid (X ⊓ Y)).restrict E = X|E ⊓ Y|E`.  This is the
identity the paper's proof of Theorem 2 opens with. -/
lemma restrict_ofSetoid_inf (X Y : Setoid S) (E : Set S) :
    (ofSetoid (X ⊓ Y)).restrict E = (ofSetoid X).restrict E ⊓ (ofSetoid Y).restrict E :=
  ext fun _ _ => ⟨fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, ⟨h.1, h.2.1, h.2.2.2⟩⟩,
    fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.2.2⟩⟩

/-- The paper's "`X ⊆ Z`" between subpartitions: every block of `X` is a block of `Z`
(inclusion as sets of blocks — "a slightly unnatural relation", the paper notes, but the
one Proposition 21 clause 6 and Proposition 23 clause 3 are stated with). -/
def Subset (X Z : Subpartition S) : Prop := ∀ s ∈ X.dom, ∀ t, X t s ↔ Z t s

lemma Subset.dom_subset {X Z : Subpartition S} (h : X.Subset Z) : X.dom ⊆ Z.dom :=
  fun s hs => (h s hs s).1 hs

lemma Subset.classes_subset {X Z : Subpartition S} (h : X.Subset Z) : X.classes ⊆ Z.classes := by
  rintro x ⟨s, hs, rfl⟩
  exact ⟨s, h.dom_subset hs, Set.ext fun t => h s hs t⟩

lemma subset_iff_classes_subset {X Z : Subpartition S} :
    X.Subset Z ↔ X.classes ⊆ Z.classes := by
  refine ⟨Subset.classes_subset, fun h s hs t => ?_⟩
  obtain ⟨u, -, hxu⟩ := h (mem_classes hs)
  have hsu : Z s u := by
    have hmem : s ∈ Z.part u := by
      rw [← hxu]
      exact hs
    exact hmem
  have key : X.part s = Z.part s := hxu.trans (part_eq_of_rel hsu).symm
  exact Set.ext_iff.1 key t

-- Both hypotheses below are redundant for this inclusion (`X.part s` is empty unless
-- `s ∈ dom X`); they are kept because Lemma 2 supplies them and reads with them.
set_option linter.unusedVariables false in
/-- Restricting to a block of another subpartition yields a `Subset` of the common
refinement — the shape Lemma 2's `Y|x ⊆ X ∨_E Y` has. -/
lemma restrict_part_subset_inf {X Y : Subpartition S} (hE : X.dom = Y.dom) {s : S}
    (hs : s ∈ X.dom) : (Y.restrict (X.part s)).Subset (X ⊓ Y) := by
  intro u hu t
  rw [dom_restrict] at hu
  obtain ⟨-, huX⟩ := hu
  constructor
  · rintro ⟨htX, -, hY⟩
    exact ⟨X.trans' htX (X.symm' huX), hY⟩
  · rintro ⟨hX, hY⟩
    exact ⟨X.trans' hX huX, huX, hY⟩

/-- Restricting `Y|z` further to a block of `W` lands inside `(Y ∨_S W)|z` as a set of
blocks — the `Subset` that Proposition 23 clause 3 consumes in §4.3's weak-union argument
(`dd:order-flip`: the paper's `Y ∨_S W` is `Y ⊓ W`). -/
lemma restrict_inter_subset_restrict_inf (Y W : Setoid S) (z : Set S) (s : S) :
    ((ofSetoid Y).restrict (z ∩ {x | W x s})).Subset ((ofSetoid (Y ⊓ W)).restrict z) := by
  intro a ha t
  rw [dom_restrict_ofSetoid] at ha
  obtain ⟨haz, has⟩ := ha
  constructor
  · rintro ⟨⟨htz, hts⟩, -, hY⟩
    exact ⟨htz, haz, hY, W.trans' hts (W.symm' has)⟩
  · rintro ⟨htz, -, hY, hW⟩
    exact ⟨⟨htz, W.trans' hW has⟩, ⟨haz, has⟩, hY⟩

/-! ### The correspondence with `Σ E, Setoid E` — the content of `dd:subpartition` -/

/-- The setoid a subpartition induces on its own domain. -/
def toSetoid (X : Subpartition S) : Setoid X.dom where
  r a b := X a b
  iseqv := ⟨fun a => a.2, fun h => X.symm' h, fun h₁ h₂ => X.trans' h₁ h₂⟩

/-- A partition of a subset `E ⊆ S`, as a subpartition of `S`. -/
def ofSetoidOn (E : Set S) (Y : Setoid E) : Subpartition S :=
  ⟨fun s t => ∃ hs : s ∈ E, ∃ ht : t ∈ E, Y ⟨s, hs⟩ ⟨t, ht⟩,
    fun ⟨hs, ht, h⟩ => ⟨ht, hs, Y.symm' h⟩,
    fun ⟨hs, _, h₁⟩ ⟨_, hu, h₂⟩ => ⟨hs, hu, Y.trans' h₁ h₂⟩⟩

@[simp] lemma dom_ofSetoidOn (E : Set S) (Y : Setoid E) : (ofSetoidOn E Y).dom = E :=
  Set.ext fun s => ⟨fun ⟨hs, _, _⟩ => hs, fun hs => ⟨hs, hs, Y.refl' ⟨s, hs⟩⟩⟩

lemma ofSetoidOn_apply (E : Set S) (Y : Setoid E) {s t : S} (hs : s ∈ E) (ht : t ∈ E) :
    ofSetoidOn E Y s t ↔ Y ⟨s, hs⟩ ⟨t, ht⟩ :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hs, ht, h⟩⟩

lemma toSetoid_ofSetoidOn (E : Set S) (Y : Setoid E) (a b : (ofSetoidOn E Y).dom) :
    (ofSetoidOn E Y).toSetoid a b ↔ Y ⟨a, by simpa using a.2⟩ ⟨b, by simpa using b.2⟩ :=
  ofSetoidOn_apply E Y _ _

lemma ofSetoidOn_toSetoid (X : Subpartition S) : ofSetoidOn X.dom X.toSetoid = X :=
  ext fun _ _ => ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨mem_dom_of_rel h, mem_dom_of_rel' h, h⟩⟩

lemma ofSetoidOn_univ (X : Setoid S) :
    ofSetoidOn Set.univ (Setoid.comap Subtype.val X) = ofSetoid X :=
  ext fun _ _ => ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨trivial, trivial, h⟩⟩

/-- Client's-eye use of the `Subset` API: restricting to a block of a subpartition with the
same domain lands inside the common refinement, block by block (the shape Lemma 2 uses). -/
example {X Y : Subpartition S} (hE : X.dom = Y.dom) {s : S} (hs : s ∈ X.dom) :
    (Y.restrict (X.part s)).classes ⊆ (X ⊓ Y).classes :=
  Subset.classes_subset (restrict_part_subset_inf hE hs)

end Subpartition

/-! ## §4.1 Generating a subpartition -/

namespace FactoredSet

open scoped Classical
open Subpartition

variable (F : FactoredSet S)

/-- Definition 23: `C` generates the subpartition `X` (in `F`), `C ⊢^F X`, when
`χ^F_C(x, dom X) = x` for every block `x` of `X`.  As with `Generates` (Definition 16), `C`
is unrestricted; `C ⊆ B` is a hypothesis where it is load-bearing.

Paper node: Definition 23 (§4.1). -/
def GeneratesSub (C : Set (Setoid S)) (X : Subpartition S) : Prop :=
  ∀ x ∈ X.classes, F.chimeraImage C x X.dom = x

/-- Definition 23 coincides with Definition 16 on partitions of `S`. -/
lemma generatesSub_ofSetoid (C : Set (Setoid S)) (X : Setoid S) :
    F.GeneratesSub C (ofSetoid X) ↔ F.Generates C X := by
  simp only [GeneratesSub, Generates, classes_ofSetoid, dom_ofSetoid]

/-- The direction of Proposition 20 that turns clause 5 back into clause 1.  It needs no
`C ⊆ B`, and it is used twice: in the `7 → 1` leg of the cycle below, and in
`generatesSub_iff_rel`. -/
private lemma generatesSub_of_rel {C : Set (Setoid S)} {X : Subpartition S}
    (h : ∀ s ∈ X.dom, ∀ t ∈ X.dom, X (F.chimera C s t) s) : F.GeneratesSub C X := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := hx
  refine Set.Subset.antisymm ?_ ?_
  · rintro u ⟨t, ht, r, hr, rfl⟩
    exact X.trans' (h t (mem_dom_of_rel ht) r hr) ht
  · intro u hu
    exact ⟨u, hu, u, mem_dom_of_rel hu, F.chimera_self C u⟩

/-- **Proposition 20** — the seven equivalent forms of `C ⊢^F X` for a subpartition, `C ⊆ B`,
`E = dom X`.  Clauses 1–5 mirror Proposition 10; clauses 6 and 7 carry the extra
membership condition the paper singles out (`χ^F_C(s,t) ∈ E`, resp. `χ^F_C(E,E) = E`).
Clause 7's first half is the paper's `X ≤_E (⋁_S(C)|E)`, which under `dd:order-flip` reads
`(ofSetoid (sInf C)).restrict E ≤ X`.

Paper node: Proposition 20 (§4.1). -/
theorem generatesSub_tfae {C : Set (Setoid S)} (hC : C ⊆ F.B) (X : Subpartition S) :
    [F.GeneratesSub C X,
     ∀ x ∈ X.classes, F.chimeraImage C x X.dom = x,
     ∀ x ∈ X.classes, F.chimeraImage C x X.dom ⊆ x,
     ∀ x ∈ X.classes, ∀ y ∈ X.classes, F.chimeraImage C x y ⊆ x,
     ∀ s ∈ X.dom, ∀ t ∈ X.dom, F.chimera C s t ∈ X.part s,
     ∀ s ∈ X.dom, ∀ t ∈ X.dom, F.chimera C s t ∈ X.dom ∧ X (F.chimera C s t) s,
     (ofSetoid (commonRefinement C)).restrict X.dom ≤ X ∧
       F.chimeraImage C X.dom X.dom = X.dom].TFAE := by
  -- 1 ↔ 2 is the definition.
  tfae_have 1 ↔ 2 := Iff.rfl
  -- 2 → 3: an equality of sets is in particular an inclusion.
  tfae_have 2 → 3 := fun h x hx => (h x hx).subset
  -- 3 → 4: `y ⊆ E` for every block `y`, so `χ^F_C(x, y) ⊆ χ^F_C(x, E)`.
  tfae_have 3 → 4 := by
    rintro h x hx y hy u ⟨t, ht, r, hr, rfl⟩
    exact h x hx ⟨t, ht, r, classes_subset_dom hy hr, rfl⟩
  -- 4 → 5: instantiate at the blocks `[s]_X` and `[t]_X`.
  tfae_have 4 → 5 := fun h s hs t ht =>
    h (X.part s) (mem_classes hs) (X.part t) (mem_classes ht) ⟨s, hs, t, ht, rfl⟩
  -- 5 → 6: the membership half is `[s]_X ⊆ E`; the paper calls this a trivial restatement.
  tfae_have 5 → 6 := fun h s hs t ht =>
    ⟨part_subset_dom X s (h s hs t ht), h s hs t ht⟩
  -- 6 → 7: the first half uses that `s ∼_{⋁_S(C)} t` forces `χ^F_C(s,t) = t`; the second
  -- half is exactly the membership clause of 6, which is why the paper needs it there.
  tfae_have 6 → 7 := by
    intro h
    refine ⟨?_, ?_⟩
    · rintro s t ⟨hs, ht, hrel⟩
      have hrel' : commonRefinement C s t := hrel
      have heq : F.chimera C s t = t := F.eq_of_forall_rel fun b hb => by
        by_cases hbC : b ∈ C
        · exact b.trans' (F.chimera_rel_of_mem s t hb hbC) (commonRefinement_iff.1 hrel' b hbC)
        · exact F.chimera_rel_of_notMem s t hb hbC
      have hX := (h s hs t ht).2
      rw [heq] at hX
      exact X.symm' hX
    · refine Set.Subset.antisymm ?_ ?_
      · rintro u ⟨t, ht, r, hr, rfl⟩
        exact (h t ht r hr).1
      · intro u hu
        exact ⟨u, hu, u, hu, F.chimera_self C u⟩
  -- 7 → 1: here `C ⊆ B` is load-bearing, exactly as in Proposition 10 — it is what makes
  -- `χ^F_C(s,t) ∼_b s` for `b ∈ C`.  The second half of 7 supplies `χ^F_C(s,t) ∈ E`,
  -- without which the restricted order relation says nothing.
  tfae_have 7 → 1 := by
    rintro ⟨hle, himg⟩
    refine F.generatesSub_of_rel fun s hs t ht => ?_
    have hmem : F.chimera C s t ∈ F.chimeraImage C X.dom X.dom := ⟨s, hs, t, ht, rfl⟩
    rw [himg] at hmem
    exact hle ⟨hmem, hs, commonRefinement_iff.2 fun b hb => F.chimera_rel_of_mem s t (hC hb) hb⟩
  tfae_finish

/-- Clause 5 of Proposition 20 without the subset hypothesis: the working form. -/
lemma generatesSub_iff_rel (C : Set (Setoid S)) (X : Subpartition S) :
    F.GeneratesSub C X ↔ ∀ s ∈ X.dom, ∀ t ∈ X.dom, X (F.chimera C s t) s := by
  refine ⟨fun h s hs t ht => ?_, F.generatesSub_of_rel⟩
  have hmem : F.chimera C s t ∈ F.chimeraImage C (X.part s) X.dom := ⟨s, hs, t, ht, rfl⟩
  rw [h _ (mem_classes hs)] at hmem
  exact hmem

/-- **Proposition 21** — the basic properties of `⊢^F` on subpartitions, in the paper's
order, for `X`, `Y` of the same domain `E`.  Clause 1's `X ≤_E Y` is `Y ≤ X`, clause 2's
`X ∨_E Y` is `X ⊓ Y`, clause 4's `Ind_E` is `indiscrete E` (`dd:order-flip`); clause 5
carries both the intersection and the union (generation of subpartitions is closed under
union but not under supersets); clause 6 uses `Subset`, inclusion as sets of blocks.

Paper node: Proposition 21 (§4.1). -/
theorem generatesSub_spec (C D : Set (Setoid S)) (X Y Z : Subpartition S)
    (hE : X.dom = Y.dom) :
    (Y ≤ X → F.GeneratesSub C Y → F.GeneratesSub C X) ∧
    (F.GeneratesSub C X → F.GeneratesSub C Y → F.GeneratesSub C (X ⊓ Y)) ∧
    F.GeneratesSub F.B X ∧
    (F.GeneratesSub ∅ X ↔ X = indiscrete X.dom) ∧
    (F.GeneratesSub C X → F.GeneratesSub D X →
      F.GeneratesSub (C ∩ D) X ∧ F.GeneratesSub (C ∪ D) X) ∧
    (X.Subset Z → F.GeneratesSub C Z → F.GeneratesSub C X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1: coarsening.  `hE` is what carries `s ∈ dom X` over to `dom Y`.
    intro hYX hY
    rw [F.generatesSub_iff_rel] at hY ⊢
    intro s hs t ht
    have hsY : s ∈ Y.dom := hE ▸ hs
    have htY : t ∈ Y.dom := hE ▸ ht
    exact hYX (hY s hsY t htY)
  · -- 2: common refinement.
    intro hX hY
    rw [F.generatesSub_iff_rel] at hX hY ⊢
    intro s hs t ht
    obtain ⟨hsX, hsY⟩ := hs
    obtain ⟨htX, htY⟩ := ht
    exact ⟨hX s hsX t htX, hY s hsY t htY⟩
  · -- 3: the whole basis generates, since `χ^F_B(s,t) = s`.
    rw [F.generatesSub_iff_rel]
    intro s hs t _
    rw [F.chimera_basis]
    exact hs
  · -- 4: no factors at all generates exactly the indiscrete partition of `E`.
    rw [F.generatesSub_iff_rel]
    constructor
    · intro h
      refine ext fun s t => ⟨fun hst => ⟨mem_dom_of_rel hst, mem_dom_of_rel' hst⟩, ?_⟩
      rintro ⟨hs, ht⟩
      have hts := h t ht s hs
      rw [F.chimera_empty] at hts
      exact hts
    · intro h s hs t ht
      rw [F.chimera_empty]
      have key : (indiscrete X.dom) t s := ⟨ht, hs⟩
      rw [← h] at key
      exact key
  · -- 5: intersection and union.  Both legs use that `χ^F_D(s,t) ∼_X s` already places
    -- `χ^F_D(s,t)` in `E`, which is the extra condition Proposition 20 clause 6 isolates.
    intro hCX hDX
    rw [F.generatesSub_iff_rel] at hCX hDX
    constructor
    · refine (F.generatesSub_iff_rel _ _).2 fun s hs t ht => ?_
      rw [F.chimera_inter]
      have h1 : X (F.chimera D s t) s := hDX s hs t ht
      exact X.trans' (hCX (F.chimera D s t) (mem_dom_of_rel h1) t ht) h1
    · refine (F.generatesSub_iff_rel _ _).2 fun s hs t ht => ?_
      rw [F.chimera_union]
      have h1 : X (F.chimera D s t) s := hDX s hs t ht
      exact hCX s hs (F.chimera D s t) (mem_dom_of_rel h1)
  · -- 6: inclusion as sets of blocks.
    intro hXZ hZ
    rw [F.generatesSub_iff_rel] at hZ ⊢
    intro s hs t ht
    exact (hXZ s hs _).2 (hZ s (hXZ.dom_subset hs) t (hXZ.dom_subset ht))

/-- Client's-eye use of Proposition 20: the working clause is 6, projected out of the
`TFAE`; its membership half is what tells a client that splicing two points of `E` along
`C` stays inside `E`. -/
example {C : Set (Setoid S)} (hC : C ⊆ F.B) (X : Subpartition S) (h : F.GeneratesSub C X)
    {s t : S} (hs : s ∈ X.dom) (ht : t ∈ X.dom) : F.chimera C s t ∈ X.dom := by
  have h6 : ∀ s ∈ X.dom, ∀ t ∈ X.dom, F.chimera C s t ∈ X.dom ∧ X (F.chimera C s t) s :=
    ((F.generatesSub_tfae hC X).out 0 5).1 h
  exact (h6 s hs t ht).1

/-- Proposition 21 read as a client would: the generating sets of a subpartition are closed
under union (clause 5), and generation transfers down an inclusion of blocks (clause 6).
Note there is no clause for supersets — that is the paper's point. -/
example {C D : Set (Setoid S)} (X Z : Subpartition S) (hXZ : X.Subset Z)
    (hC : F.GeneratesSub C Z) (hD : F.GeneratesSub D Z) : F.GeneratesSub (C ∪ D) X :=
  (F.generatesSub_spec (C ∪ D) (C ∪ D) X X Z rfl).2.2.2.2.2 hXZ
    ((F.generatesSub_spec C D Z Z Z rfl).2.2.2.2.1 hC hD).2

/-- The correspondence of `dd:subpartition` in use: a §3 generation fact transports to the
subpartition of `S` that a partition of `S` becomes. -/
example (C : Set (Setoid S)) (X : Setoid S) (h : F.Generates C X) :
    F.GeneratesSub C (ofSetoidOn Set.univ (Setoid.comap Subtype.val X)) := by
  rw [ofSetoidOn_univ, F.generatesSub_ofSetoid]
  exact h

end FactoredSet

end FiniteFactoredSets
