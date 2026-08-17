import Condensation.Probability
import Mathlib.Order.Comparable
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Extension.Linear

/-!
# Condensation §3 — random variable models and latent variable models

This file is Definitions 3.1–3.4 of Eisenstat, *Condensation: A Theory of Concepts*:

* Definition 3.1 — a **random variable model** `(Ω, (Xᵢ)ᵢ∈I)` (`RVModel`);
* Definition 3.2 — a **latent variable model** `((Λ, (Y_A)_{A ∈ P⁺I}), π)` for one
  (`LatentModel`);
* Definition 3.4 — the joint variables `X_A` (`RVModel.joint`) and `Y_F`
  (`RVModel.jointOn`), and the four families `∩A`, `⊇A`, `⊋A`, `∋i` of (3.5)–(3.8),
  together with (3.9);
* Definition 3.3 — the three scores `σ_L`, `χ_L`, `ϱ_L` (`LatentModel.simpleScore`,
  `.condScore`, `.reconScore`).

Definition 3.4 is presented before Definition 3.3 here because Definition 3.2's
"contributes" condition and Definition 3.3's scores are both stated in terms of the joint
variables.  The paper's own order is 3.1, 3.2, 3.3, 3.4; nothing in the content changes.

## Modeling decisions

* `dd:bundled-model` — `RVModel` bundles the sample space, its instances, the measure, the
  range family and the variables as *fields*, because Definitions 3.5–3.12 need models as
  objects of a category and Definition 3.2 needs "a random variable model together with a
  map to another one".
* Definition 3.1's finiteness is carried **verbatim**: the sample space has finite entropy
  (`ShannonInformation.FiniteEntropyMeasure`) and the variables have countable discrete
  range.  `dd:finite-range`, the standing narrowing to `FiniteRange` variables, was
  **retired** on 2026-08-17 when the substrate `ShannonInformation/FiniteEntropy/` reached
  the corpus this development needs; there is no modeling substitution left here.
* `dd:pplus` — subfamilies `F ⊆ P⁺I` are `Set (PPlus I)`, and `Y_F` is the dependent
  product over the subtype `↥F`.
* Definition 3.1's "**finite** family of random variables" is part of the model:
  `RVModel` takes `[Finite I]` as a class parameter of the structure, so every statement
  quantifying over a model inherits it by instance search and no declaration can silently
  accept an infinite index type.  It is a parameter rather than a field because
  `Finite I` does not mention the model, so as a field it would never be found by instance
  search — a score over `I = ℕ` would elaborate, with `famFinset` silently empty.
  Finiteness of `P⁺I` then follows by instance (`Condensation.PPlus.instFinite`), and no
  `Fintype`/`DecidableEq` data is needed anywhere in this file.

## Imports

Beyond `Condensation.Probability` this file imports exactly two targeted `Mathlib.Order.*`
modules (never `import Mathlib` wholesale — that fails to elaborate against the vendored
shims):

* `Mathlib.Order.UpperLower.Basic` for `IsUpperSet`, which is how §4.10 and §5 spell
  "upward-closed subfamily of `P⁺I`".  The library uses Mathlib's predicate directly and
  defines no synonym for it.
* `Mathlib.Order.Extension.Linear` for `LinearExtension`/`toLinearExtension`.  Nothing in
  this file uses it; it is here because the linear-extension argument that Proposition 4.2
  (4.7)–(4.9), Theorem 4.9 (4.29)–(4.36) and Proposition 4.10 (4.38) all run on needs it,
  and it is *not* otherwise in the transitive import closure of `ShannonInformation.API`
  at this pin.
-/

universe u v w u' v'

namespace Condensation

open MeasureTheory ProbabilityTheory

/-! ## Definition 3.1 — random variable models

There used to be a `Condensation.finiteRange_pi` here — `FiniteRange` for a dependent
product of finitely many finite-range variables, which the vendored `FiniteRange/Defs.lean`
lacks.  It was retired on 2026-08-17 with `dd:finite-range`: the joint variables get their
finiteness from `RVModel.finiteEntropyOf`, in one step from Definition 3.1's finite-entropy
sample space, and after the swap nothing called it.  If a `FiniteRange` product is ever
wanted again it is six lines (`Set.Finite.pi` over the ranges). -/

/-- A **random variable model**: a countable discrete probability space `Ω` *with finite
entropy*, together with a finite family of random variables `Xᵢ : Ω → Rᵢ` with countable
discrete ranges.

`dd:bundled-model`.  This is Definition 3.1 verbatim.  "Countable discrete probability
space with finite entropy" is `[Countable Ω] [MeasurableSingletonClass Ω]
[IsProbabilityMeasure P]` together with the field `finiteEntropy_Ω :
ShannonInformation.FiniteEntropyMeasure P`; "countable and discrete range" is
`[Countable (R i)] [MeasurableSingletonClass (R i)]`.

The variables' own finite entropy (`finiteEntropy_X`) is carried as a role-named field
even though it is *implied* by `finiteEntropy_Ω` — every `Xᵢ` is a measurable function of
`Ω`, so `RVModel.finiteEntropyOf` derives it — because it is the hypothesis every §2
substrate lemma actually consumes, and having it as a field puts it one instance step from
the goal rather than behind a lemma with a measurability side condition.  It is therefore
a redundant, not a strengthening, field: a model is exactly Definition 3.1's data.

Until 2026-08-17 the second field read `finiteRange_X : ∀ i, FiniteRange (X i)` and the
`Ω` clause was dropped; that was the disclosed narrowing `dd:finite-range`, retired when
`ShannonInformation/FiniteEntropy/` reached the corpus §2–§5 need.  A geometric variable on
`ℕ` is now a model (`Condensation.Example.geomModel`).

The index type is **finite** — Definition 3.1's "finite family".  It is a class parameter
of the structure rather than a field: `Finite I` does not mention the model, so as a field
it would never be found by instance search, and a declaration over `I = ℕ` would
elaborate with every sum over `P⁺I` silently empty.

Paper node: `Definition 3.1` -/
structure RVModel (I : Type w) [Finite I] where
  /-- The sample space `Ω`. -/
  Ω : Type u
  [mΩ : MeasurableSpace Ω]
  [countΩ : Countable Ω]
  [singΩ : MeasurableSingletonClass Ω]
  /-- The probability measure `P` on `Ω`. -/
  P : Measure Ω
  [probP : IsProbabilityMeasure P]
  /-- Definition 3.1's "with finite entropy": the sample space itself has finite entropy. -/
  [finiteEntropy_Ω : ShannonInformation.FiniteEntropyMeasure P]
  /-- The range `Rᵢ` of the `i`-th variable. -/
  R : I → Type v
  [mR : ∀ i, MeasurableSpace (R i)]
  [countR : ∀ i, Countable (R i)]
  [singR : ∀ i, MeasurableSingletonClass (R i)]
  /-- The random variables `Xᵢ : Ω → Rᵢ`. -/
  X : ∀ i, Ω → R i
  measurable_X : ∀ i, Measurable (X i)
  finiteEntropy_X : ∀ i, ShannonInformation.FiniteEntropyOf (X i) P

attribute [instance] RVModel.mΩ RVModel.countΩ RVModel.singΩ RVModel.probP
  RVModel.finiteEntropy_Ω RVModel.mR RVModel.countR RVModel.singR RVModel.finiteEntropy_X

namespace RVModel

variable {I J : Type*} [Finite I] [Finite J]

/-- **Every measurable variable on a model's sample space has finite entropy.**  This is
what Definition 3.1's hypothesis on `Ω` buys: the finiteness condition need never be
re-established for a derived variable, only its measurability.

It is a lemma rather than an instance because instance search cannot discharge the
`Measurable` side condition; the joint variables below register the instances that are
actually wanted. -/
lemma finiteEntropyOf (M : RVModel I) {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] {Z : M.Ω → S} (hZ : Measurable Z) :
    ShannonInformation.FiniteEntropyOf Z M.P :=
  ShannonInformation.finiteEntropyMeasure_map M.P hZ

/-! ## Definition 3.4 — joint variables -/

/-- The **joint random variable** `X_A = (Xᵢ)ᵢ∈A` at a finite set `A ⊆ I` of indices.

Paper node: `Definition 3.4` -/
def joint (M : RVModel I) (A : Finset I) : M.Ω → (∀ i : A, M.R i) := fun ω i => M.X i ω

/-- The **joint random variable** `Y_F = (Y_B)_{B ∈ F}` over an arbitrary subfamily `F` of
the index set.  Definition 3.4 states this for a latent variable model's family
`F ⊆ P⁺I`; it is stated here for a general index type because that is where it lives.
The paper's `Y_F` is `LatentModel.jointOn`, which carries the node annotation; this is the
machinery it is built from. -/
def jointOn (M : RVModel J) (F : Set J) : M.Ω → (∀ B : F, M.R B) := fun ω B => M.X B ω

@[simp] lemma joint_apply (M : RVModel I) (A : Finset I) (ω : M.Ω) (i : A) :
    M.joint A ω i = M.X i ω := rfl

@[simp] lemma jointOn_apply (M : RVModel J) (F : Set J) (ω : M.Ω) (B : F) :
    M.jointOn F ω B = M.X B ω := rfl

lemma measurable_joint (M : RVModel I) (A : Finset I) : Measurable (M.joint A) :=
  measurable_pi_lambda _ fun i => M.measurable_X i

lemma measurable_jointOn (M : RVModel J) (F : Set J) : Measurable (M.jointOn F) :=
  measurable_pi_lambda _ fun B => M.measurable_X B

instance finiteEntropy_joint (M : RVModel I) (A : Finset I) :
    ShannonInformation.FiniteEntropyOf (M.joint A) M.P :=
  M.finiteEntropyOf (M.measurable_joint A)

instance finiteEntropy_jointOn (M : RVModel J) (F : Set J) :
    ShannonInformation.FiniteEntropyOf (M.jointOn F) M.P :=
  M.finiteEntropyOf (M.measurable_jointOn F)

/-- The joint variable over **all** of the index type, `X_I` — the top element of the
`X_A` family.  Spelled as the dependent product over `I` itself rather than as
`M.joint Finset.univ`, so that only `[Finite I]` is needed and no `Fintype I` datum has to
be produced to *name* it.  `Finset.univ` requires a `Fintype`; `∀ i, M.R i` does not.

Not a paper node of its own: it is `Definition 3.4`'s `X_A` at `A = I`, up to the
coordinate relabelling `∀ i : (univ : Finset I), M.R i ≃ ∀ i, M.R i`. -/
def jointAll (M : RVModel I) : M.Ω → ∀ i, M.R i := fun ω i => M.X i ω

@[simp] lemma jointAll_apply (M : RVModel I) (ω : M.Ω) (i : I) : M.jointAll ω i = M.X i ω :=
  rfl

lemma measurable_jointAll (M : RVModel I) : Measurable M.jointAll :=
  measurable_pi_lambda _ fun i => M.measurable_X i

instance finiteEntropy_jointAll (M : RVModel I) :
    ShannonInformation.FiniteEntropyOf M.jointAll M.P :=
  M.finiteEntropyOf M.measurable_jointAll

/-! ### Restriction and projection of joint variables

The companions of `measurable_joint(On)` / `finiteEntropy_joint(On)` that §4 and §5 run on.
They are generic facts about `joint`/`jointOn`, not about any numbered node. -/

/-- Restriction of a joint variable along an inclusion of index families: `Y_G` is
(everywhere) a function of `Y_F` whenever `G ⊆ F`, namely the coordinate projection. -/
lemma functionOf_jointOn_mono (N : RVModel J) {F G : Set J} (h : G ⊆ F) :
    FunctionOf (N.jointOn F) (N.jointOn G) :=
  ⟨fun y B => y ⟨B.1, h B.2⟩, measurable_pi_lambda _ fun _ => measurable_pi_apply _,
    fun _ => rfl⟩

/-- The a.e. form of `RVModel.functionOf_jointOn_mono`, which is what the `AEFunctionOf`
API composes with. -/
lemma aeFunctionOf_jointOn_mono (N : RVModel J) {F G : Set J} (h : G ⊆ F)
    (μ : Measure N.Ω) : AEFunctionOf (N.jointOn F) (N.jointOn G) μ :=
  AEFunctionOf.of_functionOf (N.functionOf_jointOn_mono h)

/-- A single coordinate of a joint variable: `X_i` is (everywhere) a function of `X_A`
whenever `i ∈ A`. -/
lemma functionOf_joint (N : RVModel I) {A : Finset I} {i : I} (hi : i ∈ A) :
    FunctionOf (N.joint A) (N.X i) :=
  ⟨fun x => x ⟨i, hi⟩, measurable_pi_apply _, fun _ => rfl⟩

/-- `H(X_{i}) = H(X_i)`: the joint variable over a singleton index set is an injective
relabelling of the variable itself.  The index type `↥({i} : Finset I)` is a subsingleton,
which is what makes the coordinate projection injective. -/
lemma entropy_joint_singleton (N : RVModel I) (i : I) :
    H[N.joint {i} ; N.P] = H[N.X i ; N.P] := by
  have hinj : Function.Injective
      (fun x : (∀ j : ({i} : Finset I), N.R j) => x ⟨i, Finset.mem_singleton_self i⟩) := by
    intro x y hxy
    funext j
    obtain rfl : j = ⟨i, Finset.mem_singleton_self i⟩ := Subtype.ext (Finset.mem_singleton.mp j.2)
    exact hxy
  exact (entropy_comp_of_injective N.P (N.measurable_joint {i}) _ hinj).symm

end RVModel

/-! ## Definition 3.4 — the four families of contributing indices

The paper's `∩A`, `⊇A`, `⊋A` and `∋i` of (3.5)–(3.8), as subsets of `P⁺I`.  They are
declared before Definition 3.2 because `LatentModel`'s "contributes" field is stated with
`contribIdx`. -/

section Families

variable {I : Type*}

/-- `{B ∈ P⁺I : B ∩ A ≠ ∅}` — the latents that **contribute to** `A`, indexing `Y_∩A` of
(3.5).  Spelled as "some index of `A` lies in `B`" so that no `DecidableEq I` is needed;
`mem_contrib_iff` gives back the paper's literal `B ∩ A ≠ ∅`.  The node carrier for
(3.5) is `LatentModel.jointContrib`; this is the index family it ranges over. -/
def contrib (A : Finset I) : Set (PPlus I) := {B | ∃ i ∈ A, i ∈ B}

/-- `{B ∈ P⁺I : A ⊆ B}`, the index family of `Y_⊇A` of (3.6). -/
def above (A : Finset I) : Set (PPlus I) := {B | A ⊆ B.toFinset}

/-- `{B ∈ P⁺I : A ⊊ B}`, the index family of `Y_⊋A` of (3.7). -/
def strictAbove (A : Finset I) : Set (PPlus I) := {B | A ⊂ B.toFinset}

/-- `{B ∈ P⁺I : i ∈ B}` — the latents that **contribute to** `i`, indexing `Y_∋i` of
(3.8); the index family of `Y_∋i`. -/
def contribIdx (i : I) : Set (PPlus I) := {B | i ∈ B}

/-- `{B ∈ P⁺I : B` is incomparable to `A}` — neither a subset nor a superset of `A`.  This
is the family `F` of Definition 4.8's ordered Markov condition and of Proposition 4.10 (1).

"Incomparable" is Mathlib's `IncompRel`, not a local synonym: `IncompRel r a b` is
`¬ r a b ∧ ¬ r b a`, so `IncompRel (· ≤ ·) B A` is `rfl`-equal to the hand-written
`¬ B ≤ A ∧ ¬ A ≤ B` and `mem_incomparable` stays `Iff.rfl` (R2-F27).  Same policy as
"upward closed", which is Mathlib's `IsUpperSet` here and nothing of this library's own.

An *auxiliary index family* like `contrib`/`above`/`strictAbove`/`contribIdx`: it carries
no paper node, because Definition 4.8 is the independence statement, not the set. -/
def incomparable (A : PPlus I) : Set (PPlus I) := {B | IncompRel (· ≤ ·) B A}

@[simp] lemma mem_contrib {A : Finset I} {B : PPlus I} : B ∈ contrib A ↔ ∃ i ∈ A, i ∈ B :=
  Iff.rfl

@[simp] lemma mem_above {A : Finset I} {B : PPlus I} : B ∈ above A ↔ A ⊆ B.toFinset := Iff.rfl

@[simp] lemma mem_strictAbove {A : Finset I} {B : PPlus I} :
    B ∈ strictAbove A ↔ A ⊂ B.toFinset := Iff.rfl

@[simp] lemma mem_contribIdx {i : I} {B : PPlus I} : B ∈ contribIdx i ↔ i ∈ B := Iff.rfl

@[simp] lemma mem_incomparable {A B : PPlus I} :
    B ∈ incomparable A ↔ ¬ B ≤ A ∧ ¬ A ≤ B := Iff.rfl

/-- `contrib A` is literally the paper's `{B : B ∩ A ≠ ∅}`. -/
lemma mem_contrib_iff [DecidableEq I] {A : Finset I} {B : PPlus I} :
    B ∈ contrib A ↔ (B.toFinset ∩ A).Nonempty := by
  simp [contrib, Finset.Nonempty, Finset.mem_inter, and_comm]

/-- Equation (3.9): `Y_∋i = Y_∩{i}`. -/
lemma contribIdx_eq_contrib_singleton (i : I) : contribIdx i = contrib {i} := by
  ext B; simp

/-- Equation (3.9): `Y_∋i = Y_⊇{i}`. -/
lemma contribIdx_eq_above_singleton (i : I) : contribIdx i = above {i} := by
  ext B; simp [Finset.singleton_subset_iff]

lemma strictAbove_subset_above (A : Finset I) : strictAbove A ⊆ above A := by
  intro B hB
  show A ⊆ B.toFinset
  exact (hB : A ⊂ B.toFinset).subset

/-- `contribIdx i ⊆ contrib A` whenever `i ∈ A`: every latent contributing to `i`
contributes to `A`.  The companion of `strictAbove_subset_above`, and the inclusion of
index families behind the last inequality of (4.6). -/
lemma contribIdx_subset_contrib {i : I} {A : Finset I} (hi : i ∈ A) :
    contribIdx i ⊆ contrib A :=
  fun _ hB => ⟨i, hi, hB⟩

/-! ### Upward closure

§4.10 and §5 quantify over *upward-closed* subfamilies of `P⁺I`.  That is Mathlib's
`IsUpperSet` for the inclusion order `PPlus.instPartialOrder`; the library uses it
directly rather than defining a synonym. -/

/-- `{B : B ∩ A ≠ ∅}` is upward-closed — Proposition 4.10's hypothesis shape, and why the
leaf labels of Theorem 5.8's intersection tree lie in the lattice that theorem's tree
ranges over. -/
lemma isUpperSet_contrib (A : Finset I) : IsUpperSet (contrib A) := by
  rintro B C hBC ⟨i, hiA, hiB⟩
  exact ⟨i, hiA, hBC hiB⟩

/-- `{B : A ⊆ B}` is upward-closed. -/
lemma isUpperSet_above (A : Finset I) : IsUpperSet (above A) := by
  intro B C hBC hB
  exact (hB : A ⊆ B.toFinset).trans (PPlus.le_iff.mp hBC)

/-- `B ↦ {C : B ∩ C ≠ ∅}` is injective on `P⁺I`.  This is what makes Theorem 5.8's
hypothesis "`ℓ` restricts to a bijection between the leaves of `T` and the sets
`{C : B ∩ C ≠ ∅}` ranging over `B ∈ F`" equivalent to the multiset equation stated there:
the image multiset is automatically duplicate-free. -/
lemma contrib_injective :
    Function.Injective (fun A : PPlus I => contrib A.toFinset) := by
  intro A B h
  ext i
  simp only at h
  have h' : PPlus.single i ∈ contrib A.toFinset ↔ PPlus.single i ∈ contrib B.toFinset := by
    rw [h]
  simpa using h'

end Families

/-! ## Definition 3.2 — latent variable models -/

/-- A **latent variable model** for a random variable model `M = (Ω, (Xᵢ)ᵢ∈I)`: a random
variable model `L = (Λ, (Y_A)_{A ∈ P⁺I})` indexed by the nonempty power set of `I`,
together with a probability-preserving map `π : Λ → Ω` such that each pullback `π^* Xᵢ` is
almost everywhere a function of the latents that contribute to `i`.

Note the direction: `π` goes from the *latent* space `Λ` down to `Ω`, the opposite of the
morphisms of §3.1.

The latent model's universes are **independent** of `M`'s: `Λ : Type u'` and the latent
ranges in `Type v'`, with `u'`/`v'` unrelated to `M`'s `u`/`v`.  Nothing in the paper ties
them, and Example 4.4 needs them apart — there `X_i := Y_∋i` puts the *given* ranges in
`Type (max v' w)` while the latent ranges stay in `Type v'`, which is unstatable if the
two are pinned together.

Paper node: `Definition 3.2` -/
structure LatentModel {I : Type w} [Finite I] (M : RVModel.{u, v, w} I) where
  /-- The latent random variable model `(Λ, (Y_A)_{A ∈ P⁺I})`. -/
  L : RVModel.{u', v', w} (PPlus I)
  /-- The probability-preserving map `π : Λ → Ω`. -/
  π : L.Ω → M.Ω
  π_pres : MeasurePreserving π L.P M.P
  /-- Each `π^* Xᵢ` is a.e. a function of `Y_∋i`. -/
  contributes : ∀ i, AEFunctionOf (L.jointOn (contribIdx i)) (M.X i ∘ π) L.P

namespace LatentModel

variable {I : Type*} [Finite I] {M : RVModel I} (L : LatentModel M)

/-- The latent sample space `Λ`. -/
abbrev Λ : Type _ := L.L.Ω

/-- The measure on the latent sample space. -/
abbrev P : Measure L.Λ := L.L.P

/-- The latent variables `Y_A`, `A ∈ P⁺I`. -/
abbrev Y : ∀ A : PPlus I, L.Λ → L.L.R A := L.L.X

/-- The joint latent variable `Y_F` over a subfamily `F ⊆ P⁺I` (Definition 3.4).

Paper node: `Definition 3.4` -/
abbrev jointOn (F : Set (PPlus I)) : L.Λ → (∀ B : F, L.L.R B) := L.L.jointOn F

/-- `Y_∩A` of (3.5).

Paper node: `Definition 3.4` -/
abbrev jointContrib (A : Finset I) := L.jointOn (contrib A)

/-- `Y_⊇A` of (3.6).

Paper node: `Definition 3.4` -/
abbrev jointAbove (A : Finset I) := L.jointOn (above A)

/-- `Y_⊋A` of (3.7).

Paper node: `Definition 3.4` -/
abbrev jointStrictAbove (A : Finset I) := L.jointOn (strictAbove A)

/-- `Y_∋i` of (3.8).

Paper node: `Definition 3.4` -/
abbrev jointContribIdx (i : I) := L.jointOn (contribIdx i)

/-- The pullback `π^* X_A` of the joint variable `X_A` to the latent space — the paper's
convention (2.2) that `X_A` may be read as a random variable on `Λ`. -/
abbrev pullbackJoint (A : Finset I) : L.Λ → (∀ i : A, M.R i) := M.joint A ∘ L.π

lemma measurable_pullbackJoint (A : Finset I) : Measurable (L.pullbackJoint A) :=
  (M.measurable_joint A).comp L.π_pres.measurable

instance finiteEntropy_pullbackJoint (A : Finset I) :
    ShannonInformation.FiniteEntropyOf (L.pullbackJoint A) L.P :=
  L.L.finiteEntropyOf (L.measurable_pullbackJoint A)

/-- Convention (2.2) for the joint variable `X_A`: its entropy is the same computed on `Ω`
or pulled back to `Λ`. -/
lemma entropy_pullbackJoint (A : Finset I) :
    H[L.pullbackJoint A ; L.P] = H[M.joint A ; M.P] :=
  entropy_comp_measurePreserving L.π_pres (M.measurable_joint A)

/-! ## Definition 3.3 — the three scores

All three are real numbers: Definition 3.1's finite-entropy sample space makes every
entropy appearing in them finite, which is the paper's own remark after (3.3). -/

section Scores

/-- A subfamily of `P⁺I` is finite when `I` is; this is it as a `Finset`, which is what
the sums of (3.1) and (3.2) range over.  Only `[Finite I]` is needed — which every model
carries, Definition 3.1 asking for a finite family — so all three scores below have the
same binder shape and none of them can be formed over an infinite index type. -/
noncomputable def _root_.Condensation.famFinset (F : Set (PPlus I)) : Finset (PPlus I) :=
  (Set.toFinite F).toFinset

@[simp] lemma _root_.Condensation.mem_famFinset {F : Set (PPlus I)} {B : PPlus I} :
    B ∈ famFinset F ↔ B ∈ F := Set.Finite.mem_toFinset _

/-- The **simple score** `σ_L(A) = ∑_{B ∩ A ≠ ∅} H(Y_B)` of (3.1).

Paper node: `Definition 3.3` -/
noncomputable def simpleScore (A : Finset I) : ℝ :=
  ∑ B ∈ famFinset (contrib A), H[L.Y B ; L.P]

/-- The **conditioned score** `χ_L(A) = ∑_{B ∩ A ≠ ∅} H(Y_B | (Y_C)_{C ⊋ B})` of (3.2).

Paper node: `Definition 3.3` -/
noncomputable def condScore (A : Finset I) : ℝ :=
  ∑ B ∈ famFinset (contrib A), H[L.Y B | L.jointStrictAbove B.toFinset ; L.P]

/-- The **reconstruction score** `ϱ_L(A) = H((Y_B)_{B ⊇ A} | (Xᵢ)ᵢ∈A)` of (3.3).

`X_A` lives on `Ω` and `Y_⊇A` on `Λ`, so the conditioning variable is the pullback
`π^* X_A`, per the paper's convention (2.2) (`dd:pullback`).

Paper node: `Definition 3.3` -/
noncomputable def reconScore (A : Finset I) : ℝ :=
  H[L.jointAbove A | L.pullbackJoint A ; L.P]

end Scores

end LatentModel

end Condensation
