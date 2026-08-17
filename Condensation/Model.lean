import Condensation.Probability

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
* `dd:finite-range` — every variable of a model carries `FiniteRange`.  The paper asks for
  countable discrete range and finite entropy; this is strictly stronger, and is the
  standing disclosed narrowing forced by the vendored entropy library
  (`ShannonInformation/SCOPE.md`).  The paper's separate hypothesis that `Ω` itself has
  finite entropy is *not* carried: it is used in the paper only to make the variables'
  entropies finite, which finite range already does.
* `dd:pplus` — subfamilies `F ⊆ P⁺I` are `Set (PPlus I)`, and `Y_F` is the dependent
  product over the subtype `↥F`.
* Definition 3.1's "finite family of random variables" is **not** a field of `RVModel`:
  the index type `I` is unconstrained in the structure, and `[Fintype I] [DecidableEq I]`
  is required exactly on the declarations that need it (the scores, and everything
  quantifying over `P⁺I`).  Nothing is thereby claimed for infinite `I` that the paper
  claims for finite `I`.
-/

universe u v w

namespace Condensation

open MeasureTheory ProbabilityTheory

/-! ### A finite-range lemma for dependent products

`FiniteRange` has no instance for a dependent product of finite-range variables in the
vendored `FiniteRange/Defs.lean` (it has the binary product one).  This supplies it. -/

/-- A dependent product of finitely many finite-range variables has finite range. -/
lemma finiteRange_pi {Ω' ι : Type*} [Finite ι] {R : ι → Type*} (Z : ∀ i, Ω' → R i)
    [∀ i, FiniteRange (Z i)] : FiniteRange (fun ω i => Z i ω) where
  finite := by
    refine Set.Finite.subset (Set.Finite.pi (t := fun i => Set.range (Z i))
      fun i => (FiniteRange.finite (X := Z i))) ?_
    rintro _ ⟨ω, rfl⟩ i -
    exact Set.mem_range_self ω

/-! ## Definition 3.1 — random variable models -/

/-- A **random variable model**: a countable discrete probability space `Ω` together with
a family of random variables `Xᵢ : Ω → Rᵢ` with countable discrete ranges.

`dd:bundled-model`, `dd:finite-range`.  The paper's "countable discrete probability space
with finite entropy" becomes `[Countable Ω] [MeasurableSingletonClass Ω]` plus
`[IsProbabilityMeasure P]` — with no hypothesis on the entropy of `Ω` itself — and the
paper's "countable and discrete range" becomes `[Countable (R i)]
[MeasurableSingletonClass (R i)]` *plus* `FiniteRange (X i)`.  The last conjunct is
strictly stronger than the paper (a geometric variable on `ℕ` is excluded); it is the
standing narrowing recorded in `Condensation/KNOWLEDGE.md`, forced by the fact that the
vendored entropy theorems are proved only in the finite-range fragment.

Paper node: `Definition 3.1` -/
structure RVModel (I : Type w) where
  /-- The sample space `Ω`. -/
  Ω : Type u
  [mΩ : MeasurableSpace Ω]
  [countΩ : Countable Ω]
  [singΩ : MeasurableSingletonClass Ω]
  /-- The probability measure `P` on `Ω`. -/
  P : Measure Ω
  [probP : IsProbabilityMeasure P]
  /-- The range `Rᵢ` of the `i`-th variable. -/
  R : I → Type v
  [mR : ∀ i, MeasurableSpace (R i)]
  [countR : ∀ i, Countable (R i)]
  [singR : ∀ i, MeasurableSingletonClass (R i)]
  /-- The random variables `Xᵢ : Ω → Rᵢ`. -/
  X : ∀ i, Ω → R i
  measurable_X : ∀ i, Measurable (X i)
  finiteRange_X : ∀ i, FiniteRange (X i)

attribute [instance] RVModel.mΩ RVModel.countΩ RVModel.singΩ RVModel.probP
  RVModel.mR RVModel.countR RVModel.singR RVModel.finiteRange_X

namespace RVModel

variable {I J : Type*}

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

instance finiteRange_joint (M : RVModel I) (A : Finset I) : FiniteRange (M.joint A) := by
  exact finiteRange_pi (fun (i : A) => M.X (i : I))

instance finiteRange_jointOn (M : RVModel J) (F : Set J) [Finite F] :
    FiniteRange (M.jointOn F) := by
  exact finiteRange_pi (fun (B : F) => M.X (B : J))

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

@[simp] lemma mem_contrib {A : Finset I} {B : PPlus I} : B ∈ contrib A ↔ ∃ i ∈ A, i ∈ B :=
  Iff.rfl

@[simp] lemma mem_above {A : Finset I} {B : PPlus I} : B ∈ above A ↔ A ⊆ B.toFinset := Iff.rfl

@[simp] lemma mem_strictAbove {A : Finset I} {B : PPlus I} :
    B ∈ strictAbove A ↔ A ⊂ B.toFinset := Iff.rfl

@[simp] lemma mem_contribIdx {i : I} {B : PPlus I} : B ∈ contribIdx i ↔ i ∈ B := Iff.rfl

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

end Families

/-! ## Definition 3.2 — latent variable models -/

/-- A **latent variable model** for a random variable model `M = (Ω, (Xᵢ)ᵢ∈I)`: a random
variable model `L = (Λ, (Y_A)_{A ∈ P⁺I})` indexed by the nonempty power set of `I`,
together with a probability-preserving map `π : Λ → Ω` such that each pullback `π^* Xᵢ` is
almost everywhere a function of the latents that contribute to `i`.

Note the direction: `π` goes from the *latent* space `Λ` down to `Ω`, the opposite of the
morphisms of §3.1.

The latent model is pinned to the same universes as `M` (`Λ : Type u`, each latent range
in `Type v`).  This is the documented universe narrowing of `dd:bundled-model`; leaving
the two pairs independent makes `LatentModel M` require explicit universe annotations at
every use site for no mathematical gain, since the paper's spaces are all countable and
discrete.

Paper node: `Definition 3.2` -/
structure LatentModel {I : Type w} (M : RVModel.{u, v, w} I) where
  /-- The latent random variable model `(Λ, (Y_A)_{A ∈ P⁺I})`. -/
  L : RVModel.{u, v, w} (PPlus I)
  /-- The probability-preserving map `π : Λ → Ω`. -/
  π : L.Ω → M.Ω
  π_pres : MeasurePreserving π L.P M.P
  /-- Each `π^* Xᵢ` is a.e. a function of `Y_∋i`. -/
  contributes : ∀ i, AEFunctionOf (L.jointOn (contribIdx i)) (M.X i ∘ π) L.P

namespace LatentModel

variable {I : Type*} {M : RVModel I} (L : LatentModel M)

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

/-! ## Definition 3.3 — the three scores

All three are real numbers: `dd:finite-range` makes every entropy appearing in them
finite, which is the paper's own remark after (3.3). -/

section Scores

variable [Fintype I] [DecidableEq I]

/-- A subfamily of `P⁺I` is finite when `I` is; this is it as a `Finset`, which is what
the sums of (3.1) and (3.2) range over. -/
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
