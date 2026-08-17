import ShannonInformation.API

/-!
# Condensation §2 — probabilistic conventions

This file is §2 of Eisenstat, *Condensation: A Theory of Concepts* (July 2025;
`Condensation/notes/condensation-25-07.pdf`): the notational conventions the rest of the
paper runs on, and the one substantive result of the section, Proposition 2.5.

Contents:

* Definition 2.1's fifth convention — "`Y` is a function of `X`", everywhere
  (`FunctionOf`) and almost everywhere (`AEFunctionOf`) — together with the pullback
  invariance of equation (2.2);
* Definition 2.2 — the nonempty power set `P⁺ I` (`PPlus`);
* Definition 2.3 — interaction information (`interactionInfo`) and its conditional form
  (`condInteractionInfo`), over the entropy vocabulary re-exported by
  `ShannonInformation.API`;
* Definition 2.4 — the Giry σ-algebra on the space of measures (`GiryMeasurableSpace`);
* **Proposition 2.5** — the determinism bridge `H(Y | X) = 0 → Y = f(X)` a.e., and its
  converse, which §4 uses in both directions.

## Modeling decisions

`dd:ae-function`, `dd:pullback`, `dd:pplus`, `dd:interaction`, `dd:finite-range` — see the
`dd:` glossary in `Condensation.lean` and `Condensation/notes/roadmap.md`.  The one that
shapes every statement here is `dd:finite-range`: the vendored entropy library proves its
theorems only for finite-range variables (`ShannonInformation/SCOPE.md`), so every
statement with entropy content carries `FiniteRange`, which is strictly narrower than the
paper's "countable discrete range with finite entropy".  This is a disclosed narrowing,
recorded in `Condensation/KNOWLEDGE.md`.

Entropy, conditional entropy, mutual information and conditional mutual information are
**not** defined here: they are PFR's, re-exported through `ShannonInformation.API`.  No
`PFR.*` module is named, and Mathlib is never imported wholesale (that clashes with the
vendored shims — see `ShannonInformation/README.md`).
-/

universe u v w

namespace Condensation

open MeasureTheory ProbabilityTheory

/-! ## Definition 2.1 — random variables, pullbacks, and "is a function of" -/

section FunctionOf

variable {Ω Λ S T U : Type*}

/-- A **random variable** is a measurable function between measurable spaces.  The paper
introduces no structure beyond measurability; the concept exists to license a family of
notational conventions (`f (X)` for `f ∘ X`, `(X, Y)` for the product variable, `π^* X`
for the pullback `X ∘ π`), each of which is spelled directly in Lean.  This alias names
the Mathlib rendering; it is not a new definition.

Paper node: `Definition 2.1` -/
abbrev IsRandomVariable [MeasurableSpace Ω] [MeasurableSpace S] (X : Ω → S) : Prop :=
  Measurable X

/-- `Y` **is a function of** `X`: there is a measurable `f : R_X → R_Y` with `Y = f (X)`.
This is the fifth convention of Definition 2.1.

The measurability conjunct is kept even though it is free on the countable discrete ranges
this paper works over (`measurable_of_countable`), so that the definition cannot drift from
the paper's (`dd:ae-function`).

Paper node: `Definition 2.1` -/
def FunctionOf [MeasurableSpace S] [MeasurableSpace T] (X : Ω → S) (Y : Ω → T) : Prop :=
  ∃ f : S → T, Measurable f ∧ ∀ ω, Y ω = f (X ω)

/-- `Y` **is a function of `X` almost everywhere**: there is a measurable `f : R_X → R_Y`
with `Y = f (X)` off a `μ`-null set.  This is the a.e. variant of Definition 2.1's fifth
convention, and it is the form Definition 3.2 and all of §4 use.

The measure is an explicit argument, following the vendored API's convention of writing
`H[X ; μ]` rather than leaving `μ` implicit (`dd:ae-function`).

Paper node: `Definition 2.1` -/
def AEFunctionOf [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : Prop :=
  ∃ f : S → T, Measurable f ∧ ∀ᵐ ω ∂μ, Y ω = f (X ω)

variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  {μ : Measure Ω} {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

lemma AEFunctionOf.of_functionOf (h : FunctionOf X Y) : AEFunctionOf X Y μ := by
  obtain ⟨f, hf, hfX⟩ := h
  exact ⟨f, hf, Filter.Eventually.of_forall hfX⟩

omit [MeasurableSpace Ω] in
lemma functionOf_comp {f : S → T} (hf : Measurable f) : FunctionOf X (f ∘ X) :=
  ⟨f, hf, fun _ => rfl⟩

lemma aeFunctionOf_comp {f : S → T} (hf : Measurable f) : AEFunctionOf X (f ∘ X) μ :=
  AEFunctionOf.of_functionOf (functionOf_comp hf)

lemma aeFunctionOf_self : AEFunctionOf X X μ :=
  aeFunctionOf_comp (f := id) measurable_id

/-- Post-composing the dependent variable with a measurable map preserves "is a.e. a
function of". -/
lemma AEFunctionOf.comp (h : AEFunctionOf X Y μ) {g : T → U} (hg : Measurable g) :
    AEFunctionOf X (g ∘ Y) μ := by
  obtain ⟨f, hf, hfX⟩ := h
  refine ⟨g ∘ f, hg.comp hf, ?_⟩
  filter_upwards [hfX] with ω hω
  simp [Function.comp_apply, hω]

/-- "Is a.e. a function of" is transitive. -/
lemma AEFunctionOf.trans (h : AEFunctionOf X Y μ) (h' : AEFunctionOf Y Z μ) :
    AEFunctionOf X Z μ := by
  obtain ⟨f, hf, hfX⟩ := h
  obtain ⟨g, hg, hgY⟩ := h'
  refine ⟨g ∘ f, hg.comp hf, ?_⟩
  filter_upwards [hfX, hgY] with ω hω hω'
  simp [Function.comp_apply, hω', hω]

/-- A pair of variables each of which is a.e. a function of `X` is itself a.e. a function
of `X`. -/
lemma AEFunctionOf.prodMk (h : AEFunctionOf X Y μ) (h' : AEFunctionOf X Z μ) :
    AEFunctionOf X (⟨Y, Z⟩ : Ω → T × U) μ := by
  obtain ⟨f, hf, hfX⟩ := h
  obtain ⟨g, hg, hgX⟩ := h'
  refine ⟨fun s => (f s, g s), hf.prodMk hg, ?_⟩
  filter_upwards [hfX, hgX] with ω hω hω'
  simp [hω, hω']

/-- **Pullback of an a.e. functional dependence** (Definition 2.1, `dd:pullback`).  If `Y`
is a.e. a function of `X` on `Ω` and `π : Λ → Ω` is measure preserving, then `π^* Y` is
a.e. a function of `π^* X` on `Λ`. -/
lemma AEFunctionOf.comp_measurePreserving [MeasurableSpace Λ] {μΛ : Measure Λ} {π : Λ → Ω}
    (hπ : MeasurePreserving π μΛ μ) (h : AEFunctionOf X Y μ) :
    AEFunctionOf (X ∘ π) (Y ∘ π) μΛ := by
  obtain ⟨f, hf, hfX⟩ := h
  refine ⟨f, hf, ?_⟩
  have := hπ.quasiMeasurePreserving.ae hfX
  filter_upwards [this] with l hl using hl

end FunctionOf

/-! ## Equation (2.2) — invariance of the information quantities under pullback

The paper's convention that a random variable on `Ω` may be silently read as a random
variable on `Λ` is licensed by these three identities (`dd:pullback`).  Each is
`IdentDistrib`-based: a measure-preserving `π` makes `X` and `π^* X` identically
distributed. -/

section Pullback

variable {Λ Ω S T : Type*} [MeasurableSpace Λ] [MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T]
  {μΛ : Measure Λ} {μΩ : Measure Ω} {π : Λ → Ω} {X : Ω → S} {Y : Ω → T}

/-- Pullback along a measure-preserving map identifies distributions: `π^* X` and `X` are
identically distributed. -/
lemma identDistrib_comp_measurePreserving (hπ : MeasurePreserving π μΛ μΩ)
    (hX : Measurable X) : IdentDistrib (X ∘ π) X μΛ μΩ :=
  (hπ.identDistrib hX.aemeasurable).symm

/-- Entropy is invariant under pullback along a measure-preserving map. -/
lemma entropy_comp_measurePreserving (hπ : MeasurePreserving π μΛ μΩ) (hX : Measurable X) :
    H[X ∘ π ; μΛ] = H[X ; μΩ] :=
  (identDistrib_comp_measurePreserving hπ hX).entropy_congr

/-- **Equation (2.2)**: mutual information is invariant under pullback along a
measure-preserving map. -/
lemma mutualInfo_comp_measurePreserving (hπ : MeasurePreserving π μΛ μΩ)
    (hX : Measurable X) (hY : Measurable Y) :
    I[X ∘ π : Y ∘ π ; μΛ] = I[X : Y ; μΩ] := by
  have h : IdentDistrib (⟨X ∘ π, Y ∘ π⟩ : Λ → S × T) (⟨X, Y⟩ : Ω → S × T) μΛ μΩ :=
    identDistrib_comp_measurePreserving hπ (hX.prodMk hY)
  exact h.mutualInfo_eq

/-- Conditional entropy is invariant under pullback along a measure-preserving map. -/
lemma condEntropy_comp_measurePreserving [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T]
    [IsProbabilityMeasure μΛ] [IsProbabilityMeasure μΩ]
    (hπ : MeasurePreserving π μΛ μΩ) (hX : Measurable X) (hY : Measurable Y)
    [FiniteRange X] [FiniteRange Y] :
    H[X ∘ π | Y ∘ π ; μΛ] = H[X | Y ; μΩ] := by
  have h : IdentDistrib (⟨X ∘ π, Y ∘ π⟩ : Λ → S × T) (⟨X, Y⟩ : Ω → S × T) μΛ μΩ :=
    identDistrib_comp_measurePreserving hπ (hX.prodMk hY)
  exact IdentDistrib.condEntropy_eq (hX.comp hπ.measurable) (hY.comp hπ.measurable) hX hY h

end Pullback

/-! ## Definition 2.2 — the nonempty power set `P⁺ S` -/

/-- `P⁺ I`, the **nonempty power set** of `I`: the nonempty finite subsets of `I`.  For the
finite index sets of Definition 3.1 this is exactly the paper's set of nonempty subsets
(`dd:pplus`); the `Finset` carrier is what makes the joint variables `Y_F` of Definition
3.4 index over a finite type by instance.

Paper node: `Definition 2.2` -/
def PPlus (I : Type u) : Type u := {A : Finset I // A.Nonempty}

namespace PPlus

variable {I : Type u}

/-- The underlying finite set of an element of `P⁺ I`. -/
def toFinset (A : PPlus I) : Finset I := A.1

instance : CoeHead (PPlus I) (Finset I) := ⟨toFinset⟩

instance : Membership I (PPlus I) := ⟨fun A i => i ∈ A.toFinset⟩

@[simp] lemma mem_iff {i : I} {A : PPlus I} : i ∈ A ↔ i ∈ A.toFinset := Iff.rfl

@[simp] lemma coe_toFinset (A : PPlus I) : (A : Finset I) = A.toFinset := rfl

lemma nonempty (A : PPlus I) : A.toFinset.Nonempty := A.2

@[ext] lemma ext {A B : PPlus I} (h : A.toFinset = B.toFinset) : A = B := Subtype.ext h

lemma toFinset_injective : Function.Injective (toFinset (I := I)) := fun _ _ h => ext h

/-- The order on `P⁺ I` is inclusion of the underlying sets. -/
instance : PartialOrder (PPlus I) := PartialOrder.lift toFinset toFinset_injective

lemma le_iff {A B : PPlus I} : A ≤ B ↔ A.toFinset ⊆ B.toFinset := Iff.rfl

lemma lt_iff {A B : PPlus I} : A < B ↔ A.toFinset ⊂ B.toFinset := Iff.rfl

instance [DecidableEq I] : DecidableEq (PPlus I) := fun A B =>
  decidable_of_iff (A.toFinset = B.toFinset) ⟨ext, fun h => by rw [h]⟩

instance [Fintype I] [DecidableEq I] : Fintype (PPlus I) := Subtype.fintype _

instance [Countable I] : Countable (PPlus I) := Subtype.countable

instance [Nonempty I] : Nonempty (PPlus I) :=
  ⟨⟨{Classical.arbitrary I}, Finset.singleton_nonempty _⟩⟩

/-- The singleton `{i} ∈ P⁺ I`. -/
def single (i : I) : PPlus I := ⟨{i}, Finset.singleton_nonempty i⟩

@[simp] lemma toFinset_single (i : I) : (single i).toFinset = {i} := rfl

@[simp] lemma mem_single {i j : I} : j ∈ single i ↔ j = i := Finset.mem_singleton

end PPlus

/-! ## Definition 2.3 — interaction information -/

section Interaction

variable {Ω S T U V : Type*} [MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]

/-- The **interaction information** `I(X; Y; Z) = I(X; Y) − I(X; Y | Z)` of equation
(2.3).  FAF-authored over the vendored `mutualInfo`/`condMutualInfo` (`dd:interaction`);
the shared API deliberately adds no definitions of its own.

Paper node: `Definition 2.3` -/
noncomputable def interactionInfo (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) : ℝ :=
  I[X : Y ; μ] - I[X : Y|Z;μ]

/-- The **conditional interaction information**
`I(X; Y; Z | C) = I(X; Y | C) − I(X; Y | ⟨Z, C⟩)`, the form Lemma 5.4 and Theorem 5.8 use.

The paper does *not* number this: Definition 2.3 introduces only `I(X; Y; Z)` at (2.3),
and §5 writes the conditional form without defining it.  It is therefore FAF-authored
(`dd:interaction`) and carries no paper node; `interactionInfo` is Definition 2.3's
carrier. -/
noncomputable def condInteractionInfo (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (C : Ω → V)
    (μ : Measure Ω) : ℝ :=
  I[X : Y|C;μ] - I[X : Y|⟨Z, C⟩;μ]

variable [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
  {μ : Measure Ω} {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

omit [Countable U] [MeasurableSingletonClass U] in
/-- Interaction information is symmetric in its first two arguments. -/
lemma interactionInfo_comm (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U)
    (μ : Measure Ω) : interactionInfo X Y Z μ = interactionInfo Y X Z μ := by
  rw [interactionInfo, interactionInfo, mutualInfo_comm hX hY, condMutualInfo_comm hX hY]

/-- Interaction information is symmetric in its last two arguments — the second half of
the paper's remark that `I(X; Y; Z)` is invariant under permutation of its arguments.
Together with `interactionInfo_comm` this generates the full symmetric group on the three
arguments. -/
lemma interactionInfo_swap [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    interactionInfo X Y Z μ = interactionInfo X Z Y μ := by
  have hcond : H[X | ⟨Z, Y⟩ ; μ] = H[X | ⟨Y, Z⟩ ; μ] :=
    condEntropy_of_injective' μ hX (hY.prodMk hZ) Prod.swap Prod.swap_injective
      (hZ.prodMk hY)
  rw [interactionInfo, interactionInfo,
    mutualInfo_eq_entropy_sub_condEntropy hX hY μ, mutualInfo_eq_entropy_sub_condEntropy hX hZ μ,
    condMutualInfo_eq' hX hY hZ μ, condMutualInfo_eq' hX hZ hY μ, hcond]
  ring

end Interaction

/-! ## Definition 2.4 — the Giry σ-algebra -/

/-- **`G (Ω)`**: the space of measures on `Ω`, equipped with the smallest σ-algebra making
every evaluation map `P ↦ P E` (for `E ⊆ Ω` measurable) measurable.  This is Mathlib's
`MeasureTheory.Measure.instMeasurableSpace`; the alias exists only to name the paper's
`G (Ω)` and is not a new definition.

Paper node: `Definition 2.4` -/
abbrev GiryMeasurableSpace (Ω : Type*) [MeasurableSpace Ω] : MeasurableSpace (Measure Ω) :=
  inferInstance

/-! ## Proposition 2.5 — the determinism bridge -/

section Prop25

variable {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  {μ : Measure Ω} {X : Ω → S} {Y : Ω → T}

/-- An a.e. function of `X` has no more entropy than `X` — the data-processing inequality
in the form §4 uses it. -/
lemma entropy_le_of_aeFunctionOf [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) [FiniteRange X] (h : AEFunctionOf X Y μ) : H[Y ; μ] ≤ H[X ; μ] := by
  obtain ⟨f, hf, hfX⟩ := h
  have hae : Y =ᵐ[μ] f ∘ X := hfX
  rw [entropy_congr hae]
  exact entropy_comp_le μ hX f

omit [Countable T] in
/-- Adjoining an a.e. function of `X` to `X` does not change the joint entropy. -/
lemma entropy_pair_of_aeFunctionOf [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) [FiniteRange X] (h : AEFunctionOf X Y μ) :
    H[⟨X, Y⟩ ; μ] = H[X ; μ] := by
  obtain ⟨f, hf, hfX⟩ := h
  have hae : (⟨X, Y⟩ : Ω → S × T) =ᵐ[μ] (fun ω => (X ω, f (X ω))) := by
    filter_upwards [hfX] with ω hω
    simp [hω]
  rw [entropy_congr hae]
  exact entropy_prod_comp hX μ f

/-- If `Y` is a.e. a function of `X` then it carries no residual uncertainty given `X`.
This is the converse of Proposition 2.5; the paper does not number it, but §4 uses both
directions constantly (for instance at (4.13)–(4.14)). -/
lemma condEntropy_eq_zero_of_aeFunctionOf [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y]
    (h : AEFunctionOf X Y μ) : H[Y | X ; μ] = 0 := by
  rw [chain_rule'' μ hY hX, entropy_comm hY hX, entropy_pair_of_aeFunctionOf hX h, sub_self]

omit [Countable T] in
/-- **Proposition 2.5** (the determinism bridge).  On a countable discrete probability
space, a variable of zero conditional entropy given `X` is almost everywhere a measurable
function of `X`.

This is what turns every entropy inequality of §4 into the paper's "is a function of"
conclusions (Lemma 4.5, Corollary 4.6, Theorem 4.9, Theorem 4.15).

`dd:finite-range`: the paper's hypothesis is countable discrete range with finite entropy;
here the variables carry `FiniteRange`, which is strictly stronger.  See
`Condensation/KNOWLEDGE.md`.

Paper node: `Proposition 2.5` -/
theorem aeFunctionOf_of_condEntropy_eq_zero [Countable Ω] [MeasurableSingletonClass Ω]
    [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    [FiniteRange X] [FiniteRange Y] (h : H[Y | X ; μ] = 0) : AEFunctionOf X Y μ := by
  classical
  have : Nonempty T := Nonempty.map Y μ.nonempty_of_neZero
  have hsum : ∑ x ∈ FiniteRange.toFinset X, ((μ.map X).real {x}) * H[Y | X ← x; μ] = 0 := by
    rw [← condEntropy_eq_sum Y X μ hX, h]
  have hterm : ∀ x ∈ FiniteRange.toFinset X, ((μ.map X).real {x}) * H[Y | X ← x; μ] = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
      mul_nonneg measureReal_nonneg (entropy_nonneg _ _)).mp hsum
  have key : ∀ x : S, μ (X ⁻¹' {x}) ≠ 0 → ∃ t : T, (μ[|X ⁻¹' {x}]).real (Y ⁻¹' {t}) = 1 := by
    intro x hx
    haveI : IsProbabilityMeasure (μ[|X ⁻¹' {x}]) := cond_isProbabilityMeasure hx
    obtain ⟨ω, hω⟩ : (X ⁻¹' {x}).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro he
      exact hx (by rw [he, measure_empty])
    have hmem : x ∈ FiniteRange.toFinset X := (FiniteRange.mem_iff X x).2 ⟨ω, hω⟩
    have hmass : ((μ.map X).real {x}) ≠ 0 := by
      rw [map_measureReal_apply hX (MeasurableSet.singleton x)]
      exact (measureReal_ne_zero_iff (measure_ne_top μ _)).2 hx
    refine const_of_nonpos_entropy hY (le_of_eq ?_)
    exact (mul_eq_zero.1 (hterm x hmem)).resolve_left hmass
  refine ⟨fun x => if hx : μ (X ⁻¹' {x}) ≠ 0 then (key x hx).choose else Classical.arbitrary T,
    measurable_of_countable _, ?_⟩
  rw [ae_iff_of_countable]
  intro ω hω
  have hsub : ({ω} : Set Ω) ⊆ X ⁻¹' {X ω} := Set.singleton_subset_iff.2 rfl
  have hfib : μ (X ⁻¹' {X ω}) ≠ 0 := fun h0 => hω (measure_mono_null hsub h0)
  haveI : IsProbabilityMeasure (μ[|X ⁻¹' {X ω}]) := cond_isProbabilityMeasure hfib
  show Y ω = if hx : μ (X ⁻¹' {X ω}) ≠ 0 then (key (X ω) hx).choose else Classical.arbitrary T
  rw [dif_pos hfib]
  set t : T := (key (X ω) hfib).choose
  have hspec : (μ[|X ⁻¹' {X ω}]).real (Y ⁻¹' {t}) = 1 := (key (X ω) hfib).choose_spec
  have h1 : (μ[|X ⁻¹' {X ω}]) (Y ⁻¹' {t}) = 1 := by
    rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at hspec
  have h2 : (μ[|X ⁻¹' {X ω}]) {ω} ≠ 0 := by
    rw [cond_apply (hX (MeasurableSet.singleton (X ω))), Set.inter_eq_right.2 hsub]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 (measure_ne_top μ _)) hω
  have h3 : (μ[|X ⁻¹' {X ω}]) (Y ⁻¹' {t})ᶜ = 0 := by
    rw [measure_compl (hY (MeasurableSet.singleton t)) (measure_ne_top _ _), h1, measure_univ,
      tsub_self]
  by_contra hne
  exact h2 (measure_mono_null (Set.singleton_subset_iff.2 hne) h3)

/-- Proposition 2.5 and its converse, as the equivalence §4 actually uses. -/
lemma aeFunctionOf_iff_condEntropy_eq_zero [Countable Ω] [MeasurableSingletonClass Ω]
    [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    [FiniteRange X] [FiniteRange Y] : AEFunctionOf X Y μ ↔ H[Y | X ; μ] = 0 :=
  ⟨condEntropy_eq_zero_of_aeFunctionOf hX hY, aeFunctionOf_of_condEntropy_eq_zero hX hY⟩

end Prop25

end Condensation
