import ShannonInformation.API
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

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
* Definition 2.4 — the Giry σ-algebra on the space of *probability* measures
  (`GiryMeasurableSpace`);
* **Proposition 2.5** — the determinism bridge `H(Y | X) = 0 → Y = f(X)` a.e., and its
  converse, which §4 uses in both directions.

## Modeling decisions

`dd:ae-function`, `dd:pullback`, `dd:pplus`, `dd:interaction` — see the `dd:` glossary in
`Condensation.lean` and `Condensation/notes/roadmap.md`.  The finiteness hypothesis is the
paper's own: a variable of **finite entropy** with countable discrete range, rendered as
`[ShannonInformation.FiniteEntropyOf X μ]` over the FAF finite-entropy layer of
`ShannonInformation.API`.  `dd:finite-range` — the standing narrowing to `FiniteRange`
variables, forced while the vendored theorems existed only in the finite-range fragment —
was **retired on 2026-08-17**; there is no modeling substitution in this file.

Finiteness is **not** carried by every statement with entropy content, and it is worth
knowing which: exactly **eleven** declarations here take it, namely
`condEntropy_comp_measurePreserving`, `interactionInfo_swap`,
`condEntropy_eq_entropy_of_subsingleton`, `entropy_le_of_aeFunctionOf`,
`condEntropy_eq_zero_of_aeFunctionOf`, `aeFunctionOf_of_condEntropy_eq_zero`,
`aeFunctionOf_iff_condEntropy_eq_zero`, `condEntropy_congr_of_aeFunctionOf`,
`condEntropy_le_condEntropy_of_aeFunctionOf`, `condEntropy_le_of_aeFunctionOf` and
`condEntropy_eq_zero_of_subsingleton`.  (The count read "seven" until 2026-08-18; the last
four arrived with the conditional-entropy comparison block and the subsingleton companions
and were never added to it.  Re-derive it by grepping `FiniteEntropyOf` in the binders,
not by trusting this sentence.)  The pullback identities
`entropy_comp_measurePreserving` and `mutualInfo_comp_measurePreserving`, the first
symmetry `interactionInfo_comm` and `entropy_pair_of_aeFunctionOf` are `IdentDistrib`- or
injectivity-based and hold with no finiteness at all (`entropy_pair_of_aeFunctionOf` lost
its hypothesis in the same change; `ProbabilityTheory.entropy_prod_comp` never needed
one); `interactionInfo` and `condInteractionInfo` are definitions and carry none either.
These are §2 substrate lemmas over **bare variables**, so the hypothesis is explicit here
rather than supplied by a model structure — `RVModel` (Definition 3.1) hands it to every
statement quantifying over a model.

**Namespace hazard.**  With `ProbabilityTheory` open, a bare entropy lemma name resolves by
elaboration success, not by namespace, and can silently pick the vendored `FiniteRange`
version.  Every FAF-layer citation below is written `ShannonInformation.foo` in full; see
`ShannonInformation/API.lean`'s "which version to cite" table.

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

/-- A family of variables each of which is a.e. a function of `X`, indexed by a countable
type, is jointly a.e. a function of `X`.  This is the form §4 needs: `X_A` is a.e. a
function of `Y_∩A` because each `X_i`, `i ∈ A`, is a.e. a function of `Y_∋i`. -/
lemma AEFunctionOf.pi {ι : Type*} [Countable ι] {R : ι → Type*} [∀ i, MeasurableSpace (R i)]
    {Z : ∀ i, Ω → R i} (h : ∀ i, AEFunctionOf X (Z i) μ) :
    AEFunctionOf X (fun ω i => Z i ω) μ := by
  choose f hf hfX using h
  refine ⟨fun s i => f i s, measurable_pi_lambda _ hf, ?_⟩
  rw [← ae_all_iff] at hfX
  filter_upwards [hfX] with ω hω
  exact funext hω

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

/-- Replacing the *independent* variable of an a.e. functional dependence by an
a.e.-equal one.  `LatentAmalgamation.comm` makes this a workhorse of Theorem 4.15: a
dependence witnessed through `π̃₁` has to be read through `π̃₂`. -/
lemma AEFunctionOf.congr_left {X X' : Ω → S} {Y : Ω → T} (h : AEFunctionOf X Y μ)
    (hX : X =ᵐ[μ] X') : AEFunctionOf X' Y μ := by
  obtain ⟨f, hf, hfX⟩ := h
  refine ⟨f, hf, ?_⟩
  filter_upwards [hfX, hX] with ω hω hω' using hω.trans (congrArg f hω')

/-- Replacing the *dependent* variable of an a.e. functional dependence by an a.e.-equal
one: if `Y` is a.e. a function of `X` and `Y' = Y` a.e., then so is `Y'`.

This is also what reconciles the two maps `Λ₀ → Ω` of an amalgamation.  Definition 4.12's
contribution condition for `L̃₂` is phrased through `π̃₂` while Theorem 5.8's `X_B` is pulled
back along `π̃₁`; the field `LatentAmalgamation.comm` says the two agree almost everywhere,
and this lemma is how that field is consumed. -/
lemma AEFunctionOf.congr_right {X : Ω → S} {Y Y' : Ω → T} (h : AEFunctionOf X Y μ)
    (hY : Y' =ᵐ[μ] Y) : AEFunctionOf X Y' μ := by
  obtain ⟨f, hf, hfX⟩ := h
  refine ⟨f, hf, ?_⟩
  filter_upwards [hfX, hY] with ω hω hω' using hω'.trans hω

/-- `⟨X, V⟩` is a.e. a function of `⟨X, W⟩` when `V` is a.e. a function of `W`. -/
lemma AEFunctionOf.prodMk_left {X : Ω → S} {W : Ω → T} {V : Ω → U}
    (h : AEFunctionOf W V μ) :
    AEFunctionOf (⟨X, W⟩ : Ω → S × T) (⟨X, V⟩ : Ω → S × U) μ := by
  obtain ⟨f, hf, hfW⟩ := h
  refine ⟨fun p => (p.1, f p.2), measurable_fst.prodMk (hf.comp measurable_snd), ?_⟩
  filter_upwards [hfW] with ω hω
  simp [hω]

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

/-- Entropy is invariant under pullback along a measure-preserving map — the entropy
companion of the displayed identity (2.2), which sits inside Definition 2.1's discussion
of the pullback convention.

Paper node: `Definition 2.1` -/
lemma entropy_comp_measurePreserving (hπ : MeasurePreserving π μΛ μΩ) (hX : Measurable X) :
    H[X ∘ π ; μΛ] = H[X ; μΩ] :=
  (identDistrib_comp_measurePreserving hπ hX).entropy_congr

/-- **Equation (2.2)**: mutual information is invariant under pullback along a
measure-preserving map.  The equation is displayed inside Definition 2.1, as the
justification of that definition's pullback convention.

Paper node: `Definition 2.1` -/
lemma mutualInfo_comp_measurePreserving (hπ : MeasurePreserving π μΛ μΩ)
    (hX : Measurable X) (hY : Measurable Y) :
    I[X ∘ π : Y ∘ π ; μΛ] = I[X : Y ; μΩ] := by
  have h : IdentDistrib (⟨X ∘ π, Y ∘ π⟩ : Λ → S × T) (⟨X, Y⟩ : Ω → S × T) μΛ μΩ :=
    identDistrib_comp_measurePreserving hπ (hX.prodMk hY)
  exact h.mutualInfo_eq

/-- Conditional entropy is invariant under pullback along a measure-preserving map — the
conditional-entropy companion of the displayed identity (2.2), which sits inside
Definition 2.1's discussion of the pullback convention.

`μΩ` needs no probability hypothesis of its own: it is the pushforward of `μΛ` along `π`.

Paper node: `Definition 2.1` -/
lemma condEntropy_comp_measurePreserving [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [IsProbabilityMeasure μΛ]
    (hπ : MeasurePreserving π μΛ μΩ) (hX : Measurable X) (hY : Measurable Y)
    [ShannonInformation.FiniteEntropyOf X μΩ] [ShannonInformation.FiniteEntropyOf Y μΩ] :
    H[X ∘ π | Y ∘ π ; μΛ] = H[X | Y ; μΩ] := by
  haveI : IsProbabilityMeasure μΩ :=
    hπ.map_eq ▸ Measure.isProbabilityMeasure_map hπ.measurable.aemeasurable
  haveI : ShannonInformation.FiniteEntropyOf (X ∘ π) μΛ :=
    ShannonInformation.finiteEntropyOf_pullback hπ hX
  haveI : ShannonInformation.FiniteEntropyOf (Y ∘ π) μΛ :=
    ShannonInformation.finiteEntropyOf_pullback hπ hY
  have h : IdentDistrib (⟨X ∘ π, Y ∘ π⟩ : Λ → S × T) (⟨X, Y⟩ : Ω → S × T) μΛ μΩ :=
    identDistrib_comp_measurePreserving hπ (hX.prodMk hY)
  exact ShannonInformation.IdentDistrib.condEntropy_eq (hX.comp hπ.measurable)
    (hY.comp hπ.measurable) hX hY h

end Pullback

/-! ## Definition 2.2 — the nonempty power set `P⁺ S` -/

/-- `Finset I` is finite when `I` is.  Mathlib carries `Finset.fintype` for `[Fintype I]`
but no `Finite (Finset I)` instance at this pin, and `[Finite I]` does not yield
`Fintype I` by instance search (`Fintype.ofFinite` is noncomputable and deliberately not
an instance), so this is a genuine gap rather than an inference detail. -/
instance instFiniteFinset {I : Type u} [Finite I] : Finite (Finset I) :=
  Finite.of_injective (fun s : Finset I => (s : Set I)) Finset.coe_injective

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

/-- `P⁺ I` is finite whenever `I` is — no `Fintype`/`DecidableEq` data needed.  Definition
3.1 asks for a *finite* family of random variables, so `[Finite I]` is carried by every
model in this development, and this instance is what makes every subfamily `F ⊆ P⁺ I`
finite (`Set.toFinite`), which is what the sums of (3.1)–(3.2) and the joint variables
`Y_F` of Definition 3.4 range over. -/
instance instFinite [Finite I] : Finite (PPlus I) := Subtype.finite

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
/-- Interaction information is symmetric in its first two arguments — half of the remark
displayed with Definition 2.3 that `I (X; Y; Z)` is invariant under permutation of its
arguments.

Paper node: `Definition 2.3` -/
lemma interactionInfo_comm (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U)
    (μ : Measure Ω) : interactionInfo X Y Z μ = interactionInfo Y X Z μ := by
  rw [interactionInfo, interactionInfo, mutualInfo_comm hX hY, condMutualInfo_comm hX hY]

/-- Interaction information is symmetric in its last two arguments — the second half of
Definition 2.3's remark that `I (X; Y; Z)` is invariant under permutation of its
arguments.  Together with `interactionInfo_comm` this generates the full symmetric group
on the three arguments.

Paper node: `Definition 2.3` -/
lemma interactionInfo_swap [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [ShannonInformation.FiniteEntropyOf X μ] [ShannonInformation.FiniteEntropyOf Y μ]
    [ShannonInformation.FiniteEntropyOf Z μ] :
    interactionInfo X Y Z μ = interactionInfo X Z Y μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [interactionInfo, mutualInfo_def]
  haveI : ShannonInformation.FiniteEntropyOf (⟨Y, Z⟩ : Ω → T × U) μ :=
    ShannonInformation.finiteEntropyOf_pair hY hZ
  have hcond : H[X | ⟨Z, Y⟩ ; μ] = H[X | ⟨Y, Z⟩ ; μ] :=
    ShannonInformation.condEntropy_of_injective' μ hX (hY.prodMk hZ) Prod.swap
      Prod.swap_injective (hZ.prodMk hY)
  rw [interactionInfo, interactionInfo,
    ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy hX hY μ,
    ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy hX hZ μ,
    ShannonInformation.condMutualInfo_eq' hX hY hZ μ,
    ShannonInformation.condMutualInfo_eq' hX hZ hY μ, hcond]
  ring

end Interaction

/-! ## Definition 2.4 — the Giry σ-algebra -/

/-- **`G (Ω)`**: the space of *probability* measures on `Ω`, equipped with the smallest
σ-algebra making every evaluation map `P ↦ P E` (for `E ⊆ Ω` measurable) measurable.  This
is Mathlib's σ-algebra on `MeasureTheory.ProbabilityMeasure Ω`, inherited from
`MeasureTheory.Measure.instMeasurableSpace` by comap along the coercion; the alias exists
only to name the paper's `G (Ω)` and is not a new definition.

The carrier is `ProbabilityMeasure Ω`, not `Measure Ω`: Definition 2.4 equips *the space
of probability measures* on `Ω`, and the proof of Proposition 2.5 reads "each such
probability distribution is a Dirac measure in `G (Ω)`", which is a statement about a
point of that space.

Paper node: `Definition 2.4` -/
abbrev GiryMeasurableSpace (Ω : Type*) [MeasurableSpace Ω] :
    MeasurableSpace (ProbabilityMeasure Ω) :=
  inferInstance

/-! ## An auxiliary: conditioning on a constant -/

/-- Conditioning on a variable whose range is a subsingleton leaves entropy unchanged:
such a variable is literally constant, and mutual information with a constant vanishes.

Not a paper statement — the paper never says it, because on paper "conditioning on nothing"
needs no lemma.  In Lean it does: Definition 3.4's `Y_⊋B` is a dependent product over a
possibly *empty* index family, and at the maximal `B` it is exactly such a subsingleton, so
`χ_L`'s top term is an unconditioned entropy.  The vendored library has `entropy_const` and
`mutualInfo_const` but no `condEntropy_const`; this is the missing form.  It is generic
enough to belong in `ShannonInformation/API.lean` if a second client ever wants it. -/
lemma condEntropy_eq_entropy_of_subsingleton {Ω S T : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSpace T] [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [Subsingleton T] [Nonempty T]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → S} (hX : Measurable X)
    [ShannonInformation.FiniteEntropyOf X μ]
    (Y : Ω → T) : H[X | Y ; μ] = H[X ; μ] := by
  have hY : Y = fun _ => (Classical.arbitrary T) := funext fun _ => Subsingleton.elim _ _
  subst hY
  have h0 := ShannonInformation.mutualInfo_const (μ := μ) hX (Classical.arbitrary T)
  rw [ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy hX measurable_const μ] at h0
  linarith

/-! ## Proposition 2.5 — the determinism bridge -/

section Prop25

variable {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  {μ : Measure Ω} {X : Ω → S} {Y : Ω → T}

/-- An a.e. function of `X` has no more entropy than `X` — the data-processing inequality
in the form §4 uses it. -/
lemma entropy_le_of_aeFunctionOf [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) [ShannonInformation.FiniteEntropyOf X μ] (h : AEFunctionOf X Y μ) :
    H[Y ; μ] ≤ H[X ; μ] := by
  obtain ⟨f, hf, hfX⟩ := h
  have hae : Y =ᵐ[μ] f ∘ X := hfX
  rw [entropy_congr hae]
  exact ShannonInformation.entropy_comp_le μ hX f

omit [Countable T] in
/-- Adjoining an a.e. function of `X` to `X` does not change the joint entropy.

No finiteness hypothesis: `ProbabilityTheory.entropy_prod_comp` is an injective-relabelling
identity and carries none. -/
lemma entropy_pair_of_aeFunctionOf [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (h : AEFunctionOf X Y μ) :
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
    (hX : Measurable X) (hY : Measurable Y) [ShannonInformation.FiniteEntropyOf X μ]
    [ShannonInformation.FiniteEntropyOf Y μ]
    (h : AEFunctionOf X Y μ) : H[Y | X ; μ] = 0 := by
  rw [ShannonInformation.chain_rule'' μ hY hX, entropy_comm hY hX,
    entropy_pair_of_aeFunctionOf hX h, sub_self]

/-- **Proposition 2.5** (the determinism bridge).  On a countable discrete probability
space, a variable of zero conditional entropy given `X` is almost everywhere a measurable
function of `X`.

This is what turns every entropy inequality of §4 into the paper's "is a function of"
conclusions (Lemma 4.5, Corollary 4.6, Theorem 4.9, Theorem 4.15).

The hypotheses are now the paper's own: countable discrete ranges with finite entropy.  (Up
to 2026-08-17 they were `FiniteRange X`/`FiniteRange Y` — the `dd:finite-range` narrowing —
and `Countable R_Y` was `omit`ted because the finite-range proof did not need it.  Both
changed in the same edit: the `tsum` form of the conditional entropy and
`ShannonInformation.const_of_nonpos_entropy` both require `Countable R_Y`, and the paper
assumes it, so the statement is now neither stronger nor weaker than the printed one.)

Paper node: `Proposition 2.5` -/
theorem aeFunctionOf_of_condEntropy_eq_zero [Countable Ω] [MeasurableSingletonClass Ω]
    [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    [ShannonInformation.FiniteEntropyOf X μ] [ShannonInformation.FiniteEntropyOf Y μ]
    (h : H[Y | X ; μ] = 0) : AEFunctionOf X Y μ := by
  classical
  have : Nonempty T := Nonempty.map Y μ.nonempty_of_neZero
  have hsummable : Summable fun x : S ↦ ((μ.map X).real {x}) * H[Y | X ← x; μ] :=
    ShannonInformation.summable_measureReal_mul_entropy_cond hY hX μ
  have hnonneg : ∀ x : S, 0 ≤ ((μ.map X).real {x}) * H[Y | X ← x; μ] := fun x ↦
    mul_nonneg measureReal_nonneg (entropy_nonneg _ _)
  have hsum : ∑' x : S, ((μ.map X).real {x}) * H[Y | X ← x; μ] = 0 := by
    rw [← ShannonInformation.condEntropy_eq_tsum hY hX μ, h]
  have hterm : ∀ x : S, ((μ.map X).real {x}) * H[Y | X ← x; μ] = 0 := fun x ↦
    le_antisymm (hsum ▸ hsummable.le_tsum x fun j _ ↦ hnonneg j) (hnonneg x)
  have key : ∀ x : S, μ (X ⁻¹' {x}) ≠ 0 → ∃ t : T, (μ[|X ⁻¹' {x}]).real (Y ⁻¹' {t}) = 1 := by
    intro x hx
    haveI : IsProbabilityMeasure (μ[|X ⁻¹' {x}]) := cond_isProbabilityMeasure hx
    haveI : ShannonInformation.FiniteEntropyOf Y (μ[|X ⁻¹' {x}]) :=
      ShannonInformation.finiteEntropyOf_cond (μ := μ) (Z := X) hY x
    have hmass : ((μ.map X).real {x}) ≠ 0 := by
      rw [map_measureReal_apply hX (MeasurableSet.singleton x)]
      exact (measureReal_ne_zero_iff (measure_ne_top μ _)).2 hx
    refine ShannonInformation.const_of_nonpos_entropy hY (le_of_eq ?_)
    exact (mul_eq_zero.1 (hterm x)).resolve_left hmass
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
    [ShannonInformation.FiniteEntropyOf X μ] [ShannonInformation.FiniteEntropyOf Y μ] :
    AEFunctionOf X Y μ ↔ H[Y | X ; μ] = 0 :=
  ⟨condEntropy_eq_zero_of_aeFunctionOf hX hY, aeFunctionOf_of_condEntropy_eq_zero hX hY⟩

end Prop25

/-! ## Conditional entropy under a.e. functional dependence

Generic consequences of Proposition 2.5 and the chain rule, with no paper node of their
own.  They are what §4 and §5 use to compare two conditionings of the same variable. -/

section CondEntropyComparison

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U]
  [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
  {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
  {X : Ω → S} {W : Ω → T} {V : Ω → U}

/-- **Conditioning on either of two mutually a.e.-functional variables is the same.**
`H (X | W) = H (X | V)` when each of `V`, `W` is almost everywhere a function of the other.

Proved from the chain rule and `entropy_le_of_aeFunctionOf` in both directions, which is
why it needs no injectivity or relabelling data. -/
lemma condEntropy_congr_of_aeFunctionOf (hX : Measurable X) (hW : Measurable W)
    (hV : Measurable V)
    [hfX : ShannonInformation.FiniteEntropyOf X μ] [hfW : ShannonInformation.FiniteEntropyOf W μ]
    [hfV : ShannonInformation.FiniteEntropyOf V μ]
    (h : AEFunctionOf W V μ) (h' : AEFunctionOf V W μ) : H[X | W ; μ] = H[X | V ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  haveI := ShannonInformation.finiteEntropyOf_pair (μ := μ) hX hW
  haveI := ShannonInformation.finiteEntropyOf_pair (μ := μ) hX hV
  have hWV : H[W ; μ] = H[V ; μ] :=
    le_antisymm (entropy_le_of_aeFunctionOf hV h') (entropy_le_of_aeFunctionOf hW h)
  have hpair : H[(⟨X, W⟩ : Ω → S × T) ; μ] = H[(⟨X, V⟩ : Ω → S × U) ; μ] :=
    le_antisymm (entropy_le_of_aeFunctionOf (hX.prodMk hV) (AEFunctionOf.prodMk_left h'))
      (entropy_le_of_aeFunctionOf (hX.prodMk hW) (AEFunctionOf.prodMk_left h))
  rw [ShannonInformation.chain_rule'' μ hX hW, ShannonInformation.chain_rule'' μ hX hV,
    hWV, hpair]

/-- **Conditioning on more can only help**: if `V` is a.e. a function of `W`, then
`H (X | W) ≤ H (X | V)`.  Submodularity gives `H (X | W, V) ≤ H (X | V)`, and
`condEntropy_congr_of_aeFunctionOf` identifies `H (X | W, V)` with `H (X | W)`. -/
lemma condEntropy_le_condEntropy_of_aeFunctionOf (hX : Measurable X) (hW : Measurable W)
    (hV : Measurable V)
    [hfX : ShannonInformation.FiniteEntropyOf X μ] [hfW : ShannonInformation.FiniteEntropyOf W μ]
    [hfV : ShannonInformation.FiniteEntropyOf V μ]
    (h : AEFunctionOf W V μ) : H[X | W ; μ] ≤ H[X | V ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  haveI := ShannonInformation.finiteEntropyOf_pair (μ := μ) hW hV
  have e : H[X | W ; μ] = H[X | (⟨W, V⟩ : Ω → T × U) ; μ] :=
    condEntropy_congr_of_aeFunctionOf hX hW (hW.prodMk hV)
      (aeFunctionOf_self.prodMk h)
      (AEFunctionOf.of_functionOf (functionOf_comp (f := Prod.fst) measurable_fst))
  rw [e]
  exact ShannonInformation.entropy_submodular hX hW hV

/-- **Data processing for the conditioned variable**: an a.e. function of `X` carries no
more conditional entropy than `X` does, `H (V | W) ≤ H (X | W)`.  The conditional analogue
of `entropy_le_of_aeFunctionOf`; (5.23) is its only client here. -/
lemma condEntropy_le_of_aeFunctionOf (hX : Measurable X) (hV : Measurable V)
    (hW : Measurable W)
    [hfX : ShannonInformation.FiniteEntropyOf X μ] [hfV : ShannonInformation.FiniteEntropyOf V μ]
    [hfW : ShannonInformation.FiniteEntropyOf W μ]
    (h : AEFunctionOf X V μ) : H[V | W ; μ] ≤ H[X | W ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  haveI := ShannonInformation.finiteEntropyOf_pair (μ := μ) hX hW
  haveI := ShannonInformation.finiteEntropyOf_pair (μ := μ) hV hW
  have hfst : AEFunctionOf (⟨X, W⟩ : Ω → S × T) X μ :=
    AEFunctionOf.of_functionOf ⟨Prod.fst, measurable_fst, fun _ => rfl⟩
  have hsnd : AEFunctionOf (⟨X, W⟩ : Ω → S × T) W μ :=
    AEFunctionOf.of_functionOf ⟨Prod.snd, measurable_snd, fun _ => rfl⟩
  have hle : H[(⟨V, W⟩ : Ω → U × T) ; μ] ≤ H[(⟨X, W⟩ : Ω → S × T) ; μ] :=
    entropy_le_of_aeFunctionOf (hX.prodMk hW) ((hfst.trans h).prodMk hsnd)
  rw [ShannonInformation.chain_rule'' μ hV hW, ShannonInformation.chain_rule'' μ hX hW]
  linarith

end CondEntropyComparison

/-! ## Auxiliaries: variables with subsingleton *range*

The companions of `condEntropy_eq_entropy_of_subsingleton`, which says what happens when
the *conditioning* variable has subsingleton range.  These say what happens when the
*conditioned* variable does: Example 4.1's guarded-subtype encoding makes "let `Y_A` be
constant" into "the range of `Y_A` is a one-point type", and both scores then need every
such term to drop out. -/

/-- A random variable into a subsingleton has zero entropy: it is literally constant. -/
lemma entropy_eq_zero_of_subsingleton {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Subsingleton S] [Nonempty S]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] (X : Ω → S) : H[X ; μ] = 0 := by
  have hX : X = fun _ => Classical.arbitrary S := funext fun _ => Subsingleton.elim _ _
  rw [hX, entropy_const]

/-- A random variable into a subsingleton has zero conditional entropy given anything. -/
lemma condEntropy_eq_zero_of_subsingleton {Ω S T : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSpace T] [Countable S] [MeasurableSingletonClass S]
    [Subsingleton S] [Nonempty S] [Countable T] [MeasurableSingletonClass T]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T}
    (hX : Measurable X) (hY : Measurable Y)
    [ShannonInformation.FiniteEntropyOf X μ] [ShannonInformation.FiniteEntropyOf Y μ] :
    H[X | Y ; μ] = 0 :=
  condEntropy_eq_zero_of_aeFunctionOf hY hX
    ⟨fun _ => Classical.arbitrary S, measurable_const,
      Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _⟩

/-- **Joint independence is automatic over a subsingleton index type.**  The defining
identity of `iIndepFun` quantifies over finite subfamilies, and over a subsingleton index
type the only ones are `∅` and a singleton, where it reads `μ univ = 1` and `μ s = μ s`.

The companion of the two lemmas above at the level of an index *family* rather than a
range: it is what makes Example 4.4's joint-independence hypothesis discharge on a
`Unit`-indexed witness, where `P⁺Unit` has the single element `{()}`.  Nothing about it is
specific to this paper; it is stated for a bare family of measurable functions and would
belong in `ShannonInformation/API.lean`, or upstream of it, if a second client wanted it. -/
lemma iIndepFun_of_subsingleton {ι : Type*} [Subsingleton ι] {Ω : Type*} [MeasurableSpace Ω]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)] (f : ∀ i, Ω → β i) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : iIndepFun f μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets _
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · obtain rfl : s = {a} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun x _ => Subsingleton.elim x a⟩
    simp

end Condensation
