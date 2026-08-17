import Condensation.Model
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso

/-!
# Condensation §3.1 — morphisms of random variable models

This file is §3.1 of Eisenstat, *Condensation: A Theory of Concepts*:

* Definition 3.5 — a **morphism** `(π, ι, (f_j)_{j∈J}) : (Ω, (X_i)_{i∈I}) → (Λ, (Y_j)_{j∈J})`
  (`RVModel.Hom`), equation (3.10);
* Definition 3.6 — the **composite** (3.13) (`RVModel.Hom.comp`) and the identity morphism
  (3.16) (`RVModel.Hom.id`);
* **Proposition 3.7** — random variable models and morphisms form a category
  (`RVModelObj.instCategory`);
* **Proposition 3.8** — the characterization of the isomorphisms (`RVModel.Hom.isIso_iff`);
* Definition 3.9 — **equality almost everywhere** of morphisms (`RVModel.Hom.AEEq`);
* Definition 3.10 — **equivalence** of random variable models (`RVModel.IsEquivalence`,
  `RVModel.Equivalent`), together with the "laid out" characterization the paper gives
  immediately afterwards (`RVModel.isEquivalence_ofSameIndex_iff`);
* **Proposition 3.11** — a.e. equality is a congruence for composition
  (`RVModel.Hom.aeEq_equivalence`, `RVModel.Hom.comp_aeEq_congr`);
* **Proposition 3.12** — equivalence of random variable models is an equivalence relation
  (`RVModelObj.equivalent_equivalence`).

## Modeling decisions

* `dd:category` — Proposition 3.7 is a `CategoryTheory.Category` instance on the bundled
  type `RVModelObj` of random variable models at fixed universes (the index type is a
  field, so that a morphism may change it, which Definition 3.5 requires); Proposition 3.8
  uses `CategoryTheory.IsIso`; Definition 3.9's a.e. equality is a `Setoid` on hom-types,
  and 3.10–3.12 are stated over it.  No `Bicategory`: the paper names the 2-category and
  declines to use it.
* `dd:pullback` — the pullback `π^* Y_j` is plain composition `N.X j ∘ φ.π`, so
  Definition 3.5's condition is stated directly as `N.X j (π ω) = f j (M.X (ι j) ω)`
  a.e. on `Ω`.
* Definition 3.5's `f_j` is a **function**, not a measurable function: the paper's own
  remark is that "the function `f_j` is automatically measurable, since these random
  variables have countable and discrete range".  So `RVModel.Hom` carries no measurability
  field for `f`, and `RVModel.Hom.measurable_f` supplies the measurability as a lemma via
  `measurable_of_countable`.  This is the paper's reading; adding the field would be a
  (harmless but unfaithful) strengthening of the data.
* Definition 3.5's condition is stated in the pointwise-in-`j` form
  `∀ j, ∀ᵐ ω, …`.  The paper remarks that this is equivalent to the form with a single
  full-measure set, `∀ᵐ ω, ∀ j, …`; that is `RVModel.Hom.eq_ae_all`, which holds because
  `J` is countable (Definition 3.1's index sets are finite).

## Position in the import graph

This file imports `Condensation.Model` and two `Mathlib.CategoryTheory.*` modules, and
nothing else of the library.  In particular it does **not** import
`Condensation.Examples`: Proposition 4.7 is stated over Definition 3.10, so
`Condensation.Perfect` imports this file, and `Condensation.Examples` imports
`Condensation.Perfect`.  The concrete morphisms and category objects that exercise §3.1 —
`coinCollapse`, `coinObj`, `twoCoinObj`, `coinCollapseArrow`, `pairCoinModel`,
`pairCoinHom₁`, `pairCoinHom₂` — therefore live in the "§3.1 witnesses" section at the end
of `Condensation/Examples.lean`, the library's terminal non-vacuity file.
-/

universe u v w u₁ v₁ w₁ u₂ v₂ w₂

namespace Condensation

-- `Real` is deliberately *not* opened: it would make `π` notation for `Real.pi`, which
-- collides with the field name `π` of `RVModel.Hom` in structure-instance syntax.
open MeasureTheory ProbabilityTheory

/-! ## Definition 3.5 — morphisms of random variable models -/

/-- A **morphism of random variable models**
`(π, ι, (f_j)_{j∈J}) : (Ω, (X_i)_{i∈I}) → (Λ, (Y_j)_{j∈J})`, equation (3.10): a
probability-preserving map `π : Ω → Λ`, a function `ι : J → I`, and for each `j ∈ J` a
function `f_j` from the range of `X_{ι(j)}` to the range of `Y_j`, subject to
`Y_j = f_j (X_{ι(j)})` almost everywhere on `Ω`.

Note the direction of `ι`: it runs `J → I`, from the *target*'s index set to the
*source*'s.  This is what lets the source's variables "make more distinctions than" the
target's, as the paragraph before Definition 3.5 explains.

`Y_j` lives on `Λ` and `X_{ι(j)}` on `Ω`, so the displayed condition is read through the
pullback convention (2.2) (`dd:pullback`): the field says
`(π^* Y_j) ω = f_j (X_{ι(j)} ω)` for `P`-almost every `ω ∈ Ω`.  `Hom.pullback_eq` states
exactly the paper's `π^* Y_j = f_j (X_{ι(j)})`.

No measurability field for `f_j`: the paper observes that `f_j` is automatically
measurable because the ranges are countable and discrete (`Hom.measurable_f`), so it is
plain function data.

*(Paper's parenthetical remark, formalized nowhere because it is a negative claim about a
different structure: the map `π` of a latent variable model `((Λ, Y), π)` is **not**
necessarily a morphism of random variable models, since each `X_i` may depend
nontrivially on several latent variables.  Note also that a latent model's `π` runs
`Λ → Ω`, the opposite direction to a morphism's.)*

Paper node: `Definition 3.5` -/
structure RVModel.Hom {I : Type w} [Finite I] {J : Type w₁} [Finite J]
    (M : RVModel.{u, v, w} I) (N : RVModel.{u₁, v₁, w₁} J) where
  /-- The probability-preserving map `π : Ω → Λ`. -/
  π : M.Ω → N.Ω
  /-- `π` is probability preserving. -/
  π_pres : MeasurePreserving π M.P N.P
  /-- The index map `ι : J → I`. -/
  ι : J → I
  /-- `f_j`, a function from the range of `X_{ι(j)}` to the range of `Y_j`. -/
  f : ∀ j, M.R (ι j) → N.R j
  /-- `Y_j = f_j (X_{ι(j)})` almost everywhere on `Ω`, read through the pullback. -/
  eq_ae : ∀ j, ∀ᵐ ω ∂M.P, N.X j (π ω) = f j (M.X (ι j) ω)

namespace RVModel

variable {I : Type w} {J : Type w₁} {K : Type w₂} [Finite I] [Finite J] [Finite K]
  {L : RVModel.{u, v, w} I} {M : RVModel.{u, v, w} I} {N : RVModel.{u₁, v₁, w₁} J}
  {P : RVModel.{u₂, v₂, w₂} K}

namespace Hom

/-- Definition 3.5's `f_j` is automatically measurable: the paper's own remark, valid
because the ranges are countable and discrete. -/
lemma measurable_f (φ : Hom M N) (j : J) : Measurable (φ.f j) :=
  measurable_of_countable _

/-- **Equation of Definition 3.5 with the pullback made explicit**: `π^* Y_j`, as a random
variable on `Ω`, is almost everywhere `f_j (X_{ι(j)})`. -/
lemma pullback_eq (φ : Hom M N) (j : J) :
    (N.X j ∘ φ.π) =ᵐ[M.P] (φ.f j ∘ M.X (φ.ι j)) := φ.eq_ae j

/-- Definition 3.5's condition, phrased with §2's vocabulary: the pullback `π^* Y_j` is
almost everywhere a function of `X_{ι(j)}`. -/
lemma aeFunctionOf (φ : Hom M N) (j : J) :
    AEFunctionOf (M.X (φ.ι j)) (N.X j ∘ φ.π) M.P :=
  ⟨φ.f j, φ.measurable_f j, φ.eq_ae j⟩

/-- The paper's remark after Definition 3.5: the pointwise-in-`j` condition is equivalent
to the condition that on a *single* set of full measure in `Ω` we have
`Y_j = f_j (X_{ι(j)})` for all `j ∈ J`.  The two agree because `J` is countable — every
index set of Definition 3.1 is finite. -/
lemma eq_ae_all (φ : Hom M N) :
    ∀ᵐ ω ∂M.P, ∀ j, N.X j (φ.π ω) = φ.f j (M.X (φ.ι j) ω) :=
  (ae_all_iff (p := fun ω j => N.X j (φ.π ω) = φ.f j (M.X (φ.ι j) ω))).2 φ.eq_ae

/-! ## Definition 3.6 — composition, and the identity morphism (3.16) -/

/-- The **composite** of two morphisms, equation (3.13):
`(ρ ∘ π, ι ∘ ν, (g_k ∘ f_{ν(k)})_{k∈K})`.

The index maps compose the other way round from the underlying maps: with `ι : J → I` and
`ν : K → J`, the composite's index map is `ι ∘ ν : K → I`.

Well-definedness is the paper's (3.14)–(3.15): `ρ^* Z_k = g_k (Y_{ν(k)})` almost
everywhere on `Λ`, and `π` is probability preserving, so that identity transports to a
full-measure subset of `Ω`, where it may be combined with `π^* Y_{ν(k)} = f_{ν(k)}
(X_{ι(ν(k))})`.

The argument order is Lean's diagrammatic one: `φ.comp ψ` is the paper's `ψ ∘ φ`.

Paper node: `Definition 3.6` -/
def comp (φ : Hom M N) (ψ : Hom N P) : Hom M P where
  π := ψ.π ∘ φ.π
  π_pres := ψ.π_pres.comp φ.π_pres
  ι := φ.ι ∘ ψ.ι
  f := fun k => ψ.f k ∘ φ.f (ψ.ι k)
  eq_ae := fun k => by
    filter_upwards [φ.π_pres.quasiMeasurePreserving.ae (ψ.eq_ae k), φ.eq_ae (ψ.ι k)]
      with ω hω hω'
    simp only [Function.comp_apply] at hω hω' ⊢
    rw [hω, hω']

/-- The **identity morphism** `(id_Ω, id_I, (id_{R X_i})_{i∈I})` of equation (3.16). -/
def id (M : RVModel.{u, v, w} I) : Hom M M where
  π := _root_.id
  π_pres := MeasurePreserving.id _
  ι := _root_.id
  f := fun _ => _root_.id
  eq_ae := fun _ => Filter.Eventually.of_forall fun _ => rfl

@[simp] lemma comp_π (φ : Hom M N) (ψ : Hom N P) : (φ.comp ψ).π = ψ.π ∘ φ.π := rfl

@[simp] lemma comp_ι (φ : Hom M N) (ψ : Hom N P) : (φ.comp ψ).ι = φ.ι ∘ ψ.ι := rfl

@[simp] lemma id_π (M : RVModel.{u, v, w} I) : (Hom.id M).π = _root_.id := rfl

@[simp] lemma id_ι (M : RVModel.{u, v, w} I) : (Hom.id M).ι = _root_.id := rfl

/-- Extensionality for morphisms.  Only `π`, `ι` and `f` matter: `π_pres` and `eq_ae` are
`Prop`-valued and therefore proof-irrelevant, so a hom-type is a `Subsingleton` in those
fields.  The hypothesis on `f` is a `HEq` because `f`'s type depends on `ι`. -/
lemma ext {φ ψ : Hom M N} (hπ : φ.π = ψ.π) (hι : φ.ι = ψ.ι) (hf : HEq φ.f ψ.f) : φ = ψ := by
  obtain ⟨π₁, hp₁, ι₁, f₁, e₁⟩ := φ
  obtain ⟨π₂, hp₂, ι₂, f₂, e₂⟩ := ψ
  simp only at hπ hι hf
  subst hπ
  subst hι
  simp only [heq_eq_eq] at hf
  subst hf
  rfl

end Hom

end RVModel

/-! ## Proposition 3.7 — random variable models form a category

The objects are random variable models with their index type as a *field*: Definition 3.5
lets a morphism change the index set, so the index type cannot be a parameter of the
object type.  Universes are fixed, as they must be for a `Category` instance
(`dd:category`, `dd:bundled-model`). -/

/-- A random variable model bundled with its index type — the object type of the category
of Proposition 3.7.  Definition 3.1's finiteness of the index set travels along as an
instance field. -/
structure RVModelObj where
  /-- The index set `I`. -/
  I : Type w
  [finI : Finite I]
  /-- The model `(Ω, (X_i)_{i ∈ I})`. -/
  M : RVModel.{u, v, w} I

attribute [instance] RVModelObj.finI

namespace RVModelObj

/-- **Proposition 3.7**: random variable models and morphisms form a category.

The identity is (3.16) and composition is (3.13); the unit laws and associativity (3.17)–
(3.20) hold on the nose, because they are the corresponding laws for composition of the
three components, and the two remaining fields of `RVModel.Hom` are `Prop`-valued.

Paper node: `Proposition 3.7` -/
instance instCategory : CategoryTheory.Category.{max u v w} RVModelObj.{u, v, w} where
  Hom A B := RVModel.Hom A.M B.M
  id A := RVModel.Hom.id A.M
  comp φ ψ := RVModel.Hom.comp φ ψ
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

lemma id_eq (A : RVModelObj.{u, v, w}) :
    CategoryTheory.CategoryStruct.id A = RVModel.Hom.id A.M := rfl

lemma comp_eq {A B C : RVModelObj.{u, v, w}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    CategoryTheory.CategoryStruct.comp φ ψ = RVModel.Hom.comp φ ψ := rfl

end RVModelObj

namespace RVModel

variable {I : Type w} {J : Type w₁} {K : Type w₂} [Finite I] [Finite J] [Finite K]

/-! ## Proposition 3.8 — the isomorphisms -/

namespace Hom

/-- An **isomorphism of measurable spaces** is Mathlib's `MeasurableEquiv`: a measurable
bijection with measurable inverse.  This spells out what Proposition 3.8's phrase means
for a bare function. -/
def IsMeasurableIso {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (g : α → β) :
    Prop := ∃ e : α ≃ᵐ β, ⇑e = g

/-- On countable discrete ranges a bijection is automatically an isomorphism of measurable
spaces, both it and its inverse being measurable by `measurable_of_countable`. -/
lemma isMeasurableIso_of_bijective {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] [Countable β] [MeasurableSingletonClass β]
    {g : α → β} (hg : Function.Bijective g) : IsMeasurableIso g :=
  ⟨⟨Equiv.ofBijective g hg, measurable_of_countable _, measurable_of_countable _⟩, rfl⟩

/-! ### Two transport lemmas for the dependent `f`-component

`Hom.f`'s type depends on `Hom.ι`, so an equality of morphisms gives only a `HEq` of the
`f`-components.  These two lemmas are the only places that friction is handled: the first
turns such a `HEq` into pointwise bijectivity, the second builds one from a pointwise
description by `cast`.  Both work by `subst`ing the index-map equation, which is legal
exactly because the index map is a variable there. -/

private lemma bijective_of_heq_id {ι : Type*} {R : ι → Type*} {κ : ι → ι}
    (hκ : κ = _root_.id) (g : ∀ i, R (κ i) → R i)
    (hg : HEq g (fun i => (_root_.id : R i → R i))) (i : ι) : Function.Bijective (g i) := by
  subst hκ
  rw [eq_of_heq hg]
  exact Function.bijective_id

private lemma heq_id_family {ι : Type*} {R : ι → Type*} {κ : ι → ι} (hκ : κ = _root_.id)
    (g : ∀ i, R (κ i) → R i)
    (hg : ∀ i (x : R (κ i)) (h : κ i = i), g i x = cast (congrArg R h) x) :
    HEq g (fun i => (_root_.id : R i → R i)) := by
  subst hκ
  exact heq_of_eq (funext fun i => funext fun x => hg i x rfl)

/-- The `f`-component of a morphism known to be the identity, as a `HEq`. -/
private lemma f_heq_id {M : RVModel.{u, v, w} I} (χ : Hom M M) (h : χ = Hom.id M) :
    HEq χ.f (fun i => (_root_.id : M.R i → M.R i)) := by
  subst h; rfl

/-- Transport of a variable along an equality of its index. -/
private lemma cast_X {M : RVModel.{u, v, w} I} {i i' : I} (h : i' = i) (ω : M.Ω) :
    cast (congrArg M.R h) (M.X i' ω) = M.X i ω := by
  subst h; rfl

/-- The inverse triple's `f`-component composes back to a cast — the step of (3.23) that
crosses the index bijection.  Stated with the index equality `q` universally quantified so
that it can be `subst`ed. -/
private lemma f_comp_symm_cast {M : RVModel.{u, v, w} I} {N : RVModel.{u₁, v₁, w₁} J}
    (φ : Hom M N) (ef : ∀ j, M.R (φ.ι j) ≃ᵐ N.R j) (hef : ∀ j, ⇑(ef j) = φ.f j) :
    ∀ (j j' : J) (q : j' = j) (y : N.R j'),
      φ.f j (cast (congrArg M.R (congrArg φ.ι q)) ((ef j').symm y)) = cast (congrArg N.R q) y := by
  intro j j' q y
  subst q
  show φ.f j' ((ef j').symm y) = y
  rw [← hef j']
  exact (ef j').apply_symm_apply y

/-- **Proposition 3.8**: a morphism of random variable models
`(π, ι, (f_j)_{j∈J}) : (Ω, (X_i)_{i∈I}) → (Λ, (Y_j)_{j∈J})` is an isomorphism if and only
if `π` is an isomorphism of measurable spaces, `ι` is a bijection, and for every `j ∈ J`
the map `f_j` is an isomorphism of measurable spaces.

"Isomorphism of measurable spaces" is `Hom.IsMeasurableIso`, i.e. Mathlib's
`MeasurableEquiv`.  The forward direction reads the three components off the two
identities `φ ≫ φ⁻¹ = 𝟙` and `φ⁻¹ ≫ φ = 𝟙`; because the `f`-component's type depends on
the index map, that reading goes through `bijective_of_heq_id`, and the bijectivity of
`f_j` itself is obtained by first showing the inverse morphism's `f`-component bijective
(it is injective by one identity and surjective by the other).

The reverse direction is the paper's (3.22)–(3.23): the candidate inverse is the triple
`(π⁻¹, ι⁻¹, (f_{ι⁻¹(i)}⁻¹)_{i∈I})`, and `π⁻¹` is probability preserving because `π` is and
is an isomorphism of measurable spaces (`MeasureTheory.MeasurePreserving.symm`).

Paper node: `Proposition 3.8` -/
theorem isIso_iff {A B : RVModelObj.{u, v, w}} (φ : A ⟶ B) :
    CategoryTheory.IsIso φ ↔
      IsMeasurableIso (RVModel.Hom.π φ) ∧ Function.Bijective (RVModel.Hom.ι φ) ∧
        ∀ j, IsMeasurableIso (RVModel.Hom.f φ j) := by
  constructor
  · -- "It is clear that isomorphisms have these properties."
    intro hiso
    obtain ⟨ψ, hc₁, hc₂⟩ := hiso.out
    have h₁ : Hom.comp φ ψ = Hom.id A.M := hc₁
    have h₂ : Hom.comp ψ φ = Hom.id B.M := hc₂
    have hπ₁ : ∀ ω, ψ.π (φ.π ω) = ω := fun ω => congrFun (congrArg Hom.π h₁) ω
    have hπ₂ : ∀ l, φ.π (ψ.π l) = l := fun l => congrFun (congrArg Hom.π h₂) l
    have hι₁ : Hom.ι φ ∘ Hom.ι ψ = _root_.id := congrArg Hom.ι h₁
    have hι₂ : Hom.ι ψ ∘ Hom.ι φ = _root_.id := congrArg Hom.ι h₂
    refine ⟨⟨⟨⟨φ.π, ψ.π, hπ₁, hπ₂⟩, φ.π_pres.measurable, ψ.π_pres.measurable⟩, rfl⟩,
      Function.bijective_iff_has_inverse.2 ⟨ψ.ι, congrFun hι₂, congrFun hι₁⟩, fun j => ?_⟩
    have hbA : ∀ i, Function.Bijective (ψ.f i ∘ φ.f (ψ.ι i)) :=
      bijective_of_heq_id (R := A.M.R) hι₁ (Hom.comp φ ψ).f (f_heq_id _ h₁)
    have hbB : ∀ k, Function.Bijective (φ.f k ∘ ψ.f (φ.ι k)) :=
      bijective_of_heq_id (R := B.M.R) hι₂ (Hom.comp ψ φ).f (f_heq_id _ h₂)
    have hsurj : Function.Surjective (ψ.f (φ.ι j)) := (hbA (φ.ι j)).2.of_comp
    have hinj : Function.Injective (ψ.f (φ.ι j)) := (hbB j).1.of_comp
    exact isMeasurableIso_of_bijective
      ((Function.Bijective.of_comp_iff (φ.f j) ⟨hinj, hsurj⟩).1 (hbB j))
  · -- The paper's (3.22)–(3.23).
    rintro ⟨⟨eπ, heπ⟩, hι, hfiso⟩
    choose ef hef using hfiso
    have hπpres : MeasurePreserving (⇑eπ) A.M.P B.M.P := by rw [heπ]; exact φ.π_pres
    have hsymm : MeasurePreserving (⇑eπ.symm) B.M.P A.M.P := MeasurePreserving.symm eπ hπpres
    set eι : B.I ≃ A.I := Equiv.ofBijective (Hom.ι φ) hι with heι
    have hri : ∀ i, Hom.ι φ (eι.symm i) = i := fun i => eι.apply_symm_apply i
    have hli : ∀ j, eι.symm (Hom.ι φ j) = j := fun j => eι.symm_apply_apply j
    have hpl : ∀ l, φ.π (eπ.symm l) = l := fun l => by rw [← heπ]; exact eπ.apply_symm_apply l
    have hlp : ∀ ω, eπ.symm (φ.π ω) = ω := fun ω => by rw [← heπ]; exact eπ.symm_apply_apply ω
    have hae : ∀ i, ∀ᵐ l ∂B.M.P, A.M.X i (eπ.symm l)
        = cast (congrArg A.M.R (hri i)) ((ef (eι.symm i)).symm (B.M.X (eι.symm i) l)) := by
      intro i
      filter_upwards [hsymm.quasiMeasurePreserving.ae (φ.eq_ae (eι.symm i))] with l hl
      rw [hpl l] at hl
      rw [hl, ← hef (eι.symm i), MeasurableEquiv.symm_apply_apply]
      exact (cast_X (hri i) _).symm
    refine ⟨⟨⟨eπ.symm, hsymm, eι.symm,
      fun i y => cast (congrArg A.M.R (hri i)) ((ef (eι.symm i)).symm y), hae⟩, ?_, ?_⟩⟩
    · refine Hom.ext (funext fun ω => hlp ω) (funext hri)
        (heq_id_family (R := A.M.R) (funext hri) _ fun i x h => ?_)
      show cast (congrArg A.M.R (hri i)) ((ef (eι.symm i)).symm (φ.f (eι.symm i) x))
        = cast (congrArg A.M.R h) x
      rw [← hef (eι.symm i), MeasurableEquiv.symm_apply_apply]
    · refine Hom.ext (funext fun l => hpl l) (funext hli)
        (heq_id_family (R := B.M.R) (funext hli) _ fun j y h => ?_)
      exact f_comp_symm_cast φ ef hef j _ (hli j) y

/-! ## Definition 3.9 — equality almost everywhere of morphisms -/

variable {M : RVModel.{u, v, w} I} {N : RVModel.{u₁, v₁, w₁} J} {P : RVModel.{u₂, v₂, w₂} K}

/-- Two morphisms `(π, ι, (f_j))` and `(ρ, ν, (g_j))` from `(Ω, X)` to `(Λ, Y)` are
**equal almost everywhere** when (1) `π` and `ρ` agree almost everywhere and (2) `ι = ν`.

There is deliberately **no** condition on `f` and `g`: the paper's remark after
Definition 3.9 is that they may genuinely differ.  Equation (3.24) gives
`f_j (X_{ι(j)}) = Y_j = g_j (X_{ι(j)})` almost everywhere on `Ω`, but that constrains `f_j`
and `g_j` only on the values `X_{ι(j)}` actually attains, and `X_{ι(j)}` need not be
surjective — so even an everywhere-valid version of (3.24) would not force `f_j = g_j`.

Paper node: `Definition 3.9` -/
def AEEq (φ ψ : Hom M N) : Prop :=
  (∀ᵐ ω ∂M.P, φ.π ω = ψ.π ω) ∧ φ.ι = ψ.ι

/-! ## Proposition 3.11 — a.e. equality is a congruence for composition -/

/-- **Proposition 3.11 (1)**: equality almost everywhere of morphisms of random variable
models is an equivalence relation.

Paper node: `Proposition 3.11` -/
theorem aeEq_equivalence : Equivalence (AEEq (M := M) (N := N)) where
  refl _ := ⟨Filter.Eventually.of_forall fun _ => rfl, rfl⟩
  symm h := ⟨h.1.mono fun _ hω => hω.symm, h.2.symm⟩
  trans h h' := ⟨by filter_upwards [h.1, h'.1] with ω hω hω' using hω.trans hω',
    h.2.trans h'.2⟩

/-- Definition 3.9 as a `Setoid` on each hom-type (`dd:category`). -/
instance instSetoid : Setoid (Hom M N) where
  r := AEEq
  iseqv := aeEq_equivalence

/-- **Proposition 3.11 (2)**: given morphisms `π, ρ : L → M` and `σ, τ : M → N` of (3.27)
with `π` equal almost everywhere to `ρ` and `σ` to `τ`, the composite `σ ∘ π` is equal
almost everywhere to `τ ∘ ρ`.

The proof is the paper's (3.28): if `π` and `ρ` agree on a full-measure `E ⊆ Ω` and `σ`
and `τ` on a full-measure `F ⊆ Λ`, then `E ∩ π⁻¹ F` has full measure — this is where `π`
being probability preserving is used — and on it
`σ (π ω) = τ (π ω) = τ (ρ ω)`.

Paper node: `Proposition 3.11` -/
theorem comp_aeEq_congr {φ ψ : Hom M N} {χ ξ : Hom N P}
    (h : AEEq φ ψ) (h' : AEEq χ ξ) : AEEq (φ.comp χ) (ψ.comp ξ) := by
  refine ⟨?_, by simp only [comp_ι, h.2, h'.2]⟩
  filter_upwards [h.1, φ.π_pres.quasiMeasurePreserving.ae h'.1] with ω hω hω'
  show χ.π (φ.π ω) = ξ.π (ψ.π ω)
  rw [hω', hω]

end Hom

/-! ## Definition 3.10 — equivalence of random variable models -/

variable {M : RVModel.{u, v, w} I} {N : RVModel.{u₁, v₁, w₁} J} {P : RVModel.{u₂, v₂, w₂} K}

/-- The pair `(φ, ψ)` is an **equivalence** between the random variable models `M` and `N`:
morphisms `φ : M → N` and `ψ : N → M` of (3.25)–(3.26) whose composites `ψ ∘ φ` and
`φ ∘ ψ` are equal almost everywhere to the identity morphisms on `M` and `N`
respectively.  Informally, an isomorphism almost everywhere.

Paper node: `Definition 3.10` -/
structure IsEquivalence (φ : Hom M N) (ψ : Hom N M) : Prop where
  /-- `ψ ∘ φ` is a.e. equal to the identity on `M`. -/
  comp_left : Hom.AEEq (φ.comp ψ) (Hom.id M)
  /-- `φ ∘ ψ` is a.e. equal to the identity on `N`. -/
  comp_right : Hom.AEEq (ψ.comp φ) (Hom.id N)

/-- Two random variable models `M` and `N` are **equivalent** when some pair of morphisms
between them is an equivalence.

Paper node: `Definition 3.10` -/
def Equivalent (M : RVModel.{u, v, w} I) (N : RVModel.{u₁, v₁, w₁} J) : Prop :=
  ∃ (φ : Hom M N) (ψ : Hom N M), IsEquivalence φ ψ

/-! ### The "laid out" characterization

The paragraph after Definition 3.10 spells the definition out for two models over the
*same* index set `I`, joined by probability-preserving maps `π : Ω → Λ` and `ρ : Λ → Ω`
and families of maps `f_i : R X_i → R Y_i`, `g_i : R Y_i → R X_i`.  The "obvious triples"
are the ones with `ι = id_I`, and they are morphisms exactly when the paper's condition
(2) holds — which is `hf`/`hg` below — and then constitute an equivalence exactly when its
condition (1) holds.  Proposition 4.7 uses precisely this shape. -/

/-- The "obvious triple" `(π, id_I, (f_i)_{i∈I})` over a fixed index set: a morphism as
soon as `f_i (X_i) = π^* Y_i` almost everywhere for every `i`, which is half of the
paper's condition (2) after Definition 3.10. -/
def Hom.ofSameIndex {M : RVModel.{u, v, w} I} {N : RVModel.{u₁, v₁, w} I}
    (π : M.Ω → N.Ω) (hπ : MeasurePreserving π M.P N.P) (f : ∀ i, M.R i → N.R i)
    (hf : ∀ i, ∀ᵐ ω ∂M.P, N.X i (π ω) = f i (M.X i ω)) : Hom M N where
  π := π
  π_pres := hπ
  ι := _root_.id
  f := f
  eq_ae := hf

@[simp] lemma Hom.ofSameIndex_π {M : RVModel.{u, v, w} I} {N : RVModel.{u₁, v₁, w} I}
    (π : M.Ω → N.Ω) (hπ : MeasurePreserving π M.P N.P) (f : ∀ i, M.R i → N.R i)
    (hf : ∀ i, ∀ᵐ ω ∂M.P, N.X i (π ω) = f i (M.X i ω)) :
    (Hom.ofSameIndex π hπ f hf).π = π := rfl

/-- The characterization the paper lays out after Definition 3.10.  Given two random
variable models over the same index set `I`, probability-preserving maps `π : Ω → Λ` and
`ρ : Λ → Ω`, and families `f_i : R X_i → R Y_i` and `g_i : R Y_i → R X_i` satisfying the
paper's condition (2) — `f_i (X_i) = π^* Y_i` and `g_i (Y_i) = ρ^* X_i` almost everywhere,
which is exactly what makes the two obvious triples morphisms — the pair is an equivalence
if and only if the paper's condition (1) holds: `ρ ∘ π` and `π ∘ ρ` are equal almost
everywhere to `id_Ω` and `id_Λ`.

The index condition of Definition 3.9 is automatic here, both triples having `ι = id_I`. -/
lemma isEquivalence_ofSameIndex_iff {M : RVModel.{u, v, w} I} {N : RVModel.{u₁, v₁, w} I}
    {π : M.Ω → N.Ω} {ρ : N.Ω → M.Ω} (hπ : MeasurePreserving π M.P N.P)
    (hρ : MeasurePreserving ρ N.P M.P) {f : ∀ i, M.R i → N.R i} {g : ∀ i, N.R i → M.R i}
    (hf : ∀ i, ∀ᵐ ω ∂M.P, N.X i (π ω) = f i (M.X i ω))
    (hg : ∀ i, ∀ᵐ l ∂N.P, M.X i (ρ l) = g i (N.X i l)) :
    IsEquivalence (Hom.ofSameIndex π hπ f hf) (Hom.ofSameIndex ρ hρ g hg) ↔
      ((∀ᵐ ω ∂M.P, ρ (π ω) = ω) ∧ ∀ᵐ l ∂N.P, π (ρ l) = l) := by
  constructor
  · rintro ⟨⟨h₁, -⟩, ⟨h₂, -⟩⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩

/-! ## Proposition 3.12 — equivalence of models is an equivalence relation -/

/-- Reflexivity: `(id, id)` is an equivalence. -/
lemma Equivalent.refl (M : RVModel.{u, v, w} I) : Equivalent M M :=
  ⟨Hom.id M, Hom.id M, ⟨Hom.aeEq_equivalence.refl _, Hom.aeEq_equivalence.refl _⟩⟩

/-- Symmetry: swap the two morphisms of the equivalence. -/
lemma Equivalent.symm (h : Equivalent M N) : Equivalent N M := by
  obtain ⟨φ, ψ, hφψ⟩ := h
  exact ⟨ψ, φ, ⟨hφψ.comp_right, hφψ.comp_left⟩⟩

/-- Transitivity — the paper's (3.29): if `(φ₁, ψ₁)` is an equivalence between `L` and `M`
and `(φ₂, ψ₂)` one between `M` and `N`, then `(φ₂ ∘ φ₁, ψ₁ ∘ ψ₂)` is one between `L` and
`N`, because `(ψ₁ ∘ ψ₂) ∘ (φ₂ ∘ φ₁) = ψ₁ ∘ (ψ₂ ∘ φ₂) ∘ φ₁` is a.e. equal to
`ψ₁ ∘ φ₁`, hence to `id_L`, by Proposition 3.11 (2). -/
lemma Equivalent.trans (h : Equivalent M N) (h' : Equivalent N P) : Equivalent M P := by
  obtain ⟨φ₁, ψ₁, hL, hM⟩ := h
  obtain ⟨φ₂, ψ₂, hM', hN⟩ := h'
  refine ⟨φ₁.comp φ₂, ψ₂.comp ψ₁, ⟨?_, ?_⟩⟩
  · have hstep : Hom.AEEq ((φ₁.comp φ₂).comp (ψ₂.comp ψ₁)) (φ₁.comp ψ₁) := by
      have h1 : Hom.AEEq ((φ₁.comp φ₂).comp (ψ₂.comp ψ₁)) ((φ₁.comp (φ₂.comp ψ₂)).comp ψ₁) :=
        Hom.aeEq_equivalence.refl _
      refine Hom.aeEq_equivalence.trans h1 ?_
      exact Hom.comp_aeEq_congr (Hom.comp_aeEq_congr (Hom.aeEq_equivalence.refl _) hM')
        (Hom.aeEq_equivalence.refl _)
    exact Hom.aeEq_equivalence.trans hstep hL
  · have hstep : Hom.AEEq ((ψ₂.comp ψ₁).comp (φ₁.comp φ₂)) (ψ₂.comp φ₂) := by
      have h1 : Hom.AEEq ((ψ₂.comp ψ₁).comp (φ₁.comp φ₂)) ((ψ₂.comp (ψ₁.comp φ₁)).comp φ₂) :=
        Hom.aeEq_equivalence.refl _
      refine Hom.aeEq_equivalence.trans h1 ?_
      exact Hom.comp_aeEq_congr (Hom.comp_aeEq_congr (Hom.aeEq_equivalence.refl _) hM)
        (Hom.aeEq_equivalence.refl _)
    exact Hom.aeEq_equivalence.trans hstep hN

end RVModel

namespace RVModelObj

/-- Equivalence of random variable models, as a relation on the objects of the category of
Proposition 3.7.  Universes are fixed here only so that the relation has a single type to
live on; `RVModel.Equivalent` itself relates models over arbitrary index types and
universes. -/
def Equivalent (A B : RVModelObj.{u, v, w}) : Prop := RVModel.Equivalent A.M B.M

/-- **Proposition 3.12**: equivalence of random variable models is an equivalence relation.

Reflexivity and symmetry are immediate; transitivity is the paper's (3.29), which runs
through Proposition 3.11 (`RVModel.Equivalent.trans`).

Paper node: `Proposition 3.12` -/
theorem equivalent_equivalence : Equivalence (Equivalent.{u, v, w}) where
  refl A := RVModel.Equivalent.refl A.M
  symm h := RVModel.Equivalent.symm h
  trans h h' := RVModel.Equivalent.trans h h'

end RVModelObj

end Condensation
