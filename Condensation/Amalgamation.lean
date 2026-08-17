import Condensation.Model

/-!
# Condensation §4 — amalgamation

Definitions 4.11 and 4.12 and Lemma 4.13 of Eisenstat, *Condensation: A Theory of
Concepts*:

* Definition 4.11 — an **amalgamation of a cospan** of probability-preserving maps
  (`Amalgamation`);
* Definition 4.12 — an **amalgamation of two latent variable models** for the same
  random variable model (`LatentAmalgamation`);
* Lemma 4.13 — every cospan, and every pair of latent variable models over a common `M`,
  admits one: `Amalgamation.canonical` / `LatentAmalgamation.canonical` build the paper's
  (4.49)–(4.53) explicitly, and `nonempty_amalgamation` / `nonempty_latentAmalgamation`
  are the existence statements.

## Modeling decisions (`dd:amalgamation`)

**Why `Λ₀` is a field and the two `L̃ₖ` are not.**  Definition 4.12 asks for "two latent
variable models `L̃₁` and `L̃₂`, *both of which have underlying probability space `Λ₀`*".
Rendering that literally — two `LatentModel M` fields plus a proof that their carriers
agree — would make the agreement a *type* equality, and every subsequent use of it would
have to travel through `Eq.mpr`/`HEq`.  That is a known dead end (`Condensation/KNOWLEDGE.md`).

So `Λ₀` is primary: the structure carries the countable discrete probability space
`(Λ₀, P₀)` once, and carries the two latent *families* over it as data —
`Y₁ : ∀ A, Λ₀ → L₁.L.R A` and `Y₂ : ∀ A, Λ₀ → L₂.L.R A` — together with their maps
`πₖ : Λ₀ → Ω` and Definition 3.2's contribution conditions.  The two latent variable
models the paper names are then *derived*, `LatentAmalgamation.lat₁` and `.lat₂`, and their
underlying spaces are `Λ₀` **definitionally**, which is exactly the property Definition
4.12 was asking for and Theorem 4.15 needs (it compares `Y_A` with `Z_⊇A` on one space).

**Why `Yₖ` is valued in `Lₖ`'s ranges.**  Clause (3) of Definition 4.12 says the morphisms
`ρₖ : L̃ₖ → Lₖ` act "as the identity on the respective index sets and on the respective
ranges of all the latent variables" — the forms (4.44)/(4.45).  A morphism whose range
components are identities can only exist if `L̃ₖ` and `Lₖ` have the *same* range family, so
`Yₖ A` is valued in `Lₖ.L.R A` by construction and the range-component data of the morphism
carries no information.  What is left of Definition 3.5's morphism conditions is then just:
`ρₖ` is probability preserving (`ρₖ_pres`), and `(Lₖ.Y A) ∘ ρₖ = Yₖ A` almost everywhere
(`ρₖ_Y`) — the paper's `fⱼ(X_{ι(j)}) = π^* Yⱼ` a.e. of (3.24) with `fⱼ = id`.

**And that is all of clause (3).**  The morphisms (4.44)/(4.45) are morphisms in the sense
of Definition 3.5, which is a morphism of the underlying *random variable* models; the
paper never defines a morphism of *latent* variable models, and Definition 3.5 imposes
exactly two conditions — "`π` is probability preserving" and `fⱼ(X_{ι(j)}) = π^* Yⱼ` a.e.
Nothing in Definition 4.12 relates `Lₖ.π ∘ ρₖ` to `πₖ`, so this structure carries no such
field: `ρₖ_pres` and `ρₖ_Y` are the whole of clause (3).  The `π`-compatibility that
Theorem 4.15's proof genuinely needs is the one *between* `π₁` and `π₂`, and it is carried
separately, and only almost everywhere, by the field `comm` — an addition justified as an
erratum against Definition 4.12 (see below), not something read off clause (3).

Note the two directions of `π`, which `KNOWLEDGE.md` warns about: a latent variable model's
`π` goes `Λ → Ω`, while §3.1's morphisms go source → target.  Here `ρₖ : Λ₀ → Λₖ` is both:
the underlying map of the morphism `L̃ₖ → Lₖ` *and* a map in the same direction as the
`ρₖ` of diagram (4.43).

**Naming.**  Lean identifiers may not carry a combining tilde, so the paper's `Ỹ`, `Z̃`
and `π̃` are spelled `Y₁`, `Y₂`, `π₁`, `π₂` as *fields of `LatentAmalgamation`* — the
tilde is carried by the qualification (`Am.Y₁` is the paper's `Ỹ`, while `L₁.Y` is the
paper's `Y`).  Docstrings keep the paper's `L̃ₖ`.

**Why `π₁` and `π₂` are separate fields, plus a `comm` field tying them.**  Definition
4.12 asks only that each `L̃ₖ` be a latent variable model for `M`, and a latent variable
model carries its own map to `Ω`; nothing in the printed clause (2) ties `Am.π₁` to
`Am.π₂`.  They are nonetheless equal in the construction of Lemma 4.13 (that is exactly
what the commuting square (4.43) says), and Theorem 4.15's proof needs them to agree
almost everywhere, so the a.e. commutation is carried as the field `comm` and recorded as
an erratum against Definition 4.12.

**`dd:amalgamation`: the measure.**  Equation (4.53) defines `P̃₀` by an integral over `Ω`
of a product of conditional measures.  On a countable discrete `Ω` that integral is a sum,
and the resulting measure is determined by its values on singletons; `canonicalWeight`
writes those values directly.  The `ℝ≥0∞` quotient is the paper's formula verbatim: when
`P_Ω {π₁ λ₁} = 0` the numerator `P₁ {λ₁} · P₂ {λ₂}` is `0` as well (a `π`-fibre of a null
point is null), and `0 / 0 = 0` in `ℝ≥0∞`, so no case split is needed to get the paper's
"`0` when the denominator vanishes".
-/

universe u v w u₀ u₁ v₁ u₂ v₂

namespace Condensation

open MeasureTheory ProbabilityTheory

/-! ## Definition 4.11 — amalgamation of a cospan of probability spaces -/

/-- An **amalgamation** of the cospan (4.42)

```
        Λ₁
        │ π₁
   π₂   ▼
Λ₂ ───► Ω
```

of probability-preserving maps: a countable discrete probability space `Λ₀` together with
probability-preserving `ρₖ : Λ₀ → Λₖ` making the square (4.43) commute.

Definition 4.11's standing hypothesis that `π₁` and `π₂` are themselves probability
preserving is carried as the two `Prop` fields `π₁_pres`/`π₂_pres`, so that the structure
is a self-contained rendering of "an amalgamation of the diagram (4.42)" rather than of
"an amalgamation of a pair of bare maps".  They are proof-irrelevant, so this costs
nothing at a use site.

Paper node: `Definition 4.11` -/
structure Amalgamation {Ω : Type u} [MeasurableSpace Ω] (PΩ : Measure Ω)
    {Λ₁ : Type u₁} [MeasurableSpace Λ₁] (P₁ : Measure Λ₁)
    {Λ₂ : Type u₂} [MeasurableSpace Λ₂] (P₂ : Measure Λ₂)
    (π₁ : Λ₁ → Ω) (π₂ : Λ₂ → Ω) where
  /-- Definition 4.11's hypothesis on the diagram (4.42): `π₁` is probability preserving. -/
  π₁_pres : MeasurePreserving π₁ P₁ PΩ
  /-- Definition 4.11's hypothesis on the diagram (4.42): `π₂` is probability preserving. -/
  π₂_pres : MeasurePreserving π₂ P₂ PΩ
  /-- The amalgamating countable discrete probability space `Λ₀`. -/
  Λ₀ : Type u₀
  [mΛ₀ : MeasurableSpace Λ₀]
  [countΛ₀ : Countable Λ₀]
  [singΛ₀ : MeasurableSingletonClass Λ₀]
  /-- The probability measure `P₀` on `Λ₀`. -/
  P₀ : Measure Λ₀
  [probP₀ : IsProbabilityMeasure P₀]
  /-- The projection `ρ₁ : Λ₀ → Λ₁` of (4.43). -/
  ρ₁ : Λ₀ → Λ₁
  /-- The projection `ρ₂ : Λ₀ → Λ₂` of (4.43). -/
  ρ₂ : Λ₀ → Λ₂
  ρ₁_pres : MeasurePreserving ρ₁ P₀ P₁
  ρ₂_pres : MeasurePreserving ρ₂ P₀ P₂
  /-- The square (4.43) commutes. -/
  comm : π₁ ∘ ρ₁ = π₂ ∘ ρ₂

attribute [instance] Amalgamation.mΛ₀ Amalgamation.countΛ₀ Amalgamation.singΛ₀
  Amalgamation.probP₀

/-! ## Definition 4.12 — amalgamation of two latent variable models -/

/-- An **amalgamation of two latent variable models** `L₁` and `L₂` for the same random
variable model `M` (Definition 4.12).  It consists of

1. a countable discrete probability space `Λ₀` (`Λ₀`, `P₀`) — with finite entropy, since
   clause (2) makes it the sample space of two random variable models (Definition 3.1);
2. two latent variable models for `M` with underlying probability space `Λ₀` — carried
   here as the latent families `Y₁`, `Y₂` over `Λ₀` together with their maps `πₖ : Λ₀ → Ω`
   and Definition 3.2's contribution conditions, and assembled into honest
   `LatentModel M`s by `LatentAmalgamation.lat₁` and `.lat₂`;
3. two morphisms `ρₖ : L̃ₖ → Lₖ` of the forms (4.44)/(4.45) — Definition 3.5 morphisms of
   the *underlying random variable models*, identity on the index set `P⁺I` and on every
   range, so all that remains is a probability-preserving `ρₖ : Λ₀ → Λₖ` with
   `(Lₖ.Y A) ∘ ρₖ = Yₖ A` almost everywhere.

See this file's header for why `Λ₀` is primary and the two `L̃ₖ` are derived.

Paper node: `Definition 4.12` -/
structure LatentAmalgamation {I : Type w} [Finite I] {M : RVModel.{u, v, w} I}
    (L₁ : LatentModel.{u, v, w, u₁, v₁} M) (L₂ : LatentModel.{u, v, w, u₂, v₂} M) where
  /-- (1) the countable discrete probability space `Λ₀`. -/
  Λ₀ : Type u₀
  [mΛ₀ : MeasurableSpace Λ₀]
  [countΛ₀ : Countable Λ₀]
  [singΛ₀ : MeasurableSingletonClass Λ₀]
  /-- The probability measure on `Λ₀`. -/
  P₀ : Measure Λ₀
  [probP₀ : IsProbabilityMeasure P₀]
  /-- Definition 3.1's "with finite entropy", inherited by `Λ₀` from clause (2): `L̃₁` and
  `L̃₂` are latent variable models, hence random variable models on `Λ₀`. -/
  [finiteEntropy_Λ₀ : ShannonInformation.FiniteEntropyMeasure P₀]
  /-- (2) the latent variables of `L̃₁`, valued in `L₁`'s ranges — the morphism (4.44)
  acts as the identity on those ranges, which forces the range families to agree. -/
  Y₁ : ∀ A : PPlus I, Λ₀ → L₁.L.R A
  measurable_Y₁ : ∀ A, Measurable (Y₁ A)
  finiteEntropy_Y₁ : ∀ A, ShannonInformation.FiniteEntropyOf (Y₁ A) P₀
  /-- The map `π₁ : Λ₀ → Ω` making `L̃₁` a latent variable model *for `M`*. -/
  π₁ : Λ₀ → M.Ω
  π₁_pres : MeasurePreserving π₁ P₀ M.P
  /-- Definition 3.2's contribution condition for `L̃₁`. -/
  contributes₁ : ∀ i : I,
    AEFunctionOf (fun l (B : contribIdx i) => Y₁ (B : PPlus I) l) (M.X i ∘ π₁) P₀
  /-- (2) the latent variables of `L̃₂`, valued in `L₂`'s ranges. -/
  Y₂ : ∀ A : PPlus I, Λ₀ → L₂.L.R A
  measurable_Y₂ : ∀ A, Measurable (Y₂ A)
  finiteEntropy_Y₂ : ∀ A, ShannonInformation.FiniteEntropyOf (Y₂ A) P₀
  /-- The map `π₂ : Λ₀ → Ω` making `L̃₂` a latent variable model *for `M`*. -/
  π₂ : Λ₀ → M.Ω
  π₂_pres : MeasurePreserving π₂ P₀ M.P
  /-- Definition 3.2's contribution condition for `L̃₂`. -/
  contributes₂ : ∀ i : I,
    AEFunctionOf (fun l (B : contribIdx i) => Y₂ (B : PPlus I) l) (M.X i ∘ π₂) P₀
  /-- (3) the underlying map of the morphism `ρ₁ : L̃₁ → L₁` of (4.44). -/
  ρ₁ : Λ₀ → L₁.Λ
  ρ₁_pres : MeasurePreserving ρ₁ P₀ L₁.P
  /-- (3) the morphism condition (3.24) for `ρ₁`, with identity range components. -/
  ρ₁_Y : ∀ A : PPlus I, ∀ᵐ l ∂P₀, L₁.Y A (ρ₁ l) = Y₁ A l
  /-- (3) the underlying map of the morphism `ρ₂ : L̃₂ → L₂` of (4.45). -/
  ρ₂ : Λ₀ → L₂.Λ
  ρ₂_pres : MeasurePreserving ρ₂ P₀ L₂.P
  /-- (3) the morphism condition (3.24) for `ρ₂`, with identity range components. -/
  ρ₂_Y : ∀ A : PPlus I, ∀ᵐ l ∂P₀, L₂.Y A (ρ₂ l) = Y₂ A l
  /-- The commuting square (4.43) of Definition 4.11, carried into Definition 4.12: the
  two derived latent variable models observe `M` through the *same* map.

  Definition 4.12 leaves this implicit — it says only that `L̃₁` and `L̃₂` are latent
  variable models with underlying space `Λ₀` and associated model `M`, which by itself
  does not tie `π₁` to `π₂`.  It is nonetheless part of what "amalgamation" means: the
  construction of Lemma 4.13 gives `Am.π₁ = L₁.π ∘ ρ₁ = L₂.π ∘ ρ₂ = Am.π₂` on the nose by
  (4.51),
  and Theorem 4.15's proof uses it — the step "`Y_A` is a function of `X_i` a.e., and `X_i`
  is a function of `Z_∋i` a.e., so `Y_A` is a function of `Z_∋i` a.e." composes a
  dependence witnessed through `π₁` with one witnessed through `π₂`, which is only legal
  when the two agree almost everywhere.  Recorded as an erratum. -/
  comm : ∀ᵐ l ∂P₀, π₁ l = π₂ l

attribute [instance] LatentAmalgamation.mΛ₀ LatentAmalgamation.countΛ₀
  LatentAmalgamation.singΛ₀ LatentAmalgamation.probP₀ LatentAmalgamation.finiteEntropy_Λ₀
  LatentAmalgamation.finiteEntropy_Y₁ LatentAmalgamation.finiteEntropy_Y₂

namespace LatentAmalgamation

variable {I : Type w} [Finite I] {M : RVModel.{u, v, w} I}
  {L₁ : LatentModel.{u, v, w, u₁, v₁} M} {L₂ : LatentModel.{u, v, w, u₂, v₂} M}

/-- Clause (2) of Definition 4.12, half of it: `L̃₁` as a random variable model over `Λ₀`
indexed by `P⁺I`. -/
def rv₁ (Am : LatentAmalgamation L₁ L₂) : RVModel.{u₀, v₁, w} (PPlus I) where
  Ω := Am.Λ₀
  P := Am.P₀
  R := fun A => L₁.L.R A
  X := Am.Y₁
  measurable_X := Am.measurable_Y₁
  finiteEntropy_X := Am.finiteEntropy_Y₁

/-- Clause (2) of Definition 4.12, the other half. -/
def rv₂ (Am : LatentAmalgamation L₁ L₂) : RVModel.{u₀, v₂, w} (PPlus I) where
  Ω := Am.Λ₀
  P := Am.P₀
  R := fun A => L₂.L.R A
  X := Am.Y₂
  measurable_X := Am.measurable_Y₂
  finiteEntropy_X := Am.finiteEntropy_Y₂

/-- The latent variable model `L̃₁` of Definition 4.12(2).  Its underlying probability
space is `Λ₀` *definitionally*, which is what makes Theorem 4.15 statable. -/
def lat₁ (Am : LatentAmalgamation L₁ L₂) : LatentModel.{u, v, w, u₀, v₁} M where
  L := Am.rv₁
  π := Am.π₁
  π_pres := Am.π₁_pres
  contributes := Am.contributes₁

/-- The latent variable model `L̃₂` of Definition 4.12(2). -/
def lat₂ (Am : LatentAmalgamation L₁ L₂) : LatentModel.{u, v, w, u₀, v₂} M where
  L := Am.rv₂
  π := Am.π₂
  π_pres := Am.π₂_pres
  contributes := Am.contributes₂

@[simp] lemma lat₁_Λ (Am : LatentAmalgamation L₁ L₂) : Am.lat₁.Λ = Am.Λ₀ := rfl

@[simp] lemma lat₂_Λ (Am : LatentAmalgamation L₁ L₂) : Am.lat₂.Λ = Am.Λ₀ := rfl

@[simp] lemma lat₁_P (Am : LatentAmalgamation L₁ L₂) : Am.lat₁.P = Am.P₀ := rfl

@[simp] lemma lat₂_P (Am : LatentAmalgamation L₁ L₂) : Am.lat₂.P = Am.P₀ := rfl

@[simp] lemma lat₁_Y (Am : LatentAmalgamation L₁ L₂) (A : PPlus I) :
    Am.lat₁.Y A = Am.Y₁ A := rfl

@[simp] lemma lat₂_Y (Am : LatentAmalgamation L₁ L₂) (A : PPlus I) :
    Am.lat₂.Y A = Am.Y₂ A := rfl

/-- The **non-vacuity witness for Definition 4.12**: every latent variable model is
amalgamated with itself along the identity.  `Λ₀` is `L`'s own latent space `Λ`, both
latent families are `L`'s own `(Y_A)`, both maps to `Ω` are `L.π`, and both morphisms
`ρₖ : L̃ₖ → Lₖ` are the identity — so Definition 3.5's conditions hold on the nose and
`comm` is `rfl`.

It is the cheap non-vacuity witness for Theorem 4.15 and the whole of §5: it needs none of
Lemma 4.13's measure machinery — no fibre product, no (4.53) weight, no `MeasurePreserving`
computation — so a reader checking that the §5 hypotheses are satisfiable at all need only
read this definition.  (`LatentAmalgamation.canonical` is the paper's general construction
and is also axiom-clean; `diagonal` is the short path, not the only one.)

Machinery, not a paper node — Definition 4.12 is the node it witnesses. -/
def diagonal (L : LatentModel.{u, v, w, u₁, v₁} M) :
    LatentAmalgamation.{u, v, w, u₁, u₁, v₁, u₁, v₁} L L where
  Λ₀ := L.Λ
  P₀ := L.P
  Y₁ := L.Y
  measurable_Y₁ := L.L.measurable_X
  finiteEntropy_Y₁ := L.L.finiteEntropy_X
  π₁ := L.π
  π₁_pres := L.π_pres
  contributes₁ := L.contributes
  Y₂ := L.Y
  measurable_Y₂ := L.L.measurable_X
  finiteEntropy_Y₂ := L.L.finiteEntropy_X
  π₂ := L.π
  π₂_pres := L.π_pres
  contributes₂ := L.contributes
  ρ₁ := id
  ρ₁_pres := MeasurePreserving.id _
  ρ₁_Y := fun _ => Filter.Eventually.of_forall fun _ => rfl
  ρ₂ := id
  ρ₂_pres := MeasurePreserving.id _
  ρ₂_Y := fun _ => Filter.Eventually.of_forall fun _ => rfl
  comm := Filter.Eventually.of_forall fun _ => rfl

end LatentAmalgamation

/-! ## Lemma 4.13 — existence, and the explicit construction

The paper's (4.49)–(4.53).  `Λ₀` is the fibre product `S` of (4.49), and the measure of
(4.53) is written out on singletons (`dd:amalgamation`). -/

namespace Amalgamation

variable {Ω : Type u} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  {Λ₁ : Type u₁} [MeasurableSpace Λ₁] [Countable Λ₁] [MeasurableSingletonClass Λ₁]
  {Λ₂ : Type u₂} [MeasurableSpace Λ₂] [Countable Λ₂] [MeasurableSingletonClass Λ₂]
  (PΩ : Measure Ω) (P₁ : Measure Λ₁) (P₂ : Measure Λ₂) (π₁ : Λ₁ → Ω) (π₂ : Λ₂ → Ω)

/-- The fibre product `S = {(λ₁, λ₂) | π₁ λ₁ = π₂ λ₂}` of (4.49): a pullback in the
category of measurable spaces, carrying the subspace σ-algebra. -/
abbrev carrier : Type (max u₁ u₂) := {p : Λ₁ × Λ₂ // π₁ p.1 = π₂ p.2}

namespace carrier

/-- `ρ₁` of (4.50). -/
def fst (p : carrier π₁ π₂) : Λ₁ := (p : Λ₁ × Λ₂).1

/-- `ρ₂` of (4.50). -/
def snd (p : carrier π₁ π₂) : Λ₂ := (p : Λ₁ × Λ₂).2

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
lemma measurable_fst : Measurable (carrier.fst π₁ π₂) :=
  measurable_of_countable _

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
lemma measurable_snd : Measurable (carrier.snd π₁ π₂) :=
  measurable_of_countable _

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] [MeasurableSpace Λ₁]
  [Countable Λ₁] [MeasurableSingletonClass Λ₁] [MeasurableSpace Λ₂] [Countable Λ₂]
  [MeasurableSingletonClass Λ₂] in
/-- `π₀ = π₁ ∘ ρ₁ = π₂ ∘ ρ₂` of (4.51), on the nose. -/
lemma comm : π₁ ∘ carrier.fst π₁ π₂ = π₂ ∘ carrier.snd π₁ π₂ := funext fun p => p.2

end carrier

/-- The weight `P₀ {(λ₁, λ₂)}` of (4.53) evaluated on a singleton of the countable
discrete space `Λ₀`: `P₁{λ₁} · P₂{λ₂} / P_Ω{π₁ λ₁}` (`dd:amalgamation`).

In `ℝ≥0∞` this is already the paper's "`0` when the denominator vanishes": if
`P_Ω {π₁ λ₁} = 0` then, `π₁` being probability preserving, `P₁ {λ₁} = 0` too, and
`0 / 0 = 0`. -/
noncomputable def canonicalWeight (p : carrier π₁ π₂) : ENNReal :=
  P₁ {carrier.fst π₁ π₂ p} * P₂ {carrier.snd π₁ π₂ p} / PΩ {π₁ (carrier.fst π₁ π₂ p)}

/-- The measure `P₀` of (4.53), in countable discrete form (`dd:amalgamation`). -/
noncomputable def canonicalMeasure : Measure (carrier π₁ π₂) :=
  Measure.sum fun p => canonicalWeight PΩ P₁ P₂ π₁ π₂ p • Measure.dirac p

omit [Countable Ω] [MeasurableSingletonClass Ω] [Countable Λ₁] [Countable Λ₂] in
/-- `canonicalMeasure` is the measure whose mass at each point is `canonicalWeight` — the
sanity check that the `Measure.sum`-of-Diracs spelling is the intended object, and the
form in which the remaining proofs of Lemma 4.13 will use it. -/
@[simp] lemma canonicalMeasure_singleton (p : carrier π₁ π₂) :
    canonicalMeasure PΩ P₁ P₂ π₁ π₂ {p} = canonicalWeight PΩ P₁ P₂ π₁ π₂ p :=
  Measure.sum_smul_dirac_singleton

variable [IsProbabilityMeasure PΩ] [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]

/-- The weight (4.53), as a function on all of `Λ₁ × Λ₂` (zero off the fibre product).
Writing it this way is what lets the sums of (4.54)–(4.57) be iterated sums over `Λ₁` and
`Λ₂` rather than sums over a subtype. -/
private noncomputable def offWeight (a : Λ₁) (b : Λ₂) : ENNReal :=
  Set.indicator {q : Λ₁ × Λ₂ | π₁ q.1 = π₂ q.2}
    (fun q => P₁ {q.1} * P₂ {q.2} / PΩ {π₁ q.1}) (a, b)

omit [Countable Ω] [MeasurableSingletonClass Ω] [Countable Λ₁] [MeasurableSingletonClass Λ₁]
  [Countable Λ₂] [MeasurableSingletonClass Λ₂] [IsProbabilityMeasure PΩ]
  [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] in
private lemma offWeight_of_eq {a : Λ₁} {b : Λ₂} (h : π₁ a = π₂ b) :
    offWeight PΩ P₁ P₂ π₁ π₂ a b = P₁ {a} * P₂ {b} / PΩ {π₁ a} :=
  Set.indicator_of_mem (s := {q : Λ₁ × Λ₂ | π₁ q.1 = π₂ q.2}) (a := (a, b)) h _

omit [Countable Ω] [MeasurableSingletonClass Ω] [Countable Λ₁] [MeasurableSingletonClass Λ₁]
  [Countable Λ₂] [MeasurableSingletonClass Λ₂] [IsProbabilityMeasure PΩ]
  [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] in
private lemma offWeight_of_ne {a : Λ₁} {b : Λ₂} (h : ¬ π₁ a = π₂ b) :
    offWeight PΩ P₁ P₂ π₁ π₂ a b = 0 :=
  Set.indicator_of_notMem (s := {q : Λ₁ × Λ₂ | π₁ q.1 = π₂ q.2}) (a := (a, b)) h _

omit [Countable Ω] [Countable Λ₁] [MeasurableSingletonClass Λ₁] [IsProbabilityMeasure P₁]
  [IsProbabilityMeasure P₂] in
/-- The weight (4.53) summed over a `π₂`-fibre: (4.54).  This is the one computation the
rest of Lemma 4.13 runs on — the total mass (4.55)–(4.56) and both halves of (4.57) are
one further `tsum` step from it and from its mirror `tsum_offWeight_left`. -/
private lemma tsum_offWeight_right (h₁ : MeasurePreserving π₁ P₁ PΩ)
    (h₂ : MeasurePreserving π₂ P₂ PΩ) (a : Λ₁) :
    ∑' b : Λ₂, offWeight PΩ P₁ P₂ π₁ π₂ a b = P₁ {a} := by
  have hstep : ∀ b : Λ₂, offWeight PΩ P₁ P₂ π₁ π₂ a b
      = P₁ {a} / PΩ {π₁ a} * (π₂ ⁻¹' {π₁ a}).indicator (fun b => P₂ {b}) b := by
    intro b
    by_cases h : π₁ a = π₂ b
    · rw [offWeight_of_eq PΩ P₁ P₂ π₁ π₂ h,
        Set.indicator_of_mem (by simpa [Set.mem_preimage] using h.symm)]
      simp only [div_eq_mul_inv]
      ring
    · rw [offWeight_of_ne PΩ P₁ P₂ π₁ π₂ h,
        Set.indicator_of_notMem (by simpa [Set.mem_preimage, eq_comm] using h), mul_zero]
  rw [tsum_congr hstep, ENNReal.tsum_mul_left,
    Measure.tsum_indicator_apply_singleton P₂ _ (Set.to_countable _).measurableSet,
    h₂.measure_preimage (measurableSet_singleton _).nullMeasurableSet]
  by_cases h0 : PΩ {π₁ a} = 0
  · have hz : P₁ {a} = 0 := by
      have hle : P₁ {a} ≤ P₁ (π₁ ⁻¹' {π₁ a}) := measure_mono (Set.singleton_subset_iff.2 rfl)
      rw [h₁.measure_preimage (measurableSet_singleton _).nullMeasurableSet, h0] at hle
      simpa using hle
    simp [hz, h0]
  · exact ENNReal.div_mul_cancel h0 (measure_ne_top _ _)

omit [Countable Ω] [Countable Λ₂] [MeasurableSingletonClass Λ₂] [IsProbabilityMeasure P₁]
  [IsProbabilityMeasure P₂] in
/-- (4.54) on the other side: the weight (4.53) summed over a `π₁`-fibre. -/
private lemma tsum_offWeight_left (h₁ : MeasurePreserving π₁ P₁ PΩ)
    (h₂ : MeasurePreserving π₂ P₂ PΩ) (b : Λ₂) :
    ∑' a : Λ₁, offWeight PΩ P₁ P₂ π₁ π₂ a b = P₂ {b} := by
  have hstep : ∀ a : Λ₁, offWeight PΩ P₁ P₂ π₁ π₂ a b
      = P₂ {b} / PΩ {π₂ b} * (π₁ ⁻¹' {π₂ b}).indicator (fun a => P₁ {a}) a := by
    intro a
    by_cases h : π₁ a = π₂ b
    · rw [offWeight_of_eq PΩ P₁ P₂ π₁ π₂ h,
        Set.indicator_of_mem (by simpa [Set.mem_preimage] using h), h]
      simp only [div_eq_mul_inv]
      ring
    · rw [offWeight_of_ne PΩ P₁ P₂ π₁ π₂ h,
        Set.indicator_of_notMem (by simpa [Set.mem_preimage] using h), mul_zero]
  rw [tsum_congr hstep, ENNReal.tsum_mul_left,
    Measure.tsum_indicator_apply_singleton P₁ _ (Set.to_countable _).measurableSet,
    h₁.measure_preimage (measurableSet_singleton _).nullMeasurableSet]
  by_cases h0 : PΩ {π₂ b} = 0
  · have hz : P₂ {b} = 0 := by
      have hle : P₂ {b} ≤ P₂ (π₂ ⁻¹' {π₂ b}) := measure_mono (Set.singleton_subset_iff.2 rfl)
      rw [h₂.measure_preimage (measurableSet_singleton _).nullMeasurableSet, h0] at hle
      simpa using hle
    simp [hz, h0]
  · exact ENNReal.div_mul_cancel h0 (measure_ne_top _ _)

omit [Countable Ω] [MeasurableSingletonClass Ω] [Countable Λ₁] [MeasurableSingletonClass Λ₁]
  [Countable Λ₂] [MeasurableSingletonClass Λ₂] [IsProbabilityMeasure PΩ]
  [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] in
/-- A sum of (4.53)'s weight over the fibre product, reindexed as an iterated sum over
`Λ₁` and `Λ₂` with the off-fibre terms killed by `offWeight`. -/
private lemma tsum_carrier (g : Λ₁ × Λ₂ → ENNReal) :
    ∑' p : carrier π₁ π₂, canonicalWeight PΩ P₁ P₂ π₁ π₂ p * g (p : Λ₁ × Λ₂)
      = ∑' (a : Λ₁) (b : Λ₂), offWeight PΩ P₁ P₂ π₁ π₂ a b * g (a, b) := by
  have hsub : ∑' p : carrier π₁ π₂, canonicalWeight PΩ P₁ P₂ π₁ π₂ p * g (p : Λ₁ × Λ₂)
      = ∑' q : Λ₁ × Λ₂, Set.indicator {q : Λ₁ × Λ₂ | π₁ q.1 = π₂ q.2}
          (fun q => P₁ {q.1} * P₂ {q.2} / PΩ {π₁ q.1} * g q) q := by
    refine (tsum_subtype {q : Λ₁ × Λ₂ | π₁ q.1 = π₂ q.2}
      (fun q => P₁ {q.1} * P₂ {q.2} / PΩ {π₁ q.1} * g q)).symm.symm.trans ?_
    rfl
  rw [hsub, ENNReal.tsum_prod (f := fun a b => Set.indicator {q : Λ₁ × Λ₂ | π₁ q.1 = π₂ q.2}
    (fun q => P₁ {q.1} * P₂ {q.2} / PΩ {π₁ q.1} * g q) (a, b))]
  refine tsum_congr fun a => tsum_congr fun b => ?_
  by_cases h : π₁ a = π₂ b
  · rw [Set.indicator_of_mem (s := {q : Λ₁ × Λ₂ | π₁ q.1 = π₂ q.2}) (a := (a, b)) h,
      offWeight_of_eq PΩ P₁ P₂ π₁ π₂ h]
  · rw [Set.indicator_of_notMem (s := {q : Λ₁ × Λ₂ | π₁ q.1 = π₂ q.2}) (a := (a, b)) h,
      offWeight_of_ne PΩ P₁ P₂ π₁ π₂ h, zero_mul]

omit [Countable Ω] [IsProbabilityMeasure P₂] in
/-- (4.55)–(4.56): the total mass of `canonicalMeasure` is `1`. -/
lemma isProbabilityMeasure_canonicalMeasure
    (h₁ : MeasurePreserving π₁ P₁ PΩ) (h₂ : MeasurePreserving π₂ P₂ PΩ) :
    IsProbabilityMeasure (canonicalMeasure PΩ P₁ P₂ π₁ π₂) := by
  refine ⟨?_⟩
  rw [canonicalMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  have h := tsum_carrier PΩ P₁ P₂ π₁ π₂ (fun _ => 1)
  simp only [mul_one] at h
  rw [h, tsum_congr fun a => tsum_offWeight_right PΩ P₁ P₂ π₁ π₂ h₁ h₂ a]
  simpa using Measure.tsum_indicator_apply_singleton P₁ Set.univ MeasurableSet.univ

omit [Countable Ω] [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] in
/-- The mass `canonicalMeasure` puts on a `ρ₁`-fibre is `P₁` of the point below it: the
computation behind (4.57). -/
private lemma canonicalMeasure_preimage_fst (h₁ : MeasurePreserving π₁ P₁ PΩ)
    (h₂ : MeasurePreserving π₂ P₂ PΩ) (a : Λ₁) :
    canonicalMeasure PΩ P₁ P₂ π₁ π₂ (carrier.fst π₁ π₂ ⁻¹' {a}) = P₁ {a} := by
  have hT : MeasurableSet (carrier.fst π₁ π₂ ⁻¹' {a}) :=
    carrier.measurable_fst (Ω := Ω) π₁ π₂ (measurableSet_singleton a)
  rw [canonicalMeasure, Measure.sum_apply _ hT]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hT]
  have hind : ∀ p : carrier π₁ π₂,
      canonicalWeight PΩ P₁ P₂ π₁ π₂ p *
          (carrier.fst π₁ π₂ ⁻¹' {a}).indicator (1 : carrier π₁ π₂ → ENNReal) p
      = canonicalWeight PΩ P₁ P₂ π₁ π₂ p *
          (fun q : Λ₁ × Λ₂ => ({a} : Set Λ₁).indicator (1 : Λ₁ → ENNReal) q.1) (p : Λ₁ × Λ₂) := by
    intro p
    by_cases h : carrier.fst π₁ π₂ p = a
    · simp only [Set.indicator_of_mem (s := carrier.fst π₁ π₂ ⁻¹' {a}) (a := p) h,
        Set.indicator_of_mem (s := ({a} : Set Λ₁)) (a := (p : Λ₁ × Λ₂).1) h, Pi.one_apply]
    · simp only [Set.indicator_of_notMem (s := carrier.fst π₁ π₂ ⁻¹' {a}) (a := p) h,
        Set.indicator_of_notMem (s := ({a} : Set Λ₁)) (a := (p : Λ₁ × Λ₂).1) h]
  rw [tsum_congr hind,
    tsum_carrier PΩ P₁ P₂ π₁ π₂ (fun q => ({a} : Set Λ₁).indicator (1 : Λ₁ → ENNReal) q.1),
    tsum_eq_single a]
  · simp only [Set.indicator_of_mem (s := ({a} : Set Λ₁)) (a := a) rfl, Pi.one_apply, mul_one]
    exact tsum_offWeight_right PΩ P₁ P₂ π₁ π₂ h₁ h₂ a
  · intro c hc
    simp [Set.indicator_of_notMem (s := ({a} : Set Λ₁)) (a := c) (by simpa using hc)]

omit [Countable Ω] [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] in
/-- The mass `canonicalMeasure` puts on a `ρ₂`-fibre. -/
private lemma canonicalMeasure_preimage_snd (h₁ : MeasurePreserving π₁ P₁ PΩ)
    (h₂ : MeasurePreserving π₂ P₂ PΩ) (b : Λ₂) :
    canonicalMeasure PΩ P₁ P₂ π₁ π₂ (carrier.snd π₁ π₂ ⁻¹' {b}) = P₂ {b} := by
  have hT : MeasurableSet (carrier.snd π₁ π₂ ⁻¹' {b}) :=
    carrier.measurable_snd (Ω := Ω) π₁ π₂ (measurableSet_singleton b)
  rw [canonicalMeasure, Measure.sum_apply _ hT]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hT]
  have hind : ∀ p : carrier π₁ π₂,
      canonicalWeight PΩ P₁ P₂ π₁ π₂ p *
          (carrier.snd π₁ π₂ ⁻¹' {b}).indicator (1 : carrier π₁ π₂ → ENNReal) p
      = canonicalWeight PΩ P₁ P₂ π₁ π₂ p *
          (fun q : Λ₁ × Λ₂ => ({b} : Set Λ₂).indicator (1 : Λ₂ → ENNReal) q.2) (p : Λ₁ × Λ₂) := by
    intro p
    by_cases h : carrier.snd π₁ π₂ p = b
    · simp only [Set.indicator_of_mem (s := carrier.snd π₁ π₂ ⁻¹' {b}) (a := p) h,
        Set.indicator_of_mem (s := ({b} : Set Λ₂)) (a := (p : Λ₁ × Λ₂).2) h, Pi.one_apply]
    · simp only [Set.indicator_of_notMem (s := carrier.snd π₁ π₂ ⁻¹' {b}) (a := p) h,
        Set.indicator_of_notMem (s := ({b} : Set Λ₂)) (a := (p : Λ₁ × Λ₂).2) h]
  rw [tsum_congr hind,
    tsum_carrier PΩ P₁ P₂ π₁ π₂ (fun q => ({b} : Set Λ₂).indicator (1 : Λ₂ → ENNReal) q.2),
    ENNReal.tsum_comm, tsum_eq_single b]
  · simp only [Set.indicator_of_mem (s := ({b} : Set Λ₂)) (a := b) rfl, Pi.one_apply, mul_one]
    exact tsum_offWeight_left PΩ P₁ P₂ π₁ π₂ h₁ h₂ b
  · intro c hc
    simp [Set.indicator_of_notMem (s := ({b} : Set Λ₂)) (a := c) (by simpa using hc)]

omit [Countable Ω] [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] in
/-- (4.57): `ρ₁` is probability preserving. -/
lemma measurePreserving_fst (h₁ : MeasurePreserving π₁ P₁ PΩ)
    (h₂ : MeasurePreserving π₂ P₂ PΩ) :
    MeasurePreserving (carrier.fst π₁ π₂) (canonicalMeasure PΩ P₁ P₂ π₁ π₂) P₁ := by
  refine ⟨carrier.measurable_fst (Ω := Ω) π₁ π₂, ?_⟩
  rw [Measure.map_eq_sum _ _ (carrier.measurable_fst (Ω := Ω) π₁ π₂)]
  simp_rw [canonicalMeasure_preimage_fst PΩ P₁ P₂ π₁ π₂ h₁ h₂]
  exact P₁.sum_smul_dirac

omit [Countable Ω] [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] in
/-- (4.57), the other side: `ρ₂` is probability preserving. -/
lemma measurePreserving_snd (h₁ : MeasurePreserving π₁ P₁ PΩ)
    (h₂ : MeasurePreserving π₂ P₂ PΩ) :
    MeasurePreserving (carrier.snd π₁ π₂) (canonicalMeasure PΩ P₁ P₂ π₁ π₂) P₂ := by
  refine ⟨carrier.measurable_snd (Ω := Ω) π₁ π₂, ?_⟩
  rw [Measure.map_eq_sum _ _ (carrier.measurable_snd (Ω := Ω) π₁ π₂)]
  simp_rw [canonicalMeasure_preimage_snd PΩ P₁ P₂ π₁ π₂ h₁ h₂]
  exact P₂.sum_smul_dirac

omit [Countable Ω] [IsProbabilityMeasure P₂] in
/-- The fibre product inherits Definition 3.1's **finite entropy** from the two spaces it
amalgamates.  The fibre product embeds in `Λ₁ × Λ₂`, whose law has finite entropy by
subadditivity, and finite entropy passes back along an injection
(`ShannonInformation.finiteEntropyMeasure_of_injective`).

Not a paper node: Definition 4.11 says "countable discrete probability space", and it is
Definition 3.1 — applied to the latent variable models of Definition 4.12(2), which live on
`Λ₀` — that asks for finite entropy.  This lemma is what discharges that field for the
construction of Lemma 4.13. -/
lemma finiteEntropyMeasure_canonicalMeasure
    [ShannonInformation.FiniteEntropyMeasure P₁] [ShannonInformation.FiniteEntropyMeasure P₂]
    (h₁ : MeasurePreserving π₁ P₁ PΩ) (h₂ : MeasurePreserving π₂ P₂ PΩ) :
    ShannonInformation.FiniteEntropyMeasure (canonicalMeasure PΩ P₁ P₂ π₁ π₂) := by
  haveI : IsProbabilityMeasure (canonicalMeasure PΩ P₁ P₂ π₁ π₂) :=
    isProbabilityMeasure_canonicalMeasure PΩ P₁ P₂ π₁ π₂ h₁ h₂
  haveI hfst : ShannonInformation.FiniteEntropyOf (carrier.fst π₁ π₂)
      (canonicalMeasure PΩ P₁ P₂ π₁ π₂) := by
    show ShannonInformation.FiniteEntropyMeasure _
    rw [(measurePreserving_fst PΩ P₁ P₂ π₁ π₂ h₁ h₂).map_eq]
    infer_instance
  haveI hsnd : ShannonInformation.FiniteEntropyOf (carrier.snd π₁ π₂)
      (canonicalMeasure PΩ P₁ P₂ π₁ π₂) := by
    show ShannonInformation.FiniteEntropyMeasure _
    rw [(measurePreserving_snd PΩ P₁ P₂ π₁ π₂ h₁ h₂).map_eq]
    infer_instance
  haveI hval : ShannonInformation.FiniteEntropyOf
      (Subtype.val : carrier π₁ π₂ → Λ₁ × Λ₂) (canonicalMeasure PΩ P₁ P₂ π₁ π₂) := by
    have hv : (Subtype.val : carrier π₁ π₂ → Λ₁ × Λ₂)
        = fun p ↦ (carrier.fst π₁ π₂ p, carrier.snd π₁ π₂ p) := funext fun _ ↦ rfl
    rw [ShannonInformation.FiniteEntropyOf, hv]
    exact ShannonInformation.finiteEntropyOf_pair (carrier.measurable_fst (Ω := Ω) π₁ π₂)
      (carrier.measurable_snd (Ω := Ω) π₁ π₂)
  exact ShannonInformation.finiteEntropyMeasure_of_injective measurable_subtype_coe
    Subtype.val_injective

/-- The canonical amalgamation of a cospan: the fibre product (4.49) with the measure
(4.53).  This is the *construction* half of Lemma 4.13; `nonempty_amalgamation` is the
existence statement it witnesses.

Paper node: `Lemma 4.13` -/
noncomputable def canonical (h₁ : MeasurePreserving π₁ P₁ PΩ)
    (h₂ : MeasurePreserving π₂ P₂ PΩ) :
    Amalgamation.{u, max u₁ u₂, u₁, u₂} PΩ P₁ P₂ π₁ π₂ where
  π₁_pres := h₁
  π₂_pres := h₂
  Λ₀ := carrier π₁ π₂
  P₀ := canonicalMeasure PΩ P₁ P₂ π₁ π₂
  probP₀ := isProbabilityMeasure_canonicalMeasure PΩ P₁ P₂ π₁ π₂ h₁ h₂
  ρ₁ := carrier.fst π₁ π₂
  ρ₂ := carrier.snd π₁ π₂
  ρ₁_pres := measurePreserving_fst PΩ P₁ P₂ π₁ π₂ h₁ h₂
  ρ₂_pres := measurePreserving_snd PΩ P₁ P₂ π₁ π₂ h₁ h₂
  comm := carrier.comm π₁ π₂

end Amalgamation

/-- **Lemma 4.13**, first half: every cospan of probability-preserving maps between
countable discrete probability spaces admits an amalgamation.

Paper node: `Lemma 4.13` -/
theorem nonempty_amalgamation {Ω : Type u} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] {Λ₁ : Type u₁} [MeasurableSpace Λ₁] [Countable Λ₁]
    [MeasurableSingletonClass Λ₁] {Λ₂ : Type u₂} [MeasurableSpace Λ₂] [Countable Λ₂]
    [MeasurableSingletonClass Λ₂] (PΩ : Measure Ω) (P₁ : Measure Λ₁) (P₂ : Measure Λ₂)
    [IsProbabilityMeasure PΩ] [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {π₁ : Λ₁ → Ω} {π₂ : Λ₂ → Ω} (h₁ : MeasurePreserving π₁ P₁ PΩ)
    (h₂ : MeasurePreserving π₂ P₂ PΩ) :
    Nonempty (Amalgamation.{u, max u₁ u₂, u₁, u₂} PΩ P₁ P₂ π₁ π₂) :=
  ⟨Amalgamation.canonical PΩ P₁ P₂ π₁ π₂ h₁ h₂⟩

namespace LatentAmalgamation

variable {I : Type w} [Finite I] {M : RVModel.{u, v, w} I}
  (L₁ : LatentModel.{u, v, w, u₁, v₁} M) (L₂ : LatentModel.{u, v, w, u₂, v₂} M)

/-- The canonical amalgamation of two latent variable models over a common `M`: the
fibre product `Λ₀` of (4.49) with the measure (4.53), and the pulled-back latent families
`ρₖ^* Yₖ` of (4.46), with the morphisms (4.47)/(4.48).

Paper node: `Lemma 4.13` -/
noncomputable def canonical : LatentAmalgamation.{u, v, w, max u₁ u₂, u₁, v₁, u₂, v₂} L₁ L₂ where
  Λ₀ := Amalgamation.carrier L₁.π L₂.π
  P₀ := Amalgamation.canonicalMeasure M.P L₁.P L₂.P L₁.π L₂.π
  probP₀ := Amalgamation.isProbabilityMeasure_canonicalMeasure M.P L₁.P L₂.P L₁.π L₂.π
    L₁.π_pres L₂.π_pres
  finiteEntropy_Λ₀ := Amalgamation.finiteEntropyMeasure_canonicalMeasure M.P L₁.P L₂.P
    L₁.π L₂.π L₁.π_pres L₂.π_pres
  Y₁ := fun A => L₁.Y A ∘ Amalgamation.carrier.fst L₁.π L₂.π
  measurable_Y₁ := fun A =>
    (L₁.L.measurable_X A).comp (Amalgamation.carrier.measurable_fst L₁.π L₂.π)
  finiteEntropy_Y₁ := fun A =>
    ShannonInformation.finiteEntropyOf_pullback
      (Amalgamation.measurePreserving_fst M.P L₁.P L₂.P L₁.π L₂.π L₁.π_pres L₂.π_pres)
      (L₁.L.measurable_X A)
  π₁ := L₁.π ∘ Amalgamation.carrier.fst L₁.π L₂.π
  π₁_pres := L₁.π_pres.comp (Amalgamation.measurePreserving_fst M.P L₁.P L₂.P L₁.π L₂.π
    L₁.π_pres L₂.π_pres)
  contributes₁ := fun i =>
    (L₁.contributes i).comp_measurePreserving
      (Amalgamation.measurePreserving_fst M.P L₁.P L₂.P L₁.π L₂.π L₁.π_pres L₂.π_pres)
  Y₂ := fun A => L₂.Y A ∘ Amalgamation.carrier.snd L₁.π L₂.π
  measurable_Y₂ := fun A =>
    (L₂.L.measurable_X A).comp (Amalgamation.carrier.measurable_snd L₁.π L₂.π)
  finiteEntropy_Y₂ := fun A =>
    ShannonInformation.finiteEntropyOf_pullback
      (Amalgamation.measurePreserving_snd M.P L₁.P L₂.P L₁.π L₂.π L₁.π_pres L₂.π_pres)
      (L₂.L.measurable_X A)
  π₂ := L₂.π ∘ Amalgamation.carrier.snd L₁.π L₂.π
  π₂_pres := L₂.π_pres.comp (Amalgamation.measurePreserving_snd M.P L₁.P L₂.P L₁.π L₂.π
    L₁.π_pres L₂.π_pres)
  contributes₂ := fun i =>
    (L₂.contributes i).comp_measurePreserving
      (Amalgamation.measurePreserving_snd M.P L₁.P L₂.P L₁.π L₂.π L₁.π_pres L₂.π_pres)
  ρ₁ := Amalgamation.carrier.fst L₁.π L₂.π
  ρ₁_pres := Amalgamation.measurePreserving_fst M.P L₁.P L₂.P L₁.π L₂.π L₁.π_pres L₂.π_pres
  ρ₁_Y := fun _ => Filter.Eventually.of_forall fun _ => rfl
  ρ₂ := Amalgamation.carrier.snd L₁.π L₂.π
  ρ₂_pres := Amalgamation.measurePreserving_snd M.P L₁.P L₂.P L₁.π L₂.π L₁.π_pres L₂.π_pres
  ρ₂_Y := fun _ => Filter.Eventually.of_forall fun _ => rfl
  comm := Filter.Eventually.of_forall fun p => p.2

end LatentAmalgamation

/-- **Lemma 4.13**, second half: any two latent variable models for the same random
variable model admit an amalgamation in the sense of Definition 4.12.

Paper node: `Lemma 4.13` -/
theorem nonempty_latentAmalgamation {I : Type w} [Finite I] {M : RVModel.{u, v, w} I}
    (L₁ : LatentModel.{u, v, w, u₁, v₁} M) (L₂ : LatentModel.{u, v, w, u₂, v₂} M) :
    Nonempty (LatentAmalgamation.{u, v, w, max u₁ u₂, u₁, v₁, u₂, v₂} L₁ L₂) :=
  ⟨LatentAmalgamation.canonical L₁ L₂⟩

end Condensation
