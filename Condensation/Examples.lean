import Condensation.Model

/-!
# Condensation — constructed inhabitants

Non-vacuity witnesses for the boundary structures of §3 (repo standard: every boundary
structure gets a *constructed* inhabitant, never a stand-in).

The witness here is the fair coin: `Ω = Bool` under the uniform measure, one random
variable observing it, and the `L₂`-shaped latent variable model of Example 4.1 over it —
`Λ = Ω`, `π = id`, and the single latent `Y_{i}` equal to `X_i`.  Its entropy is
`log 2 > 0`, so the witness is not the degenerate zero-entropy model: every score defined
in `Model.lean` takes a genuinely positive value on it.

Example 4.1 and Example 4.4 of the paper get their own annotated declarations when §4
lands; nothing here carries a paper-node annotation.
-/

namespace Condensation

-- `Real` is deliberately *not* opened: it would make `π` notation for `Real.pi`, which
-- collides with `LatentModel`'s field name `π` in structure-instance syntax.
open MeasureTheory ProbabilityTheory

/-! ## The fair coin as a random variable model -/

/-- The uniform measure on `Bool`. -/
noncomputable def coinMeasure : Measure Bool := uniformOn (Set.univ : Set Bool)

instance : IsProbabilityMeasure coinMeasure := by
  unfold coinMeasure; infer_instance

/-- The fair coin as a random variable model with a single variable: `Ω = Bool` with the
uniform measure, indexed by `Unit`, and `X () = id`. -/
noncomputable def coinModel : RVModel Unit where
  Ω := Bool
  P := coinMeasure
  R := fun _ => Bool
  X := fun _ => id
  measurable_X := fun _ => measurable_id
  finiteRange_X := fun _ => inferInstance

@[simp] lemma coinModel_X (i : Unit) : coinModel.X i = id := rfl

@[simp] lemma coinModel_P : coinModel.P = coinMeasure := rfl

/-- The fair coin has entropy `log 2`, so `coinModel` is not the degenerate model in which
every information quantity vanishes. -/
lemma coinModel_entropy : H[coinModel.X () ; coinModel.P] = Real.log 2 := by
  show H[(id : Bool → Bool) ; coinMeasure] = Real.log 2
  have huniform : IsUniform (Set.univ : Set Bool) (id : Bool → Bool) coinMeasure :=
    isUniform_uniformOn
  have h := huniform.entropy_eq' Set.finite_univ measurable_id
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h

lemma coinModel_entropy_pos : 0 < H[coinModel.X () ; coinModel.P] := by
  rw [coinModel_entropy]; exact Real.log_pos (by norm_num)

/-! ## The `L₂`-shaped latent variable model over it

`P⁺ Unit` has a single element, `{()}`, so the latent family is a single variable, taken
to be the coin itself.  `π` is the identity, which is trivially measure preserving, and
the contribution condition holds because `Y_{()} = X_()` on the nose. -/

/-- The latent random variable model: `Λ = Bool` with the uniform measure and one latent
variable per element of `P⁺ Unit`, each equal to the coin. -/
noncomputable def coinLatentRV : RVModel (PPlus Unit) where
  Ω := Bool
  P := coinMeasure
  R := fun _ => Bool
  X := fun _ => id
  measurable_X := fun _ => measurable_id
  finiteRange_X := fun _ => inferInstance

/-- The `L₂`-shaped latent variable model for `coinModel`: `Λ = Ω`, `π = id`, and the
latents recover the given variables exactly. -/
noncomputable def coinLatent : LatentModel coinModel where
  L := coinLatentRV
  π := id
  π_pres := MeasurePreserving.id _
  contributes := fun i => by
    refine ⟨fun g => g ⟨PPlus.single i, by simp⟩, measurable_of_countable _, ?_⟩
    filter_upwards with ω
    rfl

/-- Non-vacuity of `LatentModel`, spelled out: the type has an inhabitant over a model of
strictly positive entropy. -/
lemma coinLatent_nonempty : Nonempty (LatentModel coinModel) := ⟨coinLatent⟩

end Condensation
