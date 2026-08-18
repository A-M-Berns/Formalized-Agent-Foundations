import Condensation.Perfect
import ShannonInformation.FiniteEntropy.Examples

/-!
# Condensation — constructed inhabitants

Non-vacuity witnesses for the boundary structures of §3 (repo standard: every boundary
structure gets a *constructed* inhabitant, never a stand-in).

What is here, and what each witness is *for*:

* `coinModel` / `coinLatent` — the fair coin: `Ω = Bool` under the uniform measure, one
  random variable observing it, and the **`L₁`**-shaped latent variable model of Example
  4.1 over it (`Λ = Ω`, `π = id`, and the single latent `Y_{i}` equal to `X_i`).  `L₁`, not
  `L₂`: Example 4.1's `L₁` is the one that sets `Y_{i} = X_i` on singletons.  With
  `I = Unit` the two recipes happen to coincide, since `P⁺Unit = {{()}}` is at once the
  singletons and the whole index set, but the recipe followed here is `L₁`'s.
  The coin has entropy `log 2 > 0`, so this is not the degenerate zero-entropy model.
* `twoCoinLatent` — a **two-index** witness (`I = Bool`), where `P⁺I` has three elements
  and the conditioning in Definition 3.3's `χ_L` does real work: `σ = 2 log 2` while
  `χ = log 2`.  The `Unit`-indexed witness cannot show that, its `P⁺I` having a single
  element with nothing strictly above it.
* `noisyLatent` — a witness whose **reconstruction score is strictly positive**.  This one
  exists because `ϱ_L(A) = H(Y_⊇A | X_A)` vanishes whenever the latents above `A` are a
  function of `X_A`, which is the case for both witnesses above; a reader who saw only
  those could reasonably suspect `ϱ` of being identically zero.  Here the latent carries a
  fair bit of randomness that `π` discards, and `ϱ` is `log 2`.
* `LatentModel.nonempty` — non-vacuity not by example but in general: **every** random
  variable model has a latent variable model, namely the tautological `LatentModel.ofJoint`
  with `Λ = Ω`, `π = id` and `Y_A = X_A`.  This is the statement that Definition 3.2
  constrains nothing away.
* `Example.geomModel` / `Example.geomLatent` — the witness with an **infinite-range**
  variable: `Ω = ℕ` under `Geometric(1/2)`, `X_() = id`.  Every witness above has a finite
  sample space, so none of them can tell Definition 3.1's actual hypothesis apart from the
  narrowing `dd:finite-range` this library carried until 2026-08-17.  `geomModel` can:
  `geomModel_not_finiteRange` proves it is outside the narrowed class, and
  `geomModel_entropy` proves it is not degenerate (`H = 2 log 2`).

This file is the one place in `Condensation/` that imports outside
`Condensation.Perfect`'s closure: `ShannonInformation.FiniteEntropy.Examples`, for the
geometric law `geomModel` is built on.  That module is deliberately not re-exported by
`ShannonInformation.API` (it would cost every client
`Mathlib.Probability.Distributions.Geometric`), so the import has to be named here.

Beside the *structures*, the **conditions** of §4 get witnesses too, added 2026-08-18 and
collected in the "Definitions 4.3 and 4.8" section below.  Until then nothing in the library
exhibited a latent variable model that perfectly condenses anything, so Theorem 4.9,
Proposition 4.10 and Theorem 4.15 were non-vacuous only in the sense that their statements
elaborate.  Now `coinLatent_perfectlyCondenses` inhabits Definition 4.3's conditioned
clause, `coinLatent_orderedMarkov` (through Theorem 4.9's (B1 ⇒ B2)) inhabits Definition
4.8, `Example44.L44_coin_simplyPerfectlyCondenses` inhabits the simple clause and discharges
Example 4.4's joint-independence hypothesis on a constructed family, and
`noisyLatent_not_perfectlyCondenses` is the **negative** witness that perfect condensation
is a real restriction rather than a property every latent variable model has.

A caution the earlier draft of this file got wrong: it is **not** true that every score is
positive on `coinLatent`.  `coinLatent.reconScore {()} = 0`, proved below — perfect
reconstruction is exactly what `ϱ = 0` means, and the `L₁` recipe achieves it.  The
positive-`ϱ` claim needs `noisyLatent`.

Below the witnesses, §4's two examples are constructed for an **arbitrary** model — both
are `def`s taking the model, not concrete inhabitants, because that is how the paper states
them:

* `Example41.L₁` and `Example41.L₂` — the two deliberately uninformative latent variable
  models Example 4.1 associates with a given `M` (`Λ = Ω`, `π = idΩ`; `Y_{i} = X_i` with
  everything else constant, respectively `Z_I = X_I` with everything else constant),
  together with equations (4.2)–(4.5) for their simple and conditioned scores.
* `Example44.M44` and `Example44.L44` — Example 4.4's construction in the opposite
  direction: from a family `L = (Ω, (Y_A)_{A ∈ P⁺I})` of jointly independent variables, the
  model with `Xᵢ = Y_∋i` of (4.10), which `L` simply-perfectly condenses.

Those four constructions and the six equations they carry — (4.2)–(4.5), (4.11) and
Example 4.4's conclusion — are the node-annotated declarations of this file, and the only
`theorem`s in it.  The equations *are* the examples' content, so they are paper-facing
statements in the sense the surface rule means, not internal lemmas.  All six were proved
at M2 and are inventoried in `AxiomAudit.lean`'s CONDENSATION-INVENTORY block; nothing in
this file is `sorry`.  Everything else here is a `lemma` (or a `private def`, where the
thing produced is an instance rather than a proof): the non-vacuity witnesses, the
guarded-latent machinery of Example 4.1, and their supporting computations state nothing
the paper states.
-/

universe u v w

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
  finiteEntropy_X := fun _ => inferInstance

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

/-! ## The `L₁`-shaped latent variable model over it

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
  finiteEntropy_X := fun _ => inferInstance

/-- The `L₁`-shaped latent variable model for `coinModel` (Example 4.1's first recipe,
`Y_{i} = X_i`): `Λ = Ω`, `π = id`, and the latents recover the given variables exactly. -/
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
lemma coinLatent_nonempty : Nonempty (LatentModel.{0, 0, 0, 0, 0} coinModel) := ⟨coinLatent⟩

/-- The reconstruction score of `coinLatent` is **zero**, not positive: `Y_⊇{()}` is the
coin and `X_{()}` is the coin, so there is nothing left to reconstruct.  This is stated
because it is the corner a reader is likeliest to get wrong — `ϱ_L = 0` is what *perfect*
reconstruction looks like, and the `L₁` recipe achieves it.  `noisyLatent` below is the
witness that `ϱ_L` is not identically zero. -/
lemma coinLatent_reconScore : coinLatent.reconScore {()} = 0 := by
  refine condEntropy_eq_zero_of_aeFunctionOf
    (coinLatent.measurable_pullbackJoint _)
    (coinLatentRV.measurable_jointOn _) ?_
  refine ⟨fun g _ => g ⟨(), by simp⟩, measurable_of_countable _, ?_⟩
  filter_upwards with ω
  rfl

/-! ## A two-index witness, where `χ_L`'s conditioning does real work

`I = Bool`, so `P⁺I` has three elements — `{true}`, `{false}`, `{true, false}` — and the
family `{B : B ∩ {true} ≠ ∅}` of (3.1)–(3.2) has two of them, one of which has something
strictly above it and one of which does not.  Both given variables observe the same fair
coin, and every latent is that coin.  The point of the witness is the pair of proved
values `σ_L({true}) = 2 log 2` and `χ_L({true}) = log 2`: the conditioning of (3.2) kills
the `{true}` term outright (because `Y_{true}` is a function of `Y_{true,false}`) and
leaves the maximal term alone.  The `Unit`-indexed witness above cannot exhibit this, its
`P⁺I` having a single element with nothing strictly above it. -/

/-- Two given variables, both observing the same fair coin. -/
noncomputable def twoCoinModel : RVModel Bool where
  Ω := Bool
  P := coinMeasure
  R := fun _ => Bool
  X := fun _ => id
  measurable_X := fun _ => measurable_id
  finiteEntropy_X := fun _ => inferInstance

/-- The latent random variable model: one latent per element of `P⁺ Bool`, each the coin. -/
noncomputable def twoCoinLatentRV : RVModel (PPlus Bool) where
  Ω := Bool
  P := coinMeasure
  R := fun _ => Bool
  X := fun _ => id
  measurable_X := fun _ => measurable_id
  finiteEntropy_X := fun _ => inferInstance

/-- The latent variable model for `twoCoinModel`: `Λ = Ω`, `π = id`, every latent is the
coin. -/
noncomputable def twoCoinLatent : LatentModel twoCoinModel where
  L := twoCoinLatentRV
  π := id
  π_pres := MeasurePreserving.id _
  contributes := fun i => by
    refine ⟨fun g => g ⟨PPlus.single i, by simp⟩, measurable_of_countable _, ?_⟩
    filter_upwards with ω
    rfl

/-- `{true} ∈ P⁺ Bool`. -/
def twoCoinT : PPlus Bool := ⟨{true}, Finset.singleton_nonempty _⟩

/-- `{true, false} ∈ P⁺ Bool`, the maximum of `P⁺ Bool`. -/
def twoCoinTF : PPlus Bool := ⟨{true, false}, ⟨true, by decide⟩⟩

lemma twoCoinT_ne_twoCoinTF : twoCoinT ≠ twoCoinTF := by decide

/-- The latents contributing to `{true}` are exactly `{true}` and `{true, false}`. -/
lemma twoCoin_famFinset_contrib :
    famFinset (contrib ({true} : Finset Bool)) = {twoCoinT, twoCoinTF} := by
  ext B
  simp only [mem_famFinset, mem_contrib, Finset.mem_singleton, exists_eq_left, PPlus.mem_iff,
    Finset.mem_insert]
  revert B
  decide

/-- Every latent of the two-coin witness is the fair coin, of entropy `log 2`. -/
lemma twoCoinLatent_entropy (B : PPlus Bool) :
    H[twoCoinLatent.Y B ; twoCoinLatent.P] = Real.log 2 := by
  show H[(id : Bool → Bool) ; coinMeasure] = Real.log 2
  have huniform : IsUniform (Set.univ : Set Bool) (id : Bool → Bool) coinMeasure :=
    isUniform_uniformOn
  have h := huniform.entropy_eq' Set.finite_univ measurable_id
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h

/-- `σ_L({true}) = 2 log 2` — two contributing latents, each a fair coin. -/
lemma twoCoinLatent_simpleScore :
    twoCoinLatent.simpleScore ({true} : Finset Bool) = 2 * Real.log 2 := by
  rw [LatentModel.simpleScore, twoCoin_famFinset_contrib,
    Finset.sum_pair twoCoinT_ne_twoCoinTF, twoCoinLatent_entropy, twoCoinLatent_entropy]
  ring

/-- `Y_{true}` is a.e. a function of `Y_⊋{true}`, since `{true, false} ⊋ {true}`. -/
lemma twoCoinLatent_condEntropy_T :
    H[twoCoinLatent.Y twoCoinT | twoCoinLatent.jointStrictAbove twoCoinT.toFinset ;
      twoCoinLatent.P] = 0 := by
  have hmem : twoCoinTF ∈ strictAbove twoCoinT.toFinset := by
    show twoCoinT.toFinset ⊂ twoCoinTF.toFinset
    decide
  refine condEntropy_eq_zero_of_aeFunctionOf
    (twoCoinLatent.L.measurable_jointOn _) (twoCoinLatent.L.measurable_X _) ?_
  refine ⟨fun g => g ⟨twoCoinTF, hmem⟩, measurable_of_countable _, ?_⟩
  filter_upwards with ω
  rfl

/-- Nothing strictly contains `{true, false}`. -/
instance : IsEmpty (strictAbove twoCoinTF.toFinset) :=
  ⟨fun C => (by decide : ∀ D : PPlus Bool, ¬ twoCoinTF.toFinset ⊂ D.toFinset) C.1 C.2⟩

/-- `Y_⊋{true,false}` is a variable into a subsingleton, so it does not reduce entropy. -/
lemma twoCoinLatent_condEntropy_TF :
    H[twoCoinLatent.Y twoCoinTF | twoCoinLatent.jointStrictAbove twoCoinTF.toFinset ;
      twoCoinLatent.P] = Real.log 2 := by
  rw [condEntropy_eq_entropy_of_subsingleton (twoCoinLatent.L.measurable_X _),
    twoCoinLatent_entropy]

/-- `χ_L({true}) = log 2` — the conditioning kills the `{true}` term. -/
lemma twoCoinLatent_condScore :
    twoCoinLatent.condScore ({true} : Finset Bool) = Real.log 2 := by
  rw [LatentModel.condScore, twoCoin_famFinset_contrib,
    Finset.sum_pair twoCoinT_ne_twoCoinTF, twoCoinLatent_condEntropy_T,
    twoCoinLatent_condEntropy_TF, zero_add]

/-- The conditioning of (3.2) does real work here: `0 < χ_L < σ_L`. -/
lemma twoCoinLatent_condScore_lt_simpleScore :
    0 < twoCoinLatent.condScore ({true} : Finset Bool) ∧
      twoCoinLatent.condScore ({true} : Finset Bool) <
        twoCoinLatent.simpleScore ({true} : Finset Bool) := by
  rw [twoCoinLatent_condScore, twoCoinLatent_simpleScore]
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact ⟨h, by linarith⟩

/-- The reconstruction score degenerates here too: `Y_⊇{true}` is a function of
`π^* X_{true}`, so there is nothing left to reconstruct.  `noisyLatent` below is the
witness that `ϱ_L` is not identically zero. -/
lemma twoCoinLatent_reconScore :
    twoCoinLatent.reconScore ({true} : Finset Bool) = 0 := by
  have hmem : true ∈ ({true} : Finset Bool) := by decide
  refine condEntropy_eq_zero_of_aeFunctionOf
    (twoCoinLatent.measurable_pullbackJoint _) (twoCoinLatent.L.measurable_jointOn _) ?_
  refine ⟨fun g _ => g ⟨true, hmem⟩, measurable_of_countable _, ?_⟩
  filter_upwards with ω
  rfl

/-! ## A witness with a strictly positive reconstruction score

Every witness above has `ϱ_L = 0`, and that is not an accident: `ϱ_L(A) = H(Y_⊇A | X_A)`
vanishes exactly when the latents above `A` are a.e. a function of `X_A`, which holds for
any latent system built out of the observables on the same sample space.  So a reader who
saw only those could reasonably suspect `ϱ_L` of being identically zero.  It is not.

Here `Λ = Bool × Bool` carries two independent fair bits, `π = Prod.fst` throws the second
away, and the single latent `Y_{()}` is the whole latent state.  `X_()` is still a.e. a
function of `Y_{()}` — Definition 3.2 is satisfied — but the reverse fails, and
`ϱ_L({()}) = log 2`. -/

/-- The uniform measure on two independent fair bits. -/
noncomputable def noisyMeasure : Measure (Bool × Bool) :=
  uniformOn (Set.univ : Set (Bool × Bool))

instance : IsProbabilityMeasure noisyMeasure := by
  unfold noisyMeasure; infer_instance

/-- The observable measure: the pushforward of `noisyMeasure` along the first coordinate.
Taking the pushforward *as the definition* is what makes `π_pres` the identity proof. -/
noncomputable def noisyObsMeasure : Measure Bool := noisyMeasure.map Prod.fst

instance : IsProbabilityMeasure noisyObsMeasure :=
  Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

/-- The observable model: `Ω = Bool` carrying the pushforward measure, one variable. -/
noncomputable def noisyModel : RVModel Unit where
  Ω := Bool
  P := noisyObsMeasure
  R := fun _ => Bool
  X := fun _ => id
  measurable_X := fun _ => measurable_id
  finiteEntropy_X := fun _ => inferInstance

/-- The latent model: `Λ = Bool × Bool` uniform, the single latent being the identity. -/
noncomputable def noisyLatentRV : RVModel (PPlus Unit) where
  Ω := Bool × Bool
  P := noisyMeasure
  R := fun _ => Bool × Bool
  X := fun _ => id
  measurable_X := fun _ => measurable_id
  finiteEntropy_X := fun _ => inferInstance

/-- The latent variable model whose latent keeps a bit that `π` discards. -/
noncomputable def noisyLatent : LatentModel noisyModel where
  L := noisyLatentRV
  π := Prod.fst
  π_pres := ⟨measurable_fst, rfl⟩
  contributes := fun i => by
    refine ⟨fun g => (g ⟨PPlus.single i, by simp⟩).1, measurable_of_countable _, ?_⟩
    filter_upwards with ω
    rfl

lemma noisy_fst_preimage (x : Bool) :
    (Prod.fst ⁻¹' {x} : Set (Bool × Bool)) = {(x, false), (x, true)} := by
  ext ⟨a, b⟩
  cases b <;> simp [eq_comm]

lemma noisy_measure_fst_preimage (x : Bool) :
    noisyMeasure (Prod.fst ⁻¹' {x}) = 2 / 4 := by
  rw [noisyMeasure, uniformOn_apply Set.finite_univ, Set.univ_inter, noisy_fst_preimage,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_univ,
    Set.ncard_pair (by simp)]
  norm_num

lemma noisy_isUniform_fst : IsUniform (Set.univ : Set Bool) Prod.fst noisyMeasure where
  eq_of_mem := by
    intro x _ y _
    rw [noisy_measure_fst_preimage, noisy_measure_fst_preimage]
  measure_preimage_compl := by
    rw [Set.compl_univ, Set.preimage_empty, measure_empty]

lemma noisy_entropy_fst : H[Prod.fst ; noisyMeasure] = Real.log 2 := by
  have h := noisy_isUniform_fst.entropy_eq' Set.finite_univ measurable_fst
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h

lemma noisy_entropy_id :
    H[(id : Bool × Bool → Bool × Bool) ; noisyMeasure] = 2 * Real.log 2 := by
  have huniform : IsUniform (Set.univ : Set (Bool × Bool)) (id : Bool × Bool → Bool × Bool)
      noisyMeasure := isUniform_uniformOn
  have h := huniform.entropy_eq' Set.finite_univ measurable_id
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h
  rw [h, show ((Fintype.card (Bool × Bool) : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- Instance search does not unfold `noisyLatentRV` to see that `Λ` is finite. -/
instance : Finite noisyLatent.Λ := inferInstanceAs (Finite (Bool × Bool))

/-- The pullback `π^* X_{()}` is the first coordinate, up to a bijective relabelling. -/
lemma noisy_entropy_pullback :
    H[noisyLatent.pullbackJoint ({()} : Finset Unit) ; noisyLatent.P] = Real.log 2 := by
  have h : H[noisyLatent.pullbackJoint ({()} : Finset Unit) ; noisyLatent.P]
      = H[(Prod.fst : Bool × Bool → Bool) ; noisyMeasure] :=
    (ShannonInformation.entropy_of_comp_eq_of_comp (μ := noisyLatent.P) measurable_fst
      (noisyLatent.measurable_pullbackJoint _) (fun b _ => b)
      (fun t => t ⟨(), Finset.mem_singleton_self ()⟩) rfl rfl).symm
  rw [h, noisy_entropy_fst]

/-- The pair `(Y_⊇A, π^* X_A)` determines and is determined by the latent state. -/
lemma noisy_entropy_pair :
    H[⟨noisyLatent.jointAbove ({()} : Finset Unit),
        noisyLatent.pullbackJoint ({()} : Finset Unit)⟩ ; noisyLatent.P] = 2 * Real.log 2 := by
  -- The conditioning variable is a *pair*, and `finiteEntropyOf_pair` is a lemma, not an
  -- instance; `RVModel.finiteEntropyOf` gets it in one step from Definition 3.1's `Ω`.
  haveI : ShannonInformation.FiniteEntropyOf
      (fun ω => (noisyLatent.L.jointOn (above ({()} : Finset Unit)) ω,
        noisyLatent.pullbackJoint ({()} : Finset Unit) ω)) noisyLatent.P :=
    noisyLatent.L.finiteEntropyOf
      ((noisyLatent.L.measurable_jointOn _).prodMk (noisyLatent.measurable_pullbackJoint _))
  have h : H[⟨noisyLatent.jointAbove ({()} : Finset Unit),
        noisyLatent.pullbackJoint ({()} : Finset Unit)⟩ ; noisyLatent.P]
      = H[(id : Bool × Bool → Bool × Bool) ; noisyMeasure] :=
    (ShannonInformation.entropy_of_comp_eq_of_comp (μ := noisyLatent.P) measurable_id
      ((noisyLatent.L.measurable_jointOn _).prodMk (noisyLatent.measurable_pullbackJoint _))
      (fun ω => (fun _ => ω, fun _ => ω.1))
      (fun p => p.1 ⟨PPlus.single (), by simp⟩) rfl rfl).symm
  rw [h, noisy_entropy_id]

/-- **The headline**: the reconstruction score of `noisyLatent` at `A = {()}` is `log 2`. -/
lemma noisyLatent_reconScore :
    noisyLatent.reconScore ({()} : Finset Unit) = Real.log 2 := by
  rw [LatentModel.reconScore,
    ShannonInformation.chain_rule'' _ (noisyLatent.L.measurable_jointOn _)
      (noisyLatent.measurable_pullbackJoint _),
    noisy_entropy_pair, noisy_entropy_pullback]
  ring

/-- `ϱ_L` is **not** identically zero: here the latents are not recoverable from the
observables, and the reconstruction score is strictly positive. -/
lemma noisyLatent_reconScore_pos : 0 < noisyLatent.reconScore ({()} : Finset Unit) := by
  rw [noisyLatent_reconScore]
  exact Real.log_pos (by norm_num)

/-- `P⁺ Unit` is a singleton. -/
lemma noisy_pplus_eq (B : PPlus Unit) : B = PPlus.single () := by
  obtain ⟨u, hu⟩ := B.nonempty
  refine PPlus.ext (Finset.ext fun a => ?_)
  exact ⟨fun _ => Finset.mem_singleton_self (), fun _ => hu⟩

lemma noisy_famFinset : famFinset (contrib ({()} : Finset Unit)) = {PPlus.single ()} := by
  ext B
  simp only [mem_famFinset, Finset.mem_singleton]
  refine ⟨fun _ => noisy_pplus_eq B, fun _ => ?_⟩
  obtain ⟨u, hu⟩ := B.nonempty
  exact ⟨(), Finset.mem_singleton_self (), hu⟩

lemma noisy_entropy_Y (B : PPlus Unit) :
    H[noisyLatent.Y B ; noisyLatent.P] = 2 * Real.log 2 := noisy_entropy_id

/-- The **simple score**: `σ_L({()}) = H(Y_{()}) = log 4`. -/
lemma noisyLatent_simpleScore :
    noisyLatent.simpleScore ({()} : Finset Unit) = 2 * Real.log 2 := by
  rw [LatentModel.simpleScore, noisy_famFinset, Finset.sum_singleton, noisy_entropy_Y]

lemma noisy_strictAbove : strictAbove ({()} : Finset Unit) = ∅ := by
  ext B
  simp only [mem_strictAbove, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨a, _, ha⟩ := Finset.exists_of_ssubset h
  exact ha (Finset.mem_singleton_self ())

lemma noisy_strictAbove' :
    strictAbove (PPlus.single () : PPlus Unit).toFinset = (∅ : Set (PPlus Unit)) := by
  rw [PPlus.toFinset_single]
  exact noisy_strictAbove

lemma noisy_jointStrictAbove_const (ω ω' : noisyLatent.Λ) :
    noisyLatent.jointStrictAbove (PPlus.single () : PPlus Unit).toFinset ω
      = noisyLatent.jointStrictAbove (PPlus.single () : PPlus Unit).toFinset ω' := by
  funext B
  have hB : (↑B : PPlus Unit) ∈ (∅ : Set (PPlus Unit)) := by
    rw [← noisy_strictAbove']
    exact B.2
  exact hB.elim

/-- The **conditioned score**: `Y_⊋{()}` is empty, so `χ_L({()}) = σ_L({()}) = log 4`. -/
lemma noisyLatent_condScore :
    noisyLatent.condScore ({()} : Finset Unit) = 2 * Real.log 2 := by
  rw [LatentModel.condScore, noisy_famFinset, Finset.sum_singleton]
  -- Cite the FAF version in full: `h.condEntropy_eq_entropy` resolves in the head symbol's
  -- namespace, `ProbabilityTheory`, and so always finds the `FiniteRange` original — which
  -- no longer has a structure instance to feed it, `RVModel`'s finiteness field being
  -- `FiniteEntropyOf` (and instance search will not unfold `noisyLatentRV` to see that the
  -- latent range is `Bool × Bool`).
  have hconst : noisyLatent.jointStrictAbove (PPlus.single () : PPlus Unit).toFinset
      = fun _ => noisyLatent.jointStrictAbove (PPlus.single () : PPlus Unit).toFinset
          ((true, true) : Bool × Bool) :=
    funext fun ω => noisy_jointStrictAbove_const ω _
  rw [hconst,
    ShannonInformation.IndepFun.condEntropy_eq_entropy (indepFun_const_right _ _)
      (noisyLatent.L.measurable_X (PPlus.single ())) measurable_const,
    noisy_entropy_Y]

/-! ## Definitions 4.3 and 4.8 — witnesses on both sides

`PerfectlyCondenses`, `SimplyPerfectlyCondenses` (Definition 4.3) and `OrderedMarkov`
(Definition 4.8) are the standing hypotheses of Theorem 4.9, Proposition 4.10 and Theorem
4.15.  Until this section nothing in the library exhibited a latent variable model
satisfying any of them, so those results were non-vacuous only in the weak sense that their
*statements* elaborate — the boundary structures had inhabitants, the conditions on them
did not.  This section supplies witnesses in both directions.

* `coinLatent_perfectlyCondenses` — the fair coin's `L₁`-shaped latent variable model
  perfectly condenses `coinModel`.  There is one latent, it *is* the coin, the coin is the
  only observable, and nothing strictly contains `{()}` in `P⁺Unit`, so `χ_L({()})` is the
  bare `H(Y_{()}) = log 2 = H(X_{()})`.  Theorem 4.9's (B1 ⇒ B2) then hands over the
  ordered Markov condition for free (`coinLatent_orderedMarkov`), so Definition 4.8 is
  inhabited too.
* `Example44.L44_coin_simplyPerfectlyCondenses` — the *simple* clause of Definition 4.3,
  and with it the joint-independence hypothesis of `Example44.simplyPerfectlyCondenses`,
  which no previous declaration discharged for a concrete family.  Over the one-element
  index type `P⁺Unit` joint independence is automatic (`iIndepFun_of_subsingleton`), so
  Example 4.4's construction applies to the coin's latent family on the nose.
* `noisyLatent_not_perfectlyCondenses` — the **negative** witness, and the reason the
  positive ones are worth having: perfect condensation is a real condition, not one every
  latent variable model happens to satisfy.  Here `χ_L({()}) = 2 log 2` while
  `H(X_{()}) = log 2`; the gap is exactly the bit `π = Prod.fst` discards, which the score
  counts and the observables cannot see.

The `Unit`-indexed combinatorics these proofs run on — that `{()}` is the only element of
`P⁺Unit`, that `contrib {()}` is `{{()}}` and that `strictAbove {()}` is empty — is already
proved above for `noisyLatent` (`noisy_pplus_eq`, `noisy_famFinset`, `noisy_strictAbove'`);
none of it mentions a model, so it is reused here rather than restated.  That is also why
this section sits below the `noisyLatent` block rather than beside `coinLatent`. -/

section Definition43

/-- `P⁺Unit` is a one-element type.  Registered as an instance because it is what makes
joint independence of the coin's latent family automatic, via
`iIndepFun_of_subsingleton`. -/
instance : Subsingleton (PPlus Unit) :=
  ⟨fun A B => (noisy_pplus_eq A).trans (noisy_pplus_eq B).symm⟩

/-- Nothing strictly contains `{()}`, so `Y_⊋{()}` is a variable into a one-point type.  The
`noisyLatent` block proves the underlying set equation (`noisy_strictAbove'`); this is the
instance form, which is what `condEntropy_eq_entropy_of_subsingleton` consumes. -/
instance : IsEmpty ↥(strictAbove (PPlus.single () : PPlus Unit).toFinset) :=
  Set.isEmpty_coe_sort.mpr noisy_strictAbove'

/-- Every latent of `coinLatent` is the fair coin, of entropy `log 2`. -/
lemma coinLatent_entropy (B : PPlus Unit) :
    H[coinLatent.Y B ; coinLatent.P] = Real.log 2 := by
  show H[(id : Bool → Bool) ; coinMeasure] = Real.log 2
  have huniform : IsUniform (Set.univ : Set Bool) (id : Bool → Bool) coinMeasure :=
    isUniform_uniformOn
  have h := huniform.entropy_eq' Set.finite_univ measurable_id
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h

/-- `χ_{coinLatent}({()}) = log 2`: one contributing latent, and nothing strictly above it
to condition on. -/
lemma coinLatent_condScore :
    coinLatent.condScore ({()} : Finset Unit) = Real.log 2 := by
  rw [LatentModel.condScore, noisy_famFinset, Finset.sum_singleton,
    condEntropy_eq_entropy_of_subsingleton (coinLatent.L.measurable_X _)]
  exact coinLatent_entropy _

/-- `χ_{coinLatent}(∅) = 0`: `contrib ∅` is empty, so (3.2)'s sum is the empty sum. -/
private lemma coinLatent_condScore_empty : coinLatent.condScore (∅ : Finset Unit) = 0 := by
  have hfam : famFinset (contrib (∅ : Finset Unit)) = (∅ : Finset (PPlus Unit)) := by
    ext C; simp
  rw [LatentModel.condScore, hfam, Finset.sum_empty]

/-- `H(X_∅) = 0`: the joint variable over the empty index set is constant. -/
private lemma coinModel_entropy_joint_empty :
    H[coinModel.joint (∅ : Finset Unit) ; coinModel.P] = 0 := by
  haveI : IsEmpty ((∅ : Finset Unit) : Type _) := ⟨fun i => Finset.notMem_empty i.1 i.2⟩
  have hconst : coinModel.joint (∅ : Finset Unit) =
      fun _ => (default : ∀ i : (∅ : Finset Unit), coinModel.R i) :=
    funext fun _ => Subsingleton.elim _ _
  rw [hconst, entropy_const]

/-- `Finset Unit` has exactly two elements. -/
private lemma finsetUnit_cases (A : Finset Unit) : A = ∅ ∨ A = {()} := by
  rcases A.eq_empty_or_nonempty with h | ⟨u, hu⟩
  · exact Or.inl h
  · refine Or.inr (Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun x _ => Subsingleton.elim x ()⟩)
    have hu' : u = () := Subsingleton.elim u ()
    subst hu'
    exact hu

/-- **`coinLatent` perfectly condenses `coinModel`** — a constructed inhabitant of
Definition 4.3's first clause, and so of the hypothesis of Theorem 4.15 and of (B1) in
Theorem 4.9.  Both instances of the quantifier are checked: at `A = ∅` the score and
`H(X_∅)` are both `0`, and at `A = {()}` both are `log 2`. -/
lemma coinLatent_perfectlyCondenses : coinLatent.PerfectlyCondenses := by
  intro A
  rcases finsetUnit_cases A with rfl | rfl
  · rw [coinLatent_condScore_empty, coinModel_entropy_joint_empty]
  · rw [coinLatent_condScore, coinModel.entropy_joint_singleton (), coinModel_entropy]

/-- **Definition 4.8 is inhabited**: the coin's latent family obeys the ordered Markov
condition.  Not proved by hand — it is Theorem 4.9's (B1 ⇒ B2) applied to
`coinLatent_perfectlyCondenses`, which is the cheapest honest way to get a witness for a
conditional-independence condition. -/
lemma coinLatent_orderedMarkov : coinLatent.L.OrderedMarkov :=
  ((LatentModel.perfect_tfae_B coinLatent).mp coinLatent_perfectlyCondenses).2

/-- The coin's latent family is jointly independent, for the trivial reason that `P⁺Unit`
has a single element.  This is what Example 4.4's hypothesis asks for. -/
lemma coinLatentRV_iIndepFun : iIndepFun coinLatent.L.X coinLatent.L.P :=
  iIndepFun_of_subsingleton _ _

/-- `H(X_{()}) = log 2` on the noisy model: `X_()` is the identity on `Bool` under the
pushforward of `noisyMeasure` along `π = Prod.fst`, and convention (2.2) computes its
entropy upstairs, where `noisy_entropy_pullback` already has it. -/
lemma noisyModel_entropy_joint :
    H[noisyModel.joint ({()} : Finset Unit) ; noisyModel.P] = Real.log 2 :=
  (noisyLatent.entropy_pullbackJoint ({()} : Finset Unit)).symm.trans noisy_entropy_pullback

/-- **The negative witness**: `noisyLatent` does *not* perfectly condense `noisyModel`.
The conditioned score at `{()}` is `2 log 2` — the latent carries two independent bits and
has nothing above it to be conditioned on — while `H(X_{()})` is `log 2`, the one bit `π`
keeps.  So Definition 4.3 is a genuine restriction on latent variable models, and the
positive witnesses above are not recording a triviality. -/
lemma noisyLatent_not_perfectlyCondenses : ¬ noisyLatent.PerfectlyCondenses := by
  intro h
  have hA := h ({()} : Finset Unit)
  rw [noisyLatent_condScore, noisyModel_entropy_joint] at hA
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

end Definition43

/-! ## Non-vacuity in general: every model has a latent variable model

The witnesses above are single models.  This is the general statement — Definition 3.2's
conditions are satisfiable over an *arbitrary* random variable model, so no theorem
quantifying over latent variable models is vacuous.

The construction is the tautological one: take `Λ = Ω`, `π = id`, and let the latent at
`A ∈ P⁺I` be the joint variable `X_A` of the model itself.  Then `π^* X_i = X_i` is a
function of `Y_{i} = X_{i}` on the nose, so Definition 3.2's contribution condition holds
with the projection as the witnessing function.  (Compare Example 4.1's `L₁`, which sets
`Y_{i} = X_i` and everything else constant; the difference is immaterial for non-vacuity,
and taking `Y_A = X_A` avoids transporting along `rep A = i`.) -/

namespace RVModel

variable {I : Type w} [Finite I]

/-- The latent family `Y_A := X_A`: the joint variables of `M` itself, re-indexed over
`P⁺I`.  Together with `π = id` this is a latent variable model for `M`
(`LatentModel.ofJoint`). -/
noncomputable def jointFamily (M : RVModel.{u, v, w} I) : RVModel.{u, max v w, w} (PPlus I) where
  Ω := M.Ω
  P := M.P
  R := fun A => ∀ i : A.toFinset, M.R i
  X := fun A => M.joint A.toFinset
  measurable_X := fun _ => M.measurable_joint _
  finiteEntropy_X := fun _ => inferInstance

end RVModel

namespace LatentModel

variable {I : Type w} [Finite I]

/-- The tautological latent variable model of `M`: `Λ = Ω`, `π = id`, `Y_A = X_A`. -/
noncomputable def ofJoint (M : RVModel.{u, v, w} I) : LatentModel M where
  L := M.jointFamily
  π := id
  π_pres := MeasurePreserving.id _
  contributes := fun i => by
    refine ⟨fun g => g ⟨PPlus.single i, by simp [contribIdx]⟩ ⟨i, by simp⟩,
      measurable_of_countable _, ?_⟩
    filter_upwards with ω
    rfl

/-- **Every** random variable model has a latent variable model: Definition 3.2 is
satisfiable over an arbitrary `M`, so nothing quantifying over `LatentModel M` is vacuous.

The universe list is explicit because the conclusion is an *existence* statement over a
universe-polymorphic type, so `u'`/`v'` would otherwise be free; `Nonempty (RVModel.{u,v,w} I)`
needs the same treatment.  Here they are instantiated at `M`'s own universes, except that
the latent ranges are dependent products over subsets of `I` and so land in
`Type (max v w)`. -/
lemma nonempty (M : RVModel.{u, v, w} I) :
    Nonempty (LatentModel.{u, v, w, u, max v w} M) := ⟨ofJoint M⟩

end LatentModel

/-! ## A witness Definition 3.1 admits and `dd:finite-range` excluded

Every witness above lives on a finite sample space, so every variable in it has finite
range.  That makes them silent on exactly the point Definition 3.1 turns on: the definition
asks for a countable discrete probability space **with finite entropy**, carrying variables
with countable discrete range — it does *not* ask for finite range.  Until 2026-08-17 this
library narrowed it to `FiniteRange` variables (`dd:finite-range`, now retired), and no
witness above can tell the two readings apart.

`geomModel` can.  It is `Ω = ℕ` under the geometric law with success probability `1/2`,
with one variable reading off the sample point: a model in Definition 3.1's sense
(`ShannonInformation.finiteEntropyMeasure_geom`) and **not** one in the narrowed sense
(`geomModel_not_finiteRange`).  So it is the evidence that retiring the narrowing has
content rather than being a re-spelling.  `geomModel_entropy` rules out the degenerate
reading in which the witness is admitted only because it carries no information: the
entropy is `2 log 2`, the textbook two bits of `Geometric(1/2)`.

The section sits here, after `LatentModel.ofJoint`, rather than beside the fair coin,
because `geomLatent` *is* `ofJoint geomModel` — there is nothing model-specific to say
about the latent side of this witness, and spelling the tautological construction out again
by hand would only obscure that.

The geometric law itself, its finite-entropy instances and the entropy computation live in
`ShannonInformation/FiniteEntropy/Examples.lean`, shared with
`APITests/ShannonInformationFiniteEntropy.lean`; none of it is restated here. -/

namespace Example

/-- **A random variable model with an infinite-range variable**: `Ω = ℕ` carrying the
geometric law with success probability `1/2`, indexed by `Unit`, with `X () = id`.

Definition 3.1 asks for a countable discrete probability space with finite entropy and
variables with countable discrete range.  `ℕ` is countable and discrete, `geom` has finite
entropy, and `id` has countable discrete range — but *not* finite range.  This is therefore
a model Definition 3.1 admits and the retired `dd:finite-range` narrowing excluded. -/
noncomputable def geomModel : RVModel Unit where
  Ω := ℕ
  P := ShannonInformation.geom
  R := fun _ => ℕ
  X := fun _ => id
  measurable_X := fun _ => measurable_id
  finiteEntropy_X := fun _ => ShannonInformation.finiteEntropyOf_id_geom

@[simp] lemma geomModel_X (i : Unit) : geomModel.X i = id := rfl

@[simp] lemma geomModel_P : geomModel.P = ShannonInformation.geom := rfl

/-- **The point of the witness**: `geomModel` is not a model of the retired
`dd:finite-range` class.  Its variable is injective on an infinite sample space, so its
range is infinite and no `FiniteRange`-gated theorem applies to it. -/
lemma geomModel_not_finiteRange : ¬ FiniteRange (geomModel.X ()) :=
  ShannonInformation.not_finiteRange_id

/-- …and the witness is not degenerate: its entropy is `2 log 2`, so it is not admitted
merely for carrying no information.  The finite-sample-space counterpart is
`coinModel_entropy`. -/
lemma geomModel_entropy : H[geomModel.X () ; geomModel.P] = 2 * Real.log 2 :=
  ShannonInformation.entropy_geom

lemma geomModel_entropy_pos : 0 < H[geomModel.X () ; geomModel.P] :=
  ShannonInformation.entropy_geom_pos

/-- A latent variable model over the infinite-range witness, so that Definition 3.2 is
exhibited outside the finite-range fragment too.  It is the tautological `ofJoint`
construction, which applies to any model at all; nothing here is special to `geomModel`. -/
noncomputable def geomLatent : LatentModel geomModel := LatentModel.ofJoint geomModel

/-- The scores of Definition 3.3 are real numbers on this witness, and computable: `ϱ_L`
degenerates here for the same reason it does on `coinLatent`, since `Y_⊇{()}` is built from
the observables on `Λ = Ω`.  (`noisyLatent` remains the witness that `ϱ_L` is not
identically zero; that phenomenon is orthogonal to finite range.) -/
lemma geomLatent_reconScore : geomLatent.reconScore {()} = 0 := by
  refine condEntropy_eq_zero_of_aeFunctionOf
    (geomLatent.measurable_pullbackJoint _)
    (geomLatent.L.measurable_jointOn _) ?_
  refine ⟨fun g _ _ => g ⟨(), by simp⟩, measurable_of_countable _, ?_⟩
  filter_upwards with ω
  rfl

end Example

/-! ## Example 4.1 — the two uninformative latent variable models of an arbitrary `M`

Example 4.1 is stated for an *arbitrary* random variable model `M = (Ω, (Xᵢ)ᵢ∈I)`, so
`L₁` and `L₂` below are `def`s taking `M`, not concrete witnesses.  Both take `Λ = Ω` and
`π = idΩ`, per (4.1); they differ in the latent family.

**How "let `Y_A` be constant" is spelled.**  Both families are *guarded dependent
products*: the latent range at `A` is `∀ j : G A, M.R j` where `G A` is a subtype of `I`
carrying the guard as its defining property.  When the guard fails, `G A` is empty, the
product is a one-point type, and `Y_A` is literally the unique such function — the paper's
"constant".  When it holds, `G A` names exactly the given variables the paper puts there.

The alternative spelling — `R_A := if |A| = 1 then M.R (rep A) else PUnit`, with `rep A`
the unique element of a singleton — was tried and rejected.  It is *more* literal (it gives
`Y_{i} = X_i` on the nose rather than the one-element family `(X_i)`), but it costs twice:
the `contributes` field then has to transport along `rep {i} = i`, which is propositional
and not definitional (`Finset.Nonempty.choose` is `Classical.choose`, which does not
reduce), and every downstream computation with `Y_B` at a *variable* `B` has to case-split
a `Decidable` instance sitting inside a *type*, with a dependent motive.  The guarded
product has none of that: `Y_B = fun ω j => M.X j ω` uniformly in `B`, and the case
distinction is relocated to the (propositional, `Finset`-level) question of whether the
index type `G B` is empty.  The re-indexing this costs — `Y_{i}` is `X_i` carried by a
one-point index type rather than `X_i` itself — is entropy-invariant, and equations
(4.2)–(4.5) below are stated in the paper's own terms, `H[M.X i ; M.P]`, so nothing of the
example's content is displaced into the encoding.

Definition 3.1's finite-entropy sample space makes every entropy occurring in (4.2)–(4.5)
finite — `RVModel.finiteEntropyOf` derives it for each of them — so the paper's hedge "if
all the following quantities are defined" needs no counterpart here. -/

namespace Example41

variable {I : Type w} [Finite I]

/-- The latent family of Example 4.1's `L₁`: `Y_A` is the family of given variables `X_j`
over the indices `j` with `A = {j}`.  There is at most one such `j`, so this is `X_i` at
`A = {i}` and a constant elsewhere. -/
noncomputable def L₁RV (M : RVModel.{u, v, w} I) : RVModel.{u, max v w, w} (PPlus I) where
  Ω := M.Ω
  P := M.P
  R := fun A => ∀ j : {i : I // A.toFinset = {i}}, M.R j.1
  X := fun _ ω j => M.X j.1 ω
  measurable_X := fun _ => measurable_pi_lambda _ fun j => M.measurable_X j.1
  finiteEntropy_X := fun _ =>
    M.finiteEntropyOf (measurable_pi_lambda _ fun j => M.measurable_X j.1)

/-- **Example 4.1's `L₁`**, for an arbitrary random variable model `M`: the latent variable
model `(Ω, (Y_A)_{A ∈ P⁺I}, idΩ)` of (4.1) with `Y_{i} = X_i` for `i ∈ I` and `Y_A`
constant for `|A| ≠ 1`.

The contribution condition of Definition 3.2 holds because `{i} ∈ P⁺I` contributes to `i`
and `Y_{i}` *is* `X_i` (indexed by the one-point type `{j // {i} = {j}}`, whose inhabitant
is `⟨i, rfl⟩`), so the witnessing function is a projection followed by an evaluation.

Paper node: `Example 4.1` -/
noncomputable def L₁ (M : RVModel.{u, v, w} I) : LatentModel M where
  L := L₁RV M
  π := id
  π_pres := MeasurePreserving.id _
  contributes := fun i => by
    refine ⟨fun g => g ⟨PPlus.single i, by simp [contribIdx]⟩ ⟨i, rfl⟩,
      measurable_of_countable _, ?_⟩
    filter_upwards with ω
    rfl

/-- The latent family of Example 4.1's `L₂`: `Z_A` is the family of *all* given variables
when `A` is all of `I`, and a constant otherwise.  The guard is written
`∀ k : I, k ∈ A.toFinset` rather than `A.toFinset = Finset.univ` so that no `Fintype I` is
needed to form the definition. -/
noncomputable def L₂RV (M : RVModel.{u, v, w} I) : RVModel.{u, max v w, w} (PPlus I) where
  Ω := M.Ω
  P := M.P
  R := fun A => ∀ j : {_i : I // ∀ k : I, k ∈ A.toFinset}, M.R j.1
  X := fun _ ω j => M.X j.1 ω
  measurable_X := fun _ => measurable_pi_lambda _ fun j => M.measurable_X j.1
  finiteEntropy_X := fun _ =>
    M.finiteEntropyOf (measurable_pi_lambda _ fun j => M.measurable_X j.1)

/-- **Example 4.1's `L₂`**, for an arbitrary random variable model `M`: the latent variable
model `(Ω, (Z_A)_{A ∈ P⁺I}, idΩ)` of (4.1) with `Z_I = X_I` and `Z_A` constant for
`A ⊊ I`.

No `[Fintype I]`, `[DecidableEq I]` or `[Nonempty I]` is taken: the top element of `P⁺I` is
only ever needed *inside* the proof of the contribution condition, where an index `i : I`
is in hand and so `I` is nonempty there; the `Finset` of all indices is produced by a local
`Fintype.ofFinite`, which never escapes into the statement.  Equations (4.4)–(4.5) below
name `X_I` as `RVModel.jointAll` — the dependent product over `I` itself — rather than as
`M.joint Finset.univ`, precisely so that they too need only `[Finite I]`: `Finset.univ`
requires a `Fintype` datum to *write down*, and `∀ i, M.R i` does not.  The two differ only
by the coordinate relabelling `↥(univ : Finset I) ≃ I`.

Paper node: `Example 4.1` -/
noncomputable def L₂ (M : RVModel.{u, v, w} I) : LatentModel M where
  L := L₂RV M
  π := id
  π_pres := MeasurePreserving.id _
  contributes := fun i => by
    letI : Fintype I := Fintype.ofFinite I
    refine ⟨fun g => g ⟨⟨Finset.univ, ⟨i, Finset.mem_univ i⟩⟩, Finset.mem_univ i⟩
      ⟨i, fun k => Finset.mem_univ k⟩, measurable_of_countable _, ?_⟩
    filter_upwards with ω
    rfl

/-! ### The two shapes a guarded latent takes

Every term of (4.2)–(4.5) is one of two things: a latent whose guard *fails*, whose range
is then a one-point type, or a latent whose guard *holds*, whose range is then a
relabelling of the given variables it names.  The four lemmas below are those two shapes
for `L₁` and `L₂`; the equations are bookkeeping on top of them. -/

/-- When `B` is not a singleton, `L₁`'s guard `{i : I // B = {i}}` is empty, so the latent
range `Y_B` is a one-point type — the paper's "let `Y_B` be constant". -/
@[reducible] private def L₁RV_unique (M : RVModel.{u, v, w} I) {B : PPlus I}
    (hB : ∀ i : I, B.toFinset ≠ {i}) : Unique ((L₁ M).L.R B) := by
  haveI : IsEmpty {i : I // B.toFinset = {i}} := ⟨fun j => hB j.1 j.2⟩
  exact Pi.uniqueOfIsEmpty _

/-- `Y_{i} = X_i` up to the guarded-subtype relabelling: the index type
`{j : I // {i} = {j}}` is a one-point type, so evaluating at its inhabitant `⟨i, rfl⟩` is
an injective map of ranges and entropy is invariant under it. -/
private lemma L₁_entropy_single (M : RVModel.{u, v, w} I) (i : I) :
    H[(L₁ M).Y (PPlus.single i) ; (L₁ M).P] = H[M.X i ; M.P] := by
  -- The relabelling is passed explicitly: leaving it to higher-order unification against
  -- `?f ∘ X` is a heartbeat bomb at every `entropy_comp_of_injective` call site.
  have hinj : Function.Injective
      (fun x : (∀ j : {k : I // (PPlus.single i).toFinset = {k}}, M.R j.1) => x ⟨i, rfl⟩) := by
    intro x y hxy
    funext j
    obtain rfl : j = ⟨i, rfl⟩ := Subtype.ext (Finset.singleton_injective j.2).symm
    exact hxy
  exact (entropy_comp_of_injective (L₁ M).P ((L₁ M).L.measurable_X _)
    (fun x : (∀ j : {k : I // (PPlus.single i).toFinset = {k}}, M.R j.1) => x ⟨i, rfl⟩)
    hinj).symm

/-- The contributing latents of `L₁` that are *not* constant are exactly the singletons
`{i}` with `i ∈ A` — the shared bookkeeping of (4.2) and (4.3). -/
private lemma L₁_sum_eq (A : Finset I) (f : PPlus I → ℝ)
    (hzero : ∀ B : PPlus I, (∀ i : I, B.toFinset ≠ {i}) → f B = 0) :
    ∑ B ∈ famFinset (contrib A), f B = ∑ i ∈ A, f (PPlus.single i) := by
  classical
  have hsub : A.image PPlus.single ⊆ famFinset (contrib A) := by
    intro B hB
    obtain ⟨i, hiA, rfl⟩ := Finset.mem_image.1 hB
    exact mem_famFinset.2 ⟨i, hiA, by simp⟩
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · intro i _ j _ hij
    simpa using congrArg PPlus.toFinset hij
  · intro B hB hB'
    refine hzero B fun i hi => hB' ?_
    obtain ⟨j, hjA, hjB⟩ := mem_famFinset.1 hB
    have hji : j = i := Finset.mem_singleton.1 (hi ▸ (hjB : j ∈ B.toFinset))
    subst hji
    exact Finset.mem_image.2 ⟨j, hjA, PPlus.ext hi.symm⟩

/-- **Equation (4.2)**: `σ_{L₁}(A) = ∑_{B ∩ A ≠ ∅} H(Y_B) = ∑_{i ∈ A} H(Xᵢ)`.  The latents
that contribute to `A` and are not constant are exactly the singletons `{i}`, `i ∈ A`.

Paper node: `Example 4.1` -/
theorem L₁_simpleScore (M : RVModel.{u, v, w} I) (A : Finset I) :
    (L₁ M).simpleScore A = ∑ i ∈ A, H[M.X i ; M.P] := by
  rw [LatentModel.simpleScore,
    L₁_sum_eq A _ fun B hB => by
      letI := L₁RV_unique M hB
      exact entropy_eq_zero_of_subsingleton _]
  exact Finset.sum_congr rfl fun i _ => L₁_entropy_single M i

/-- **Equation (4.3)**: `χ_{L₁}(A) = ∑_{B ∩ A ≠ ∅} H(Y_B | Y_⊋B) = ∑_{i ∈ A} H(Xᵢ)`.  The
conditioning does nothing here: everything strictly above a singleton has `|B| ≠ 1` and is
therefore constant, so `Y_⊋{i}` is constant and `H(Y_{i} | Y_⊋{i}) = H(Xᵢ)`.

Paper node: `Example 4.1` -/
theorem L₁_condScore (M : RVModel.{u, v, w} I) (A : Finset I) :
    (L₁ M).condScore A = ∑ i ∈ A, H[M.X i ; M.P] := by
  rw [LatentModel.condScore,
    L₁_sum_eq A _ fun B hB => by
      letI := L₁RV_unique M hB
      exact condEntropy_eq_zero_of_subsingleton ((L₁ M).L.measurable_X B)
        ((L₁ M).L.measurable_jointOn _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Everything strictly above `{i}` has at least two elements, so `Y_⊋{i}` is constant.
  haveI : ∀ C : ↥(strictAbove (PPlus.single i).toFinset), Unique ((L₁ M).L.R ↑C) := by
    intro C
    refine L₁RV_unique M fun k hk => ?_
    have h : (PPlus.single i).toFinset < (C : PPlus I).toFinset := C.2
    rw [hk] at h
    have : i = k := Finset.mem_singleton.1 (h.le (Finset.mem_singleton_self i))
    subst this
    exact absurd h (lt_irrefl _)
  rw [condEntropy_eq_entropy_of_subsingleton ((L₁ M).L.measurable_X _), L₁_entropy_single]

/-- When `B` is not all of `I`, `L₂`'s guard `{_i : I // ∀ k, k ∈ B}` is empty, so the
latent range `Z_B` is a one-point type — the paper's "let `Z_B` be constant". -/
@[reducible] private def L₂RV_unique (M : RVModel.{u, v, w} I) {B : PPlus I} {k : I}
    (hk : k ∉ B.toFinset) : Unique ((L₂ M).L.R B) := by
  haveI : IsEmpty {_i : I // ∀ k : I, k ∈ B.toFinset} := ⟨fun j => hk (j.2 k)⟩
  exact Pi.uniqueOfIsEmpty _

omit [Finite I] in
/-- Anything other than the top element of `P⁺I` misses an index.  Stated through
"`T` contains every index" rather than `T.toFinset = Finset.univ` so that no `Fintype I`
datum is needed. -/
private lemma L₂_exists_notMem_of_ne {B T : PPlus I} (hT : ∀ k : I, k ∈ T.toFinset)
    (hBT : B ≠ T) : ∃ k : I, k ∉ B.toFinset := by
  by_contra h
  exact hBT (PPlus.ext (Finset.Subset.antisymm (fun k _ => hT k)
    (fun k _ => not_not.1 fun hk => h ⟨k, hk⟩)))

/-- `Z_I = X_I` up to the guarded-subtype relabelling: where the guard holds its subtype is
a copy of `I` itself, and `Z_I` is `M.jointAll` read along that copy.  Entropy is invariant
under the relabelling because it is injective. -/
private lemma L₂_entropy_top (M : RVModel.{u, v, w} I) {T : PPlus I}
    (hT : ∀ k : I, k ∈ T.toFinset) :
    H[(L₂ M).Y T ; (L₂ M).P] = H[M.jointAll ; M.P] := by
  -- `f` is passed explicitly: leaving it to higher-order unification is a heartbeat bomb.
  have hinj : Function.Injective (fun (x : (L₂ M).L.R T) (i : I) => x ⟨i, hT⟩) := by
    intro x y hxy
    funext j
    exact congrFun hxy j.1
  exact (entropy_comp_of_injective (L₂ M).P ((L₂ M).L.measurable_X T)
    (fun (x : (L₂ M).L.R T) (i : I) => x ⟨i, hT⟩) hinj).symm

/-- **Equation (4.4)**: `σ_{L₂}(A) = ∑_{B ∩ A ≠ ∅} H(Z_B) = H(Z_I) = H(X_I)`.

`A` is required to be **nonempty**, which the paper's (4.4) does not say and needs: at
`A = ∅` the index family `{B : B ∩ A ≠ ∅}` is empty, so the left side is `0` while the
right side is `H(X_I)`, which is not in general zero.  (`notes/paper-errata.md` entry 11;
the corresponding (4.2)–(4.3) hold at `A = ∅` because both sides are then empty sums.)

`X_I` is `RVModel.jointAll`, the joint variable over the whole index type, so that no
`[Fintype I]` binder is needed to name it.

Paper node: `Example 4.1` -/
theorem L₂_simpleScore (M : RVModel.{u, v, w} I) {A : Finset I} (hA : A.Nonempty) :
    (L₂ M).simpleScore A = H[M.jointAll ; M.P] := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨a, haA⟩ := hA
  set T : PPlus I := ⟨Finset.univ, ⟨a, Finset.mem_univ a⟩⟩ with hTdef
  have hTu : ∀ k : I, k ∈ T.toFinset := by rw [hTdef]; exact fun k => Finset.mem_univ k
  have hmem : T ∈ famFinset (contrib A) := mem_famFinset.2 ⟨a, haA, hTu a⟩
  have hzero : ∀ B ∈ famFinset (contrib A), B ≠ T → H[(L₂ M).Y B ; (L₂ M).P] = 0 := by
    intro B _ hBT
    obtain ⟨k, hk⟩ := L₂_exists_notMem_of_ne hTu hBT
    letI := L₂RV_unique M hk
    exact entropy_eq_zero_of_subsingleton _
  rw [LatentModel.simpleScore, Finset.sum_eq_single_of_mem T hmem hzero,
    L₂_entropy_top M hTu]

/-- **Equation (4.5)**: `χ_{L₂}(A) = ∑_{B ∩ A ≠ ∅} H(Z_B | Z_⊋B) = H(X_I)`.  Nothing
strictly contains the top element of `P⁺I`, so `Z_⊋I` is a variable into a one-point type
and its term is the unconditioned `H(Z_I)`; every other term is the entropy of a constant.

`A` nonempty for the same reason as in (4.4).

Paper node: `Example 4.1` -/
theorem L₂_condScore (M : RVModel.{u, v, w} I) {A : Finset I} (hA : A.Nonempty) :
    (L₂ M).condScore A = H[M.jointAll ; M.P] := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨a, haA⟩ := hA
  set T : PPlus I := ⟨Finset.univ, ⟨a, Finset.mem_univ a⟩⟩ with hTdef
  have hTu : ∀ k : I, k ∈ T.toFinset := by rw [hTdef]; exact fun k => Finset.mem_univ k
  have hmem : T ∈ famFinset (contrib A) := mem_famFinset.2 ⟨a, haA, hTu a⟩
  have hzero : ∀ B ∈ famFinset (contrib A), B ≠ T →
      H[(L₂ M).Y B | (L₂ M).jointStrictAbove B.toFinset ; (L₂ M).P] = 0 := by
    intro B _ hBT
    obtain ⟨k, hk⟩ := L₂_exists_notMem_of_ne hTu hBT
    letI := L₂RV_unique M hk
    exact condEntropy_eq_zero_of_subsingleton ((L₂ M).L.measurable_X B)
      ((L₂ M).L.measurable_jointOn _)
  rw [LatentModel.condScore, Finset.sum_eq_single_of_mem T hmem hzero]
  -- Nothing strictly contains the top element of `P⁺I`, so `Z_⊋I` is empty-indexed.
  haveI : IsEmpty ↥(strictAbove T.toFinset) := by
    refine ⟨fun C => ?_⟩
    have h : T.toFinset < (C : PPlus I).toFinset := C.2
    have h2 : (C : PPlus I).toFinset ≤ T.toFinset := fun k _ => hTu k
    exact absurd (lt_of_lt_of_le h h2) (lt_irrefl _)
  rw [condEntropy_eq_entropy_of_subsingleton ((L₂ M).L.measurable_X _), L₂_entropy_top M hTu]

end Example41

/-! ## Example 4.4 — a model simply-perfectly condensed by a given independent family

Example 4.1 goes from a model to (bad) latent variable models for it.  Example 4.4 goes the
other way: it starts from an arbitrary random variable model `L = (Ω, (Y_A)_{A ∈ P⁺I})`
*indexed by* `P⁺I` whose variables are jointly independent, and manufactures a model `M`
over `I` that `L` simply-perfectly condenses, by declaring `Xᵢ := Y_∋i` — equation (4.10).

This is the construction the `LatentModel` universe unpinning exists for: `Xᵢ = Y_∋i` is a
dependent product over `↥(contribIdx i) : Type w`, so `M`'s ranges land in `Type (max v w)`
while `L`'s stay in `Type v`.  `L44` therefore takes `L` in its **given** universes; nothing
is pre-inflated. -/

namespace Example44

variable {I : Type w} [Finite I]

/-- **Equation (4.10)**: the random variable model `M = (Ω, (Xᵢ)ᵢ∈I)` built from a latent
family `L = (Ω, (Y_A)_{A ∈ P⁺I})` by `Xᵢ := Y_∋i = (Y_A : i ∈ A ⊆ I)`.  The sample space
and measure are `L`'s own, as Example 4.4 stipulates ("as related to `M` via the identity
map `idΩ`").

Paper node: `Example 4.4` -/
noncomputable def M44 (L : RVModel.{u, v, w} (PPlus I)) : RVModel.{u, max v w, w} I where
  Ω := L.Ω
  P := L.P
  R := fun i => ∀ B : contribIdx i, L.R B
  X := fun i => L.jointOn (contribIdx i)
  measurable_X := fun _ => L.measurable_jointOn _
  finiteEntropy_X := fun _ => inferInstance

/-- **Example 4.4's latent variable model**: `L` itself, related to `M44 L` by the identity
map.  The contribution condition of Definition 3.2 is a tautology here — `Xᵢ` *is* `Y_∋i`,
so `π^* Xᵢ` is a function of `Y_∋i` by `aeFunctionOf_self`.

No independence hypothesis is needed to *build* this; independence enters only in (4.11),
which is what makes the simple score come out right.

Paper node: `Example 4.4` -/
noncomputable def L44 (L : RVModel.{u, v, w} (PPlus I)) : LatentModel (M44 L) where
  L := L
  π := id
  π_pres := MeasurePreserving.id _
  contributes := fun _ => aeFunctionOf_self

/-- **Equation (4.11)**:
`H(X_A) = H(Xᵢ : i ∈ A) = H(Y_B : B ∩ A ≠ ∅) = ∑_{B ∩ A ≠ ∅} H(Y_B)`.  The first two
equalities are re-indexings; the last is where "the variables `Y_A` are jointly
independent" is used.

Paper node: `Example 4.4` -/
theorem entropy_joint_eq (L : RVModel.{u, v, w} (PPlus I))
    (hindep : iIndepFun L.X L.P) (A : Finset I) :
    H[(M44 L).joint A ; (M44 L).P] = ∑ B ∈ famFinset (contrib A), H[L.X B ; L.P] := by
  rw [← L.entropy_jointOn_eq_sum_famFinset hindep (contrib A)]
  -- `X_A` and `Y_∩A` are functions of each other: `X_A` repeats each `Y_B` once for every
  -- `i ∈ A ∩ B`, so the relabelling is surjective-with-repeats rather than injective and
  -- the Schröder–Bernstein form of entropy invariance is what applies.
  have hA' : ∀ C : ↥(contrib A), (mem_contrib.1 C.2).choose ∈ A :=
    fun C => (mem_contrib.1 C.2).choose_spec.1
  have hC' : ∀ C : ↥(contrib A), (mem_contrib.1 C.2).choose ∈ (C : PPlus I) :=
    fun C => (mem_contrib.1 C.2).choose_spec.2
  -- Two data-processing inequalities rather than the packaged `entropy_of_comp_eq_of_comp`:
  -- that lemma takes one measure, and `(M44 L).P` is `L.P` only *definitionally*, so its
  -- `[FiniteEntropyOf _ μ]` arguments end up carrying `(M44 L).mΩ` on one side and `L.mΩ`
  -- on the other — a mismatch instance search cannot bridge (it will not unfold `M44`).
  -- Split this way, each inequality stays inside one model and finds its own instance.
  -- Both relabellings are passed explicitly; a `_` there is a higher-order-unification
  -- heartbeat bomb.
  refine le_antisymm
    (ShannonInformation.entropy_comp_le L.P (L.measurable_jointOn (contrib A))
      (fun (y : ∀ C : ↥(contrib A), L.R ↑C) (i : ↥A) (B : ↥(contribIdx (i : I))) =>
        y ⟨(B : PPlus I), ⟨(i : I), i.2, B.2⟩⟩))
    (ShannonInformation.entropy_comp_le (M44 L).P ((M44 L).measurable_joint A)
      (fun (x : ∀ i : ↥A, (M44 L).R ↑i) (C : ↥(contrib A)) =>
        x ⟨(mem_contrib.1 C.2).choose, hA' C⟩ ⟨(C : PPlus I), hC' C⟩))

/-- Example 4.4's conclusion: `L` **simply-perfectly condenses** `M44 L`, i.e.
`σ_L(A) = H(X_A)` for every `A ⊆ I`.  Immediate from (4.11): the simple score is by
definition the right-hand sum of (4.11).

This is Definition 4.3's `LatentModel.SimplyPerfectlyCondenses`, which unfolds to exactly
that universally quantified equation.

Paper node: `Example 4.4` -/
theorem simplyPerfectlyCondenses (L : RVModel.{u, v, w} (PPlus I))
    (hindep : iIndepFun L.X L.P) : (L44 L).SimplyPerfectlyCondenses :=
  fun A => (entropy_joint_eq L hindep A).symm

/-! ### Example 4.4 on a constructed family

`simplyPerfectlyCondenses` above quantifies over a family `L` satisfying a
joint-independence hypothesis, and nothing so far discharged that hypothesis for a concrete
`L`.  The coin's latent family does, for the trivial reason that its index type `P⁺Unit`
has a single element (`iIndepFun_of_subsingleton`, `Subsingleton (PPlus Unit)` — both
declared in the Definition 4.3 section above).  These two witnesses are what keep
Definition 4.3's *simple* clause from being a condition with no exhibited inhabitant; the
`coinLatent` witnesses above cover the conditioned clause and Definition 4.8. -/

/-- **Example 4.4's hypothesis is satisfiable, so its conclusion is non-vacuous**: `L44`
over the coin's latent family simply-perfectly condenses the model `M44` it builds.  A
constructed inhabitant of Definition 4.3's `SimplyPerfectlyCondenses`. -/
lemma L44_coin_simplyPerfectlyCondenses :
    (L44 coinLatent.L).SimplyPerfectlyCondenses :=
  simplyPerfectlyCondenses coinLatent.L coinLatentRV_iIndepFun

/-- …and hence a second inhabitant of `PerfectlyCondenses`, through the squeeze
`PerfectlyCondenses.of_simply` of (4.21).  (`perfect_tfae_A`'s (A1 ⇒ A3) carries the same
implication with the joint-independence conjunct attached; `of_simply` is that implication
with nothing extra, and is what a non-vacuity claim should cite.) -/
lemma L44_coin_perfectlyCondenses :
    (L44 coinLatent.L).PerfectlyCondenses :=
  LatentModel.PerfectlyCondenses.of_simply _ L44_coin_simplyPerfectlyCondenses

end Example44

/-! ## §3.1 witnesses — morphisms, the category of Proposition 3.7, and Definition 3.9

`Condensation/Morphism.lean` states Definitions 3.5–3.10 and Propositions 3.7, 3.8, 3.11,
3.12; the concrete morphisms that exercise them live here rather than there, because they
are built over the constructed models of this file.  That is not a preference but a
constraint on the import graph: `Perfect.lean` needs Definition 3.10 for Proposition 4.7,
so `Morphism.lean` has to sit *upstream* of `Perfect.lean`, and `Examples.lean` imports
`Perfect.lean`.  A regression `example` inside `Morphism.lean` naming `coinModel` would
close the cycle `Morphism → Examples → Perfect → Morphism`.  `Examples.lean` is the
terminal non-vacuity file of the library, which is exactly where witnesses belong.

Non-vacuity discipline: `RVModel.Hom` gets a constructed inhabitant that is not an
identity (`coinCollapse`, which genuinely changes the index set), the category of
Proposition 3.7 gets objects and a non-identity arrow, and Definition 3.9's remark — that
a.e. equality constrains the `f` components not at all — gets the pair
`pairCoinHom₁`/`pairCoinHom₂`, which differ as functions and are a.e. equal as morphisms. -/

section MorphismWitnesses

/-- The identity morphism on the fair-coin model. -/
noncomputable example : RVModel.Hom coinModel coinModel := RVModel.Hom.id coinModel

/-- A morphism collapsing the two-index model onto the one-index one: `π` is the identity
on `Ω = Bool`, the index map `ι : Unit → Bool` picks out the variable `X_true`, and
`f_() = id`.  It is a morphism because both models' single relevant variable is the coin
itself. -/
noncomputable def coinCollapse : RVModel.Hom twoCoinModel coinModel where
  π := id
  π_pres := MeasurePreserving.id _
  ι := fun _ => true
  f := fun _ => id
  eq_ae := fun _ => Filter.Eventually.of_forall fun _ => rfl

example : coinCollapse.comp (RVModel.Hom.id coinModel) = coinCollapse := rfl

example : (RVModel.Hom.id twoCoinModel).comp coinCollapse = coinCollapse := rfl

example : RVModel.Hom.AEEq coinCollapse coinCollapse := RVModel.Hom.aeEq_equivalence.refl _

example : RVModel.Equivalent coinModel coinModel := RVModel.Equivalent.refl coinModel

/-! ### The category of Proposition 3.7, over the constructed models -/

/-- The fair-coin model as an object of the category. -/
noncomputable def coinObj : RVModelObj := ⟨Unit, coinModel⟩

/-- The two-index model as an object of the category. -/
noncomputable def twoCoinObj : RVModelObj := ⟨Bool, twoCoinModel⟩

/-- `coinCollapse` read as a morphism of the category. -/
noncomputable def coinCollapseArrow : twoCoinObj ⟶ coinObj := coinCollapse

example : CategoryTheory.CategoryStruct.comp coinCollapseArrow
    (CategoryTheory.CategoryStruct.id coinObj) = coinCollapseArrow := by
  simp

/-- Proposition 3.8 applied to a real morphism: the identity of `coinObj` is an
isomorphism, so its index map is a bijection. -/
example : Function.Bijective
    (RVModel.Hom.ι (CategoryTheory.CategoryStruct.id coinObj)) :=
  ((RVModel.Hom.isIso_iff _).1 inferInstance).2.1

/-! ### Definition 3.9's remark: a.e.-equal morphisms with different `f`

The remark after Definition 3.9 is that a.e. equality puts *no* condition on the `f`
components, and that they may genuinely differ because `X_{ι(j)}`, considered as a
measurable function, need not be surjective.  Here is that phenomenon on constructed
models: `pairCoinModel` observes the fair coin through the range `Bool × Bool` but never
attains a pair whose second coordinate is `true`, and the two morphisms below to
`coinModel` agree on every attained value and differ at `(true, true)`. -/

/-- The fair coin observed through a range half of whose values are never attained. -/
noncomputable def pairCoinModel : RVModel Unit where
  Ω := Bool
  P := coinMeasure
  R := fun _ => Bool × Bool
  X := fun _ ω => (ω, false)
  measurable_X := fun _ => measurable_of_countable _
  finiteEntropy_X := fun _ => inferInstance

/-- The morphism reading off the first coordinate. -/
noncomputable def pairCoinHom₁ : RVModel.Hom pairCoinModel coinModel where
  π := id
  π_pres := MeasurePreserving.id _
  ι := fun _ => ()
  f := fun _ p => p.1
  eq_ae := fun _ => Filter.Eventually.of_forall fun _ => rfl

/-- The morphism reading off the two coordinates' disagreement.  It agrees with
`pairCoinHom₁` on every value `X` attains, and differs from it at `(true, true)`. -/
noncomputable def pairCoinHom₂ : RVModel.Hom pairCoinModel coinModel where
  π := id
  π_pres := MeasurePreserving.id _
  ι := fun _ => ()
  f := fun _ p => (p.1 != p.2)
  eq_ae := fun _ => Filter.Eventually.of_forall fun ω => by cases ω <;> rfl

example : pairCoinHom₁.f ≠ pairCoinHom₂.f := fun h =>
  Bool.noConfusion (congrFun (congrFun h ()) (true, true) : (true : Bool) = false)

example : RVModel.Hom.AEEq pairCoinHom₁ pairCoinHom₂ :=
  ⟨Filter.Eventually.of_forall fun _ => rfl, rfl⟩

end MorphismWitnesses

end Condensation
