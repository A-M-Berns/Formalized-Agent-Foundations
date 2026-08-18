import Condensation.API

/-! Client-style smoke tests for the Condensation API.  These import only
`Condensation.API` — no `Mathlib.*` import of their own, and never `import Mathlib`, which
fails to elaborate against the vendored PFR shims.  They build a client's own random
variable model and latent variable model rather than reusing `Condensation/Examples.lean`'s
fixtures, compute both scores on it by rewriting, and then compose endpoints across §2–§5
to prove facts a downstream project would want.  None of them restates a paper node.

Where an endpoint needed a `haveI`, an explicit universe, a qualified name or a workaround
for an elaboration order, the workaround is **left visible with a comment saying why**: a
rough edge in the interface is a finding about the interface, and these tests are where a
future client meets it first.  The same rough edges are written up in `Condensation/API.lean`.

Note the `open _root_.Condensation` below.  A bare `open Condensation` inside a namespace
that itself ends in `Condensation` resolves to the *current* namespace, succeeds silently,
and then every name in the file fails as an unknown identifier. -/

namespace APITests.Condensation

open MeasureTheory ProbabilityTheory
open _root_.Condensation
open CategoryTheory

/-! ## A client random variable model, built from scratch

`Ω = Bool × Bool` with the uniform measure, `I = Bool`, and the two variables are the two
coordinates — so unlike every fixture in `Condensation/Examples.lean`, whose variables all
observe the *same* coin, this client's two observables are genuinely independent.  That is
what makes the chain-rule section at the end of this file say something. -/

/-- The uniform measure on two independent fair coins. -/
noncomputable def pairMeasure : Measure (Bool × Bool) :=
  uniformOn (Set.univ : Set (Bool × Bool))

instance : IsProbabilityMeasure pairMeasure := by
  unfold pairMeasure; infer_instance

/-- The client's random variable model.  Only six fields have to be supplied: the bracketed
instance fields of `RVModel`, including Definition 3.1's finite-entropy clause on `Ω`, are
all discharged by instance search on a finite sample space.

`_root_.cond` is written in full because `open ProbabilityTheory` makes a bare `cond`
ambiguous with `ProbabilityTheory.cond` (conditioning a measure on a set). -/
noncomputable def coins : RVModel Bool where
  Ω := Bool × Bool
  P := pairMeasure
  R := fun _ => Bool
  X := fun i ω => _root_.cond i ω.2 ω.1
  measurable_X := fun i => by cases i <;> simpa using (by measurability : Measurable _)
  finiteEntropy_X := fun _ => inferInstance

@[simp] lemma coins_X_false : coins.X false = Prod.fst := rfl
@[simp] lemma coins_X_true : coins.X true = Prod.snd := rfl
@[simp] lemma coins_P : coins.P = pairMeasure := rfl

lemma pair_preimage_fst (x : Bool) :
    (Prod.fst ⁻¹' {x} : Set (Bool × Bool)) = {(x, false), (x, true)} := by
  ext ⟨a, b⟩; cases b <;> simp [eq_comm]

lemma pair_preimage_snd (x : Bool) :
    (Prod.snd ⁻¹' {x} : Set (Bool × Bool)) = {(false, x), (true, x)} := by
  ext ⟨a, b⟩; cases a <;> simp [eq_comm]

lemma pairMeasure_preimage_fst (x : Bool) : pairMeasure (Prod.fst ⁻¹' {x}) = 2 / 4 := by
  rw [pairMeasure, uniformOn_apply Set.finite_univ, Set.univ_inter, pair_preimage_fst,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_univ, Set.ncard_pair (by simp)]
  norm_num

lemma pairMeasure_preimage_snd (x : Bool) : pairMeasure (Prod.snd ⁻¹' {x}) = 2 / 4 := by
  rw [pairMeasure, uniformOn_apply Set.finite_univ, Set.univ_inter, pair_preimage_snd,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_univ, Set.ncard_pair (by simp)]
  norm_num

lemma isUniform_fst : IsUniform (Set.univ : Set Bool) Prod.fst pairMeasure where
  eq_of_mem := by intro x _ y _; rw [pairMeasure_preimage_fst, pairMeasure_preimage_fst]
  measure_preimage_compl := by rw [Set.compl_univ, Set.preimage_empty, measure_empty]

lemma isUniform_snd : IsUniform (Set.univ : Set Bool) Prod.snd pairMeasure where
  eq_of_mem := by intro x _ y _; rw [pairMeasure_preimage_snd, pairMeasure_preimage_snd]
  measure_preimage_compl := by rw [Set.compl_univ, Set.preimage_empty, measure_empty]

lemma entropy_fst : H[(Prod.fst : Bool × Bool → Bool) ; pairMeasure] = Real.log 2 := by
  have h := isUniform_fst.entropy_eq' Set.finite_univ measurable_fst
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h

lemma entropy_snd : H[(Prod.snd : Bool × Bool → Bool) ; pairMeasure] = Real.log 2 := by
  have h := isUniform_snd.entropy_eq' Set.finite_univ measurable_snd
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h

/-- Each client observable is a fair coin, so this is not the degenerate model in which
every information quantity vanishes.

Rough edge kept visible: the two `have`s above are stated over the *ambient*
`MeasurableSpace Bool`, while the goal's is the projection `coins.mR false`.  They are
definitionally equal but `simpa` closes at reducible transparency and reports the maddening
"after simplification, `h` has type `X` but is expected to have type `X`".  Splitting the
computation into a separately stated lemma and discharging with a bare `exact`, which runs
at default transparency, is the fix. -/
lemma coins_entropy (i : Bool) : H[coins.X i ; coins.P] = Real.log 2 := by
  cases i
  · exact entropy_fst
  · exact entropy_snd

lemma pair_entropy_id :
    H[(id : Bool × Bool → Bool × Bool) ; pairMeasure] = 2 * Real.log 2 := by
  have huniform : IsUniform (Set.univ : Set (Bool × Bool)) (id : Bool × Bool → Bool × Bool)
      pairMeasure := isUniform_uniformOn
  have h := huniform.entropy_eq' Set.finite_univ measurable_id
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h
  rw [h, show ((Fintype.card (Bool × Bool) : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

/-! ## A client latent variable model over it

One latent per element of `P⁺ Bool`, each carrying the whole joint state.  `π` is the
identity, and Definition 3.2's contribution condition is discharged by reading `X_i` off the
single latent `Y_{i}`, which is a coordinate of `Y_∋i`. -/

noncomputable def coinsLatentRV : RVModel (PPlus Bool) where
  Ω := Bool × Bool
  P := pairMeasure
  R := fun _ => Bool × Bool
  X := fun _ => id
  measurable_X := fun _ => measurable_id
  finiteEntropy_X := fun _ => inferInstance

noncomputable def coinsLatent : LatentModel coins where
  L := coinsLatentRV
  π := id
  π_pres := MeasurePreserving.id _
  contributes := fun i => by
    refine ⟨fun g => coins.X i (g ⟨PPlus.single i, by simp⟩), measurable_of_countable _, ?_⟩
    filter_upwards with ω
    rfl

/-- `{false} ∈ P⁺ Bool`. -/
def bF : PPlus Bool := ⟨{false}, Finset.singleton_nonempty _⟩

/-- `{true, false} ∈ P⁺ Bool`, the maximum. -/
def bTF : PPlus Bool := ⟨{true, false}, ⟨true, by decide⟩⟩

lemma bF_ne_bTF : bF ≠ bTF := by decide

/-- Computing a score starts here: `famFinset` turns Definition 3.3's index set into the
`Finset` its sums range over, and `mem_famFinset` is its whole interface.  The
`ext` / `simp only` / `revert` / `decide` shape is the one that works — `famFinset` is
noncomputable, so `decide` cannot see through it until membership has been unfolded to a
decidable statement about `P⁺ Bool`. -/
lemma famFinset_contrib_false :
    famFinset (contrib ({false} : Finset Bool)) = {bF, bTF} := by
  ext B
  simp only [mem_famFinset, mem_contrib, Finset.mem_singleton, exists_eq_left, PPlus.mem_iff,
    Finset.mem_insert]
  revert B
  decide

lemma coinsLatent_entropy (B : PPlus Bool) :
    H[coinsLatent.Y B ; coinsLatent.P] = 2 * Real.log 2 := pair_entropy_id

/-- The simple score of Definition 3.3, computed: two latents contribute to `{false}`, and
each carries both coins. -/
lemma coinsLatent_simpleScore :
    coinsLatent.simpleScore ({false} : Finset Bool) = 4 * Real.log 2 := by
  rw [LatentModel.simpleScore, famFinset_contrib_false, Finset.sum_pair bF_ne_bTF,
    coinsLatent_entropy, coinsLatent_entropy]
  ring

/-- Nothing strictly contains the maximum, which is what makes its conditioned term
computable through `condEntropy_eq_entropy_of_subsingleton`. -/
instance : IsEmpty (strictAbove bTF.toFinset) :=
  ⟨fun C => (by decide : ∀ D : PPlus Bool, ¬ bTF.toFinset ⊂ D.toFinset) C.1 C.2⟩

lemma coinsLatent_condEntropy_bF :
    H[coinsLatent.Y bF | coinsLatent.jointStrictAbove bF.toFinset ; coinsLatent.P] = 0 := by
  have hmem : bTF ∈ strictAbove bF.toFinset := by
    show bF.toFinset ⊂ bTF.toFinset
    decide
  refine condEntropy_eq_zero_of_aeFunctionOf
    (coinsLatent.L.measurable_jointOn _) (coinsLatent.L.measurable_X _) ?_
  refine ⟨fun g => g ⟨bTF, hmem⟩, measurable_of_countable _, ?_⟩
  filter_upwards with ω
  rfl

lemma coinsLatent_condEntropy_bTF :
    H[coinsLatent.Y bTF | coinsLatent.jointStrictAbove bTF.toFinset ; coinsLatent.P]
      = 2 * Real.log 2 := by
  rw [condEntropy_eq_entropy_of_subsingleton (coinsLatent.L.measurable_X _),
    coinsLatent_entropy]

/-- The conditioned score of Definition 3.3, computed termwise: the conditioning kills the
`{false}` term outright and leaves the maximal one alone. -/
lemma coinsLatent_condScore :
    coinsLatent.condScore ({false} : Finset Bool) = 2 * Real.log 2 := by
  rw [LatentModel.condScore, famFinset_contrib_false, Finset.sum_pair bF_ne_bTF,
    coinsLatent_condEntropy_bF, coinsLatent_condEntropy_bTF, zero_add]

-- Client need: check on one's own model that Definition 3.3's conditioning is doing real
-- work, i.e. that `χ_L` is a strictly better score than `σ_L` here rather than equal to it.
example : 0 < coinsLatent.condScore ({false} : Finset Bool) ∧
    coinsLatent.condScore ({false} : Finset Bool) <
      coinsLatent.simpleScore ({false} : Finset Bool) := by
  rw [coinsLatent_condScore, coinsLatent_simpleScore]
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor <;> linarith

/-! ## §2 vocabulary, used generically -/

-- Client need: replace a latent by a measurable coarsening of it and keep the determinism
-- certificate.  Proposition 2.5 read in both directions with `AEFunctionOf.comp` between.
example {I : Type*} [Finite I] (M : RVModel I) (i : I) {S T : Type*}
    [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    [MeasurableSpace T] [Countable T] [MeasurableSingletonClass T]
    {Y : M.Ω → S} (hY : Measurable Y) {g : S → T} (hg : Measurable g)
    (h : H[Y | M.X i ; M.P] = 0) : H[g ∘ Y | M.X i ; M.P] = 0 := by
  -- Rough edge kept visible: finite entropy of a *derived* variable is `RVModel.finiteEntropyOf`,
  -- a lemma rather than an instance, because instance search cannot discharge the
  -- `Measurable` side condition.  Two `haveI`s, and it never has to be thought about again.
  haveI := M.finiteEntropyOf hY
  haveI := M.finiteEntropyOf (hg.comp hY)
  exact (aeFunctionOf_iff_condEntropy_eq_zero (M.measurable_X i) (hg.comp hY)).1
    (((aeFunctionOf_iff_condEntropy_eq_zero (M.measurable_X i) hY).2 h).comp hg)

-- Client need: monotonicity of joint entropy in the subfamily, which is what licenses
-- discarding latents.  The finite-entropy instance for `jointOn` *is* registered, so unlike
-- the previous example this one needs no `haveI` at all.
example {I : Type*} [Finite I] (L : RVModel (PPlus I)) {F G : Set (PPlus I)} (h : G ⊆ F) :
    H[L.jointOn G ; L.P] ≤ H[L.jointOn F ; L.P] :=
  entropy_le_of_aeFunctionOf (L.measurable_jointOn F) (L.aeFunctionOf_jointOn_mono h L.P)

/-! ## The chain-rule layer, on the client family -/

lemma coins_entropy_jointOn_univ :
    H[coins.jointOn (↑(Finset.univ : Finset Bool) : Set Bool) ; coins.P]
      = 2 * Real.log 2 := by
  -- Same rough edge as above, in the place it bites hardest: `id : Ω → Ω` is a derived
  -- variable like any other, so its finite entropy comes from `RVModel.finiteEntropyOf`.
  haveI : ShannonInformation.FiniteEntropyOf (id : coins.Ω → coins.Ω) coins.P :=
    coins.finiteEntropyOf measurable_id
  rw [← pair_entropy_id]
  exact (ShannonInformation.entropy_of_comp_eq_of_comp (μ := coins.P) measurable_id
    (coins.measurable_jointOn _) (fun ω i => coins.X i ω)
    (fun t => (t ⟨false, by simp⟩, t ⟨true, by simp⟩)) rfl rfl).symm

-- Client need: certify joint independence of one's own observables from an entropy
-- computation.  This is the converse direction of `ChainRule.lean`'s independence bridge —
-- the paper's (4.23)–(4.26) — which neither Mathlib nor the vendored PFR snapshot has.
example : iIndepFun coins.X coins.P := by
  refine coins.iIndepFun_of_entropy_jointOn_eq_sum (t := Finset.univ) Finset.mem_univ ?_
  rw [coins_entropy_jointOn_univ, Fintype.sum_bool, coins_entropy, coins_entropy]
  ring

/-! ## §3.1 — the category of random variable models -/

-- Client need: pull a target variable back along a *composite* morphism and land in §2's
-- `AEFunctionOf` vocabulary, without unfolding Definition 3.6's triple.
example {I J K : Type} [Finite I] [Finite J] [Finite K]
    {M : RVModel I} {N : RVModel J} {P : RVModel K}
    (φ : RVModel.Hom M N) (ψ : RVModel.Hom N P) (k : K) :
    AEFunctionOf (M.X (φ.ι (ψ.ι k))) (P.X k ∘ (ψ.π ∘ φ.π)) M.P :=
  (φ.comp ψ).aeFunctionOf k

-- Client need: the category laws of Proposition 3.7 hold on the nose, so a client may
-- reassociate and drop identities by `rfl` in a `calc`.
example (A B C D : RVModelObj.{0, 0, 0}) (φ : A ⟶ B) (ψ : B ⟶ C) (χ : C ⟶ D) :
    (𝟙 A ≫ φ) ≫ (ψ ≫ χ) = φ ≫ ψ ≫ χ ≫ 𝟙 D := rfl

-- Client need: certify that an arrow is invertible through Proposition 3.8's three
-- component conditions rather than by exhibiting an inverse or by `inferInstance` (here at
-- the identity arrow).  Rough edge kept visible: `RVModel.Hom.isIso_iff` must be named in
-- full on `𝟙 A`, because `𝟙 A`'s type prints as the stuck projection
-- `CategoryStruct.toQuiver.1 A A` and dot notation refuses it outright.
example (A : RVModelObj.{0, 0, 0}) : IsIso (𝟙 A) :=
  (RVModel.Hom.isIso_iff (𝟙 A)).2
    ⟨⟨MeasurableEquiv.refl A.M.Ω, rfl⟩, Function.bijective_id,
      fun i => ⟨MeasurableEquiv.refl (A.M.R i), rfl⟩⟩

-- Client need: read the three component conditions *off* an arrow already known to be
-- invertible — the direction Proposition 3.8 is usually consumed in.  On a *variable*
-- arrow `φ : A ⟶ B` the type does reduce to `RVModel.Hom A.M B.M`, so `φ.isIso_iff` and
-- `φ.π` do work; only the `𝟙`/`≫` spellings above need the full name.
example (A B : RVModelObj.{0, 0, 0}) (φ : A ⟶ B) [IsIso φ] :
    Function.Bijective (RVModel.Hom.ι φ) := (φ.isIso_iff.1 ‹_›).2.1

/-! ## §3.1 — a.e. equality as a transport tool -/

-- Client need: Definition 3.10's `IsEquivalence` depends only on the a.e. classes of its
-- two morphisms, so a client may swap in an a.e.-equal morphism (Definitions 3.9/3.10 and
-- Proposition 3.11 composed).  `≈` is the `Setoid` of Definition 3.9 on the hom-type.
-- Rough edge kept visible: the fields of `IsEquivalence` are spelled `Hom.AEEq _ _`, and a
-- `Setoid.trans`/`Setoid.symm` term whose result type is `?a ≈ ?b` will *not* unify against
-- them (the `Setoid` instance cannot be recovered from a stuck `AEEq` goal).  Restating the
-- composite through an explicitly `≈`-typed `have` fixes the instance and then closes the
-- field by defeq.
example {I J : Type} [Finite I] [Finite J] {M : RVModel I} {N : RVModel J}
    {φ φ' : RVModel.Hom M N} {ψ : RVModel.Hom N M}
    (h : φ ≈ φ') (he : RVModel.IsEquivalence φ ψ) : RVModel.IsEquivalence φ' ψ where
  comp_left := by
    have : φ'.comp ψ ≈ RVModel.Hom.id M :=
      Setoid.trans (Setoid.symm (RVModel.Hom.comp_aeEq_congr h (Setoid.refl ψ))) he.comp_left
    exact this
  comp_right := by
    have : ψ.comp φ' ≈ RVModel.Hom.id N :=
      Setoid.trans (RVModel.Hom.comp_aeEq_congr (Setoid.refl ψ) (Setoid.symm h)) he.comp_right
    exact this

-- Client need: the same transport at the level of models.  The other way round the rough
-- edge above: `aeEq_equivalence.trans`/`.symm` are stated directly about `AEEq`, so they
-- unify with `IsEquivalence`'s fields without going through `≈` at all.
example {I J : Type} [Finite I] [Finite J] {M : RVModel I} {N : RVModel J}
    {φ φ' : RVModel.Hom M N} {ψ : RVModel.Hom N M}
    (h : φ ≈ φ') (he : RVModel.IsEquivalence φ ψ) : RVModel.Equivalent M N :=
  ⟨φ', ψ, ⟨RVModel.Hom.aeEq_equivalence.trans
      (RVModel.Hom.aeEq_equivalence.symm (RVModel.Hom.comp_aeEq_congr h (Setoid.refl ψ)))
      he.comp_left,
    RVModel.Hom.aeEq_equivalence.trans
      (RVModel.Hom.comp_aeEq_congr (Setoid.refl ψ) (Setoid.symm h)) he.comp_right⟩⟩

/-! ## §4 — perfect condensation, Theorem 4.9, and Theorem 4.15

Everything in this section is generic over an arbitrary client model, which is the honest
client shape for §4: nothing here needs a concrete sample space.  Worth recording about the
section as a whole — a §4 client composes `Condensation.*` endpoints and never touches the
entropy layer directly, so the `ShannonInformation` bare-name hazard never arises. -/

section Four

universe u v w

variable {I : Type*} [Finite I] {M : RVModel I}

-- Client need: "my latent model's *cheap* score already undershoots the entropy it is
-- supposed to explain — what does that buy me?"  The whole chain (4.6) collapses in one
-- `linarith`: all four quantities of Proposition 4.2 coincide.
example (L : LatentModel M) (A : Finset I) (h : L.simpleScore A ≤ H[M.joint A ; M.P]) :
    L.simpleScore A = L.condScore A ∧ L.condScore A = H[L.jointContrib A ; L.P] ∧
      H[L.jointContrib A ; L.P] = H[M.joint A ; M.P] := by
  have h1 := L.simpleScore_ge_condScore A
  have h2 := L.condScore_ge_entropy_jointContrib A
  have h3 := L.entropy_jointContrib_ge_entropy_joint A
  exact ⟨by linarith, by linarith, by linarith⟩

-- Client need: comparing two candidate latent models by score.  Proposition 4.2's chain is
-- what makes the comparison one-sided — `H(X_A)` is the floor every candidate shares.
example (L L' : LatentModel M) (A : Finset I) (h : L.condScore A ≤ L'.simpleScore A) :
    H[M.joint A ; M.P] ≤ L'.simpleScore A :=
  (L.entropy_joint_le_condScore A).trans h

-- Client need: a simple-perfect condensation reconstructs every latent from a *single*
-- observable.  Definition 4.3's squeeze through `PerfectlyCondenses.of_simply`, then
-- Corollary 4.6.  Rough edge kept visible: `of_simply` lives in the `PerfectlyCondenses`
-- namespace but consumes a `SimplyPerfectlyCondenses`, so `h.of_simply` does not resolve —
-- and since `PerfectlyCondenses` is a `def … : Prop`, the elaborator whnfs the hypothesis
-- to a pi type and looks the field up in `Function`.  Its `L` is explicit too.
example (L : LatentModel M) (h : L.SimplyPerfectlyCondenses) (i : I) (A : PPlus I)
    (hi : i ∈ A) : AEFunctionOf (M.X i ∘ L.π) (L.Y A) L.P :=
  L.aeFunctionOf_of_perfectlyCondenses (LatentModel.PerfectlyCondenses.of_simply L h) i A hi

-- Client need: "hand me a latent variable model that provably perfectly condenses
-- something."  Example 4.4 turns any jointly-independent family indexed by `P⁺I` into a
-- model it simply-perfectly condenses; (4.21) upgrades that to perfect condensation, and
-- Lemma 4.5 read backwards hands back the entropy identity for free.
example (L : RVModel (PPlus I)) (hindep : iIndepFun L.X L.P) :
    (Example44.L44 L).PerfectlyCondenses ∧
      ∀ A : PPlus I, H[(Example44.L44 L).jointContrib A.toFinset ; (Example44.L44 L).P]
        = H[(Example44.M44 L).joint A.toFinset ; (Example44.M44 L).P] := by
  have hp : (Example44.L44 L).PerfectlyCondenses :=
    LatentModel.PerfectlyCondenses.of_simply _ (Example44.simplyPerfectlyCondenses L hindep)
  exact ⟨hp, (Example44.L44 L).perfect_entropy_iff_aeFunctionOf.mpr
    ((Example44.L44 L).aeFunctionOf_of_perfectlyCondenses hp)⟩

-- Client need: no hypothesis on `M` at all — every random variable model has a latent
-- variable model (`ofJoint`), and Proposition 4.2's outer ends sandwich its two scores.
example (M : RVModel I) (A : Finset I) :
    H[M.joint A ; M.P] ≤ (LatentModel.ofJoint M).condScore A ∧
      (LatentModel.ofJoint M).condScore A ≤ (LatentModel.ofJoint M).simpleScore A :=
  ⟨(LatentModel.ofJoint M).entropy_joint_le_condScore A,
    (LatentModel.ofJoint M).simpleScore_ge_condScore A⟩

-- Client need: the *existential* form — "some latent variable model does at least this
-- well" — which is what a client states with no candidate in hand.  Rough edge kept
-- visible, and it is the one place in this file where an explicit universe annotation is
-- unavoidable: `LatentModel` has two universe parameters that do not appear in `M`, so a
-- bare `∃ L : LatentModel M, …` auto-binds them to fresh levels and `ofJoint M` — which
-- lands at `LatentModel.{u, v, w, u, max v w} M` — no longer fits.  Worse, the failure is
-- misreported: with `open ProbabilityTheory` in scope `⟨_, _⟩` is overloaded against the
-- random-variable pairing notation, so the error names the anonymous constructor and never
-- mentions universes.
example {I : Type w} [Finite I] (M : RVModel.{u, v, w} I) (A : Finset I) :
    ∃ L : LatentModel.{u, v, w, u, max v w} M, H[M.joint A ; M.P] ≤ L.condScore A :=
  ⟨LatentModel.ofJoint M, (LatentModel.ofJoint M).entropy_joint_le_condScore A⟩

-- Client need: "I proved my condensation is perfect; give me conditional independence I
-- can actually apply."  Theorem 4.9's (B1 ⇒ B2) is the `.mp` of an ordinary `↔` — *not* a
-- `TFAE`, despite `perfect_tfae_B`'s name — whose second component is Definition 4.8's
-- ordered Markov condition; Proposition 4.10 converts that into the upward-closed form.
example (L : LatentModel M) (h : L.PerfectlyCondenses)
    (F G : Set (PPlus I)) (hF : IsUpperSet F) (hG : IsUpperSet G) :
    CondIndepFun (L.jointOn F) (L.jointOn G) (L.jointOn (F ∩ G)) L.P :=
  L.L.orderedMarkov_iff.mp (L.perfect_tfae_B.mp h).2 F G hF hG

-- Client need: the concrete instance of the previous example a downstream project reaches
-- for — conditioning on the latents above `A ∪ B` makes those above `A` independent of
-- those above `B`.
example [DecidableEq I] (L : LatentModel M) (h : L.PerfectlyCondenses) (A B : Finset I) :
    CondIndepFun (L.jointOn (above A)) (L.jointOn (above B))
      (L.jointOn (above (A ∪ B))) L.P := by
  have hci := L.L.orderedMarkov_iff.mp (L.perfect_tfae_B.mp h).2
    (above A) (above B) (isUpperSet_above A) (isUpperSet_above B)
  have hAB : above A ∩ above B = above (A ∪ B) := by
    ext C; simp [Finset.union_subset_iff]
  rwa [hAB] at hci

-- Client need: project one implication (A1 ⇒ A3) out of Theorem 4.9's (A1)–(A3)
-- `List.TFAE` bundle.  Unlike `APITests/FiniteFactoredSets.lean`'s Proposition 10 test,
-- `List.TFAE.out` needs no explicitly typed `have` here — its index autoparams do
-- elaborate in term position against a concrete three-element list.
example (L : LatentModel M) (h : L.SimplyPerfectlyCondenses) :
    L.PerfectlyCondenses ∧ iIndepFun L.Y L.P :=
  (L.perfect_tfae_A.out 0 2).mp h

-- Client need: Lemma 4.14 with its conditional-independence side condition *supplied* by
-- the API rather than assumed — Theorem 4.9 (B1 ⇒ B2) feeds Proposition 4.10, which
-- discharges it.  All the instance arguments on the pi-typed ranges are found by search.
example (L : LatentModel M) (h : L.PerfectlyCondenses)
    {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] {Z : L.Λ → S}
    (hZ : Measurable Z) (F G : Set (PPlus I)) (hF : IsUpperSet F) (hG : IsUpperSet G)
    (h₁ : AEFunctionOf (⟨L.jointOn (F ∩ G), L.jointOn F⟩) Z L.P)
    (h₂ : AEFunctionOf (⟨L.jointOn (F ∩ G), L.jointOn G⟩) Z L.P) :
    AEFunctionOf (L.jointOn (F ∩ G)) Z L.P :=
  aeFunctionOf_of_condIndepFun hZ (L.L.measurable_jointOn F) (L.L.measurable_jointOn G)
    (L.L.measurable_jointOn (F ∩ G))
    (L.L.orderedMarkov_iff.mp (L.perfect_tfae_B.mp h).2 F G hF hG) h₁ h₂

-- Client need: Proposition 4.7 as a *consequence* rather than a restatement — Corollary
-- 4.6 feeds its `↔`, so a perfect condensation makes `(Λ, (X_i))` and `(Λ, (Y_∩{i}))`
-- equivalent in the sense of Definition 3.10.  Rough edge kept visible: the right-hand side
-- is a bare four-fold existential over the morphism data, so a client cannot *name* this
-- conclusion without copying eight lines of binders; a bundled abbreviation would make it
-- one line.
example (L : LatentModel M) (h : L.PerfectlyCondenses) :
    ∃ (g : ∀ i, L.pullbackModel.R i → L.contribModel.R i)
      (hg : ∀ i, ∀ᵐ l ∂L.pullbackModel.P,
        L.contribModel.X i (id l) = g i (L.pullbackModel.X i l))
      (k : ∀ i, L.contribModel.R i → L.pullbackModel.R i)
      (hk : ∀ i, ∀ᵐ l ∂L.contribModel.P,
        L.pullbackModel.X i (id l) = k i (L.contribModel.X i l)),
      RVModel.IsEquivalence
        (RVModel.Hom.ofSameIndex L.pullbackModel L.contribModel id
          (MeasurePreserving.id L.P) g hg)
        (RVModel.Hom.ofSameIndex L.contribModel L.pullbackModel id
          (MeasurePreserving.id L.P) k hk) :=
  L.aeFunctionOf_iff_isEquivalence_contribModel.mp (L.aeFunctionOf_of_perfectlyCondenses h)

section Fifteen

variable {L₁ L₂ : LatentModel M}

-- Client need: a *single* perfect condensation is already rigid — each latent `Y_A` is a.e.
-- recoverable from the family `Y_⊇A` above it, on `L`'s own space with `L`'s own measure.
-- `LatentAmalgamation.diagonal L` is the amalgamation Theorem 4.15 needs, so no fibre
-- product and no Lemma 4.13 are involved.  Note that Theorem 4.15 is root-level and takes
-- `Am` as its *third* explicit argument: `Am.aeFunctionOf_jointAbove_of_…` does not resolve.
example (L : LatentModel M) (h : L.PerfectlyCondenses) (A : PPlus I) :
    AEFunctionOf (L.jointAbove A.toFinset) (L.Y A) L.P :=
  (aeFunctionOf_jointAbove_of_perfectlyCondenses h h (LatentAmalgamation.diagonal L) A).1

-- Client need: Theorem 4.15 is stronger than it reads — the other model's family above a
-- *smaller* index set already determines this model's latent at a larger one.
example (h₁ : L₁.PerfectlyCondenses) (h₂ : L₂.PerfectlyCondenses)
    (Am : LatentAmalgamation L₁ L₂) {A B : PPlus I} (hAB : A ≤ B) :
    AEFunctionOf (Am.lat₂.jointAbove A.toFinset) (Am.lat₁.Y B) Am.P₀ :=
  (Am.lat₂.L.aeFunctionOf_jointOn_mono (above_mono (PPlus.le_iff.mp hAB)) Am.P₀).trans
    (aeFunctionOf_jointAbove_of_perfectlyCondenses h₁ h₂ Am B).1

-- Client need: scores computed inside an amalgamation are the scores of the models you
-- started with — on both sides, and `symm` really does swap them.
example (Am : LatentAmalgamation L₁ L₂) (A : Finset I) :
    Am.lat₁.condScore A = L₁.condScore A ∧ Am.symm.lat₁.condScore A = L₂.condScore A :=
  ⟨Am.condScore_lat₁ A, Am.symm.condScore_lat₁ A⟩

-- Client need: know, before building anything on top of `diagonal`, that its derived data
-- really is `L`'s.  All four identifications hold by `rfl`, so no transport is ever needed.
example (L : LatentModel M) (A : PPlus I) :
    (LatentAmalgamation.diagonal L).P₀ = L.P ∧
      (LatentAmalgamation.diagonal L).lat₁.Y A = L.Y A ∧
      (LatentAmalgamation.diagonal L).lat₂.Y A = L.Y A ∧
      (LatentAmalgamation.diagonal L).lat₁.π = L.π :=
  ⟨rfl, rfl, rfl, rfl⟩

end Fifteen

end Four

/-! ## §5 — Theorem 5.8 and the polar -/

-- Client need: Theorem 5.8 at the smallest tree that satisfies its hypotheses.  With
-- `F = {B}` the tree is a single leaf, so the tree sum is empty and the `F`-sum is one
-- term, and (5.13) collapses to `H (Y_⊇A | Z_{∩B}) ≤ H (Y_⊇A | X_B)`.  Worth noting what
-- this did *not* need: `LatentAmalgamation` carries every finiteness and probability
-- instance as a field, so there is no `haveI` and no `(μ := …)` anywhere here.
example {I : Type} [Finite I] {M : RVModel I}
    {L₁ L₂ : LatentModel M} (Am : LatentAmalgamation L₁ L₂) (A B : PPlus I) :
    H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (contrib B.toFinset) ; Am.P₀]
      ≤ H[Am.lat₁.jointAbove A.toFinset | Am.lat₁.pullbackJoint B.toFinset ; Am.P₀] := by
  have hfam : famFinset ({B} : Set (PPlus I)) = {B} := by ext C; simp
  have h := condEntropy_jointAbove_le Am A {B} (.leaf (contrib B.toFinset))
    (by simpa using isUpperSet_contrib (I := I) B.toFinset)
    (by rw [hfam]; rfl)
  rw [polar_singleton] at h
  simpa [hfam] using h

-- Client need: the first *non-degenerate* tree — two leaves, one internal vertex — which
-- is where (5.13)'s second sum stops being empty.  Reading it at `F = {B₁, B₂}` gives the
-- two-source bound with its single interaction term made explicit.  Rough edge kept
-- visible: discharging the leaf-multiset hypothesis at two leaves needs `classical` and
-- `Finset.insert_val_of_notMem` to expose `({B₁, B₂} : Finset _).val` as `B₁ ::ₘ {B₂}`.
example {I : Type} [Finite I] {M : RVModel I}
    {L₁ L₂ : LatentModel M} (Am : LatentAmalgamation L₁ L₂) (A B₁ B₂ : PPlus I)
    (hne : B₁ ≠ B₂) :
    H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (polar {B₁, B₂}) ; Am.P₀]
      ≤ (H[Am.lat₁.jointAbove A.toFinset | Am.lat₁.pullbackJoint B₁.toFinset ; Am.P₀]
          + H[Am.lat₁.jointAbove A.toFinset | Am.lat₁.pullbackJoint B₂.toFinset ; Am.P₀])
        + I[Am.lat₂.jointOn (contrib B₁.toFinset) : Am.lat₂.jointOn (contrib B₂.toFinset) |
            Am.lat₂.jointOn (contrib B₁.toFinset ⊓ contrib B₂.toFinset) ; Am.P₀] := by
  classical
  have hne' : B₁ ∉ ({B₂} : Finset (PPlus I)) := by simpa using hne
  have hfam : famFinset ({B₁, B₂} : Set (PPlus I)) = ({B₁, B₂} : Finset (PPlus I)) := by
    ext C; simp
  have hval : ({B₁, B₂} : Finset (PPlus I)).val = B₁ ::ₘ {B₂} :=
    Finset.insert_val_of_notMem hne'
  have h := condEntropy_jointAbove_le Am A {B₁, B₂}
    (.node (.leaf (contrib B₁.toFinset)) (.leaf (contrib B₂.toFinset)))
    (by simp [isUpperSet_contrib])
    (by rw [hfam, hval]; rfl)
  simpa [hfam, Finset.sum_insert hne'] using h

-- Client need: any member of `F` already bounds the polar, so a client can discard the
-- rest of `F` when it only needs one containment (Definition 5.5 antitone + the singleton
-- computation).
example {I : Type} {F : Set (PPlus I)} {B : PPlus I} (hB : B ∈ F) :
    polar F ⊆ contrib B.toFinset := by
  rw [← polar_singleton B]
  exact polar_antitone (Set.singleton_subset_iff.2 hB)

-- Client need: Corollary 5.9 at the one-leaf tree, which is where its bound becomes a
-- single reconstruction score: `H (Y_⊇A | Z_{∩B}) ≤ ϱ_Y(B)` for any `B ≤ A`.  No ordered
-- Markov hypothesis is needed, because a one-leaf tree has no internal vertices.
example {I : Type} [Finite I] {M : RVModel I}
    {L₁ L₂ : LatentModel M} (Am : LatentAmalgamation L₁ L₂) (A B : PPlus I) (hBA : B ≤ A) :
    H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (contrib B.toFinset) ; Am.P₀]
      ≤ Am.lat₁.reconScore B.toFinset := by
  have hfam : famFinset ({B} : Set (PPlus I)) = {B} := by ext C; simp
  have h := condEntropy_jointAbove_le_reconScore Am A {B}
    (by rintro C (rfl : C = B); exact hBA) (.leaf (contrib B.toFinset))
    (by simpa using isUpperSet_contrib (I := I) B.toFinset)
    (by rw [hfam]; rfl)
  rw [polar_singleton] at h
  simpa [hfam] using h

-- Client need: Corollary 5.10's (5.24) at `k = 1` says the polar of the singletons of `A`
-- is exactly the upward cone `{C : A ⊆ C}` of (3.6) — the identification a client needs to
-- read (5.25) as a statement about `Y_⊇A`'s own conditioning family.
example {I : Type} [DecidableEq I] (A : PPlus I) :
    polar (kSubsets A 1) = above A.toFinset := by
  rw [polar_kSubsets A le_rfl]
  ext C
  simp [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

end APITests.Condensation
