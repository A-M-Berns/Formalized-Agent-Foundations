import Condensation.ChainRule
import Condensation.Morphism

/-!
# Condensation §4 — perfect condensation

This file is §4 of Eisenstat, *Condensation: A Theory of Concepts*, up to and including
Proposition 4.10:

* **Proposition 4.2** — the chain of lower bounds (4.6)
  `σ_L(A) ≥ χ_L(A) ≥ H(Y_∩A) ≥ H(X_A)`, as three separate inequalities;
* **Definition 4.3** — `LatentModel.PerfectlyCondenses` and
  `LatentModel.SimplyPerfectlyCondenses`;
* **Lemma 4.5** — `H(Y_∩A) = H(X_A)` for all `A` iff every `Y_A` with `i ∈ A` is a.e. a
  function of `X_i`;
* **Corollary 4.6** — a perfect condensation satisfies that functional-dependence clause;
* **Proposition 4.7** — the same clause, restated as an equivalence of random variable
  models between `(Λ, (X_i))` and `(Λ, (Y_∩{i}))`;
* **Definition 4.8** — the ordered Markov condition (`RVModel.OrderedMarkov`);
* **Theorem 4.9** — the (A1)–(A3) and (B1)–(B2) equivalences;
* **Proposition 4.10** — the upward-closed reformulation of the ordered Markov condition.

## Modeling decisions

* **`H(X_A)` is measured on `Ω`, `H(Y_∩A)` on `Λ`.**  The paper's (4.6) puts all four
  quantities on one line, silently using convention (2.2) to read `X_A` as a variable on
  `Λ`.  Here `H[M.joint A ; M.P]` is the literal `H(X_A)` on the base space and the bridge
  is `entropy_comp_measurePreserving` applied to `L.pullbackJoint A` (`dd:pullback`); the
  Lean statements are therefore the printed ones, not their pullbacks.

* **Proposition 4.2 quantifies over `Finset I`, not `PPlus I`.**  The paper says "for any
  `A ⊆ I`", which includes `A = ∅`.  Nothing degenerates there: `contrib ∅ = ∅`, so both
  scores are the empty sum `0`, `Y_∩∅` and `X_∅` are maps into a subsingleton, and all four
  entropies are `0`.  Same choice, for the same reason, in Definition 4.3 — so the
  `Finset I` and `P⁺I` readings of Definition 4.3 agree.

* **Definition 4.8 is stated over a bare `RVModel (PPlus I)`**, not over a latent variable
  model.  The paper says "`(Y_A)_{A ∈ P⁺I}` are random variables on some probability
  space" — there is no `M`, no `π`, and no contribution condition in sight.  A latent
  variable model `L` supplies such a model as `L.L`, which is how Theorem 4.9 (B2) and
  Proposition 4.10 consume it.

* **`CondIndepFun` argument order.**  `ProbabilityTheory.CondIndepFun f g h μ` (PFR,
  `PFR/ForMathlib/ConditionalIndependence.lean:105`) says *`f` and `g` are conditionally
  independent given `h`* — the conditioning variable is the **third** argument, and the
  definition unfolds to `∀ᵐ z ∂(μ.map h), IndepFun f g (μ[|h ← z])`.  Definition 4.8's
  "`Y_A` and `Y_F` are independent conditional on `Y_⊋A`" is therefore
  `CondIndepFun (N.X A) (N.jointOn (incomparable A)) (N.jointOn (strictAbove A.toFinset))`.

* **`incomparable` carries no paper node, and "upward closed" is Mathlib's `IsUpperSet`.**
  Like `contrib`/`above`, `incomparable` is an auxiliary *index family*, not the object
  Definition 4.8 is about; annotating it would attach the node to a set rather than to the
  independence statement.  It lives beside them in `Model.lean`.  Proposition 4.10's
  "upward closed" is `IsUpperSet` for `PPlus I`'s inclusion order — the same predicate,
  taken from Mathlib rather than redefined (the earlier local `IsUpwardClosed` was a
  synonym and is retired).

* **Erratum #1 (`P I` for `P⁺I`)**: Lemma 4.5 clause (2) and Corollary 4.6 print `A ∈ P I`;
  the intended index set is `P⁺I`, which is what the surrounding clauses quantify over.
  The Lean statements use `PPlus I`.  Benign — for `i ∈ A` the set `A` is nonempty anyway.

* **Erratum #4 (Theorem 4.9 (B2) drops "almost everywhere")**: (A2) reads "is a function of
  `X_i` almost everywhere" and the parallel (B2) omits the qualifier.  Both are rendered
  with `AEFunctionOf`; see `Condensation/notes/paper-errata.md` entry 4.

* **Erratum #3 (Corollary 4.6's proof cites only Proposition 4.2)**: the argument also
  needs Lemma 4.5's `(1) ⇒ (2)`.  The Lean proof uses both, as recorded in the docstring.

* **Proposition 4.7 clause (2) is Definition 3.10, not a local surrogate.**  The two
  models it compares are named here — `LatentModel.pullbackModel` is `(Λ, (X_i)_{i∈I})`
  and `LatentModel.contribModel` is `(Λ, (Y_∩{i})_{i∈I})`, both over the index set `I` and
  the sample space `Λ` — and the clause is `RVModel.IsEquivalence` (Definition 3.10)
  applied to the two "obvious triples" `RVModel.Hom.ofSameIndex` of the paragraph that
  follows it, at `π = ρ = id_Λ`.  That is exactly the printed "via an equivalence of the
  form `(id_Λ, id_I, (g_i))` and `(id_Λ, id_I, (h_i))`": `ofSameIndex` fixes `ι = id_I` by
  construction and the two `id_Λ`s are supplied explicitly.  The two models carry no paper
  node — they are the objects Proposition 4.7's `↔` is *about*, and that `↔` is the node.
  (An earlier draft of this file, written while `Morphism.lean` was a concurrent shard,
  spelled the clause as a local `ContribEquivalence`; it is retired.  It differed from the
  present statement only by two `Measurable (g i)` conjuncts, which Definition 3.5
  deliberately does not ask for — the paper's own remark is that the `f_j` of a morphism
  are automatically measurable on countable discrete ranges.)

* **`Y_∩{i}` versus `Y_∋i`.**  Proposition 4.7 writes `Y_∩{i}`; equation (3.9)
  (`contribIdx_eq_contrib_singleton`) identifies the two *families* as sets.  The dependent
  products `∀ B : contribIdx i, _` and `∀ B : contrib {i}, _` are nevertheless different
  **types**, so this file uses `contribIdx i` throughout and never rewrites along (3.9).
-/

universe u v w u' v'

namespace Condensation

-- `Real` is deliberately *not* opened: it would make `π` notation for `Real.pi`, which
-- collides with `LatentModel`'s field name `π`.
open MeasureTheory ProbabilityTheory

/-! ## Note on the machinery this file runs on

The linear-extension argument that Proposition 4.2 (4.7)–(4.9), Theorem 4.9 (4.29)–(4.36)
and Proposition 4.10 (4.38) all run on, together with the chain rule for a *finite family*
of variables along a linear order that the vendored library does not have (it stops at
`chain_rule`, `chain_rule'`, `chain_rule''`, `cond_chain_rule`, `cond_chain_rule'`), lives
in `Condensation/ChainRule.lean`: `exists_revIncl_strictTotalOrder` and
`exists_revIncl_strictTotalOrder_incomparable_first` are the two orders, and
`RVModel.entropy_jointOn_eq_sum` / `RVModel.condEntropy_jointOn_eq_sum` the expansion.
`RVModel.condEntropy_jointOn_mono` is (4.8), and the two bridges
`RVModel.condEntropy_jointOn_eq_of_condIndepFun` /
`RVModel.condIndepFun_of_condEntropy_jointOn_eq` are the termwise equalities
(4.30)/(4.32), (4.35) and (4.40).

The generic facts about `RVModel.joint`/`RVModel.jointOn` and the index families of
Definition 3.4 that this file runs on — `RVModel.functionOf_jointOn_mono`,
`RVModel.aeFunctionOf_jointOn_mono`, `contribIdx_subset_contrib`,
`RVModel.functionOf_joint`, `RVModel.entropy_joint_singleton` and
`LatentModel.entropy_pullbackJoint` — live in `Condensation/Model.lean`, beside the
`measurable_joint(On)` / `finiteEntropy_joint(On)` companions they belong with. -/

namespace LatentModel

variable {I : Type*} [Finite I] {M : RVModel I} (L : LatentModel M)

/-! ## Proposition 4.2 — the lower bounds (4.6) -/

/-- `X_A` is a.e. a function of `Y_∩A` — "by definition", as the last line of the proof of
Proposition 4.2 puts it: each `X_i` with `i ∈ A` is a.e. a function of `Y_∋i` by
Definition 3.2, and `Y_∋i` is a coordinate restriction of `Y_∩A`. -/
lemma aeFunctionOf_jointContrib_pullbackJoint (A : Finset I) :
    AEFunctionOf (L.jointContrib A) (L.pullbackJoint A) L.P :=
  AEFunctionOf.pi fun i : A =>
    (L.L.aeFunctionOf_jointOn_mono (contribIdx_subset_contrib i.2) L.P).trans (L.contributes i)

/-- The first inequality of **(4.6)**: `σ_L(A) ≥ χ_L(A)`.  "It is immediate", says the
paper — termwise, each summand of `χ_L` conditions the corresponding summand of `σ_L`.

Paper node: `Proposition 4.2` -/
theorem simpleScore_ge_condScore (A : Finset I) : L.condScore A ≤ L.simpleScore A :=
  Finset.sum_le_sum fun B _ =>
    ShannonInformation.condEntropy_le_entropy (μ := L.P) (L.L.measurable_X B)
      (L.L.measurable_jointOn _)

/-- The second inequality of **(4.6)**: `χ_L(A) ≥ H(Y_∩A)`.  The paper's proof extends the
reverse-inclusion partial order on `{B : B ∩ A ≠ ∅}` to a total order `⪯`, drops from
conditioning on `Y_⊋B` to conditioning on `Y_{C ≺ B}` by nonnegativity of mutual
information (4.8), and recognises the resulting sum as a chain-rule expansion of
`H(Y_∩A)` (4.9).

Paper node: `Proposition 4.2` -/
theorem condScore_ge_entropy_jointContrib (A : Finset I) :
    H[L.jointContrib A ; L.P] ≤ L.condScore A := by
  obtain ⟨r, hr, hrev⟩ := exists_revIncl_strictTotalOrder (I := I)
  haveI := hr
  have hcoe : ((famFinset (contrib A) : Finset (PPlus I)) : Set (PPlus I)) = contrib A := by
    ext B; simp
  have hexp := L.L.entropy_jointOn_eq_sum r (famFinset (contrib A))
  rw [hcoe] at hexp
  rw [show L.jointContrib A = L.L.jointOn (contrib A) from rfl, hexp]
  refine Finset.sum_le_sum fun B hB => ?_
  -- (4.8): every strict superset of `B` already contributes to `A`, and precedes `B` in
  -- `r`, so `Y_⊋B` is a coordinate restriction of `Y_{C ≺ B}` and conditioning on the
  -- larger family can only decrease the entropy.
  refine L.L.condEntropy_jointOn_mono (L.L.measurable_X B) fun C hC => ?_
  obtain ⟨i, hiA, hiB⟩ := mem_famFinset.mp hB
  have hBC : B < C := PPlus.lt_iff.mpr hC
  exact ⟨mem_famFinset.mpr ⟨i, hiA, PPlus.le_iff.mp hBC.le hiB⟩, hrev C B hBC⟩

/-- The third inequality of **(4.6)**: `H(Y_∩A) ≥ H(X_A)`.  `X_A` is a.e. a function of
`Y_∩A` by Definition 3.2, and entropy is monotone under a.e. functional dependence.

`H(X_A)` is the entropy on `Ω`; the bridge to `Λ` is convention (2.2)
(`entropy_pullbackJoint`).

Paper node: `Proposition 4.2` -/
theorem entropy_jointContrib_ge_entropy_joint (A : Finset I) :
    H[M.joint A ; M.P] ≤ H[L.jointContrib A ; L.P] := by
  rw [← L.entropy_pullbackJoint A]
  exact entropy_le_of_aeFunctionOf (L.L.measurable_jointOn _)
    (L.aeFunctionOf_jointContrib_pullbackJoint A)

/-- The **outer two ends** of the chain (4.6): `H(X_A) ≤ χ_L(A)`, obtained by composing the
last two of the three inequalities above.  This is a single inequality, not the chain
itself — the chain `σ_L(A) ≥ χ_L(A) ≥ H(Y_∩A) ≥ H(X_A)` is the three theorems
`simpleScore_ge_condScore`, `condScore_ge_entropy_jointContrib` and
`entropy_jointContrib_ge_entropy_joint`, which are what carry the paper-node annotation
for Proposition 4.2.

A consequence of the chain rather than a node of the paper, so it carries no paper-node
annotation; it is inventoried in `AxiomAudit.lean` among the un-annotated conveniences. -/
lemma entropy_joint_le_condScore (A : Finset I) : H[M.joint A ; M.P] ≤ L.condScore A :=
  (L.entropy_jointContrib_ge_entropy_joint A).trans (L.condScore_ge_entropy_jointContrib A)

/-- The two outer ends of (4.6) again, one step further out: `H(X_A) ≤ σ_L(A)`.  Like
`entropy_joint_le_condScore`, a consequence of the chain rather than a node of the paper,
and un-annotated for the same reason. -/
lemma entropy_joint_le_simpleScore (A : Finset I) : H[M.joint A ; M.P] ≤ L.simpleScore A :=
  (L.entropy_joint_le_condScore A).trans (L.simpleScore_ge_condScore A)

/-! ## Definition 4.3 — perfect and simple-perfect condensation -/

/-- `L` **perfectly condenses** `M`: `χ_L(A) = H(X_A)` for all `A ⊆ I`.

The quantifier ranges over `Finset I`, matching the paper's "for all `A ⊆ I`".  It could
equally range over `P⁺I`: at `A = ∅` the family `contrib ∅` is empty, so `χ_L(∅)` is the
empty sum `0`, while `X_∅` is a map into a subsingleton and `H(X_∅) = 0` too.  The two
readings therefore agree, and the `Finset I` one is the printed one.

Paper node: `Definition 4.3` -/
def PerfectlyCondenses : Prop := ∀ A : Finset I, L.condScore A = H[M.joint A ; M.P]

/-- `L` **simply-perfectly condenses** `M`: `σ_L(A) = H(X_A)` for all `A ⊆ I`.  The
quantifier ranges over `Finset I` for the same reason as in `PerfectlyCondenses`, and the
`A = ∅` instance is again `0 = 0`.

Paper node: `Definition 4.3` -/
def SimplyPerfectlyCondenses : Prop := ∀ A : Finset I, L.simpleScore A = H[M.joint A ; M.P]

/-- A simple-perfect condensation is a perfect condensation: this is the squeeze
`σ_L(A) ≥ χ_L(A) ≥ H(X_A) = σ_L(A)` of (4.21).

Carries no paper-node annotation — (4.21) is a step inside a proof, not a numbered node — so
it is inventoried among the un-annotated conveniences of `AxiomAudit.lean`. -/
lemma PerfectlyCondenses.of_simply (h : L.SimplyPerfectlyCondenses) : L.PerfectlyCondenses :=
  fun A => le_antisymm ((h A) ▸ L.simpleScore_ge_condScore A) (L.entropy_joint_le_condScore A)

/-! ## Lemma 4.5 -/

/-- **Lemma 4.5.**  For a latent variable model `L` of `M`, the entropy identity
`H(Y_∩A) = H(X_A)` at every `A ∈ P⁺I` is equivalent to: every latent `Y_A` is a.e. a
function of `X_i`, for every `i ∈ A`.

Clause (2) is printed with `A ∈ P I`; the intended index set is `P⁺I`, which clause (1) and
the `(⇐=)` half of the proof both use (errata entry 1).  Note the argument order of
`AEFunctionOf`: `AEFunctionOf X Y μ` reads "`Y` is a.e. a function of `X`", so here the
*first* argument is the pullback `π^* X_i` and the second is the latent `Y_A`.

Both halves follow the printed proof: `(=⇒)` is (4.12)–(4.13) through Proposition 2.5, and
`(⇐=)` is (4.14)–(4.15).  Neither uses the linear-extension argument, so neither depends on
the still-open half of Proposition 4.2.

Paper node: `Lemma 4.5` -/
theorem perfect_entropy_iff_aeFunctionOf :
    (∀ A : PPlus I, H[L.jointContrib A.toFinset ; L.P] = H[M.joint A.toFinset ; M.P]) ↔
      ∀ (i : I) (A : PPlus I), i ∈ A → AEFunctionOf (M.X i ∘ L.π) (L.Y A) L.P := by
  refine ⟨fun hent i A hiA => ?_, fun h A => ?_⟩
  -- (=⇒): (4.12)–(4.13).  At `A = {i}` the hypothesis reads `H(Y_∋i) = H(X_i)`, and `X_i`
  -- is a.e. a function of `Y_∋i` by Definition 3.2, so `H(Y_∋i | X_i) = 0`; Proposition
  -- 2.5 turns that into a functional dependence, and `Y_A` is a coordinate of `Y_∋i`.
  · have hWmeas : Measurable (L.jointContrib ({i} : Finset I)) := L.L.measurable_jointOn _
    have hZmeas : Measurable (M.X i ∘ L.π) := (M.measurable_X i).comp L.π_pres.measurable
    haveI : ShannonInformation.FiniteEntropyOf (M.X i ∘ L.π) L.P := L.L.finiteEntropyOf hZmeas
    have hZW : AEFunctionOf (L.jointContrib ({i} : Finset I)) (M.X i ∘ L.π) L.P :=
      (L.L.aeFunctionOf_jointOn_mono
        (contribIdx_subset_contrib (Finset.mem_singleton_self i)) L.P).trans (L.contributes i)
    have hent1 := hent (PPlus.single i)
    rw [PPlus.toFinset_single] at hent1
    have hzero : H[L.jointContrib ({i} : Finset I) | M.X i ∘ L.π ; L.P] = 0 := by
      rw [ShannonInformation.chain_rule'' L.P hWmeas hZmeas,
        entropy_pair_of_aeFunctionOf hWmeas hZW, hent1,
        entropy_comp_measurePreserving L.π_pres (M.measurable_X i),
        M.entropy_joint_singleton i, sub_self]
    have hA : A ∈ contrib ({i} : Finset I) := ⟨i, Finset.mem_singleton_self i, hiA⟩
    exact (aeFunctionOf_of_condEntropy_eq_zero hZmeas hWmeas hzero).trans
      (AEFunctionOf.of_functionOf ⟨fun w => w ⟨A, hA⟩, measurable_pi_apply _, fun _ => rfl⟩)
  -- (⇐=): (4.14)–(4.15).  `Y_∩A` is a.e. a function of `X_A` — each `Y_B` with `B ∩ A ≠ ∅`
  -- is a.e. a function of some `X_i`, `i ∈ A ∩ B`, hence of `X_A` — so
  -- `H(Y_∩A) ≤ H(X_A)`, and Proposition 4.2 gives the reverse.
  · refine le_antisymm ?_ (L.entropy_jointContrib_ge_entropy_joint A.toFinset)
    rw [← L.entropy_pullbackJoint A.toFinset]
    refine entropy_le_of_aeFunctionOf (L.measurable_pullbackJoint _)
      (AEFunctionOf.pi fun B : contrib A.toFinset => ?_)
    obtain ⟨i, hiA, hiB⟩ := B.2
    exact (AEFunctionOf.comp_measurePreserving L.π_pres
      (AEFunctionOf.of_functionOf (M.functionOf_joint hiA))).trans (h i B hiB)

/-! ## Corollary 4.6 -/

/-- **Corollary 4.6.**  If `L` perfectly condenses `M` then every latent `Y_A` is a.e. a
function of `X_i`, for every `i ∈ A`.

The printed proof is "Using Proposition 4.2, this follows immediately", which is
incomplete: Proposition 4.2 supplies `H(Y_∩A) = H(X_A)` by squeezing `χ_L(A)` between
`H(Y_∩A)` and `H(X_A)`, but getting from that entropy identity to the functional
dependence is exactly Lemma 4.5's `(1) ⇒ (2)` (errata entry 3).  As with Lemma 4.5, the
printed `i ∈ A ∈ P I` means `P⁺I` (errata entry 1).

Paper node: `Corollary 4.6` -/
theorem aeFunctionOf_of_perfectlyCondenses (h : L.PerfectlyCondenses) :
    ∀ (i : I) (A : PPlus I), i ∈ A → AEFunctionOf (M.X i ∘ L.π) (L.Y A) L.P :=
  L.perfect_entropy_iff_aeFunctionOf.mp fun A =>
    le_antisymm ((h A.toFinset) ▸ L.condScore_ge_entropy_jointContrib A.toFinset)
      (L.entropy_jointContrib_ge_entropy_joint A.toFinset)

/-! ## Proposition 4.7 -/

-- TODO(Definition 3.10): restate via RVModel.Equivalent once Morphism.lean lands
/-- The random variable model `(Λ, (X_i)_{i ∈ I})` that Proposition 4.7 (2) compares:
`M`'s own observables, read on the latent space through the pullback convention (2.2)
(`dd:pullback`).  Same index set and same ranges as `M`; only the sample space changes,
from `Ω` to `Λ`.

Scaffolding for the statement of Proposition 4.7, not a numbered node of its own. -/
def pullbackModel : RVModel I where
  Ω := L.Λ
  P := L.P
  R := M.R
  X := fun i => M.X i ∘ L.π
  measurable_X := fun i => (M.measurable_X i).comp L.π_pres.measurable
  finiteEntropy_X := fun i =>
    L.L.finiteEntropyOf ((M.measurable_X i).comp L.π_pres.measurable)

/-- The random variable model `(Λ, (Y_∩{i})_{i ∈ I})` that Proposition 4.7 (2) compares:
the latent space, carrying at each index `i` the joint latent variable `Y_∋i` of (3.8).

The paper writes `Y_∩{i}`; this uses `contribIdx i`, which equation (3.9)
(`contribIdx_eq_contrib_singleton`) identifies with `contrib {i}` as a *set*.  The two
dependent-product **types** `∀ B : contribIdx i, _` and `∀ B : contrib {i}, _` differ, so
the identification is never used to rewrite.

Scaffolding for the statement of Proposition 4.7, not a numbered node of its own. -/
def contribModel : RVModel I where
  Ω := L.Λ
  P := L.P
  R := fun i => ∀ B : contribIdx i, L.L.R B
  X := L.jointContribIdx
  measurable_X := fun _ => L.L.measurable_jointOn _
  finiteEntropy_X := fun _ => L.L.finiteEntropyOf (L.L.measurable_jointOn _)

@[simp] lemma pullbackModel_X (i : I) : L.pullbackModel.X i = M.X i ∘ L.π := rfl

@[simp] lemma contribModel_X (i : I) : L.contribModel.X i = L.jointContribIdx i := rfl

/-- **Proposition 4.7.**  The conclusion of Corollary 4.6 — every `Y_A` with `i ∈ A` is
a.e. a function of `X_i` — holds exactly when `(Λ, (X_i)_{i∈I})` and `(Λ, (Y_∩{i})_{i∈I})`
are equivalent as random variable models, via an equivalence of the form
`(id_Λ, id_I, (g_i))` and `(id_Λ, id_I, (h_i))`.

Clause (2) is Definition 3.10's `RVModel.IsEquivalence` applied to the two "obvious
triples" of the paragraph that follows Definition 3.10 (`RVModel.Hom.ofSameIndex`, whose
index map is `id_I` by construction), taken at `π = ρ = id_Λ`.  The existential therefore
binds exactly the paper's data: the two families `(g_i)`, `(h_i)` and the proofs that the
triples built from them are morphisms.  Definition 3.5 asks for no measurability of the
`f_j` — the paper's own remark is that it is automatic on countable discrete ranges
(`RVModel.Hom.measurable_f`) — so no measurability conjunct appears here either.

`(⇒)` is (4.16)–(4.17): `g_i` is the product of the `f^i_A` over `A ∋ i`, and `h_i` comes
free from Definition 3.2's contribution condition.  `(⇐)` is (4.18)–(4.20): compose `g_i`
with the coordinate projection `p^i_A`.  Clause (1) of the "laid out" characterization —
`ρ ∘ π` and `π ∘ ρ` a.e. the identity — is trivial here, both maps being `id_Λ`, which is
`RVModel.isEquivalence_ofSameIndex_iff` read at `π = ρ = id`.

Paper node: `Proposition 4.7` -/
theorem aeFunctionOf_iff_isEquivalence_contribModel :
    (∀ (i : I) (A : PPlus I), i ∈ A → AEFunctionOf (M.X i ∘ L.π) (L.Y A) L.P) ↔
      ∃ (g : ∀ i, L.pullbackModel.R i → L.contribModel.R i)
        (hg : ∀ i, ∀ᵐ l ∂L.pullbackModel.P,
          L.contribModel.X i (_root_.id l) = g i (L.pullbackModel.X i l))
        (h : ∀ i, L.contribModel.R i → L.pullbackModel.R i)
        (hh : ∀ i, ∀ᵐ l ∂L.contribModel.P,
          L.pullbackModel.X i (_root_.id l) = h i (L.contribModel.X i l)),
        RVModel.IsEquivalence
          (RVModel.Hom.ofSameIndex L.pullbackModel L.contribModel
            _root_.id (MeasurePreserving.id L.P) g hg)
          (RVModel.Hom.ofSameIndex L.contribModel L.pullbackModel
            _root_.id (MeasurePreserving.id L.P) h hh) := by
  constructor
  · intro hf
    choose h _ hae using fun i => L.contributes i
    refine ⟨fun i => (AEFunctionOf.pi (X := M.X i ∘ L.π)
        (fun B : contribIdx i => hf i B B.2)).choose, ?_, h, hae, ?_⟩
    · intro i
      exact (AEFunctionOf.pi (X := M.X i ∘ L.π)
        (fun B : contribIdx i => hf i B B.2)).choose_spec.2
    · exact ⟨⟨Filter.Eventually.of_forall fun _ => rfl, rfl⟩,
        ⟨Filter.Eventually.of_forall fun _ => rfl, rfl⟩⟩
  · rintro ⟨g, hg, -, -, -⟩ i A hiA
    refine ⟨fun x => g i x ⟨A, hiA⟩, measurable_of_countable _, ?_⟩
    filter_upwards [hg i] with l hl
    exact congrFun hl ⟨A, hiA⟩

end LatentModel

/-! ## Definition 4.8 — the ordered Markov condition -/

section Markov

variable {I : Type*} [Finite I]

/-- **Definition 4.8**: the family `(Y_A)_{A ∈ P⁺I}` satisfies the **ordered Markov
condition** if for every `A ∈ P⁺I`, the variables `Y_A` and `Y_F` are independent
conditional on `Y_⊋A`, where `F` is the family of `B` incomparable to `A` in the inclusion
order.

Stated over a bare `RVModel (PPlus I)`, as the paper does: Definition 4.8 speaks of
"random variables on some probability space", with no `M`, no `π` and no contribution
condition.  A latent variable model supplies one as `L.L`.

`ProbabilityTheory.CondIndepFun f g h μ` (PFR,
`PFR/ForMathlib/ConditionalIndependence.lean:105`) asserts that `f` and `g` are
conditionally independent **given `h`** — the conditioning variable is the third argument,
the definition unfolding to `∀ᵐ z ∂(μ.map h), IndepFun f g (μ[|h ← z])`.  So `Y_⊋A` goes
last.

Paper node: `Definition 4.8` -/
def RVModel.OrderedMarkov (N : RVModel (PPlus I)) : Prop :=
  ∀ A : PPlus I,
    CondIndepFun (N.X A) (N.jointOn (incomparable A)) (N.jointOn (strictAbove A.toFinset)) N.P

/-! ## Proposition 4.10 -/

/-- **Proposition 4.10.**  The ordered Markov condition is equivalent to: for any two
upward-closed families `F, G ⊆ P⁺I`, the variables `Y_F` and `Y_G` are independent
conditional on `Y_{F ∩ G}`.

The paper's hypothesis is that the `Y_A` have finite entropy; here that comes from
Definition 3.1's own clause on `Ω` — the `RVModel` field `finiteEntropy_Ω`, via
`RVModel.finiteEntropyOf` — so no hypothesis is carried locally.  (Until 2026-08-17 it was
supplied by the narrowing `dd:finite-range` instead; that decision is retired.)

Paper node: `Proposition 4.10` -/
theorem RVModel.orderedMarkov_iff (N : RVModel (PPlus I)) :
    N.OrderedMarkov ↔ ∀ F G : Set (PPlus I), IsUpperSet F → IsUpperSet G →
      CondIndepFun (N.jointOn F) (N.jointOn G) (N.jointOn (F ∩ G)) N.P := by
  classical
  have hsymm : ∀ {S₁ S₂ S₃ : Set (PPlus I)},
      CondIndepFun (N.jointOn S₁) (N.jointOn S₂) (N.jointOn S₃) N.P →
      CondIndepFun (N.jointOn S₂) (N.jointOn S₁) (N.jointOn S₃) N.P := by
    intro S₁ S₂ S₃ h
    rw [← ShannonInformation.condMutualInfo_eq_zero (N.measurable_jointOn _)
      (N.measurable_jointOn _) (N.measurable_jointOn _)] at h ⊢
    rwa [ProbabilityTheory.condMutualInfo_comm (N.measurable_jointOn S₂)
      (N.measurable_jointOn S₁)]
  constructor
  · intro hM F G hF hG
    have key : H[N.jointOn G | N.jointOn F ; N.P] =
        H[N.jointOn G | N.jointOn (F ∩ G) ; N.P] := by
      obtain ⟨r, hr, hrev⟩ := exists_revIncl_strictTotalOrder (I := I)
      haveI := hr
      obtain ⟨D, hD⟩ : ∃ D : Finset (PPlus I), (↑D : Set (PPlus I)) = G \ F :=
        ⟨famFinset (G \ F), by ext B; simp⟩
      have hterm : ∀ A ∈ D, ∀ W : Set (PPlus I), F ∩ G ⊆ W → W ⊆ F →
          H[N.X A | N.jointOn ({C | C ∈ D ∧ r C A} ∪ W) ; N.P] =
            H[N.X A | N.jointOn (strictAbove A.toFinset) ; N.P] := by
        intro A hA W hW1 hW2
        have hAD : A ∈ G \ F := by rw [← hD]; exact hA
        refine N.condEntropy_jointOn_eq_of_condIndepFun (N.measurable_X A) (hM A) ?_ ?_
        · intro B hB
          have hAB : A < B := PPlus.lt_iff.mpr hB
          have hBG : B ∈ G := hG hAB.le hAD.1
          simp only [Set.mem_union, Set.mem_setOf_eq]
          by_cases hBF : B ∈ F
          · exact Or.inr (hW1 ⟨hBF, hBG⟩)
          · exact Or.inl ⟨by rw [← Finset.mem_coe, hD]; exact ⟨hBG, hBF⟩, hrev B A hAB⟩
        · intro B hB
          simp only [Set.mem_union, Set.mem_setOf_eq] at hB
          have hnle : ¬ B ≤ A := by
            rcases hB with hBP | hBW
            · intro hBA
              rcases eq_or_lt_of_le hBA with rfl | hlt
              · exact irrefl_of r B hBP.2
              · exact irrefl_of r B (trans_of r hBP.2 (hrev A B hlt))
            · intro hBA
              exact hAD.2 (hF hBA (hW2 hBW))
          simp only [Set.mem_union, mem_incomparable, mem_strictAbove]
          by_cases hAle : A ≤ B
          · exact Or.inr (PPlus.lt_iff.mp
              (lt_of_le_of_ne hAle (fun hc => hnle (hc ▸ le_rfl))))
          · exact Or.inl ⟨hnle, hAle⟩
      have step : ∀ W : Set (PPlus I), F ∩ G ⊆ W → W ⊆ F →
          H[N.jointOn G | N.jointOn W ; N.P] =
            ∑ A ∈ D, H[N.X A | N.jointOn (strictAbove A.toFinset) ; N.P] := by
        intro W hW1 hW2
        have hGW : G \ W = G \ F := by
          ext B
          simp only [Set.mem_sdiff]
          exact ⟨fun h => ⟨h.1, fun hBF => h.2 (hW1 ⟨hBF, h.1⟩)⟩,
            fun h => ⟨h.1, fun hBW => h.2 (hW2 hBW)⟩⟩
        rw [N.condEntropy_jointOn_sdiff G W, hGW, ← hD,
          N.condEntropy_jointOn_eq_sum (N.measurable_jointOn W) r D]
        refine Finset.sum_congr rfl fun A hA => ?_
        rw [N.condEntropy_pair_jointOn (N.measurable_X A) {C | C ∈ D ∧ r C A} W]
        exact hterm A hA W hW1 hW2
      rw [step F Set.inter_subset_left subset_rfl,
        step (F ∩ G) subset_rfl Set.inter_subset_left]
    exact hsymm (N.condIndepFun_of_condEntropy_jointOn_eq (N.measurable_jointOn G)
      (Set.union_subset subset_rfl Set.inter_subset_left) key)
  · intro h2 A
    have hF : IsUpperSet (incomparable A ∪ strictAbove A.toFinset) := by
      rintro B C hBC (hB | hB)
      · have hCA : ¬ C ≤ A := fun h => hB.1 (hBC.trans h)
        by_cases hAC : A ≤ C
        · exact Or.inr (PPlus.lt_iff.mp
            (lt_of_le_of_ne hAC (fun hc => hCA (hc ▸ le_rfl))))
        · exact Or.inl ⟨hCA, hAC⟩
      · exact Or.inr (PPlus.lt_iff.mp (lt_of_lt_of_le (PPlus.lt_iff.mpr hB) hBC))
    have hG : IsUpperSet (above A.toFinset) := isUpperSet_above _
    have hFG : (incomparable A ∪ strictAbove A.toFinset) ∩ above A.toFinset =
        strictAbove A.toFinset := by
      ext B
      constructor
      · rintro ⟨hB | hB, hBG⟩
        · exact absurd (PPlus.le_iff.mpr hBG) hB.2
        · exact hB
      · intro hB
        exact ⟨Or.inr hB, strictAbove_subset_above _ hB⟩
    have h := hsymm (h2 (incomparable A ∪ strictAbove A.toFinset) (above A.toFinset) hF hG)
    rw [hFG] at h
    have e1 : H[N.jointOn (above A.toFinset) |
          N.jointOn (incomparable A ∪ strictAbove A.toFinset) ; N.P] =
        H[N.jointOn (above A.toFinset) | N.jointOn (strictAbove A.toFinset) ; N.P] :=
      N.condEntropy_jointOn_eq_of_condIndepFun (N.measurable_jointOn _) h
        Set.subset_union_right Set.subset_union_left
    have e2 : H[N.jointOn (above A.toFinset) |
          N.jointOn (incomparable A ∪ strictAbove A.toFinset) ; N.P] =
        H[N.X A | N.jointOn (incomparable A ∪ strictAbove A.toFinset) ; N.P] :=
      N.condEntropy_jointOn_above A Set.subset_union_right
    have e3 : H[N.jointOn (above A.toFinset) |
          N.jointOn (strictAbove A.toFinset) ; N.P] =
        H[N.X A | N.jointOn (strictAbove A.toFinset) ; N.P] :=
      N.condEntropy_jointOn_above A subset_rfl
    exact N.condIndepFun_of_condEntropy_jointOn_eq (N.measurable_X A) subset_rfl
      (by rw [← e2, ← e3, e1])

end Markov

/-! ## Theorem 4.9 -/

namespace LatentModel

variable {I : Type*} [Finite I] {M : RVModel I} (L : LatentModel M)

/-- **Theorem 4.9**, the (A1)–(A3) equivalence.  For a latent variable model `L` of `M`,
the following are equivalent:

* (A1) `L` simply-perfectly condenses `M`;
* (A2) every `Y_A` with `i ∈ A` is a.e. a function of `X_i`, and the latents `(Y_A)` are
  jointly independent;
* (A3) `L` perfectly condenses `M`, and the latents `(Y_A)` are jointly independent.

Joint independence is Mathlib's `ProbabilityTheory.iIndepFun`.

Paper node: `Theorem 4.9` -/
theorem perfect_tfae_A :
    List.TFAE
      [L.SimplyPerfectlyCondenses,
        (∀ (i : I) (A : PPlus I), i ∈ A → AEFunctionOf (M.X i ∘ L.π) (L.Y A) L.P) ∧
          iIndepFun L.Y L.P,
        L.PerfectlyCondenses ∧ iIndepFun L.Y L.P] := by
  classical
  -- (A1 ⇒ A3), equations (4.21)–(4.26).
  tfae_have 1 → 3 := by
    intro h1
    refine ⟨PerfectlyCondenses.of_simply L h1, ?_⟩
    letI : Fintype I := Fintype.ofFinite I
    -- Every `B ∈ P⁺I` is nonempty, hence meets `I`: `contrib I` is all of `P⁺I`.
    have hcontrib : contrib (Finset.univ : Finset I) = (Set.univ : Set (PPlus I)) := by
      ext B
      simp only [mem_contrib, Set.mem_univ, iff_true]
      obtain ⟨i, hi⟩ := B.nonempty
      exact ⟨i, Finset.mem_univ i, hi⟩
    have hcoe : ((famFinset (contrib (Finset.univ : Finset I)) : Finset (PPlus I)) :
        Set (PPlus I)) = contrib (Finset.univ : Finset I) := by
      ext B; simp
    refine L.L.iIndepFun_of_entropy_jointOn_eq_sum
      (t := famFinset (contrib (Finset.univ : Finset I)))
      (fun B => mem_famFinset.mpr (hcontrib ▸ Set.mem_univ B)) ?_
    rw [hcoe]
    -- (4.21) at `A = I`: `σ_L(I) ≥ χ_L(I) ≥ H(Y_∩I) ≥ H(X_I) = σ_L(I)`, so `(4.23)`.
    have h2 := L.condScore_ge_entropy_jointContrib (Finset.univ : Finset I)
    have h3 := L.simpleScore_ge_condScore (Finset.univ : Finset I)
    have h4 := L.entropy_jointContrib_ge_entropy_joint (Finset.univ : Finset I)
    have h5 := h1 (Finset.univ : Finset I)
    show H[L.jointContrib (Finset.univ : Finset I) ; L.P] = L.simpleScore Finset.univ
    linarith
  -- (A3 ⇒ A2): Corollary 4.6, carrying the independence conjunct through.
  tfae_have 3 → 2 := fun h => ⟨L.aeFunctionOf_of_perfectlyCondenses h.1, h.2⟩
  -- (A2 ⇒ A1), equations (4.27)–(4.28).
  tfae_have 2 → 1 := by
    rintro ⟨hfun, hindep⟩
    have hent := L.perfect_entropy_iff_aeFunctionOf.mpr hfun
    intro B
    rcases B.eq_empty_or_nonempty with rfl | hB
    · -- `contrib ∅ = ∅`, so `σ_L(∅)` is the empty sum and `X_∅` is a constant.
      have hfam : famFinset (contrib (∅ : Finset I)) = (∅ : Finset (PPlus I)) := by
        ext C; simp
      haveI : IsEmpty ((∅ : Finset I) : Type _) := ⟨fun i => Finset.notMem_empty i.1 i.2⟩
      have hconst : M.joint (∅ : Finset I) =
          fun _ => (default : ∀ i : (∅ : Finset I), M.R i) :=
        funext fun _ => Subsingleton.elim _ _
      calc L.simpleScore (∅ : Finset I)
          = ∑ C ∈ famFinset (contrib (∅ : Finset I)), H[L.L.X C ; L.L.P] := rfl
        _ = 0 := by rw [hfam, Finset.sum_empty]
        _ = H[M.joint (∅ : Finset I) ; M.P] := by rw [hconst, entropy_const]
    · -- (4.28): `σ_L(B) = H(Y_∩B)` by independence, and `H(Y_∩B) = H(X_B)` by Lemma 4.5.
      have hA := hent ⟨B, hB⟩
      have halpha := L.L.entropy_jointOn_eq_sum_of_iIndepFun hindep (famFinset (contrib B))
      have hcoe : ((famFinset (contrib B) : Finset (PPlus I)) : Set (PPlus I)) = contrib B := by
        ext C; simp
      rw [hcoe] at halpha
      calc L.simpleScore B = ∑ C ∈ famFinset (contrib B), H[L.L.X C ; L.L.P] := rfl
        _ = H[L.L.jointOn (contrib B) ; L.L.P] := halpha.symm
        _ = H[M.joint B ; M.P] := hA
  tfae_finish

/-- **Theorem 4.9**, the (B1) ⟺ (B2) equivalence: `L` perfectly condenses `M` if and only
if every `Y_A` with `i ∈ A` is a.e. a function of `X_i` and the latents obey the ordered
Markov condition.

The printed (B2) says "the latent variable `Y_A` is a function of `X_i`", dropping the
"almost everywhere" that the parallel (A2) carries.  The intended reading is the a.e. one —
the whole development is a.e.-based, and the everywhere reading is not implied by (B1),
since a perfect condensation can be modified on a null set.  See
`Condensation/notes/paper-errata.md` entry 4.

Paper node: `Theorem 4.9` -/
theorem perfect_tfae_B :
    L.PerfectlyCondenses ↔
      ((∀ (i : I) (A : PPlus I), i ∈ A → AEFunctionOf (M.X i ∘ L.π) (L.Y A) L.P) ∧
        L.L.OrderedMarkov) := by
  constructor
  · -- (B1 ⇒ B2).  The first conjunct is Lemma 4.5, through Corollary 4.6.
    intro h
    refine ⟨L.aeFunctionOf_of_perfectlyCondenses h, fun A => ?_⟩
    letI : Fintype I := Fintype.ofFinite I
    -- the special order of the paragraph before (4.29): supersets first, and every
    -- element incomparable to `A` before `A`.
    obtain ⟨r, hr, hrev, hinc⟩ := exists_revIncl_strictTotalOrder_incomparable_first A
    haveI := hr
    -- every `B ∈ P⁺I` is nonempty, hence contributes to the full index set
    have huniv : contrib (Finset.univ : Finset I) = (Set.univ : Set (PPlus I)) := by
      ext B
      simp only [mem_contrib, Set.mem_univ, iff_true, Finset.mem_univ, true_and]
      obtain ⟨i, hi⟩ := B.nonempty
      exact ⟨i, hi⟩
    set U : Finset (PPlus I) := famFinset (contrib (Finset.univ : Finset I)) with hU
    have hUall : ∀ C : PPlus I, C ∈ U := fun C => mem_famFinset.mpr (huniv ▸ Set.mem_univ C)
    have hcoe : ((U : Finset (PPlus I)) : Set (PPlus I)) = contrib (Finset.univ : Finset I) := by
      ext C; simp [hU]
    -- (4.29): the perfect-condensation hypothesis squeezes the chain expansion of
    -- `H(Y_{P⁺I})` against `χ_L(I)`, so the two sums are equal.
    have hsq : H[L.L.jointOn (contrib (Finset.univ : Finset I)) ; L.L.P] =
        L.condScore (Finset.univ : Finset I) :=
      le_antisymm (L.condScore_ge_entropy_jointContrib _)
        ((h Finset.univ) ▸ L.entropy_jointContrib_ge_entropy_joint _)
    have hexp := L.L.entropy_jointOn_eq_sum r U
    rw [hcoe] at hexp
    rw [hexp] at hsq
    have hsc : L.condScore (Finset.univ : Finset I) =
        ∑ B ∈ U, H[L.L.X B | L.L.jointOn (strictAbove B.toFinset) ; L.L.P] := rfl
    rw [hsc] at hsq
    -- termwise the left side is `≤` the right, so the equality of sums is termwise
    have hle : ∀ B ∈ U, H[L.L.X B | L.L.jointOn {C | C ∈ U ∧ r C B} ; L.L.P] ≤
        H[L.L.X B | L.L.jointOn (strictAbove B.toFinset) ; L.L.P] := fun B _ =>
      L.L.condEntropy_jointOn_mono (L.L.measurable_X B)
        (fun C hC => ⟨hUall C, hrev C B (PPlus.lt_iff.mpr hC)⟩)
    have hterm := (Finset.sum_eq_sum_iff_of_le hle).mp hsq A (hUall A)
    -- (4.30)–(4.32): read at `B = A`, and `{C | C ≺ A} ⊇ F ∪ {D | D ⊋ A}` by construction
    -- of `r`, so the equality is the desired conditional independence.
    refine L.L.condIndepFun_of_condEntropy_jointOn_eq (L.L.measurable_X A) ?_ hterm
    rintro C (hC | hC)
    · exact ⟨hUall C, hinc C hC⟩
    · exact ⟨hUall C, hrev C A (PPlus.lt_iff.mpr hC)⟩
  · -- (B2 ⇒ B1), equations (4.33)–(4.36).
    rintro ⟨hae, hmk⟩ A
    have hent := L.perfect_entropy_iff_aeFunctionOf.mpr hae
    rcases A.eq_empty_or_nonempty with rfl | hA
    · have hc : contrib (∅ : Finset I) = (∅ : Set (PPlus I)) := by ext B; simp
      have h1 : L.condScore (∅ : Finset I) = 0 := by
        have hfe : famFinset (contrib (∅ : Finset I)) = (∅ : Finset (PPlus I)) := by
          ext B; simp [hc]
        rw [show L.condScore (∅ : Finset I)
          = ∑ B ∈ famFinset (contrib (∅ : Finset I)),
              H[L.Y B | L.jointStrictAbove B.toFinset ; L.P] from rfl, hfe, Finset.sum_empty]
      -- `X_∅` is a map into a subsingleton, but there is no need to say so: the outer two
      -- ends of (4.6) already squeeze `H(X_∅)` between `0` and `χ_L(∅) = 0`.
      rw [h1]
      exact (le_antisymm (h1 ▸ L.entropy_joint_le_condScore (∅ : Finset I))
        (entropy_nonneg _ _)).symm
    · -- (4.34): expand `H(Y_∩A)` along a linear extension of reverse inclusion, then
      -- (4.35): the ordered Markov condition makes each term `H(Y_B | Y_⊋B)`.
      obtain ⟨r, hr, hrev⟩ := exists_revIncl_strictTotalOrder (I := I)
      haveI := hr
      have hcoe : ((famFinset (contrib A) : Finset (PPlus I)) : Set (PPlus I)) = contrib A := by
        ext B; simp
      have hexp := L.L.entropy_jointOn_eq_sum r (famFinset (contrib A))
      rw [hcoe] at hexp
      have key : L.condScore A = H[L.jointContrib A ; L.P] := by
        rw [show L.jointContrib A = L.L.jointOn (contrib A) from rfl, hexp,
          show L.condScore A = ∑ B ∈ famFinset (contrib A),
            H[L.L.X B | L.L.jointOn (strictAbove B.toFinset) ; L.L.P] from rfl]
        refine Finset.sum_congr rfl fun B hB => ?_
        obtain ⟨i, hiA, hiB⟩ := mem_famFinset.mp hB
        refine (L.L.condEntropy_jointOn_eq_of_condIndepFun (L.L.measurable_X B) (hmk B)
          (fun C hC => ?_) ?_).symm
        · exact ⟨mem_famFinset.mpr ⟨i, hiA, PPlus.le_iff.mp (PPlus.lt_iff.mpr hC).le hiB⟩,
            hrev C B (PPlus.lt_iff.mpr hC)⟩
        · exact pred_subset_incomparable_union_strictAbove hrev B (fun C hC => hC.2)
      -- (4.33): `H(Y_∩A) = H(X_A)` is Lemma 4.5 again.
      rw [key]
      exact hent ⟨A, hA⟩

end LatentModel

end Condensation
