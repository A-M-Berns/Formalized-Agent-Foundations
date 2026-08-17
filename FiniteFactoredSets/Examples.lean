import FiniteFactoredSets.ConditionalOrthogonality
import FiniteFactoredSets.Factoring
import FiniteFactoredSets.Inference
import FiniteFactoredSets.Probability

/-!
# Worked factored sets — the non-vacuity witnesses

Every §2–§6 endpoint is stated over `FactoredSet` or, in §6, over `Model`, so until
something exhibits one those endpoints say nothing about anything.  This file exhibits four
factored sets, covering the degenerate sizes Proposition 5 singles out and one genuinely
two-dimensional example that makes the chimera function actually splice, and then runs the
§2.5, §3, §4, §5 and §6 vocabulary — `size`, `dim`, `Generates`, `history`, `Orthogonal`,
`Entangled`, `Before`, `StrictlyBefore`, `Subpartition`, `GeneratesSub`, `historySub`,
`OrthogonalSub`, `OrthogonalGivenSet`, `OrthogonalGiven`, `Q`, `mono`, `monos`, `poly`,
`irr`, `ProbDist`, `IsDistribution`, `Model`, `Model.pullback`, `OrthDatabase`, `Models`,
`Consistent`, `Complete` and `OrthDatabase.Before` — over them.

`coordFS` is the load-bearing one: with a single factor every `C` behaves as `∅` or `B`,
so Proposition 4 would be a family of near-tautologies.  `not_subsingleton_coordFS_basis`
and `coordFS_chimera_corners` are what rule that out — the four `C`-corners of
`χ^F_C((true,true),(false,false))` are pairwise distinct.

The §3 half computes the three histories that pin the whole order down —
`h(fstFactor) = {fstFactor}`, `h(Ind_S) = {}`, `h(Dis_S) = B` — and then exhibits each §3
relation both holding and failing, so that none of `Orthogonal`, `Entangled`, `Before`,
`StrictlyBefore` is silently empty or silently total.  Two negative facts are worth
calling out: `history_not_injective` shows `Before` is a preorder and *not* antisymmetric
(the XOR partition and `Dis_S` are distinct partitions sharing a history), and the
`emptyFS_*` lemmas show the `Nonempty S` hypothesis on Proposition 13 clause 4 and
Proposition 19 is load-bearing rather than decorative.

The §4 half restricts `coordFS`'s factors to two subsets — a block `Efst` of `fstFactor`
and the diagonal `Ediag` (a block of `xorPart`) — and computes domains, blocks,
`GeneratesSub`, `historySub` and conditional orthogonality over them.  Four negative facts
carry most of the weight: generation of a subpartition is **not** monotone in `C`
(`generatesSub_not_superset_monotone`), the second conjunct of Proposition 20 clause 7 is
**not** implied by the first (`clause7_second_conjunct_loadbearing`), the `hE` hypothesis
of Proposition 23 clause 2 is load-bearing (`historySub_spec_hE_loadbearing`), and
restriction can **entangle** two unconditionally orthogonal partitions
(`not_orthogonalGivenSet_Ediag`, `not_orthogonalGiven_fst_snd_xorPart`) — which is what
stops `OrthogonalGiven` from being silently total.

The §5 half computes the characteristic polynomial of `coordFS` outright.  `Q^F_{S}` is
the four-term multilinear polynomial `∑_{a,b} X_{[·]₁=a} X_{[·]₂=b}`; it is nonzero, every
variable has degree at most one in it, and it factors as
`poly^F_{fst}(S) · poly^F_{snd}(S)` — all of that computed from Definitions 31–34 alone.
Three things there are worth calling out.  First, `poly^F_{fst}(S)` has *two* summands
where `S` has four elements, because `monos` is an image and coincident monomials
collapse; that collapse is exactly the subtlety Proposition 26 has to rule out at
`C = B`, and `mono_coordFS_basis_injective` is the instance of the ruling-out.  Second,
`Q_coordFS_univ_eq` and `poly_coordFS_basis_univ_eq` are a **cross-check pair** for
Proposition 26 on this witness: each computes its own side to the same explicit
polynomial, and neither mentions `Q_eq_poly`, so `prop26_coordFS_crosscheck` re-derives the
proposition here rather than echoing it (`prop26_coordFS_applied` is the separate, honest
*application* of the endpoint).  The same pairing runs for Proposition 30
(`Q_coordFS_univ_eq_mul_poly` computed, `prop30_coordFS_univ_applied` applied).  Third,
`Irr^F` is computed at four subsets and the answers differ: at `S`, at the block `Efst` and
at `∅` the irreducible parts are the two singletons `{fstFactor}`, `{sndFactor}`, while on
the diagonal `Ediag` the first coordinate determines the second,
`χ^F_{fst}(Ediag, Ediag) ≠ Ediag`, and the only irreducible part is the whole basis — the
§5 shadow of the §4 fact that restriction entangles.  Note the minimality clause of
Definition 35 is *vacuous* at a singleton: the only strict subset of `{b}` is `∅`, which
is not nonempty.

Four further groups make the §5 endpoints say something rather than merely typecheck.
Proposition 27 is applied at a genuinely nontrivial split (`C₀ = {fstFactor}`,
`C₁ = {sndFactor}` disjoint and nonempty, `E₀ = Efst ≠ S = E₁`), cross-checked by
computation, and its chimera's argument order is pinned by `prop27_reversed_false`, which
shows the reversed reading false.  Proposition 28 is applied at two divisors its
conclusion actually has to work for — `2 · poly^F_{fst}(S)`, which
`prop28_r_loadbearing` shows is no `poly^F_C(S)` at all, so the real coefficient `r`
cannot be dropped; and a nonzero constant, where `prop28_const_forces_empty` shows the
returned `C` must be `∅`.  Propositions 29 and 31 are applied and paired with negatives:
`irr_isPartition` is instantiated, and `not_irreducible_Q_coordFS_univ` shows
`Irreducible` is not vacuously total on this ring.  Finally the `E.Nonempty` hypotheses of
Propositions 28, 30 and 31 are each shown load-bearing at `E = ∅` (Proposition 30's on
`unitFS`, where the empty product is `1` while `Q^F_∅ = 0`), while
`irr_partition_holds_at_empty` backs Proposition 29's disclosure that *its* `hE` is not
consumed; and `poly_top_univ_junk` records what the total function `poly` does at a `C`
outside `B`, so nobody reads a §5 statement as covering that value.

The §5.3–§5.5 half turns all of that into probability.  It builds three inhabitants of
Definition 36 on `Bool × Bool` — `uniform`, `P(E) = |E| / 4`; `biased`, the product of two
`1/3`-biased coins; and `diagDist`, `P(E) = |E ∩ Ediag| / 2` — and uses them to separate
Definition 37 from Definition 36 and from any one distribution: `uniform` and `biased` are
two *different* distributions on `coordFS`, while `diagDist` is a distribution on the *set*
only, since it makes the two coordinates perfectly correlated.  Lemma 3's clauses 2 and 3
and Theorem 3 are then each cross-checked and separately applied, and each is computed at
both of the conditioning partitions §4.3 already separates: at `Ind_S` the coordinate
factors are orthogonal, clause 3 holds, clause 2's cofactor is `Q^F_{(t,t)}`, and `uniform`
makes the factors independent (`1/2 · 1/2 = 1/4 · 1`); at the `xorPart` block `Ediag` the
pair is entangled, clause 3 fails by one separating evaluation (`310` against `100`),
clause 2 fails at a zero of the divisor, and `uniform` breaks independence (`1/16` against
`1/8`).  That last computation is the concrete form of the existential Theorem 3's hard
direction promises, and `thm3_coordFS_xorPart_witness` and `thm3_coordFS_xorPart_applied`
are the cross-check/application pair for it.  Proposition 32 is not conditioned on a
partition, so it is varied along its own axes instead — two subsets (`Efst` and the
three-element `E3`) and two distributions.

Three further things §5.4–§5.5 needs and the pair above does not supply.  The two
directions the fundamental theorem consumes are run **forward**, with their hypotheses
discharged by computation rather than under a `by_contra`
(`clause3_fst_snd_top` feeding `orthogonalGiven_from_clause3` and
`orthogonalGiven_from_independence`); the degenerate carriers are recorded, since Theorem
3's right-hand side is vacuous exactly over an empty `S` (`isEmpty_probDist_empty`,
`orthogonalGiven_emptyFS`, and at the other extreme `subsingleton_probDist_unit` with
`unitDist_isDistribution` on the zero-dimensional `unitFS`); and
`not_orthogonalGiven_bot_bot_top_boolFS` shows Theorem 3's right-hand side is not
universally true, on the one-dimensional `boolFS`, where `boolFS_isDistribution` makes
every `ProbDist Bool` a distribution on the factored set.

The §6 half changes what is being quantified over: Definitions 42–45 range over *models*
of a sample space, not over factored sets, so none of the §2–§5 witnesses touches them.
Definition 38 is inhabited four ways — the identity models `coordModel` and `boolModel`,
the non-injective `fstModel` (`coordFS` observed through `Prod.fst`, so `S` has four points
where `Ω` has two: the latent structure Definition 38 exists to allow), and the one-point
`pointModel`.  Definition 39 is then computed on the two that are not the identity:
`pullback_fstModel_bot` shows `f⁻¹(Dis_Ω)` is the *first coordinate factor* rather than
`Dis_S` (with `history_pullback_fstModel_bot` giving its §3 history), and
`pullback_pointModel` shows the pullback can collapse every partition of `Ω` to `Ind_S`.

Four databases then separate Definitions 43 and 44 from each other and from Definition 45,
and the separation runs against the two readings a client is most likely to arrive with.
`Consistent` is *cheap on `O` alone*: `totalDB`, which asserts every triple orthogonal, is
consistent — the one-point model satisfies all of `O` at once, because `unitFS` has no
factors — so a database is never ruled out by what it puts in `O`.  It is `N` that
constrains, and `nonconstDB_forces_nonconstant` is the mechanism in its simplest form: a
single `N`-entry `(Dis_Ω, Dis_Ω, Ind_Ω)` forces every model's map to be non-constant.  The
other reading to rule out is that `Consistent` and `Complete` might travel together:
`emptyDB` is consistent and not complete, `totalDB` is both, and `contradictoryDB` — which
asserts one triple both ways — is neither model-satisfiable nor, being inconsistent,
informative.  `models_coordDB` is the Definition-42 computation proper, discharging both
clauses on the identity model of `coordFS` from §4.3's own computations.

Definition 45 gets the same two-sided treatment, and the trap there is worth stating
plainly: `X <_D Y` quantifies over models of `D`, so on an **inconsistent** database it is
vacuously *total* (`before_of_not_consistent`, instantiated at `contradictoryDB`), while on
a consistent one it is irreflexive (`not_before_self_of_consistent`, instantiated at a
database whose consistency is computed here rather than cited from §6.2).  The informative
positive instances — an actual inferred `X <_D Y` — are Propositions 34 and 36, which live
in `InferenceExamples.lean`; nothing here stands in for them.

One negative record deserves its name here: Proposition 28's conclusion, asserted at a
`poly^F_C(E)`, is a triviality — provable for every `C ⊆ B` and every `E` with none of the
proposition's hypotheses, as the `example` beside
`poly_singleton_fst_dvd_Q_coordFS_univ` shows.  A witness of that shape certifies nothing,
which is why the informative Proposition 28 instances are the two above.

No declaration here is a paper node, so all of them are `lemma`s: the `theorem` keyword is
reserved for the paper's numbered nodes.  Every *witness* lemma — the ones that carry a
non-vacuity claim, kind `N±` — is inventoried in `AxiomAudit.lean` alongside the nodes it
de-vacuates; the proof helpers that only exist to shorten those proofs
(`fstFactor_ne_sndFactor`, `coordFS_chimera_eq`, `coordFS_basis_eq`, `fstFactor_mem`,
`sndFactor_mem`, the `singleton_*_subset` and `commonRefinement_singleton_*` lemmas, and
in §4 the `mem_*`, `dom_*`, `*_apply` unfoldings together with `Ediag_eq`,
`generatesSub_snd_botInfIndEfalse`, `botInfIndEfalse_ne_indiscrete`,
`generatesSub_fstOnEdiag_forces`, `generatesSub_sndOnEdiag_forces` and
`inf_ofSetoid_coord`, and in §5 the `part_*` unfoldings and distinctness lemmas for the
variables, the separating evaluation `coordSep` with its four `coordSep_*` values,
`eval_coordSep_mono_coordFS`, `eval_coordSep_poly_fst`, `eval_coordSep_poly_snd`,
`eval_coordSep_poly_basis`, `mono_coordFS_basis`, `mono_singleton_fst`,
`mono_singleton_snd`, `monos_singleton_fst_univ`, `monos_singleton_snd_univ`,
`degreeOf_X_mul_X_le_one`, `subset_coordFS_basis_cases`,
`singleton_mem_irr_univ`, `Ediag_nonempty`, `Efst_nonempty`, `Efst_eq`,
`univ_nonempty_coord`, `chimeraImage_basis_Ediag`, `chimeraImage_Efst`,
`chimeraImage_fst_Efst_univ`, `chimeraImage_empty`, `part_top_eq_univ`,
`singleton_fst_union_snd_eq_basis`, `disjoint_singleton_fst_snd`,
`two_mul_poly_fst_dvd_Q_coordFS_univ` and `singleton_fst_ne_singleton_snd`, and in
§5.3–§5.5 the block descriptions `vfst_eq`, `vsnd_eq`, `E3_coe`, the intersection
computations `vfst_inter_vsnd`,
`Efst_inter_vsnd_true`, `Efst_inter_Ediag`, `vsnd_true_inter_Ediag`,
`Efst_inter_vsnd_true_inter_Ediag` with `singleton_tt_subset_Ediag`, the three
`Setoid.classes` memberships `Efst_mem_fstFactor_classes`,
`vsnd_true_mem_sndFactor_classes`, `univ_mem_top_classes`, the second separating
evaluation `coordZero` with its four `coordZero_*` values, the point weights `w` and
`w_nonneg`, and the numeric unfoldings
`uniform_apply`, `uniform_singleton`, `uniform_vfst`, `uniform_vsnd`, `uniform_Efst`,
`uniform_Ediag`, `diagDist_apply`, `biased_apply`, `biased_singleton`, `biased_vfst`,
`biased_vsnd`, `biased_Efst`, `eval_biased_Q_Efst`, `biased_E3`, `eval_biased_Q_E3`, and in
§6 the identity-pullback unfoldings `pullback_coordModel` and `pullback_boolModel` together
with `historySub_unitFS` and `orthogonalGiven_unitFS`) are
not, since they claim nothing about the paper.  The witnesses cite the paper in prose
rather than carrying the reserved node annotation: the paper's own Examples 1 and 2 are the
two §6.2 orthogonality databases, formalized in `InferenceExamples.lean`, and none of the
databases built here is one of them.
-/

universe u

namespace FiniteFactoredSets
namespace Examples

open scoped Classical

/-! ### `|S| = 2` (prime): the discrete factorization of `Bool`, `B = {Dis_S}`. -/

lemma bool_isFactorization :
    IsFactorization ({(⊥ : Setoid Bool)} : Set (Setoid Bool)) where
  nontrivial := by
    rintro b hb ⟨-, h⟩
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    exact Bool.noConfusion (h true false)
  bijective := by
    refine ⟨fun s t h => Quotient.exact (congrFun h ⟨⊥, rfl⟩), fun y => ?_⟩
    refine ⟨Quotient.out (y ⟨⊥, rfl⟩), funext fun b => ?_⟩
    obtain ⟨b, hb⟩ := b
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    exact Quotient.out_eq _

/-- A factored set of size 2 and dimension 1. -/
def boolFS : FactoredSet Bool := ⟨_, bool_isFactorization⟩

/-! ### Dimension 2: the coordinate factorization of `Bool × Bool`. -/

/-- The partition of `Bool × Bool` by first coordinate. -/
def fstFactor : Setoid (Bool × Bool) := Setoid.comap Prod.fst ⊥
/-- The partition of `Bool × Bool` by second coordinate. -/
def sndFactor : Setoid (Bool × Bool) := Setoid.comap Prod.snd ⊥

lemma fstFactor_ne_sndFactor : fstFactor ≠ sndFactor := by
  intro h
  have hr : fstFactor (true, false) (true, true) := rfl
  rw [h] at hr
  exact Bool.noConfusion hr

/-- The two-element basis `{fstFactor, sndFactor}`. -/
def coordBasis : Set (Setoid (Bool × Bool)) := {fstFactor, sndFactor}

lemma coord_isFactorization : IsFactorization coordBasis where
  nontrivial := by
    rintro b (rfl | rfl) ⟨-, h⟩
    · exact Bool.noConfusion (h (true, true) (false, true))
    · exact Bool.noConfusion (h (true, true) (true, false))
  bijective := by
    refine ⟨fun s t h => Prod.ext (Quotient.exact (congrFun h ⟨fstFactor, Or.inl rfl⟩))
      (Quotient.exact (congrFun h ⟨sndFactor, Or.inr rfl⟩)), fun y => ?_⟩
    refine ⟨((Quotient.out (y ⟨fstFactor, Or.inl rfl⟩)).1,
            (Quotient.out (y ⟨sndFactor, Or.inr rfl⟩)).2), funext fun b => ?_⟩
    obtain ⟨b, hb⟩ := b
    rcases hb with rfl | rfl
    · refine Eq.trans (Quotient.sound (?_ : fstFactor _ _)) (Quotient.out_eq _); rfl
    · refine Eq.trans (Quotient.sound (?_ : sndFactor _ _)) (Quotient.out_eq _); rfl

/-- A factored set of size 4 and dimension 2 — the smallest one whose chimera splices. -/
def coordFS : FactoredSet (Bool × Bool) := ⟨coordBasis, coord_isFactorization⟩

/-- The basis is not a subsingleton: `chimera` really has two independent factors. -/
lemma not_subsingleton_coordFS_basis : ¬ Subsingleton coordFS.B := fun h =>
  fstFactor_ne_sndFactor
    (congrArg Subtype.val (h.allEq ⟨fstFactor, Or.inl rfl⟩ ⟨sndFactor, Or.inr rfl⟩))

/-- The chimera of `coordFS` computes coordinatewise. -/
lemma coordFS_chimera_eq (C : Set (Setoid (Bool × Bool))) (s t : Bool × Bool) :
    coordFS.chimera C s t = (if fstFactor ∈ C then s.1 else t.1,
                             if sndFactor ∈ C then s.2 else t.2) := by
  refine Prod.ext ?_ ?_
  · by_cases h : fstFactor ∈ C
    · rw [if_pos h]; exact coordFS.chimera_rel_of_mem s t (Or.inl rfl) h
    · rw [if_neg h]; exact coordFS.chimera_rel_of_notMem s t (Or.inl rfl) h
  · by_cases h : sndFactor ∈ C
    · rw [if_pos h]; exact coordFS.chimera_rel_of_mem s t (Or.inr rfl) h
    · rw [if_neg h]; exact coordFS.chimera_rel_of_notMem s t (Or.inr rfl) h

/-- The four corners of `χ^F_C((⊤,⊤), (⊥,⊥))` are pairwise distinct. -/
lemma coordFS_chimera_corners :
    coordFS.chimera ∅ (true, true) (false, false) = (false, false) ∧
    coordFS.chimera {fstFactor} (true, true) (false, false) = (true, false) ∧
    coordFS.chimera {sndFactor} (true, true) (false, false) = (false, true) ∧
    coordFS.chimera coordFS.B (true, true) (false, false) = (true, true) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [coordFS_chimera_eq] <;>
    simp [coordFS, coordBasis, fstFactor_ne_sndFactor, Ne.symm fstFactor_ne_sndFactor]

/-! ### `|S| = 0`: Proposition 5's `B = {Dis_S} = {{}}`. -/

lemma empty_isFactorization :
    IsFactorization ({(⊥ : Setoid Empty)} : Set (Setoid Empty)) where
  nontrivial := by rintro b - ⟨⟨e⟩, -⟩; exact e.elim
  bijective := ⟨fun s => s.elim, fun y => (Quotient.out (y ⟨⊥, rfl⟩)).elim⟩

def emptyFS : FactoredSet Empty := ⟨_, empty_isFactorization⟩

/-- The empty basis is *not* a factorization of the empty set (paper, Proposition 5). -/
lemma not_isFactorization_empty_basis : ¬ IsFactorization (∅ : Set (Setoid Empty)) := by
  rintro ⟨-, -, hsurj⟩
  obtain ⟨s, -⟩ := hsurj fun b => b.2.elim
  exact s.elim

/-! ### `|S| = 1`: Proposition 5's `B = {}`, and it is the only one. -/

lemma unit_isFactorization : IsFactorization (∅ : Set (Setoid Unit)) where
  nontrivial := by rintro b ⟨⟩
  bijective := ⟨fun s t _ => Subsingleton.elim s t, fun y => ⟨(), funext fun b => b.2.elim⟩⟩

def unitFS : FactoredSet Unit := ⟨_, unit_isFactorization⟩

lemma unitFS_basis_unique (F : FactoredSet Unit) : F.B = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hb
  refine F.nontrivial_of_mem hb ⟨⟨()⟩, fun s t => ?_⟩
  have hst : s = t := Subsingleton.elim s t
  subst hst
  exact b.refl' s

/-! ### Definition 10's two fields are independent.

Neither field of `IsFactorization` implies the other, so neither is decoration.  The two
lemmas below exhibit a set of partitions satisfying `nontrivial` and failing `bijective`,
and one satisfying `bijective` and failing `nontrivial`. -/

/-- `nontrivial` does not imply `bijective`: `{fstFactor}` is a set of nontrivial
partitions of `Bool × Bool`, but nothing in it sees the second coordinate, so the
coordinate map is not injective. -/
lemma not_isFactorization_singleton_fstFactor :
    (∀ b ∈ ({fstFactor} : Set (Setoid (Bool × Bool))), ¬ IsTrivialPartition b) ∧
      ¬ IsFactorization ({fstFactor} : Set (Setoid (Bool × Bool))) := by
  refine ⟨?_, ?_⟩
  · rintro b hb ⟨-, h⟩
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    exact Bool.noConfusion (h (true, true) (false, true))
  · rintro ⟨-, hinj, -⟩
    refine Bool.noConfusion (congrArg Prod.snd (hinj (funext fun b => ?_) :
      ((true, true) : Bool × Bool) = (true, false)))
    obtain ⟨b, hb⟩ := b
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    exact Quotient.sound (rfl : fstFactor (true, true) (true, false))

/-- `bijective` does not imply `nontrivial`: over `Unit` the basis `{Ind_S}` has a
bijective coordinate map, yet `Ind_Unit` is the one-block partition and so is barred as a
factor.  Dropping the `nontrivial` field would therefore give `Unit` two factorizations,
`∅` and `{Ind_S}`, falsifying Proposition 5's uniqueness. -/
lemma not_isFactorization_unit_singleton_top :
    Function.Bijective (fun (s : Unit) (b : ({(⊤ : Setoid Unit)} : Set (Setoid Unit))) =>
        Quotient.mk (b : Setoid Unit) s) ∧
      ¬ IsFactorization ({(⊤ : Setoid Unit)} : Set (Setoid Unit)) := by
  refine ⟨⟨fun s t _ => Subsingleton.elim s t, fun y => ⟨(), funext fun b => ?_⟩⟩, ?_⟩
  · obtain ⟨b, hb⟩ := b
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    refine Eq.trans (Quotient.sound (?_ : (⊤ : Setoid Unit) _ _)) (Quotient.out_eq _)
    trivial
  · rintro ⟨hnt, -⟩
    exact hnt ⊤ rfl ⟨⟨()⟩, fun _ _ => trivial⟩

/-! ## §2.5 and §3 over the witnesses

Everything below is stated for `coordFS` unless it says otherwise.  `Finite F.B` — the
hypothesis every §3.2–§3.4 theorem carries — is discharged by instance search on each
witness, so no declaration here has to supply it by hand. -/

example : Finite coordFS.B := inferInstance
example : Finite boolFS.B := inferInstance
example : Finite emptyFS.B := inferInstance
example : Finite unitFS.B := inferInstance

lemma coordFS_basis_eq :
    coordFS.B = ({fstFactor, sndFactor} : Set (Setoid (Bool × Bool))) := rfl

lemma fstFactor_mem : fstFactor ∈ coordFS.B := Or.inl rfl
lemma sndFactor_mem : sndFactor ∈ coordFS.B := Or.inr rfl

lemma singleton_fstFactor_subset :
    ({fstFactor} : Set (Setoid (Bool × Bool))) ⊆ coordFS.B :=
  Set.singleton_subset_iff.2 fstFactor_mem

lemma singleton_sndFactor_subset :
    ({sndFactor} : Set (Setoid (Bool × Bool))) ⊆ coordFS.B :=
  Set.singleton_subset_iff.2 sndFactor_mem

/-! ### §2.5: size, dimension, and Propositions 7–9 on a witness.

`size` and `dim` unfold for a client through the public `@[simp]` lemmas `size_eq_mk` and
`dim_eq_mk`, which is how the two computations below start. -/

lemma size_coordFS : coordFS.size = ((4 : ℕ) : Cardinal) := by
  rw [coordFS.size_eq_mk, Cardinal.mk_prod, Cardinal.mk_bool, Cardinal.lift_two]
  norm_num

lemma dim_coordFS : coordFS.dim = ((2 : ℕ) : Cardinal) := by
  rw [coordFS.dim_eq_mk, coordFS_basis_eq, Cardinal.mk_insert (by
    simp only [Set.mem_singleton_iff]; exact fstFactor_ne_sndFactor), Cardinal.mk_singleton]
  norm_num

/-- Proposition 7 applies to `coordFS`: `|S| = ∏_b |b|`, and both sides are `4`. -/
lemma size_eq_prod_coordFS :
    (Cardinal.prod fun b : coordFS.B => Cardinal.mk (Quotient (b : Setoid (Bool × Bool))))
      = ((4 : ℕ) : Cardinal) := coordFS.size_eq_prod ▸ size_coordFS

/-- Proposition 9 clause 4 applies to `coordFS`: `4 = 2 · 2` is a product of two primes,
so `1 ≤ dim ≤ 2`. -/
lemma dim_spec_coordFS : 1 ≤ coordFS.dim ∧ coordFS.dim ≤ 2 := by
  have hl : ∀ p ∈ [2, 2], Nat.Prime p := by decide
  have h := coordFS.dim_spec.2.2.2 [2, 2] hl (by decide) (by rw [size_coordFS]; rfl)
  simpa using h

/-- Proposition 8 applies to `boolFS`: `|Bool| = 2` is prime, so its factorization is the
trivial one. -/
lemma boolFS_trivial : IsTrivialFactorization boolFS.B :=
  isTrivialFactorization_of_isFactorization
    (Or.inr (Or.inr ⟨2, Nat.prime_two, by simp⟩)) boolFS.isFactorization

/-! ### §3.1–§3.2: generation and history on `coordFS`. -/

/-- Proposition 10 clause 7 read as a client would: `{fstFactor}` generates `fstFactor`.
Binding clause 7 with an explicitly typed `have` first is necessary — it unfolds to a
strict-implicit `∀ ⦃x y⦄`, and `List.TFAE.out`'s autoparams then fail in term mode. -/
lemma generates_singleton_fstFactor : coordFS.Generates {fstFactor} fstFactor := by
  have h7 : commonRefinement ({fstFactor} : Set (Setoid (Bool × Bool))) ≤ fstFactor :=
    fun {_ _} h => commonRefinement_iff.1 h fstFactor rfl
  exact ((coordFS.generates_tfae singleton_fstFactor_subset fstFactor).out 6 0).1 h7

/-- Proposition 13 clause 4 on a witness: `h^F(b) = {b}` for a factor `b`. -/
lemma history_fstFactor : coordFS.history fstFactor = {fstFactor} :=
  (coordFS.history_spec fstFactor fstFactor).2.2.2 ⟨(true, true)⟩ fstFactor fstFactor_mem

lemma history_sndFactor : coordFS.history sndFactor = {sndFactor} :=
  (coordFS.history_spec sndFactor sndFactor).2.2.2 ⟨(true, true)⟩ sndFactor sndFactor_mem

/-- The same history re-derived *without* Proposition 13 clause 4, so the witness does not
merely echo the endpoint it is testing: `le_iff_history_subset` gives the inclusion in
`{fstFactor}`, and clause 3 rules out `∅`. -/
example : coordFS.history fstFactor = {fstFactor} := by
  have hsub : coordFS.history fstFactor ⊆ {fstFactor} :=
    (coordFS.le_iff_history_subset singleton_fstFactor_subset fstFactor).1
      (fun {_ _} h => commonRefinement_iff.1 h fstFactor rfl)
  have hne : coordFS.history fstFactor ≠ ∅ := by
    intro h
    have htop : fstFactor = (⊤ : Setoid (Bool × Bool)) :=
      (coordFS.history_spec fstFactor fstFactor).2.2.1.1 h
    have hr : fstFactor (true, true) (false, true) := by rw [htop]; trivial
    exact Bool.noConfusion hr
  rcases Set.subset_singleton_iff_eq.1 hsub with h | h
  · exact absurd h hne
  · exact h

/-- Proposition 13 clause 3 on a witness: `Ind_S` has empty history. -/
lemma history_top : coordFS.history (⊤ : Setoid (Bool × Bool)) = ∅ :=
  (coordFS.history_spec (⊤ : Setoid (Bool × Bool)) ⊤).2.2.1.2 rfl

lemma commonRefinement_singleton_fstFactor :
    commonRefinement ({fstFactor} : Set (Setoid (Bool × Bool))) (true, true) (true, false) :=
  commonRefinement_iff.2 fun c hc => by
    simp only [Set.mem_singleton_iff] at hc; subst hc; rfl

lemma commonRefinement_singleton_sndFactor :
    commonRefinement ({sndFactor} : Set (Setoid (Bool × Bool))) (true, true) (false, true) :=
  commonRefinement_iff.2 fun c hc => by
    simp only [Set.mem_singleton_iff] at hc; subst hc; rfl

/-- Any partition separating both coordinate pairs needs *both* factors: its history is
all of `B`.  This is Proposition 10 clause 7 composed with Proposition 12, used
contrapositively. -/
lemma history_eq_basis_of {X : Setoid (Bool × Bool)}
    (h₁ : ¬ X (true, true) (true, false)) (h₂ : ¬ X (true, true) (false, true)) :
    coordFS.history X = coordFS.B := by
  have hsub : coordFS.history X ⊆ coordFS.B := coordFS.history_subset X
  have hnf : ¬ coordFS.history X ⊆ {fstFactor} := fun hle =>
    h₁ ((coordFS.le_iff_history_subset singleton_fstFactor_subset X).2 hle
      commonRefinement_singleton_fstFactor)
  have hns : ¬ coordFS.history X ⊆ {sndFactor} := fun hle =>
    h₂ ((coordFS.le_iff_history_subset singleton_sndFactor_subset X).2 hle
      commonRefinement_singleton_sndFactor)
  obtain ⟨c, hc, hcne⟩ := Set.not_subset.1 hnf
  obtain ⟨d, hd, hdne⟩ := Set.not_subset.1 hns
  have hcs : c = sndFactor := by
    rcases hsub hc with rfl | rfl
    · exact absurd rfl hcne
    · rfl
  have hdf : d = fstFactor := by
    rcases hsub hd with rfl | rfl
    · rfl
    · exact absurd rfl hdne
  subst hcs; subst hdf
  refine Set.Subset.antisymm hsub ?_
  rintro b (rfl | rfl)
  · exact hd
  · exact hc

/-- `Dis_S` needs every factor: `h^F(⊥) = B`. -/
lemma history_bot : coordFS.history (⊥ : Setoid (Bool × Bool)) = coordFS.B :=
  history_eq_basis_of (fun h => Bool.noConfusion (congrArg Prod.snd h))
    (fun h => Bool.noConfusion (congrArg Prod.fst h))

/-! ### §3.3: orthogonality and entanglement on `coordFS`. -/

/-- `fstFactor ⊥^F sndFactor`, proved through Proposition 14 — no history in sight. -/
lemma orthogonal_fstFactor_sndFactor : coordFS.Orthogonal fstFactor sndFactor :=
  (coordFS.orthogonal_iff_exists fstFactor sndFactor).2
    ⟨{fstFactor}, singleton_fstFactor_subset,
      fun {_ _} h => commonRefinement_iff.1 h fstFactor rfl,
      fun {_ _} h => commonRefinement_iff.1 h sndFactor
        ⟨sndFactor_mem, fun hc => fstFactor_ne_sndFactor (Set.mem_singleton_iff.1 hc).symm⟩⟩

/-- Orthogonality is not reflexive: by Proposition 15 clause 4 only `Ind_S` is orthogonal
to itself, and `fstFactor` is not `Ind_S`. -/
lemma not_orthogonal_fstFactor_self : ¬ coordFS.Orthogonal fstFactor fstFactor := by
  intro hO
  have htop : fstFactor = (⊤ : Setoid (Bool × Bool)) :=
    (coordFS.orthogonal_spec fstFactor fstFactor fstFactor).2.2.2.1 hO
  have hr : fstFactor (true, true) (false, true) := by rw [htop]; trivial
  exact Bool.noConfusion hr

/-- Orthogonality is not total either: `Dis_S` sees every factor, so it is entangled with
`fstFactor`. -/
lemma not_orthogonal_bot_fstFactor :
    ¬ coordFS.Orthogonal (⊥ : Setoid (Bool × Bool)) fstFactor := by
  intro hO
  exact (coordFS.orthogonal_iff_forall_notMem ⊥ fstFactor).1 hO fstFactor
    (by rw [history_bot]; exact fstFactor_mem) (by rw [history_fstFactor]; rfl)

/-! ### §3.4: time on `coordFS`. -/

/-- Proposition 18 clause 3 at `Dis_S ≤_S fstFactor`: every factor is before `Dis_S`. -/
lemma before_fstFactor_bot : coordFS.Before fstFactor ⊥ :=
  (coordFS.before_spec fstFactor ⊥ ⊥).2.2.1 bot_le

/-- And strictly so: `{fstFactor} ⊂ B`. -/
lemma strictlyBefore_fstFactor_bot : coordFS.StrictlyBefore fstFactor ⊥ := by
  rw [coordFS.strictlyBefore_def, history_fstFactor, history_bot]
  refine ⟨singleton_fstFactor_subset, fun hall => fstFactor_ne_sndFactor ?_⟩
  exact (Set.mem_singleton_iff.1 (hall sndFactor_mem)).symm

/-- `Before` is not total: the two coordinate factors are incomparable in time. -/
lemma not_before_fstFactor_sndFactor : ¬ coordFS.Before fstFactor sndFactor := by
  intro h
  have h' := (coordFS.before_def fstFactor sndFactor).1 h
  rw [history_fstFactor, history_sndFactor] at h'
  exact fstFactor_ne_sndFactor (Set.mem_singleton_iff.1 (h' rfl))

/-- Proposition 19 on a witness satisfying both `[Finite F.B]` and `[Nonempty S]`: its
hypothesis set is satisfiable. -/
lemma history_eq_setOf_before_coordFS :
    coordFS.history fstFactor = {b ∈ coordFS.B | coordFS.Before b fstFactor} :=
  coordFS.history_eq_setOf_before fstFactor

/-! ### The XOR partition: `Before` is a preorder, not a partial order. -/

/-- `p ∼ q` iff `p.1 XOR p.2 = q.1 XOR q.2`.  Two blocks, and neither coordinate factor
alone determines it. -/
def xorPart : Setoid (Bool × Bool) := Setoid.comap (fun p => p.1 != p.2) ⊥

lemma xorPart_tt_ff : xorPart (true, true) (false, false) := rfl

lemma not_xorPart_tt_tf : ¬ xorPart (true, true) (true, false) := fun h => Bool.noConfusion h

lemma not_xorPart_tt_ft : ¬ xorPart (true, true) (false, true) := fun h => Bool.noConfusion h

/-- The whole basis is the history of `xorPart`: neither coordinate alone computes it. -/
lemma history_xorPart : coordFS.history xorPart = coordFS.B :=
  history_eq_basis_of not_xorPart_tt_tf not_xorPart_tt_ft

lemma xorPart_ne_bot : xorPart ≠ (⊥ : Setoid (Bool × Bool)) := fun h =>
  Bool.noConfusion (congrArg Prod.snd (h ▸ xorPart_tt_ff))

/-- History is *not* injective, so `Before` is a preorder and not a partial order:
`xorPart` and `Dis_S` are distinct partitions with the same history, hence each before the
other.  Proposition 18 claims reflexivity and transitivity and stops there; this is why. -/
lemma history_not_injective :
    coordFS.history xorPart = coordFS.history ⊥ ∧ xorPart ≠ (⊥ : Setoid (Bool × Bool)) :=
  ⟨history_xorPart.trans history_bot.symm, xorPart_ne_bot⟩

lemma before_xorPart_bot_and_back :
    coordFS.Before xorPart ⊥ ∧ coordFS.Before ⊥ xorPart :=
  ⟨le_of_eq (history_xorPart.trans history_bot.symm),
   le_of_eq (history_bot.trans history_xorPart.symm)⟩

/-- Definition 18's second sentence on a witness: `xorPart` is *entangled* with each
coordinate factor, since computing it needs that coordinate. -/
lemma entangled_xorPart_fstFactor : coordFS.Entangled xorPart fstFactor := by
  rw [coordFS.entangled_iff]
  intro hO
  refine (coordFS.orthogonal_iff_forall_notMem xorPart fstFactor).1 hO fstFactor ?_ ?_
  · rw [history_xorPart]; exact fstFactor_mem
  · rw [history_fstFactor]; rfl

/-! ### `Fintype F.B` is *not* dischargeable by instance search on a witness.

`Finite coordFS.B` is (the four `inferInstance`s above), but `natCard_eq_prod` asks for
`Fintype F.B`, which no witness supplies.  The reason is *not* a missing `DecidableEq`:
`open scoped Classical` is in force in this file, so `DecidableEq (Setoid (Bool × Bool))`
synthesizes as `Classical.propDecidable`, and `Fintype ↥({fstFactor, sndFactor} : Set _)`
synthesizes as `Set.fintypeInsert`.  What fails is `Fintype ↥coordBasis` — and hence
`Fintype ↥coordFS.B` — because `coordBasis` and `coordFS` are ordinary non-reducible
`def`s, which instance search will not unfold to find the `insert`/`singleton` structure
underneath.  So a client must build the instance by hand, and it has to be in scope *at
statement elaboration time*, because the `∏` in the statement needs it. -/

section FintypeFriction

noncomputable local instance : Fintype coordFS.B := Fintype.ofFinite _

example : Nat.card (Bool × Bool)
    = ∏ b : coordFS.B, Nat.card (Quotient (b : Setoid (Bool × Bool))) :=
  coordFS.natCard_eq_prod

end FintypeFriction

/-! ### `emptyFS`: the `Nonempty S` hypotheses of §3 are load-bearing.

Proposition 13 clause 4 and Proposition 19 both carry `Nonempty S`.  Over `Empty` all
setoids coincide, so `⊥` is a factor whose history is `∅` rather than `{⊥}` — both
conclusions fail outright, and the hypothesis is not decoration. -/

lemma emptyFS_history_bot : emptyFS.history (⊥ : Setoid Empty) = ∅ :=
  (emptyFS.history_spec (⊥ : Setoid Empty) ⊥).2.2.1.2
    (Setoid.ext fun a _ => (IsEmpty.false a).elim)

/-- Proposition 13 clause 4 fails without `Nonempty S`: `⊥ ∈ emptyFS.B` but `h(⊥) ≠ {⊥}`. -/
lemma emptyFS_history_ne_singleton :
    emptyFS.history (⊥ : Setoid Empty) ≠ {(⊥ : Setoid Empty)} := by
  rw [emptyFS_history_bot]
  exact fun h => Set.singleton_ne_empty _ h.symm

/-- Proposition 19 fails without `Nonempty S`: its right-hand side contains `⊥`. -/
lemma emptyFS_history_ne_setOf_before :
    emptyFS.history (⊥ : Setoid Empty) ≠ {b ∈ emptyFS.B | emptyFS.Before b ⊥} := by
  rw [emptyFS_history_bot]
  intro h
  have hmem : (⊥ : Setoid Empty) ∈ {b ∈ emptyFS.B | emptyFS.Before b ⊥} :=
    ⟨rfl, subset_rfl.trans (le_of_eq (congrArg emptyFS.history
      (Setoid.ext fun a _ => (IsEmpty.false a).elim)))⟩
  rw [← h] at hmem
  exact hmem

/-! ### Client's-eye uses of the §3 endpoints on a witness. -/

example : IsLeast {C | C ⊆ coordFS.B ∧ coordFS.Generates C fstFactor}
    (coordFS.history fstFactor) := coordFS.history_isLeast fstFactor

example : coordFS.Generates {fstFactor} fstFactor ↔
    coordFS.history fstFactor ⊆ {fstFactor} :=
  coordFS.generates_iff_history_subset singleton_fstFactor_subset fstFactor

example : coordFS.Orthogonal fstFactor sndFactor ↔
    ∃ C ⊆ coordFS.B, commonRefinement C ≤ fstFactor ∧
      commonRefinement (coordFS.B \ C) ≤ sndFactor :=
  coordFS.orthogonal_iff_exists fstFactor sndFactor

example : coordFS.Before fstFactor ⊥ ↔
    ∀ C ⊆ coordFS.B, commonRefinement C ≤ (⊥ : Setoid (Bool × Bool)) →
      commonRefinement C ≤ fstFactor :=
  coordFS.before_iff_forall_sInf fstFactor ⊥

/-! ## §4 over `coordFS`: subpartitions, generation, history, conditional orthogonality

Everything below restricts the two coordinate factors of `coordFS` to one of two subsets
of `Bool × Bool`, and computes the §4 vocabulary over the result.  The subsets are chosen
so that one restriction *keeps* the factors independent and the other *entangles* them,
which is what makes the §4.3 endpoints say something.

Definitions 20–22 are exercised by exhibiting a subpartition's domain and its actual set
of blocks; Definition 23 and Propositions 20–21 by a generating set and a non-generating
one; Definition 24 and Propositions 22–23 by histories computed to `{sndFactor}`, `∅` and
`B`; Definitions 25–27 and Propositions 24–25 and Theorem 2 by conditional orthogonality
holding and failing on the same pair of factors. -/

open Subpartition

/-! ### The two subsets that are conditioned on -/

/-- A block of `fstFactor`: the points with first coordinate `true`. -/
def Efst : Set (Bool × Bool) := {p | p.1 = true}

/-- The diagonal `{(false, false), (true, true)}` — a block of `xorPart`. -/
def Ediag : Set (Bool × Bool) := {p | p.1 = p.2}

lemma Ediag_eq : Ediag = ({(false, false), (true, true)} : Set (Bool × Bool)) := by
  ext p
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;>
    simp [Ediag, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]

/-! ### §4.1: `sndFactor` restricted to a block of `fstFactor`

Definition 22's `X|E` on a concrete `X` and `E`.  Its domain is `E` on the nose, its two
blocks are computed, and `{sndFactor}` generates it while `{fstFactor}` does not — so
Definition 23 is neither empty nor total on the witness. -/

/-- `sndFactor|Efst`, the paper's `X|E` for `X = sndFactor` and `E` a block of
`fstFactor`. -/
def sndOnEfst : Subpartition (Bool × Bool) := (ofSetoid sndFactor).restrict Efst

lemma dom_sndOnEfst : sndOnEfst.dom = Efst := dom_restrict_ofSetoid _ _

/-- Definition 22's blocks, computed: `sndFactor|Efst` is the *discrete* partition of
`Efst`, with the two singleton blocks. -/
lemma classes_sndOnEfst :
    sndOnEfst.classes
      = {{((true, true) : Bool × Bool)}, {((true, false) : Bool × Bool)}} := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [dom_sndOnEfst] at hs
    obtain ⟨a, b⟩ := s
    have ha : a = true := hs
    subst ha
    cases b
    · refine Or.inr ?_
      ext u
      obtain ⟨c, d⟩ := u
      constructor
      · rintro ⟨hc, -, hd⟩
        simp only [Set.mem_singleton_iff, Prod.mk.injEq]
        exact ⟨hc, hd⟩
      · rintro h
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
        exact ⟨h.1, rfl, h.2⟩
    · refine Or.inl ?_
      ext u
      obtain ⟨c, d⟩ := u
      constructor
      · rintro ⟨hc, -, hd⟩
        simp only [Set.mem_singleton_iff, Prod.mk.injEq]
        exact ⟨hc, hd⟩
      · rintro h
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
        exact ⟨h.1, rfl, h.2⟩
  · rintro (rfl | rfl)
    · refine ⟨(true, true), by rw [dom_sndOnEfst]; rfl, ?_⟩
      ext u
      obtain ⟨c, d⟩ := u
      constructor
      · rintro h
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
        exact ⟨h.1, rfl, h.2⟩
      · rintro ⟨hc, -, hd⟩
        simp only [Set.mem_singleton_iff, Prod.mk.injEq]
        exact ⟨hc, hd⟩
    · refine ⟨(true, false), by rw [dom_sndOnEfst]; rfl, ?_⟩
      ext u
      obtain ⟨c, d⟩ := u
      constructor
      · rintro h
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
        exact ⟨h.1, rfl, h.2⟩
      · rintro ⟨hc, -, hd⟩
        simp only [Set.mem_singleton_iff, Prod.mk.injEq]
        exact ⟨hc, hd⟩

/-- Definition 23 on the witness: `{sndFactor} ⊢^F sndFactor|Efst`. -/
lemma generatesSub_sndOnEfst : coordFS.GeneratesSub {sndFactor} sndOnEfst := by
  rw [coordFS.generatesSub_iff_rel]
  intro s hs t ht
  rw [dom_sndOnEfst] at hs ht
  rw [coordFS_chimera_eq, if_neg (by simpa using fstFactor_ne_sndFactor),
    if_pos (Set.mem_singleton _)]
  exact ⟨ht, hs, rfl⟩

/-- And `{fstFactor}` does **not** generate it, so `GeneratesSub` is not total. -/
lemma not_generatesSub_fst_sndOnEfst : ¬ coordFS.GeneratesSub {fstFactor} sndOnEfst := by
  intro h
  rw [coordFS.generatesSub_iff_rel] at h
  have hs : ((true, true) : Bool × Bool) ∈ sndOnEfst.dom := by rw [dom_sndOnEfst]; rfl
  have ht : ((true, false) : Bool × Bool) ∈ sndOnEfst.dom := by rw [dom_sndOnEfst]; rfl
  have key := h _ hs _ ht
  rw [coordFS_chimera_eq, if_pos (Set.mem_singleton _),
    if_neg (by simpa using (Ne.symm fstFactor_ne_sndFactor))] at key
  exact Bool.noConfusion key.2.2

/-- Definition 24 computed: `h^F(sndFactor|Efst) = {sndFactor}`, obtained from
Proposition 22's leastness and Proposition 23 clause 4 rather than by unfolding the
intersection. -/
lemma historySub_sndOnEfst : coordFS.historySub sndOnEfst = {sndFactor} := by
  have hle : coordFS.historySub sndOnEfst ⊆ {sndFactor} :=
    (coordFS.historySub_isLeast_and_eq_history.1 sndOnEfst).2
      ⟨singleton_sndFactor_subset, generatesSub_sndOnEfst⟩
  rcases Set.subset_singleton_iff_eq.1 hle with h | h
  · exfalso
    have hind : sndOnEfst = indiscrete sndOnEfst.dom :=
      (coordFS.historySub_spec sndOnEfst sndOnEfst sndOnEfst rfl).2.2.2.1.1 h
    have hmem : sndOnEfst (true, true) (true, false) := by
      rw [hind, dom_sndOnEfst]
      exact ⟨rfl, rfl⟩
    exact Bool.noConfusion hmem.2.2
  · exact h

/-- Proposition 20 clause 7 read as a client would, on the witness. -/
lemma generatesSub_tfae_on_sndOnEfst :
    coordFS.GeneratesSub {sndFactor} sndOnEfst ↔
      ((ofSetoid (commonRefinement ({sndFactor} : Set (Setoid (Bool × Bool))))).restrict
            sndOnEfst.dom ≤ sndOnEfst ∧
        coordFS.chimeraImage {sndFactor} sndOnEfst.dom sndOnEfst.dom = sndOnEfst.dom) :=
  (coordFS.generatesSub_tfae singleton_sndFactor_subset sndOnEfst).out 0 6

/-- The §4.2 replacement for `generates_iff_history_subset`, on the witness: containing the
history is only half of the criterion. -/
lemma generatesSub_iff_on_sndOnEfst :
    coordFS.GeneratesSub {sndFactor} sndOnEfst ↔
      coordFS.historySub sndOnEfst ⊆ {sndFactor} ∧
        ∀ s ∈ sndOnEfst.dom, ∀ t ∈ sndOnEfst.dom,
          coordFS.chimera {sndFactor} s t ∈ sndOnEfst.dom :=
  coordFS.generatesSub_iff_historySub_subset singleton_sndFactor_subset sndOnEfst

/-! ### Generating a subpartition is not monotone in `C`

The paper says so in the remark after Proposition 21; this is the executable
counterexample.  `Ind_Ediag` is generated by `∅`, its history `∅` is contained in
`{fstFactor}`, and yet `{fstFactor}` does not generate it — because
`χ^F_{fstFactor}((false,false), (true,true)) = (false,true) ∉ Ediag`.  So the naive §4
analogue of `generates_iff_history_subset` is false, and Proposition 20 clause 7's second
conjunct is what repairs it. -/

/-- `Ind_E` on the diagonal. -/
def indDiag : Subpartition (Bool × Bool) := indiscrete Ediag

lemma dom_indDiag : indDiag.dom = Ediag := dom_indiscrete _

lemma historySub_indDiag : coordFS.historySub indDiag = ∅ :=
  (coordFS.historySub_spec indDiag indDiag indDiag rfl).2.2.2.1.2 (by rw [dom_indDiag]; rfl)

lemma generatesSub_empty_indDiag : coordFS.GeneratesSub ∅ indDiag :=
  (coordFS.generatesSub_spec ∅ ∅ indDiag indDiag indDiag rfl).2.2.2.1.2
    (by rw [dom_indDiag]; rfl)

lemma not_generatesSub_fst_indDiag : ¬ coordFS.GeneratesSub {fstFactor} indDiag := by
  intro h
  rw [coordFS.generatesSub_iff_rel] at h
  have hs : ((false, false) : Bool × Bool) ∈ indDiag.dom := by rw [dom_indDiag]; rfl
  have ht : ((true, true) : Bool × Bool) ∈ indDiag.dom := by rw [dom_indDiag]; rfl
  have key := h _ hs _ ht
  rw [coordFS_chimera_eq, if_pos (Set.mem_singleton _),
    if_neg (by simpa using (Ne.symm fstFactor_ne_sndFactor))] at key
  exact Bool.noConfusion (key.1 : (false : Bool) = true)

/-- **Generation of a subpartition is not superset-monotone.**  `∅` generates `Ind_Ediag`,
its history is `∅ ⊆ {fstFactor}`, and yet `{fstFactor}` does not generate it. -/
lemma generatesSub_not_superset_monotone :
    coordFS.GeneratesSub ∅ indDiag ∧
      coordFS.historySub indDiag ⊆ ({fstFactor} : Set (Setoid (Bool × Bool))) ∧
      ¬ coordFS.GeneratesSub {fstFactor} indDiag :=
  ⟨generatesSub_empty_indDiag, by rw [historySub_indDiag]; exact Set.empty_subset _,
    not_generatesSub_fst_indDiag⟩

/-- **Proposition 20 clause 7's second conjunct is load-bearing.**  On the diagonal,
`{fstFactor}` satisfies the order half (trivially, since `Ind_E` is the coarsest
subpartition of `E`) but fails the membership half `χ^F_C(E,E) = E`, and indeed does not
generate.  So clause 7 is not equivalent to its first conjunct alone. -/
lemma clause7_second_conjunct_loadbearing :
    (ofSetoid (commonRefinement ({fstFactor} : Set (Setoid (Bool × Bool))))).restrict
        indDiag.dom ≤ indDiag ∧
      coordFS.chimeraImage {fstFactor} indDiag.dom indDiag.dom ≠ indDiag.dom ∧
      ¬ coordFS.GeneratesSub {fstFactor} indDiag := by
  refine ⟨?_, ?_, not_generatesSub_fst_indDiag⟩
  · intro s t h
    have hs : s ∈ Ediag := by rw [← dom_indDiag]; exact h.1
    have ht : t ∈ Ediag := by rw [← dom_indDiag]; exact h.2.1
    exact ⟨hs, ht⟩
  · intro h
    have hmem : ((false, true) : Bool × Bool) ∈
        coordFS.chimeraImage {fstFactor} indDiag.dom indDiag.dom := by
      refine ⟨(false, false), by rw [dom_indDiag]; rfl, (true, true),
        by rw [dom_indDiag]; rfl, ?_⟩
      rw [coordFS_chimera_eq, if_pos (Set.mem_singleton _),
        if_neg (by simpa using (Ne.symm fstFactor_ne_sndFactor))]
    rw [h, dom_indDiag] at hmem
    exact Bool.noConfusion (hmem : (false : Bool) = true)

/-! ### Proposition 23 clause 2's `hE : X.dom = Y.dom` is load-bearing

With `X = Dis_S` (domain all of `S`) and `Y = Ind_E` for `E` the `fst = false` block,
`h^F(X ∨_E Y) = {sndFactor}` while `h^F(X) ∪ h^F(Y) = B ∋ fstFactor`.  The history on the
left is *nonempty*, so the discriminator is not the degenerate `∅`. -/

/-- The other block of `fstFactor`: the points with first coordinate `false`. -/
def Efalse : Set (Bool × Bool) := {p | p.1 = false}

/-- `Dis_S ∨_E Ind_Efalse` — a common refinement of two subpartitions with *different*
domains. -/
def botInfIndEfalse : Subpartition (Bool × Bool) :=
  ofSetoid (⊥ : Setoid (Bool × Bool)) ⊓ indiscrete Efalse

lemma dom_botInfIndEfalse : botInfIndEfalse.dom = Efalse := by
  show ((ofSetoid (⊥ : Setoid (Bool × Bool))).dom ∩ (indiscrete Efalse).dom) = Efalse
  simp

lemma generatesSub_snd_botInfIndEfalse :
    coordFS.GeneratesSub {sndFactor} botInfIndEfalse := by
  refine (coordFS.generatesSub_iff_rel _ _).2 fun s hs t ht => ?_
  rw [dom_botInfIndEfalse] at hs ht
  have hchi : coordFS.chimera {sndFactor} s t = s := by
    rw [coordFS_chimera_eq, if_neg (by simpa using fstFactor_ne_sndFactor),
      if_pos (Set.mem_singleton _)]
    have h1 : t.1 = s.1 := by rw [(ht : t.1 = false), (hs : s.1 = false)]
    rw [h1]
  rw [hchi]
  exact ⟨rfl, hs, hs⟩

lemma botInfIndEfalse_ne_indiscrete : botInfIndEfalse ≠ indiscrete botInfIndEfalse.dom := by
  intro h
  have h1 : botInfIndEfalse ((false, false) : Bool × Bool) ((false, true) : Bool × Bool) := by
    rw [h, dom_botInfIndEfalse]
    exact ⟨rfl, rfl⟩
  exact Bool.noConfusion (congrArg Prod.snd h1.1)

/-- A nondegenerate subpartition history: `{sndFactor}`, neither `∅` nor `B`. -/
lemma historySub_botInfIndEfalse : coordFS.historySub botInfIndEfalse = {sndFactor} := by
  have hle : coordFS.historySub botInfIndEfalse ⊆ {sndFactor} :=
    coordFS.historySub_subset_of_generatesSub singleton_sndFactor_subset
      generatesSub_snd_botInfIndEfalse
  rcases Set.subset_singleton_iff_eq.1 hle with h | h
  · exact absurd ((coordFS.historySub_spec botInfIndEfalse botInfIndEfalse botInfIndEfalse
      rfl).2.2.2.1.1 h) botInfIndEfalse_ne_indiscrete
  · exact h

/-- **Proposition 23 clause 2 fails without `hE`.**  `Dis_S` and `Ind_Efalse` have different
domains, and the union formula for the history of their common refinement is then false. -/
lemma historySub_spec_hE_loadbearing :
    coordFS.historySub botInfIndEfalse ≠
      coordFS.historySub (ofSetoid (⊥ : Setoid (Bool × Bool))) ∪
        coordFS.historySub (indiscrete Efalse) := by
  intro heq
  have hIndY : coordFS.historySub (indiscrete Efalse) = ∅ :=
    (coordFS.historySub_spec (indiscrete Efalse) (indiscrete Efalse) (indiscrete Efalse)
      rfl).2.2.2.1.2 (by rw [dom_indiscrete])
  have hbotX : coordFS.historySub (ofSetoid (⊥ : Setoid (Bool × Bool))) = coordFS.B :=
    (coordFS.historySub_isLeast_and_eq_history.2 ⊥).trans history_bot
  rw [hIndY, hbotX, Set.union_empty, historySub_botInfIndEfalse] at heq
  have hmem : fstFactor ∈ ({sndFactor} : Set (Setoid (Bool × Bool))) := by
    rw [heq]; exact fstFactor_mem
  exact fstFactor_ne_sndFactor (Set.mem_singleton_iff.1 hmem)

/-! ### `Subset` and the `dd:subpartition` correspondence on a witness

`Subset` — the paper's inclusion *as sets of blocks* — is exhibited both holding and
failing, and the `ofSetoidOn` / `toSetoid` bijection of `dd:subpartition` is run in both
directions on a concrete subset. -/

/-- `sndFactor|Efst` is the discrete partition of `Efst`, exhibited through `ofSetoidOn`:
the client-facing constructor and the restriction agree on the nose. -/
lemma ofSetoidOn_bot_Efst : ofSetoidOn Efst (⊥ : Setoid Efst) = sndOnEfst := by
  refine Subpartition.ext fun s t => ⟨?_, ?_⟩
  · rintro ⟨hs, ht, hst⟩
    have h : s = t := congrArg Subtype.val hst
    exact ⟨hs, ht, congrArg Prod.snd h⟩
  · rintro ⟨hs, ht, hsnd⟩
    refine ⟨hs, ht, ?_⟩
    have h : s = t := Prod.ext (hs.trans ht.symm) hsnd
    exact Subtype.ext h

/-- Round trip one, on a concrete subpartition: `ofSetoidOn (dom X) (toSetoid X) = X`. -/
lemma roundtrip_sndOnEfst : ofSetoidOn sndOnEfst.dom sndOnEfst.toSetoid = sndOnEfst :=
  ofSetoidOn_toSetoid sndOnEfst

/-- Round trip two, on a concrete `E` and a concrete partition of it: `toSetoid` recovers
the setoid it was built from, pointwise. -/
lemma roundtrip_bot_Efst (a b : (ofSetoidOn Efst (⊥ : Setoid Efst)).dom) :
    (ofSetoidOn Efst (⊥ : Setoid Efst)).toSetoid a b ↔
      (⊥ : Setoid Efst) ⟨a, by simpa using a.2⟩ ⟨b, by simpa using b.2⟩ :=
  toSetoid_ofSetoidOn Efst (⊥ : Setoid Efst) a b

/-- `Subset`, positive: the diagonal is a block of `xorPart`, so `Ind_Ediag ⊆ xorPart`. -/
lemma subset_indDiag_xorPart : indDiag.Subset (ofSetoid xorPart) := by
  intro s hs t
  rw [dom_indDiag] at hs
  have hs' : s.1 = s.2 := hs
  constructor
  · rintro ⟨ht, -⟩
    have ht' : t.1 = t.2 := ht
    show (t.1 != t.2) = (s.1 != s.2)
    rw [ht', hs']
    simp
  · intro h
    have h' : (t.1 != t.2) = (s.1 != s.2) := h
    rw [hs'] at h'
    simp only [bne_self_eq_false] at h'
    exact ⟨by simpa [Ediag] using h', hs⟩

/-- `Subset`, negative: the blocks of `sndFactor|Efst` are singletons, which are not blocks
of `sndFactor`.  So `Subset` is strictly stronger than `dom`-inclusion, and Proposition 21
clause 6 is not vacuous. -/
lemma not_subset_sndOnEfst_snd : ¬ sndOnEfst.Subset (ofSetoid sndFactor) := by
  intro h
  have hs : ((true, true) : Bool × Bool) ∈ sndOnEfst.dom := by rw [dom_sndOnEfst]; rfl
  have key := (h _ hs (false, true)).2 (rfl : sndFactor (false, true) (true, true))
  exact Bool.noConfusion (key.1 : (false : Bool) = true)

/-- Nested restriction on the witness: `(sndFactor|Efst)|{(true,true)}` collapses. -/
lemma restrict_restrict_sndOnEfst :
    sndOnEfst.restrict {((true, true) : Bool × Bool)}
      = (ofSetoid sndFactor).restrict {((true, true) : Bool × Bool)} :=
  restrict_restrict_of_subset _ (by
    rintro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rfl)

/-! ### §4.2: Lemmas 1 and 2 instantiated on `coordFS`

Both lemmas carry hypotheses (`X.dom = Y.dom`, disjoint histories, a point of the domain)
that a reader could suspect of being jointly unsatisfiable.  They are not: on `coordFS`
every one of them is discharged in a line, and Lemma 2's two sides are each computed to
`B` *without* invoking Lemma 2 — the left side from Proposition 22, the right side from
Lemma 1 — so the pair cross-checks Lemma 2 on the witness. -/

lemma historySub_ofSetoid_fstFactor :
    coordFS.historySub (ofSetoid fstFactor) = {fstFactor} := by
  rw [coordFS.historySub_isLeast_and_eq_history.2 fstFactor, history_fstFactor]

lemma historySub_ofSetoid_sndFactor :
    coordFS.historySub (ofSetoid sndFactor) = {sndFactor} := by
  rw [coordFS.historySub_isLeast_and_eq_history.2 sndFactor, history_sndFactor]

/-- Lemma 1's disjointness hypothesis, discharged on the witness. -/
lemma historySub_disjoint_coord :
    coordFS.historySub (ofSetoid fstFactor) ∩ coordFS.historySub (ofSetoid sndFactor)
      = ∅ := by
  rw [historySub_ofSetoid_fstFactor, historySub_ofSetoid_sndFactor]
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro b ⟨hb1, hb2⟩
  simp only [Set.mem_singleton_iff] at hb1 hb2
  exact fstFactor_ne_sndFactor (hb1.symm.trans hb2)

/-- **Lemma 1** on the witness: restricting `fstFactor` to any block of `sndFactor` leaves
its history equal to `{fstFactor}`. -/
lemma lemma1_coordFS (s : Bool × Bool) :
    coordFS.historySub ((ofSetoid fstFactor).restrict ((ofSetoid sndFactor).part s))
      = {fstFactor} := by
  rw [← coordFS.historySub_restrict_part_eq (X := ofSetoid fstFactor)
      (Y := ofSetoid sndFactor) (by simp) historySub_disjoint_coord (by simp),
    historySub_ofSetoid_fstFactor]

/-- Lemma 1 the other way round, so that neither coordinate is privileged. -/
lemma lemma1_coordFS' (s : Bool × Bool) :
    coordFS.historySub ((ofSetoid sndFactor).restrict ((ofSetoid fstFactor).part s))
      = {sndFactor} := by
  rw [← coordFS.historySub_restrict_part_eq (X := ofSetoid sndFactor)
      (Y := ofSetoid fstFactor) (by simp)
      (by rw [Set.inter_comm]; exact historySub_disjoint_coord) (by simp),
    historySub_ofSetoid_sndFactor]

lemma inf_ofSetoid_coord :
    ofSetoid fstFactor ⊓ ofSetoid sndFactor = ofSetoid (⊥ : Setoid (Bool × Bool)) :=
  Subpartition.ext fun _ _ =>
    ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

/-- Lemma 2's left side, computed independently of Lemma 2: `fst ∨_S snd = Dis_S`, whose
history is all of `B`. -/
lemma lemma2_lhs_coordFS :
    coordFS.historySub (ofSetoid fstFactor ⊓ ofSetoid sndFactor) = coordFS.B := by
  rw [inf_ofSetoid_coord, coordFS.historySub_isLeast_and_eq_history.2, history_bot]

/-- **Lemma 2**'s right side, computed *without* using Lemma 2, so that the pair
`lemma2_lhs_coordFS`/`lemma2_rhs_coordFS` genuinely cross-checks it on `coordFS`: every
union term is `{sndFactor}` by Lemma 1 (`lemma1_coordFS'`) and `h^F(fstFactor)` is
`{fstFactor}`, so the union is `{fstFactor, sndFactor} = B`. -/
lemma lemma2_rhs_coordFS :
    coordFS.historySub (ofSetoid fstFactor) ∪
      (⋃ s ∈ (ofSetoid fstFactor).dom,
        coordFS.historySub ((ofSetoid sndFactor).restrict ((ofSetoid fstFactor).part s)))
      = coordFS.B := by
  have h : ∀ s : Bool × Bool,
      coordFS.historySub ((ofSetoid sndFactor).restrict ((ofSetoid fstFactor).part s))
        = {sndFactor} := lemma1_coordFS'
  simp only [h, historySub_ofSetoid_fstFactor, dom_ofSetoid]
  ext b
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, exists_const]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

/-! ### §4.3: conditioning on the diagonal entangles the coordinate factors

`fstFactor ⊥^F sndFactor` unconditionally, but on the diagonal the first coordinate
*determines* the second, so each restriction needs both factors and the two histories
coincide with `B`.  This is what stops Definitions 26–27 from being implied by
Definition 18, and Proposition 24 from being the whole story. -/

/-- `fstFactor|Ediag`. -/
def fstOnEdiag : Subpartition (Bool × Bool) := (ofSetoid fstFactor).restrict Ediag

/-- `sndFactor|Ediag`. -/
def sndOnEdiag : Subpartition (Bool × Bool) := (ofSetoid sndFactor).restrict Ediag

lemma dom_fstOnEdiag : fstOnEdiag.dom = Ediag := dom_restrict_ofSetoid _ _

lemma dom_sndOnEdiag : sndOnEdiag.dom = Ediag := dom_restrict_ofSetoid _ _

/-- Every set generating `fstFactor|Ediag` contains **both** factors: splicing two diagonal
points along one coordinate alone leaves the diagonal. -/
lemma generatesSub_fstOnEdiag_forces {C : Set (Setoid (Bool × Bool))}
    (h : coordFS.GeneratesSub C fstOnEdiag) : fstFactor ∈ C ∧ sndFactor ∈ C := by
  rw [coordFS.generatesSub_iff_rel] at h
  have hs : ((false, false) : Bool × Bool) ∈ fstOnEdiag.dom := by rw [dom_fstOnEdiag]; rfl
  have ht : ((true, true) : Bool × Bool) ∈ fstOnEdiag.dom := by rw [dom_fstOnEdiag]; rfl
  have key := h _ hs _ ht
  rw [coordFS_chimera_eq] at key
  obtain ⟨hmem, -, hfst⟩ := key
  have h1 : (if fstFactor ∈ C then false else true) = false := hfst
  have hC1 : fstFactor ∈ C := by
    by_contra hc
    rw [if_neg hc] at h1
    exact Bool.noConfusion h1
  have h2 : (if fstFactor ∈ C then false else true)
      = (if sndFactor ∈ C then false else true) := hmem
  rw [if_pos hC1] at h2
  have hC2 : sndFactor ∈ C := by
    by_contra hc
    rw [if_neg hc] at h2
    exact Bool.noConfusion h2
  exact ⟨hC1, hC2⟩

lemma generatesSub_sndOnEdiag_forces {C : Set (Setoid (Bool × Bool))}
    (h : coordFS.GeneratesSub C sndOnEdiag) : fstFactor ∈ C ∧ sndFactor ∈ C := by
  rw [coordFS.generatesSub_iff_rel] at h
  have hs : ((false, false) : Bool × Bool) ∈ sndOnEdiag.dom := by rw [dom_sndOnEdiag]; rfl
  have ht : ((true, true) : Bool × Bool) ∈ sndOnEdiag.dom := by rw [dom_sndOnEdiag]; rfl
  have key := h _ hs _ ht
  rw [coordFS_chimera_eq] at key
  obtain ⟨hmem, -, hsnd⟩ := key
  have h1 : (if sndFactor ∈ C then false else true) = false := hsnd
  have hC2 : sndFactor ∈ C := by
    by_contra hc
    rw [if_neg hc] at h1
    exact Bool.noConfusion h1
  have h2 : (if fstFactor ∈ C then false else true)
      = (if sndFactor ∈ C then false else true) := hmem
  rw [if_pos hC2] at h2
  have hC1 : fstFactor ∈ C := by
    by_contra hc
    rw [if_neg hc] at h2
    exact Bool.noConfusion h2
  exact ⟨hC1, hC2⟩

lemma historySub_fstOnEdiag : coordFS.historySub fstOnEdiag = coordFS.B := by
  refine Set.Subset.antisymm (coordFS.historySub_subset _) ?_
  intro b hb
  refine Set.mem_sInter.2 ?_
  rintro C ⟨-, hC⟩
  rcases hb with rfl | rfl
  · exact (generatesSub_fstOnEdiag_forces hC).1
  · exact (generatesSub_fstOnEdiag_forces hC).2

lemma historySub_sndOnEdiag : coordFS.historySub sndOnEdiag = coordFS.B := by
  refine Set.Subset.antisymm (coordFS.historySub_subset _) ?_
  intro b hb
  refine Set.mem_sInter.2 ?_
  rintro C ⟨-, hC⟩
  rcases hb with rfl | rfl
  · exact (generatesSub_sndOnEdiag_forces hC).1
  · exact (generatesSub_sndOnEdiag_forces hC).2

/-- **Restriction can entangle.**  Definition 18 holds for the pair, Definition 26 fails on
the diagonal. -/
lemma not_orthogonalGivenSet_Ediag :
    coordFS.Orthogonal fstFactor sndFactor ∧
      ¬ coordFS.OrthogonalGivenSet fstFactor sndFactor Ediag := by
  refine ⟨orthogonal_fstFactor_sndFactor, ?_⟩
  intro h
  rw [coordFS.orthogonalGivenSet_def] at h
  have h' : coordFS.historySub fstOnEdiag ∩ coordFS.historySub sndOnEdiag = ∅ := h
  rw [historySub_fstOnEdiag, historySub_sndOnEdiag, Set.inter_self] at h'
  have hmem : fstFactor ∈ (∅ : Set (Setoid (Bool × Bool))) := h' ▸ fstFactor_mem
  exact hmem

/-- The diagonal is a block of `xorPart`, so Definition 27 can be tested at it. -/
lemma Ediag_mem_xorPart_classes : Ediag ∈ xorPart.classes := by
  refine ⟨(false, false), ?_⟩
  ext p
  constructor
  · intro h
    show (p.1 != p.2) = (false != false)
    have hp : p.1 = p.2 := h
    rw [hp]
    simp
  · intro h
    show p.1 = p.2
    have hp : (p.1 != p.2) = (false != false) := h
    simpa using hp

/-- Definition 27 fails at `Z = xorPart` even though Definition 18 holds for the pair. -/
lemma not_orthogonalGiven_fst_snd_xorPart :
    ¬ coordFS.OrthogonalGiven fstFactor sndFactor xorPart := fun h =>
  not_orthogonalGivenSet_Ediag.2 (h Ediag Ediag_mem_xorPart_classes)

/-- Proposition 24 on the witness. -/
lemma orthogonalGiven_fst_snd_top : coordFS.OrthogonalGiven fstFactor sndFactor ⊤ :=
  (coordFS.orthogonal_iff_orthogonalGiven_top fstFactor sndFactor).1
    orthogonal_fstFactor_sndFactor

/-- `OrthogonalGiven` is neither empty nor total on `coordFS`: the same pair of factors is
orthogonal given `Ind_S` and entangled given `xorPart`. -/
lemma orthogonalGiven_nondegenerate :
    coordFS.OrthogonalGiven fstFactor sndFactor ⊤ ∧
      ¬ coordFS.OrthogonalGiven fstFactor sndFactor xorPart :=
  ⟨orthogonalGiven_fst_snd_top, not_orthogonalGiven_fst_snd_xorPart⟩

/-- Proposition 25, negative side: `X ⊥^F X | Ind_S` would force `Ind_S ≤ X`. -/
lemma not_orthogonalGiven_fst_fst_top :
    ¬ coordFS.OrthogonalGiven fstFactor fstFactor ⊤ := by
  intro h
  have hle : (⊤ : Setoid (Bool × Bool)) ≤ fstFactor :=
    (coordFS.orthogonalGiven_self_iff fstFactor ⊤).1 h
  have hr : fstFactor (true, true) (false, true) := hle trivial
  exact Bool.noConfusion hr

/-- Proposition 25, positive side at `Y = X`. -/
lemma orthogonalGiven_fst_fst_fst :
    coordFS.OrthogonalGiven fstFactor fstFactor fstFactor :=
  (coordFS.orthogonalGiven_self_iff fstFactor fstFactor).2 le_rfl

/-- Theorem 2's decomposition on the witness. -/
lemma thm2_decomposition_coordFS :
    coordFS.OrthogonalGiven fstFactor sndFactor ⊤ ∧
      coordFS.OrthogonalGiven fstFactor ⊤ ⊤ := by
  have h : coordFS.OrthogonalGiven fstFactor (sndFactor ⊓ ⊤) ⊤ := by
    rw [inf_top_eq]; exact orthogonalGiven_fst_snd_top
  exact (coordFS.orthogonalGiven_semigraphoid fstFactor sndFactor ⊤ ⊤).2.1 h

/-- Theorem 2's weak union on the witness: `fst ⊥^F snd | snd`. -/
lemma thm2_weakUnion_coordFS :
    coordFS.OrthogonalGiven fstFactor sndFactor sndFactor := by
  have h : coordFS.OrthogonalGiven fstFactor (sndFactor ⊓ sndFactor) ⊤ := by
    rw [inf_idem]; exact orthogonalGiven_fst_snd_top
  have h2 := (coordFS.orthogonalGiven_semigraphoid fstFactor sndFactor ⊤ sndFactor).2.2.1 h
  rwa [top_inf_eq] at h2

/-! ### Degenerate corners of Definitions 26–27

Conditioning on the empty set, or on `Dis_S`, makes *every* pair orthogonal — including a
partition with itself.  Both match the paper (a block of a partition is never empty, so
Definition 27 never conditions on `∅`), but a client reading Definition 26 alone should
know, so both corners are recorded here rather than left to be rediscovered. -/

lemma orthogonalGivenSet_empty : coordFS.OrthogonalGivenSet fstFactor fstFactor ∅ := by
  refine (coordFS.orthogonalGivenSet_def fstFactor fstFactor ∅).2 ?_
  have h : coordFS.historySub ((ofSetoid fstFactor).restrict (∅ : Set (Bool × Bool)))
      = ∅ := by
    refine (coordFS.historySub_spec ((ofSetoid fstFactor).restrict ∅)
      ((ofSetoid fstFactor).restrict ∅) ((ofSetoid fstFactor).restrict ∅) rfl).2.2.2.1.2 ?_
    rw [dom_restrict_ofSetoid]
    exact Subpartition.ext fun s t => ⟨fun hst => ⟨hst.1, hst.2.1⟩, fun hst => hst.1.elim⟩
  rw [h, Set.empty_inter]

/-- Conditioning on `Dis_S` trivializes conditional orthogonality (Proposition 25 at
`Y = ⊥`), even though `fstFactor` is not orthogonal to itself. -/
lemma orthogonalGiven_bot :
    coordFS.OrthogonalGiven fstFactor fstFactor ⊥ ∧
      ¬ coordFS.Orthogonal fstFactor fstFactor :=
  ⟨(coordFS.orthogonalGiven_self_iff fstFactor ⊥).2 bot_le, not_orthogonal_fstFactor_self⟩

/-! ### Client's-eye uses of the §4 endpoints on a witness. -/

example : IsLeast {C | C ⊆ coordFS.B ∧ coordFS.GeneratesSub C sndOnEfst}
    (coordFS.historySub sndOnEfst) :=
  coordFS.historySub_isLeast_and_eq_history.1 sndOnEfst

example : coordFS.OrthogonalSub fstOnEdiag sndOnEdiag ↔
    coordFS.historySub fstOnEdiag ∩ coordFS.historySub sndOnEdiag = ∅ :=
  coordFS.orthogonalSub_def fstOnEdiag sndOnEdiag

/-! ## §5.1–§5.2 over `coordFS`

§5 adds a third layer of vocabulary — the polynomial ring `Poly^F`, the characteristic
polynomial `Q^F_E`, the monomials `mono^F_C(s)`, `monos^F_C(E)`, `poly^F_C(E)`, and the
irreducible parts `Irr^F(E)` — none of which the §2–§4 witnesses touch.  `coordFS` is
again the load-bearing example: over a one-dimensional factored set `Q^F_E` is a sum of
single variables, so `mono`'s product is a one-factor product and Propositions 26–31 all
degenerate.

`Finite S` is what §5 needs and §2–§4 never did (`dd:finiteness-minimal`), and it is
discharged here by instance search: `Bool × Bool` is a `Fintype`.

Everything in this section is computed from Definitions 28 and 31–35 alone unless its
docstring says it *applies* a proposition. -/

open MvPolynomial

/-- `[Finite S]` itself, not just `[Finite F.B]`, and by instance search alone. -/
example : Finite (Bool × Bool) := inferInstance

/-- The variable `[s]_fstFactor` of `Poly^{coordFS}` for any `s` with `s.1 = a` — the
block `{p | p.1 = a}` of `fstFactor`, which under `dd:partition` *is* a subset of `S` and
so is a variable of the ring verbatim. -/
def vfst (a : Bool) : Set (Bool × Bool) := {p | p.1 = a}

/-- The variable `[s]_sndFactor` for any `s` with `s.2 = b`. -/
def vsnd (b : Bool) : Set (Bool × Bool) := {p | p.2 = b}

lemma part_fstFactor (s : Bool × Bool) : part fstFactor s = vfst s.1 := rfl
lemma part_sndFactor (s : Bool × Bool) : part sndFactor s = vsnd s.2 := rfl

lemma vfst_ne_vsnd (a b : Bool) : vfst a ≠ vsnd b := by
  intro h
  have hm : ((a, !b) : Bool × Bool) ∈ vfst a := rfl
  rw [h] at hm
  exact (Bool.not_ne_self b) hm

lemma vfst_true_ne_false : vfst true ≠ vfst false := by
  intro h
  have hm : ((true, true) : Bool × Bool) ∈ vfst true := rfl
  rw [h] at hm
  exact Bool.noConfusion hm

lemma vsnd_true_ne_false : vsnd true ≠ vsnd false := by
  intro h
  have hm : ((true, true) : Bool × Bool) ∈ vsnd true := rfl
  rw [h] at hm
  exact Bool.noConfusion hm

/-! ### Definitions 31–34 computed -/

/-- Definition 32 at `C = B`: the `B`-monomial of a point is the product of its two
coordinate blocks. -/
lemma mono_coordFS_basis (s : Bool × Bool) :
    mono coordFS.B s = (X (vfst s.1) * X (vsnd s.2) : Poly (Bool × Bool)) := by
  simp only [mono, coordFS_basis_eq, finprod_mem_pair fstFactor_ne_sndFactor,
    part_fstFactor, part_sndFactor]

lemma mono_singleton_fst (s : Bool × Bool) :
    mono ({fstFactor} : Set (Setoid (Bool × Bool))) s = (X (vfst s.1) : Poly (Bool × Bool)) := by
  simp only [mono, finprod_mem_singleton, part_fstFactor]

lemma mono_singleton_snd (s : Bool × Bool) :
    mono ({sndFactor} : Set (Setoid (Bool × Bool))) s = (X (vsnd s.2) : Poly (Bool × Bool)) := by
  simp only [mono, finprod_mem_singleton, part_sndFactor]

/-- Definition 32 on the nose at a concrete point: `mono^F_{fst}((true, false))` is the
single variable `{p | p.1 = true}`, and in particular `mono` is not the empty product. -/
lemma mono_singleton_fst_true_false :
    mono ({fstFactor} : Set (Setoid (Bool × Bool))) (true, false)
      = (X (vfst true) : Poly (Bool × Bool)) :=
  mono_singleton_fst _

/-- **Definition 31 computed.**  `Q^F_S` is the four-term multilinear polynomial
`∑_{a, b} X_{[·]₁ = a} · X_{[·]₂ = b}` — the sum over the four points of `S` of the
product over the two factors, with nothing left folded up in a `finsum`/`finprod`. -/
lemma Q_coordFS_univ_eq :
    coordFS.Q Set.univ =
      (X (vfst true) * X (vsnd true) + X (vfst true) * X (vsnd false) +
        X (vfst false) * X (vsnd true) + X (vfst false) * X (vsnd false) :
          Poly (Bool × Bool)) := by
  rw [coordFS.Q_eq_finsum_mono, finsum_mem_univ, finsum_eq_sum_of_fintype]
  simp only [mono_coordFS_basis, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- `Q^F_S` is not the zero polynomial, so Definition 31 is not a definition of `0` in
disguise: evaluating every variable at `1` gives `4`. -/
lemma Q_coordFS_univ_ne_zero : coordFS.Q Set.univ ≠ 0 := by
  intro h
  have h' := congrArg (MvPolynomial.eval fun _ => (1 : ℝ)) h
  rw [Q_coordFS_univ_eq] at h'
  simp only [map_add, map_mul, eval_X, map_zero, mul_one] at h'
  norm_num at h'

lemma degreeOf_X_mul_X_le_one {a b : Set (Bool × Bool)} (hab : a ≠ b) (v : Set (Bool × Bool)) :
    ((X a : Poly (Bool × Bool)) * X b).degreeOf v ≤ 1 := by
  refine le_trans (MvPolynomial.degreeOf_mul_le v (X a) (X b)) ?_
  rw [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_X]
  rcases eq_or_ne v a with rfl | hva
  · rw [if_pos rfl, if_neg hab]
  · rw [if_neg hva]; split_ifs <;> simp

/-- The squarefreeness Proposition 28's proof turns on, exhibited: **every** variable has
degree at most one in `Q^F_S`.  This is Corollary 1 doing its work — the four monomials
each pick one block from each of the two factors, so no variable can appear twice. -/
lemma degreeOf_Q_coordFS_univ_le_one (v : Set (Bool × Bool)) :
    (coordFS.Q Set.univ).degreeOf v ≤ 1 := by
  rw [Q_coordFS_univ_eq]
  refine (MvPolynomial.degreeOf_add_le v _ _).trans
    (max_le ?_ (degreeOf_X_mul_X_le_one (vfst_ne_vsnd _ _) v))
  refine (MvPolynomial.degreeOf_add_le v _ _).trans
    (max_le ?_ (degreeOf_X_mul_X_le_one (vfst_ne_vsnd _ _) v))
  exact (MvPolynomial.degreeOf_add_le v _ _).trans
    (max_le (degreeOf_X_mul_X_le_one (vfst_ne_vsnd _ _) v)
      (degreeOf_X_mul_X_le_one (vfst_ne_vsnd _ _) v))

/-! ### Definition 33 collapses, and Proposition 26 says when it does not

`monos^F_C(E)` is an *image*, so coincident monomials collapse: `S` has four points but
`monos^F_{fst}(S)` has two elements, and `poly^F_{fst}(S)` accordingly has two summands
rather than four.  That collapse is precisely what Proposition 26 has to rule out at
`C = B`, and `mono_coordFS_basis_injective` is the instance of the ruling-out. -/

lemma monos_singleton_fst_univ :
    monos ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ
      = ({X (vfst true), X (vfst false)} : Set (Poly (Bool × Bool))) := by
  ext m
  simp only [monos, Set.image_univ, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    rw [mono_singleton_fst]
    cases a
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact ⟨(true, true), mono_singleton_fst _⟩
    · exact ⟨(false, false), mono_singleton_fst _⟩

lemma monos_singleton_snd_univ :
    monos ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ
      = ({X (vsnd true), X (vsnd false)} : Set (Poly (Bool × Bool))) := by
  ext m
  simp only [monos, Set.image_univ, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    rw [mono_singleton_snd]
    cases b
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact ⟨(true, true), mono_singleton_snd _⟩
    · exact ⟨(false, false), mono_singleton_snd _⟩

/-- **Definition 34 computed, with the collapse visible.**  `S` has four points, yet
`poly^F_{fst}(S)` is a sum of *two* monomials — the two blocks of `fstFactor`. -/
lemma poly_singleton_fst_univ :
    poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ
      = (X (vfst true) + X (vfst false) : Poly (Bool × Bool)) := by
  rw [poly, monos_singleton_fst_univ,
    finsum_mem_pair (fun h => vfst_true_ne_false (MvPolynomial.X_injective h))]

lemma poly_singleton_snd_univ :
    poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ
      = (X (vsnd true) + X (vsnd false) : Poly (Bool × Bool)) := by
  rw [poly, monos_singleton_snd_univ,
    finsum_mem_pair (fun h => vsnd_true_ne_false (MvPolynomial.X_injective h))]

/-- A separating evaluation: four pairwise-distinct values on the four variables of
`Poly^{coordFS}` that this file ever uses, chosen so that the four `B`-monomials evaluate
to the four distinct products `10`, `14`, `15`, `21`. -/
noncomputable def coordSep : Set (Bool × Bool) → ℝ := fun v =>
  if v = vfst true then 2 else if v = vfst false then 3 else if v = vsnd true then 5 else 7

lemma coordSep_vfst_true : coordSep (vfst true) = 2 := if_pos rfl

lemma coordSep_vfst_false : coordSep (vfst false) = 3 := by
  rw [coordSep, if_neg (Ne.symm vfst_true_ne_false), if_pos rfl]

lemma coordSep_vsnd_true : coordSep (vsnd true) = 5 := by
  rw [coordSep, if_neg (Ne.symm (vfst_ne_vsnd true true)),
    if_neg (Ne.symm (vfst_ne_vsnd false true)), if_pos rfl]

lemma coordSep_vsnd_false : coordSep (vsnd false) = 7 := by
  rw [coordSep, if_neg (Ne.symm (vfst_ne_vsnd true false)),
    if_neg (Ne.symm (vfst_ne_vsnd false false)), if_neg (Ne.symm vsnd_true_ne_false)]

lemma eval_coordSep_mono_coordFS (s : Bool × Bool) :
    MvPolynomial.eval coordSep (mono coordFS.B s) = coordSep (vfst s.1) * coordSep (vsnd s.2) := by
  rw [mono_coordFS_basis]; simp only [map_mul, eval_X]

/-- **The hypothesis of Proposition 26's proof, on the witness**: distinct points of `S`
have distinct `B`-monomials, so `monos^F_B(S)` does *not* collapse the way
`monos^F_{fst}(S)` does.  Proved by separating evaluation, not by citing Proposition 3. -/
lemma mono_coordFS_basis_injective : Function.Injective (mono coordFS.B) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h' := congrArg (MvPolynomial.eval coordSep) h
  rw [eval_coordSep_mono_coordFS, eval_coordSep_mono_coordFS] at h'
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [coordSep_vfst_true, coordSep_vfst_false, coordSep_vsnd_true,
      coordSep_vsnd_false] at h' <;>
    first
      | rfl
      | norm_num at h'

/-- Definition 34 at `C = B`, computed to the same explicit polynomial
`Q_coordFS_univ_eq` computes `Q^F_S` to.  Together the two are a **cross-check pair** for
Proposition 26 on this witness: neither mentions `Q_eq_poly`. -/
lemma poly_coordFS_basis_univ_eq :
    poly coordFS.B Set.univ =
      (X (vfst true) * X (vsnd true) + X (vfst true) * X (vsnd false) +
        X (vfst false) * X (vsnd true) + X (vfst false) * X (vsnd false) :
          Poly (Bool × Bool)) := by
  rw [poly, monos, finsum_mem_image mono_coordFS_basis_injective.injOn, finsum_mem_univ,
    finsum_eq_sum_of_fintype]
  simp only [mono_coordFS_basis, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- **Proposition 26 cross-checked** on `coordFS` at `E = S`: the two sides are computed
separately and agree.  This declaration does not mention `Q_eq_poly`. -/
lemma prop26_coordFS_crosscheck : coordFS.Q Set.univ = poly coordFS.B Set.univ :=
  Q_coordFS_univ_eq.trans poly_coordFS_basis_univ_eq.symm

/-- Proposition 26 **applied** on `coordFS` at `E = S` — the endpoint instantiated, which
is a different claim from cross-checking it, and is recorded separately for that reason. -/
lemma prop26_coordFS_applied : coordFS.Q Set.univ = poly coordFS.B Set.univ :=
  coordFS.Q_eq_poly Set.univ

/-! ### Definition 35: the irreducible parts of `S` and of the diagonal

At `E = S` the two coordinate factors are independent and `Irr^F(S)` is the two
singletons.  Note that Definition 35's minimality clause is *vacuous* at a singleton: the
only strict subset of `{b}` is `∅`, which is not nonempty — so what does the work at `S`
is ruling out `C = B`, which fails minimality because `{fstFactor}` already fixes `S`.

On the diagonal `Ediag = {p | p.1 = p.2}` the picture inverts: neither coordinate alone
fixes `Ediag` (`χ^F_{fst}(Ediag, Ediag) ∋ (true, false) ∉ Ediag`), so the only irreducible
part is the whole basis.  This is the §5 shadow of the §4 fact that restricting to `Ediag`
entangles two orthogonal factors. -/

lemma subset_coordFS_basis_cases {C : Set (Setoid (Bool × Bool))} (h : C ⊆ coordFS.B) :
    C = ∅ ∨ C = {fstFactor} ∨ C = {sndFactor} ∨ C = coordFS.B := by
  by_cases hf : fstFactor ∈ C <;> by_cases hs : sndFactor ∈ C
  · refine Or.inr (Or.inr (Or.inr (Set.Subset.antisymm h ?_)))
    rintro x (rfl | rfl)
    exacts [hf, hs]
  · refine Or.inr (Or.inl (Set.Subset.antisymm ?_ (Set.singleton_subset_iff.2 hf)))
    intro x hx
    rcases h hx with rfl | rfl
    · rfl
    · exact absurd hx hs
  · refine Or.inr (Or.inr (Or.inl (Set.Subset.antisymm ?_ (Set.singleton_subset_iff.2 hs))))
    intro x hx
    rcases h hx with rfl | rfl
    · exact absurd hx hf
    · rfl
  · refine Or.inl (Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_)
    rcases h hx with rfl | rfl
    · exact hf hx
    · exact hs hx

lemma singleton_mem_irr_univ {b : Setoid (Bool × Bool)} (hb : b ∈ coordFS.B) :
    ({b} : Set (Setoid (Bool × Bool))) ∈ coordFS.irr Set.univ := by
  refine ⟨⟨b, rfl⟩, Set.singleton_subset_iff.2 hb, coordFS.chimeraImage_univ_univ _, ?_⟩
  intro D hD hne
  rw [Set.ssubset_singleton_iff] at hD
  exact absurd hne (hD ▸ Set.not_nonempty_empty)

/-- Definition 35 is inhabited: `{fstFactor}` is an irreducible part of `S`. -/
lemma mem_irr_singleton_fst_univ :
    ({fstFactor} : Set (Setoid (Bool × Bool))) ∈ coordFS.irr Set.univ :=
  singleton_mem_irr_univ fstFactor_mem

/-- …and so is `{sndFactor}`, so `Irr^F(S)` has more than one member. -/
lemma mem_irr_singleton_snd_univ :
    ({sndFactor} : Set (Setoid (Bool × Bool))) ∈ coordFS.irr Set.univ :=
  singleton_mem_irr_univ sndFactor_mem

/-- **Definition 35 computed at `E = S`**: `Irr^F(S) = {{fstFactor}, {sndFactor}}`.  The
whole basis is excluded by minimality, and `∅` by nonemptiness. -/
lemma irr_coordFS_univ : coordFS.irr Set.univ = {{fstFactor}, {sndFactor}} := by
  ext C
  constructor
  · rintro ⟨⟨c, hc⟩, hsub, -, hmin⟩
    rcases subset_coordFS_basis_cases hsub with rfl | rfl | rfl | rfl
    · exact absurd hc (Set.notMem_empty c)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · refine absurd (coordFS.chimeraImage_univ_univ ({fstFactor} : Set (Setoid (Bool × Bool))))
        (hmin {fstFactor} ⟨Set.singleton_subset_iff.2 fstFactor_mem, ?_⟩ ⟨fstFactor, rfl⟩)
      intro hcon
      exact fstFactor_ne_sndFactor (Set.mem_singleton_iff.1 (hcon sndFactor_mem)).symm
  · rintro (rfl | rfl)
    · exact mem_irr_singleton_fst_univ
    · exact mem_irr_singleton_snd_univ

lemma Ediag_nonempty : Ediag.Nonempty := ⟨(false, false), rfl⟩

lemma chimeraImage_basis_Ediag : coordFS.chimeraImage coordFS.B Ediag Ediag = Ediag := by
  ext u
  constructor
  · rintro ⟨t, ht, r, -, rfl⟩
    rwa [coordFS.chimera_basis]
  · intro hu
    exact ⟨u, hu, (false, false), rfl, coordFS.chimera_basis _ _⟩

/-- Restricting to the diagonal entangles: `χ^F_{fst}(Ediag, Ediag)` contains
`(true, false)`, which is not on the diagonal. -/
lemma chimeraImage_singleton_fst_Ediag_ne :
    coordFS.chimeraImage ({fstFactor} : Set (Setoid (Bool × Bool))) Ediag Ediag ≠ Ediag := by
  intro h
  have hmem : ((true, false) : Bool × Bool) ∈
      coordFS.chimeraImage ({fstFactor} : Set (Setoid (Bool × Bool))) Ediag Ediag :=
    ⟨(true, true), rfl, (false, false), rfl, coordFS_chimera_corners.2.1⟩
  rw [h] at hmem
  exact Bool.noConfusion (hmem : (true : Bool) = false)

lemma chimeraImage_singleton_snd_Ediag_ne :
    coordFS.chimeraImage ({sndFactor} : Set (Setoid (Bool × Bool))) Ediag Ediag ≠ Ediag := by
  intro h
  have hmem : ((false, true) : Bool × Bool) ∈
      coordFS.chimeraImage ({sndFactor} : Set (Setoid (Bool × Bool))) Ediag Ediag :=
    ⟨(true, true), rfl, (false, false), rfl, coordFS_chimera_corners.2.2.1⟩
  rw [h] at hmem
  exact Bool.noConfusion (hmem : (false : Bool) = true)

/-- **Definition 35 computed at `E = Ediag`**: `Irr^F(Ediag) = {B}`.  So `Irr^F` is not a
constant of `F` — it genuinely depends on `E`, and the dependence is the §4 entanglement
seen through §5. -/
lemma irr_coordFS_Ediag : coordFS.irr Ediag = {coordFS.B} := by
  ext C
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨c, hc⟩, hsub, hchi, -⟩
    rcases subset_coordFS_basis_cases hsub with rfl | rfl | rfl | rfl
    · exact absurd hc (Set.notMem_empty c)
    · exact absurd hchi chimeraImage_singleton_fst_Ediag_ne
    · exact absurd hchi chimeraImage_singleton_snd_Ediag_ne
    · rfl
  · rintro rfl
    refine ⟨⟨fstFactor, fstFactor_mem⟩, subset_rfl, chimeraImage_basis_Ediag, ?_⟩
    intro D hD hne
    rcases subset_coordFS_basis_cases hD.1 with rfl | rfl | rfl | rfl
    · exact absurd hne Set.not_nonempty_empty
    · exact chimeraImage_singleton_fst_Ediag_ne
    · exact chimeraImage_singleton_snd_Ediag_ne
    · exact absurd subset_rfl hD.2

/-! ### The factorization of `Q^F_S`, computed and applied -/

/-- **Proposition 30's factorization at `E = S`, computed.**  Both sides are expanded from
Definitions 31 and 34 and compared as polynomials; this declaration does not mention
`Q_eq_finprod_poly_irr`. -/
lemma Q_coordFS_univ_eq_mul_poly :
    coordFS.Q Set.univ
      = poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ
        * poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ := by
  rw [Q_coordFS_univ_eq, poly_singleton_fst_univ, poly_singleton_snd_univ]
  ring

lemma singleton_fst_ne_singleton_snd :
    ({fstFactor} : Set (Setoid (Bool × Bool))) ≠ {sndFactor} := by
  intro h
  exact fstFactor_ne_sndFactor (Set.mem_singleton_iff.1 (h ▸ Set.mem_singleton fstFactor))

/-- Proposition 30 **applied** at `E = S`, using the computed `Irr^F(S)`.  It lands on the
same product `Q_coordFS_univ_eq_mul_poly` computes, so the two cross-check the endpoint. -/
lemma prop30_coordFS_univ_applied :
    coordFS.Q Set.univ
      = poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ
        * poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ := by
  rw [coordFS.Q_eq_finprod_poly_irr ⟨(true, true), Set.mem_univ _⟩, irr_coordFS_univ,
    finprod_mem_pair singleton_fst_ne_singleton_snd]

/-- Proposition 30 **applied** at `E = Ediag`, where the product has a single factor: it
degenerates into Proposition 26's statement at `Ediag`, which is a consistency check
between two endpoints rather than a factorization. -/
lemma prop30_coordFS_Ediag_applied : coordFS.Q Ediag = poly coordFS.B Ediag := by
  rw [coordFS.Q_eq_finprod_poly_irr Ediag_nonempty, irr_coordFS_Ediag, finprod_mem_singleton]

/-- **Proposition 28's divisor exhibited, computed.**  `poly^F_{fst}(S)` really divides
`Q^F_S`, so Proposition 28 is not quantifying over an empty set of divisors on this
witness.  Nothing here cites `eq_C_mul_poly_of_dvd_Q` — the cofactor is read straight off
`Q_coordFS_univ_eq_mul_poly`.

The proposition's *conclusion* is deliberately not folded into this statement: exhibiting
`p = C r · poly^F_C(S)` at `p := poly^F_{fst}(S)` is trivially satisfiable at `r = 1`,
`C = {fstFactor}` (see the probe `example` below, which proves that shape for *every*
`C ⊆ B` with no finiteness, no divisibility and no nonemptiness).  The informative
instances are `prop28_coordFS_scaled_applied` / `prop28_r_loadbearing`, where the divisor
is *not* any `poly^F_C(S)` and the coefficient `r` is what saves the conclusion, and
`prop28_coordFS_const_applied` / `prop28_const_forces_empty`, where `C` is forced to `∅`. -/
lemma poly_singleton_fst_dvd_Q_coordFS_univ :
    poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ ∣ coordFS.Q Set.univ :=
  ⟨_, Q_coordFS_univ_eq_mul_poly⟩

/-- The probe behind the paragraph above: Proposition 28's existential, *asserted at a
`poly^F_C(E)`*, is a triviality — it holds for every `C ⊆ B` and every `E`, with none of
the proposition's hypotheses.  So a witness of that shape certifies nothing beyond the
divisibility it is paired with. -/
example {S : Type u} (F : FactoredSet S) {C : Set (Setoid S)} (hC : C ⊆ F.B) (E : Set S) :
    ∃ (r : ℝ) (C' : Set (Setoid S)), C' ⊆ F.B ∧ poly C E = MvPolynomial.C r * poly C' E :=
  ⟨1, C, hC, by rw [map_one, one_mul]⟩

/-- **Proposition 31's conclusion is not vacuous on the witness**: `poly^F_{fst}(S)` is not
a unit, so calling it irreducible says something.  (In `Poly^F` over `ℝ` the units are the
nonzero constants; this polynomial has no constant term, so evaluating every variable at
`0` gives `0`.) -/
lemma not_isUnit_poly_singleton_fst_univ :
    ¬ IsUnit (poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ) := by
  intro h
  have h0 : MvPolynomial.eval (fun _ => (0 : ℝ))
      (poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ) = 0 := by
    rw [poly_singleton_fst_univ]
    simp
  have hu := h.map (MvPolynomial.eval (fun _ => (0 : ℝ)))
  rw [h0] at hu
  exact zero_ne_one (isUnit_zero_iff.1 hu)

/-- …and neither is the other factor. -/
lemma not_isUnit_poly_singleton_snd_univ :
    ¬ IsUnit (poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ) := by
  intro h
  have h0 : MvPolynomial.eval (fun _ => (0 : ℝ))
      (poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ) = 0 := by
    rw [poly_singleton_snd_univ]
    simp
  have hu := h.map (MvPolynomial.eval (fun _ => (0 : ℝ)))
  rw [h0] at hu
  exact zero_ne_one (isUnit_zero_iff.1 hu)

/-! ### `E = Efst`: a third subset, where Definitions 31 and 34 take different values

`Efst = {p | p.1 = true}` is a *block* of `fstFactor`, so the first coordinate is constant
on it and the second is free.  That makes it the subset the §5 endpoints have the most to
say about: `poly^F_{fst}(Efst)` collapses to a single variable while `poly^F_{snd}(Efst)`
keeps both of its, so Propositions 27 and 30 factor `Q^{coordFS}_{Efst}` into two
*different* polynomials — where at `E = S` the two factors are symmetric and at `E = Ediag`
there is only one factor.  `S` and `Efst` also make Proposition 27's two set arguments
genuinely different, which is what its chimera splice needs in order to be doing work. -/

lemma Efst_nonempty : Efst.Nonempty := ⟨(true, true), rfl⟩

lemma Efst_eq : Efst = ({(true, true), (true, false)} : Set (Bool × Bool)) := by
  ext ⟨a, b⟩
  constructor
  · intro h
    cases b
    · exact Or.inr (by rw [(show a = true from h)]; rfl)
    · exact Or.inl (by rw [(show a = true from h)])
  · rintro (h | h) <;> rw [h] <;> rfl

/-- **Definition 34 at `C = {fstFactor}`, `E = Efst`**: the image `monos` collapses `Efst`'s
two points to one monomial, so `poly^F_{fst}(Efst)` is the *single variable* `X_{[·]₁=true}`
— a different value from `poly^F_{fst}(S)`, which has two summands. -/
lemma poly_singleton_fst_Efst :
    poly ({fstFactor} : Set (Setoid (Bool × Bool))) Efst
      = (X (vfst true) : Poly (Bool × Bool)) := by
  have hmonos : monos ({fstFactor} : Set (Setoid (Bool × Bool))) Efst
      = ({X (vfst true)} : Set (Poly (Bool × Bool))) := by
    ext m
    simp only [monos, Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [mono_singleton_fst, (show s.1 = true from hs)]
    · rintro rfl
      exact ⟨(true, true), rfl, mono_singleton_fst _⟩
  rw [poly, hmonos, finsum_mem_singleton]

/-- …while at `C = {sndFactor}` nothing collapses: `poly^F_{snd}(Efst)` still has both
blocks of the second coordinate. -/
lemma poly_singleton_snd_Efst :
    poly ({sndFactor} : Set (Setoid (Bool × Bool))) Efst
      = (X (vsnd true) + X (vsnd false) : Poly (Bool × Bool)) := by
  have hmonos : monos ({sndFactor} : Set (Setoid (Bool × Bool))) Efst
      = ({X (vsnd true), X (vsnd false)} : Set (Poly (Bool × Bool))) := by
    ext m
    simp only [monos, Efst_eq, Set.image_insert_eq, Set.image_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff, mono_singleton_snd]
  rw [poly, hmonos,
    finsum_mem_pair (fun h => vsnd_true_ne_false (MvPolynomial.X_injective h))]

/-- **Definition 31 computed at `E = Efst`**: a two-term polynomial, half of `Q^F_S`. -/
lemma Q_coordFS_Efst_eq :
    coordFS.Q Efst
      = (X (vfst true) * X (vsnd true) + X (vfst true) * X (vsnd false) :
          Poly (Bool × Bool)) := by
  rw [coordFS.Q_eq_finsum_mono, Efst_eq,
    finsum_mem_pair (show ((true, true) : Bool × Bool) ≠ (true, false) by
      intro h; exact Bool.noConfusion (congrArg Prod.snd h)),
    mono_coordFS_basis, mono_coordFS_basis]

/-- Definition 34 at `C = B`, `E = Efst`, computed to the same explicit polynomial
`Q_coordFS_Efst_eq` computes `Q^F_{Efst}` to — the `E = Efst` half of the Proposition 26
cross-check pair. -/
lemma poly_coordFS_basis_Efst_eq :
    poly coordFS.B Efst
      = (X (vfst true) * X (vsnd true) + X (vfst true) * X (vsnd false) :
          Poly (Bool × Bool)) := by
  rw [poly, monos, finsum_mem_image mono_coordFS_basis_injective.injOn, Efst_eq,
    finsum_mem_pair (show ((true, true) : Bool × Bool) ≠ (true, false) by
      intro h; exact Bool.noConfusion (congrArg Prod.snd h)),
    mono_coordFS_basis, mono_coordFS_basis]

/-- Proposition 26 **applied** at `E = Efst`. -/
lemma prop26_coordFS_Efst_applied : coordFS.Q Efst = poly coordFS.B Efst :=
  coordFS.Q_eq_poly Efst

/-- …and **cross-checked** at `E = Efst`: both sides computed, no mention of `Q_eq_poly`. -/
lemma prop26_coordFS_Efst_crosscheck : coordFS.Q Efst = poly coordFS.B Efst :=
  Q_coordFS_Efst_eq.trans poly_coordFS_basis_Efst_eq.symm

/-- Every point of `Efst` has first coordinate `true`, so *every* `C` fixes `Efst` in the
sense of Definition 35 — including the singletons.  This is what makes `Irr^F(Efst)` the
two singletons rather than `{B}`. -/
lemma chimeraImage_Efst (C : Set (Setoid (Bool × Bool))) :
    coordFS.chimeraImage C Efst Efst = Efst := by
  ext u
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    rw [coordFS_chimera_eq]
    show (if fstFactor ∈ C then s.1 else t.1) = true
    split_ifs
    · exact hs
    · exact ht
  · intro hu
    exact ⟨u, hu, u, hu, coordFS.chimera_self _ u⟩

/-- **Definition 35 computed at `E = Efst`**: `Irr^F(Efst) = {{fstFactor}, {sndFactor}}`, as
at `E = S` — so `Irr^F` agreeing at two subsets does *not* mean the factorizations agree,
because the factors themselves differ (`prop30_coordFS_Efst_applied`). -/
lemma irr_coordFS_Efst : coordFS.irr Efst = {{fstFactor}, {sndFactor}} := by
  ext D
  constructor
  · rintro ⟨⟨c, hc⟩, hsub, -, hmin⟩
    rcases subset_coordFS_basis_cases hsub with rfl | rfl | rfl | rfl
    · exact absurd hc (Set.notMem_empty c)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · refine absurd (chimeraImage_Efst ({fstFactor} : Set (Setoid (Bool × Bool))))
        (hmin {fstFactor} ⟨Set.singleton_subset_iff.2 fstFactor_mem, ?_⟩ ⟨fstFactor, rfl⟩)
      intro hcon
      exact fstFactor_ne_sndFactor (Set.mem_singleton_iff.1 (hcon sndFactor_mem)).symm
  · rintro (rfl | rfl)
    · exact ⟨⟨fstFactor, rfl⟩, singleton_fstFactor_subset, chimeraImage_Efst _, by
        intro D hD hne
        rw [Set.ssubset_singleton_iff] at hD
        exact absurd hne (hD ▸ Set.not_nonempty_empty)⟩
    · exact ⟨⟨sndFactor, rfl⟩, singleton_sndFactor_subset, chimeraImage_Efst _, by
        intro D hD hne
        rw [Set.ssubset_singleton_iff] at hD
        exact absurd hne (hD ▸ Set.not_nonempty_empty)⟩

/-- **Proposition 30 applied at `E = Efst`**, where the two factors are *different*
polynomials: `poly^F_{fst}(Efst)` is a single variable and `poly^F_{snd}(Efst)` is a sum of
two.  At `E = S` the factorization is symmetric and at `E = Ediag` it has one factor, so
this is the instance where the product structure is visible. -/
lemma prop30_coordFS_Efst_applied :
    coordFS.Q Efst
      = poly ({fstFactor} : Set (Setoid (Bool × Bool))) Efst
        * poly ({sndFactor} : Set (Setoid (Bool × Bool))) Efst := by
  rw [coordFS.Q_eq_finprod_poly_irr Efst_nonempty, irr_coordFS_Efst,
    finprod_mem_pair singleton_fst_ne_singleton_snd]

/-- …cross-checked by computing both sides.  This declaration does not mention
`Q_eq_finprod_poly_irr`. -/
lemma prop30_coordFS_Efst_crosscheck :
    coordFS.Q Efst
      = poly ({fstFactor} : Set (Setoid (Bool × Bool))) Efst
        * poly ({sndFactor} : Set (Setoid (Bool × Bool))) Efst := by
  rw [Q_coordFS_Efst_eq, poly_singleton_fst_Efst, poly_singleton_snd_Efst]
  ring

/-! ### Proposition 27 at a nontrivial split, and the orientation of its chimera

Proposition 27 splices `E₀` against `E₁` along a *disjoint* pair `C₀`, `C₁` of subsets of
`B`.  The instance below takes `C₀ = {fstFactor}`, `C₁ = {sndFactor}`, `E₀ = Efst`,
`E₁ = S` — so `C₀ ∪ C₁ = B`, `C₀ ∩ C₁ = ∅`, both are nonempty, and `E₀ ≠ E₁`.  Every
degeneracy the proposition could hide behind is therefore ruled out at once, and the
argument order of the chimera is pinned executably by `prop27_reversed_false`. -/

lemma singleton_fst_union_snd_eq_basis :
    ({fstFactor} : Set (Setoid (Bool × Bool))) ∪ {sndFactor} = coordFS.B := rfl

lemma disjoint_singleton_fst_snd :
    Disjoint ({fstFactor} : Set (Setoid (Bool × Bool))) {sndFactor} := by
  rw [Set.disjoint_singleton]
  exact fstFactor_ne_sndFactor

/-- Splicing `Efst`'s first coordinate onto anything leaves `Efst`: `χ^F_{fst}(Efst, S)`
is `Efst` again. -/
lemma chimeraImage_fst_Efst_univ :
    coordFS.chimeraImage ({fstFactor} : Set (Setoid (Bool × Bool))) Efst Set.univ = Efst := by
  ext u
  constructor
  · rintro ⟨s, hs, t, -, rfl⟩
    rw [coordFS_chimera_eq]
    show (if fstFactor ∈ ({fstFactor} : Set (Setoid (Bool × Bool))) then s.1 else t.1) = true
    rw [if_pos (Set.mem_singleton _)]
    exact hs
  · intro hu
    exact ⟨u, hu, u, Set.mem_univ _, coordFS.chimera_self _ u⟩

/-- **Proposition 27 applied on `coordFS` at a nontrivial split**: `C₀ = {fstFactor}` and
`C₁ = {sndFactor}` are disjoint and nonempty, and `E₀ = Efst ≠ S = E₁`. -/
lemma prop27_coordFS_applied :
    poly coordFS.B Efst
      = poly ({fstFactor} : Set (Setoid (Bool × Bool))) Efst
        * poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ := by
  have h := coordFS.poly_union_chimeraImage singleton_fstFactor_subset
    singleton_sndFactor_subset disjoint_singleton_fst_snd Efst Set.univ
  rwa [chimeraImage_fst_Efst_univ, singleton_fst_union_snd_eq_basis] at h

/-- The same identity **computed** from Definitions 32–34: this declaration does not
mention `poly_union_chimeraImage`. -/
lemma prop27_coordFS_crosscheck :
    poly coordFS.B Efst
      = poly ({fstFactor} : Set (Setoid (Bool × Bool))) Efst
        * poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ := by
  rw [poly_coordFS_basis_Efst_eq, poly_singleton_fst_Efst, poly_singleton_snd_univ]
  ring

/-- **Proposition 27's chimera argument order is load-bearing.**  Reading its spliced set as
`χ^F_{C₀}(E₁, E₀)` instead of `χ^F_{C₀}(E₀, E₁)` makes the conclusion *false* at
`C₀ = {fstFactor}`, `C₁ = {sndFactor}`, `E₀ = Efst`, `E₁ = S`: the reversed splice is all
of `S`, whose `poly^F_B` evaluates to `60` under `coordSep`, where the right-hand side
evaluates to `2 · 12 = 24`. -/
lemma prop27_reversed_false :
    poly coordFS.B
        (coordFS.chimeraImage ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ Efst)
      ≠ poly ({fstFactor} : Set (Setoid (Bool × Bool))) Efst
        * poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ := by
  have hchi : coordFS.chimeraImage ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ Efst
      = Set.univ := by
    ext ⟨a, b⟩
    simp only [Set.mem_univ, iff_true]
    refine ⟨(a, a), Set.mem_univ _, (true, b), rfl, ?_⟩
    rw [coordFS_chimera_eq, if_pos (Set.mem_singleton _),
      if_neg (by simpa using Ne.symm fstFactor_ne_sndFactor)]
  rw [hchi]
  intro h
  have h' := congrArg (MvPolynomial.eval coordSep) h
  rw [poly_coordFS_basis_univ_eq] at h'
  rw [poly_singleton_fst_Efst, poly_singleton_snd_univ] at h'
  simp only [map_add, map_mul, eval_X, coordSep_vfst_true, coordSep_vfst_false,
    coordSep_vsnd_true, coordSep_vsnd_false] at h'
  norm_num at h'

/-! ### Proposition 28 where its conclusion is doing work

The divisor exhibited above has Proposition 28's shape for the uninteresting reason that
it *is* a `poly^F_C(S)`.  The two instances here are the ones that certify the endpoint's
two moving parts.  First, `2 · poly^F_{fst}(S)` is a divisor of `Q^F_S` that is not equal
to `poly^F_C(S)` for **any** `C ⊆ B`, so the real coefficient `r` in the conclusion cannot
be dropped.  Second, a nonzero constant divides `Q^F_S` too, and there the conclusion's
`C` is forced to be `∅` — the degenerate corner Proposition 31's case split exists for. -/

lemma univ_nonempty_coord : (Set.univ : Set (Bool × Bool)).Nonempty :=
  ⟨(true, true), Set.mem_univ _⟩

lemma two_mul_poly_fst_dvd_Q_coordFS_univ :
    (MvPolynomial.C (2 : ℝ) * poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ)
      ∣ coordFS.Q Set.univ := by
  refine ⟨MvPolynomial.C (2⁻¹ : ℝ) * poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ, ?_⟩
  rw [Q_coordFS_univ_eq_mul_poly,
    show (MvPolynomial.C (2 : ℝ) * poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ)
        * (MvPolynomial.C (2⁻¹ : ℝ) * poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ)
      = (MvPolynomial.C (2 : ℝ) * MvPolynomial.C (2⁻¹ : ℝ))
        * (poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ
          * poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ) from by ring,
    ← map_mul, show (2 : ℝ) * 2⁻¹ = 1 from by norm_num, map_one, one_mul]

/-- **Proposition 28 applied at a divisor that is not any `poly^F_C(S)`.** -/
lemma prop28_coordFS_scaled_applied :
    ∃ (r : ℝ) (C : Set (Setoid (Bool × Bool))), C ⊆ coordFS.B ∧
      MvPolynomial.C (2 : ℝ) * poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ
        = MvPolynomial.C r * poly C Set.univ :=
  coordFS.eq_C_mul_poly_of_dvd_Q univ_nonempty_coord two_mul_poly_fst_dvd_Q_coordFS_univ

lemma eval_coordSep_poly_fst :
    MvPolynomial.eval coordSep (poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ)
      = 5 := by
  rw [poly_singleton_fst_univ]
  simp only [map_add, eval_X, coordSep_vfst_true, coordSep_vfst_false]
  norm_num

lemma eval_coordSep_poly_snd :
    MvPolynomial.eval coordSep (poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ)
      = 12 := by
  rw [poly_singleton_snd_univ]
  simp only [map_add, eval_X, coordSep_vsnd_true, coordSep_vsnd_false]
  norm_num

lemma eval_coordSep_poly_basis :
    MvPolynomial.eval coordSep (poly coordFS.B Set.univ) = 60 := by
  rw [poly_coordFS_basis_univ_eq]
  simp only [map_add, map_mul, eval_X, coordSep_vfst_true, coordSep_vfst_false,
    coordSep_vsnd_true, coordSep_vsnd_false]
  norm_num

/-- **Proposition 28's real coefficient `r` is load-bearing.**  The divisor
`2 · poly^F_{fst}(S)` of `Q^F_S` is not equal to `poly^F_C(S)` for any of the four
`C ⊆ B`, so the conclusion would be false without the `C r` factor.  Separated by the
evaluation `coordSep`, at which the four candidates take the values `1`, `5`, `12`, `60`
while the divisor takes `10`. -/
lemma prop28_r_loadbearing :
    ∀ C ⊆ coordFS.B,
      MvPolynomial.C (2 : ℝ) * poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ
        ≠ poly C Set.univ := by
  intro D hD h
  have h' := congrArg (MvPolynomial.eval coordSep) h
  rw [map_mul, eval_C, eval_coordSep_poly_fst] at h'
  rcases subset_coordFS_basis_cases hD with rfl | rfl | rfl | rfl
  · rw [poly_empty univ_nonempty_coord] at h'; norm_num at h'
  · rw [eval_coordSep_poly_fst] at h'; norm_num at h'
  · rw [eval_coordSep_poly_snd] at h'; norm_num at h'
  · rw [eval_coordSep_poly_basis] at h'; norm_num at h'

/-- **Proposition 28 applied at a constant (unit) divisor.**  Every nonzero constant
divides `Q^F_S`, so this instance is forced on the endpoint. -/
lemma prop28_coordFS_const_applied :
    ∃ (r : ℝ) (C : Set (Setoid (Bool × Bool))), C ⊆ coordFS.B ∧
      (MvPolynomial.C (3 : ℝ) : Poly (Bool × Bool))
        = MvPolynomial.C r * poly C Set.univ := by
  refine coordFS.eq_C_mul_poly_of_dvd_Q univ_nonempty_coord ?_
  exact ⟨MvPolynomial.C (3⁻¹ : ℝ) * coordFS.Q Set.univ, by
    rw [← mul_assoc, ← map_mul, show (3 : ℝ) * 3⁻¹ = 1 from by norm_num, map_one, one_mul]⟩

/-- …and the `C` it returns really must be `∅`, so the empty factor set in Proposition 28's
conclusion is not decoration: a constant has no variables, while `poly^F_C(S)` has one for
every `b ∈ C`. -/
lemma prop28_const_forces_empty
    {r : ℝ} {D : Set (Setoid (Bool × Bool))} (hD : D ⊆ coordFS.B)
    (h : (MvPolynomial.C (3 : ℝ) : Poly (Bool × Bool)) = MvPolynomial.C r * poly D Set.univ) :
    D = ∅ := by
  by_contra hne
  obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hr : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at h
    exact three_ne_zero (MvPolynomial.C_injective _ _ (h.trans (map_zero _).symm))
  have hmem : part b ((true, true) : Bool × Bool) ∈ (poly D Set.univ).vars :=
    (coordFS.mem_vars_poly hD Set.univ).2 ⟨b, hb, (true, true), Set.mem_univ _, rfl⟩
  have hvars : (poly D Set.univ).vars = (MvPolynomial.C (3 : ℝ) : Poly (Bool × Bool)).vars := by
    rw [h, vars_C_mul _ hr]
  rw [hvars, vars_C] at hmem
  exact absurd hmem (Finset.notMem_empty _)

/-! ### Proposition 29 applied, cross-checked against the computed `Irr^F`

The endpoint is applied at both subsets where `Irr^F` was computed, and in each case the
cover clause is re-derived from the computed value without mentioning `irr_partition`. -/

/-- **Proposition 29 applied at `E = S`**: all three clauses. -/
lemma prop29_coordFS_univ_applied :
    (∀ C ∈ coordFS.irr Set.univ, C.Nonempty) ∧
      (coordFS.irr Set.univ).PairwiseDisjoint id ∧ ⋃₀ coordFS.irr Set.univ = coordFS.B :=
  coordFS.irr_partition univ_nonempty_coord

/-- The cover clause cross-checked against the computed `Irr^F(S) = {{fst}, {snd}}`: this
is Proposition 29's third conjunct at `E = S` verbatim, re-derived from Definition 35's
computed value, and this declaration does not mention `irr_partition`. -/
lemma sUnion_irr_coordFS_univ_crosscheck :
    ⋃₀ coordFS.irr Set.univ = coordFS.B := by
  rw [irr_coordFS_univ, Set.sUnion_insert, Set.sUnion_singleton]
  rfl

/-- **Proposition 29 applied at `E = Ediag`**, where the partition of `B` is the single
block `B` — a different partition from the one at `E = S`, so the proposition is not
asserting a constant. -/
lemma prop29_coordFS_Ediag_applied :
    ⋃₀ coordFS.irr Ediag = coordFS.B :=
  (coordFS.irr_partition Ediag_nonempty).2.2

/-- The same cover clause at `E = Ediag`, re-derived from the computed
`Irr^F(Ediag) = {B}`: this declaration does not mention `irr_partition` either. -/
lemma sUnion_irr_coordFS_Ediag_crosscheck :
    ⋃₀ coordFS.irr Ediag = coordFS.B := by
  rw [irr_coordFS_Ediag]
  exact Set.sUnion_singleton _

/-- `irr_isPartition` applied: Proposition 29's §4 restatement is inhabited on the
witness, so the `Subpartition` it promises really is constructed. -/
lemma irr_isPartition_coordFS_univ_applied :
    ∃ P : Subpartition (Setoid (Bool × Bool)),
      P.dom = coordFS.B ∧ P.classes = coordFS.irr Set.univ :=
  coordFS.irr_isPartition univ_nonempty_coord

/-! ### Proposition 31 applied, and the negative that stops `Irreducible` being total -/

/-- **Proposition 31 applied on `coordFS`**: `poly^F_{fst}(S)` is irreducible. -/
lemma prop31_coordFS_fst_applied :
    Irreducible (poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ) :=
  coordFS.irreducible_poly_of_mem_irr univ_nonempty_coord mem_irr_singleton_fst_univ

/-- …and so is the other irreducible part's polynomial. -/
lemma prop31_coordFS_snd_applied :
    Irreducible (poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ) :=
  coordFS.irreducible_poly_of_mem_irr univ_nonempty_coord mem_irr_singleton_snd_univ

/-- **The negative check**: `Irreducible` is not vacuously total on `Poly^{coordFS}` —
`Q^F_S` itself is *reducible*, since it factors as the product of the two irreducibles
above.  Without this, Proposition 31 could be true because everything in sight is
irreducible. -/
lemma not_irreducible_Q_coordFS_univ : ¬ Irreducible (coordFS.Q Set.univ) := by
  intro h
  rcases h.isUnit_or_isUnit Q_coordFS_univ_eq_mul_poly with hu | hu
  · exact not_isUnit_poly_singleton_fst_univ hu
  · exact not_isUnit_poly_singleton_snd_univ hu

/-! ### The remaining §5.1 endpoints, applied on the witness

`Q_ne_zero`, `degreeOf_Q_le` and `vars_disjoint_of_mul_eq_Q` are the three §5.1 results the
computed facts above shadow but never instantiate.  Each is applied here, so the computed
and the applied form sit side by side. -/

lemma Q_ne_zero_coordFS_applied : coordFS.Q Set.univ ≠ 0 :=
  coordFS.Q_ne_zero univ_nonempty_coord

lemma degreeOf_Q_le_coordFS_applied (v : Set (Bool × Bool)) :
    (coordFS.Q Set.univ).degreeOf v ≤ 1 :=
  coordFS.degreeOf_Q_le Set.univ v

/-- The variable-disjointness behind Proposition 28's coefficient argument, applied to the
computed factorization: the two factors of `Q^F_S` share no variable. -/
lemma vars_disjoint_coordFS_applied :
    Disjoint (poly ({fstFactor} : Set (Setoid (Bool × Bool))) Set.univ).vars
      (poly ({sndFactor} : Set (Setoid (Bool × Bool))) Set.univ).vars :=
  coordFS.vars_disjoint_of_mul_eq_Q univ_nonempty_coord Q_coordFS_univ_eq_mul_poly.symm

/-! ### The `E.Nonempty` hypotheses of §5 are load-bearing, not decoration

Propositions 28, 30 and 31 all carry `hE : E.Nonempty`.  At `E = ∅` the characteristic
polynomial is `0` and every `poly^F_C(∅)` is `0`, and each of the three conclusions fails
outright — Proposition 30's on the zero-dimensional `unitFS`, where the empty product is
`1` rather than `0`.  Proposition 29's `hE`, by contrast, is *not* consumed (its docstring
says so), and `irr_partition_holds_at_empty` is the computation that backs that claim. -/

/-- `poly^F_C(∅) = 0` for every `C`: the sum over an empty image.  Not to be confused with
`poly_empty`, which is the `C = ∅` corner and gives `1`. -/
lemma poly_empty_eq_zero (C : Set (Setoid (Bool × Bool))) :
    poly C (∅ : Set (Bool × Bool)) = 0 := by
  rw [poly, monos, Set.image_empty, finsum_mem_empty]

lemma Q_coordFS_empty : coordFS.Q (∅ : Set (Bool × Bool)) = 0 := by
  rw [coordFS.Q_eq_finsum_mono, finsum_mem_empty]

lemma chimeraImage_empty (C : Set (Setoid (Bool × Bool))) :
    coordFS.chimeraImage C (∅ : Set (Bool × Bool)) ∅ = ∅ := by
  ext u
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨s, hs, -⟩
  exact hs

/-- **Definition 35 computed at `E = ∅`**: `Irr^F(∅) = {{b} | b ∈ B}`, since `χ^F_C(∅,∅) = ∅`
for every `C`. -/
lemma irr_coordFS_empty : coordFS.irr (∅ : Set (Bool × Bool)) = {{fstFactor}, {sndFactor}} := by
  ext D
  constructor
  · rintro ⟨⟨c, hc⟩, hsub, -, hmin⟩
    rcases subset_coordFS_basis_cases hsub with rfl | rfl | rfl | rfl
    · exact absurd hc (Set.notMem_empty c)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · refine absurd (chimeraImage_empty ({fstFactor} : Set (Setoid (Bool × Bool))))
        (hmin {fstFactor} ⟨Set.singleton_subset_iff.2 fstFactor_mem, ?_⟩ ⟨fstFactor, rfl⟩)
      intro hcon
      exact fstFactor_ne_sndFactor (Set.mem_singleton_iff.1 (hcon sndFactor_mem)).symm
  · rintro (rfl | rfl)
    · exact ⟨⟨fstFactor, rfl⟩, singleton_fstFactor_subset, chimeraImage_empty _, by
        intro D hD hne
        rw [Set.ssubset_singleton_iff] at hD
        exact absurd hne (hD ▸ Set.not_nonempty_empty)⟩
    · exact ⟨⟨sndFactor, rfl⟩, singleton_sndFactor_subset, chimeraImage_empty _, by
        intro D hD hne
        rw [Set.ssubset_singleton_iff] at hD
        exact absurd hne (hD ▸ Set.not_nonempty_empty)⟩

/-- **Proposition 29's `hE` really is unused**, as its docstring discloses: all three of
its conjuncts — nonemptiness of the blocks, pairwise disjointness, and the cover — hold at
`E = ∅` on the witness, computed from `irr_coordFS_empty` rather than from the endpoint. -/
lemma irr_partition_holds_at_empty :
    (∀ C ∈ coordFS.irr (∅ : Set (Bool × Bool)), C.Nonempty) ∧
      (coordFS.irr (∅ : Set (Bool × Bool))).PairwiseDisjoint id ∧
        ⋃₀ coordFS.irr (∅ : Set (Bool × Bool)) = coordFS.B := by
  rw [irr_coordFS_empty]
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl
    · exact ⟨fstFactor, rfl⟩
    · exact ⟨sndFactor, rfl⟩
  · intro C₀ h₀ C₁ h₁ hne
    show Disjoint C₀ C₁
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h₀ h₁
    rcases h₀ with rfl | rfl <;> rcases h₁ with rfl | rfl
    · exact absurd rfl hne
    · exact Set.disjoint_singleton.2 fstFactor_ne_sndFactor
    · exact Set.disjoint_singleton.2 (Ne.symm fstFactor_ne_sndFactor)
    · exact absurd rfl hne
  · rw [Set.sUnion_insert, Set.sUnion_singleton]
    rfl

/-- **Proposition 28's `hE` is load-bearing**: at `E = ∅`, `Q^F_∅ = 0`, so *every*
polynomial divides it, while `poly^F_C(∅) = 0` for every `C` — the conclusion fails for
`p = X_{[·]₁ = true}`. -/
lemma prop28_hE_loadbearing :
    (X (vfst true) : Poly (Bool × Bool)) ∣ coordFS.Q (∅ : Set (Bool × Bool)) ∧
      ¬ ∃ (r : ℝ) (C : Set (Setoid (Bool × Bool))), C ⊆ coordFS.B ∧
        (X (vfst true) : Poly (Bool × Bool)) = MvPolynomial.C r * poly C ∅ := by
  refine ⟨⟨0, by rw [Q_coordFS_empty, mul_zero]⟩, ?_⟩
  rintro ⟨r, D, -, h⟩
  rw [poly_empty_eq_zero, mul_zero] at h
  exact X_ne_zero _ h

/-- **Proposition 31's `hE` is load-bearing**: `{fstFactor} ∈ Irr^F(∅)` but
`poly^F_{fst}(∅) = 0`, which is not irreducible. -/
lemma prop31_hE_loadbearing :
    ({fstFactor} : Set (Setoid (Bool × Bool))) ∈ coordFS.irr (∅ : Set (Bool × Bool)) ∧
      ¬ Irreducible (poly ({fstFactor} : Set (Setoid (Bool × Bool))) ∅) := by
  refine ⟨by rw [irr_coordFS_empty]; exact Or.inl rfl, ?_⟩
  rw [poly_empty_eq_zero]
  exact not_irreducible_zero

/-- **Proposition 30's `hE` is load-bearing**, on the zero-dimensional witness `unitFS`
(`B = ∅`): there `Irr^F(∅) = ∅`, so the empty product is `1`, while `Q^F_∅ = 0`. -/
lemma prop30_hE_loadbearing :
    unitFS.Q (∅ : Set Unit) ≠ ∏ᶠ C ∈ unitFS.irr (∅ : Set Unit), poly C (∅ : Set Unit) := by
  have hirr : unitFS.irr (∅ : Set Unit) = ∅ := by
    ext D
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨c, hc⟩, hsub, -, -⟩
    exact hsub hc
  rw [hirr, finprod_mem_empty, unitFS.Q_eq_finsum_mono, finsum_mem_empty]
  exact zero_ne_one

/-! ### `poly^F_C(E)` is total, so it takes junk values off the paper's `C ⊆ B`

Definition 34 is written for `C ⊆ B`, but the Lean `poly` is a total function of `C`.  The
record below is what it does at a `C` the paper never speaks about, so that nobody reads a
§5 statement as covering it: at `C = {Ind_S}` every point has the same block, `monos`
collapses to one monomial, and `poly^F_{{Ind_S}}(S)` is a *single variable* — where the
paper's `poly` for `C ⊆ B` would have `|monos^F_C(S)|` summands.  `Ind_S ∉ B`, so no
hypothesis of §5.1–§5.2 is satisfied by it and no §5 theorem applies to this value. -/

lemma part_top_eq_univ (s : Bool × Bool) :
    part (⊤ : Setoid (Bool × Bool)) s = (Set.univ : Set (Bool × Bool)) := rfl

lemma poly_top_univ_junk :
    poly ({(⊤ : Setoid (Bool × Bool))} : Set (Setoid (Bool × Bool))) Set.univ
      = (X Set.univ : Poly (Bool × Bool)) := by
  have hmonos : monos ({(⊤ : Setoid (Bool × Bool))} : Set (Setoid (Bool × Bool))) Set.univ
      = ({X (Set.univ : Set (Bool × Bool))} : Set (Poly (Bool × Bool))) := by
    ext m
    simp only [monos, Set.image_univ, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, rfl⟩
      rw [mono, finprod_mem_singleton, part_top_eq_univ]
    · rintro rfl
      exact ⟨(true, true), by rw [mono, finprod_mem_singleton, part_top_eq_univ]⟩
  rw [poly, hmonos, finsum_mem_singleton]

/-- The junk value is out of the paper's reach: `Ind_S ∉ B`, so no `C ⊆ B` hypothesis of
§5.1–§5.2 is satisfied by `{Ind_S}`. -/
lemma top_notMem_coordFS_basis : (⊤ : Setoid (Bool × Bool)) ∉ coordFS.B := by
  rintro (h | h)
  · have hr : (⊤ : Setoid (Bool × Bool)) (true, false) (false, false) := trivial
    rw [h] at hr
    exact Bool.noConfusion (hr : (true : Bool) = false)
  · have hr : (⊤ : Setoid (Bool × Bool)) (false, true) (false, false) := trivial
    rw [h] at hr
    exact Bool.noConfusion (hr : (true : Bool) = false)

/-! ## §5.3–§5.5 over `coordFS`: divisibility, distributions, and the fundamental theorem

§5.3–§5.5 add the last layer of vocabulary — the divisibility characterization of
conditional orthogonality (Lemma 3), probability distributions on a set and on a factored
set (Definitions 36–37), their characterization by evaluation (Proposition 32), and the
fundamental theorem (Theorem 3) — and none of the §2–§5.2 witnesses touch any of it.
`ProbDist` in particular is a bare structure: until something builds one, every statement
quantified over distributions is vacuously satisfiable and Theorem 3's right-hand side
says nothing.

The two *conditional* notions — Lemma 3's clauses and Theorem 3 — are organized around a
single discriminating pair of conditioning partitions, already established in §4.3 and
§5.2 on this witness: `coordFS`'s two coordinate factors are orthogonal given `Ind_S`
(`orthogonalGiven_fst_snd_top`) and entangled given `xorPart`
(`not_orthogonalGiven_fst_snd_xorPart`, via the diagonal block `Ediag`).  Each of those is
computed at *both*, and in each case the two answers differ.  The two *unconditional*
notions are not conditioned on anything, so they are separated along their own axes
instead: Proposition 32 at two subsets under two distributions, and Definitions 36–37 at
the single point `(true, true)`.

* **Lemma 3 clause 3** holds at `z = S` — `Q^F_S · Q^F_{x∩y}` and `Q^F_x · Q^F_y` are the
  same polynomial — and **fails** at `z = Ediag`, where the two products are separated by
  one evaluation (`310` against `100`).  So clause 3 is neither vacuous nor total on this
  witness, and its failure sits exactly where §4.3 says the pair is entangled.
* **Lemma 3 clause 2** — the divisibility, reachable only through the `TFAE` — runs at the
  same two conditionings: at `z = S` the cofactor is `Q^F_{(t,t)}`, and at `z = Ediag`
  divisibility fails outright, refuted by a single *zero* of the divisor (`coordZero`).
* **Definitions 36–37 are inhabited, the second is not implied by the first, and neither
  names one particular distribution.**  `uniform` — `P(E) = |E| / 4` — and `biased` — the
  product of two `1/3`-biased coins — are two *different* distributions on `coordFS`.
  `diagDist` — `P(E) = |E ∩ Ediag| / 2`, concentrated on the diagonal — is a `ProbDist` and
  **not** a distribution on `coordFS`; the separation is at the single point
  `s = (true, true)`, where `P{s} = 1/2` while `P([s]_fst) · P([s]_snd) = 1/4`.  That is
  what stops Definition 37's product condition from being decoration, and it is the same
  failure of the diagonal that §4.3 and §5.2 see combinatorially.
* **Proposition 32** is computed at two subsets and under two distributions: at `E = Efst`
  under `uniform` (two summands, equal) and under `biased` (two summands, unequal), and at
  the three-element `E3` under `biased`, where the polynomial has three terms taking two
  distinct values.  It is not conditioned on a partition, so `Ind_S`/`xorPart` is not an
  axis it can be varied along.
* **Theorem 3** applied forward at `Z = Ind_S` gives `P(x)·P(y) = P(x∩y)·P(S)`, which
  `uniform` satisfies as `1/2 · 1/2 = 1/4 · 1`; applied backward at `Z = xorPart` it turns
  `¬ (fst ⊥^F snd | xorPart)` into the *existence* of a distribution and blocks whose
  independence fails, and `thm3_coordFS_xorPart_witness` exhibits that existential
  concretely — `uniform` at `z = Ediag`, where `1/4 · 1/4 = 1/16` but
  `1/4 · 1/2 = 1/8`.  Conditional independence genuinely fails given the diagonal.

Two further groups keep the §5.4–§5.5 quantifiers honest.  The **hard directions run
forward**: Lemma 3's `3 → 1` and Theorem 3's converse are applied with their hypotheses
discharged by computation (`clause3_fst_snd_top`, then `orthogonalGiven_from_clause3` and
`orthogonalGiven_from_independence`) rather than only under a `by_contra`, so the two
directions §5.5 actually consumes are exercised in the direction a client would use them;
the three derivations of `coordFS.OrthogonalGiven fstFactor sndFactor ⊤` in this file take
three independent routes on purpose.  And the **degenerate carriers** are recorded: there
is no distribution at all over `Empty` (`isEmpty_probDist_empty`), where Theorem 3's two
sides are both vacuously true (`orthogonalGiven_emptyFS`); there is exactly one over `Unit`
and it *is* a distribution on the zero-dimensional `unitFS`; and on the one-dimensional
`boolFS` every `ProbDist Bool` is a distribution on the factored set, which is what makes
`not_orthogonalGiven_bot_bot_top_boolFS` a genuine refutation of Theorem 3's right-hand
side rather than a statement about an empty family.  The general form of the positive half
— the point mass is a distribution on *every* factored set of finite dimension — is
`isDistribution_diracAt`, in `Probability.lean` rather than here, because it is a fact
about all factored sets and not about a witness.

The cross-check discipline of §5.1–§5.2 runs here too: `lemma3_clause3_coordFS_top_crosscheck`,
`lemma3_clause2_top_crosscheck`, `prop32_coordFS_Efst_crosscheck`,
`prop32_biased_Efst_crosscheck`, `prop32_biased_E3_crosscheck`,
`thm3_coordFS_top_crosscheck` and
`thm3_coordFS_xorPart_witness` compute their claims from Definitions 31–37, while the
`*_applied` twins — which state the *same* propositions — instantiate the endpoint.  (While
the endpoints were still `sorry`d during drafting, `#print axioms` split the two groups
exactly; now that they are proved the separation is textual, as in §5.1–§5.2:
no cross-check names `orthogonalGiven_tfae`, `Q_mul_Q_eq_of_orthogonalGiven`,
`isDistribution_iff` or `orthogonalGiven_iff_forall_isDistribution`.) -/

/-! ### The blocks Lemma 3 and Theorem 3 quantify over

`Efst = {p | p.1 = true}` is a block of `fstFactor` and `vsnd true` is a block of
`sndFactor` (both are `part b s` on the nose, so `Setoid.mem_classes` applies with no
glue), `Set.univ` is the single block of `Ind_S`, and `Ediag` is a block of `xorPart`
(`Ediag_mem_xorPart_classes`, §4.3).  Their pairwise intersections all collapse to the
single point `(true, true)`, which is what makes the two verdicts computable. -/

lemma vfst_eq (a : Bool) : vfst a = ({(a, true), (a, false)} : Set (Bool × Bool)) := by
  ext ⟨x, y⟩
  constructor
  · intro h
    have hx : x = a := h
    subst hx
    cases y
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (h | h) <;> exact congrArg Prod.fst h

lemma vsnd_eq (b : Bool) : vsnd b = ({(true, b), (false, b)} : Set (Bool × Bool)) := by
  ext ⟨x, y⟩
  constructor
  · intro h
    have hy : y = b := h
    subst hy
    cases x
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (h | h) <;> exact congrArg Prod.snd h

/-- A block of `fstFactor` meets a block of `sndFactor` in exactly one point — which is
what makes the intersections Lemma 3 and Theorem 3 quantify over computable. -/
lemma vfst_inter_vsnd (a b : Bool) : vfst a ∩ vsnd b = {(a, b)} := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x = a := h1
    have hy : y = b := h2
    subst hx; subst hy; rfl
  · intro h
    have h' : (x, y) = ((a, b) : Bool × Bool) := h
    rw [h']
    exact ⟨rfl, rfl⟩

lemma Efst_inter_vsnd_true : Efst ∩ vsnd true = ({((true, true) : Bool × Bool)} : Set _) :=
  vfst_inter_vsnd true true

lemma singleton_tt_subset_Ediag :
    ({((true, true) : Bool × Bool)} : Set _) ⊆ Ediag := by
  intro p hp
  have h' : p = ((true, true) : Bool × Bool) := hp
  rw [h']
  rfl

lemma Efst_inter_Ediag : Efst ∩ Ediag = ({((true, true) : Bool × Bool)} : Set _) := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x = true := h1
    have hy : x = y := h2
    subst hx
    have hy' : true = y := hy
    subst hy'
    rfl
  · intro h
    have h' : (x, y) = ((true, true) : Bool × Bool) := h
    rw [h']
    exact ⟨rfl, rfl⟩

lemma vsnd_true_inter_Ediag : vsnd true ∩ Ediag = ({((true, true) : Bool × Bool)} : Set _) := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y = true := h1
    have hx : x = y := h2
    subst hy
    have hx' : x = true := hx
    subst hx'
    rfl
  · intro h
    have h' : (x, y) = ((true, true) : Bool × Bool) := h
    rw [h']
    exact ⟨rfl, rfl⟩

lemma Efst_inter_vsnd_true_inter_Ediag :
    Efst ∩ vsnd true ∩ Ediag = ({((true, true) : Bool × Bool)} : Set _) := by
  rw [Efst_inter_vsnd_true, Set.inter_eq_self_of_subset_left singleton_tt_subset_Ediag]

lemma Efst_mem_fstFactor_classes : Efst ∈ fstFactor.classes :=
  fstFactor.mem_classes (true, true)

lemma vsnd_true_mem_sndFactor_classes : vsnd true ∈ sndFactor.classes :=
  sndFactor.mem_classes (true, true)

lemma univ_mem_top_classes :
    (Set.univ : Set (Bool × Bool)) ∈ (⊤ : Setoid (Bool × Bool)).classes := by
  rw [classes_top ⟨(true, true)⟩]
  rfl

/-! ### Definition 31 at the two remaining blocks -/

lemma Q_coordFS_singleton (s : Bool × Bool) :
    coordFS.Q {s} = (X (vfst s.1) * X (vsnd s.2) : Poly (Bool × Bool)) := by
  rw [coordFS.Q_eq_finsum_mono, finsum_mem_singleton, mono_coordFS_basis]

/-- Definition 31 at every block of `fstFactor`. -/
lemma Q_coordFS_vfst (a : Bool) :
    coordFS.Q (vfst a)
      = (X (vfst a) * X (vsnd true) + X (vfst a) * X (vsnd false) : Poly (Bool × Bool)) := by
  rw [coordFS.Q_eq_finsum_mono]
  conv_lhs => rw [vfst_eq a]
  rw [finsum_mem_pair (show ((a, true) : Bool × Bool) ≠ (a, false) by
      intro h; exact Bool.noConfusion (congrArg Prod.snd h)),
    mono_coordFS_basis, mono_coordFS_basis]

/-- Definition 31 at every block of `sndFactor`. -/
lemma Q_coordFS_vsnd (b : Bool) :
    coordFS.Q (vsnd b)
      = (X (vfst true) * X (vsnd b) + X (vfst false) * X (vsnd b) : Poly (Bool × Bool)) := by
  rw [coordFS.Q_eq_finsum_mono]
  conv_lhs => rw [vsnd_eq b]
  rw [finsum_mem_pair (show ((true, b) : Bool × Bool) ≠ (false, b) by
      intro h; exact Bool.noConfusion (congrArg Prod.fst h)),
    mono_coordFS_basis, mono_coordFS_basis]

lemma Q_coordFS_vsnd_true :
    coordFS.Q (vsnd true)
      = (X (vfst true) * X (vsnd true) + X (vfst false) * X (vsnd true) :
          Poly (Bool × Bool)) := Q_coordFS_vsnd true

lemma Q_coordFS_Ediag :
    coordFS.Q Ediag
      = (X (vfst false) * X (vsnd false) + X (vfst true) * X (vsnd true) :
          Poly (Bool × Bool)) := by
  rw [coordFS.Q_eq_finsum_mono, Ediag_eq,
    finsum_mem_pair (show ((false, false) : Bool × Bool) ≠ (true, true) by
      intro h; exact Bool.noConfusion (congrArg Prod.fst h)),
    mono_coordFS_basis, mono_coordFS_basis]

/-! ### §5.3: Lemma 3's clause 3 holds at `Ind_S` and fails on the diagonal -/

/-- **Lemma 3 clause 3, cross-checked** at `z = S` for the blocks `x = Efst` of
`fstFactor` and `y = [·]₂ = true` of `sndFactor`: both products expand, from Definition 31
alone, to `(X_{[·]₁=t} + X_{[·]₁=f})(X_{[·]₂=t} + X_{[·]₂=f}) · X_{[·]₁=t} X_{[·]₂=t}`.
No divisibility endpoint is mentioned. -/
lemma lemma3_clause3_coordFS_top_crosscheck :
    coordFS.Q Set.univ * coordFS.Q (Efst ∩ vsnd true ∩ Set.univ)
      = coordFS.Q (Efst ∩ Set.univ) * coordFS.Q (vsnd true ∩ Set.univ) := by
  rw [Set.inter_univ, Set.inter_univ, Set.inter_univ, Efst_inter_vsnd_true,
    Q_coordFS_univ_eq, Q_coordFS_singleton, Q_coordFS_Efst_eq, Q_coordFS_vsnd_true]
  ring

/-- …and the same proposition **applied**: Lemma 3's clause 1 → clause 3 direction fed the
§4.3 fact `fstFactor ⊥^F sndFactor | Ind_S`. -/
lemma lemma3_clause3_coordFS_top_applied :
    coordFS.Q Set.univ * coordFS.Q (Efst ∩ vsnd true ∩ Set.univ)
      = coordFS.Q (Efst ∩ Set.univ) * coordFS.Q (vsnd true ∩ Set.univ) :=
  coordFS.Q_mul_Q_eq_of_orthogonalGiven orthogonalGiven_fst_snd_top
    Efst_mem_fstFactor_classes vsnd_true_mem_sndFactor_classes univ_mem_top_classes

/-- **Lemma 3 clause 3 fails on the diagonal**, which is what stops it being a triviality:
at `z = Ediag` — a block of `xorPart` — the three intersections all collapse to the point
`(true, true)`, so the left product is `(X_{[·]₁=f}X_{[·]₂=f} + X_{[·]₁=t}X_{[·]₂=t}) ·
X_{[·]₁=t}X_{[·]₂=t}` while the right is its square.  One separating evaluation
(`coordSep`) sends them to `310` and `100`.  By Lemma 3 this is the polynomial shadow of
`¬ (fstFactor ⊥^F sndFactor | xorPart)`. -/
lemma lemma3_clause3_coordFS_Ediag_fails :
    coordFS.Q Ediag * coordFS.Q (Efst ∩ vsnd true ∩ Ediag)
      ≠ coordFS.Q (Efst ∩ Ediag) * coordFS.Q (vsnd true ∩ Ediag) := by
  rw [Efst_inter_vsnd_true_inter_Ediag, Efst_inter_Ediag, vsnd_true_inter_Ediag,
    Q_coordFS_Ediag, Q_coordFS_singleton]
  intro h
  have h' := congrArg (MvPolynomial.eval coordSep) h
  simp only [map_add, map_mul, eval_X, coordSep_vfst_true, coordSep_vfst_false,
    coordSep_vsnd_true, coordSep_vsnd_false] at h'
  norm_num at h'

/-! ### §5.4: Definitions 36 and 37 inhabited, and kept apart

Definition 36 is a bare structure and Definition 37 a predicate on it, so a client's first
question is whether either is inhabited and whether the second is stronger than the first.
`uniform` answers the first and `diagDist` the second. -/

/-- **Definition 36 on the witness**: the uniform distribution on the four points of
`Bool × Bool`, `P(E) = |E| / 4`.  Additivity is `Set.ncard_union_eq`; the three constant
fields are `Set.ncard_empty` and `|Bool × Bool| = 4`. -/
noncomputable def uniform : ProbDist (Bool × Bool) where
  P E := (E.ncard : ℝ) / 4
  nonneg _ := by positivity
  empty := by rw [Set.ncard_empty]; norm_num
  univ := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    norm_num
  additive E₀ E₁ h := by
    rw [Set.ncard_union_eq h]
    push_cast
    ring

lemma uniform_apply (E : Set (Bool × Bool)) : uniform E = (E.ncard : ℝ) / 4 := rfl

lemma uniform_singleton (s : Bool × Bool) : uniform {s} = 1 / 4 := by
  rw [uniform_apply, Set.ncard_singleton]
  norm_num

lemma uniform_vfst (a : Bool) : uniform (vfst a) = 1 / 2 := by
  rw [uniform_apply, vfst_eq,
    Set.ncard_pair (show ((a, true) : Bool × Bool) ≠ (a, false) by
      intro h; exact Bool.noConfusion (congrArg Prod.snd h))]
  norm_num

lemma uniform_vsnd (b : Bool) : uniform (vsnd b) = 1 / 2 := by
  rw [uniform_apply, vsnd_eq,
    Set.ncard_pair (show ((true, b) : Bool × Bool) ≠ (false, b) by
      intro h; exact Bool.noConfusion (congrArg Prod.fst h))]
  norm_num

lemma uniform_Efst : uniform Efst = 1 / 2 := uniform_vfst true

lemma uniform_Ediag : uniform Ediag = 1 / 2 := by
  rw [uniform_apply, Ediag_eq,
    Set.ncard_pair (show ((false, false) : Bool × Bool) ≠ (true, true) by
      intro h; exact Bool.noConfusion (congrArg Prod.fst h))]
  norm_num

/-- **Definition 37 on the witness**: `uniform` is a distribution on the factored set, not
merely on the set — each factor contributes `1/2` and `1/4 = 1/2 · 1/2`.  This is the
first *computed* inhabitant of `IsDistribution`, so Proposition 32 and Theorem 3 acquire
an exhibited inhabitant to quantify over here.  (The family they quantify over is never
empty over a nonempty `S`: `isDistribution_diracAt` puts the point mass in it for every
factored set of finite dimension.  What a witness adds is a distribution whose values are
computed, and — with `biased` — a second one.) -/
lemma uniform_isDistribution : coordFS.IsDistribution uniform := by
  intro s
  rw [coordFS_basis_eq, finprod_mem_pair fstFactor_ne_sndFactor, part_fstFactor,
    part_sndFactor, uniform_vfst, uniform_vsnd, uniform_singleton]
  norm_num

/-- The distribution concentrated on the diagonal: `P(E) = |E ∩ Ediag| / 2`, so
`P{(f,f)} = P{(t,t)} = 1/2` and the two off-diagonal points have probability `0`. -/
noncomputable def diagDist : ProbDist (Bool × Bool) where
  P E := ((E ∩ Ediag).ncard : ℝ) / 2
  nonneg _ := by positivity
  empty := by rw [Set.empty_inter, Set.ncard_empty]; norm_num
  univ := by
    rw [Set.univ_inter, Ediag_eq,
      Set.ncard_pair (show ((false, false) : Bool × Bool) ≠ (true, true) by
        intro h; exact Bool.noConfusion (congrArg Prod.fst h))]
    norm_num
  additive E₀ E₁ h := by
    rw [Set.union_inter_distrib_right,
      Set.ncard_union_eq (h.mono Set.inter_subset_left Set.inter_subset_left)]
    push_cast
    ring

lemma diagDist_apply (E : Set (Bool × Bool)) : diagDist E = ((E ∩ Ediag).ncard : ℝ) / 2 := rfl

/-- **Definition 37 is strictly stronger than Definition 36.**  `diagDist` is a
probability distribution on `S` — all four fields hold — and is *not* a distribution on
`coordFS`: at `s = (true, true)` the singleton has probability `1/2` while the product
over the factors is `1/2 · 1/2 = 1/4`.  So the product condition of Definition 37 is doing
work, and the counterexample is the diagonal again: `diagDist` is exactly the distribution
under which the two coordinate factors are perfectly correlated. -/
lemma not_isDistribution_diagDist : ¬ coordFS.IsDistribution diagDist := by
  intro h
  have hs := h (true, true)
  rw [coordFS_basis_eq, finprod_mem_pair fstFactor_ne_sndFactor, part_fstFactor,
    part_sndFactor] at hs
  rw [diagDist_apply, diagDist_apply, diagDist_apply,
    Set.inter_eq_self_of_subset_left singleton_tt_subset_Ediag, Set.ncard_singleton] at hs
  rw [show vfst (true, true).1 = Efst from rfl, Efst_inter_Ediag, Set.ncard_singleton,
    show vsnd (true, true).2 = vsnd true from rfl, vsnd_true_inter_Ediag,
    Set.ncard_singleton] at hs
  norm_num at hs

/-! ### §5.4: Proposition 32 at a subset where the two sides are not the same expression -/

/-- **Proposition 32, cross-checked** at `E = Efst`: the polynomial `Q^F_{Efst}` evaluated
at `uniform` is `1/2 · 1/2 + 1/2 · 1/2`, and `uniform(Efst)` is `2/4` — computed from
Definitions 31 and 36, mentioning no characterization endpoint.  `Efst` is chosen because
`Q^F_{Efst}` has two terms while `Efst` has two points, so the evaluation is a genuine sum
rather than a restatement. -/
lemma prop32_coordFS_Efst_crosscheck :
    uniform Efst = eval uniform.P (coordFS.Q Efst) := by
  rw [Q_coordFS_Efst_eq]
  simp only [map_add, map_mul, eval_X]
  rw [show uniform.P (vfst true) = 1 / 2 from uniform_vfst true,
    show uniform.P (vsnd true) = 1 / 2 from uniform_vsnd true,
    show uniform.P (vsnd false) = 1 / 2 from uniform_vsnd false, uniform_Efst]
  norm_num

/-- …and the same proposition **applied**: Proposition 32's forward direction at
`uniform`. -/
lemma prop32_coordFS_Efst_applied :
    uniform Efst = eval uniform.P (coordFS.Q Efst) :=
  (coordFS.isDistribution_iff uniform).1 uniform_isDistribution Efst

/-! ### §5.5: the fundamental theorem, both directions, on the discriminating pair -/

/-- **Theorem 3's right-hand side, cross-checked** at `Z = Ind_S`: under `uniform` the two
coordinate factors are independent, `1/2 · 1/2 = 1/4 · 1`, computed from Definition 36. -/
lemma thm3_coordFS_top_crosscheck :
    uniform (Efst ∩ Set.univ) * uniform (vsnd true ∩ Set.univ)
      = uniform (Efst ∩ vsnd true ∩ Set.univ) * uniform Set.univ := by
  rw [Set.inter_univ, Set.inter_univ, Set.inter_univ, Efst_inter_vsnd_true,
    uniform_Efst, uniform_vsnd, uniform_singleton, uniform.univ]
  norm_num

/-- …and the same proposition **applied**: Theorem 3's forward direction turns the §4.3
combinatorial fact `fstFactor ⊥^F sndFactor | Ind_S` into that numerical independence,
with no computation of `uniform` at all. -/
lemma thm3_coordFS_top_applied :
    uniform (Efst ∩ Set.univ) * uniform (vsnd true ∩ Set.univ)
      = uniform (Efst ∩ vsnd true ∩ Set.univ) * uniform Set.univ :=
  (coordFS.orthogonalGiven_iff_forall_isDistribution fstFactor sndFactor ⊤).1
    orthogonalGiven_fst_snd_top uniform uniform_isDistribution
    Efst Efst_mem_fstFactor_classes (vsnd true) vsnd_true_mem_sndFactor_classes
    Set.univ univ_mem_top_classes

/-- **Conditional independence fails given the diagonal.**  Conditioning `uniform` on
`Ediag`: `P(x ∩ z) = P(y ∩ z) = P(x ∩ y ∩ z) = 1/4` and `P(z) = 1/2`, so the left side is
`1/16` and the right is `1/8`.  This is the numerical form of the entanglement §4.3 sees
combinatorially and §5.3 sees in the polynomials. -/
lemma thm3_coordFS_Ediag_fails :
    uniform (Efst ∩ Ediag) * uniform (vsnd true ∩ Ediag)
      ≠ uniform (Efst ∩ vsnd true ∩ Ediag) * uniform Ediag := by
  rw [Efst_inter_Ediag, vsnd_true_inter_Ediag, Efst_inter_vsnd_true_inter_Ediag,
    uniform_singleton, uniform_Ediag]
  norm_num

/-- **The existential Theorem 3's hard direction promises, exhibited.**  Since
`¬ (fstFactor ⊥^F sndFactor | xorPart)`, the theorem says *some* distribution on `coordFS`
and *some* blocks break independence; this names them — `uniform`, the blocks `Efst`,
`[·]₂ = true`, and the `xorPart` block `Ediag` — without invoking the theorem. -/
lemma thm3_coordFS_xorPart_witness :
    ∃ P : ProbDist (Bool × Bool), coordFS.IsDistribution P ∧
      ∃ x ∈ fstFactor.classes, ∃ y ∈ sndFactor.classes, ∃ z ∈ xorPart.classes,
        P (x ∩ z) * P (y ∩ z) ≠ P (x ∩ y ∩ z) * P z :=
  ⟨uniform, uniform_isDistribution, Efst, Efst_mem_fstFactor_classes,
    vsnd true, vsnd_true_mem_sndFactor_classes, Ediag, Ediag_mem_xorPart_classes,
    thm3_coordFS_Ediag_fails⟩

/-- …and the same proposition **applied**: Theorem 3's *backward* direction, contraposed
against `not_orthogonalGiven_fst_snd_xorPart`, produces that existential from the §4.3
fact alone.  This is the direction the paper's "vanishes on an open set" argument proves,
and it is the one that makes conditional orthogonality *testable*. -/
lemma thm3_coordFS_xorPart_applied :
    ∃ P : ProbDist (Bool × Bool), coordFS.IsDistribution P ∧
      ∃ x ∈ fstFactor.classes, ∃ y ∈ sndFactor.classes, ∃ z ∈ xorPart.classes,
        P (x ∩ z) * P (y ∩ z) ≠ P (x ∩ y ∩ z) * P z := by
  by_contra hcon
  push Not at hcon
  exact not_orthogonalGiven_fst_snd_xorPart
    ((coordFS.orthogonalGiven_iff_forall_isDistribution fstFactor sndFactor xorPart).2
      fun P hP x hx y hy z hz => hcon P hP x hx y hy z hz)

/-! ### §5.3: Lemma 3's clause 2 — divisibility — at `Ind_S`, and its failure on the diagonal

Clause 3 above is the equational form.  Clause 2, the *divisibility* `Q^F_z ∣ Q^F_{x∩z} ·
Q^F_{y∩z}`, is reachable only through the `TFAE`, so nothing exercised it; these two do.
The cross-check exhibits the cofactor — `Q^F_{(t,t)}`, computed from Definition 31 — and
the application projects Lemma 3's `1 → 2` leg, both stating the same divisibility. -/

/-- **Lemma 3 clause 2, cross-checked** at `z = S`: the cofactor is `Q^F_{(t,t)}`, and the
identity `Q^F_{Efst} · Q^F_{[·]₂=t} = Q^F_S · Q^F_{(t,t)}` expands from Definition 31
alone.  No divisibility endpoint is mentioned. -/
lemma lemma3_clause2_top_crosscheck :
    coordFS.Q (Set.univ : Set (Bool × Bool)) ∣
      coordFS.Q (Efst ∩ Set.univ) * coordFS.Q (vsnd true ∩ Set.univ) :=
  ⟨coordFS.Q ({((true, true) : Bool × Bool)} : Set (Bool × Bool)), by
    rw [Set.inter_univ, Set.inter_univ, Q_coordFS_univ_eq, Q_coordFS_singleton,
      Q_coordFS_Efst_eq, Q_coordFS_vsnd true]
    ring⟩

/-- …and the same proposition **applied**: clause 2 of Lemma 3's `TFAE`, projected with
`.out 0 1` and fed the §4.3 fact `fstFactor ⊥^F sndFactor | Ind_S`.  Projecting the clause
needs the typed `have` that `List.TFAE.out` forces in term position. -/
lemma lemma3_clause2_top_applied :
    coordFS.Q (Set.univ : Set (Bool × Bool)) ∣
      coordFS.Q (Efst ∩ Set.univ) * coordFS.Q (vsnd true ∩ Set.univ) := by
  have h2 : ∀ x ∈ fstFactor.classes, ∀ y ∈ sndFactor.classes,
      ∀ z ∈ (⊤ : Setoid (Bool × Bool)).classes,
      coordFS.Q z ∣ coordFS.Q (x ∩ z) * coordFS.Q (y ∩ z) :=
    ((coordFS.orthogonalGiven_tfae fstFactor sndFactor ⊤).out 0 1).1 orthogonalGiven_fst_snd_top
  exact h2 Efst Efst_mem_fstFactor_classes (vsnd true) vsnd_true_mem_sndFactor_classes
    Set.univ univ_mem_top_classes

/-- The assignment sending the block `[·]₂ = false` to `-1` and every other block to `1`.
It is a zero of `Q^F_{Ediag}` and not of `Q^F_{(t,t)}`, which is what refutes divisibility
outright — a separating *zero* rather than the separating value `coordSep` supplies for the
equational clause. -/
noncomputable def coordZero : Set (Bool × Bool) → ℝ := fun v => if v = vsnd false then -1 else 1

lemma coordZero_vsnd_false : coordZero (vsnd false) = -1 := if_pos rfl
lemma coordZero_vsnd_true : coordZero (vsnd true) = 1 := if_neg vsnd_true_ne_false
lemma coordZero_vfst_true : coordZero (vfst true) = 1 := if_neg (vfst_ne_vsnd true false)
lemma coordZero_vfst_false : coordZero (vfst false) = 1 := if_neg (vfst_ne_vsnd false false)

/-- **Lemma 3 clause 2 fails on the diagonal**, so clause 2 is no more total than clause 3
is: at `z = Ediag` the divisor is `X_{[·]₁=f}X_{[·]₂=f} + X_{[·]₁=t}X_{[·]₂=t}`, which
`coordZero` sends to `0`, while the dividend `(X_{[·]₁=t}X_{[·]₂=t})²` goes to `1`. -/
lemma lemma3_clause2_Ediag_fails :
    ¬ (coordFS.Q Ediag ∣ coordFS.Q (Efst ∩ Ediag) * coordFS.Q (vsnd true ∩ Ediag)) := by
  rw [Efst_inter_Ediag, vsnd_true_inter_Ediag]
  rintro ⟨q, hq⟩
  have h' := congrArg (MvPolynomial.eval coordZero) hq
  rw [Q_coordFS_Ediag, Q_coordFS_singleton] at h'
  simp only [map_add, map_mul, eval_X, coordZero_vfst_true, coordZero_vfst_false,
    coordZero_vsnd_true, coordZero_vsnd_false] at h'
  norm_num at h'

/-! ### §5.3: Lemma 3's `3 → 1` direction, run forward

`lemma3_clause3_coordFS_top_applied` above runs Lemma 3 in the easy direction, from an
orthogonality certificate to a polynomial identity.  The direction the fundamental theorem
consumes is the other one, and everything above reaches it only under a `by_contra`.  Here
its hypothesis is discharged outright: clause 3 is proved for *all* blocks by computation,
and `orthogonalGiven_of_Q_mul_Q_eq` turns it into conditional orthogonality.

`orthogonalGiven_from_clause3` therefore reproves `orthogonalGiven_fst_snd_top` by a
different route — that is the point, not duplication: the first goes through Proposition
24 and §3's combinatorics, this one through §5's polynomials, and
`orthogonalGiven_from_independence` below through Theorem 3's converse.  Three independent
derivations of one fact are three exercised endpoints. -/

/-- Lemma 3's clause 3 at `Z = Ind_S`, for *every* pair of blocks: the four cases of
`(s.1, t.2)` all reduce to the same polynomial identity, since a block of `fstFactor` meets
a block of `sndFactor` in a single point. -/
lemma clause3_fst_snd_top :
    ∀ x ∈ fstFactor.classes, ∀ y ∈ sndFactor.classes,
      ∀ z ∈ (⊤ : Setoid (Bool × Bool)).classes,
        coordFS.Q z * coordFS.Q (x ∩ y ∩ z)
          = coordFS.Q (x ∩ z) * coordFS.Q (y ∩ z) := by
  rintro x ⟨s, rfl⟩ y ⟨t, rfl⟩ z hz
  rw [classes_top ⟨(true, true)⟩] at hz
  have hz' : z = Set.univ := hz
  subst hz'
  rw [Set.inter_univ, Set.inter_univ, Set.inter_univ]
  show coordFS.Q Set.univ * coordFS.Q (vfst s.1 ∩ vsnd t.2)
    = coordFS.Q (vfst s.1) * coordFS.Q (vsnd t.2)
  rw [vfst_inter_vsnd, Q_coordFS_univ_eq, Q_coordFS_singleton, Q_coordFS_vfst, Q_coordFS_vsnd]
  cases s.1 <;> cases t.2 <;> ring

/-- **Lemma 3's `3 → 1` direction with its hypothesis genuinely discharged.** -/
lemma orthogonalGiven_from_clause3 : coordFS.OrthogonalGiven fstFactor sndFactor ⊤ :=
  coordFS.orthogonalGiven_of_Q_mul_Q_eq clause3_fst_snd_top

/-! ### §5.4: a second distribution on `coordFS`, and Definition 37 at three-in-four points

`uniform` is the only inhabitant of Definition 37 built so far, and it is symmetric in
every argument, so a client could reasonably suspect Definition 37 of naming *the* uniform
distribution.  `biased` — the product of two independent coins with `P(true) = 1/3` — is a
distribution on `coordFS` too, and differs from `uniform` already at a singleton.  It also
gives Proposition 32 a test at a subset where neither side is symmetric: `E3` has three of
the four points, so `Q^F_{E3}` has three terms with three different values. -/

/-- The point weights of the biased product: `1/3` for a `true` coordinate, `2/3` for a
`false` one. -/
noncomputable def w : Bool × Bool → ℝ :=
  fun s => (if s.1 = true then (1:ℝ)/3 else 2/3) * (if s.2 = true then (1:ℝ)/3 else 2/3)

lemma w_nonneg (s : Bool × Bool) : 0 ≤ w s := by
  unfold w; split <;> split <;> norm_num

/-- **A second inhabitant of Definition 36 on the witness**: the product of two
independent `1/3`-biased coins, `P(E) = ∑_{s ∈ E} w(s)`.  Additivity is the pointwise
case split on which of the two disjoint sets contains `s`. -/
noncomputable def biased : ProbDist (Bool × Bool) where
  P E := ∑ s : Bool × Bool, if s ∈ E then w s else 0
  nonneg E := Finset.sum_nonneg fun s _ => by split <;> simp [w_nonneg s]
  empty := by simp
  univ := by
    simp only [Set.mem_univ, if_true]
    unfold w
    rw [Fintype.sum_prod_type]
    simp
    norm_num
  additive E₀ E₁ hd := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h0 : s ∈ E₀
    · have h1 : s ∉ E₁ := fun h => Set.disjoint_left.1 hd h0 h
      simp [h0, h1, Set.mem_union]
    · by_cases h1 : s ∈ E₁ <;> simp [h0, h1, Set.mem_union]

lemma biased_apply (E : Set (Bool × Bool)) :
    biased E = ∑ s : Bool × Bool, if s ∈ E then w s else 0 := rfl

lemma biased_singleton (s : Bool × Bool) : biased {s} = w s := by
  rw [biased_apply]; simp

lemma biased_vfst (a : Bool) : biased (vfst a) = if a = true then (1:ℝ)/3 else 2/3 := by
  rw [biased_apply]
  simp only [vfst, Set.mem_setOf_eq, w]
  rw [Fintype.sum_prod_type]
  cases a <;> simp <;> norm_num

lemma biased_vsnd (b : Bool) : biased (vsnd b) = if b = true then (1:ℝ)/3 else 2/3 := by
  rw [biased_apply]
  simp only [vsnd, Set.mem_setOf_eq, w]
  rw [Fintype.sum_prod_type]
  cases b <;> simp <;> norm_num

/-- **Definition 37 is not "the uniform distribution".**  The biased product satisfies the
factoring condition just as `uniform` does — each coordinate contributes its own marginal
and the singleton is their product. -/
lemma biased_isDistribution : coordFS.IsDistribution biased := by
  intro s
  rw [coordFS_basis_eq, finprod_mem_pair fstFactor_ne_sndFactor, part_fstFactor,
    part_sndFactor, biased_vfst, biased_vsnd, biased_singleton]
  rfl

/-- …and it is a genuinely different distribution: `1/9` against `1/4` at `(t,t)`.  So the
family Theorem 3 quantifies over has at least two members on this witness, and a proof that
holds for `uniform` alone would not do. -/
lemma biased_ne_uniform : biased ≠ uniform := by
  intro h
  have h1 : biased {((true, true) : Bool × Bool)} = uniform {((true, true) : Bool × Bool)} :=
    congrFun (congrArg ProbDist.P h) _
  rw [biased_singleton, uniform_singleton] at h1
  unfold w at h1
  norm_num at h1

lemma biased_Efst : biased Efst = 1 / 3 := by
  rw [show Efst = vfst true from rfl, biased_vfst]
  norm_num

lemma eval_biased_Q_Efst : eval biased.P (coordFS.Q Efst) = 1 / 3 := by
  rw [Q_coordFS_Efst_eq]
  simp only [map_add, map_mul, eval_X]
  rw [show biased.P (vfst true) = 1 / 3 from biased_vfst true,
    show biased.P (vsnd true) = 1 / 3 from biased_vsnd true,
    show biased.P (vsnd false) = 2 / 3 from biased_vsnd false]
  norm_num

/-- **Proposition 32, cross-checked under `biased`** at `E = Efst`: `1/3` on both sides,
each computed on its own — the left from Definition 36, the right by evaluating
Definition 31's polynomial at the two unequal marginals `1/3` and `2/3`.  Under `uniform`
this evaluation is `1/2·1/2 + 1/2·1/2`, where the two summands coincide; here they do
not. -/
lemma prop32_biased_Efst_crosscheck : biased Efst = eval biased.P (coordFS.Q Efst) :=
  biased_Efst.trans eval_biased_Q_Efst.symm

/-- …and the same proposition **applied**, at the second distribution. -/
lemma prop32_biased_Efst_applied : biased Efst = eval biased.P (coordFS.Q Efst) :=
  (coordFS.isDistribution_iff biased).1 biased_isDistribution Efst

/-- Three of the four points — a subset that is neither a block, nor a union of blocks of
one factor, nor closed under the chimera. -/
def E3 : Set (Bool × Bool) := {(true, true), (true, false), (false, true)}

lemma E3_coe : E3 = (({(true, true), (true, false), (false, true)} : Finset (Bool × Bool)) :
    Set (Bool × Bool)) := by simp [E3]

/-- Definition 31 at `E3`: three of the four monomials of `Q^F_S`. -/
lemma Q_coordFS_E3 :
    coordFS.Q E3 = (X (vfst true) * X (vsnd true) + X (vfst true) * X (vsnd false)
      + X (vfst false) * X (vsnd true) : Poly (Bool × Bool)) := by
  rw [coordFS.Q_eq_finsum_mono]
  conv_lhs => rw [E3_coe]
  rw [finsum_mem_coe_finset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, mono_coordFS_basis, mono_coordFS_basis, mono_coordFS_basis]
  ring

lemma biased_E3 : biased E3 = 5 / 9 := by
  rw [biased_apply]
  simp only [E3, w]
  rw [Fintype.sum_prod_type]
  norm_num

lemma eval_biased_Q_E3 : eval biased.P (coordFS.Q E3) = 5 / 9 := by
  rw [Q_coordFS_E3]
  simp only [map_add, map_mul, eval_X]
  rw [show biased.P (vfst true) = 1 / 3 from biased_vfst true,
    show biased.P (vfst false) = 2 / 3 from biased_vfst false,
    show biased.P (vsnd true) = 1 / 3 from biased_vsnd true,
    show biased.P (vsnd false) = 2 / 3 from biased_vsnd false]
  norm_num

/-- **Proposition 32, cross-checked** at a three-element set: `biased(E3) = 1/9 + 2/9 +
2/9 = 5/9` from Definition 36, and the three-term `Q^F_{E3}` evaluates to `1/9 + 2/9 + 2/9`
from Definition 31 — three summands with two distinct values, so neither side collapses. -/
lemma prop32_biased_E3_crosscheck : biased E3 = eval biased.P (coordFS.Q E3) :=
  biased_E3.trans eval_biased_Q_E3.symm

/-- …and the same proposition **applied** at that set. -/
lemma prop32_biased_E3_applied : biased E3 = eval biased.P (coordFS.Q E3) :=
  (coordFS.isDistribution_iff biased).1 biased_isDistribution E3

/-! ### §5.4: the two degenerate carriers — `ProbDist` over `Empty` and over `Unit`

Definition 36 is not inhabited over every `S`, and where it is not, Theorem 3's right-hand
side is vacuously true — so the honest statement about the empty case is that *both* sides
of the theorem hold there, not that the theorem says something.  Over `Unit` the opposite
degeneracy appears: there is exactly one distribution, and it is a distribution on the
zero-dimensional `unitFS` (the empty product is `1`).  Between them these bracket the
general fact proved in `Probability.lean`: over a nonempty `S` the point mass is a
distribution on *every* factored set of finite dimension. -/

/-- **`ProbDist` is uninhabited over an empty type**: `P(S) = 1` and `P(∅) = 0` collide,
since `S = ∅`. -/
lemma isEmpty_probDist_empty : IsEmpty (ProbDist Empty) := by
  constructor
  intro P
  have h1 : P.P Set.univ = 1 := P.univ
  have h2 : P.P (∅ : Set Empty) = 0 := P.empty
  have huniv : (Set.univ : Set Empty) = ∅ := Set.eq_empty_of_isEmpty _
  rw [huniv, h2] at h1
  norm_num at h1

/-- …so Theorem 3's right-hand side is vacuous over `emptyFS` — and its left-hand side
holds too, since a partition of `∅` has no blocks.  The theorem is *consistent* there, not
informative, and this is the declaration that says which. -/
lemma orthogonalGiven_emptyFS (X Y Z : Setoid Empty) : emptyFS.OrthogonalGiven X Y Z := by
  intro z hz
  exact absurd hz (Set.eq_empty_of_isEmpty z ▸ Setoid.empty_notMem_classes)

/-- The unique distribution on `Unit`: `1` on the whole space, `0` on `∅`. -/
noncomputable def unitDist : ProbDist Unit where
  P E := if E = ∅ then 0 else 1
  nonneg E := by split <;> norm_num
  empty := if_pos rfl
  univ := if_neg (by intro h; exact absurd (h ▸ Set.mem_univ ()) (by simp))
  additive E₀ E₁ hd := by
    rcases eq_or_ne E₀ ∅ with rfl | h0
    · simp
    · rcases eq_or_ne E₁ ∅ with rfl | h1
      · simp
      · exfalso
        obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 h0
        obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.2 h1
        exact Set.disjoint_left.1 hd ha (by cases a; cases b; exact hb)

/-- **`ProbDist Unit` is a singleton**: `Unit` has exactly two subsets, and Definition 36
pins the value at each.  So over a one-point `S` "for every distribution `P`" is a
quantification over one object. -/
lemma subsingleton_probDist_unit : Subsingleton (ProbDist Unit) := by
  constructor
  rintro ⟨P, -, hp0, hp1, -⟩ ⟨Q, -, hq0, hq1, -⟩
  have hPQ : P = Q := by
    funext E
    rcases eq_or_ne E ∅ with rfl | h
    · rw [hp0, hq0]
    · have hE : E = Set.univ := by
        ext u; cases u
        obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 h
        cases a
        simp [ha]
      rw [hE, hp1, hq1]
  subst hPQ
  rfl

/-- …and that one distribution *is* a distribution on the zero-dimensional `unitFS`: with
`B = ∅` Definition 37's product is the empty product `1`, which is `P{()}`.  So
Proposition 32 and Theorem 3 are non-vacuous at dimension `0` as well. -/
lemma unitDist_isDistribution : unitFS.IsDistribution unitDist := by
  intro s
  rw [show unitFS.B = (∅ : Set (Setoid Unit)) from rfl, finprod_mem_empty]
  cases s
  rw [show ({()} : Set Unit) = Set.univ from by ext u; cases u; simp]
  exact unitDist.univ

/-! ### §5.5: Theorem 3's converse run forward, and a one-dimensional discriminator

`thm3_coordFS_xorPart_applied` uses Theorem 3's converse contrapositively, under a
`by_contra`; nothing runs it forward with its hypothesis discharged.
`orthogonalGiven_from_independence` does, deriving conditional orthogonality from
independence in *every* distribution — the hypothesis being obtained from
`clause3_fst_snd_top` through Proposition 32, so the argument never invokes Lemma 3 or
Theorem 3's forward direction.

The last pair rules out the remaining way Theorem 3 could be trivial: that its right-hand
side might hold for every triple of partitions.  On the one-dimensional `boolFS` every
`ProbDist Bool` is a distribution on the factored set, and the uniform one separates
`{true}` from `{false}` given `Ind_S`. -/

/-- **Theorem 3's converse with its hypothesis genuinely discharged.**  A third,
independent route to `coordFS.OrthogonalGiven fstFactor sndFactor ⊤` — the first is
Proposition 24 (`orthogonalGiven_fst_snd_top`), the second Lemma 3's `3 → 1`
(`orthogonalGiven_from_clause3`), and this one the fundamental theorem itself. -/
lemma orthogonalGiven_from_independence : coordFS.OrthogonalGiven fstFactor sndFactor ⊤ := by
  refine (coordFS.orthogonalGiven_iff_forall_isDistribution fstFactor sndFactor ⊤).2 ?_
  intro P hP x hx y hy z hz
  have hE := (coordFS.isDistribution_iff P).1 hP
  rw [hE (x ∩ z), hE (y ∩ z), hE (x ∩ y ∩ z), hE z]
  have hcong := congrArg (eval P.P) (clause3_fst_snd_top x hx y hy z hz)
  rw [map_mul, map_mul] at hcong
  rw [mul_comm (eval P.P (coordFS.Q (x ∩ y ∩ z)))]
  exact hcong.symm

/-- The uniform distribution on `Bool`, `P(E) = |E| / 2` written as a sum of point
weights. -/
noncomputable def boolUniform : ProbDist Bool where
  P E := ∑ s : Bool, if s ∈ E then (1:ℝ)/2 else 0
  nonneg E := Finset.sum_nonneg fun s _ => by split <;> norm_num
  empty := by simp
  univ := by simp
  additive E₀ E₁ hd := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h0 : s ∈ E₀
    · have h1 : s ∉ E₁ := fun h => Set.disjoint_left.1 hd h0 h
      simp [h0, h1, Set.mem_union]
    · by_cases h1 : s ∈ E₁ <;> simp [h0, h1, Set.mem_union]

/-- At dimension `1` Definition 37 is no constraint at all: with `B = {Dis_S}` the product
over the factors is the singleton probability itself, so *every* `ProbDist Bool` is a
distribution on `boolFS`. -/
lemma boolFS_isDistribution (P : ProbDist Bool) : boolFS.IsDistribution P := by
  intro s
  rw [show boolFS.B = ({(⊥ : Setoid Bool)} : Set (Setoid Bool)) from rfl, finprod_mem_singleton,
    show part (⊥ : Setoid Bool) s = {s} from rfl]

/-- **Theorem 3's right-hand side is not universally true**, and one dimension suffices to
see it: `Dis_S` is not orthogonal to itself given `Ind_S` on `boolFS`, because
`boolUniform` gives `1/2 · 1/2` on the left and `0 · 1` on the right at the blocks
`{true}`, `{false}`.  Without this, "for every distribution `P` …" could be suspected of
being satisfiable by every triple. -/
lemma not_orthogonalGiven_bot_bot_top_boolFS :
    ¬ boolFS.OrthogonalGiven ⊥ ⊥ (⊤ : Setoid Bool) := by
  intro h
  have key := (boolFS.orthogonalGiven_iff_forall_isDistribution ⊥ ⊥ ⊤).1 h
    boolUniform (boolFS_isDistribution boolUniform)
    {true} ⟨true, rfl⟩ {false} ⟨false, rfl⟩ Set.univ (by rw [classes_top ⟨true⟩]; rfl)
  rw [Set.inter_univ, Set.inter_univ, Set.inter_univ] at key
  rw [show ({true} ∩ {false} : Set Bool) = ∅ by
      ext b; cases b <;> simp, boolUniform.empty, boolUniform.univ] at key
  rw [show boolUniform {true} = 1 / 2 from by simp [boolUniform], zero_mul] at key
  rw [show boolUniform {false} = 1 / 2 from by simp [boolUniform]] at key
  norm_num at key

/-! ## §6.1 over the witnesses: models, orthogonality databases, and inferred time

Definitions 42–45 quantify over **models** of a sample space rather than over factored
sets, so this is a family none of the §2–§5 witnesses inhabits.  What follows builds four
models and four databases, and uses them to separate `Consistent`, `Complete` and `<_D`
from each other.

Two readings are ruled out along the way, because both are natural and both are wrong.
The first is that a rich `O` makes a database hard to satisfy: it does not — a database
asserting *every* triple orthogonal is consistent, because a one-point model satisfies all
of them at once.  The second is that `X <_D Y` is a substantive claim whatever `D` is: on
an inconsistent `D` it is vacuously true of every pair, since it quantifies over models
that do not exist.

The informative positive instances of Definition 45 are Propositions 34 and 36 in
`InferenceExamples.lean`; nothing here is a stand-in for them, and this file deliberately
does not import that one, so that no witness below can lean on a §6.2 proof. -/

/-! ### Definition 38: four models, and Definition 39 computed on them -/

/-- The identity model of `Bool × Bool`: the coordinate factored set with `f = id`.  This
is the shape the paper's own Example 1 model has — a factorization of `Ω` itself, with no
latent structure. -/
def coordModel : Model (Bool × Bool) := ⟨coordFS, id⟩

/-- The identity model of `Bool`, on the one-dimensional `boolFS`. -/
def boolModel : Model Bool := ⟨boolFS, id⟩

/-- Under an identity model Definition 39's `f⁻¹(X)` is `X` itself. -/
lemma pullback_coordModel (X : Setoid (Bool × Bool)) : coordModel.pullback X = X :=
  Setoid.ext fun _ _ => Iff.rfl

lemma pullback_boolModel (X : Setoid Bool) : boolModel.pullback X = X :=
  Setoid.ext fun _ _ => Iff.rfl

/-- A model whose map is **not** a bijection: `coordFS` over the sample space `Bool`, with
`f = Prod.fst`.  This is the case Definition 38 exists for — `S` has four points where `Ω`
has two, so the model carries latent structure that `Ω` does not distinguish. -/
def fstModel : Model Bool := ⟨coordFS, Prod.fst⟩

/-- **Definition 39 on a non-identity model.**  The pullback of `Dis_Ω` — the *finest*
partition of the sample space — is the first coordinate *factor* of `S`, not `Dis_S`.  So
`f⁻¹` genuinely coarsens, which is what makes Definitions 42 and 45 statements about `S`
rather than about `Ω`. -/
lemma pullback_fstModel_bot : fstModel.pullback ⊥ = fstFactor := rfl

/-- …and the partition it lands on is one whose §3 history is already computed here: a
singleton, so `f⁻¹(Dis_Ω)` is generated by a single factor of `S`. -/
lemma history_pullback_fstModel_bot :
    fstModel.F.history (fstModel.pullback ⊥) = {fstFactor} := history_fstFactor

/-- The **one-point model** of `Bool × Bool`: the zero-dimensional `unitFS` with the
constant map.  Definition 38 asks nothing of `f` beyond being a function, so this is a
legal model of every sample space — which is what makes Definition 43 cheap on `O` alone
(`totalDB_consistent` below). -/
def pointModel : Model (Bool × Bool) := ⟨unitFS, fun _ => (true, true)⟩

/-- **Definition 39 collapses** under the one-point model: every partition of `Ω`, however
fine, pulls back to `Ind_S`.  Together with `pullback_fstModel_bot` this pins `f⁻¹` between
its two extremes on concrete models. -/
lemma pullback_pointModel (X : Setoid (Bool × Bool)) : pointModel.pullback X = ⊤ :=
  Setoid.ext fun a b => by
    cases a; cases b; exact ⟨fun _ => trivial, fun _ => X.refl' _⟩

/-- With `B = ∅` every Definition 24 history is a subset of `∅`. -/
lemma historySub_unitFS (X : Subpartition Unit) : unitFS.historySub X = ∅ :=
  Set.subset_empty_iff.1 (unitFS.historySub_subset X)

/-- …so on the zero-dimensional `unitFS` *every* triple is conditionally orthogonal.  This
is the fact that makes a one-point model satisfy an arbitrary `O`. -/
lemma orthogonalGiven_unitFS (X Y Z : Setoid Unit) : unitFS.OrthogonalGiven X Y Z := by
  intro z _
  rw [unitFS.orthogonalGivenSet_def, historySub_unitFS, Set.empty_inter]

/-! ### Definitions 40–44: four databases, and what `Consistent` and `Complete` each cost -/

/-- The **empty** database on `Bool × Bool`: it asserts nothing at all. -/
def emptyDB : OrthDatabase (Bool × Bool) := ⟨∅, ∅⟩

/-- Definition 42 is vacuous at the empty database, so *every* model models it. -/
lemma models_emptyDB (M : Model (Bool × Bool)) : OrthDatabase.Models M emptyDB := by
  intro X Y Z
  constructor <;> intro h <;>
    simp only [OrthDatabase.Orth, OrthDatabase.NotOrth, emptyDB, Set.mem_empty_iff_false] at h

/-- Definition 43 therefore holds of it, witnessed by the identity model. -/
lemma emptyDB_consistent : emptyDB.Consistent := ⟨coordModel, models_emptyDB _⟩

/-- Definition 44 does **not**: nothing is asserted about `(Ind_Ω, Ind_Ω, Ind_Ω)`.  So
`Consistent` and `Complete` are independent conditions, and a database can be the first
without being the second. -/
lemma not_emptyDB_complete : ¬ emptyDB.Complete := by
  intro h
  rcases h ⊤ ⊤ ⊤ with h | h <;>
    simp only [OrthDatabase.Orth, OrthDatabase.NotOrth, emptyDB, Set.mem_empty_iff_false] at h

/-- A database asserting **one triple both ways**.  Definition 42's two clauses then
contradict each other on that triple. -/
def contradictoryDB : OrthDatabase (Bool × Bool) :=
  ⟨{(fstFactor, fstFactor, ⊤)}, {(fstFactor, fstFactor, ⊤)}⟩

/-- **Definition 43 is not automatic**: `contradictoryDB` has no model at all, so the
existential in Definition 43 is a real condition rather than a formality. -/
lemma not_contradictoryDB_consistent : ¬ contradictoryDB.Consistent := by
  rintro ⟨M, hM⟩
  exact (hM fstFactor fstFactor ⊤).2 rfl ((hM fstFactor fstFactor ⊤).1 rfl)

/-- The **totally asserting** database: `O` is everything, `N` is empty. -/
def totalDB : OrthDatabase (Bool × Bool) := ⟨Set.univ, ∅⟩

/-- It is `Complete` by construction… -/
lemma totalDB_complete : totalDB.Complete := fun _ _ _ => Or.inl (Set.mem_univ _)

/-- …and, against first appearances, `Consistent`: the one-point model satisfies **every**
orthogonality assertion simultaneously, because `unitFS` has no factors.  So a rich `O`
never rules a database out — it is `N` that carries the content of Definition 43, which
`nonconstDB_forces_nonconstant` exhibits in its simplest form.  Note also that this
database is both consistent and complete, so those two conditions are not in tension
either. -/
lemma totalDB_consistent : totalDB.Consistent := by
  refine ⟨pointModel, fun X Y Z => ⟨fun _ => orthogonalGiven_unitFS _ _ _, fun h => ?_⟩⟩
  simp only [OrthDatabase.NotOrth, totalDB, Set.mem_empty_iff_false] at h

/-- A database whose whole content sits in `N`: it asserts that `Dis_Ω` is **not**
orthogonal to itself given `Ind_Ω`. -/
def nonconstDB : OrthDatabase Bool := ⟨∅, {(⊥, ⊥, ⊤)}⟩

/-- It is consistent, witnessed by the identity model of the one-dimensional `boolFS` —
where the assertion is exactly the §5.5 computation `not_orthogonalGiven_bot_bot_top_boolFS`
already made on this file's own witnesses. -/
lemma nonconstDB_consistent : nonconstDB.Consistent := by
  refine ⟨boolModel, fun X Y Z => ⟨fun h => ?_, fun h => ?_⟩⟩
  · simp only [OrthDatabase.Orth, nonconstDB, Set.mem_empty_iff_false] at h
  · simp only [OrthDatabase.NotOrth, nonconstDB, Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [pullback_boolModel]
    exact not_orthogonalGiven_bot_bot_top_boolFS

/-- **Definition 42's second clause is the one with teeth.**  A single `N`-entry forces
every model's map to be non-constant, via Proposition 25 (`X ⊥^F X | Y ↔ Y ≤ X`) at
`X = f⁻¹(Dis_Ω)` and `Y = f⁻¹(Ind_Ω) = Ind_S`.  In particular the one-point model — which
satisfies an arbitrary `O` — is excluded, so this is the mechanism by which a database
constrains the latent structure `Ω` does not see. -/
lemma nonconstDB_forces_nonconstant {M : Model Bool}
    (hM : OrthDatabase.Models M nonconstDB) : ¬ ∀ s t : M.S, M.f s = M.f t := by
  intro hconst
  exact (hM ⊥ ⊥ ⊤).2 rfl
    ((M.F.orthogonalGiven_self_iff (M.pullback ⊥) (M.pullback ⊤)).2 fun s t _ => hconst s t)

/-- A database on `Bool × Bool` with both clauses non-empty, stated over this file's own
`coordFS` vocabulary: `O` asserts the two coordinate factors orthogonal given `Ind_Ω`, `N`
asserts the first factor is *not* orthogonal to itself given `Ind_Ω`. -/
def coordDB : OrthDatabase (Bool × Bool) :=
  ⟨{(fstFactor, sndFactor, ⊤)}, {(fstFactor, fstFactor, ⊤)}⟩

/-- **Definition 42 computed at a database with both clauses non-empty.**  The identity
model of `coordFS` models `coordDB`, both clauses discharged from §4.3's computations on
this witness — `orthogonalGiven_fst_snd_top` and `not_orthogonalGiven_fst_fst_top`. -/
lemma models_coordDB : OrthDatabase.Models coordModel coordDB := by
  intro X Y Z
  constructor
  · intro h
    simp only [OrthDatabase.Orth, coordDB, Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [pullback_coordModel]
    exact orthogonalGiven_fst_snd_top
  · intro h
    simp only [OrthDatabase.NotOrth, coordDB, Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [pullback_coordModel]
    exact not_orthogonalGiven_fst_fst_top

/-- …so `coordDB` is consistent, and unlike `totalDB` its consistency is not carried by a
degenerate model: this one is witnessed by a two-dimensional factored set on which the two
clauses take different truth values. -/
lemma coordDB_consistent : coordDB.Consistent := ⟨coordModel, models_coordDB⟩

/-- …and it is not complete: it says nothing about `sndFactor` against itself. -/
lemma not_coordDB_complete : ¬ coordDB.Complete := by
  intro h
  rcases h sndFactor sndFactor ⊤ with h | h <;>
    simp only [OrthDatabase.Orth, OrthDatabase.NotOrth, coordDB, Set.mem_singleton_iff,
      Prod.mk.injEq, Ne.symm fstFactor_ne_sndFactor, false_and, and_false] at h

/-! ### Definition 45: irreflexive where it is informative, vacuous where it is not -/

/-- **Definition 45 is irreflexive on every consistent database.**  A model of `D` supplies
a factored set on which `<^F` is a *strict* inclusion of histories, which no partition
bears to itself.  So `X <_D Y` is not the total relation. -/
lemma not_before_self_of_consistent {Ω : Type u} {D : OrthDatabase Ω} (hD : D.Consistent)
    (X : Setoid Ω) : ¬ D.Before X X := by
  obtain ⟨M, hM⟩ := hD
  exact fun h => lt_irrefl _ (h M hM)

/-- …instantiated at a database whose consistency is computed in this file, so the witness
does not depend on §6.2. -/
lemma not_nonconstDB_before_self (X : Setoid Bool) : ¬ nonconstDB.Before X X :=
  not_before_self_of_consistent nonconstDB_consistent X

/-- The other side of the same coin, and the trap worth recording: on an **inconsistent**
database Definition 45 is vacuously *total*, because it quantifies over models that do not
exist.  `X <_D Y` is therefore an inference only once `D` is known consistent — which is
why Propositions 33 and 35 come before Propositions 34 and 36 in the paper. -/
lemma before_of_not_consistent {Ω : Type u} {D : OrthDatabase Ω} (hD : ¬ D.Consistent)
    (X Y : Setoid Ω) : D.Before X Y := fun M hM => absurd ⟨M, hM⟩ hD

/-- …exhibited on the contradictory database, where every pair is "inferred" both ways. -/
lemma contradictoryDB_before_all (X Y : Setoid (Bool × Bool)) :
    contradictoryDB.Before X Y :=
  before_of_not_consistent not_contradictoryDB_consistent X Y

end Examples
end FiniteFactoredSets
