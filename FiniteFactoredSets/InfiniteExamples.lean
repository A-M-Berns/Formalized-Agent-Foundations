import FiniteFactoredSets.Conjecture
import FiniteFactoredSets.Examples

/-!
# Witnesses for Conjecture 1 — the two sides of the finiteness boundary

`Conjecture.lean` states Conjecture 1 as a `Prop` over *finite-dimensional* factored sets:
`F.B` finite, `S` arbitrary.  That statement is only about something if both of its sides
are, so this file exhibits them — and on the right-hand side an *inhabited* family of
distributions is not enough, since the obvious inhabitants satisfy its identity
unconditionally (`diracAt_rhs_trivial`); what is exhibited there is a discriminating one.

* `natBoolFS` is **inside** the conjecture's scope and outside Theorem 3's: two factors on
  the infinite carrier `ℕ × Bool`.  `Finite natBoolFS.B` holds by instance while
  `¬ Finite (ℕ × Bool)`, so the conjecture's hypothesis is met by something the proved
  fundamental theorem cannot reach.  The §3–§4 vocabulary is then run on it — histories
  through Proposition 13 clause 4, orthogonality through Proposition 14 and Definition 18,
  conditional orthogonality through Proposition 24 — and none of it needs `Finite S`,
  which is `dd:finiteness-minimal` doing its job.  The conjecture's right-hand side is a
  real constraint there, and *inhabitation* is not what makes it one: `isDistribution_diracAt`
  does supply distributions, but a point mass satisfies Theorem 3's right-hand-side identity
  for arbitrary sets (`diracAt_rhs_trivial`), so a family of point masses leaves that side
  constantly true and — against `not_orthogonal_natFactor_self` — would refute the conjecture
  rather than exhibit it.  The family has to contain a *discriminating* member, and `rich`,
  the uniform distribution on `{0,1} × Bool`, is one (`rich_isDistribution`,
  `rich_discriminates`).
* `infFS` is **outside** it: the coordinate factorization of `ℕ → Bool`, whose basis is
  infinite.  Up to the bijection `𝒫(ℕ) ≃ (ℕ → Bool)` this is the factored set §7.2 uses
  when it says it does *not* expect the fundamental theorem to generalize past finite
  dimension — `S = 𝒫(ℕ)`, `b_n` the partition by membership of `n`.  It is the `F` of both
  §7.2 examples: Example 3 is out of scope by the ruling in `KNOWLEDGE.md` and nothing here
  claims a node for it, while Example 4 is in scope (since 2026-08-30) and carried below —
  `infFS` doubles as the witness that the conjecture's `Finite F.B` hypothesis excludes
  something, and that it excludes it for a reason.

What `infFS` shows concretely is that `[Finite F.B]` is load-bearing rather than inherited,
in two independent places.

First, **Proposition 12 itself fails there**.  For the "eventually equal" partition `evEq`
of `ℕ → Bool`, dropping any single coordinate from `B` still generates it, so `h^F(evEq)`
is empty (`history_evEq`); but the empty set of factors generates only `Ind_S`, and `evEq`
is not `Ind_S`.  So the history does not generate (`not_generates_history_evEq`) and is not
the least generating subset (`not_isLeast_history_evEq`).  Proposition 12 is what earns the
word "smallest" in Definition 17, so past finite dimension `history` is still defined but
is no longer the object §3.2 onwards reasons about.

Second, `FactoredSet.isDistribution_diracAt` — the point mass is a distribution on every
factored set of finite dimension — is **false** on `infFS`
(`not_isDistribution_diracAt_infFS`).  The reason is the finprod junk value.  Definition 37
reads `P {s} = ∏ᶠ b ∈ B, P [s]_b`; with `B` infinite the multiplicative support of that
family is infinite, `finprod` returns `1` rather than the elementary product, and the
identity fails at every `s` other than the point mass's own.  So with infinitely many
factors the paper's Definition 37 product is not the elementary product it is written as,
and every §5 statement that consumes Definition 37 stops meaning what it says — which is
exactly why the conjecture is stated at finite dimension.

The Example 4 declarations (`infFS`, `finSupp`, `finSupp_ne_top`, `orthogonal_finSupp_self`)
are paper endpoints and are annotated; everything else in this file is an unannotated
witness — a `lemma`, `def` or `example` citing the paper in prose.
-/

namespace FiniteFactoredSets
namespace InfiniteExamples

open FactoredSet

/-! ### Finite dimension, infinite carrier: `natBoolFS` on `ℕ × Bool`

This is the shape the conjecture is about and Theorem 3 is not: two factors, infinitely
many points. -/

/-- The partition of `ℕ × Bool` by first coordinate. -/
def natFactor : Setoid (ℕ × Bool) := Setoid.comap Prod.fst ⊥
/-- The partition of `ℕ × Bool` by second coordinate. -/
def boolFactor : Setoid (ℕ × Bool) := Setoid.comap Prod.snd ⊥

lemma natFactor_ne_boolFactor : natFactor ≠ boolFactor := by
  intro h
  have hr : natFactor (0, false) (0, true) := rfl
  rw [h] at hr
  exact Bool.noConfusion hr

/-- The two-element basis `{natFactor, boolFactor}`. -/
def natBoolBasis : Set (Setoid (ℕ × Bool)) := {natFactor, boolFactor}

lemma natBoolBasis_nontrivial : ∀ b ∈ natBoolBasis, ¬ IsTrivialPartition b := by
  rintro b (rfl | rfl) ⟨-, h⟩
  · exact Nat.zero_ne_one (h (0, true) (1, true))
  · exact Bool.noConfusion (h (0, true) (0, false))

/-- Definition 10 through `isFactorization_iff_existsUnique`: a point of `ℕ × Bool` is
determined by, and freely chosen by, its two coordinates. -/
lemma natBoolBasis_existsUnique (g : natBoolBasis → ℕ × Bool) :
    ∃! s : ℕ × Bool, ∀ b : natBoolBasis, (b : Setoid (ℕ × Bool)) s (g b) := by
  refine ⟨((g ⟨natFactor, Or.inl rfl⟩).1, (g ⟨boolFactor, Or.inr rfl⟩).2), ?_, ?_⟩
  · rintro ⟨b, rfl | rfl⟩
    · rfl
    · rfl
  · intro s hs
    exact Prod.ext (hs ⟨natFactor, Or.inl rfl⟩) (hs ⟨boolFactor, Or.inr rfl⟩)

lemma natBool_isFactorization : IsFactorization natBoolBasis :=
  (isFactorization_iff_existsUnique natBoolBasis_nontrivial).2 natBoolBasis_existsUnique

/-- A factored set of dimension 2 whose carrier is infinite: inside Conjecture 1's scope,
outside Theorem 3's. -/
def natBoolFS : FactoredSet (ℕ × Bool) := ⟨natBoolBasis, natBool_isFactorization⟩

lemma natBoolFS_B : natBoolFS.B = natBoolBasis := rfl

lemma natFactor_mem : natFactor ∈ natBoolFS.B := Or.inl rfl
lemma boolFactor_mem : boolFactor ∈ natBoolFS.B := Or.inr rfl

lemma singleton_natFactor_subset : {natFactor} ⊆ natBoolFS.B := by
  rintro b rfl; exact natFactor_mem

lemma singleton_boolFactor_subset : {boolFactor} ⊆ natBoolFS.B := by
  rintro b rfl; exact boolFactor_mem

lemma natBoolFS_B_finite : natBoolFS.B.Finite :=
  Set.Finite.insert _ (Set.finite_singleton _)

/-- The conjecture's hypothesis holds here — and by `Set.Finite.to_subtype`, not by
Proposition 6, since the carrier is infinite. -/
instance : Finite natBoolFS.B := natBoolFS_B_finite.to_subtype

/-- …and Theorem 3's does not: `ℕ × Bool` is infinite, so nothing in §5 applies to
`natBoolFS`.  `Q^F_E` sums over subsets of `S`, so it is not a polynomial here; this is the
boundary `dd:finiteness-minimal` keeps §3–§4 on the near side of. -/
lemma not_finite_natBool : ¬ Finite (ℕ × Bool) := fun h => h.false

/-! #### §3–§4 vocabulary at an infinite carrier

Every §3–§4 endpoint below carries `[Finite F.B]` and nothing else, so all of it applies to
`natBoolFS` verbatim.  That is the concrete content of `dd:finiteness-minimal`: none of
history, orthogonality, time or conditional orthogonality needs `S` finite, and the
statements are the same ones `Examples.lean` runs on the four-point `coordFS`. -/

/-- Proposition 13 clause 4 on the infinite carrier: `h^F(b) = {b}` for a factor `b`.  The
clause's `Nonempty S` side condition is met by any point. -/
lemma history_natFactor : natBoolFS.history natFactor = {natFactor} :=
  (natBoolFS.history_spec natFactor natFactor).2.2.2 ⟨(0, true)⟩ natFactor natFactor_mem

lemma history_boolFactor : natBoolFS.history boolFactor = {boolFactor} :=
  (natBoolFS.history_spec boolFactor boolFactor).2.2.2 ⟨(0, true)⟩ boolFactor boolFactor_mem

/-- Definition 18 computed **from the histories**: the two singletons are disjoint. -/
lemma orthogonal_natFactor_boolFactor : natBoolFS.Orthogonal natFactor boolFactor :=
  (natBoolFS.orthogonal_iff_forall_notMem natFactor boolFactor).2 fun b hb hb' => by
    rw [history_natFactor] at hb
    rw [history_boolFactor] at hb'
    exact natFactor_ne_boolFactor
      ((Set.mem_singleton_iff.1 hb).symm.trans (Set.mem_singleton_iff.1 hb'))

/-- The same fact re-derived through Proposition 14, which mentions no history — so the
computation above is not merely echoing the endpoint that produced it. -/
example : natBoolFS.Orthogonal natFactor boolFactor :=
  (natBoolFS.orthogonal_iff_exists natFactor boolFactor).2
    ⟨{natFactor}, singleton_natFactor_subset,
      fun {_ _} h => commonRefinement_iff.1 h natFactor rfl,
      fun {_ _} h => commonRefinement_iff.1 h boolFactor
        ⟨boolFactor_mem, fun hc => natFactor_ne_boolFactor (Set.mem_singleton_iff.1 hc).symm⟩⟩

/-- Orthogonality is not vacuously total here either: by Proposition 15 clause 4 only
`Ind_S` is orthogonal to itself. -/
lemma not_orthogonal_natFactor_self : ¬ natBoolFS.Orthogonal natFactor natFactor := by
  intro hO
  have htop : natFactor = (⊤ : Setoid (ℕ × Bool)) :=
    (natBoolFS.orthogonal_spec natFactor natFactor natFactor).2.2.2.1 hO
  have hr : natFactor (0, true) (1, true) := by rw [htop]; trivial
  exact Nat.zero_ne_one hr

/-- Definition 27 at `Z = Ind_S`, through Proposition 24 — the left-hand side of
Conjecture 1's biconditional, computed on this witness. -/
lemma orthogonalGiven_natFactor_boolFactor_top :
    natBoolFS.OrthogonalGiven natFactor boolFactor ⊤ :=
  (natBoolFS.orthogonal_iff_orthogonalGiven_top natFactor boolFactor).1
    orthogonal_natFactor_boolFactor

/-- Definition 37 is inhabited on `natBoolFS`: `Finite natBoolFS.B` is all
`FactoredSet.isDistribution_diracAt` needs, so there are distributions to quantify over at
an infinite carrier.  Inhabitation is not by itself what makes Conjecture 1's right-hand
side a constraint; `diracAt_rhs_trivial` and `rich` below say what is. -/
lemma isDistribution_diracAt_natBoolFS (s₀ : ℕ × Bool) :
    natBoolFS.IsDistribution (ProbDist.diracAt s₀) :=
  natBoolFS.isDistribution_diracAt s₀

/-! #### Conjecture 1's right-hand side discriminates at `natBoolFS`

The `Prop` unfolds at this factored set to a biconditional between a computed left-hand
side and a quantification over the Definition-37 distributions.  That the family is
*inhabited* buys nothing.  A point mass satisfies Theorem 3's right-hand-side identity for
arbitrary sets (`diracAt_rhs_trivial`) — the identity never mentions the factored set, let
alone the triple — so a family consisting only of point masses would make the right-hand
side constantly true; and since the left-hand side is false at `X = Y = natFactor`,
`Z = Ind_S` (`not_orthogonal_natFactor_self`), such a family would *refute* Conjecture 1
rather than exhibit it.

The content is therefore that the family contains a **discriminating** member.  `rich`, the
uniform distribution on the four points `{0,1} × Bool`, is one: it is a Definition-37
distribution on `natBoolFS` (`rich_isDistribution`) and it falsifies the right-hand side at
that same triple (`rich_discriminates`), so both sides of the biconditional are genuinely
computed there and agree (`both_sides_fail_at_natFactor_self`).  This is the
infinite-carrier counterpart of `Examples.not_orthogonalGiven_bot_bot_top_boolFS`, which
guards the same failure mode on the finite side. -/

section Discriminating

/-- A point mass satisfies Theorem 3's right-hand-side identity for **arbitrary** sets
`x`, `y`, `z`: the identity reads `1 = 1` or `0 = 0` according to which of them contain
`s₀`.  Nothing about a factored set, a block, or conditional orthogonality enters, so a
`diracAt` witness certifies nothing about that side of Conjecture 1. -/
lemma diracAt_rhs_trivial {T : Type*} (s₀ : T) (x y z : Set T) :
    (ProbDist.diracAt s₀) (x ∩ z) * (ProbDist.diracAt s₀) (y ∩ z)
      = (ProbDist.diracAt s₀) (x ∩ y ∩ z) * (ProbDist.diracAt s₀) z := by
  simp only [ProbDist.diracAt_apply, Set.mem_inter_iff]
  by_cases hx : s₀ ∈ x <;> by_cases hy : s₀ ∈ y <;> by_cases hz : s₀ ∈ z <;>
    simp [hx, hy, hz]

/-- The support of `rich`: the four points `{0,1} × Bool`. -/
def richSupport : Set (ℕ × Bool) := {(0, true), (0, false), (1, true), (1, false)}

private lemma richSupport_finite : richSupport.Finite := by
  simp only [richSupport]
  exact ((((Set.finite_singleton _).insert _).insert _).insert _)

private lemma richSupport_ncard : richSupport.ncard = 4 := by
  simp only [richSupport]
  rw [Set.ncard_insert_of_notMem (by decide)
        (((Set.finite_singleton _).insert _).insert _),
      Set.ncard_insert_of_notMem (by decide) ((Set.finite_singleton _).insert _),
      Set.ncard_insert_of_notMem (by decide) (Set.finite_singleton _),
      Set.ncard_singleton]

/-- A Definition-37 distribution on `natBoolFS` that is **not** a point mass: uniform on
the four points `{0,1} × Bool`, i.e. `P(E) = |E ∩ richSupport| / 4`.  This is the witness
that makes Conjecture 1's right-hand side a constraint at an infinite carrier rather than a
tautology; see `rich_isDistribution` and `rich_discriminates`. -/
noncomputable def rich : ProbDist (ℕ × Bool) where
  P E := ((E ∩ richSupport).ncard : ℝ) / 4
  nonneg _ := by positivity
  empty := by rw [Set.empty_inter, Set.ncard_empty]; norm_num
  univ := by rw [Set.univ_inter, richSupport_ncard]; norm_num
  additive E₀ E₁ h := by
    rw [Set.union_inter_distrib_right,
      Set.ncard_union_eq (h.mono Set.inter_subset_left Set.inter_subset_left)
        (richSupport_finite.subset Set.inter_subset_right)
        (richSupport_finite.subset Set.inter_subset_right)]
    push_cast; ring

/-- `rich` counts its support: `P(E) = |E ∩ richSupport| / 4`. -/
lemma rich_apply (E : Set (ℕ × Bool)) : rich E = ((E ∩ richSupport).ncard : ℝ) / 4 := rfl

private lemma part_natFactor (s : ℕ × Bool) :
    part natFactor s = {p : ℕ × Bool | p.1 = s.1} := rfl

private lemma part_boolFactor (s : ℕ × Bool) :
    part boolFactor s = {p : ℕ × Bool | p.2 = s.2} := rfl

private lemma natRow_inter (n : ℕ) : {p : ℕ × Bool | p.1 = n} ∩ richSupport
    = if n = 0 then {((0:ℕ), true), ((0:ℕ), false)}
      else if n = 1 then {((1:ℕ), true), ((1:ℕ), false)} else ∅ := by
  split_ifs with h0 h1 <;> subst_vars <;>
    (ext p; obtain ⟨n, b⟩ := p; cases b <;> simp [richSupport, Set.mem_inter_iff] <;> omega)

/-- A block of `natFactor` has mass `1/2` when it meets the support, `0` otherwise. -/
private lemma rich_natRow (n : ℕ) :
    rich {p : ℕ × Bool | p.1 = n} = if n = 0 ∨ n = 1 then (1:ℝ)/2 else 0 := by
  rw [rich_apply, natRow_inter]
  split_ifs with h0 h1 h2 h3 h4 <;>
    first
      | (exfalso; omega)
      | (exfalso; tauto)
      | (rw [Set.ncard_pair (by decide)]; norm_num)
      | (rw [Set.ncard_empty]; norm_num)

private lemma boolCol_inter (b : Bool) :
    {p : ℕ × Bool | p.2 = b} ∩ richSupport = {((0:ℕ), b), ((1:ℕ), b)} := by
  cases b <;>
    (ext p; obtain ⟨n, c⟩ := p; cases c <;> simp [richSupport, Set.mem_inter_iff])

/-- Every block of `boolFactor` has mass `1/2`. -/
private lemma rich_boolCol (b : Bool) : rich {p : ℕ × Bool | p.2 = b} = (1:ℝ)/2 := by
  rw [rich_apply, boolCol_inter, Set.ncard_pair (by simp)]
  norm_num

private lemma singleton_inter_richSupport (n : ℕ) (c : Bool) :
    ({((n, c) : ℕ × Bool)} ∩ richSupport)
      = if n = 0 ∨ n = 1 then {((n, c) : ℕ × Bool)} else ∅ := by
  split_ifs with h
  · rw [Set.inter_eq_self_of_subset_left]
    rcases h with h | h <;> subst h <;> cases c <;> simp [richSupport]
  · ext p
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
      not_and]
    rintro rfl hp
    simp only [richSupport, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
    omega

private lemma rich_singleton (n : ℕ) (c : Bool) :
    rich {((n, c) : ℕ × Bool)} = if n = 0 ∨ n = 1 then (1:ℝ)/4 else 0 := by
  rw [rich_apply, singleton_inter_richSupport]
  split_ifs <;> simp [Set.ncard_singleton]

/-- `rich` **is** a Definition-37 distribution on `natBoolFS`: at a point of the support
`1/4 = 1/2 · 1/2`, and off it `0 = 0 · 1/2`.  So the discriminating witness lies inside the
family Conjecture 1's right-hand side quantifies over. -/
lemma rich_isDistribution : natBoolFS.IsDistribution rich := by
  intro s
  rw [natBoolFS_B, show natBoolBasis = {natFactor, boolFactor} from rfl,
    finprod_mem_pair natFactor_ne_boolFactor, part_natFactor, part_boolFactor,
    rich_natRow, rich_boolCol, rich_singleton]
  split_ifs <;> norm_num

/-- `rich` falsifies Theorem 3's right-hand-side clause **in the shape Conjecture 1
quantifies it**, at `X = Y = natFactor` and `Z = Ind_S`: taking `x = y` the block
`{p | p.1 = 0}` and `z = S`, the identity would read `1/2 · 1/2 = 1/2 · 1`.  Together with
`diracAt_rhs_trivial` this is what says the right-hand side is a constraint at `natBoolFS`
rather than a tautology. -/
lemma rich_discriminates :
    ¬ ∀ x ∈ natFactor.classes, ∀ y ∈ natFactor.classes,
        ∀ z ∈ (⊤ : Setoid (ℕ × Bool)).classes,
          rich (x ∩ z) * rich (y ∩ z) = rich (x ∩ y ∩ z) * rich z := by
  intro h
  have hx : {p : ℕ × Bool | p.1 = 0} ∈ natFactor.classes := natFactor.mem_classes (0, true)
  have hz : (Set.univ : Set (ℕ × Bool)) ∈ (⊤ : Setoid (ℕ × Bool)).classes := by
    rw [classes_top ⟨(0, true)⟩]; rfl
  have key := h _ hx _ hx _ hz
  simp only [Set.inter_univ, Set.inter_self] at key
  rw [rich_natRow, rich.univ] at key
  norm_num at key

/-- The payoff, and the shape a non-vacuity claim has to have: at the triple
`X = Y = natFactor`, `Z = Ind_S` **both** sides of Conjecture 1's biconditional are false —
the left by Proposition 15 clause 4, the right because `rich` is a Definition-37
distribution violating the identity.  A family of point masses could not have supplied the
second conjunct (`diracAt_rhs_trivial`), which is why an inhabited family is not enough. -/
lemma both_sides_fail_at_natFactor_self :
    ¬ natBoolFS.OrthogonalGiven natFactor natFactor ⊤ ∧
      ¬ (∀ P : ProbDist (ℕ × Bool), natBoolFS.IsDistribution P →
          ∀ x ∈ natFactor.classes, ∀ y ∈ natFactor.classes,
            ∀ z ∈ (⊤ : Setoid (ℕ × Bool)).classes,
              P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z) :=
  ⟨fun h => not_orthogonal_natFactor_self
      ((natBoolFS.orthogonal_iff_orthogonalGiven_top natFactor natFactor).2 h),
   fun h => rich_discriminates (h rich rich_isDistribution)⟩

end Discriminating

example (h : FundamentalTheoremFiniteDim.{0}) :
    natBoolFS.OrthogonalGiven natFactor boolFactor ⊤ ↔
      ∀ P : ProbDist (ℕ × Bool), natBoolFS.IsDistribution P →
        ∀ x ∈ natFactor.classes, ∀ y ∈ boolFactor.classes,
          ∀ z ∈ (⊤ : Setoid (ℕ × Bool)).classes,
            P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z :=
  h natBoolFS natFactor boolFactor ⊤

/-- And run forward: the conjecture, applied here, would say something about every
distribution on `natBoolFS` — of which `ProbDist.diracAt` supplies one for each point. -/
example (h : FundamentalTheoremFiniteDim.{0}) :
    ∀ P : ProbDist (ℕ × Bool), natBoolFS.IsDistribution P →
      ∀ x ∈ natFactor.classes, ∀ y ∈ boolFactor.classes,
        ∀ z ∈ (⊤ : Setoid (ℕ × Bool)).classes,
          P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z :=
  (h natBoolFS natFactor boolFactor ⊤).1 orthogonalGiven_natFactor_boolFactor_top

/-- The conjecture's finite instance **is** Theorem 3
(`orthogonalGiven_iff_forall_isDistribution`), exercised here on the four-point witness
`Examples.coordFS` — the same statement the `Prop` above weakens, at a carrier where it is
proved. -/
example :
    Examples.coordFS.OrthogonalGiven Examples.fstFactor Examples.sndFactor ⊤ ↔
      ∀ P : ProbDist (Bool × Bool), Examples.coordFS.IsDistribution P →
        ∀ x ∈ Examples.fstFactor.classes, ∀ y ∈ Examples.sndFactor.classes,
          ∀ z ∈ (⊤ : Setoid (Bool × Bool)).classes,
            P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z :=
  Examples.coordFS.orthogonalGiven_iff_forall_isDistribution _ _ _

/-! ### Infinite dimension: `infFS` on `ℕ → Bool`, outside the conjecture's scope

`memFactor n` is the partition of `ℕ → Bool` by the `n`-th bit.  Under the bijection
`𝒫(ℕ) ≃ (ℕ → Bool)` sending a set to its indicator, this is the factored set §7.2 discusses
when it says it does *not* expect the fundamental theorem to survive past finite dimension:
carrier `𝒫(ℕ)`, and one factor per natural number recording whether `n` belongs.  It is the
`F` of both §7.2 examples.  Example 3 (the fundamental-theorem counterexample) is out of
scope by the ruling in `KNOWLEDGE.md` and no node is claimed for it here; Example 4 — which
is about Definition 17's history at infinite dimension, not about the fundamental theorem —
is carried below (`finSupp`, `orthogonal_finSupp_self`).  Independently of either, `infFS`
shows that Conjecture 1's `Finite F.B` hypothesis excludes something, and that it excludes
it for a reason. -/

/-- The partition of `ℕ → Bool` by the `n`-th bit — the paper's `b_n`, "does `n` belong?",
transported along `𝒫(ℕ) ≃ (ℕ → Bool)`. -/
def memFactor (n : ℕ) : Setoid (ℕ → Bool) := Setoid.comap (fun s => s n) ⊥

/-- The infinite basis `{b_n | n ∈ ℕ}`. -/
def infBasis : Set (Setoid (ℕ → Bool)) := Set.range memFactor

lemma memFactor_injective : Function.Injective memFactor := by
  intro n m h
  by_contra hne
  have hr : memFactor m (fun k => decide (k = n)) (fun _ => false) := by
    show decide (m = n) = false
    simp [Ne.symm hne]
  rw [← h] at hr
  have : decide (n = n) = false := hr
  simp at this

lemma infBasis_nontrivial : ∀ b ∈ infBasis, ¬ IsTrivialPartition b := by
  rintro _ ⟨n, rfl⟩ ⟨-, hall⟩
  have h := hall (fun _ => false) (fun _ => true)
  exact Bool.noConfusion (h : (false : Bool) = true)

lemma infBasis_existsUnique (g : infBasis → (ℕ → Bool)) :
    ∃! s : ℕ → Bool, ∀ b : infBasis, (b : Setoid (ℕ → Bool)) s (g b) := by
  refine ⟨fun n => g ⟨memFactor n, ⟨n, rfl⟩⟩ n, ?_, ?_⟩
  · rintro ⟨b, m, rfl⟩
    rfl
  · intro s' hs'
    funext n
    exact hs' ⟨memFactor n, ⟨n, rfl⟩⟩

/-- A factored set of infinite dimension: Definition 11 does not ask for finiteness, so
this is a legitimate inhabitant, and it is what Conjecture 1's hypothesis rules out.  This
is the `F = (S, B)` of the paper's Example 4 (and of its out-of-scope Example 3), with
`S = 𝒫(ℕ)` read as `ℕ → Bool` and `B = {b_n | n ∈ ℕ}`.

Paper node: Example 4 (§7.2). -/
def infFS : FactoredSet (ℕ → Bool) :=
  ⟨infBasis, (isFactorization_iff_existsUnique infBasis_nontrivial).2 infBasis_existsUnique⟩

lemma infFS_B : infFS.B = infBasis := rfl

lemma infFS_B_infinite : infFS.B.Infinite :=
  Set.infinite_range_of_injective memFactor_injective

/-- So `infFS` is outside Conjecture 1's scope — and outside the reach of the §3–§4
*results* that carry `[Finite F.B]` (the definitions, and e.g. Propositions 10, 11 and 24,
carry none and run on it).  `FactoredSet.history_isLeast` genuinely fails here: every
cofinite subset of `B` generates the "eventually equal" partition, so the intersection of
all generating subsets generates nothing.  That is proved below, at
`not_isLeast_history_evEq`. -/
lemma not_finite_B : ¬ Finite infFS.B := fun h => infFS_B_infinite (Set.finite_coe_iff.1 h)

/-- The `[Finite F.B]` on `FactoredSet.isDistribution_diracAt` is load-bearing, not
inherited: the point mass is **not** a distribution on `infFS`.

The mechanism is the finprod junk value.  Definition 37 reads
`P {s} = ∏ᶠ b ∈ B, P [s]_b`, and at `s = (fun _ => true)` the left-hand side is `0` while
every factor of the right-hand side is `0` as well — so the multiplicative support of the
family is all of `B`, which is infinite, and `finprod` returns its junk value `1` instead of
the elementary product `0`.  With infinitely many factors the paper's Definition 37 product
is therefore not the elementary product it is written as, which is the precise sense in
which §5 stops applying past finite dimension. -/
lemma not_isDistribution_diracAt_infFS :
    ¬ infFS.IsDistribution (ProbDist.diracAt (fun _ => false)) := by
  intro h
  have hs := h (fun _ => true)
  rw [ProbDist.diracAt_apply, if_neg (by
    intro hm
    have : (fun _ => false : ℕ → Bool) = (fun _ => true : ℕ → Bool) := hm
    exact Bool.noConfusion (congrFun this 0))] at hs
  have hzero : ∀ b ∈ infFS.B, ProbDist.diracAt (fun _ => false)
      (part b (fun _ => true : ℕ → Bool)) = 0 := by
    rintro b hb
    obtain ⟨n, rfl⟩ := hb
    rw [ProbDist.diracAt_apply, if_neg]
    intro hm
    exact Bool.noConfusion (hm : (false : Bool) = true)
  rw [finprod_mem_def] at hs
  rw [finprod_of_infinite_mulSupport] at hs
  · exact absurd hs (by norm_num)
  · refine Set.Infinite.mono (s := infFS.B) ?_ infFS_B_infinite
    intro b hb
    rw [Function.mem_mulSupport, Set.mulIndicator_of_mem hb, hzero b hb]
    norm_num

/-! #### Proposition 12 fails at infinite dimension

`FactoredSet.history_isLeast` carries `[Finite F.B]` because the paper's proof writes
`h^F(X)` as a *finite* intersection of generating subsets.  At infinite dimension that
argument has nothing to fall back on, and the conclusion is false, not merely unproved.

The witness is the "eventually equal" partition `evEq` on `ℕ → Bool` — the one the paper's
`𝒫(ℕ)` example suggests.  Dropping a single coordinate from `B` still generates it, because
the chimera then differs from `s` in at most that one place; so `h^F(evEq)` is contained in
`B \ {b_m}` for every `m`, hence empty.  But the empty set generates only `Ind_S`, and
`evEq` is not `Ind_S`.  So the history of `evEq` does not generate it, and is therefore not
the least generating subset. -/

/-- The "eventually equal" partition of `ℕ → Bool`: `s ≈ t` when `s` and `t` differ at only
finitely many coordinates. -/
def evEq : Setoid (ℕ → Bool) where
  r s t := {n | s n ≠ t n}.Finite
  iseqv :=
    { refl := fun _ => Set.Finite.subset Set.finite_empty fun _ hn => absurd rfl hn
      symm := fun {_ _} h => Set.Finite.subset h fun _ hn he => hn he.symm
      trans := fun {s t _} h₁ h₂ =>
        Set.Finite.subset (h₁.union h₂) fun n hn => by
          by_cases hst : s n = t n
          · exact Or.inr fun htu => hn (hst.trans htu)
          · exact Or.inl hst }

/-- `evEq` is not `Ind_S`: the all-`false` and all-`true` sequences differ everywhere. -/
lemma evEq_ne_top : evEq ≠ ⊤ := by
  intro h
  have hrel : evEq (fun _ => false) (fun _ => true) := by rw [h]; trivial
  have hfin : {_n : ℕ | (false : Bool) ≠ true}.Finite := hrel
  rw [show {_n : ℕ | (false : Bool) ≠ true} = (Set.univ : Set ℕ) from by ext n; simp] at hfin
  exact Set.infinite_univ hfin

/-- On `infFS` the empty set of factors splices out the first argument entirely. -/
private lemma chimera_empty_infFS (s t : ℕ → Bool) : infFS.chimera ∅ s t = t := by
  funext n
  exact infFS.chimera_rel_of_notMem s t ⟨n, rfl⟩ (Set.notMem_empty _)

/-- Every *cofinite* subset of `B` generates `evEq`, and one missing coordinate already
suffices: the chimera along `B \ {b_m}` agrees with `s` away from `m`. -/
private lemma generates_sdiff_singleton (m : ℕ) :
    infFS.Generates (infFS.B \ {memFactor m}) evEq := by
  rw [infFS.generates_iff_rel]
  intro s t
  refine Set.Finite.subset (Set.finite_singleton m) fun n hn => ?_
  by_contra hnm
  exact hn (infFS.chimera_rel_of_mem s t ⟨n, rfl⟩
    ⟨⟨n, rfl⟩, fun hc => hnm (memFactor_injective (Set.mem_singleton_iff.1 hc))⟩)

/-- Definition 17's intersection collapses: no factor survives in `h^F(evEq)`. -/
lemma history_evEq : infFS.history evEq = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun b hb => ?_
  obtain ⟨m, rfl⟩ := infFS.history_subset evEq hb
  exact (infFS.history_subset_of_generates Set.sdiff_subset
    (generates_sdiff_singleton m) hb).2 rfl

/-- **Proposition 12's conclusion is false at infinite dimension.**  The history of `evEq`
is empty, and the empty set of factors generates only `Ind_S`, which `evEq` is not.  So the
`[Finite F.B]` on `FactoredSet.history_isLeast` is load-bearing rather than inherited from
the paper's finite setting. -/
lemma not_generates_history_evEq : ¬ infFS.Generates (infFS.history evEq) evEq := by
  rw [history_evEq, infFS.generates_iff_rel]
  intro h
  refine evEq_ne_top (Setoid.ext fun s t => ⟨fun _ => trivial, fun _ => ?_⟩)
  have hts := h s t
  rw [chimera_empty_infFS] at hts
  exact evEq.symm' hts

/-- The same failure in Proposition 12's own shape: `h^F(evEq)` is not the least subset of
`B` generating `evEq`, because it does not generate `evEq` at all. -/
lemma not_isLeast_history_evEq :
    ¬ IsLeast {C | C ⊆ infFS.B ∧ infFS.Generates C evEq} (infFS.history evEq) :=
  fun h => not_generates_history_evEq h.1.2

/-! ### Example 4: a two-block partition orthogonal to itself

§7.2.2 asks how orthogonality should be defined at infinite dimension and lists three
options.  The second — "define the history of `X` to be the intersection of all `C ⊆ B`
such that `C ⊢^F X`, and leave the definitions of orthogonality and time alone" — is
*exactly* Definitions 17 and 18 of this library read on an arbitrary factored set, since
`FactoredSet.history` is that intersection and `Orthogonal` is disjointness of histories.
Example 4 is the paper's illustration of that option's "unintuitive behavior": on the
`𝒫(ℕ)` factored set, `Z = {finite subsets, infinite subsets}` "is orthogonal to itself
according to the second option, in spite of having more than one part".  Both halves of
that sentence are proved here: `orthogonal_finSupp_self` and `finSupp_ne_top`.  The
mechanism is the same as for `evEq` above — dropping any single coordinate from `B` still
generates `Z`, so `h^F(Z)` is empty. -/

/-- Example 4's partition `Z`: under `𝒫(ℕ) ≃ (ℕ → Bool)`, `s ≈ t` when `s` and `t` are both
finitely supported or both not — the paper's `{{s | |s| < ∞}, {s | |s| = ∞}}`.

Paper node: Example 4 (§7.2). -/
def finSupp : Setoid (ℕ → Bool) := Setoid.comap (fun s => {n | s n = true}.Finite) ⊥

lemma finSupp_rel_iff (s t : ℕ → Bool) :
    finSupp s t ↔ ({n | s n = true}.Finite ↔ {n | t n = true}.Finite) :=
  ⟨fun h => Iff.of_eq h, fun h => propext h⟩

/-- `Z` has more than one part: the empty set and `ℕ` lie in different blocks.

Paper node: Example 4 (§7.2). -/
theorem finSupp_ne_top : finSupp ≠ ⊤ := by
  intro h
  have hrel : finSupp (fun _ => false) (fun _ => true) := by rw [h]; trivial
  rw [finSupp_rel_iff] at hrel
  have hfin : {n : ℕ | (fun _ : ℕ => (true : Bool)) n = true}.Finite :=
    hrel.1 (Set.finite_empty.subset fun n hn => by simp at hn)
  rw [show {n : ℕ | (fun _ : ℕ => (true : Bool)) n = true} = (Set.univ : Set ℕ) from by
    ext n; simp] at hfin
  exact Set.infinite_univ hfin

/-- Dropping one coordinate from `B` still generates `Z`: the chimera along `B \ {b_m}`
agrees with `s` away from `m`, and finiteness of support is insensitive to one coordinate. -/
private lemma generates_sdiff_singleton_finSupp (m : ℕ) :
    infFS.Generates (infFS.B \ {memFactor m}) finSupp := by
  rw [infFS.generates_iff_rel]
  intro s t
  have hagree : ∀ n, n ≠ m → infFS.chimera (infFS.B \ {memFactor m}) s t n = s n :=
    fun n hnm => infFS.chimera_rel_of_mem s t ⟨n, rfl⟩
      ⟨⟨n, rfl⟩, fun hc => hnm (memFactor_injective (Set.mem_singleton_iff.1 hc))⟩
  rw [finSupp_rel_iff]
  constructor
  · intro h
    refine (h.union (Set.finite_singleton m)).subset fun n hn => ?_
    by_cases hnm : n = m
    · exact Or.inr hnm
    · exact Or.inl (show infFS.chimera _ s t n = true by rw [hagree n hnm]; exact hn)
  · intro h
    refine (h.union (Set.finite_singleton m)).subset fun n hn => ?_
    by_cases hnm : n = m
    · exact Or.inr hnm
    · exact Or.inl (show s n = true by rw [← hagree n hnm]; exact hn)

/-- Definition 17's intersection collapses on `Z`: no factor survives in `h^F(Z)`. -/
lemma history_finSupp : infFS.history finSupp = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun b hb => ?_
  obtain ⟨m, rfl⟩ := infFS.history_subset finSupp hb
  exact (infFS.history_subset_of_generates Set.sdiff_subset
    (generates_sdiff_singleton_finSupp m) hb).2 rfl

/-- **Example 4's claim**: `Z` is orthogonal to itself under Definition 18 read with
Definition 17's history (the paper's "second option"), despite having more than one part
(`finSupp_ne_top`).

Paper node: Example 4 (§7.2). -/
theorem orthogonal_finSupp_self : infFS.Orthogonal finSupp finSupp := by
  rw [orthogonal_def, history_finSupp, Set.empty_inter]

-- A sample of the axiom profile; the full inventory is gated in `AxiomAudit.lean`.
#print axioms orthogonal_finSupp_self
#print axioms orthogonalGiven_natFactor_boolFactor_top
#print axioms rich_isDistribution
#print axioms not_isDistribution_diracAt_infFS
#print axioms not_isLeast_history_evEq

end InfiniteExamples
end FiniteFactoredSets
