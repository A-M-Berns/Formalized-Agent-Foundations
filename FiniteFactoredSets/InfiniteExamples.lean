import FiniteFactoredSets.Conjecture
import FiniteFactoredSets.Examples

/-!
# Witnesses for Conjecture 1 — the two sides of the finiteness boundary

`Conjecture.lean` states Conjecture 1 as a `Prop` over *finite-dimensional* factored sets:
`F.B` finite, `S` arbitrary.  That statement says nothing unless both of its sides are
inhabited, so this file exhibits them.

* `natBoolFS` is **inside** the conjecture's scope and outside Theorem 3's: two factors on
  the infinite carrier `ℕ × Bool`.  `Finite natBoolFS.B` holds by instance while
  `¬ Finite (ℕ × Bool)`, so the conjecture's hypothesis is met by something the proved
  fundamental theorem cannot reach.  The §3–§4 vocabulary is then run on it — histories
  through Proposition 13 clause 4, orthogonality through Proposition 14 and Definition 18,
  conditional orthogonality through Proposition 24 — and none of it needs `Finite S`,
  which is `dd:finiteness-minimal` doing its job.  `isDistribution_diracAt` supplies a
  distribution there, so the conjecture's right-hand side quantifies over a nonempty
  family.
* `infFS` is **outside** it: the coordinate factorization of `ℕ → Bool`, whose basis is
  infinite.  Up to the bijection `𝒫(ℕ) ≃ (ℕ → Bool)` this is the factored set §7.2 uses
  when it says it does *not* expect the fundamental theorem to generalize past finite
  dimension — `S = 𝒫(ℕ)`, `b_n` the partition by membership of `n`.  The paper's two §7.2
  examples are out of scope by the ruling in `KNOWLEDGE.md`, so nothing here claims a node
  for them; `infFS` lands only as the witness that the conjecture's `Finite F.B` hypothesis
  excludes something.

What `infFS` shows concretely is that the hypothesis is load-bearing rather than
inherited: `FactoredSet.isDistribution_diracAt` — the point mass is a distribution on every
factored set of finite dimension — is **false** on `infFS`
(`not_isDistribution_diracAt_infFS`).  The reason is the finprod junk value.  Definition 37
reads `P {s} = ∏ᶠ b ∈ B, P [s]_b`; with `B` infinite the multiplicative support of that
family is infinite, `finprod` returns `1` rather than the elementary product, and the
identity fails at every `s` other than the point mass's own.  So with infinitely many
factors the paper's Definition 37 product is not the elementary product it is written as,
and every §5 statement that consumes Definition 37 stops meaning what it says — which is
exactly why the conjecture is stated at finite dimension.

Nothing in this file is a paper endpoint: no statement here is annotated, and everything is
a `lemma`, `def` or `example`.
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
`FactoredSet.isDistribution_diracAt` needs, so the family Conjecture 1's right-hand side
quantifies over is nonempty at an infinite carrier. -/
lemma isDistribution_diracAt_natBoolFS (s₀ : ℕ × Bool) :
    natBoolFS.IsDistribution (ProbDist.diracAt s₀) :=
  natBoolFS.isDistribution_diracAt s₀

/-! #### Conjecture 1 is not vacuous at `natBoolFS`

The `Prop` unfolds at this factored set to a biconditional between a computed left-hand
side and a quantification over an inhabited family — so it is a statement about something,
not a claim whose hypothesis is never met. -/

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

/-- The conjecture's finite instance is Theorem 3, exercised on the four-point witness
`Examples.coordFS`: this is what `fundamentalTheoremFiniteDim_of_finite` buys a client. -/
example :
    Examples.coordFS.OrthogonalGiven Examples.fstFactor Examples.sndFactor ⊤ ↔
      ∀ P : ProbDist (Bool × Bool), Examples.coordFS.IsDistribution P →
        ∀ x ∈ Examples.fstFactor.classes, ∀ y ∈ Examples.sndFactor.classes,
          ∀ z ∈ (⊤ : Setoid (Bool × Bool)).classes,
            P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z :=
  fundamentalTheoremFiniteDim_of_finite Examples.coordFS _ _ _

/-! ### Infinite dimension: `infFS` on `ℕ → Bool`, outside the conjecture's scope

`memFactor n` is the partition of `ℕ → Bool` by the `n`-th bit.  Under the bijection
`𝒫(ℕ) ≃ (ℕ → Bool)` sending a set to its indicator, this is the factored set §7.2 discusses
when it says it does *not* expect the fundamental theorem to survive past finite dimension:
carrier `𝒫(ℕ)`, and one factor per natural number recording whether `n` belongs.  The
paper's two §7.2 examples are out of scope by the ruling in `KNOWLEDGE.md`, so no node is
claimed for this; it is here only to show that Conjecture 1's `Finite F.B` hypothesis
excludes something, and that it excludes it for a reason. -/

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
this is a legitimate inhabitant, and it is what Conjecture 1's hypothesis rules out. -/
def infFS : FactoredSet (ℕ → Bool) :=
  ⟨infBasis, (isFactorization_iff_existsUnique infBasis_nontrivial).2 infBasis_existsUnique⟩

lemma infFS_B : infFS.B = infBasis := rfl

lemma infFS_B_infinite : infFS.B.Infinite :=
  Set.infinite_range_of_injective memFactor_injective

/-- So `infFS` is outside Conjecture 1's scope — and outside §3's, since every §3–§4
statement carries `[Finite F.B]`.  `FactoredSet.history_isLeast` genuinely fails here: every
cofinite subset of `B` generates the "eventually equal" partition, so the intersection of
all generating subsets generates nothing (`KNOWLEDGE.md`). -/
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

-- A sample of the axiom profile; the full inventory is gated in `AxiomAudit.lean`.
#print axioms orthogonalGiven_natFactor_boolFactor_top
#print axioms not_isDistribution_diracAt_infFS

end InfiniteExamples
end FiniteFactoredSets
