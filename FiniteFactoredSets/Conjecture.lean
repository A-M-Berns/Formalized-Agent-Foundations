import FiniteFactoredSets.Probability

/-!
# Conjecture 1: the fundamental theorem for finite-dimensional factored sets

§7.2 of Garrabrant, *Temporal Inference with Finite Factored Sets* (arXiv:2109.11513)
conjectures that Theorem 3 generalizes from finite to *finite-dimensional* factored sets:
`B` finite, `S` arbitrary.  Per the scope ruling recorded in `KNOWLEDGE.md`, the conjecture
is **stated as a `Prop` and deliberately not proved** — this library takes no position on
it, and no declaration here or elsewhere claims it.

## Modeling decision — `dd:conjecture`

* `FundamentalTheoremFiniteDim` is Theorem 3's statement
  (`orthogonalGiven_iff_forall_isDistribution`) with its `[Finite S]` hypothesis weakened
  to `[Finite F.B]`, quantified over every carrier `S : Type u`, every factored set on it,
  and every triple of partitions.  Nothing else changes: `IsDistribution` (Definition 37) is
  a finite product over `B` and `ProbDist` (Definition 36) is elementary, so both are
  meaningful with `S` infinite — which is exactly why the statement can be *written* here
  at all (`dd:finiteness-minimal`).
* The finite case of the conjecture is Theorem 3, and `fundamentalTheoremFiniteDim_of_finite`
  records that the `Prop` restricts to the proved theorem when `S` is finite.  That lemma is
  the only thing proved about it.  `FiniteFactoredSets/InfiniteExamples.lean` carries the
  witnesses that make both sides of this statement mean something: a two-factor factored
  set on the infinite carrier `ℕ × Bool` — inside the conjecture's scope, outside
  Theorem 3's, with an inhabited family of distributions — and an infinite-dimensional one
  showing that the `Finite F.B` hypothesis excludes something, and why.
* Status in the literature (see `KNOWLEDGE.md`, "On Conjecture 1's status"): a measurable
  refinement of the *unconditional* statement has since been proved (Mayer, arXiv:2412.00847);
  the conditional statement over bare finite-dimensional factored sets, as written here,
  remains open as far as this library knows.
-/

universe u

namespace FiniteFactoredSets

open FactoredSet

/-- Conjecture 1: Theorem 3 holds for finite-dimensional factored sets — for every
factored set `F` with `B` finite (and `S` arbitrary), `X ⊥^F Y | Z` iff every distribution
on `F` makes `X` and `Y` conditionally independent given `Z`.  Stated, not proved.

Paper node: Conjecture 1 (§7.2). -/
def FundamentalTheoremFiniteDim : Prop :=
  ∀ {S : Type u} (F : FactoredSet S) [Finite F.B] (X Y Z : Setoid S),
    F.OrthogonalGiven X Y Z ↔
      ∀ P : ProbDist S, F.IsDistribution P →
        ∀ x ∈ X.classes, ∀ y ∈ Y.classes, ∀ z ∈ Z.classes,
          P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z

/-- The conjecture's instance at a finite carrier is Theorem 3: the `Prop` above restricts to
the proved fundamental theorem when `S` is finite.  This is a consistency check on the
statement, not progress on the conjecture. -/
lemma fundamentalTheoremFiniteDim_of_finite {S : Type u} [Finite S] (F : FactoredSet S)
    (X Y Z : Setoid S) :
    F.OrthogonalGiven X Y Z ↔
      ∀ P : ProbDist S, F.IsDistribution P →
        ∀ x ∈ X.classes, ∀ y ∈ Y.classes, ∀ z ∈ Z.classes,
          P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z :=
  F.orthogonalGiven_iff_forall_isDistribution X Y Z

end FiniteFactoredSets
