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
* The finite case of the conjecture **is** Theorem 3
  (`FactoredSet.orthogonalGiven_iff_forall_isDistribution`) — same statement, `[Finite S]`
  in place of `[Finite F.B]` — so it needs no restatement here, and nothing else about the
  `Prop` is proved.  What *does* exercise the `Prop`'s shape is taking it as a hypothesis
  and applying it: `FiniteFactoredSets/InfiniteExamples.lean` and
  `APITests/FiniteFactoredSets.lean` each bind `(h : FundamentalTheoremFiniteDim.{0})` and
  discharge a conclusion Theorem 3 cannot reach.
* `FiniteFactoredSets/InfiniteExamples.lean` carries the witnesses that make both sides of
  this statement mean something: a two-factor factored set on the infinite carrier
  `ℕ × Bool` — inside the conjecture's scope, outside Theorem 3's, carrying both a point
  mass and a genuinely spread-out distribution, the latter *refuting* the right-hand side at
  a triple where the left-hand side fails — and an infinite-dimensional one showing that the
  `Finite F.B` hypothesis excludes something, and why.
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

end FiniteFactoredSets
