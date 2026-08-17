import ShannonInformation.API
import ShannonInformation.FiniteEntropy.Defs
import ShannonInformation.FiniteEntropy.Examples

/-! # Client-style tests for the finite-entropy generalization layer

`ShannonInformation/FiniteEntropy/` introduces `FiniteEntropyMeasure` / `FiniteEntropyOf`
as the hypothesis PFR's `FiniteRange` ought eventually to be relaxed to.  A generalization
is only worth its weight if it is *strictly* more general, and if it does not disturb what
already worked.  This file checks both, from outside the layer:

* the existing `FiniteRange` instance graph still discharges the new class by
  `infer_instance`, so no client that worked before has to change;
* a **constructed** witness — the geometric law on `ℕ` with success probability `1/2` —
  has finite entropy and does **not** have finite range.  That pair of facts is the content
  of `ShannonInformation/SCOPE.md` §2, which until now asserted it only informally.

The witness is genuinely computed, not asserted: its point masses, its entropy series and
its entropy `2 * log 2` are all derived from `ProbabilityTheory.geometricMeasure`.  The
construction itself was moved into the library as `ShannonInformation/FiniteEntropy/Examples.lean`
when `Condensation/Examples.lean` became a second client of it; this file now checks the
claims rather than building the object.

Note on imports: `Mathlib.Probability.Distributions.Geometric` co-imports with
`ShannonInformation.API` without trouble (see `FiniteEntropy/Examples.lean`, which imports
it).  The clash recorded in `ShannonInformation/README.md` ("Known constraint") is specific
to importing *all* of Mathlib; targeted imports are fine. -/

open MeasureTheory ProbabilityTheory Real ShannonInformation

namespace APITests.ShannonInformationFiniteEntropy

/-! ### Coexistence: the `FiniteRange` instance graph feeds the new class

Nothing here is proved by hand.  Each `infer_instance` goes
`FiniteRange → FiniteSupport → FiniteEntropyMeasure`, which is what makes the new
hypothesis a drop-in weakening rather than a fork of the API. -/

example {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {Ω : Type*} [MeasurableSpace Ω] (X : Ω → S) (μ : Measure Ω) :
    FiniteEntropyOf X μ := by infer_instance

example {S : Type*} [MeasurableSpace S] (μ : Measure S) [FiniteSupport μ] :
    FiniteEntropyMeasure μ := by infer_instance

/-- A derived member of the `FiniteRange` graph — `f ∘ X` — also lands in the new class
with no user input, which is the property that keeps the graph useful. -/
example {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSingletonClass T]
    {Ω : Type*} [MeasurableSpace Ω] (X : Ω → S) (f : S → T) (μ : Measure Ω) [FiniteRange X] :
    FiniteEntropyOf (f ∘ X) μ := by infer_instance

/-! ### The witness: a geometric variable on `ℕ`

The construction itself lives in `ShannonInformation/FiniteEntropy/Examples.lean`, because it
has a second client (`Condensation/Examples.lean`'s `geomModel`, the random variable model
that Definition 3.1 admits and the retired `dd:finite-range` narrowing excluded).  What is
checked here is the *claim* the construction supports, from outside the layer. -/

/-- **`FiniteEntropyOf` is strictly weaker than `FiniteRange`**, on a constructed witness —
the claim `ShannonInformation/SCOPE.md` §2 makes informally. -/
example : FiniteEntropyOf (id : ℕ → ℕ) geom ∧ ¬ FiniteRange (id : ℕ → ℕ) :=
  finiteEntropyOf_strictly_weaker

/-- The witness is informative: its entropy is `2 * log 2`, two bits, the textbook value for
`Geometric(1/2)`.  Without this, every fact above would also hold of a variable of entropy
`0`, and the generalization would have no demonstrated content. -/
example : H[(id : ℕ → ℕ) ; geom] = 2 * Real.log 2 := entropy_geom

example : 0 < H[(id : ℕ → ℕ) ; geom] := entropy_geom_pos

/-! ### The closure lemmas apply to it

The pair closure is the one that needed new mathematics (a termwise bound summed over a
product index), so exercising it on an infinite-range variable — where `FiniteRange` cannot
help — is the test that it actually bought something. -/

/-- The diagonal pair of the witness with itself has finite entropy — via
`finiteEntropyOf_pair`, not via any `FiniteRange` instance. -/
lemma finiteEntropyOf_geom_diag : FiniteEntropyOf (fun n : ℕ ↦ (id n, id n)) geom :=
  finiteEntropyOf_pair measurable_id measurable_id

/-- …and the marginal of that pair comes back, via `finiteEntropyOf_fst`. -/
example : FiniteEntropyOf (id : ℕ → ℕ) geom :=
  haveI := finiteEntropyOf_geom_diag
  finiteEntropyOf_fst (Y := (id : ℕ → ℕ)) measurable_id measurable_id

end APITests.ShannonInformationFiniteEntropy
