import ShannonInformation.API
import ShannonInformation.FiniteEntropy.ChainRule
import APITests.ShannonInformationFiniteEntropy

/-! # Client-style tests for the chain rule at `FiniteEntropyOf`

`ShannonInformation/FiniteEntropy/ChainRule.lean` restates PFR's four chain rules with
`[FiniteRange _]` weakened to `[FiniteEntropyOf _ μ]`.  A restatement is only worth its
weight if it clears two bars, and this file checks both from outside the layer.

**Nothing that worked before has to change.**  For `Fintype`-valued variables the
hypotheses are discharged by instance search along the same
`FiniteRange → FiniteSupport → FiniteEntropyMeasure` path Phase 1 installed, so a client
that used to call `ProbabilityTheory.chain_rule` can call
`ShannonInformation.chain_rule` with an identical argument list.

**It is strictly more general.**  The second half applies the chain rule to a pair of
*dependent, infinite-range* variables — the geometric witness of
`APITests.ShannonInformationFiniteEntropy` and the coarsening `n ↦ n / 2` of it, neither of
which has a `FiniteRange` instance (and `not_finiteRange_id` proves the first genuinely has
none).  Every `FiniteEntropyOf` obligation there is met by Phase 1's closure lemmas.

The imports are deliberately explicit: `ShannonInformation.API` does not yet re-export the
`FiniteEntropy/` layer, so a client naming both has to say so.

Note on `⟨X, Y⟩`: PFR's pair notation (`PFR/ForMathlib/Pair.lean`) competes with Lean's
anonymous-constructor syntax and loses whenever the expected type is a function type that
is still a metavariable — `μ.map ⟨X, Y⟩` fails to parse where `H[⟨X, Y⟩ ; μ]` succeeds.
Ascribe (`(⟨X, Y⟩ : Ω → S × T)`) at those sites. -/

open MeasureTheory ProbabilityTheory Real ShannonInformation

namespace APITests.ShannonInformationChainRule

/-! ### The `FiniteRange` path still discharges everything automatically

Each statement below names only measurability.  The `[FiniteEntropyOf _ μ]` arguments are
found by instance search, so these are literally PFR's call sites with the namespace
changed. -/

section Finite

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U] [Fintype S] [MeasurableSingletonClass S] [Fintype T]
  [MeasurableSingletonClass T] [Fintype U] [MeasurableSingletonClass U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (μ : Measure Ω) [IsProbabilityMeasure μ]

example (hX : Measurable X) (hY : Measurable Y) : H[⟨X, Y⟩ ; μ] = H[Y ; μ] + H[X | Y ; μ] :=
  ShannonInformation.chain_rule μ hX hY

example (hX : Measurable X) (hY : Measurable Y) : H[⟨X, Y⟩ ; μ] = H[X ; μ] + H[Y | X ; μ] :=
  ShannonInformation.chain_rule' μ hX hY

example (hX : Measurable X) (hY : Measurable Y) : H[X | Y ; μ] = H[⟨X, Y⟩ ; μ] - H[Y ; μ] :=
  ShannonInformation.chain_rule'' μ hX hY

example (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[⟨X, Y⟩ | Z ; μ] = H[Y | Z ; μ] + H[X | ⟨Y, Z⟩ ; μ] :=
  ShannonInformation.cond_chain_rule μ hX hY hZ

example (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[⟨X, Y⟩ | Z ; μ] = H[X | Z ; μ] + H[Y | ⟨X, Z⟩ ; μ] :=
  ShannonInformation.cond_chain_rule' μ hX hY hZ

/-- The `tsum` form of `condEntropy` also resolves its pair instance by search. -/
example (hX : Measurable X) (hY : Measurable Y) :
    H[X | Y ; μ] = ∑' y, (μ.map Y).real {y} * H[X | Y ← y ; μ] :=
  ShannonInformation.condEntropy_eq_tsum hX hY μ

/-- The two chain rules agree where both apply.  This is the anti-fork check: the
`FiniteEntropyOf` version is not a *different* statement, it is the same one with weaker
hypotheses. -/
example (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    ShannonInformation.chain_rule μ hX hY = ProbabilityTheory.chain_rule μ hX hY := rfl

end Finite

/-! ### A genuinely infinite-range application

`X` is the geometric witness read off `geom` (entropy `2 * log 2`, no `FiniteRange`
instance — see `APITests.ShannonInformationFiniteEntropy.not_finiteRange_id`) and `W` is
the coarsening `n ↦ n / 2`, which is also infinite-range.  PFR's `chain_rule` is
unavailable for either. -/

section Geometric

open APITests.ShannonInformationFiniteEntropy

/-- The coarsening `n ↦ n / 2` of the geometric witness. -/
def half2 : ℕ → ℕ := fun n ↦ n / 2

lemma measurable_half2 : Measurable half2 := .of_discrete

/-- `half2` has finite entropy — by `finiteEntropyOf_comp`, the pushforward closure, not by
any `FiniteRange` instance. -/
instance finiteEntropyOf_half2 : FiniteEntropyOf half2 geom :=
  finiteEntropyOf_comp (X := (id : ℕ → ℕ)) measurable_id measurable_half2

/-- …and it does not have finite range: it is surjective onto `ℕ`. -/
lemma not_finiteRange_half2 : ¬ FiniteRange half2 := by
  intro h
  have hsurj : Set.range half2 = Set.univ := by
    ext n
    simp only [Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨2 * n, by simp [half2]⟩
  exact Set.infinite_univ (hsurj ▸ h.finite)

/-- **The chain rule, applied to two dependent infinite-range variables.**  Both
`FiniteEntropyOf` obligations come from Phase 1's closure lemmas; nothing here is available
at `FiniteRange`. -/
example : H[⟨(id : ℕ → ℕ), half2⟩ ; geom]
    = H[half2 ; geom] + H[(id : ℕ → ℕ) | half2 ; geom] :=
  ShannonInformation.chain_rule geom measurable_id measurable_half2

/-- The `H[X | Y] = H[⟨X, Y⟩] - H[Y]` shape, same setting. -/
example : H[(id : ℕ → ℕ) | half2 ; geom]
    = H[⟨(id : ℕ → ℕ), half2⟩ ; geom] - H[half2 ; geom] :=
  ShannonInformation.chain_rule'' geom measurable_id measurable_half2

/-- The conditional entropy really is the `tsum` its definition promises — the Bochner
integral is not silently `0`, because `integrable_entropy_cond` derives integrability from
`FiniteEntropyOf ⟨half2, id⟩ geom`. -/
example : H[(id : ℕ → ℕ) | half2 ; geom]
    = ∑' n, (geom.map half2).real {n} * H[(id : ℕ → ℕ) | half2 ← n ; geom] :=
  ShannonInformation.condEntropy_eq_tsum (X := (id : ℕ → ℕ)) measurable_id measurable_half2 geom

/-- Since `id` is recoverable from the pair `⟨half2, id⟩` — indeed `id` alone determines
`half2` — the chain rule specialises to `H[⟨X, f ∘ X⟩] = H[X]`, which pins the conditional
entropy of the *coarsening given the variable* to `0`.  A concrete numeric consequence of
the general statement, on a variable PFR cannot reach. -/
example : H[half2 | (id : ℕ → ℕ) ; geom] = 0 := by
  have hcomp : (⟨(id : ℕ → ℕ), half2⟩ : ℕ → ℕ × ℕ) = ⟨(id : ℕ → ℕ), half2 ∘ id⟩ := rfl
  have hpair : H[⟨(id : ℕ → ℕ), half2⟩ ; geom] = H[(id : ℕ → ℕ) ; geom] := by
    rw [hcomp]
    exact ProbabilityTheory.entropy_prod_comp measurable_id geom half2
  have := ShannonInformation.chain_rule' geom measurable_id measurable_half2
  rw [hpair] at this
  linarith

/-- A second infinite-range coarsening, so that the conditional chain rule below runs on
three variables none of which has finite range. -/
def third : ℕ → ℕ := fun n ↦ n / 3

lemma measurable_third : Measurable third := .of_discrete

instance finiteEntropyOf_third : FiniteEntropyOf third geom :=
  finiteEntropyOf_comp (X := (id : ℕ → ℕ)) measurable_id measurable_third

/-- **The conditional chain rule on three infinite-range variables.**  Not one of the six
`FiniteEntropyOf` obligations here is reachable from a `FiniteRange` instance. -/
example : H[⟨(id : ℕ → ℕ), half2⟩ | third ; geom]
    = H[half2 | third ; geom] + H[(id : ℕ → ℕ) | ⟨half2, third⟩ ; geom] :=
  ShannonInformation.cond_chain_rule geom measurable_id measurable_half2 measurable_third

/-- …and its primed sibling. -/
example : H[⟨(id : ℕ → ℕ), half2⟩ | third ; geom]
    = H[(id : ℕ → ℕ) | third ; geom] + H[half2 | ⟨(id : ℕ → ℕ), third⟩ ; geom] :=
  ShannonInformation.cond_chain_rule' geom measurable_id measurable_half2 measurable_third

end Geometric

end APITests.ShannonInformationChainRule
