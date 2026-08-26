import LogicalInduction.Construction.Witnesses.ComputationDP
import LogicalInduction.Construction.Witnesses.ProductDefinition
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-!
# The concrete witness for the finite-perturbation counterexample

`Properties/FinitePerturbationCounterexample.lean` develops the refutation of the
unrestricted finite-day perturbation statement abstractly and closes with
`not_overgeneral_ifp_of_advice`, a complete reduction.  This module supplies the witness
that reduction consumes and states the closed refutation.

The split is forced: `theoremDP` and the quotation layer reach the abstract module through
`ComputationSyntax` → `BoundedEvaluation` → `LogicalInduction.Properties`, so the witness
cannot be named there.  It is the same split `lic_paradox_resistance_ofDiagonal` and
`lic_paradox_resistance_ofDiagonal_unconditional` already use.

The market fed to `paradoxResistanceQuoteOfDiagonal` is the **unperturbed** one
(`theoremMarketComputation`): `χ n` asserts a fact about that quote program, and
`advicePerturbed_agree` carries the reflection to the perturbed market on every day `≥ 1`.
Nothing here carries a `Paper node:` line — this refutes `thm:ifp` rather than rendering
it.
-/

namespace LogicalInduction
namespace FinitePerturbationCounterexample

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional
open Filter Topology
open Classical

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-! ## The diagonal at threshold `1/2` -/

/-- The canonical `p = 1/2` paradox-resistance quotation package over the constructed
`LIA`, built from the **unperturbed** market's own quote program.  The width is the
harmonic family `1/(n+1)`.
Kind `Def`; hypotheses `(b)` `paradoxResistanceQuoteOfDiagonal`,
`harmonicWeight_polyRatCodes`. -/
noncomputable def cxQuote :
    ParadoxResistanceQuote (liaHistory (theoremDP T)) (theoremDP T) (1 / 2) :=
  paradoxResistanceQuoteOfDiagonal (quotationPresentation T)
    (theoremMarketComputation T) (1 / 2) (fun n : ℕ => 1 / ((n : ℚ) + 1))
    harmonicWeight_polyRatCodes
    (PolyRatCodes.inv_of_pos harmonicWeight_polyRatCodes (fun n => by positivity))
    (fun n => by positivity)
    (by
      have h : ∀ n : ℕ, ((1 / ((n : ℚ) + 1) : ℚ) : ℝ) = 1 / ((n : ℝ) + 1) := by
        intro n; push_cast; ring
      simpa only [h] using tendsto_one_div_add_atTop_nhds_zero_nat)

/-- The Boolean quotation code behind that diagonal.  Naming it separately is what makes
the sentence family's *whole-value* code available (`BooleanQuoteCode.sentence_poly`); the
`ParadoxResistanceQuote` above carries only the symbol-metered `RpnSentenceCodes`, which
the day-`0` quote program cannot use. -/
noncomputable def cxQuoteCode := (theoremDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode

/-- The diagonal family: `χ n` holds exactly when its own day-`n` price is below `1/2`. -/
noncomputable def cxDiagonal : ℕ → Sentence := (cxQuoteCode T).sentence

/-- The diagonal family is efficiently codeable as whole values.
Kind `C`; hypotheses `(b)` `BooleanQuoteCode.sentence_poly`. -/
lemma cxDiagonal_poly : PolySentenceCodes (cxDiagonal T) :=
  (cxQuoteCode T).sentence_poly

/-- The paradox-resistance package is stated about exactly this family.
Kind `T`. -/
lemma cxQuote_sentence : (cxQuote T).sentence = cxDiagonal T := rfl

/-- The perturbed market: the constructed `LIA` with day `0` republished as the advice
table. -/
noncomputable def cxPerturbed : History :=
  advicePerturbed (liaHistory (theoremDP T)) (theoremDP T) (cxDiagonal T)

/-! ## The one remaining obligation -/

/-- **Not proved.**  The day-`0` advice row is a decidable search, but the program is not
built.  This is the only `sorry` in the counterexample; nothing here may be read as
refuting the paper's `thm:ifp` until it is discharged.

Route.  `ComputableMarket` asks for prices in `[0,1]` — supplied by
`advicePerturbed_mem_Icc` over `IsMachineLogicalInductor.marketComputable` — a rational
quote table, and one `Nat.Partrec.Code` computing it on the paired input.

The remaining goal is exactly the quote-table existential; the `[0,1]` half is discharged
above.  The table is `fun n c => if n = 0 then adviceQuote c else M.quote n c` for
`M := theoremMarketComputation T`, with `adviceQuote` decoding `c` and dispatching on the
atom tag.  Semantic agreement splits by `Encodable.encodek` into the tag-`6` case, the
tag-`7` case, and `adviceRow_of_not_advice`; `Nat.pair_unpair` is what turns "an atom whose
tag is `6`" back into `schedAtom _`.

Five computability obligations remain, in dependency order:

1. `Computable (fun n => Encodable.encode (cxDiagonal T n))` — available, from
   `cxDiagonal_poly` (that is why `cxQuoteCode` is named separately: the
   `ParadoxResistanceQuote` carries only the symbol-metered `RpnSentenceCodes`, which will
   not serve here).
2. Deciding `SettledAt` at a stage: `stageEntails` is primitive recursive
   (`stageEntails_primrec`) and `stageEntails_eq_true_iff` matches it to the semantic
   predicate; the stage itself comes from `theoremDP_computable`'s code, so this composes
   to `Partrec`, not `Computable`.
3. `Computable (settleStage …)`: `Nat.rfindOpt` + `Partrec.of_eq_tot` over (2), in the
   `liaEntries_computable` style.  Totality is a bare existence statement, so the
   compactness proof of `exists_stage_entails` suffices — no constructive stage bound is
   needed.  `settleStage` being `Nat.find` rather than an arbitrary choice witness is what
   makes this true at all.
4. `Computable (sched …)`: recursion on the computable step (3).  This is the step with no
   ready-made route in the repo, and the likeliest place for real friction.
5. The gate bit: `∃ j, sched j = n` is the bounded search `∃ j ≤ n, sched j = n`, licensed
   by `sched_strictMono` with `sched 0 = 1`.

`sched_congr` and `settleStage_congr` are what make all of this a function of the
unperturbed market alone, so the day-`0` row does not refer to itself.

Recognising the advice atoms uses `sentencePrimcodable` (`Construction/LIACompiler.lean`);
`schedAtom_inj`, `signAtom_inj` and `schedAtom_ne_signAtom` make the decode unambiguous. -/
theorem computableMarket_cxPerturbed : ComputableMarket (cxPerturbed T) := by
  refine ⟨fun n φ => advicePerturbed_mem_Icc (theoremDP T) (cxDiagonal T)
    (fun m ψ => (LIA_isMachineLogicalInductor (theoremDP T)
      (theoremDP_computable T)).marketComputable.1 m ψ) n φ, ?_⟩
  -- TODO(thm:ifp): need the day-`0` quote program, by the route in the docstring above.
  sorry

/-! ## The witness, and the refutation -/

include T in
/-- The advice perturbation refuting `thm:ifp`, over any Σ₁-sound Δ₁ theory extending
`𝗜𝚺₁`.  Refutes rather than renders, so no `Paper node:` line.
Kind `C`; hypotheses `(a)`. -/
theorem exists_advice_perturbation_ofTheory :
    ∃ (P P' : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (Tr : Trader),
      IsMachineLogicalInductor P DP ∧ ComputableMarket P' ∧
      (∀ n, 1 ≤ n → ∀ φ, P n φ = P' n φ) ∧ MachineEfficientTrader Tr ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) ∧
      (∀ j, Dichotomy P' DP χ (sched P' DP χ j)) ∧
      (∀ (v : PCWorld) i, (∀ j, sched P' DP χ j ≠ i) →
        (Tr.strat i).value P' v.payout = 0) ∧
      (∀ (v : PCWorld) j, (Tr.strat (sched P' DP χ j)).value P' v.payout
        = roundValue P' χ v (sched P' DP χ j)) :=
  ⟨liaHistory (theoremDP T), cxPerturbed T, theoremDP T, cxDiagonal T,
    adviceTrader schedAtom signAtom (cxDiagonal T),
    LIA_isMachineLogicalInductor (theoremDP T) (theoremDP_computable T),
    computableMarket_cxPerturbed T,
    advicePerturbed_agree _ _ _,
    adviceTrader_efficient rpnSentenceCodes_schedAtom rpnSentenceCodes_signAtom
      (RpnSentenceCodes.ofPolySentenceCodes (cxDiagonal_poly T)),
    fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩,
    fun j => dichotomy_of_paradoxQuote (cxQuote T) (advicePerturbed_agree _ _ _)
      (one_le_sched _ _ _ j),
    fun v i hi => adviceTrader_value_off_sched schedAtom signAtom (cxDiagonal T) _ _
      (advicePerturbed_schedAtom_off _ _ _) v i hi,
    fun v j => adviceTrader_value_on_sched schedAtom signAtom (cxDiagonal T) _ _
      (advicePerturbed_schedAtom_on _ _ _) (advicePerturbed_signAtom_on _ _ _) v j⟩

include T in
/-- **The unrestricted finite-day perturbation statement is false**, over any Σ₁-sound Δ₁
theory extending `𝗜𝚺₁` — the negation of the paper's `thm:ifp` as printed, at the paper's
own quantifier.

**Depends on `sorryAx`** through `computableMarket_cxPerturbed`.  Everything else is
kernel-checked.  Refutes rather than renders, so no `Paper node:` line.
Kind `C`; hypotheses `(a)`. -/
theorem not_overgeneral_ifp_ofTheory :
    ¬ ∀ (P P' : History) (DP : DeductiveProcess) (N : ℕ),
        IsMachineLogicalInductor P DP → ComputableMarket P' →
        (∀ n, N ≤ n → ∀ φ, P n φ = P' n φ) → IsMachineLogicalInductor P' DP := by
  obtain ⟨P, P', DP, χ, Tr, hLI, hP', hagree, hTr, hworld, hdicho, hzero, hval⟩ :=
    exists_advice_perturbation_ofTheory T
  exact not_overgeneral_ifp_of_advice P P' DP χ Tr hLI hP' hagree hTr hworld hdicho
    hzero hval

/-- The advice perturbation refuting `thm:ifp`, closed at `𝗜𝚺₁` — which is `Δ₁`-definable
(`ISigma1_delta1Definable`), extends itself, and is Σ₁-sound because `ℕ ⊧* 𝗜𝚺₁`.  Refutes
rather than renders, so no `Paper node:` line.
Kind `C`; hypotheses `(a)`. -/
theorem exists_advice_perturbation :
    ∃ (P P' : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (Tr : Trader),
      IsMachineLogicalInductor P DP ∧ ComputableMarket P' ∧
      (∀ n, 1 ≤ n → ∀ φ, P n φ = P' n φ) ∧ MachineEfficientTrader Tr ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) ∧
      (∀ j, Dichotomy P' DP χ (sched P' DP χ j)) ∧
      (∀ (v : PCWorld) i, (∀ j, sched P' DP χ j ≠ i) →
        (Tr.strat i).value P' v.payout = 0) ∧
      (∀ (v : PCWorld) j, (Tr.strat (sched P' DP χ j)).value P' v.payout
        = roundValue P' χ v (sched P' DP χ j)) :=
  exists_advice_perturbation_ofTheory 𝗜𝚺₁

/-- **The unrestricted finite-day perturbation statement is false** — the negation of the
paper's `thm:ifp` as printed, at the paper's own quantifier, with no theory parameter.

**Depends on `sorryAx`** through `computableMarket_cxPerturbed`.  Refutes rather than
renders, so no `Paper node:` line.
Kind `C`; hypotheses `(a)`. -/
theorem not_overgeneral_ifp :
    ¬ ∀ (P P' : History) (DP : DeductiveProcess) (N : ℕ),
        IsMachineLogicalInductor P DP → ComputableMarket P' →
        (∀ n, N ≤ n → ∀ φ, P n φ = P' n φ) → IsMachineLogicalInductor P' DP :=
  not_overgeneral_ifp_ofTheory 𝗜𝚺₁



end FinitePerturbationCounterexample
end LogicalInduction
