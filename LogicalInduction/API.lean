import LogicalInduction.Properties
import LogicalInduction.Construction.Witnesses.FreezeOracle

/-!
# Logical Induction — the supported interface

```lean
import LogicalInduction.API
```

One import, and it is the whole interface for theoretical work over logical inductors: the
semantic objects of the paper's §2–3, the criterion at the paper's own quantifier, the §4
property library, and the two theorems that move the criterion from one market to another.
It stops short of the §5 existence construction, which is a separate import (below).

Nothing else needs to come with it.  In particular the write-out certificate layer
(`Framework/WriteOut`) arrives transitively, so its constructors — `BigSentenceCodes`,
`BigDigits`, `BigSpliceStream.ec` — are usable from this import alone.

## The objects

A **`Sentence`** is a propositional formula over Foundation's `Formula`; a **`History`** is
the market, a function from day and sentence to a price in `[0,1]`; a
**`DeductiveProcess`** is the day-indexed stream of what has been deduced, and a
**`PCWorld`** a propositionally consistent world completing it.  An **`EF`** is an
expressible feature (`dd:dsl`), a reified expression in prices and rationals with a
denotation; a **`Strategy`** is a day's finite list of (feature, sentence) trades; a
**`Trader`** is a day-indexed family of strategies, and `Trader.Exploits P DP` says its
holdings are bounded below and unbounded above across the plausible worlds — the paper's
notion of making unbounded money at no risk.  An **`AffineCombination`** is the affine
portfolio the §4 proofs price.  A **`LUV`** is a logically uncertain variable, presented by
its family of threshold sentences, with `LUV.expect` its market expectation.  The limit
vocabulary — `≈ₙ`, `≳ₙ`, `≲ₙ`, `ConvergesTo` — is owned by `Framework.Asymptotics`
(`dd:asymp`); do not redefine it downstream.

## Efficiency: one class, one certification route

The paper's `def:ec` is **ordinary machine polynomial time**, and so is the Lean rendering:

* `MachineEfficientTrader Tr` — some function in `Complexity.FP` maps the *unary* day `n` to
  a word decoding to `Tr`'s day-`n` strategy.  No fuel, no interpreter, no repository-local
  notion of cost.

To use that class you must exhibit a `Complexity.FP` witness, which is unpleasant by hand.
So there is a compositional certificate calculus, and exactly one bridge out of it:

* `EfficientlyComputable Tr` / `PolyFueled` (`dd:fuel`) ask for a `Nat.Partrec.Code` pair
  emitting the trade stream inside a polynomial fuel bound on Mathlib's `evaln`.  These are
  **certificates**, not a definition of efficiency.
* `EfficientlyComputable.toMachine : EfficientlyComputable Tr → MachineEfficientTrader Tr`
  is the bridge, proved through a real `evaln` → Turing-machine compiler.

So a fuel certificate is a *sufficient* route into the paper's class.  The converse is
neither proved nor claimed, and nothing paper-facing depends on it.  The constructors a
client actually builds with are `EfficientlyComputable.ofSingleTradeBlocksBig`,
`.ofSingleTradeBlocks` and `.ofTradeBlocks`, fed by the write-out sentence and datum classes
`BigSentenceCodes`, `BigDigits`, `DigitRatCodes`, `DigitMachineCodes` and the emission
classes `BigTokenStream` / `BigSpliceStream`.

## The criterion, and which of its two forms to state against

* `IsMachineLogicalInductor P DP` — `def:lic` over `MachineEfficientTrader`: a computable
  market and deductive process such that no polynomial-time trader exploits the market.
  **This is the paper-facing criterion**, and the one the §5 construction discharges.
* `IsLogicalInductor P DP` — the same criterion over the fuel-certified class.  It is the
  compatibility interface: the §4 property theorems are stated against it, and the instance
  `IsMachineLogicalInductor.toIsLogicalInductor` carries every one of them to a machine
  logical inductor unchanged.

The asymmetry is worth internalizing, because it determines how to state new results.  A
theorem *consuming* the criterion should take `[IsLogicalInductor P DP]`: such a statement is
automatically available at the machine class, while the reverse is not.  A theorem whose
*conclusion* is the criterion cannot use the instance at all — it must be stated at the
machine class directly, since the class has to be closed under the trader translation the
proof performs.  Both such theorems are below, at both classes.

## The §4 property library

Every `lic_*` family takes `[IsLogicalInductor P DP]` and holds of *every* logical inductor:
convergence and coherence, provability induction, timely learning (persistence of knowledge,
preemptive learning), calibration and unbiasedness, pseudorandomness, logical relationships,
non-dogmatism with its uniform and Occam forms, universal-semimeasure domination,
expectations, introspection, paradox resistance, and self-trust.  Names mirror the paper's
labels (`lic_provind` ↔ `thm:provind`).

## Moving the criterion between markets

**Conditioning (`thm:scon`).**  `lic_conditioned_machine`, `lic_conditioned_gated_machine`
and `lic_conditioned_eventual_machine` are the canonical forms; `lic_conditioned`,
`lic_conditioned_gated` and `lic_conditioned_eventual` are their fuel-class counterparts.
Neither set follows from the other, so both stand.

**Finite perturbation (`thm:ifp`).**  Read this one carefully, because the *printed* theorem
is false: a single changed pricing day is an infinite computable function, so it can carry
unbounded computational advice to an efficient trader.
`FinitePerturbationCounterexample.not_overgeneral_ifp` refutes the paper's unrestricted
statement (`notes/paper-errata.md`, PE1).

What holds — and what a client should use — is the finite-*support* correction, exported
here as `lic_iff_of_finiteSupportPerturbation_machine`: two `ComputableMarket`s differing at
only finitely many `(day, sentence)` price coordinates satisfy the criterion together, with
no certificate hypothesis (the freeze certificate is compiled from each market's own
computability certificate) and **no condition on the moved sentences**.
`FiniteSupportPerturbation` is its whole hypothesis, and
`FiniteSupportPerturbation.tail_agree` relates it to the paper's tail agreement (finite
support is strictly stronger — `tailAgree_not_finiteSupport` proves the converse fails, so
this theorem cannot re-derive the refuted printed one).
`lic_iff_of_noReservedSupportPerturbation` and
`lic_iff_of_recognizableSupportPerturbation` are the previous, weaker-reaching names, kept
for compatibility and now one-line corollaries.

No syntactic boundary travels with that theorem any more.  Both halves of the former
`Recognizable` condition stood for missing `Complexity.FP` devices, and both devices were
built rather than assumed away: `DigitFP.sqrtRemW_mem_FP` and `DigitFP.unpairW_spec` put
integer square root and `Nat.unpair` inside `Complexity.FP` and `FiberTest.fiberW_mem_FP`
builds the escape-leaf decode test on them (retiring `BotFree`), while `PayAuto` decides the
structured payload language of a fixed formula code and `CtrAuto.ctrMachine` decides the
structured block's `aⁿbⁿ` unary length field (retiring `NoReserved`).
`FreezeOracle.machine_lic_iff_hardPoint` and `FreezeOracle.machine_lic_iff_reservedPoint`
freeze coordinates at `atom 0 ⋏ ⊥` and at a reserved atom respectively — sentences the
earlier endpoints provably could not reach.  What is disclosed instead is a property of the
construction, not of the statement: the recognizer is compiled per frozen sentence, so its
polynomial-time constants depend on that sentence, which is sound exactly because the
support is finite.  And the fuel-class forms
`lic_iff_of_finitePerturbation` and `lic_iff_of_finiteSupportPerturbation` take patch
certificates (`EfficientPrefixPatch`, `FiniteSupportPatch`) that have **no inhabitant
anywhere in this repository**, because the fuel calculus does not close over the escape-leaf
decode the frozen lookup needs.  Use the machine form.

## Deeper imports, and when you need them

This import names no first-order theory, and deliberately so: the criterion and the §4 tail
name none either, and a client that never instantiates over a theory should not elaborate
the arithmetization.  When you do instantiate, three imports are the interface, in order:

* `LogicalInduction.Framework.RepresentsComputations` — the class `RepresentsComputations T`,
  the paper's standing §2 assumption that Θ represents computations, together with
  `represents_proves`, `represents_refutes`, `represents_refutes_all` and
  `RepresentsComputations.consistent`.  This is the hypothesis you supply about your theory.
* `LogicalInduction.Construction.Witnesses.R0Representability` — instances discharging it at
  `𝗣𝗔⁻`, `𝗜𝚺₁` and `𝗣𝗔`, so instantiating at one of those costs you nothing.
* `LogicalInduction.Construction.Witnesses.ComputationRepresented` — the endpoints stated at
  that premise over the single market `liaHistory (paperDP T)`.

Two further binders appear there beside the paper's own premise, and both are disclosed in
`LogicalInduction/README.md`: `[T.Δ₁]` (a `Δ₁`-definable axiom set — representation
infrastructure) and `[𝗣𝗔⁻ ⪯ T]` (a genuine, small strengthening).  `[𝗜𝚺₁ ⪯ T]` is asked for
by three endpoints only.  No endpoint asks for Σ₁-soundness.

For the §5 existence endpoints — `LIA`, `LIA_isMachineLogicalInductor`,
`exists_machine_logical_inductor` — import `LogicalInduction.Construction.LIACompiler`.  For
the `thm:ifp` refutation witness and the perturbed-`LIA` application, import
`LogicalInduction.Construction.Witnesses.FinitePerturbationWitness` and
`...Witnesses.LIAPerturbation`.  To build a new *literal* first-order LUV family, import
`...Witnesses.ArithmeticSource` for the source language.  `import LogicalInduction` takes
the whole development.

## Not interface

Lean makes transitively imported declarations visible; visibility is not a stability
promise.  Raw `Nat.Partrec.Code` manipulation, the register-machine simulator and its
compilers (`Framework/Machine/`), token and bit folds, RPN parsing internals, the freeze and
conditioning stream compilers, and the trader implementations inside the property proofs are
implementation, and may be renamed or restructured.

## Two representation interfaces you will meet

* **LUVs are threshold families.**  The `LUV` objects a client meets are rational threshold
  families over the propositional language, not first-order terms.  The paper's literal
  first-order object exists as `PaperLUV` — an actual one-variable arithmetic formula
  carrying object-level proofs — and compiles into the carrier, so results stated against the
  carrier apply to more families than the paper's.
* **`dd:mesh` and `thm:ccee`.**  `ConditionalExpectationQuote` carries a per-day reflection
  slack in its `slack` field.  That slack is the price of a *threshold-only* source: nothing
  in the abstract `LUV` interface names a value, so the quoted product can only be
  reconstructed from thresholds.  For the paper's **literal** first-order sources
  (`PaperLUVSeq`) the product is exact —
  `lic_no_expected_net_update_conditional_paperLUV_closed` states `thm:ccee` at `slack = 0`
  over the single market `liaHistory (paperDP T)`, like every other canonical endpoint.
  `lic_no_expected_net_update_conditional_exact_canonical` remains as the generalized
  semantic-extension form: exact for an *arbitrary* threshold-only source, but priced over a
  renamed deductive process.  `PaperLUVSeq` itself is a construction interface and is not
  re-exported here; import
  `LogicalInduction.Construction.Witnesses.PaperExactCCEE` to use the exact route.

`LogicalInduction/README.md` explains the modeling; `scripts/coverage-classification.md` and
`AxiomAudit.lean` carry the exact paper correspondence and the axiom accounting.
-/

namespace LogicalInduction

/-! The corrected finite-perturbation hypothesis and its atom witnesses, re-exported so
clients need not name the construction namespace they are defined in. -/

export FreezeOracle (NoReservedSupportPerturbation RecognizableSupportPerturbation
  recognizable_atom atom_zero_noReserved)

/-- **Closure under finite perturbations, corrected (`thm:ifp`).**

Two computable markets that differ at only finitely many `(day, sentence)` price
coordinates satisfy the logical induction criterion together, at the paper's own
quantifier.  This is the supported name for the result; it is definitionally
`FreezeOracle.machine_lic_iff_of_finiteSupport`, which is where it is proved.  The name
carries the `_machine` suffix because `lic_iff_of_finiteSupportPerturbation` is taken by the
*fuel-class* statement, which takes a patch certificate that has no inhabitant.

The paper's own statement — finitely many changed *days* — is **false**, and is refuted by
`FinitePerturbationCounterexample.not_overgeneral_ifp`; see `notes/paper-errata.md`, PE1.
Finite support is the natural repair, and is strictly stronger than the printed tail
agreement: `FiniteSupportPerturbation.tail_agree` gives one direction and
`tailAgree_not_finiteSupport` refutes the converse, so this theorem cannot re-derive the
refuted one.

`hpert` is the whole hypothesis on the perturbation, and there is no hypothesis at all on
the finitely many moved sentences: no `Recognizable`, no `BotFree`, no `NoReserved`, and no
freeze certificate.

Kind `C`; hypotheses `(a)`.
Paper node: `thm:ifp` -/
theorem lic_iff_of_finiteSupportPerturbation_machine (P P' : History) (DP : DeductiveProcess)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hpert : FiniteSupportPerturbation P P') :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP :=
  FreezeOracle.machine_lic_iff_of_finiteSupport P P' DP hPcomp hP'comp hpert

/-- A previous public name, kept so existing clients keep compiling.  Strictly weaker in
reach: `NoReservedSupportPerturbation` implies `FiniteSupportPerturbation`.

Kind `C`; hypotheses `(a)`.
Paper node: `thm:ifp` -/
theorem lic_iff_of_noReservedSupportPerturbation (P P' : History) (DP : DeductiveProcess)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hpert : NoReservedSupportPerturbation P P') :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP :=
  FreezeOracle.machine_lic_iff_of_noReservedSupport P P' DP hPcomp hP'comp hpert

/-- The oldest public name, likewise kept.  Strictly weaker in reach again:
`Recognizable` implies `NoReserved`.

Kind `C`; hypotheses `(a)`.
Paper node: `thm:ifp` -/
theorem lic_iff_of_recognizableSupportPerturbation (P P' : History) (DP : DeductiveProcess)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hpert : RecognizableSupportPerturbation P P') :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP :=
  FreezeOracle.machine_lic_iff_of_recognizableSupport P P' DP hPcomp hP'comp hpert

end LogicalInduction
