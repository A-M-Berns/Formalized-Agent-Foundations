import LogicalInduction.Properties
import LogicalInduction.Construction.Witnesses.FreezeOracle

/-!
# Logical Induction consumer API

The recommended import for research that builds on the logical-induction framework:

```lean
import LogicalInduction.API
```

It gives the paper's criterion at the paper's own quantifier, the §4 property tail, and
the two transport theorems whose conclusions *are* the criterion (conditioning and the
corrected finite-perturbation theorem).  It stops short of the §5 existence construction.

## The criterion, at the paper's own quantifier

Two declarations carry the trust surface, and clients should reach for them first:

* `MachineEfficientTrader` — `def:ec`.  A trader is efficient when some function in
  `Complexity.FP` maps the *unary* day `n` to a word that decodes to its day-`n` strategy.
  Ordinary machine polynomial time; no fuel, no interpreter.
* `IsMachineLogicalInductor` — `def:lic` over that class: a computable market and
  deductive process such that no `MachineEfficientTrader` exploits the market.  This is
  the criterion the LIA construction discharges.

Everything else in this file's efficiency vocabulary exists to serve those two.

## Certification and compatibility machinery

`MachineEfficientTrader` is a semantic class: to use it you must exhibit a
`Complexity.FP` witness.  Two devices help.

* `EfficientlyComputable` / `PolyFueled` (`dd:fuel`) are **certificates**, not a
  definition of efficiency.  They ask for a `Nat.Partrec.Code` pair emitting the trade
  stream inside a polynomial fuel bound on Mathlib's `evaln`, and
  `EfficientlyComputable.toMachine` proves every such certificate lands in
  `MachineEfficientTrader`.  So a fuel certificate is a *sufficient* route into the
  paper's class.  The converse is not proved and is not claimed; nothing paper-facing
  depends on it.  The high-level constructors clients actually use —
  `RpnSentenceCodes`, `RpnSpliceStream.ec`,
  `EfficientlyComputable.ofSingleTradeBlocks` / `.ofTradeBlocks` — build these
  certificates.
* `IsLogicalInductor` is the **compatibility predicate**: the same criterion stated over
  the fuel-certified class.  The §4 property theorems are all stated against it, and the
  instance `IsMachineLogicalInductor.toIsLogicalInductor` carries every one of them to a
  machine logical inductor unchanged (a machine logical inductor *is* a fuel-class one,
  because every fuel certificate is a machine certificate).  Clients writing new
  consequences of the criterion should state them against `[IsLogicalInductor P DP]` for
  exactly this reason: such a statement is automatically available at the machine class,
  while the reverse would not be.

The one place the instance does not suffice is a theorem whose *conclusion* is the
criterion, since there the class must be closed under a trader translation.  Both such
theorems are stated separately at the machine class; see below.

## Supported surface

**Framework.**  `Sentence`, `History` (markets), `PCWorld`, `DeductiveProcess`, `EF`
(expressible features, `dd:dsl`), `Strategy`, `Trader`, `Trader.Exploits`,
`AffineCombination`, `LUV` and expectations, and the shared asymptotic relations
(`≈ₙ`, `≳ₙ`, `≲ₙ`, `ConvergesTo`) owned by `Framework.Asymptotics` (`dd:asymp`).

**Properties (§4).**  The `lic_*` families: coherence and convergence, provability
induction, timely learning, calibration, pseudorandomness, logical relationships,
non-dogmatism and its uniform and Occam forms, universal-semimeasure domination,
expectations, introspection, and self-trust.  Each takes `[IsLogicalInductor P DP]`.

**Closure under conditioning (`thm:scon`).**  `lic_conditioned`,
`lic_conditioned_gated`, `lic_conditioned_eventual` at the fuel class, and
`lic_conditioned_machine`, `lic_conditioned_gated_machine`,
`lic_conditioned_eventual_machine` at the machine class.  The machine forms are the
canonical ones; the fuel forms are neither derivable from them nor they from it, so both
stand.

**Closure under finite perturbations (`thm:ifp`).**  Read this one carefully, because the
printed theorem is false.

* `FinitePerturbationCounterexample.not_overgeneral_ifp` **refutes** the paper's
  unrestricted statement.  It lives in
  `Construction/Witnesses/FinitePerturbationWitness.lean` (its abstract half,
  `not_overgeneral_ifp_of_advice`, is here); `notes/paper-errata.md` PE1 is the ledger.
* `FiniteSupportPerturbation P P'` — the two markets differ at only finitely many
  `(day, sentence)` price coordinates — is the corrected hypothesis, strictly stronger
  than the paper's tail agreement (`FiniteSupportPerturbation.tail_agree` gives one
  direction; the converse fails).  `lic_iff_of_finiteSupportPerturbation` and
  `machine_lic_iff_of_finiteSupportPerturbation` carry it, each taking a freeze
  certificate per market.
* `FreezeOracle.machine_lic_iff_of_recognizableSupport` is **the statement to use**: two
  `ComputableMarket`s and a `RecognizableSupportPerturbation` — finite support plus a
  syntactic `Recognizable` condition on the finitely many sentences whose price moves —
  and no certificate hypothesis at all, because the freeze certificate is compiled from
  each market's own computability certificate
  (`FreezeOracle.machineFiniteSupportPatch_ofRecognizable`).
* `lic_iff_of_finitePerturbation` is the older fuel-class form, and it retains an
  explicit `EfficientPrefixPatch` hypothesis.  See the honest boundaries below.

This is the one place the API reaches into `Construction/Witnesses/`, and it does so for
a statement rather than for machinery: the corrected `thm:ifp` and its own hypothesis are
defined in `FreezeOracle.lean`.

## What is deliberately not advertised

Lean makes transitively imported declarations visible, but visibility is not a stability
promise.  The following are implementation, not interface, and clients should not depend
on them: raw `Nat.Partrec.Code` manipulation, the register-machine simulator and its
compilers (`Framework/Machine/`), token and bit folds, RPN parsing internals, the
freeze and conditioning stream compilers, and the trader implementations inside the
property proofs.

For the §5 existence endpoints (`LIA`, `LIA_isMachineLogicalInductor`,
`exists_logical_inductor`) import `LogicalInduction.Construction.LIACompiler`.  For the
`thm:ifp` refutation witness and the informative `LIA` perturbation import
`LogicalInduction.Construction.Witnesses.FinitePerturbationWitness` and
`LogicalInduction.Construction.Witnesses.LIAPerturbation`.  Import `LogicalInduction`
when the whole development is wanted.

## Honest boundaries carried into client code

* **The fuel-class certificates for `thm:ifp` are uninhabited.**  `EfficientPrefixPatch`
  and `FiniteSupportPatch` have no inhabitant anywhere in this repository, because the
  fuel calculus does not close over the escape-leaf decode the frozen lookup needs
  (`dd:fuel`).  `lic_iff_of_finitePerturbation` and `lic_iff_of_finiteSupportPerturbation`
  therefore have no exhibited witness for their certificate hypotheses.  This API neither
  manufactures one nor hides that.  The *machine*-class certificate is discharged, which
  is why the machine statement above is the one to use.
* **`Recognizable` is representation residue.**  It constrains the syntax of the moved
  sentences, not the markets, traders, or the perturbation.  Its two halves stand for two
  `Complexity.FP` primitives this repository lacks (integer square root; a
  structured-payload parser); the boundary note at the end of `FreezeOracle.lean` names
  them.  The unrestricted finite-*support* statement is, as far as this development can
  tell, true, and is unproved here.
* **`dd:mesh` is not the strongest `thm:ccee`.**  `ConditionalExpectationQuote` carries a
  per-day reflection slack, and the mesh reading realizes the quoted product on a finite
  mesh of threshold atoms, reflecting it only to within `1/(n+1)`.  Statements that use
  that reading carry the slack explicitly in the `slack` field.  The closed exact endpoint
  `lic_no_expected_net_update_conditional_exact_canonical`
  (`Construction/Witnesses/SemanticLiftedCCEE.lean`) instantiates `slack` at the constant
  `0` over an arbitrary threshold-certified source family, so exactness is available — but
  the two are incomparable rather than one superseding the other: the mesh endpoint speaks
  about the market `liaHistory (theoremDP T)`, the exact one about
  `liaHistory (canonicalCCEEDP T)` over a renamed and registry-closed process.  Choose by
  which market the client needs to reason about, not by which has less slack.
* **The propositional substrate.**  LUVs are presented by rational threshold families
  over a propositional language, not by first-order terms.

`LogicalInduction/README.md` is the authoritative disclosure record and `AxiomAudit.lean`
the checked endpoint inventory; the `dd:fuel` model card in `Framework/Computable.lean`
records exactly what the fuel model does and does not settle.
-/
