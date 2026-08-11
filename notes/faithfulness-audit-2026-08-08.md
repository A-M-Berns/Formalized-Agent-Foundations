# Faithfulness audit — LogicalInduction vs. arXiv:1609.03543v5 (2026-08-08)

Fresh, current-state audit of `LogicalInduction/`, `AxiomAudit.lean`, and the public
statement inventory at HEAD `bbef282`, against the paper source
`notes/1609.03543v5-main.tex`.

Completed by Codex using GPT-5.6 Sol.

This is a snapshot, not a continuation ledger. It assigns findings from the current
signatures and definitions only; it does not preserve old finding numbers, repair history,
or superseded diagnoses. The prior 2026-07-28 report was deleted as part of this pass.
Paper errata remain separate in `notes/logical-induction-paper-errata.md`.

## Scope and method

The audit checked four surfaces:

1. the Framework definitions for deductive processes, markets, traders, exploitation,
   efficient computability, the logical induction criterion, LUVs, expectations, affine
   combinations, deferral functions, and P-generability;
2. the final signatures carrying the paper's 53 named theorem/lemma nodes, paired with the
   corresponding paper statements;
3. the construction-backed discharges in `Construction/Witnesses/`, especially the main
   LIA, quotation, conditioning, feedback, semimeasure, computation, and self-trust chains;
4. mechanical trust: endpoint coverage, paper-label coverage, axiom reports, placeholders,
   and Tier-2 field inventory.

The adversarial questions were: Is a conclusion already assumed? Is an interface
uninhabited? Does a representation structure demand more than the paper? Is an efficient
object merely asserted rather than emitted? Does a concrete instantiation import an axiom
hidden by a parametric theorem? Does prose claim more than the signature proves?

Documentation style and proof-body elegance were out of scope. Proof bodies were opened
where needed to establish that a trader, emitter, bridge, or representation was genuinely
constructed rather than restated as a hypothesis.

## Mechanical state

At the audited HEAD:

* `lake build AxiomAudit` succeeds;
* `scripts/check-paper-nodes.sh` succeeds: 68 source labels are inventory-covered, with two
  appendix/internal exclusions;
* `python3 scripts/check_endpoint_coverage.py` succeeds;
* `python3 scripts/lint_paper_labels.py` succeeds;
* the 66 classified nodes consist of 31 `universal`, 29 `instantiated`, and 6 `qualified`;
  restricting to the paper's 53 named theorem/lemma nodes gives 31 `universal`,
  19 `instantiated`, and 3 `qualified`;
* the LogicalInduction library contains no `sorry`, no Lean `axiom` declaration, and no
  `native_decide`, `unsafe`, or `@[implemented_by]` escape;
* inventoried LogicalInduction endpoints use only `propext`, `Classical.choice`, and
  `Quot.sound`;
* one concrete arithmetic-instantiation probe additionally reports Foundation's named
  `ISigma1_delta1Definable` axiom, as expected and explicitly pinned.

## Verdict

The repository's current headline count is supported: **50 of the paper's 53 named
theorem/lemma nodes are reached at paper strength within the disclosed repository model;
three are qualified.** The three qualified nodes are `thm:ccee`, `thm:ifp`, and
`thm:wubexp`.

The main existence theorem is substantive. It constructs an explicit finite-support
rational belief-state sequence, one program emits the day-`n` association list, and the
induced market defeats the repository's full symbol-metered trader class. The construction
contains a real market maker, budgeter, universal trader enumeration, and trading firm; the
fixed-point dependency is proved in-repo through Sperner/Brouwer. No semantic
no-exploitation premise is passed into `LIA_is_logical_inductor`.

The result is not literally the paper's theorem without qualification at the model level:
the efficient-computability class is the disclosed fuel-clocked interpreter class, and no
lower-calibration theorem shows that it contains every polynomial-time trader admitted by
the paper. That qualification is visible in the criterion, model card, README, and
classification.

No new vacuous property theorem, conclusion-in-hypothesis squeeze, or arithmetic stub
standing in for an exploiting trader was found. The open debt is concentrated in the three
qualified theorem nodes and the two global modeling boundaries below.

## Findings

Severity **A** means the paper node must not be cited as fully formalized. **B** is a real
model/signature narrowing with useful theorems on both sides. **C** is a trust or disclosure
qualification that does not invalidate the parametric result.

### A1 — `thm:ifp` has no exhibited instance and the unrestricted paper theorem is not proved

The paper states closure under every finite perturbation of a computable market.
`lic_iff_of_finitePerturbation` instead takes two `EfficientPrefixPatch` certificates. The
interface's load-bearing field says that freezing the early price leaves preserves
`EfficientlyComputable` traders.

There is no inhabitant of `EfficientPrefixPatch` anywhere in the repository, including for
the constructed LIA. The RPN freeze transducer and its semantic correctness are built, but
the final fuel certificate is not. Consequently the retained premise is satisfiable only in
principle, not by any exhibited object, and the endpoint cannot currently be used to obtain
even one concrete finite-perturbation equivalence.

This is disclosed accurately in `Properties/FinitePerturbations.lean`,
`Construction/Witnesses/RpnFreeze.lean`, `AxiomAudit.lean`, the README, and the strength
table. The paper's own proof also has a separate efficiency gap (PE1): finitely many changed
days do not mean finitely many old sentence-price constants. That erratum explains why the
unrestricted theorem cannot simply be copied, but it does not turn the repository's
qualified endpoint into a full formalization.

**Required status:** qualified and presently without a non-vacuity witness. Do not cite it
as `thm:ifp` without that sentence.

### B1 — `thm:wubexp` still strengthens combination-level determination, and local prose oversells it

> **Resolved 2026-08-11, after this audit.** Both parts are closed and the node is
> reclassified `instantiated`. The prose fixes landed first. The construction followed the
> route recommended below (action 2): `FeedbackTruthSequence.zero_value` — exact
> zero-valuedness — is replaced by `value_vanishing`, the eventual-`ε` form that
> `affine_provind_theory_tendsto_zero` already suffices for, and
> `FeedbackTruth.feedbackTruthSequence` is generalized to `ApproxDeterminedViaTheory` with a
> vanishing residual. The mesh then supplies its own bridge through the pre-existing
> `WorldValued.normalizedMesh_approxDetermined` plus a new `meshErrorBound_tendsto_zero`, so
> `ExactTheoryPresentation` appears in no `thm:wubexp` endpoint and `wubexp_arith` now takes
> the paper's `FeedbackTruthComputation` rather than a pre-built bridge and emitter. The
> body below is preserved as the state this audit found.

The paper assumes that each LUV **combination** `A_n` is determined via the theory and that
its common value can be computed by the next feedback deadline. It does not require every
component LUV in the combination to be individually determined.

The analytic endpoint `LUVCombination.BoundedSequence.wubexp` uses the correct
combination-level `DeterminedViaTheory`, but it retains a `FeedbackTruthSequence` for the
normalized threshold mesh. The construction endpoint
`FeedbackTruth.luv_wubexp_ofComputation` builds that bridge only after assuming
`ExactTheoryPresentation As DP`. That structure fixes one completed-theory value for every
component LUV, which is strictly stronger than determination of the signed combination.
For example, a combination containing `+X` and `-X` is theory-determined even when `X`
itself is not; such a sequence need not admit `ExactTheoryPresentation`.

The alternative `wubexp_arith` endpoint avoids `ExactTheoryPresentation` in its signature
but retains the normalized-mesh `FeedbackTruthSequence` directly. Thus no current endpoint
derives the paper theorem from only combination determination plus a deadline-bounded
program for the combination's truth values.

The repository-level README and classification disclose this correctly. Some local
docstrings do not:

* `LUVExpectationCertified.lean` calls the retained `bridge` the paper's computation
  premise and says it is constructed in `FeedbackTruth.lean`, although `wubexp_arith`
  accepts that bridge as an argument;
* `FeedbackUnconditional.lean` calls `ExactTheoryPresentation` one of the paper's explicit
  semantic inputs, which it is not.

Those statements should be corrected even before the missing construction is attempted.

**Required status:** qualified. The theorem's economic/trader core is real; the remaining
gap is the route from the paper's operational premise to the mesh feedback bridge.

### B2 — `thm:ccee` uses a vanishing-slack product; the exact route is not closed

The paper names exact quoted products `X_n * w_{f(n)}` and
`E_{f(n)}(X_n) * w_{f(n)}`. The closed repository endpoint
`lic_no_expected_net_update_conditional_closed` handles the paper's arbitrary e.c. source
family and P-generable weight, but its left product is a finite threshold mesh whose value is
within `1/(n+1)` of the product. `ConditionalExpectationQuote.left_reflected` therefore
contains a vanishing `slack`, not equality.

This does not weaken the final asymptotic equation: the added error tends to zero and is
absorbed by the proof. It does change the represented quoted object, so it is a genuine
type-`(c)` modeling substitution rather than an exact rendering of the paper's term.

`ProductDefinition.lean` now constructs the important parts of an exact route: a computable
definitional-extension process, fresh product atoms, world extension, exact product
valuation, threshold emission, and `lic_no_expected_net_update_conditional_exact` at zero
slack. That endpoint still assumes a logical inductor over the extended process, an
atom-freshness/representation package, and a deferred-weight LUV with the required exact
world value. It is not a closed replacement for the mesh endpoint over the constructed LIA.

**Required status:** qualified. The current local and repository-level disclosures are
accurate.

### B3 — `def:ec` is calibrated in only one direction

`EfficientlyComputable` is not a conventional machine-time complexity predicate. A pair of
Mathlib `Nat.Partrec.Code` programs emits the digit stream of an RPN strategy under a
polynomial `evaln` fuel clock. The repository proves useful internal calibration:
token/digit round trips, symbol-length bounds, fuel-polynomial closure facts, and separation
from whole-Godel-value metering.

What it does not prove is the lower-calibration direction needed for literal equivalence
with the paper: every polynomial-time strategy generator in the paper's model belongs to
`EfficientlyComputable`. Therefore `thm:li` defeats the fuel class, not a proved superset of
the paper's trader class. If the fuel class is smaller, the Lean existence theorem is
weaker. For the property tail the risk is mostly conservative because each exploit used in
the proof is explicitly emitted inside the class; `thm:ifp` is the load-bearing exception.

The paper permits alternative efficiency notions, so this is a legitimate neighboring
logical-induction framework. It is still a qualification on claims of literal equivalence,
and the repository correctly classifies `def:ec` as qualified.

### B4 — `def:luv` is a threshold-family interface, not a first-order term

The repository's `LUV` contains only `gt : ℚ → Sentence`. Monotonicity, existence of
a world value, connection to a computation-representing theory, and compact emission are not
fields of the bare type. They enter through `ValuesAt`, `WorldValued`,
`ExactTheoryPresentation`, syntax/emission certificates, or the certified arithmetic LUV
construction.

This abstraction is appropriate for the propositional substrate and most endpoints quantify
over exactly the world-value behavior the paper uses. It nevertheless admits arbitrary
threshold families that are not paper LUVs. Only the `dd:luv-arith` class supplies a concrete
first-order bridge. The qualification propagates to `def:blcp`; it does not independently
lower every expectation theorem whose signature includes the paper's required world-value
premise.

The boundary is disclosed consistently. `thm:ccee` is its one current theorem-level modeling
consequence.

### C1 — concrete arithmetic instantiation inherits one upstream Foundation axiom

The parametric arithmetic endpoints assume `[T.DeltaOne]`, `[ISigma1 <= T]`, and the required
soundness class, and their axiom reports are clean. Instantiating them at Foundation's
concrete `ISigma1` uses `ISigma1_delta1Definable`, declared upstream as an axiom/TODO.

`AxiomAudit.lean` makes this visible with an exact `#assert_axioms_clean_except` probe. This is
not an undisclosed axiom in the LogicalInduction proofs, but concrete arithmetic claims must
retain the upstream qualification until Foundation proves that instance.

## Paper-strength surface verified

Subject to `def:ec` and `def:luv` being read with the global disclosures above, the following
parts match the paper at statement level:

* the core market, trader, strategy, plausible-assessment, exploitation, and criterion
  definitions; the exploitation predicate is non-vacuous (`Trader.zero_not_exploits`);
* `thm:li`/`thm:lia`, including computable emission of explicit finite belief states;
* convergence, limit coherence, provability induction, timely learning, persistence,
  preemptive learning, affine coherence, affine provability, and affine persistence;
* non-dogmatism, uniform non-dogmatism from a c.e. source, Occam bounds at an actually
  universal prefix machine, and the universal-semimeasure domination/strict-domination
  statements for arbitrary presented independent atoms;
* fixed and growing conditioning, including the inconsistent/vacuous branch and the
  propositional-compactness route for the growing form;
* expectation convergence, linearity, expectation provability, expectation coherence,
  mesh independence, recurring unbiasedness, and pseudorandom expectation learning, except
  for `thm:wubexp` as stated in B1;
* the metamathematical computation family, including the paper's arbitrary computable
  horizon `f` through `ComputableHorizon` rather than a polynomial-growth restriction;
* introspection, paradox resistance, expectations of probabilities, iterated expectations,
  expected future expectations, no expected net update, and self-trust; `thm:ccee` has the
  B2 representation qualification.

The input-free `thm:dus` and `thm:strict` witnesses use the constantly empty deductive
process. That is a weak concrete example, but not a weakening of the universal endpoints,
which quantify over arbitrary deductive processes and presented independent atoms. They are
correctly classified `universal`, not `instantiated`.

## Final accounting

| surface | paper strength | qualified | qualification |
|---|---:|---:|---|
| named theorem/lemma nodes | 50 | 3 | `thm:ccee`, `thm:ifp`, `thm:wubexp` |

As of 2026-08-11 the first row reads 51 / 2 (`thm:ccee`, `thm:ifp`): `thm:wubexp` was
closed after this audit — see the resolution banner on B1.
| classified definition nodes | 10 | 3 | `def:ec`, `def:luv`, and derivative `def:blcp` |

This accounting is relative to the repository model. It does not erase the global
`def:ec` or propositional-LUV disclosures merely because a downstream theorem has the same
analytic conclusion as the paper.

## Recommended next actions

1. ~~Correct the two `thm:wubexp` local docstring overclaims immediately.~~ Done
   2026-08-11.
2. ~~For `thm:wubexp`, construct a feedback bridge from a deadline-bounded computation of
   the combination truth plus the existing vanishing mesh error, without
   `ExactTheoryPresentation`.~~ Done 2026-08-11, by exactly this route; see B1.
3. Keep `thm:ifp` visibly qualified until an `EfficientPrefixPatch` inhabitant exists; do
   not treat the paper erratum as a proof of the restricted premise.
4. Treat the exact `thm:ccee` definitional-extension endpoint as infrastructure, not the
   paper-facing closed endpoint, until the extended-process inductor/weight circle is closed.
5. Retain the concrete arithmetic axiom probe until Foundation discharges
   `ISigma1_delta1Definable`.

---

## Delta since this pass — `thm:ccee`, the exact-product route (2026-08-11)

_Appended after the audit, not part of it. The audit's B2 finding and its "required status:
qualified" verdict are unchanged; what changed is that the route B2 describes as unbuilt is
now built, on two decisions that are **PROVISIONAL** — not ratified by the human
read-through — and that therefore do not move the row._

B2 says: "`ProductDefinition.lean` now constructs the important parts of an exact route …
It is not a closed replacement for the mesh endpoint over the constructed `LIA`." It now is
one, `lic_no_expected_net_update_conditional_exact_closed`. What that costs, stated against
the audit's own criteria:

* **Not a squeeze, not a stub.** The exact reflection is `productLUV_valuesAt`, proved from
  density of ℚ in both factors against the defining schema, and it feeds
  `ConditionalExpectationQuote.left_reflected` at `slack ≡ 0`. No hypothesis of the endpoint
  is its own conclusion.
* **Non-vacuity is by the construction.** `exactProductDP_hworld` extends the base
  construction's *own* plausible world (`provabilityWorld T`, the witness
  `theoremDP_hworld` already exhibits) through the product atoms, using the least assignment
  closed under the positive clauses. There is no stand-in witness and no constant sequence.
  The joint satisfiability of the *whole* premise set — the two paper-absent premises
  included — is separately exhibited by
  `lic_no_expected_net_update_conditional_exact_closed_nonvacuous`, at a provably
  non-constant weight and a source family whose day-`n` LUV is a distinct atom family.
* **The circularity B2 names is broken, not assumed away.** The weight's quote LUV is built
  against the **base** market, which exists before the extended process does; the
  certificate's `weight_generable` field is then supplied by a second `def:pgen` premise
  about the extended market.
* **Two premises the paper does not state**, both type-`(c)` and both disclosed at the
  statement, in `LogicalInduction/README.md` and in `scripts/coverage-classification.md`:
  the second P-generability premise just described, and `ProductAtomFresh X` — with a
  first-order signature the product's new function symbol makes freshness automatic, and a
  flat propositional atom space must state it. The latter is discharged by construction
  (`arithmeticThresholdLUV_productAtomFresh`, `theoremDP_atomCodes_ne_productTag`) for every
  family this repository builds, so it is not vacuous.
* **A different market in the conclusion.** The endpoint is stated over
  `theoremDP T ∪ productDefDP`, not `theoremDP T`. This is the decision an adversarial
  reader should press on hardest, and it is the one a fresh-context audit should re-derive
  independently rather than take from this note.

**Required status: unchanged — qualified.** Recommended next action 4 above ("treat the
exact endpoint as infrastructure, not the paper-facing closed endpoint, until the extended
process inductor/weight circle is closed") is now actionable rather than blocked: the circle
is closed, and what remains is a ruling, not an obstruction.
