# Logical Induction — handoff

_Last updated: 2026-07-22 (session 3). Branch: `logical-induction`._

## ✅ Session 3 summary (2026-07-22) — feedback and LUV complete over constructed LIA

The last property-tail instantiation is complete. `FeedbackUnconditional.lean` adds four
strictly axiom-clean endpoints over `liaHistory (theoremDP T)`:

- `lic_wub_ofComputation_unconditional` (`thm:wub`);
- `lic_wubaff_ofComputation_unconditional` and
  `boundedCombination_wubaff_ofComputation_unconditional` (`thm:wubaff`); and
- `luv_wubexp_ofComputation_unconditional` (`thm:wubexp`, completing the deferred LUV path).

The spike resolved in the cheap direction: **no feedback-specific deductive process is
needed.** `FeedbackTruthComputation` is the paper's explicit deadline-bounded program for
completed-theory values, not a presentation of literals that a DP must enumerate. The existing
`theoremDP` therefore discharges every missing market-side premise: it is computable,
`LIA_is_logical_inductor` supplies the inductor, `liaHistory_range` supplies probability bounds,
and `theoremDP_hworld` supplies finite-stage plausible worlds. The caller appropriately retains
the paper's substantive affine/LUV determination, weighting, deferral, and delayed-value program
premises.

The ordinary-sentence specialization was also closed: `FeedbackTruth.lic_wub_ofComputation`
now constructs both feedback boundaries for `thm:wub`, matching the existing affine and LUV
consumers. All eight generic/unconditional feedback consumers are in `AxiomAudit.lean`.
Full build green (2723 jobs); `AxiomAudit`, paper-node validation, theorem-label lint, and
`git diff --check` all pass.

**Next focus:** verification phase — full build and repository gates, then the deferred human
statement read-through / fresh `M7-ERRATA-AUDIT` pass. After that, the orthogonal `dd:fuel`
hardening remains before the stronger “fully done” claim.

## ⏱ Session 2 summary (2026-07-22) — property tail largely unconditional over LIA

Full build green throughout (2720 jobs), strictly axiom-clean, all label/node gates pass.
Landed this session (commits `f79807d`…`1d24ad1`):

- **Quotation / self-reference — DONE, all 3 steps.** Code-indexed redesign kills the vacuity;
  `quotation_presentation_nonvacuous` certifies `Q ∧ hworld`; all **8** endpoints unconditional
  over `LIA` (`*_unconditional` in `ComputationDP.lean`).
- **Meta-learning — DONE, 6/6.** The 5 siblings joined the halting MVP (`ComputationDP.lean`).
- **Universal semimeasure — DONE** and **Conditioning — DONE** over `LIA`
  (`UnconditionalOverLIA.lean`; empty process proved computable, `hworld` trivial).
- **`dd:fuel`** unit-cost seam recorded in the roadmap: an option-A bit-cost hardening over
  `Framework/Computable.lean` is **owed before "fully done"** (poly-fuel ⊋ poly-time; the
  equivalence is appealed to, not proved). Consolidation-phase, orthogonal to the tail.

**Key reframe established this session:** the central `LIA_is_logical_inductor` (Layer 1) is
**already proved, unconditional, strictly axiom-clean, build-enforced** — only needs the
satisfiable `ComputableDeductiveProcess DP`, discharged concretely by `theoremDP`/`emptyBit`.
There is *no* remaining proof-engineering gap in the criterion theorem; what's left there is
trust-surface work (read-through fidelity to Def 4.1.2 + the `dd:fuel` seam), not proving.

**Remaining proof engineering:** feedback and LUV are now complete (session 3); the entire
property tail is instantiated over constructed `LIA` processes, bracketing the three disclosed
boundaries. Next comes the verification phase (read-through + `M7-ERRATA-AUDIT`, including a
fresh pass over the changed quotation surface), then the orthogonal `dd:fuel` hardening.

**External:** Kraft Aristotle — first attempt (`bc2df18a…`) FAILED (returned `sorry`); resubmit
`65eaafaa-2ba0-4501-8002-8e9e2043f4d8` RUNNING at handoff (poller task `b7q730kzu`). Even a
proof only removes step 1 of 5 for the *disclosed* `M7-PREFIX-MACHINE`.

**Pre-publish:** delete `LogicalInduction/IntegrationTest.lean` before publication (Anson;
recorded in `notes/consolidation.md`). It is the M3 deference-corpus integration/regression
guard — keep it until then.

---

## ✅ M7-QUOTE-DP meta-learning MVP — DONE (2026-07-22)

The **M7-QUOTE-DP meta-learning MVP is complete** and merged (commits `ad80bd3`, `671f8c1`,
unpushed). `LogicalInduction/Construction/Witnesses/ComputationDP.lean` delivers the
project's first genuinely **unconditional, strictly axiom-clean** epistemic result over the
constructed `LIA` inductor:

> `lia_learns_halting_patterns_unconditional` (Paper node `thm:halts`) — for a Σ₁-sound
> `T ⊇ 𝗜𝚺₁`, the constructed `LIA` over a **constructed, proved-computable** provability
> deductive process learns every provably-halting pattern, with **no** market/price/`hworld`
> hypotheses remaining. `hworld` is *proved* (from `T`-consistency + Σ₁-soundness), not assumed.

What landed (all axiom-clean — `propext`/`Classical.choice`/`Quot.sound` only):
- **Tall pole A** `provable_instances_re`: `REPred (fun z => T ⊢ φ/[z])` from FFL's
  `Halting.lean` template (`definability` + `re_iff_sigma1` + `Theory.Provable.sound` +
  `internalize_provability`).
- A single combined event stream (tags 0–5), r.e. via `provable_instances_re` + `REPred`
  closure; `theoremDP` enumerates fired atoms with a fuel-clocked dovetailer.
- `theoremDP_covers` (coverage → all six enters/refutes fields) and `theoremDP_hworld`
  (the non-vacuity heart: one provability world consistent with every stage).
- **Tall pole B** `theoremDP_computable`: the enumerator is primitive recursive
  (`encode_toFinset_eq` + `eventAtom_prim` 6-way encoder + `listFilterMap`/`primrec_evaln`
  + `sentenceDedup_prim`/`sentenceInsertionSort_prim`). Full build green (2720 jobs).

**Scope note carried out as planned:** computation side only. The *quotation* side remains
blocked by the vacuity obstruction (below) and still needs a frozen-boundary redesign.

---

# ✅ QUOTATION RESCUE — COMPLETE, all 3 steps (2026-07-22)

The quotation family is **fully unconditional over the constructed `LIA`** — vacuity fixed,
certified, and all eight endpoints instantiated (`logical-induction`, full build green, 2720
jobs, strictly axiom-clean). **Step 3 done:** `lic_introspection_ofCode_unconditional`,
`lic_paradox_resistance_ofDiagonal_unconditional`, `lic_expectations_of_probabilities_ofCode_unconditional`,
`lic_iterated_expectations_ofCode_unconditional`, `lic_self_trust_ofRepresentation_unconditional`,
`lic_expected_future_expectations_ofRepresentation_unconditional`,
`lic_no_expected_net_update_ofRepresentation_unconditional`,
`lic_no_expected_net_update_conditional_ofRepresentation_unconditional` (all in
`ComputationDP.lean`) discharge market / `IsLogicalInductor` / `Q` / `hworld` via
`quotationPresentation` + `theoremDP_hworld` + `LIA_is_logical_inductor` + `liaHistory_range`;
only the caller's quoted decision + reflection data remain. Steps 1–2 detail below.

## Steps 1–2 (redesign + certify) — DONE

The quotation-side vacuity is **fixed and certified** (full build green, strictly axiom-clean).
What landed:

- **Redesign (code-indexed), step 1.** `QuotationTheoryPresentation`'s two quote fields no
  longer quantify over free schema pairs. They are now keyed by a selector `code : ℕ` and
  `input`, with two **fixed** universal schemas `universalQuotePos`/`universalQuoteNeg`
  (`= codeOfREPred` of the value-1 / value-0 fibers of the universal computation, folded pair
  `⟨code,input⟩`). The `⊤,⊤` attack can no longer be phrased (schemas fixed & complementary).
  Field **names unchanged** ⇒ `#assert_fields QuotationTheoryPresentation` still frozen; the
  disclosed change is in field **types**. `BooleanQuoteCode`/`RationalQuoteCode`/
  `ParameterizedDiagonalQuoteCode` re-shaped to carry `code` (+ completeness data);
  `#assert_fields` for those three re-frozen in `AxiomAudit.lean`. `ArithmeticDecision`
  (now dead) removed. Diagonal decoupled per plan (`represents_fixedpoint` faithfulness cert;
  `diagonal_law` restated about `parameterizedFixedpoint body` directly).
- **Construction + `hworld` (certify the fix), step 2.** The **same** computable `theoremDP`
  (`ComputationDP.lean`) now also enumerates the quotation atoms (event tags 6/7), so it
  inhabits the redesigned `QuotationTheoryPresentation` (`quotationPresentation`) **and**
  `theoremDP_hworld` covers tags 6/7 (positive: coverage; negative: determinism/fiber
  exclusivity via `re_complete`). `quotation_presentation_nonvacuous` is the explicit `N+`
  certificate: `∃ DP, ∃ (_ : QuotationTheoryPresentation DP T), ∀ n, ∃ v, v.ConsistentWith
  (DP.D n)` — i.e. `Q ∧ hworld` is satisfiable. Vacuity gone.

**Disclosure owed & recorded (type-`(c)`-adjacent narrowing, `dd:quote-code`):** quotation now
only quotes **computable/decidable decisions of the market state** (selector `code` decodes to
a total `{0,1}` decider; positive = value-1 fiber, negative = value-0 fiber). This is *not* a
new semantic restriction — the paper's dual-schema `ArithmeticDecision` already required dual
weak representation (= decidability). It *is* a real modeling commitment on the presentation.
The interface stays general over any `DP`/`T`; only the quotable-decision class is fixed. See
docstrings in `QuotationAffine.lean` (`universalQuotePos`/`BooleanQuoteCode`) and
`ComputationDP.lean` (`quotationPresentation`).

**Remaining (step 3, follow-on):** instantiate the `_ofCode`/`_ofDiagonal`/`_ofRepresentation`
endpoints over `liaHistory (theoremDP T)` — `_unconditional` corollaries for introspection /
self-trust / expectations / paradox resistance. This is now unblocked (a real `Q ∧ hworld`
exists over the constructed LIA DP); it is corollary plumbing, not a construction. Note the
diagonal instantiation still *uses* the fixed point to build `truth_spec` (breaking the
`truth n ↔ price(atom n) < p` circularity), per the resolved diagonal wrinkle below.

---

# 🎯 (superseded) THE NEXT FOCUS — quotation / self-reference non-vacuity rescue

Anson's next focus (2026-07-22). The introspection / self-trust / expectation-representation /
paradox-resistance family (`M7-QUOTE-AFFINE`, endpoints `lic_introspection_ofCode`,
`lic_paradox_resistance_ofDiagonal`, `lic_self_trust_ofRepresentation`,
`lic_expectations_of_probabilities_ofCode`, `lic_iterated_expectations_ofCode`, the
`_ofRepresentation` net-update endpoints) was **vacuous** and needed rescue before
it can be made unconditional over `LIA`. **Steps 1–2 are now DONE (see the section above);**
this analysis is retained for the step-3 instantiation and the diagonal handling.

### The exact obstruction

`QuotationTheoryPresentation` (`QuotationAffine.lean:103–114`) has two fields quantifying over
**two independent, arbitrary schemas**:

```lean
quote_positive_enters : ∀ (positive negative : ArithmeticSemisentence 1) (input : ℕ),
    T ⊢ positive/[↑input] → ∃ k, quotationClaimSentence positive negative input ∈ DP.D k
quote_negative_refutes : ∀ (positive negative : ArithmeticSemisentence 1) (input : ℕ),
    T ⊢ negative/[↑input] → ∃ k, (∼quotationClaimSentence positive negative input) ∈ DP.D k
```

The atom is keyed on **both** schemas; the positive literal fires from `T ⊢ positive/[i]`, the
`∼` of the *same atom* from `T ⊢ negative/[i]`, and nothing ties the two schemas together. Take
`positive = negative = ⊤`: `T ⊢ ⊤/[i]` is trivial, so both fire on `X = quotationClaimSentence
⊤ ⊤ i`, forcing `X` and `∼X` into a common stage (by `mono`) ⇒ no consistent world ⇒
`Q ⟹ ¬hworld`. So `(Q ∧ hworld)` is unsatisfiable and every consuming endpoint is vacuously
true. (Computation escapes this: its enters/refutes quantify over the **input only**, with
**fixed** complementary schemas, so both-firing means `T` proves a Σ₁ statement and its
standard-model complement — killed by Σ₁-soundness. Quotation lost that guardrail by freeing
the pair.) Note the consumers **never use** the freedom: every call site passes
`q.decision.positive, q.decision.negative` from an `ArithmeticDecision`, which already bundles
complementarity (`positive_standard`/`negative_standard`). The bad field simply promises more
than any consumer needs. See [[quotation-presentation-vacuity]].

### The rescue = two coupled moves (need both)

- **(A) Boundary redesign** kills the *vacuity* (makes `Q ∧ hworld` satisfiable).
- **(B) Construction** builds a concrete quotation DP, proves its `hworld`, inhabits the
  redesigned `Q`, and instantiates over `liaHistory` — making the endpoints *unconditional*.

### Recommended redesign — mirror the MVP (index by predicate code)

Make quotation structurally identical to computation: **fix the schema-former to
`codeOfREPred` and index enters/refutes by a predicate code + input**, not arbitrary schemas.

```lean
-- pos code = codeOfREPred (decode code); neg code = codeOfREPred (¬ decode code)
quote_positive_enters : ∀ (code input : ℕ),
    T ⊢ (quoteSchemaPos code)/[↑input] →
      ∃ k, quotationClaimSentence (quoteSchemaPos code) (quoteSchemaNeg code) input ∈ DP.D k
quote_negative_refutes : ∀ (code input : ℕ),
    T ⊢ (quoteSchemaNeg code)/[↑input] →
      ∃ k, (∼quotationClaimSentence (quoteSchemaPos code) (quoteSchemaNeg code) input) ∈ DP.D k
```

- **Vacuity gone:** the `⊤,⊤` attack needs `⊤ = codeOfREPred truth` *and* `⊤ = codeOfREPred
  (¬truth)` at once — impossible.
- **`hworld` provable verbatim from the MVP:** world believes the atom iff `T ⊢ (pos code)/[i]`;
  both literals ⟹ `T ⊢ pos/[i]` and `T ⊢ neg/[i]` ⟹ (Σ₁-soundness + `codeOfREPred_spec`)
  `truth i ∧ ¬truth i`, contradiction. This is `theoremDP_hworld`'s tag-3 argument.
- **DP = the MVP construction with the schema as a decoded argument.** Fires-predicate is
  `T ⊢ codeOfREPred(decode code)/[i]` — provability where the *formula is a computable function
  of `code`*. The M7-QUOTE-DP spike already cleared this (`Bootstrapping.subst`/`⌜⌝`/`numeral`
  primrec ⇒ `⌜codeOfREPred(decode code)⌝` computable in `code`). This is the **one genuinely new
  piece** over the MVP; everything else reuses [[quote-dp-mvp-computable-recipe]].
- Consumers barely change: `BooleanQuoteCode`/`RationalQuoteCode` gain a `code : ℕ` field with
  `decision = ArithmeticDecision.ofComputable (decode code)`; `.reflected` proofs pass `code`.

_Lighter variant of (A):_ quantify the fields over `ArithmeticDecision T truth` directly. Kills
the vacuity with a smaller diff, but gives **no** computable enumeration for (B) (can't decode
an `ArithmeticDecision` from ℕ). Use it only to unblock the audit fast; go code-indexed for the
construction.

### The diagonal wrinkle — RESOLVED (2026-07-22): decouple, cheap, low-risk

The question "does paradox resistance need the *atom* to carry the fixed-point schema, or only
the fixed-point *law*?" is **resolved: neither.** Evidence (grepped whole `LogicalInduction/`):
`positive_fixedpoint`/`body`/`parameterizedFixedpoint` are used **only** inside the standalone
`ParameterizedDiagonalQuoteCode.diagonal_law` (`QuotationAffine.lean:2243`); `diagonal_law` is
consumed by **nothing**; and `paradoxResistanceQuoteOfDiagonal` (2259) + `lic_paradox_resistance_ofDiagonal`
(3278) use **only** `q.toBooleanQuoteCode` + `truth_spec` (they go through `reflected` /
`completedGated{Complement,Affirmative}Quote`, all of which take a bare `BooleanQuoteCode` and
structurally cannot see the fixed-point fields). So the fixed-point schema is a pure
**faithfulness certificate**, not a proof ingredient of any endpoint.

**Consequence — the diagonal rides the universal code-indexed DP with no special-casing:**

- Atom uses `codeOfREPred truth` (`truth n ↔ P n (atom n) < p` is computable — LIA prices are
  rational/computable). Same DP, same tag-3 `hworld` argument. **No dedicated `diagonal_enters/refutes`
  field. No paradox-resistance proof changes.**
- Keep `diagonal_law` as a **standalone honesty artifact** (a genuine `parameterizedFixedpoint body`
  representing the same `truth` exists + satisfies the diagonal equation). Optionally add a one-line
  bridge `T ⊢ codeOfREPred truth 🡘 parameterizedFixedpoint body` (both represent `truth`) so the
  atom's schema *is* the fixed point up to `T`-provable equivalence.
- **Honest nuance (instantiation, not boundary):** the fixed point is still *essential* to
  **construct `truth_spec`** when instantiating paradox resistance over LIA — exhibiting `truth`
  with `truth n ↔ price(atom n) < p` is circular, and `parameterizedFixedpoint` is what breaks the
  circularity. So the fixed point moves *out* of the atom's schema (→ `codeOfREPred`, for the
  DP/`hworld`) and *stays* where it does real work: defining the self-referential `truth` in the
  instantiation, plus the faithfulness cert. This keeps the quotation family at the **low end** of
  the ~2–4 session estimate — one universal DP, no boundary special-casing.

### Order of operations (frozen-surface aware)

The `⊤,⊤` vacuity argument is taken as an established (traced, not kernel-checked) premise —
we redesign to make it inapplicable rather than first proving it. The redesign is only truly
"fixed" once an inhabitant of `Q ∧ hworld` exists (step 2), which is what certifies satisfiability.

1. **Redesign the fields** (code-indexed), **re-freeze** `#assert_fields QuotationTheoryPresentation`
   (Tier-2 audited surface — this is the *disclosed* frozen-boundary change), fix the ≤6 consumer
   proofs, **re-run `M7-ERRATA-AUDIT`** over the changed surface. (~1 session; the frozen-surface
   care lives here.) This re-shapes the boundary but does **not** by itself certify non-vacuity.
2. **Build the quotation DP + `hworld` = certify the fix.** The MVP recipe with the schema as a
   decoded argument: construct the DP, prove `hworld`, **inhabit `Q`** (this is the step that
   *demonstrates* `Q ∧ hworld` is satisfiable — the real "vacuity is fixed" milestone). (~1–2
   sessions; a known pattern except the formula-as-argument enumeration and the diagonal decoupling.)
3. **Instantiate over `liaHistory`** — add `_unconditional` corollaries for introspection /
   self-trust / expectations / paradox resistance, resolving the diagonal per above. (Follow-on.)

**Disclosure owed when this lands:** narrowing quotation to `ofComputable` (code-indexed)
decisions asserts *the market only quotes computable decisions of its own state* — true of the
paper's reflection/expectation/self-trust constructions, but a real modeling commitment. Record
it in the ledger as a type-`(c)`-adjacent narrowing, don't let an auditor find it. Not blocked
by any missing Foundation lemma (`codeOfREPred`/`re_complete`/FFL fixed points already used here).

---

# Remaining proof engineering — full accounting (2026-07-22)

**Framing.** Two layers stand between the corpus and a *fully unconditional* formalization
(bracketing the 3 disclosed witnesses):

- **Layer 1 — the inductor exists. DONE.** `LIA_is_logical_inductor : ComputableDeductiveProcess
  DP → IsLogicalInductor (liaHistory DP) DP`, strictly axiom-clean. So the `[IsLogicalInductor P
  DP]` hypothesis on the whole property tail is **not a real gap** — instantiate `P := liaHistory
  DP` (one line). The criterion, trading-firm dominance, and efficient-computability plumbing all
  landed clean.
- **Layer 2 — discharge the boundary witnesses + `hworld`, per family.** Each property theorem
  also assumes (a) a boundary/representation structure and (b) `hworld : ∀ n, ∃ v, v.ConsistentWith
  (DP.D n)`. There are ~166 sites threading `hworld`; before the MVP it was discharged in **zero**.
  "Unconditional" = per family: construct a concrete DP, **prove** `hworld`, **inhabit** the
  boundary structure, instantiate over `liaHistory`. The MVP is the first (and only) endpoint that
  does all four; it also makes the hard part (r.e.-provability substrate + a *proved* `hworld`) a
  reusable template ([[quote-dp-mvp-computable-recipe]]).

**Per-family status and remaining work** (bracketing the 3 disclosed):

| Family (paper cluster) | State | Remaining | Est. |
|---|---|---|---|
| **Meta-learning** (halting/consistency, `M7-COMP-SYNTAX`) | **COMPLETE** (2026-07-22): all 6 endpoints unconditional over `LIA` (`*_unconditional` in `ComputationDP.lean`) | — (done) | **0** |
| **Universal semimeasure** (`M7-DUS-PREFIX-SYNTAX`) | **DONE** (2026-07-22): `lic_domination_universalSemimeasure_unconditional` over LIA on the proved-computable empty process (`UnconditionalOverLIA.lean`); `hworld` trivial | Only the *disclosed* `M7-DUS-APPROX` approximation `A`/`emit` remains an input (bracketed); full Occam bound also needs disclosed Kraft | **~0 (disclosed remainder)** |
| **Conditioning** (`M7-SCON-*`) | **DONE** (2026-07-22): `lic_conditioned_unconditional` — the constructed inductor conditioned on a computable event is again an inductor over the union process (`UnconditionalOverLIA.lean`) | — (`C`/compiler stay caller inputs by design) | **0** |
| **LUV combinations** (`M7-LUV-SYNTAX`) | **COMPLETE** (2026-07-22): `luv_wubexp_ofComputation_unconditional` over `liaHistory (theoremDP T)` | — (caller retains the paper's exact-theory presentation and delayed-value program) | **0** |
| **Feedback / pseudorandomness** (`wub`, `M7-FEEDBACK-TRUTH/EMIT`) | **COMPLETE** (2026-07-22): all four computation-backed consumers instantiated over constructed `LIA`; ordinary `thm:wub` specialization added | — (no new DP was needed; `theoremDP_computable` + `theoremDP_hworld` discharge the market side) | **0** |
| **Quotation / self-reference** (`M7-QUOTE-AFFINE`) | **COMPLETE** (2026-07-22): redesign + certify + all 8 endpoints unconditional over `LIA` | — (done) | **0** |

**Bottom line:** proof engineering for the property tail is complete, including quotation,
feedback, and LUV. The feedback uncertainty collapsed because its `_ofComputation` boundary is
operational data rather than a DP presentation, so the established `theoremDP`/`hworld`
corollary pattern applies directly. Remaining work is verification/read-through and the
separately disclosed `dd:fuel` hardening, not another property construction.

**Verification still owed (not proof engineering, but part of "done"):** the deferred **human
statement read-through** (Anson) over the frozen surface, then the final `M7-ERRATA-AUDIT` pass —
the steps that certify the statements are the paper's. Sequencing override in `CLAUDE.md` still
governs.

_Original MVP brief retained below for the quotation-side redesign, which reuses the same shape._

## Where things stand (audit + GL discharge + QUOTE-DP spike done, 2026-07-21)

The **12/15 conditional+disclosed green endpoint is complete**; consolidation (step 2 of the
`CLAUDE.md` sequencing override) is done. Recent landings (older consolidation detail is in
git history):

- **`M7-ERRATA-AUDIT` complete** (`notes/m7-errata-audit.md`). No soundness defects on the
  critical path. One disclosure-scope finding **F1** (introspection/self-trust/meta-learning
  family conditional on an arithmetic-representability substrate no in-repo object inhabits),
  **now upgraded** to a concrete **vacuity finding** on the quotation side (below).
- **GL fixed-point axiom discharged** — the whole repo is now strictly axiom-free. Via the
  vendored autoformalized `ProvabilityLogic/` sequent calculus (Aristotle); notations
  `scoped` to avoid Foundation collisions. See the Aristotle section.
- **`M7-QUOTE-DP` spike done — verdict GO.** Provability-in-`T` r.e. is assemblable (no
  Foundation wall); details + recipe in the `M7-QUOTE-DP` section.

Earlier consolidation landings (still true, now background):

- **Paper-node inventory, two tiers, build-enforced.** `AxiomAudit.lean` (a
  `@[default_target]`, so `lake build`/CI runs it) is the endpoint inventory: Tier 1 = 103
  proof endpoints under `#assert_axioms_clean`; Tier 2 = boundary structures under a new
  `#assert_fields` (freezes each structure's hypothesis fields — adding/removing a field
  fails the build). Membership is mechanical: a structure is Tier 2 iff it appears in a
  Tier-1 endpoint's type, transitively through fields (`SurfaceProbe.lean`). Rationale and
  judgment calls: `notes/endpoint-inventory.md`.
- **`Paper node:` annotations** on every inventory member's docstring, labels verbatim from
  `notes/1609.03543v5-main.tex`. Enforced by `scripts/check-paper-nodes.sh` (every cited
  label exists; every member carries one). `scripts/lint_paper_labels.py` is now blocking
  (every `theorem` ⇔ a paper node; no `private theorem`).
- **Whole-repo axiom audit, now strictly clean throughout.** `AxiomAudit.lean` covers
  `ModalAgents/` too. The former sole intentional axiom `glFixedPoint_thm42` has been
  **discharged** (2026-07-21) via the autoformalized `ProvabilityLogic/` sequent calculus
  (Aristotle job `9226321a…`, validated in-repo, notations scoped to avoid Foundation
  collisions); every ModalAgents endpoint is now under strict `#assert_axioms_clean`.
- **Duplication sweep.** Removed two genuine duplicate helper lemmas (`max_sub_max_neg`,
  `oneMinus_denote`). Construction/ has no duplicate *facts* — its parallel shapes
  (`*FromStages`/`*FromStageLists`, triangular/gap/frame families) are by-design over
  distinct types.
- **Stale-reference repair.** Fixed a merged-away README path (`StrictSemimeasure.lean` →
  `UniversalSemimeasure.lean`) and three dead `PROGRESS.md` pointers (that ledger was
  deleted; the comments are now self-contained). Includes a live `thm:ifp` paper-erratum
  note in `FinitePerturbations.lean` — see the errata-audit brief.

**State:** working tree clean; full `lake build` green (2720 jobs); AxiomAudit strictly clean
(no intentional axioms anywhere). Several commits on `logical-induction` unpushed (per Anson's
workflow, nothing is pushed without asking).

## What remains, in order

> Superseded by **"Remaining proof engineering — full accounting"** and **"THE NEXT FOCUS —
> quotation non-vacuity rescue"** at the top of this file (2026-07-22). Kept as a one-line index:
> (1) ~~M7-QUOTE-DP MVP~~ DONE · (2) quotation non-vacuity rescue — **the next focus** · (3) the
> four near-trivial family finishes (meta-learning siblings, universal-semimeasure, conditioning,
> LUV) · (4) feedback/pseudorandomness DP · (5) human read-through + paper comparison · (6)
> optional Kraft/`M7-PREFIX-MACHINE`.

---

# THE NEXT TASK — M7-QUOTE-DP meta-learning MVP

**Goal.** Produce the project's first *unconditional* epistemic theorem over the constructed
`LIA` inductor: "there is a concrete computable deductive process `DP` such that `LIA` over
`DP` provably learns provable halting patterns" (or a sibling meta-learning endpoint), with
**no remaining hypotheses** — in particular the market non-vacuity `hworld` is *proved*, not
assumed. This turns one `_ofComputation` endpoint from conditional-on-assumed-substrate into
constructed-over-LIA. Read the `M7-QUOTE-DP` section below first (spike verdict + recipe).

**Scope — computation side ONLY.** Build `ComputationTheoryPresentation DP T` (fixed schemas:
`universalHaltingSchema`, …). Do **not** touch `QuotationTheoryPresentation` — it is blocked
by the vacuity obstruction (below) and needs a frozen-boundary redesign, which is a separate,
larger task. The computation presentation is consistently inhabitable; the quotation one is not.

**Plan (est. ~4–5 focused sessions; tall poles flagged):**
1. Fix `T := 𝗜𝚺₁`; gather instances (`Theory.Δ₁`, `𝗜𝚺₁ ⪯ T`, `SoundOnHierarchy 𝚺 1`,
   `𝗥₀ ⪯ T`). ~½ session; risk = FFL instance resolution.
2. **[tall pole A]** Assemble `REPred {z | T ⊢ universalHaltingSchema/[z]}` (and the refutes
   duals) following `Foundation/FirstOrder/Incompleteness/Halting.lean:25-27`:
   `Provable.definable` (Σ₁ via `definability`) + `re_iff_sigma1` + `Theory.Provable.sound`.
   ~1 session; risk = Bootstrapping coding (`subst`/`⌜⌝`/`numeral`).
3. **[tall pole B]** Wrap the r.e. semi-decider into a monotone `Finset Sentence` stage
   function `D n` and prove `ComputableDeductiveProcess DP`. Reuse the proven dovetail infra
   — `dovetailFound` / `polyFueled_dovetailFound` / `dovetailFound_mono`
   (`Construction/Witnesses/M7Witnesses.lean:787+`). No "r.e. set → DP" helper exists yet, so
   this glue is new but built on proven primitives. ~1 session; **residual risk = Primrec over
   `Finset` (see [[li-primrec-natsqrt-blowup]] — scope `irreducible Nat.sqrt`).**
4. Prove `enters`/`refutes` from enumeration coverage, and **`hworld`** (each stage
   consistent, from `T`-consistency + fixed complementary schemas). ~1 session.
5. Assemble `ComputationTheoryPresentation` and instantiate one meta-learning corollary over
   `LIA` (consumer already exists in `Construction/Witnesses/ComputationSyntax.lean`). ~½ session.

**Derisking move (recommended first sitting):** do tall pole B in isolation on a trivial
predicate — build the computable `Finset`-stage program from `dovetailFound` and prove
`ComputableDeductiveProcess`. If Primrec-over-`Finset` behaves, the ~week estimate is solid;
if it fights back you learn it in one session, not a week. The spike cleared "provability is
r.e."; it did **not** clear this piece.

**The atom-coding caveat.** The stage program must emit *exactly* `haltingClaimSentence z`
(and its negation) — the frozen coding. Preserve literal token/list equalities at the
representation boundary; semantic equality is not enough for the witness (a repeated lesson).

## Aristotle experiments in flight (external state — survives context, IDs do not)

Two jobs testing whether Aristotle can discharge remaining hard pieces. **Job IDs live only
here now — a fresh context needs them to poll.** Trust rule: a returned proof is trusted
only after it compiles in *this* repo; the kernel is the gate, never Aristotle's word.

- **GL fixed-point axiom** (`glFixedPoint_thm42`) — **DONE, integrated 2026-07-21.**
  Aristotle job `9226321a-32f8-414b-9d30-6ef06093b7f0` returned a complete sorry-free proof.
  Its ~9.5k-line `ProvabilityLogic/` sequent calculus was vendored into the repo (a
  `lean_lib` in `lakefile.lean`), validated to build against our Foundation @ aada66ef
  (868 jobs), and its `Formula`-level notations were made `scoped` to stop them colliding
  with Foundation's modal notation in `ModalAgents`. The `axiom` in `FixedPoint.lean` is
  replaced by a proved `theorem` via the `GlFixedPointBridge` translation; AxiomAudit now
  asserts the cooperation endpoints strictly clean. Kernel-gated (interior not human-read),
  disclosed in the README like Brouwer. Original download kept at
  `…/scratchpad/gl-result/gl-fixedpoint_aristotle/`.
- **Kraft inequality** (`kraft_inequality`, the Mathlib-only core of `M7-PREFIX-MACHINE`).
  **Submitted 2026-07-22, FAILED.** Aristotle job `bc2df18a-a33d-4c0f-a5ec-e048986d85df`
  completed but returned the file with the `sorry` unchanged (no proof produced). Options:
  resubmit with a sharper hint (the counting argument needs an explicit length-`L` block
  enumeration Mathlib doesn't hand you), or prove it manually. Statement in
  `notes/m7-prefix-machine-scope.md`; Mathlib-only, validated to elaborate in-repo. Note even
  a proof only removes step 1 of 5 for `M7-PREFIX-MACHINE` (a disclosed boundary).

**Scratchpad projects may be ephemeral** (session-specific dir):
`…/scratchpad/gl-fixedpoint/` and `…/scratchpad/kraft/`. Both are tiny and reconstructible —
the Kraft statement is in the scope note; the GL project is `require Foundation @ aada66ef…`
+ the `Modalized`/`diag` defs + the axiom-as-`sorry` (see `ModalAgents/FixedPoint.lean:45`). If
resubmitting, use `scripts/aristotle-prove.sh <project-dir> "<prompt>"`.

## Deliberately disclosed boundaries

- `M7-PREFIX-MACHINE` — supplies standard universal self-delimiting-machine, from-below
  weight, finite Kraft, and fixed negation-overhead facts for Occam Bounds; the paper-
  specific market proof is already formalized. Optional post-target showcase; the finite
  Kraft core is the Aristotle-able piece (`notes/m7-prefix-machine-scope.md`).
- `M7-DUS-APPROX` and `M7-STRICT-SEPARATORS` — remain disclosed unless Anson reopens them.

These three are the only intentional disclosures at the 12/15 target. The audit should
confirm no fourth boundary is assumed anywhere it isn't named.

## Recorded future tranche — `M7-QUOTE-DP` (arithmetic-representability substrate)

Surfaced by `M7-ERRATA-AUDIT` finding F1 (`notes/m7-errata-audit.md`). The
introspection / self-trust / expectation-representation / meta-learning / paradox-resistance
family is conditional on `QuotationTheoryPresentation` / `ComputationTheoryPresentation`
(and the diagonal codes), which **no in-repo construction inhabits** — and nothing connects
that family to the constructed `LIA`. Not a soundness bug (disclosed per-boundary in the
README), but a disclosure-scope gap: "12/15 constructed" reads as if these results reach the
constructed inductor; they do not.

### Vacuity obstruction — computation side OK, quotation side blocked (traced 2026-07-21)

Attempting the construction surfaced what the statement-level audit missed. The two
presentations behave differently under the market non-vacuity hypothesis
`hworld : ∀ n, ∃ v, v.ConsistentWith (DP.D n)` (`ConsistentWith v D := ∀ φ ∈ D, v.Holds φ`, so a
stage containing both `X` and `∼X` has no consistent world):

- **`ComputationTheoryPresentation` — consistently inhabitable.** Its enters/refutes fields
  quantify over inputs `z` for **fixed** schemas. `T` consistent ⟹ never proves both
  `haltingSchema/[z]` and `∼haltingSchema/[z]` ⟹ `haltingClaim z` and `∼haltingClaim z` never
  co-occur. **This is the MVP target.**
- **`QuotationTheoryPresentation` — NOT inhabitable alongside `hworld`.** `quote_positive_enters`/
  `quote_negative_refutes` quantify over **arbitrary** `positive negative : ArithmeticSemisentence 1`.
  Take `positive = negative = ⊤` (or `#0 = #0`): `T ⊢ ⊤/[i]` trivially, so `enters` forces the
  atom `X = quotationClaimSentence ⊤ ⊤ i` into `DP` **and** `refutes` forces `∼X` in — an
  inconsistent stage, so `hworld` is false. Hence **any** `Q : QuotationTheoryPresentation ⟹ ¬hworld`,
  so the conjunction `(Q ∧ hworld)` in `lic_introspection_ofCode` / `lic_paradox_resistance_ofDiagonal`
  / the `_ofCode`/`_ofRepresentation` endpoints is **unsatisfiable → those Tier-1 endpoints are
  vacuously true**. This *upgrades* audit finding F1 from disclosure-scope to a genuine mode-1
  vacuity, and is why the quotation side needs a frozen-boundary redesign (restrict the quote
  fields to complementary decisions), not just a DP. The `⊤,⊤` argument is traced but not
  kernel-checked; the plan is to redesign so it no longer applies (not to first prove it), and to
  certify the fix by inhabiting `Q ∧ hworld`. See THE NEXT FOCUS above and
  [[quotation-presentation-vacuity]].

The fix is a genuine construction, and — unlike Brouwer/GL — **not blocked by any missing
Foundation lemma**; the FFL pieces are already used by `M7-COMP-SYNTAX`/`M7-QUOTE-AFFINE`
(`codeOfREPred`, `re_complete`, `DeductiveProcessComputation.union`, `deductiveStageCondition`).
Shape (full family; the MVP does only step 1's computation half + a computation corollary):
1. Build a concrete deductive process enumerating the theorems of a fixed Σ₁-sound theory
   `T` (e.g. `𝗜𝚺₁`), reusing the SCON stage/union machinery.
2. Discharge `QuotationTheoryPresentation`/`ComputationTheoryPresentation` for it:
   `theory_sigmaOne`/`theory_deltaOne` from `T`'s strength; `quote_positive_enters` /
   `quote_negative_refutes` from FFL provable-⇒-enumerated representability.
3. Add a corollary instantiating the `_ofCode`/`_ofDiagonal`/`_ofRepresentation`/
   `_ofComputation` endpoints over `LIA` on that DP — turning the family from
   conditional-on-assumed-substrate into unconditional-over-a-concrete-inductor.
   Would let the "12/15 constructed" headline honestly cover the self-reference span.

M7-scale (multi-session); tractable and unblocked. Deferred by Anson 2026-07-21 (record only).

**Spike done 2026-07-21 — verdict GO (no Foundation wall).** The one go/no-go risk was
whether Foundation exposes provability-in-`T` as a meta-level r.e./computable object (needed
because `quote_positive_enters` is ∀-quantified over all provable instances, so the DP must
enumerate them). It is not pre-packaged as `REPred (T ⊢ ·)`, and `Derivation` is a
proof-relevant `Type _` (not `Encodable`) — but the r.e. enumeration is **assemblable** from
ingredients Foundation already uses in its own incompleteness proofs
(`FirstOrder/Incompleteness/Halting.lean:25-27` is the template):
- `Provable.defined`/`Provable.definable` + the `definability` tactic: internal `T.Provable`
  is `𝚺₁-Predicate` (`Bootstrapping/Syntax/Proof/Basic.lean`).
- `re_iff_sigma1 : REPred P ↔ 𝚺₁-Predicate P` (`Incompleteness/First.lean`).
- internal-provability ↔ `⊢` bridge (`Theory.Provable.sound`; the `□`/provability iff used
  across Solovay/Jeroslow/Yablo).
- `Bootstrapping.subst`/`.neg`/`⌜⌝`/`numeral` are primrec, so the formula-as-argument coding
  (`⌜positive⌝` as a computable function of `positive`'s code) is supported.

So the labor is: (1) assemble `REPred {(pos,neg,i) | T ⊢ pos/[i]}` following the Halting.lean
pattern; (2) turn that semi-decider into a growing computable `Finset Sentence` stage program
(dovetail — repo has the `Nat.rfindOpt`/`evaln` patterns in `LIAComputation.lean` and
`DeductiveProcessComputation.union` for stage assembly), coding each provable instance as its
`quotationClaimSentence` atom; (3) prove `enters`/`refutes` from enumeration coverage; (4)
pick `T` for `theory_sigmaOne`/`theory_deltaOne`; (5) instantiate the corollary over LIA. The
one delicate boundary is the atom-coding alignment (the stage program must emit exactly
`quotationClaimSentence`/`quotationClaimCode` — the "preserve literal token equalities" caveat).
**MVP (the active next task): the *computation* half only** — DP + `ComputationTheoryPresentation`
+ `hworld` + one meta-learning corollary over LIA (e.g. learns provable halting patterns). The
quotation flagships (paradox resistance, self-trust) are the blocked side — see the vacuity
obstruction above; they need the boundary redesign first, not this MVP.

## Verification and commit discipline

Before any commit, smallest relevant build first, then:

```sh
lake build
rg -n '(^|[[:space:]])(sorry|admit)([[:space:]]|$)' LogicalInduction ModalAgents --glob '*.lean'
./scripts/check-paper-nodes.sh
python3 scripts/lint_paper_labels.py
git diff --check && git status --short
```

Axiom reports of any new public endpoint must contain only `propext`, `Classical.choice`,
`Quot.sound` — the whole repo (LogicalInduction and ModalAgents) is now strictly clean, with
no intentional axioms. Keep historical detail in git rather than appending superseded plans
below the active handoff.

## Aristotle usage

Via `scripts/aristotle-prove.sh`; only after a goal is fully stated and self-contained.
Prefer small extracted Mathlib-only projects, not the whole repo. `ARISTOTLE_API_KEY` must
be in the environment. Toolchain versions may differ; a returned proof is trusted only after
it compiles here.

## Reusable construction notes

- Search before proving. Anchors: `codeEvalnNat_polyFueled`, `deadlineRun`,
  `scheduledMatch`, `segPrefix_polyFueled`, `segLocate_polyFueled`,
  `PolySegStream.concatVar`, `PolySequence.priceFeature_polySeg`, `PGenerableWeighting.polySeg`.
- Deep `PolyFueled` proofs with nested `Nat.unpair` can trigger `Nat.sqrt` whnf blowups;
  prefer a narrow local `attribute [irreducible] Nat.sqrt` over raising heartbeats.
- Preserve literal token/list equalities at representation boundaries; semantic equality
  alone is not enough for the witness constructors.
- Keep computation certificates conclusion-free; economic/asymptotic conclusions belong in
  the already-proved consumer layer.
