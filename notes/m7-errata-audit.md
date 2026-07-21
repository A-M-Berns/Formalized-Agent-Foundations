# M7-ERRATA-AUDIT — fresh-context adversarial statement-level audit

_Run 2026-07-21, fresh context, branch `logical-induction`. Auditor did not trust
docstrings, provenance labels, or `notes/next-session.md`; every claim below was checked
against the Lean source (and, where fidelity was at stake, `notes/1609.03543v5-main.tex`)._

## Verdict

**No soundness defects found.** No vacuous theorem, no undisclosed conclusion-in-hypothesis
squeeze on the trust surface, no oversold stub standing in for an exploiting trader, no
undisclosed type-`(c)` substitution, no degenerate non-vacuity witness, and no *hidden*
fourth boundary. The build carries exactly one declared axiom (`glFixedPoint_thm42`,
ModalAgents) and no `sorry`/`admit` in any proof body (the two `rg` hits are the token
"admit"/"squeeze" appearing in prose/comments, not tactics).

There is **one finding worth Anson's triage** — a disclosure-*framing* gap, not a defect:
the introspection / self-trust / expectation-representation / meta-learning / paradox-
resistance family is conditional on a large assumed arithmetic-representability substrate
that no in-repo construction inhabits, and nothing connects that family to the *constructed*
inductor. This is honestly disclosed in the README's per-boundary table, but is easy to lose
against the "12/15 constructed" headline. Details below.

Everything else in this report is positive verification, recorded so the deferred human
read-through can start from a narrower surface.

---

## Findings (ranked)

> **Post-audit upgrade (2026-07-21, F1 → F0).** A follow-up construction spike (recorded in
> `notes/next-session.md`, `M7-QUOTE-DP`) upgraded F1 from a disclosure-scope note to a
> **genuine mode-1 vacuity** on the quotation side. F1 below stands as originally written;
> read F0 first.

### F0 — MEDIUM / vacuity (mode 1). `QuotationTheoryPresentation` is unsatisfiable alongside the market non-vacuity hypothesis `hworld`, so the `_ofCode`/`_ofDiagonal`/`_ofRepresentation` endpoints are vacuously true.

**Where.** `lic_introspection_ofCode`, `lic_paradox_resistance_ofDiagonal`, and the other
`_ofCode`/`_ofRepresentation` endpoints (`Construction/Witnesses/QuotationAffine.lean`), each
of which takes both `Q : QuotationTheoryPresentation DP T` and
`hworld : ∀ n, ∃ v, v.ConsistentWith (DP.D n)`.

**Failure scenario.** `PCWorld.ConsistentWith v D := ∀ φ ∈ D, v.Holds φ`, so a stage `D n`
containing both `X` and `∼X` has no consistent world. `quote_positive_enters` /
`quote_negative_refutes` (`QuotationAffine.lean:107-114`) quantify over **arbitrary**
`positive negative : ArithmeticSemisentence 1`. Take `positive = negative = ⊤` (or `#0 = #0`):
`T ⊢ ⊤/[i]` trivially, so `enters` forces `X = quotationClaimSentence ⊤ ⊤ i` into `DP` and
`refutes` forces `∼X` in; by `mono` both land in one stage → that stage is inconsistent →
`hworld` is false. Hence any `Q` implies `¬hworld`, the hypothesis conjunction is
unsatisfiable, and the endpoints are vacuously true. Contrast the **fixed-schema**
`ComputationTheoryPresentation` (`ComputationSyntax.lean:265`), which *is* consistently
inhabitable (`T` consistent ⟹ never both `haltingSchema/[z]` and its negation).

**Status.** Traced against the definitions, **not yet kernel-confirmed**; the honest next step
is to derive `False` from `Q + hworld` in Lean (~½ session). Not a soundness bug (the theorems
are true), but the quotation-substrate endpoints prove nothing until the boundary is fixed.

**Disposition.** Restrict `quote_positive_enters`/`quote_negative_refutes` to complementary
decisions (quantify over an `ArithmeticDecision`/`BooleanQuoteCode`, or add a complementarity
hypothesis). This is a frozen-boundary change (`#assert_fields`) → re-freeze + re-run this
audit, and it reworks the `reflected`/affine consumers. See `M7-QUOTE-DP` in the handoff.

### F1 — LOW / disclosure-framing. The introspection/self-trust/meta-learning span is conditional on an assumed representability substrate that no in-repo object inhabits, and never touches the constructed inductor.

**Where.** `Construction/Witnesses/QuotationAffine.lean` (`lic_introspection_ofCode:3244`,
`lic_paradox_resistance_ofDiagonal:3278`, the seven other `_ofCode`/`_ofDiagonal`/
`_ofRepresentation` endpoints), `Construction/Witnesses/ComputationSyntax.lean` (the six
`_ofComputation` meta-learning endpoints). Substrate structures:
`QuotationTheoryPresentation` (QuotationAffine.lean:103), `ComputationTheoryPresentation`
(ComputationSyntax.lean:265), `ParameterizedDiagonalQuoteCode` (:2235), `BoundedComputation`,
`SemidecidableComputation`, `RepresentedSemidecidableClaims`.

**Evidence.** None of these structures has a constructor anywhere in the repo
(`rg ": <Struct>" | rg 'def|instance'` returns only functions that *consume* them). So every
"construction-discharged" endpoint in this family is really *conditional on the substrate
being supplied as a hypothesis*:
- `lic_paradox_resistance_ofDiagonal` takes `q : ParameterizedDiagonalQuoteCode T truth`
  **and** `truth_spec : ∀ n, truth n ↔ P n (q.sentence n) < p` as hypotheses.
- `lic_introspection_ofCode` takes `Q : QuotationTheoryPresentation DP T` and a
  `BooleanQuoteCode`.
- `QuotationTheoryPresentation` bundles the paper's `def:ref` bridge: `theory_sigmaOne`
  (`𝗜𝚺₁ ⪯ T`) plus `quote_positive_enters`/`quote_negative_refutes` (arithmetically
  provable facts *enter the deductive process*). That bridge is inhabitable in principle —
  a DP that enumerates theorems of a Σ₁-sound arithmetic theory would satisfy it — but it is
  never built. In particular `exists_logical_inductor`/`LIA_is_logical_inductor` construct
  `LIA` over an **arbitrary** computable `DP` and never connect it to any
  `QuotationTheoryPresentation`. So there is no in-repo theorem asserting that *the
  constructed inductor* is introspective / paradox-resistant / self-trusting.

**Why this is not a defect.** The diagonal code itself is principled, not stubbed:
`ParameterizedDiagonalQuoteCode.positive_fixedpoint` pins `decision.positive =
parameterizedFixedpoint body`, an actual Foundation/FFL fixed point, and
`diagonal_law` (:2243) discharges the uniform diagonal biconditional via
`parameterized_diagonal₁`. And the README *does* disclose this in the per-boundary "What is
assumed" column for `M7-QUOTE-AFFINE` / `M7-COMP-SYNTAX` ("Constructed **from** a
`QuotationTheoryPresentation` …"). So this is disclosed, not hidden.

**The gap.** The disclosure lives only in the per-boundary table's fine print. Three signals
push the other way and could mislead a reader who does not read that column:
1. the "**Twelve of the fifteen** M7 witness boundaries have been constructed" headline
   counts QUOTE-AFFINE and COMP-SYNTAX as *constructed*, though what is constructed is the
   affine/syntax emission, not the representability substrate they consume;
2. the endpoint **names** (`_ofCode`, `_ofDiagonal`, `_ofRepresentation`) read like the
   genuinely self-inhabiting witnesses (`feedbackTruthSequence`, `liaEfficientPrefixPatch`),
   which *do* discharge their own boundary;
3. `next-session.md`'s "these three are the only intentional disclosures at the 12/15
   target" is true only under the narrow reading "the only *unbuilt M7 witnesses*." The
   arithmetic-representability substrate is a fourth *assumed* boundary in the plain sense of
   "a hypothesis no in-repo object satisfies," just filed under Tier-2 rather than under
   "disclosed boundary."

**Proposed disposition.** No code change. (a) Add one sentence to the README's headline
paragraph and to `next-session.md`'s "disclosed boundaries" block stating that the
introspection/self-trust/expectation-representation/meta-learning results are conditional on
an assumed arithmetic-representability substrate (`QuotationTheoryPresentation` /
`ComputationTheoryPresentation` and the diagonal codes) that is *not* inhabited in-repo and
is *not* connected to the constructed `LIA`. (b) Flag for the deferred human read-through
that these Tier-2 structures are the substrate whose satisfiability it must judge — they are
where "faithful to the paper's assumptions" has to be confirmed against `def:ref` and the
paper's own diagonal construction.

---

## Positive verification (method shown, so the read-through can trust the narrowing)

**Critical path to existence — genuine, kernel-clean.**
- `exists_logical_inductor` / `LIA_is_logical_inductor` (`LIACompiler.lean:6738,6747`)
  reduce, with no added hypothesis, through `lia_isLogicalInductor_of_compiler` →
  `lia_isLogicalInductor_of_computableMarket` (`LIA.lean:118`) to `noExploit :=
  lia_no_efficient_trader_exploits`, whose content is the real market-clearing/dominance
  argument (`trading_firm_dominance`, `marketMaker_not_exploited`), **not** a stub. The
  computability premise is discharged by an actual primitive-recursive bounded evaluator
  (`liaEncodedQuoteNatAtFuel_prim`), minimized to a total partrec quote program. All three
  `#print axioms` report clean.
- `Trader.Exploits` (`Criterion.lean:1350`) = `BddBelow ∧ ¬BddAbove` of plausible
  assessments — the paper's `def:exploitation` on the nose; refutability witnessed by
  `Trader.zero_not_exploits`, so `def:lic` is not vacuous.
- `IsLogicalInductor` (`Criterion.lean:1456`) quantifies `noExploit` over
  `EfficientlyComputableTok`, the token-indexed poly-*size* model. The whole-number
  `EfficientlyComputable` is retained but explicitly **superseded** and marked so; the
  residual per-token type-`(c)` disclosure (`⌜φ⌝` must be `poly n`-value) is written into the
  definition's docstring. Faithful and disclosed.

**Brouwer (on the critical path, autoformalized interior).** `brouwer_fixed_point`
(`Brouwer.lean:1366`) is the *correct* statement: `IsCompact K → Convex ℝ K → K.Nonempty →
ContinuousOn f K → MapsTo f K K → ∃ x ∈ K, f x = x`. Not weakened, not vacuous. Interior is
kernel-checked (axiom-clean); the statement — the only thing the kernel does not vouch for —
is right.

**`thm:ifp` erratum — honestly handled (the item next-session.md flagged).**
`FinitePerturbations.lean` keeps the theorem to what is provable:
`lic_iff_of_finitePerturbation` (:729) takes an `EfficientPrefixPatch` per market as a
hypothesis and proves the full biconditional; `EfficientPrefixPatch` (:718) is explicitly
documented as **not inhabited for every `ComputableMarket`** (huge-encoding day-0 quotes
admit no patch), so the theorem is honestly *strictly weaker* than the paper's `thm:ifp`.
The load-bearing `preserves_ec` field is genuinely discharged for `LIA` by
`liaEfficientPrefixPatch` (`M7Witnesses.lean:3483`) through poly-fueled quote codes — a real
inhabitation, not a stub. This belongs in the README disclosures if it is not already there;
recommend confirming. (Statement checked; the unformalized counterexample argument it cites
is disclosed as unformalized.)

**Disclosed boundaries are exactly three and genuinely uninhabited.**
`PrefixMachinePresentation`, `UniversalContinuousSemimeasure`,
`LowerSemicomputableContinuousSemimeasure`, `PrefixNegationCompiler` (PREFIX-MACHINE);
`DUSApproximationPresentation`, `DUSThresholdEmission`, `OccamThresholdEmission`
(DUS-APPROX); `StrictSeparatorPresentation` (STRICT-SEPARATORS) — none has an in-repo
constructor, matching their "disclosed" status. Their consumers (`lic_occamBounds`,
`lic_domination_universalSemimeasure`, `lic_strict_domination_universalSemimeasure`) are
correspondingly conditional. `BitPrefixSentences` (the *sentence* side of DUS) **is**
constructed (`bitPrefixSentencesOfIndependentAtoms`), consistent with "DUS-APPROX remains
disclosed while the prefix syntax is built."

**Conclusion-in-hypothesis: the one flagged interface is off the trust surface.**
`SettlementSemiDecider.sound` (`M7Witnesses.lean:1028`) does state settlement (a
conclusion-in-hypothesis shape) and its docstring says so — but it is **not** in the
AxiomAudit inventory; the audited path is `SettlementChecker` (fields `code spec`), which
derives settlement as a theorem via `settlementTest_iff_settled`. Correct call.

**Non-vacuity witnesses are honest, not degenerate.** The `N+` paths
(`quotationRepresentation_positive_path`/`_negative_path`) use the constant `True`/`False`
predicate via `trueBooleanQuoteCode`/`falseBooleanQuoteCode` — but these test only that the
*representation plumbing* reaches the DP, and are labeled `N+` for exactly that; they are not
sold as claims about a real self-referential predicate. Not a degenerate-witness abuse.

**ModalAgents axiom is a genuine, disclosed metatheorem.** `glFixedPoint_thm42` is the de
Jongh–Sambin–Bernardi GL fixed-point existence theorem with the standard atom-support side
condition — true, not vacuous, not over-strong. _(Update, same session 2026-07-21: this axiom
has since been **discharged** — proved via the vendored autoformalized `ProvabilityLogic/`
sequent calculus and validated in-repo; `AxiomAudit` now asserts the ModalAgents endpoints
strictly clean. The repo carries no intentional axioms.)_

## Method / coverage caveat

This pass verified the **critical path** (existence, Brouwer, one representative property
trader — the hysteresis/convergence loop), the **flagged erratum**, the **boundary
inhabitation map** (which structures have constructors and which do not, across all Tier-2
members), and **one representative from each failure mode**. It did **not** re-read all 103
Tier-1 proof bodies line-by-line — the kernel already certifies bodies-match-statements, and
this audit is statement-level by mandate. The remaining statement-fidelity work (each Lean
statement vs. its `Paper node:` label at full strength) is precisely the deferred human
read-through; F1 identifies the substructure where that read-through's judgment actually
bites.
