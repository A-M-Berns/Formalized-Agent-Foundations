# Faithfulness audit — LogicalInduction vs. arXiv:1609.03543 (fresh pass, 2026-07-28)

Fresh-context, code-first audit of `LogicalInduction/` + `AxiomAudit.lean` at HEAD
`32c599d` against the paper source (`notes/1609.03543v5-main.tex`). Method: every core
Framework definition read in full against the paper's §2–§3 definitions; the `thm:li`
endpoints, the property-tail statements for `thm:con/lc/provind/perkno/tbo/nd/ob/dus/
simcal/wub/benford/prand/scon/ifp/ec/ref/lp/st/pac/pazfc/incons`, and the construction
trust points (`Brouwer`, `MarketMaker`, `TradingFirm`, `LIACompiler`, `LIAComputation`)
read at statement level, with proof bodies opened only where needed to judge overselling.
Documentation quality was explicitly out of scope.

In parallel, codex (gpt-5.6-sol, high reasoning, independent context) ran the same audit
question over the same tree. Its findings were individually re-verified against the code
before incorporation; attribution and my adjudication are marked per finding. This file
**replaces** `notes/m7-errata-audit.md` (the 2026-07-24 pass), which was deleted at the
start of this audit; nothing below is carried over from it.

Mechanical state at audit time: zero `sorry`, zero `axiom` declarations, no
`native_decide`/`unsafe`/`@[implemented_by]` in the library; `AxiomAudit.lean` asserts
every listed endpoint clean of everything beyond `propext`/`Classical.choice`/
`Quot.sound` and freezes Tier-2 field sets; CI green at HEAD.

---

## Status update (2026-07-28, same-day fix wave)

Every finding below was triaged and, except where Anson ruled otherwise, **fixed** the
same day by a parallel fixer wave (worktree branches, per-branch kernel gates, batched
consolidation builds; details in `notes/next-session.md`). Outcomes:

* **F1** — docstring overclaim reverted; "Lower calibration — OPEN" recorded in the
  `dd:fuel` model card. The lower-calibration theorem itself remains the one deliberate
  open problem of the substitution.
* **F2** — **fixed**: the `thm:li` endpoint now carries the `def:belseq` emission
  conjunct (`exists_liaEntries_code`), so it states the paper's actual claim.
* **F4** — **fixed**: `thm:ec` takes the per-grid hypothesis; proof rebuilt along the
  paper's own route (affine tower + `thm:lc` + `lem:conluvapprox`); the diagonal-
  hypothesis bespoke trader was deleted as unsound-for-purpose.
* **F5** — **fixed** for `thm:wubexp` and the `_of_historicalVerifiers` recurring form
  (combination-level determination only, via the approximate-determination engine);
  prandexp family follow-up in flight (approximate settlement checker).
* **F6a** — **fixed** to `Function.Injective f.f`; the final step to bare `f n > n`
  needs a gated-fibre-sum layer — ruled future work (Anson, 2026-07-28). F6b
  (P-generable `p` in `thm:st`) — **fixed 2026-07-29** via `PGenerableRat.computable`.
* **F7** — **fixed**: fixed-sentence `thm:scon` is hypothesis-free; growing form
  discloses the propositional-compactness obstruction.
* **F9** — **fixed**, and this report's original justification was WRONG; see the
  corrected F9 section below.
* **F10** — real reindex queued as the final, solo change.
* F3/F8/F11 — stand as disclosed (F8 is paper erratum PE1).

## Headline

The core market/trader/exploitation layer is faithful to the paper essentially on the
nose, `thm:li` is proved for an arbitrary computable deductive process with a genuinely
constructed LIA (including an in-repo Sperner-route Brouwer), and the property tail's
statements track their paper nodes closely in analytic content. The faithfulness debt is
concentrated in two places: **(1)** the `dd:fuel` rendering of `def:ec`, which remains
the single load-bearing modeling substitution and is in one docstring now *overclaimed*
rather than disclosed; and **(2)** a layer of operational hypotheses (reflection
packages, settlement clocks, exact-theory presentations, patch certificates) that make
several property endpoints strictly narrower than their paper statements — most of these
are disclosed, but three are narrower than their own disclosures admit (F2, F4, F5).
No vacuous theorem, conclusion-in-hypothesis squeeze, or arithmetic stub standing in for
a trader was found; the exploiting traders are real constructions certified through the
emission calculus.

---

## Findings

Severity: **A** = should be fixed or re-disclosed before the endpoint is trusted;
**B** = real narrowing vs. the paper, disclosed or cheaply fixable; **C** = minor.

### F1 (A) — `def:ec`: the fuel-metered class is not certified to contain the paper's class, and one docstring now overclaims it. *(mine + codex #1, convergent)*

`EfficientlyComputable` (`Framework/Criterion.lean:1698`) is the RPN/digit-metered
clocked-interpreter class (`dd:fuel`). The repo's standing position — Foundations.lean,
CLAUDE.md rule 5, the model card — is that this is a **disclosed type-`(c)`
substitution**: a fuel-clocked interpreter, *not* a complexity class. That discipline is
correct, and the model card's calibration facts (`PolyFueled.primrec` upper bound,
`not_polyFueled_two_pow` separation, the two-sided `EF.cost` ↔ token-length seam) are
real. But:

* The `IsLogicalInductor` docstring (`Criterion.lean:1704`) now says the class is "the
  paper's `def:ec` **on the nose**". That is an overclaim the repo has never proved:
  there is **no lower-calibration theorem** ("every trader computed by a poly-time
  machine in the paper's sense is `EfficientlyComputable`"), and the repo's own
  stop-and-reports (the `BigDigits` inverse-operation ceiling, seam 2 route (A)) are
  evidence that the inclusion is at least not free. Codex's proposed separating example
  (a trader emitting atoms with value-exponential indices) is *not* conclusive — the
  digit layer was built precisely to admit large-value tokens as `O(bits)` digit blocks
  — but the burden of proof is on the inclusion, and it is undischarged.
* Direction of risk, stated precisely: for the **property tail** the substitution is
  harmless-to-conservative (each exploiting trader is explicitly certified inside the
  class, so `noExploit` applies to it regardless of how the class compares to the
  paper's). For **`thm:li`** the substitution weakens the theorem: `LIA_is_logical_
  inductor` defeats the fuel-metered class, and if that class is a strict subclass of
  the paper's e.c. traders, the paper's `thm:li` is strictly stronger than the Lean one.

**Remedy:** revert the `Criterion.lean:1704` docstring to the disclosed framing ("the
`dd:fuel` rendering of `def:ec`; see model card"), and record in the model card that
lower calibration (paper-e.c. ⊆ `EfficientlyComputable`) is open — or prove a partial
lower-calibration theorem (e.g. every `PolyFueled`-emittable strategy stream is in the
class, which is true by construction, plus an honest statement of what is *not* known).

### F2 (A) — `thm:li` belief-sequence endpoint does not state computability of the belief-state sequence. *(codex #2, confirmed)*

`exists_computable_beliefSequence_logical_inductor` (`LIACompiler.lean:7178`) concludes:
`IsLogicalInductor (fun n => (𝔹 n).toValuation) DP` + pointwise finite support + `[0,1]`
rationality + cast-exactness. The paper's `def:belstate`/`def:belseq` require a
*computable sequence of explicit finite belief states* — one program that on input `n`
outputs the finite association list. The Lean statement carries computability only of
the **quote table** (through `marketComputable`); no conjunct says a program emits
`(𝔹 n).entries`. Codex's separating example is correct: a uniformly computable
finite-support quote table does **not** imply a computable support listing (hide the
sole nonzero entry at a machine's halting time). The docstring's "this states exactly
that" is therefore currently false.

Mitigating fact (from reading `LIAComputation.lean`): the machinery to close this gap
already exists — `liaPrefixAtFuel` computes the exact `RationalBeliefState` prefix under
a fuel bound, with soundness/completeness/monotonicity lemmas and a `Primrec` bounded
evaluator, so `∃ code, ∀ n, Encodable.encode (liaStates DP n).entries ∈ code.eval n`
should be derivable with the existing dovetail pattern.

**Remedy:** add the entries-emission conjunct to the endpoint (and to `AxiomAudit`), or
soften the docstring to say the state-sequence computability is carried operationally by
`liaPrefixAtFuel` but not yet in the statement. The first option is clearly better and
looks cheap.

### F3 (B) — `LUV` is an abstracted threshold family, not the paper's Θ-definable variable. *(codex #3; known/disclosed; adjudicated: keep disclosed, no new action)*

`structure LUV where gt : ℚ → Sentence` (`Framework/Expectations.lean:57`) has no
uniqueness, monotonicity, boundedness, or Θ-connection; an arbitrary inconsistent
threshold map inhabits it. The docstring discloses this ("`def:luv` (abstracted)",
type-`(c)`), and the real content is reintroduced as certificates (`ValuesAt`,
`WorldValued`, `ExactTheoryPresentation`, the `dd:luv-arith` F7 witnesses that discharge
them from arithmetic for the certified family). This is the correct propositional-substrate
rendering and it is honestly labeled; the audit point is only that **every expectation
endpoint's real trust surface is its accompanying certificate**, which the Tier-2 field
freeze already tracks. No action beyond keeping that framing visible.

### F4 (B) — `thm:ec` (`LUV.expect_converges`) assumes a *rate*, and the disclosure understates it. *(codex #4, confirmed)*

The hypothesis `hval : ∀ᶠ n, ∀ v ∈ pcworlds(D n), ∃ x, v.ApproxValuesUpTo X x n`
(`ExpectationConvergence.lean:978`) aligns stage `n` of the deductive process with grid
precision `n` on the diagonal. The paper's background assumptions (Θ represents
computations, DP Θ-complete) guarantee each threshold fact is *eventually* revealed but
impose **no rate** tying the first `n` grid facts to stage `n`; a legitimate computable
DP can reveal them arbitrarily slowly, and then `hval` fails at infinitely many stages
while the paper's `thm:ec` still applies. The docstring discloses the hypothesis as
"imports 'Θ represents computations'", which undersells it — what is imported is a
*scheduling* assumption strictly stronger than Θ-completeness.

**Remedy:** either weaken `hval` to an eventual-per-grid form (∀ k, ∀ᶠ n, …) if the
proof can absorb it, or rewrite the disclosure to name the diagonal rate explicitly.

### F5 (B) — `ExactTheoryPresentation` demands per-component determination where the paper's `def:affthmval` demands only combination-level determination. *(codex #5, confirmed for `wubexp`)*

Paper `def:affthmval`: a LUV-combination is determined via Θ iff all completed worlds
agree on the value of the **combination**. `BoundedSequence.wubexp`
(`ExpectationProperties.lean:2223`) requires *both* `DeterminedViaTheory` (the paper's
hypothesis) *and* `ExactTheoryPresentation` — one canonical value per **component LUV**
agreed by every completed world (`ExpectationProperties.lean:111`). Codex's example is
apt: `Z = X + (1−X)` is determined in every world even when `X` is not, satisfying the
paper's premise but not `ExactTheoryPresentation`. The same structure feeds the other
statistical-expectation endpoints (`recurringunbiasednessexp`, `prandexp*`). The paper's
theorems therefore cover cases these endpoints exclude.

**Remedy:** disclose per-component determination as a narrowing on these endpoints (the
docstrings currently present `ExactTheoryPresentation` as a representation boundary, not
a strengthened hypothesis), or investigate whether the mesh argument can run from
combination-level determination alone (likely hard: the threshold mesh is built per
LUV).

### F6 (B) — The construction-backed self-trust chain requires `StrictlyIncreasingDeferral`; `thm:st` narrows `p` to an e.c. rational sequence. *(codex #6, confirmed with a correction)*

Paper `def:deferralfunc` requires only `f(n) > n` + time-computability; `thm:cee`,
`thm:ceu`, `thm:ccee`, `thm:st` quantify over any deferral function. Every
`ofRepresentation`/quote-code endpoint in `QuotationAffine.lean`/`QuoteCodeOfMarket.lean`
additionally assumes `StrictlyIncreasingDeferral f`. **Correction to codex:** for
`thm:wub`/`thm:wubaff`/`thm:wubexp` the *paper itself* requires a strictly increasing
deferral function, so the hypothesis is faithful there; the narrowing is real only for
the `cee/ceu/ccee/st` family. Additionally, `lic_self_trust`'s package takes `p : ℕ → ℚ`
with poly codes, whereas the paper's `thm:st` allows `p` to be **P-generable** (varying
continuously with market prices).

**Remedy:** disclose both narrowings at the endpoints (one docstring line each), or lift
them (strict-increase: possibly by monotone re-indexing; P-generable `p`: would need the
threshold sentence family to take feature-valued thresholds — likely a real extension).

**Update (2026-07-29): the `p` narrowing is lifted.** The threshold family did *not* need
feature-valued thresholds; what was missing was a program for `p` recoverable from the
feature presentation.  `PGenerableRat.computable` (`Construction/LIACompiler.lean`) builds
it: parse the emitted serialization back to the feature
(`RpnSpliceStream.feature_primrec`, on `deserializeTrades_prim` + `unRpn_prim`), evaluate
it exactly against the certified market at one interpreter clock
(`marketFeatureValueAtFuel`, on `efRatCompiledEval` guarded by `EF.priceQueries`
readiness), and minimize over the clock.  `lic_self_trust_closed` and
`lic_no_expected_net_update_conditional_closed` now take `PGenerableRat` for `p`/`w`.
The deferral narrowing (F6a) stands as future work.

### F7 (B) — `thm:scon`: the inconsistent-conditioning branch is uncovered, and `hjoint` is mislabeled as "the paper's premise". *(codex #7, confirmed)*

The paper's `thm:scon` has no consistency hypothesis: if `Θ ∪ {ψ}` is inconsistent the
conditioned market is (trivially) a logical inductor over the inconsistent theory. All
public constructors (`lic_conditioned_fixed_unconditional` etc.,
`UnconditionalOverLIA.lean:118`) require `hjoint : ∀ n, ∃ v, v.ConsistentWith (D n) ∧
v.Holds ψ`, and the docstring calls this "the paper's joint consistency premise" — the
paper states none. The missing branch should be nearly free: once some stage's
plausible-world set relevant to the union process is empty, every trader's assessment
set is bounded and `noExploit` is vacuous; `marketComputable`/`processComputable` of the
conditioned pair are already available.

**Remedy:** add the degenerate branch (or an explicit disclosure that the formalized
`thm:scon` is the consistent-condition case) and fix the docstring's attribution.

### F8 (B) — `thm:ifp` is conditional on `EfficientPrefixPatch`, which currently has no LIA inhabitant. *(codex #8; already a disclosed stop-and-report; no new content)*

`lic_iff_of_finitePerturbation` requires patch certificates for both markets; the file
and `AxiomAudit.lean` (RpnFreeze block) already disclose that `preserves_ec` has no
inhabitant at the collapsed class (the `BigDigits` inverse-operation ceiling, seam 2
route (A)). Codex independently flagged the same gap, which is corroborating evidence
that the disclosure is at the right place; nothing new to fix beyond F1's calibration
note, of which this is the concrete instance. One nuance worth keeping: the Lean's
"agree from `cutoff` on" difference notion *properly contains* the paper's
"finitely many places", so the perturbation notion itself is not narrowed.

### F9 (B) — `thm:benford`/`thm:prand` endpoints carry a settlement-clock infrastructure hypothesis absent from the paper. *(mine; not flagged by codex)*

**CORRECTED (same day).** The observation (endpoints narrower than the paper) was
right; the diagnosis was wrong. This section originally argued "decidability alone
yields no computable bound on settlement time, so the clock is a genuine strengthening."
No bound is needed by either side: the paper's `app:prandaff` proof *constructs* the
settlement occupancy as the dovetailed lower approximation `DefinitelySettled`
(tex:4863–4882) — an unbounded eventual, exactly the shape of the repo's
`eventually_inactive` field — and the repo already contained the corresponding
constructor, `PatientSettlementClock.ofComputations`, discharging the clock from
`IsLogicalInductor`'s own `marketComputable`/`processComputable` with **zero added
hypotheses**. It had zero call sites: the narrowing was a wiring omission, not a
modeling boundary. (The case the original diagnosis describes is `thm:wub`, where the
paper genuinely assumes timed feedback and the repo renders it faithfully.)

**Resolution:** fixed — all nine paper-facing `thm:prandaff`/`thm:prandexp`/
`thm:prand`/`thm:benford` endpoints are clock-free (`patientClockOfInductor` derives
the clock internally); `PseudorandomFrequencyInfrastructure` is deleted; the clock's
provenance is now kind `C` (composition of the paper's own dovetail), not type-`(c)`.
Two paper errata surfaced by the eliminability investigation are recorded as PE3/PE4 in
`notes/logical-induction-paper-errata.md`.

### F10 (C) — Expectation precision is off by one under the repo's day-index convention. *(codex #9, confirmed)*

`Foundations.lean` fixes "Lean day `n` = paper day `n+1`"; `LUV.expect P n := expectApprox
(P n) n` uses precision `n`, so Lean day `n` pairs paper day `n+1` with paper precision
`n` (and day 0 gets the degenerate precision-0 operator, identically `0`). The paper
calls `k = n` an arbitrary choice, and every exported conclusion is asymptotic, so no
theorem's truth is affected — but as a rendering of the finite-stage operator `𝔼_n` it
is off by one against the repo's own convention. Fix: precision `n+1`, or a convention
note at `expect`.

### F11 (C) — `Valuation := Sentence → ℝ` vs. the paper's `[0,1]` codomain. *(codex #10; disclosed; no action)*

Deliberate and documented (total real-valued denotations for the feature DSL; the range
constraint imposed at markets/worlds where consumed). Every endpoint that needs the
range carries it (`price_mem_Icc`, `hP` plumbing). Fine as is.

### Cross-cutting note — the `hworld` hypotheses

Most tail endpoints assume `∀ n, ∃ v, v.ConsistentWith (DP.D n)` (stage consistency).
The paper never states this because it works over a consistent Θ throughout. In the
propositional rendering it is necessary (with inconsistent stages the plausible-world
quantifier degenerates), satisfiable (any consistent theory's DP), and visible in every
statement. Correct disclosure discipline; no action.

---

## Verified faithful (read line-by-line against the paper)

* **`def:tf`/`def:valfeature`** — `EF` is the paper's grammar on the nose (price
  features, ℚ, `+`, `×`, `max`, `max(1,·)⁻¹`), with `var`/`letE` a disclosed,
  denotationally conservative sharing extension; continuity **proved** for the whole
  DSL; `EFn n` a genuine `CommRing` (subring of the pointwise function ring); rank of
  the paper's running example computes to 7; both non-vacuity witnesses real.
* **`def:tradestrat`/`def:trader`** — `Strategy.value` is exactly
  `∑ eᵢ(𝓥)·(w(φᵢ) − 𝓥ₙ(φᵢ))` (the cash term determined by the pairs, per the paper's
  own normal form); rank discipline `≤ n`; duplicate sentences aggregated before
  pricing in the market maker (load-bearing and handled).
* **`def:exploitation`/`def:lic`** — plausible assessments and
  bounded-below-not-above verbatim (0-index shift disclosed); `Exploits` refutable
  (`Trader.zero_not_exploits`), so the criterion is non-vacuous.
* **`def:world`/p.c./`def:dedproc`** — worlds as Foundation Boolean valuations of
  atoms = exactly the p.c. worlds; `cworlds` as stage-wise consistency;
  `DeductiveProcess` nested finite stages with a separate computation certificate
  matching the paper's "computable nested sequence".
* **`def:condp`** — capped ratio including the `V(ψ)=0 ↦ 1` convention, verbatim.
* **`def:e`** — `𝔼_k(X) = (1/k)·∑_{i<k} V(⌜X > i/k⌝)`, verbatim (modulo F10).
* **`dd:asymp`** — `≈ₙ/≲ₙ/≳ₙ` match the paper's `≂ₙ/≲ₙ/≳ₙ` including the
  liminf-orientation of the one-sided forms.
* **Statements checked and matching their paper nodes in analytic content**:
  `lic_preemptive_learning` (`thm:tbo`, both liminf/limsup equalities with correctly
  oriented `sup_{m≥n}`/`inf_{m≥n}`), `lic_persistence_of_knowledge` (three clauses of
  `thm:perkno`), `lic_provind`(_true/_false) with the retained fragments honestly
  quarantined in `AxiomAudit`, `lic_nonDogmatism`(+dual) in the correct stage-wise
  non-refutability form, `lic_limitCoherence` (probability measure on `PCWorld` with
  `μ{v ∣ v ⊨ φ} = P∞(φ)` and a.e. theory-consistency — Gaifman's three conditions
  packaged as the paper intends), `lic_occamBounds`/`_ofUniversalPrefix` (`C·2^{−κ(φ)}`
  with a **constructed** universal prefix machine, Kraft proved, invariance theorem
  earning "universal"), `lic_domination_universalSemimeasure` over any presented
  lower-semicomputable continuous semimeasure with the Dovetail construction
  discharging universality, `simcal`/`recurringunbiasedness` (both clauses, limit-point
  form), `lic_wub` (feedback hypotheses = the paper's own), the MetaLearning family as
  honest `provind` specializations through representation structures, and the
  introspection/self-trust family shapes (`thm:ref` two-sided ε-control with the
  rational ε-sequence constructed, `thm:st` inequality with world-dependent `A`).
* **Construction** — Brouwer proved in-repo from Sperner (Aristotle-produced body,
  kernel-validated, axiom-clean); `trading_firm_dominance` is the real `lem:tfdom`
  (exploiting e.c. trader ⇒ firm exploits, via the single-decode enumeration);
  `LIA_is_logical_inductor` assembles market-maker + budgeter + firm with no residual
  semantic premise beyond the deductive-process computation.

## Codex adjudication summary

Ten findings received; none fabricated, all file/line cites checked out. Incorporated
as-is: #2, #4, #5, #7, #9. Incorporated with reframing: #1 (severity rests on the
docstring overclaim + missing lower calibration, not on its separating example, which
the digit layer plausibly absorbs), #6 (its `wub`-family instance is wrong — the paper
requires strict increase there — but correct for `cee/ceu/ccee/st`), #8 (already a
disclosed in-repo stop-and-report; treated as corroboration), #3 and #10 (real but
already-disclosed modeling choices; no action). Codex missed F9 (settlement clocks) and
the `hjoint` docstring misattribution inside F7 (it found the branch gap itself).

## Suggested fix order

1. F1 docstring reversion + model-card lower-calibration note (trust-surface honesty,
   ~zero cost).
2. F2 entries-emission conjunct (machinery exists; upgrades the headline theorem to the
   paper's actual `thm:li`).
3. F7 degenerate branch + docstring fix (small).
4. F10 precision `n+1` (small, touches many proofs' indices — schedule with care or
   convention-note it).
5. F4/F5/F6/F9 disclosures (ledger honesty; lifting any of them is real work and should
   be triaged separately).

## Future-work register (post-wave, 2026-07-29)

All with verified obstructions, none blocking: (1) dd:fuel lower calibration — realistic
route is a two-model architecture (`def:ec` at a machine class, firm enumerates it via
poly-overhead universal simulation, fuel calculus kept as certification tool via the easy
inclusion); the pure bridge theorem is judged unlikely (~10–15%); staged plan in
`notes/two-model-ec-feasibility.md`. (2) Injective deferral → bare `f n > n`: **DONE (2026-07-30)** — the
`thm:cee`/`thm:ceu`/`thm:ccee`/`thm:st` chain now assumes only `def:deferralfunc`
(`f n > n` plus poly-clocked emission) at all twelve endpoints. The originally-registered
fix (sign-gated fibre sum forcing each `|dₖ| → 0`) was *unsound* and stays retired; the
landed device is the division-free **first-violator selector** over the deferral fibre
(`selectorFeature` with `firstSuccess_sum_le_one`/`firstSuccess_forces`), a variable-width
affine combinator (`AffineCombination.blockSum`), the paired-index emission certificate
`PairedWeighting` (rank `≤ z.unpair.1`, the day of evaluation), and
`DeferralFibre.deferred_block_price_tendsto_zero`, instantiated by
`crossPrecision_/numericQuote_/conditional_/selfTrust_deferred_tendsto_zero`. The
image-gated `deferralPreimage` layer is gone from this chain (it survives only for the
`thm:wub` feedback chain, where the paper itself asks for strict increase).
(3) **DONE
(2026-07-29)** — EF parser + market-relative evaluator: `RpnSpliceStream.feature_primrec`
recovers the feature program from the emitted serialization and `PGenerableRat.computable`
evaluates it against the certified market by clock minimization (both in
`Construction/Witnesses/M7Witnesses.lean`, built on the pre-existing
`efFromSerializedTokens` / `MarketComputation.denoteRatComp`). `lic_self_trust_closed`
and `lic_no_expected_net_update_conditional_closed` now take P-generable `p`/`w`
(`def:ece`); the `thm:st`/`thm:ccee` closed-form threshold seams are closed. The
evaluator is deliberately `Computable`, not fuel-bounded — evaluation dovetails the
market program, and a plain `Nat.Partrec.Code` quote code needs exactly that.
(4) Propositional compactness in Foundation (growing-form `thm:scon`).

Item (4) is **done** (2026-07-29): `Framework/Compactness.lean` proves compactness directly
over Cantor space (`DeductiveProcess.exists_consistentWithTheory`), and `hjoint` is deleted
from `lic_conditioned_growing_ofComputationsAndMarket` and
`lic_conditioned_growing_unconditional`, which now case-split on per-stage satisfiability of
the union process exactly as the fixed-sentence form does; `thm:scon` is complete.

---

## Completing strength pass (2026-07-31) — the headline count was wrong

The `51 of 53 at paper strength` figure carried in the README until today was built on a
prior audit that re-derived only ~28 of the 53 rows and flagged the rest as endpoint-level
spot checks. A dedicated pass re-derived 35 rows from their *elaborated final signatures*
against the paper text, instructed to assume the unchecked half was no better than the
checked half (which had a ~39% mis-tier rate). It found 11 over-claims and 0 under-calls —
a 31% mis-tier rate, confirming the prior.

**Corrected: 37 of 53 at paper strength, 16 qualified.** The corrections fall into four
groups, of which the first is by far the most consequential:

1. **Whole-value metering is a class restriction, not a fuel certificate** (10 rows:
   `thm:epr`, `thm:er`, `thm:ref`, `thm:st`, `thm:wub`, `thm:cee`, `thm:ceu`, plus
   `thm:pac`, `thm:pazfc`, `thm:dontwait` on the `f`-class analogue). The classification
   file's own rule says a `dd:fuel` certificate on the statement's own data does not lower
   a row — the fuel model is charged once, globally, at `def:ec`. That rule is right for
   `RpnSentenceCodes`, the symbol-metered faithful rendering. It is **wrong** for
   `PolySentenceCodes`/`PolyThresholdCodeSeq`/`PolyNatCodes`, which meter the single
   pair-code token, and which the repo *itself proves* strictly narrower:
   `ordinaryBitPrefixCodes` + `not_polySentenceCodes_bitPrefixSentence` exhibit a
   paper-admissible e.c. sentence family no whole-value hypothesis admits (executable check
   re-run and confirmed compiling at this commit).

   Why it was missed for so long: the two classes are one coercion apart
   (`RpnSentenceCodes.ofPolySentenceCodes`) and every narrowed endpoint *opens by applying
   that coercion*, so the hypothesis reads as an idiomatic fuel certificate. The tell is
   that `hφ` is **also passed as data** to the quote-code constructor
   (`theoremPriceQuoteCode T φ hφ`) — the quote compiler feeds the sentence code as a number
   into the market program, which is what forces whole-value metering. So this is not a
   one-line generalization; it is the fuel boundary biting the unconditional route. The
   `[IsLogicalInductor]`-conditional endpoints for all ten are at paper strength.
   The metering rule is now written into the classification file's header.

2. **`thm:ec`, `thm:expcoh`, `thm:perexpkno` — an unearned entailment claim.** All three
   rows justified a retained stage-quantified premise (`daily_value` / `hval`, over
   `v.ConsistentWith (DP.D n)`) as "provably entailed by the paper's `def:luv` world-value
   fact" (`WorldValued`, over `v.ConsistentWithTheory DP`). **No such entailment lemma
   exists** — grep shows `daily_value` is only ever *supplied* by construction
   (`LUVSyntax.lean:300`, `LUVExpectationCertified.lean:449`). The prose asserted a proof
   obligation as discharged. Proving it (propositional compactness, as
   `Framework/Compactness.lean` already does for `thm:scon`) would raise all three together
   — this is the single highest-value open item on the count.

3. **`thm:obu`** takes the paper's own WLOG preprocessing as data
   (`EfficientRepeatedEnumeration`, the padding-and-repeating the paper performs *inside*
   its proof at tex:5651-5656) while never assuming the source is c.e., which is the paper's
   actual hypothesis. No `c.e. → EfficientRepeatedEnumeration` constructor exists, so the
   interface is undischarged; and `sound : ∀ j, ∃ i, sequence j = source i` forbids the
   paper's own ⊤-padding unless `⊤ ∈ range source`. → qualified.

4. **`thm:affprovind` was mislabeled, not weak** — the one place the auditor's severity was
   too harsh, and worth recording as a calibration note. Its two annotated endpoints
   (`lic_provind_true`/`_false`) are sentence-level, i.e. the `k=1`, `b ∈ {0,1}` special
   case, and `lic_provind` is literally their pair — so the node read as covered only by
   `thm:provind`'s own theorems. But the genuine affine statements (real `b`, over
   `cworlds(Θ)`, all three comparison forms) **do exist and are proved**:
   `PolySequence.affine_provind_theory_ge/_le/_eq`. They simply carried no `Paper node:`
   line and were absent from the audit inventory. Fixed by retagging rather than
   downgrading: the three are now `theorem`s with `Paper node: thm:affprovind`, added to
   `AxiomAudit.lean`; `lic_provind_true`/`_false` are retagged to `thm:provind`, matching
   what the audit file's own tier note already said about them. Row stays `conditional`.

   Calibration lesson for future passes: an auditor told to judge from annotated endpoints
   will report a *labeling* defect as a *strength* defect, because from inside that lens the
   two are indistinguishable. Always check whether the paper-strength statement exists
   elsewhere in the file before accepting a tier drop.

**Residual uncertainty, stated plainly.** 35 of 53 rows were re-derived in this pass; two
more (`thm:expcoh`, `thm:perexpkno`) were corrected by propagating its `thm:ec` finding, and
two (`thm:cee`, `thm:ceu`) were corrected by propagating its metering finding after I checked
their signatures directly. The remaining rows carry classifications from earlier passes and
have not been independently re-derived from signatures. Given two consecutive passes at a
31–39% mis-tier rate, **37 should be read as an upper bound that has been rounded against
ourselves, not a settled figure.** The next pass should take the un-re-derived remainder,
starting with the `def:*` rows and `thm:ifp`/`thm:scon`/`thm:loe`.

---

## Repair wave (2026-08-01): 37 → 46 of 53 at paper strength

Three packets landed against the completing pass's findings. Counts re-derived from the
merged signatures each time, never from the fixers' reports.

**Quotation family metering (6 rows → `complete`).** `thm:epr`, `thm:ceu`, `thm:ref`,
`thm:wub`, `thm:er`, `thm:cee` restated at `RpnSentenceCodes` / `LUV.RpnThresholdCodeSeq`.
The diagnosis in the 2026-07-31 entry above was itself wrong and is corrected there: the
quote-code constructors take only `Primrec fun n => encode (φ n)` from the hypothesis, and
`RpnSentenceCodes.primrec` already supplies it. `thm:wub` was separately re-derived against
tex:1249-1258 rather than promoted on the metering change alone.

**`thm:st` (metering fixed; row held at `qualified` on a new finding).**
`indicatorProductLUV_rpnThresholdCodeSeq` emits the `⋏`-shell as tokens via
`RpnSentenceCodes.and` instead of a `Nat.pair` on Gödel values — and turned out *simpler*
than the whole-value original, because `RationalQuoteCode.poly` is definitionally the
paired-index fact needed. The fixer recommended promoting the row to `complete`. **Not
taken.** Re-deriving the signature showed a premise the paper does not ask for:
`hδinv : PolyRatCodes (fun n ↦ 1 / δ n)`, where tex:2093 requires only that `δ` be an e.c.
sequence of *positive* rationals. It is very likely redundant, but `exact?` finds no lemma,
so the row does not claim it. Recorded as the cheapest open item.

**`thm:ec` / `thm:expcoh` / `thm:perexpkno` (3 rows → `conditional`) — and the finding
above was half wrong.** The 2026-07-31 entry said the fix was to prove a compactness
entailment. There is nothing to prove: tracing where the premise is *consumed* shows
`thm:ec` reads a world value only inside `filter_upwards [hae]`, with
`hae : ∀ᵐ v ∂μ, v.ConsistentWithTheory DP` from `lic_limitCoherence`. Every world at which
a value was ever demanded is already completed-theory, and the old helper
`approxValuesUpTo_of_consistentWithTheory` was doing the *trivial* stage⇒theory direction.
So the premise was not under-justified, it was **excess**: stating it at the paper's
`cworlds(Θ)` quantifier and deleting the helper is strictly simpler and adds no surface.
Upstream, `TheorySemantics.stage_values` — a stage-quantified field with no constructor
anywhere in the repo — was deleted outright; that was the real smuggling site for the two
`_ofSyntax` endpoints.

**Two general lessons, both instances of the same error at different levels.** The
metering misdiagnosis and the compactness misdiagnosis were both cases of reasoning from a
hypothesis's *shape* instead of its *use*: "passed as data, therefore load-bearing" and
"stated at a stronger quantifier, therefore needs a bridge". In each case the cheap check —
grep the consumption site — settles it in minutes and was skipped. This is now a standing
check in `notes/consolidation.md`.

**Remaining 7 qualified:** `thm:ccee` (mesh slack, type-`(c)`), `thm:st` (`hδinv`),
`thm:pac`/`thm:pazfc`/`thm:dontwait` (evaluated horizon in the claim code, needs an
unevaluated-term schema), `thm:obu` (WLOG preprocessing taken as data), `thm:ifp` (fuel-class
closure gap). Confidence caveat from the completing pass still stands: 46 is an upper bound
rounded against ourselves, and the un-re-derived remainder is still worth a pass.

### `thm:st` to `complete` (2026-08-01) — 47 of 53

`PolyRatCodes.inv_of_pos` (`Framework/Computable.lean`) derives the reciprocal code from
`PolyRatCodes δ` plus positivity, so `lic_self_trust_closed` drops the `hδinv` binder. Its
hypotheses are now exactly tex:2093's four — deferral function, e.c. sentences, e.c.
**positive** rationals, P-generable probabilities — with `SelfTrustQuote` constructed and the
quoted product symbol-metered. Row moves `qualified` → `complete`.

Estimate calibration, recorded because two estimates earlier in the same wave were wrong:
predicted "~25 lines, no open question", actual ~30 lines and one scratch-file iteration.
The prediction was accurate because it was made *after* checking the three ingredients
(`encode_rat_eq` is `rfl`; positivity keeps the numerator on the `2n` branch of ℤ's sign
fold; Mathlib has `Rat.den_inv_of_ne_zero`/`num_inv`) rather than from the shape of the goal.

~8 `hδinv` occurrences remain in `ComputationDP.lean`, `QuotationAffine.lean` and the
`_ofRepresentation` layers. They are now all dischargeable from `hδ` + positivity and are
scheduled as a consolidation pass; they affect no tier.

### `thm:expprovind` to `conditional` (2026-08-02) — 46 of 53

`lic_expect_combination_provind_ge/_le/_eq` now take exactly tex:1753-1760's premise: a
one-sided bound over `cworlds(Θ)`, worlds free to disagree. `DeterminedViaTheory` is gone
from them and survives as `_ofDetermined` corollaries, which `thm:recurringunbiasednessexp`
/ `thm:wubexp` / `thm:prandexp` genuinely need (`def:affthmval`). Under the consolidation
discipline the paper-matching form took the plain name and the determinacy form was
suffixed, rather than leaving the paper's own statement behind an `_ofWorldBound` tag.

`WorldValued` is retained and is *not* the over-restriction: it is the paper's own
representation premise, and operationally it produces the valuation `ν` the bound is stated
against.

**Third estimate miss of the wave, same root cause — worth recording because the pattern is
now unmistakable.** Predicted "1–2 sessions, filter-bound factoring as the swing factor";
actual ~20 minutes of editing. I had verified that `expcoh` exists and supplies the needed
liminf chain, which is true and irrelevant: **the combination endpoints never call `expcoh`.**
They route through the diagonal mesh into `affine_provind_theory_ge_const`, which already
absorbs `completedAffineExtrema_filterBounds` internally, so the hypothesis swap cost one
`have` per endpoint.

All three bad estimates this wave (whole-value metering "structural"; compactness entailment
"needed"; this one) came from reasoning about a *hypothetical* implementation rather than
reading the existing proof body. Checking that the ingredients for a plausible route exist
is not the same as checking which route the code takes. The cheap discipline: before
estimating a change to an endpoint, read that endpoint's proof body and see what it actually
calls.

Open, unmeasured: whether `completedLow`/`completedHigh` filter bounds factor cleanly out of
`expcoh`. That question was never reached and still governs the cost of any node that *does*
route through `expcoh`.

---

## 2026-08-02 — Independent full re-audit of the frozen surface (all 66 rows)

Fresh pass, distinct model family from the fix waves, run over the freeze point
`aab35a8` before the pre-review consolidation wave. Method: every row's tier re-derived
from the strongest endpoint's elaborated signature (never from row prose); entailment
claims checked against a named lemma; plus the two standing mechanical checks
(zero-call-site inventory constructors; inhabitation lens over Tier-2 structures).

**Result: zero mis-tiered rows.** All 66 rows verified at their claimed tier — 46 of 53
theorem nodes at paper strength (16 of those instantiated over the constructed inductor,
counted per-label by the checker as instantiated=26/universal=30/qualified=10 including
the 13 def nodes), 7 theorem nodes qualified with accurate one-line reasons. The three
prior systemic failure modes (whole-value metering counted as routine fuel certificate;
prose-asserted entailments with no lemma; discharge constructors never wired to their
consumers) were each re-checked explicitly; none recurred at the row level.

Findings below the row level, all repaired in the same wave (see
`notes/consolidation.md`, "Post-freeze verification + consolidation wave"):

* **F-2026-08-02-1 (dead code, standing-check round 4):** `BoundedEvalnCompiler` +
  constructor, `representedSemidecidableClaimsOfComputation`, and the two Tok-class
  conditioning translation lemmas had zero call sites. Deleted. None affected a tier.
* **F-2026-08-02-2 (inhabitation):** `LUVCombinationSyntax` — caller data of the four
  `_ofSyntax` expectation endpoints — still had no constructed inhabitant (open since
  2026-07-30). Now witnessed by `ordinaryLUVCombinationSyntax`, non-degenerate
  (index-varying LUV family). `BoundedComputation`, `SemidecidableComputation`,
  `FeedbackTruthComputation` remain without ground-level N+ witnesses; all three are
  trivially inhabitable (fixed halting machine, constant truth) and their endpoints'
  tiers do not rest on them — recorded as nice-to-have, not defect.
* **F-2026-08-02-3 (latent over-claim, thm:lp):** `lic_paradox_resistance_ofDiagonal`
  and its `_unconditional` form carried `hwidthInv : PolyRatCodes (1/width)`, derivable
  from `hwidthPos` — the same excess premise `thm:ref` shed at the freeze. Removed,
  with the rest of the hδinv family (six paper-facing endpoints). No tier moved.
* **F-2026-08-02-4 (redundant premise family):** the `(b, hshare)` share-norm bound on
  ~20 expectation endpoints is derivable from `BoundedSequence.bounded`
  (`shareNorm ≤ l1Norm` + `exists_rat_gt`). Removed wherever `b` is not load-bearing in
  hypothesis types; the paper-facing statements now carry exactly `def:blcp`'s data. No
  tier moved — a derivable premise never lowers strength — but several rows' "retains
  only WorldValued" prose is now literally rather than approximately true.
* **F-2026-08-02-5 (doc drift):** `LogicalInduction/README.md` contradicted itself on
  `thm:st`'s metering (three-node vs four-endpoint whole-value lists, and a "needs a
  token-level `⋏` emitter" paragraph describing work that had landed). Corrected.
