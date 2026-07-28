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

`lic_learning_pseudorandom_frequency*` (`HistoricalMaturity.lean:1688`) and the varied
variants require `PseudorandomFrequencyInfrastructure` / `PatientSettlementClock` — an
e.c.-coded, antitone activity clock that eventually deactivates and certifies settlement
of each centered affine combination. The paper's `thm:prand` hypotheses are: Θ-decidable
sentences, P-generable patient divergent weightings, and pseudorandomness — **no
computable settlement clock**. (Contrast `thm:wub`, where the paper *does* assume
truth-computability in `O(f(n+1))` time, faithfully rendered by `FeedbackTruthSequence`.)
Decidability alone yields no computable bound on settlement time, so the clock is a
genuine strengthening — the "historical maturity" residue that the file's header says
was being shrunk. On the positive side, the pseudorandomness hypothesis itself is
*weaker* than paper-`benford`'s (it quantifies only over `f`-patient weightings, which
is the `thm:prand` form the paper calls a strict generalization), so the two deviations
pull in opposite directions and neither subsumes the other.

**Remedy:** disclose the clock as a type-`(c)` operational premise at the endpoint (the
structure docstring says "only the settlement clocks" as if residual — make the ledger
say *why* it is believed necessary in the propositional rendering, or discharge it for
the arithmetic instantiation the way `M7-FEEDBACK-TRUTH` was).

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
