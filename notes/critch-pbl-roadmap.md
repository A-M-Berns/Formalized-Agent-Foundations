# Roadmap: Formalizing Parametric Bounded Löb (Critch 2016/2019)

**Repo:** `Formalized-Agent-Foundations` · **Target paper:** Critch, *Parametric Bounded Löb's Theorem and Robust Cooperation of Bounded Agents* · **Base:** FormalizedFormalLogic/Foundation (IΣ₁ arithmetization layer)

**Thesis of the project:** machine-check PBL (Theorem 3) and robust cooperation (Theorem 4) with an explicit, honestly disclosed trust surface — and surface the theorem's sensitivity to proof-encoding choices (numeral size, proof-length measure), which the paper states as assumptions on S but which no existing mechanized arithmetization satisfies.

---

## Standing scope decisions (make once, document in README)

1. **Proof-size measure.** Replace "characters of written proof with abbreviations" by a measure native to Foundation's encoding — expected choice: an internal derivation-size function (nodes/symbols), *not* Gödel-number magnitude (pairing blowup breaks the additive bound algebra). Disclose the substitution; theorems only need *some* computable expansion function E for the chosen measure.
2. **Agents as sentence families.** Formalize G-fairness via its derivability conditions (the paper's eq. 6.5) — all Theorem 4 actually uses. "FairBot-the-program is G-fair" (program semantics, quining, proof search in arithmetic) is **out of scope**, mirroring the Barasz CliqueBot boundary.
3. **Quoting stays unary.** Efficient numerals are introduced only on the parameter-specialization path (the k, m, n inside bounded boxes). The Gödel-quote/diagonal machinery keeps Foundation's unary numerals; those costs are constant in k and absorbed by asymptotic hypotheses.
4. **Numeral-cost parameter ν.** All interface properties are stated relative to an abstract numeral-cost function ν(k), never with O(lg k) baked in. An lg-cost axiom would be undischargeable for Foundation's current (unary) numerals — a fake-safe interface.

---

## Phase 0 — Probe (≈1 week) — *de-risking, no public commitment before this*

- [ ] Define the internal-bound box: `bewBounded` as a semisentence with the bound as an object-level variable, over Foundation's `proof T` (generalizing `RestrictedProvable`, whose bound is meta-level).
- [ ] Decide the size measure: prototype an internal derivation-size function via the PR-construction machinery; confirm additive behavior under the derivation constructors actually used.
- [ ] Check exp-totality plumbing for bounds of form 2^a in the IΣ₁ setting (Foundation already uses `Exp.exp` here).
- [ ] Prove one toy bounded lemma end-to-end (e.g., bounded Mono: □ₐφ → □_{a+c}ψ from ⊢ φ→ψ).
- **Gate G0:** measure chosen and toy lemma closed → announce target publicly (LW post can name Critch).

## Phase A — Interface-relative PBL + Theorem 4

- [ ] `BoundedProvability` structure + bounded-HBL typeclasses, copying Foundation's `ProvabilityAbstraction` design pattern (upstream candidate).
- [ ] Interface axioms, parametrized by ν and E: Implication Distribution, Quantifier Distribution(ν), Bounded Necessitation(E), Bounded Inner Necessitation(E). Document each with the paper's informal argument and its dischargeability status.
- [ ] Parametric Diagonal Lemma — expected to be a short extension of Foundation's `substNumeralParams` / `multidiagonal` machinery (risk retired in reconnaissance).
- [ ] PBL (Thm 3) with explicit constants replacing O(·); hypotheses stated relative to (E, ν).
- [ ] Theorem 4 from interface + G-fairness derivability conditions; feasibility hypothesis stated as an explicit (E, ν) condition, with a remark that ν ∈ O(lg k) requires efficient numerals (Phase C).
- **Deliverables:** first mechanized PBL; encoding-sensitivity of Thm 4's feasibility made precise. Publishable/postable on its own.
- **Gate GA:** list every lemma invoked inside a bounded box (input to Phases B/C audits).

## Phase B — Discharge for the real encoding, unary-honest

Grind-heavy, blocker-light; highly parallelizable orchestration work.

- [ ] Size algebra: instrument the internal entailment combinators (Bootstrapping layer) with provable size bounds — bounded specialization: |instantiate d t| ≤ |d| + O(|t|); bounded MP; etc.
- [ ] Prop 1 (Implication Distribution) for the actual encoding.
- [ ] Prop 2 (Quantifier Distribution) with ν = actual (unary) numeral cost.
- [ ] Props 3–4 with explicit E: size-instrument the formalized Σ₁-completeness lineage (`term_complete` etc. — constructive by explicit induction, hence instrumentable; confirmed in reconnaissance). Note: *some* computable E always exists (□ₖφ is true Σ₁ ⇒ provable by search), so the content is E's growth rate.
- **Deliverables:** PBL fully discharged (unary-cost hypotheses); first explicit E for a real proof encoding; verdict on whether E is subexponential.
- **Gate GB:** measured E growth + ν determine whether faithful Thm 4 is reachable via Phase C or must be restated.

## Phase C — Efficient numerals → faithful Theorem 4 (builds on B)

The riskiest well-defined component; risk concentrated in one place.

- [ ] Meta-level binary numerals (binNum via ·(1+1) and +1; O(lg n) term size; val lemma). Days.
- [ ] **Internal numeral-code function** k ↦ ⌜binNum k⌝ — needs binary/course-of-values recursion; no packaged strong-recursion combinator found in Bootstrapping. Routes: build the combinator (pattern exists in-house from the LI fuel evaluator) or define via Σ₁ digit-sequence graph. ← *primary residual blocker location.*
- [ ] Substitution-interface lemmas for binNum (`subst` is term-generic; mirror the ~10 `substNumeral` lemmas).
- [ ] Short-proof discipline: bounded-context lemmas stated only in binNum form (structural enforcement of "never convert unary↔binary inside a box" — the internal conversion proof is Θ(k)). Audit against the Gate-GA lemma list.
- [ ] Re-run Thm 4 ledger with ν ∈ O(lg k); recover the paper's feasibility condition.
- **Fallback if blocked:** publish Thm 4 in encoding-weakened form with the obstruction documented — itself a finding.

---

## Risk register (ranked)

| # | Risk | Phase | Status / mitigation |
|---|------|-------|---------------------|
| 1 | Internal binary-recursion combinator absent | C | Two independent routes; blocker requires both failing |
| 2 | Size algebra doesn't compose over some combinator | B | Constructive Σ₁-completeness confirmed; expect grind not blockage |
| 3 | Ledger constants explode past the asymptotic slack | A/B | All O(·) made explicit from the start; slack is generous |
| 4 | Interface axiom later found undischargeable | A | ν-parametrization; each axiom carries a dischargeability note |
| 5 | Program-semantics scope creep (agents as code) | — | Excluded by standing decision 2 |
