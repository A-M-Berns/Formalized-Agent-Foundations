# Finite Factored Sets — Adversarial Audit

**Repository:** `A-M-Berns/Formalized-Agent-Foundations`  
**Branch:** `finite-factored-sets`  
**Audited head:** `4cbb1a73b3a9c7252135a9ce1142dfb1d10429e0`  
**Date:** 2026-08-17  
**Auditor:** GPT-5.6 Sol, read-only external review  
**Paper:** Scott Garrabrant, *Temporal Inference with Finite Factored Sets* (arXiv:2109.11513)

---

## 1. Executive verdict

### Formalization verdict: **PASS for the ruled scope**

At the audited commit, I find no substantive reason to send the project back into theorem-proving mode. The branch has the shape of a finished formalization rather than a proof collection:

- the paper source and matching PDF are committed;
- the ruled scope is explicit;
- the claimed paper-facing surface is `sorry`-free and axiom-clean;
- non-vacuity is discharged by constructed finite and infinite witnesses rather than by antecedent assumptions;
- the hard finite/infinite boundaries are tested with counterexamples, not only asserted in prose;
- the consumer API is documented and exercised by downstream-style tests importing only `FiniteFactoredSets.API`;
- the live head passes the repository's CI, including the FFS node checker, trust-surface freshness, paper wiring, API tests, and the default Lean build containing `AxiomAudit`.

The formalization therefore passes the central FAF test: the Lean kernel is not merely proving implications whose meaningful antecedents have been assumed.

### Publication / repository-closeout verdict: **CONDITIONAL PASS**

I found no open mathematical proof obligation inside the ruled scope, but I would not call the artifact *fully closed by the literal repository standard* until the following are resolved or explicitly waived:

1. **Human statement/definition read-through:** root `CLAUDE.md` says the work is not called done until Anson reads every top-level statement and definition on the consolidated surface. I found no durable record on this branch that this FFS read-through has occurred.
2. **Final-audit reproducibility:** `FiniteFactoredSets/KNOWLEDGE.md` says round 11's raw findings and parked adjudication prompts live under `.harness/audit/`; `.harness` is absent from the audited branch. The conclusions are summarized, but the evidence bundle is not reproducible from the repository.
3. **Round-11 adjudication:** `KNOWLEDGE.md` explicitly records the final round as single-family because the Codex quota was exhausted, and calls independent cross-family adjudication an outstanding TODO.
4. **Exact node completeness remains prose:** the FFS checker validates every annotation that exists, but it deliberately does not machine-check the claim that all 96 in-scope nodes are covered.

Items 1–2 are the most important. Items 3–4 are trust hardening rather than evidence of a mathematical defect.

---

## 2. Audit question

The adversarial question is not:

> Does Lean accept the files?

It is:

> Could this branch be green while still materially overstating what it formalizes?

The attack surface includes:

- a correct proof of the wrong statement;
- a hypothesis that silently assumes the hard part;
- a vacuous theorem whose hypotheses cannot be realized;
- a non-vacuity witness that is technically inhabited but cannot discriminate the intended property;
- a type or representation substitution that changes the source mathematics;
- a paper-order / Mathlib-order inversion;
- a hidden finite-carrier assumption leaking into a claimed finite-dimensional theorem;
- a conjecture being laundered into an axiom, hypothesis, or misleading "completed" result;
- a paper node being counted in prose without a corresponding audited declaration;
- a convenience/API layer hiding a modeling boundary;
- a downstream test that merely restates the theorem rather than demonstrating a usable interface;
- an audit whose verdict cannot be reproduced from committed evidence.

This review treats the **statement surface**, **witness surface**, **accounting surface**, and **consumer surface** as separate objects.

---

## 3. Evidence examined

The review was grounded in the live `finite-factored-sets` branch at the head above, especially:

- `FiniteFactoredSets/README.md`
- `FiniteFactoredSets.lean`
- `FiniteFactoredSets/KNOWLEDGE.md`
- `FiniteFactoredSets/notes/paper-errata.md`
- `FiniteFactoredSets/notes/2109.11513-main.tex`
- `FiniteFactoredSets/Basic.lean`
- `FiniteFactoredSets/History.lean`
- `FiniteFactoredSets/Orthogonality.lean`
- `FiniteFactoredSets/Subpartition.lean`
- `FiniteFactoredSets/SubpartitionHistory.lean`
- `FiniteFactoredSets/ConditionalOrthogonality.lean`
- `FiniteFactoredSets/Polynomial.lean`
- `FiniteFactoredSets/Factoring.lean`
- `FiniteFactoredSets/CharacteristicOrthogonality.lean`
- `FiniteFactoredSets/Probability.lean`
- `FiniteFactoredSets/Inference.lean`
- `FiniteFactoredSets/InferenceExamples.lean`
- `FiniteFactoredSets/Conjecture.lean`
- `FiniteFactoredSets/EmbeddedAgency.lean`
- `FiniteFactoredSets/Examples.lean`
- `FiniteFactoredSets/InfiniteExamples.lean`
- `FiniteFactoredSets/API.lean`
- `APITests/FiniteFactoredSets.lean`
- `AxiomAudit.lean`
- `scripts/check-finite-factored-sets-nodes.py`
- `scripts/papers.py`
- root `README.md`
- root `CLAUDE.md`
- `.github/workflows/ci.yml`

The audited head's GitHub Actions run `32028515874` completed successfully.

This review does **not** substitute for a line-by-line human proof review. FAF's own trust model correctly does not require that: Lean checks proof bodies. The human-critical layer is the statement and definition surface.

---

## 4. Scope audit

### 4.1 Claimed scope

The branch claims **96 of the paper's 98 numbered nodes** as in scope.

In scope:

- §1–§6 in full;
- §7 Definitions 46–50;
- Conjecture 1 **as a statement only**, deliberately unproved.

Out of scope by explicit ruling:

- Example 3;
- Example 4.

The branch accounts for the 96 in-scope nodes as:

- **87** nodes carried by declarations in this project;
- **9** nodes rendered directly by Mathlib vocabulary:
  - Definitions 1, 2, 5, 6, 7, 9, 29, 30, 39.

Some paper nodes have multiple Lean carriers, yielding **94 paper-node annotations** for the 87 declaration-carried nodes.

### 4.2 Adversarial assessment

**PASS, with an accounting caveat.**

The exclusions are not being used to dodge a theorem that the finite development needs. Examples 3 and 4 are explicitly the infinite-factored-set cases in the paper's future-work discussion, and the repository goes further than a bare exclusion by constructing the relevant infinite objects in `InfiniteExamples.lean` to probe the finiteness boundary.

Conjecture 1 is also not silently dropped. It is represented in `Conjecture.lean` as:

```lean
def FundamentalTheoremFiniteDim : Prop := ...
```

and is explicitly described as unproved. No declaration is claimed to prove that `Prop`.

The important residual weakness is mechanical: `scripts/check-finite-factored-sets-nodes.py` states in its own module documentation that it **does not enforce the converse node direction**. It checks the validity and inventory status of annotations that exist; it does not establish that every in-scope source node has an annotation or approved Mathlib-rendered disposition.

Thus the headline `87 + 9 = 96` is currently a human-maintained theorem about the repository, not a CI theorem.

### 4.3 Recommended hardening

Add an explicit scope manifest or exact-set check:

1. derive the 98 numbered source nodes from the committed TeX;
2. subtract the two ruled-out examples;
3. subtract the nine explicitly Mathlib-rendered nodes;
4. compare the remaining set for equality with the distinct annotated paper-node set.

That would turn the most important completeness sentence in the README into a failing CI invariant.

---

## 5. Statement-faithfulness audit

### 5.1 Partition representation (`dd:partition`)

The paper's partitions are represented as `Setoid S`.

**Assessment: PASS.**

This is a presentation change, not a substantive change, provided the formalization consistently treats setoid classes as the paper's nonempty blocks. The branch does so, and the choice is disclosed in the root FFS glossary and trust-surface documentation.

The empty-carrier corner is handled rather than ignored: the indiscrete and discrete setoids coincide extensionally on an empty type, matching the paper's special-case block behavior.

### 5.2 Order reversal (`dd:order-flip`)

The paper writes the finer relation in the opposite glyph direction from Mathlib's `Setoid` order; the paper's join/common-refinement notation corresponds to Mathlib meet / `sInf`.

**Assessment: PASS, high human-audit priority.**

This is the single easiest place to produce a completely type-correct but semantically reversed theorem. The branch treats it as such:

- the decision is globally disclosed;
- `commonRefinement_pair` now explicitly bridges the paper's binary common refinement to `X ⊓ Y`;
- the witness suite contains many reversed-reading counterexamples;
- API documentation repeatedly states the inversion.

I do not see evidence of a surviving systematic direction error. This remains one of the top items for the required human statement read-through because no amount of type checking can tell the reader which convention was intended.

### 5.3 Subpartition representation (`dd:subpartition`)

Subpartitions are represented as partial equivalence relations on `S`, rather than as a dependent pair `Σ E, Setoid E`.

**Assessment: PASS, with a correctly disclosed design boundary.**

Round 11 usefully corrected an earlier *justification* for this choice: Mathlib does have a partition-on-a-subset API. The real reason for the custom unindexed PER carrier is that the paper treats supports as data that may vary while still comparing/intersecting subpartitions, and a support-indexed type would turn ordinary domain equalities into transports.

This is exactly the kind of modeling correction that improves trust: the representation did not need to change, but the reason given for it did.

The paper itself has a genuine defect at Definition 22; the Lean's typed restriction operation appears to repair rather than conceal it. That repair is recorded in `notes/paper-errata.md` as E8.

### 5.4 Polynomial representation (`dd:poly`)

`Poly S := MvPolynomial (Set S) ℝ`.

**Assessment: PASS.**

Blocks are literally variables under the setoid presentation, making the representation direct. The branch is appropriately explicit about where Mathlib's `Irreducible` is stronger than the paper's informal irreducibility phrase and why Proposition 31 lives in the region where the two notions agree.

A former structural risk — parallel private exponent-vector implementations — appears to have been consolidated: current `Polynomial.lean` presents one `monoExp`-based monomial layer and describes it as the implementation detail underlying the public paper vocabulary.

### 5.5 Probability representation (`dd:probability`)

`ProbDist S` is an elementary finitely additive function on the full powerset, matching Definition 36 rather than silently replacing it with Mathlib measure theory.

**Assessment: PASS for the finite paper theorem; IMPORTANT boundary for Conjecture 1.**

This is one of the most important statement choices in the development. For finite `S`, the representation is faithful to the paper's clauses. For infinite `S`, it becomes one possible extrapolation of those finite clauses and is not a canonical reading of the paper's one-sentence conjecture.

The branch now says this explicitly. That disclosure is essential: without it, `FundamentalTheoremFiniteDim` would look like a literal formalization of an unambiguous infinite-carrier conjecture when it is actually a sharpening.

### 5.6 Model representation (`dd:model`)

`Model Ω` bundles a finite carrier, a factored set, and a map into the sample space.

**Assessment: PASS, with a disclosed universe narrowing.**

Putting finiteness in the model object is faithful to Definition 38 and is especially important because later database definitions quantify over models. The branch also discloses a Lean-universe narrowing in what model carriers are quantified over. Since carriers are finite, this is plausibly content-neutral, but it is correctly not hidden.

---

## 6. Finiteness audit

Finiteness assumptions are a central attack surface because this paper explicitly discusses relaxing finite size to finite dimension.

### 6.1 §3–§4

The branch aims to require finite **basis** where history minimality needs it, not finite **carrier**.

**Assessment: PASS, unusually well tested.**

`InfiniteExamples.natBoolFS` constructs a finite-dimensional factored set on an infinite carrier and applies the §3–§4 machinery. This is much stronger evidence than merely observing that theorem signatures lack `[Finite S]`.

The branch also constructs an infinite-dimensional coordinate factored set and uses it to show that some finite-basis assumptions are genuinely load-bearing.

### 6.2 §5 polynomial junk values

For infinite indexing sets, Mathlib's `finsum` / `finprod` conventions can collapse expressions to junk values (`0` or `1`) rather than the intended elementary infinite sum/product.

**Assessment: PASS as a disclosed boundary.**

The development does not pretend that the characteristic-polynomial theory extends unchanged. The infinite examples are used to refute inappropriate binder relaxation.

This is good adversarial practice: a hypothesis is justified by a compiled failure mode, not by author intention.

### 6.3 `isDistribution_diracAt`

A point mass is a distribution on every finite-dimensional factored set but not on an infinite-dimensional one under the `finprod` encoding.

**Assessment: PASS.**

The infinite-dimensional counterexample pins `[Finite F.B]` as a real semantic requirement rather than a proof artifact.

---

## 7. Non-vacuity and discrimination audit

FAF's strongest methodological requirement is that the interesting objects and antecedents be constructed.

### 7.1 Factored sets and histories

The branch constructs multiple nontrivial finite factored sets and evaluates histories, orthogonality, temporal relations, restrictions, and conditional orthogonality.

**Assessment: PASS.**

The examples are not all degenerate one-factor witnesses. `coordFS` supplies the two-factor setting needed to make conditioning and entanglement nontrivial.

### 7.2 Conditional orthogonality

A major potential failure would be to "test" Theorem 2 only in degenerate configurations where every clause collapses.

**Assessment: PASS after round-11 hardening.**

The knowledge base records that the final audit specifically repaired weak semigraphoid witnesses, including non-degenerate contraction/composition uses.

The existing witness design also contains reversed-form counterexamples for several orientation-sensitive claims.

### 7.3 Fundamental theorem / probability distributions

The most serious non-vacuity trap was point masses.

A Dirac distribution satisfies the division-free conditional-independence identity for arbitrary sets, so a library whose only infinite-carrier distributions were point masses could appear to exercise the right-hand side while discriminating nothing.

**Assessment: PASS after repair.**

Round 11 added a spread-out distribution `rich` on `natBoolFS`, plus a proof that it is an `IsDistribution` and a case where it **fails** the relevant independence identity. This establishes that the quantified family is not only inhabited; it can distinguish a non-orthogonal configuration.

This is exactly the correct adversarial standard:

> inhabited is not discriminating.

### 7.4 §6 orthogonality databases

`Consistent`, `Complete`, and inferred strict temporal order are particularly vulnerable to vacuity because the universal quantification is over models.

**Assessment: PASS.**

The development explicitly probes:

- a one-point model making an all-positive orthogonality database cheap;
- a negative database assertion forcing nonconstancy;
- inconsistent databases making universal inferred order vacuous;
- an empty-carrier model showing that a consistent empty-negative database need not infer strict order.

This makes the semantics legible instead of allowing the model quantifier to hide vacuity.

### 7.5 §7 embedded-agency definitions

The paper states definitions rather than theorems here, so the trust question is whether the definitions have been rendered faithfully and whether the examples exercise both clauses/nontrivial directions.

**Assessment: PASS after round-11 hardening.**

Round 11 found that earlier positive observation witnesses made the second observation clause automatic and that an `ObservesPartition` family could be constant. The branch repaired both issues with clause-2-nontrivial and non-constant-family witnesses.

Negative witnesses now distinguish failure of the two `Observes` clauses and show that the new relations are neither empty nor total except at documented degenerate corners.

---

## 8. Conjecture 1 audit

### 8.1 Is the conjecture being assumed?

**PASS.**

`FundamentalTheoremFiniteDim` is a definition of a proposition. It is not an axiom and no theorem claims it.

The finite case is not duplicated as a fake "conjecture theorem"; it is identified with Theorem 3.

The only intended uses of the conjecture object are hypothesis-form examples demonstrating what the statement would imply outside Theorem 3's finite-carrier scope.

### 8.2 Is the statement literally forced by the paper?

**NO — and the branch now says so.**

The paper defines `ProbDist` only in the finite context. Extending the same finite-additivity-on-the-powerset structure to arbitrary infinite carriers is one sharpening of the informal finite-dimensional conjecture, not a uniquely determined interpretation.

This is not a defect if prominently disclosed. It would be a defect if the README said "the paper's Conjecture 1 is exactly formalized" without qualification.

Current disclosure is adequate.

### 8.3 Literature-status claim

The branch distinguishes the bare conjecture from Mayer's measurable refinement and does not claim that the Lean `Prop` has been resolved.

**Assessment: PASS as documentation, not part of the kernel trust surface.**

---

## 9. Proof-offloading / circularity audit

The key question is whether cross-check witnesses or helper theorems secretly invoke the endpoint they are supposed to validate.

The knowledge base records several rounds that caught exactly this failure mode, including a Lemma 2 witness that originally "cross-checked" the theorem by applying it.

**Current assessment: PASS with tooling limitation.**

The development has adopted the right discipline:

- applied witness and independent cross-check are distinct;
- a cross-check must not mention the endpoint it checks;
- declaration order / textual inspection is used where proof-term introspection is unavailable.

However, Lean 4.31's imported-theorem representation makes the attempted generic dependency-graph approach unreliable: imported theorem bodies are not available through the naive `ConstantInfo.value?` route. This means independence claims are partly a source-audit property rather than a CI-enforced semantic property.

That is acceptable, but it should remain explicitly documented.

---

## 10. Provenance and axiom audit

### 10.1 Paper-node annotation validity

**PASS.**

The FFS checker derives printed numbering from the committed TeX's independent theorem counters, validates cited kind/number pairs, requires annotations to be anchored to named declaration docstrings, and requires each annotated declaration itself to appear in the FFS inventory.

### 10.2 Axiom cleanliness

**PASS at the audited head.**

The live CI build containing `AxiomAudit` succeeds. The README reports zero `sorry` and zero project axioms beyond Lean's standard trusted constants used by Mathlib-style developments (`propext`, `Classical.choice`, `Quot.sound`).

### 10.3 Exact completeness

**OPEN — low mathematical risk, medium trust-accounting risk.**

The checker itself documents that paper-node coverage is not checked in the converse direction. This is the most obvious remaining machine-checkable improvement.

---

## 11. Consumer-surface audit

### 11.1 API shape

The supported downstream import is:

```lean
import FiniteFactoredSets.API
```

**Assessment: PASS.**

`API.lean` is not merely a wildcard import. It documents:

- the core vocabulary;
- the order inversion;
- the main paper endpoints;
- bridge and rewriting lemmas;
- namespace traps;
- the finiteness surface;
- the boundary around Conjecture 1.

It also deliberately does not make `Examples.lean` part of the consumer dependency surface.

### 11.2 Client-style tests

`APITests/FiniteFactoredSets.lean` imports only `FiniteFactoredSets.API`, constructs its own factored sets, and proves composed downstream facts.

**Assessment: PASS.**

This satisfies the root repository's explicit "consumer readiness is part of paper completion" requirement much better than a collection of `#check`s or theorem restatements would.

The API tests demonstrate rewriting, transport, composition, construction, and nontrivial conditional-orthogonality use.

---

## 12. Paper errata audit

`FiniteFactoredSets/notes/paper-errata.md` currently records **E1–E14**.

**Assessment: PASS; this strengthens rather than weakens the trust surface.**

The important distinction is maintained:

- paper defects are recorded as defects in the source;
- the Lean statements are not silently changed without explanation;
- no recorded erratum is being used to excuse a missing Lean theorem.

Several errata are exactly the kind formalization should surface: wrong variables, wrong union/intersection symbols, missing evaluation notation, an incomplete proof step, and a definition whose typing does not support the later uses made of it.

A publication-facing reader should be directed to the errata before comparing Lean statements against printed proof prose.

---

## 13. Open findings

### FFS-AUDIT-01 — Required human read-through is not durably evidenced

**Severity:** HIGH for repository closeout; no evidence of a mathematical defect  
**Status:** OPEN unless completed elsewhere and merely unrecorded

Root `CLAUDE.md` states:

> Anson reads every top-level statement and every definition before the work is called done.

It further specifies the order:

1. results green;
2. consolidation / API / de-slop;
3. read-through over the frozen surface;
4. final fresh-context adversarial audit.

I found the final audit and the completed registry state, but not a durable FFS artifact recording the human read-through.

This matters more for FFS than for some libraries because the trust-surface generator renders plain `def` cards as signatures rather than bodies. `KNOWLEDGE.md` explicitly warns that a guide-only read-through cannot validate several FFS definitions.

**Recommended action:** perform and commit a short artifact such as:

`FiniteFactoredSets/notes/statement-readthrough-2026-08-17.md`

It need not re-prove anything. It should record, declaration by declaration or module by module, that the source-paper statement/definition and Lean surface were compared, with any notes or corrections.

---

### FFS-AUDIT-02 — Round-11 raw audit evidence is not committed

**Severity:** MEDIUM  
**Status:** OPEN

`FiniteFactoredSets/KNOWLEDGE.md` says:

- final findings are in `.harness/audit/final-findings-ids.json`;
- cross-family adjudication prompts are in `.harness/audit/final-codex-*.txt`.

At the audited branch head, `.harness` is not present in the repository.

Therefore a future auditor can read the **summary of the audit** but cannot reproduce which raw findings were emitted, how they were adjudicated, or what exact prompts remain to run.

This is not a defect in the Lean mathematics. It is a defect in audit provenance.

**Recommended action:** preserve the durable parts of the audit under the paper tree, e.g.

- `FiniteFactoredSets/notes/audit/round-11-findings.json`
- `FiniteFactoredSets/notes/audit/round-11-adjudication-prompts.md`
- `FiniteFactoredSets/notes/audit/round-11-resolution.md`

Do not rely on an ephemeral harness directory for a publication trust claim.

---

### FFS-AUDIT-03 — Final round lacks the branch's normal cross-family adjudication

**Severity:** MEDIUM-LOW  
**Status:** OPEN by the branch's own accounting

`KNOWLEDGE.md` explicitly says round 11 used ten Opus lenses but no independent Codex-family adjudication because quota was exhausted, and calls that an outstanding TODO.

The round was still a genuine fresh-context adversarial audit, so this does not invalidate it. But the branch should not describe round 11 as having the same methodological status as earlier dual-family rounds until adjudication occurs.

**Recommended action:** run the parked adjudication prompts from a fresh model family, resolve disagreements, and commit the resulting disposition.

---

### FFS-AUDIT-04 — The 96-node completeness claim is not a CI invariant

**Severity:** MEDIUM-LOW  
**Status:** OPEN

The checker validates annotations but deliberately does not verify exact source-node coverage.

A future edit could accidentally remove the only carrier of a paper node while leaving:

- all remaining annotations valid;
- the Python node checker green;
- `AxiomAudit` green for the remaining names;
- README prose stale.

Trust-surface freshness makes this harder, but does not prove set equality.

**Recommended action:** add an exact scoped-node set comparison.

---

### FFS-AUDIT-05 — Anonymous `example`s carry some accounting weight without inventory support

**Severity:** LOW  
**Status:** OPEN / documentation hardening

`KNOWLEDGE.md` itself notes that several anonymous `example`s perform real regression/accounting work but cannot be annotated or inventoried.

The most concrete case in the README is `OrthogonalSub`: it is described as exercised but not evaluated, and the distinction is disclosed. That is honest.

The residual risk is prose drift: anonymous checks are easy to delete or weaken without an inventory name disappearing.

**Recommended action:** where an anonymous example is cited in a public trust claim, either:

- promote it to a named clean regression lemma and inventory it; or
- keep the README wording deliberately modest ("typechecks/unfolds", not "validated/computed").

---

## 14. Human read-through priority list

The human pass should not spend equal time everywhere. Highest-risk declarations are the ones where a small syntactic change would preserve type correctness while altering the mathematical claim.

### Tier A — read against the paper extremely carefully

- `IsTrivialPartition`
- `IsFactorization`
- `FactoredSet`
- `commonRefinement`
- `chimera` / `chimeraImage`
- `Generates`
- `history`
- `Orthogonal`
- `Before` / `StrictlyBefore`
- `Subpartition`
- `Subpartition.restrict`
- `GeneratesSub`
- `historySub`
- `OrthogonalGivenSet`
- `OrthogonalGiven`
- `Poly`
- `Q`
- `mono` / `monos` / `poly`
- `FactoredSet.irr`
- `ProbDist`
- `FactoredSet.IsDistribution`
- `Model`
- `OrthDatabase`
- `OrthDatabase.Models`
- `OrthDatabase.Consistent`
- `OrthDatabase.Complete`
- `OrthDatabase.StrictlyBefore`
- `FundamentalTheoremFiniteDim`
- `Observes`
- `ObservesPartition`
- `Counterfactable`
- `CounterfactableRel`
- `BeforeGivenSet`

### Tier B — read theorem orientation / hypotheses carefully

Especially:

- Propositions 10–13 (generation/history);
- Propositions 14–19 (orthogonality/time);
- Propositions 20–25 and Lemmas 1–2 (§4);
- Proposition 28 (`factor2`);
- Propositions 29–31 (irreducible factorization);
- Lemma 3;
- Proposition 32;
- Theorem 3;
- Propositions 33–36.

### Specific questions for the human pass

For every statement:

- Does every binder occur in the paper, or is an extra one genuinely a strengthening/generalization?
- Is a finiteness hypothesis on `S` versus `F.B` in the right place?
- Is the Mathlib order reversed relative to the paper glyph exactly where expected?
- Is `⊓` being read as the paper's common refinement, not common coarsening?
- Does a `Subpartition` statement preserve the paper's domain side condition?
- Do `NotOrth` database entries mean positive negative-information assertions, not logical negation of membership in `Orth`?
- Is a theorem about all models protected by a consistency/non-vacuity fact where its interpretation requires one?
- Is any §7 statement being presented as a theorem when the paper only defines a notion?
- Does Conjecture 1 remain explicitly a sharpening of an informal infinite-carrier statement?

---

## 15. Recommended closeout sequence

I would not commission another broad proof-generation pass. The remaining work is verification of a frozen artifact.

### 1. Human statement/definition read-through

Create a durable note recording the pass and any corrections.

### 2. Reproduce and preserve the final adversarial audit

Move the durable round-11 evidence out of ephemeral `.harness` state and into the repository.

### 3. Run the missing cross-family adjudication

Resolve any disagreements in a committed audit disposition.

### 4. Add exact node-set coverage

Make `96/98` machine-enforced under the two-node scope ruling.

### 5. Re-run the full release gate at one SHA

At minimum:

```sh
python3 scripts/lint_paper_labels.py
./scripts/check-paper-nodes.sh
python3 scripts/check-cartesian-frames-nodes.py
python3 scripts/check-modal-agents-nodes.py
python3 scripts/check-finite-factored-sets-nodes.py
python3 scripts/check_trust_surface.py
python3 scripts/check_paper_wiring.py
lake build AxiomAudit
lake build APITests
```

Regenerate `docs/trust-surface.html` if any audited input changes.

The release record should name the final SHA so the read-through, adversarial audit, and green build all refer to the same frozen statement surface.

---

## 16. Final disposition

### Mathematical/formal disposition

**PASS.**

I found no surviving theorem-level issue that makes the branch materially incomplete for its explicit scope. The hard parts are not obviously off-loaded:

- history minimality is proved under a genuinely tested finite-basis condition;
- conditional orthogonality is constructed rather than postulated;
- the polynomial factorization stack reaches the fundamental theorem;
- the probability side contains discriminating, not merely inhabited, distributions;
- the §6 examples construct models and expose vacuity corners;
- infinite examples test where the finite theory does and does not extend;
- Conjecture 1 is neither proved nor assumed;
- §7's definitions have informative positive and negative witnesses;
- the API is downstream-usable.

### Trust / process disposition

**CONDITIONAL PASS.**

The remaining issues are almost entirely about making the trust claim itself durable:

- record the mandated human read-through;
- preserve the raw final-audit evidence;
- finish the explicitly pending independent adjudication;
- machine-check exact scope completeness.

Once those are closed at a single green SHA, I would regard the FFS formalization as complete to FAF's intended standard and suitable to merge as a finished paper formalization.

---

## Appendix A — Finding summary

| ID | Area | Severity | Verdict | Required action |
|---|---|---:|---|---|
| FFS-AUDIT-01 | Human statement/definition read-through | High (closeout) | Open unless done elsewhere | Perform and record frozen-surface read-through |
| FFS-AUDIT-02 | Audit evidence preservation | Medium | Open | Commit round-11 findings/prompts/disposition |
| FFS-AUDIT-03 | Independent audit adjudication | Medium-low | Open | Run fresh cross-family adjudication |
| FFS-AUDIT-04 | Exact 96-node coverage | Medium-low | Open | Add exact-set CI check |
| FFS-AUDIT-05 | Anonymous regression examples | Low | Harden | Name/inventory trust-relevant checks or keep claims modest |
| — | Ruled paper scope | — | Pass | None |
| — | `sorry` / axiom cleanliness | — | Pass at audited SHA | Keep CI green |
| — | Modeling disclosures | — | Pass | Preserve |
| — | Order inversion | — | Pass, human-sensitive | Include in read-through |
| — | Finiteness boundaries | — | Pass | Preserve infinite counterexamples |
| — | Non-vacuity / discriminating witnesses | — | Pass | Preserve |
| — | Conjecture 1 handling | — | Pass | Preserve sharpening disclosure |
| — | Consumer API and downstream tests | — | Pass | Preserve API boundary |
| — | Paper errata accounting | — | Pass | Preserve and cite |

---

## Appendix B — What should *not* trigger another research pass

The following are already settled or explicitly ruled and should not be reopened merely because they look unusual:

- partitions as `Setoid`;
- the paper/Mathlib order-glyph reversal;
- partial-equivalence-relation subpartitions;
- `MvPolynomial (Set S) ℝ`;
- elementary finite-additive `ProbDist` for the finite theorem;
- `Model` carrying finiteness internally;
- Conjecture 1 being a `def : Prop` with no proof;
- Examples 3 and 4 being outside the ruled formalization scope;
- §7.3 containing definitions but no paper theorems;
- inconsistent databases making universal inferred order vacuous;
- the empty-carrier corners explicitly recorded in the witness suite.

A new pass should be commissioned only if the human read-through or independent adjudication identifies a concrete statement mismatch, missing node, hidden assumption, or misleading public claim.
