# Errata audit — faithfulness of the LI formalization (fresh pass, 2026-07-24)

Fresh-context statement-level audit of `LogicalInduction/` against Garrabrant et al.,
*Logical Induction* (arXiv:1609.03543v5, tex in `notes/`). Method: read the code, not the
documentation — every core framework definition was read in full; construction endpoints
and a broad sample of property-tail theorem statements were read against the paper's
statements; selected proof bodies (`buyDaily_exploits_freq`, `trading_firm_dominance`,
`marketMaker_not_exploited`, `lic_nonDogmatism`, the Criterion serialization layer) were
read end to end. The previous audit file was deleted before starting; nothing below is
carried over from it.

Mechanical state at audit time: build artifacts fresh (same day as HEAD `f060abb`);
**zero `sorry` in `LogicalInduction/`** (the single grep hit, `Properties/Coherence.lean:143`,
is the word inside a docstring); **zero `axiom` declarations**; no `native_decide`,
`unsafe`, `partial def`, or `@[implemented_by]` anywhere in the library.
`AxiomAudit.lean` is a checked build target asserting every listed endpoint clean of
everything beyond `propext`/`Classical.choice`/`Quot.sound`, and freezing the field sets
of every boundary structure. `scripts/check_endpoint_coverage.py` passes:
67 paper labels covered, 0 uncovered.

---

## 1. Verified faithful (read line-by-line against the paper)

* **`def:tf` / `def:tradestrat` / `def:trader`** (`Framework/Criterion.lean`). `EF` is
  the paper's feature language on the nose: price features `φ*ⁿ`, rational constants,
  `+`, `×`, `max`, safe reciprocation `max(1,·)⁻¹` (plus `letE`/`var` sharing, a
  conservative addition — its denotation is definable without it). `Strategy.value`
  is exactly `∑ eᵢ(𝓥)·(W(φᵢ) − 𝓥ₙ(φᵢ))`, i.e. the paper's affine trade with the cash
  term determined by the pairs. Rank discipline `rank ≤ n` matches the paper's
  visibility constraint (day-`n` strategy may read prices through day `n`; the 0-based
  day indexing is disclosed at `Foundations.lean:50`).
* **`def:exploitation` / `def:lic`** (`Criterion.lean:1395–1514`).
  `plausibleAssessments = {netWorth V v n : v ⊨ D n}`, `Exploits = BddBelow ∧ ¬BddAbove`
  — the paper's Definition verbatim, including the edge behavior on empty world sets.
  `IsLogicalInductor` bundles exactly the paper's three ingredients: computable rational
  market, computable deductive process, no e.c. trader exploits.
* **`def:world` + p.c.** `PCWorld` = Boolean atom valuation read through Foundation's
  classical semantics = "determined by Boolean algebra from prime sentences". The paper
  itself uses only *propositionally* consistent worlds, so this is not a weakening.
* **`dd:asymp`** (`Framework/Asymptotics.lean`): `≈ₙ`, `≲ₙ`, `≳ₙ` match the paper's §2
  notation exactly (checked against the ε-characterizations).
* **`def:luv` / `def:e`** (`Framework/Expectations.lean:89–94`):
  `expect P n X = n⁻¹ ∑_{i<n} Pₙ(⌜X > i/n⌝)` — the paper's Riemann-sum expectation with
  precision tied to the day.
* **`def:condp`** (`Properties/Conditioning.lean:17–22`): capped conditional quote
  `min(1, P(φ∧ψ)/P(ψ))`, 1 on zero denominator — the paper's definition.
* **The construction spine** (M6/M7). `fixed_point_lemma` (Brouwer on the aggregate
  share demand — aggregation over repeated sentences is handled, a real trap avoided),
  `marketMaker_not_exploited` (geometric error budget `2^{-(n+1)}`, all plausible
  assessments `< 1`), `exists_budgetedTrader_exploits` (budget preservation),
  `trading_firm_dominance` (gate → budget → weight, exactly `lem:tfdom`'s shape),
  `TraderEnumeration` (total redundant enumeration of length/token program pairs with
  polynomial clocks — `prop:enumeration`), and `LIA.lean` closing the recursive
  fixed-point loop. Endpoints `LIA_is_logical_inductor` /
  `exists_computable_beliefSequence_logical_inductor` (`LIACompiler.lean:6738–6779`) are
  **unconditional over any computable deductive process**, with the finite-support,
  `[0,1]`, exact-rational belief-state clauses stated explicitly — this is `thm:lia` /
  `thm:li` including the computability half, not just the semantic half.
* **Brouwer** (`Construction/Brouwer.lean`): genuinely proved from scratch
  (Sperner over the Freudenthal/Kuhn triangulation, lifted to compact convex sets);
  Aristotle-autoformalized provenance disclosed in the header; axiom-checked.
* **Paper-faithful "late theorem" forms exist.** The `∀ n, φ ∈ D n` hypotheses on
  `lic_deducible_*` are stepping stones; the paper-facing `lic_provind`
  (`AffineCoherence.lean:921`) needs only `∀ n, ∃ k, φ n ∈ D k` — theorems may be proved
  arbitrarily later than their indices, which is the actual content of `thm:provind`
  ("outpacing deduction"). Likewise `lic_nonDogmatism` (`NonDogmatism.lean:950`) has no
  price-range or decaying-bound weakening (the `_weak` variant is superseded and labeled
  as such), `lic_preemptive_learning` and `lic_persistence_of_knowledge` match the
  paper's sup/inf-over-futures forms, and `lic_occamBounds` gives the paper's single
  constant `C` for both directions.
* **Uniform non-dogmatism's enumeration witness is discharged**:
  `EfficientRepeatedEnumeration.ofCE` (`M7Witnesses.lean`, in the audit surface) builds
  the required repeated enumeration from a bare c.e. enumeration, so `thm:obu` does not
  quietly demand more of the caller than the paper does.

## 2. Disclosed substitutions, verified real in the code (type-`(c)` ledger)

These are already flagged in-code; the audit confirms each disclosure matches what the
code actually does, and sharpens where each one bites.

### 2.1 `dd:fuel` — the poly-*value* token residual (the one that genuinely narrows scope)

`EfficientlyComputableTok` (`Criterion.lean:1495`) is the token-emission model: two
programs under one polynomial `evaln` clock emit the strategy's flat token stream. The
stream length is `Θ(EF.cost)` (both directions proved: `serialize_length_le_cost`,
`cost_le_serialize_length`), which correctly repairs the whole-number model's
exponential-value wall (the superseded `EfficientlyComputable` is honestly labeled at
`Criterion.lean:1429`). **But each individual token is still a clocked-program output,
hence `poly(n)`-value.** Tokens include `Encodable.encode φ` for traded sentences and
`Encodable.encode q` for rational constants. Consequences, confirmed by reading the
serializer:

* a trader whose day-`n` strategy trades a sentence whose *code value* grows
  super-polynomially (deep formulas: pairing-based `Encodable` codes are exponential in
  formula depth even at polynomial formula *size*) is not `EfficientlyComputableTok`,
  though it is e.c. in the paper's poly-*time* sense;
* likewise a per-day rational constant like `2^{-n}` as a *literal* (the in-repo traders
  avoid this by building such constants compositionally — e.g. the non-dogmatism ladder's
  poly-value band constants — which is why their `_ecTok` certificates go through).

Direction analysis (worth keeping straight in any writeup): the formal e.c. class is a
**subclass** of the paper's. So `IsLogicalInductor` is a *weaker* hypothesis than the
paper's LIC — every property theorem had to construct its exploiter *inside* the narrower
class (harder; done), while `LIA_is_logical_inductor` proves the market defeats *fewer*
traders than the paper's `thm:lia` claims. The same residual propagates into every
`PolySentenceCodes` / `PolyRatCodes` / `*_codes` hypothesis on sequence-form theorems:
they quantify over poly-*code-value* sequences, a proper subclass of the paper's
`𝓔𝓒`-sequences. Disclosed at `Criterion.lean:1467–1472` ("formula-level sub-tokenization
would remove even this"); still open.

### 2.2 Propositional substrate (`def:lang`)

`Sentence = LO.Propositional.Formula ℕ`. The criterion layer is unaffected (the paper's
worlds are propositionally consistent too), but everything in the paper that needs "Θ
represents computations" (§4.8–4.12) is rendered through presentation structures whose
atoms are code-indexed schema instances (`ComputationTheoryPresentation`,
`QuotationTheoryPresentation`), constructed for Σ₁-sound `T ⊇ 𝗜𝚺₁` in
`Witnesses/ComputationDP.lean`. The old vacuity failure is fixed and *certified*:
`quotation_presentation_nonvacuous` (`ComputationDP.lean:536`) proves the quotation
presentation and the `hworld` hypothesis jointly satisfiable, so the `_ofCode` /
`_ofRepresentation` endpoints are not vacuously true.

### 2.3 Quotation-conditioned endpoints (`thm:epr/er/cee/ceu/ccee/st/ref/lp`)

Introspection, self-trust, and the expectation reflection theorems take quotation
packages (`CurrentPriceExpectationQuote`, `SelfTrustQuote`, …) whose `reflected` /
`theory_coherent` fields assert the intended first-order semantics of the quoted
sentences. This is the project's declared conditional seam, and the field surfaces are
frozen by `#assert_fields`. Status by endpoint, checked against `AxiomAudit.lean`:
paradox resistance, expectations-of-probabilities, halting-pattern learning, wub/feedback,
conditioning, and DUS all have `_unconditional`-over-LIA instantiations;
**`lic_self_trust`, `lic_iterated_expectations`, and `lic_introspection` do not** —
their strongest forms remain `_ofRepresentation`/`_ofCode`, conditional on the quotation
package (satisfiable, per 2.2, but not yet instantiated over the constructed LIA).
This matches the "conditional+disclosed" endpoint definition; it is the honest residual
gap between the repo and the paper's §4.11–4.12 as unconditional theorems.

### 2.4 Remaining caller inputs on `thm:dus`

`lic_domination_universalSemimeasure_unconditional` (`UnconditionalOverLIA.lean:48`)
discharges the inductor, the deductive process (empty — legitimate, since bit-prefix
sentences are Boolean combinations of independent atoms, so all coherence constraints are
propositional), and `hworld`. Still caller-supplied: `DUSApproximationPresentation` +
`DUSThresholdEmission` (`M7-DUS-APPROX`) — poly-code emission of the semimeasure's
from-below approximation, i.e. the 2.1 residual again, applied to `M`'s approximants.
The paper needs only lower-semicomputability here.

### 2.5 `hworld` consistency hypotheses

Most property endpoints carry `hworld : ∀ n, ∃ v, v.ConsistentWith (DP.D n)`. The paper
states its §4 results for a deductive process over a consistent theory, so this is the
faithful propositional rendering (per-stage finite satisfiability ≡ `Θ ⊬ ⊥` by
compactness), not an added assumption — and it is *proved*, not assumed, for the
constructed processes (`theoremDP_hworld`, `emptyBitDeductiveProcess_hworld`).

## 3. Errata (things to fix or watch — none load-bearing)

1. **Leftover redundant price-range hypotheses.** Commit `c4f2392` ("remove redundant hP
   from all criterion endpoints") missed several: `lic_deducible_eventually_ge`
   (`ProvabilityInduction.lean:168`), `lic_deducible_tendsto_one` (`:184`),
   `lic_provind_seq` (`:237`), `lic_nonDogmatism_weak` (`NonDogmatism.lean:257`) still
   take `hP1`/`hP0` derivable from `IsLogicalInductor.price_mem_Icc`. Harmless
   (callers can always discharge them) but the commit message overstates, and the
   endpoints are on the audit surface — clean them or note them.
2. **Stepping-stone forms sit beside faithful forms on the same audit surface.**
   `AxiomAudit.lean` lists both `lic_deducible_tendsto_one` (needs `φ ∈ D n` for *all*
   `n`) and the faithful `lic_provind`; both `lic_nonDogmatism_weak` and
   `lic_nonDogmatism`. The docstrings label the weak ones correctly, but the flat
   endpoint list doesn't distinguish "paper statement" from "fragment kept for its
   pedagogical shape". A one-word tier tag in `AxiomAudit.lean` comments (already partly
   present) would prevent a reader from crediting the weak form as `thm:provind`.
3. **`lic_provind_seq`'s docstring oversells slightly.** It cites `thm:provind`
   ("sequence form") but its `hded : ∀ n, φ n ∈ DP.D n` makes it a *timely-membership*
   statement, not provability induction (the paper's point is precisely that `φ n` need
   not be in `D n`). The genuine sequence form is `lic_provind`. Suggest the docstring
   say so explicitly and point there.
4. **`letE`/`var` in `EF`** is an extension of the paper's feature grammar (sharing).
   Denotationally conservative and needed for poly-size deep features, but it changes
   `cost` relative to the paper's expression size; worth one disclosure line in the
   `EF` docstring (currently only the serialization comments discuss it).
5. **`ComputableMarket` totalizes quotes on non-sentence codes** (`Criterion.lean:990`,
   "extra values … are harmless"). Verified harmless: `quote_exact` pins every real
   sentence's price. No action; recording that it was checked.

## 4. What this audit did **not** cover in depth

Statement-level reading covered every file; proof-body reading was sampled. Not read line
by line: the interiors of `Framework/ROI.lean`, `Framework/Computable.lean` (beyond
`PolyFueled` and the emission layer), `Calibration.lean` / `Pseudorandomness.lean`
analytic interiors, `LIACompiler.lean:1–6690`, and the `QuotationAffine.lean` diagonal
fixed-point plumbing. These are kernel-checked and their *statements* were audited, but a
future pass hunting for off-loaded steps (rule: "hand-computation where a Mathlib lemma
should carry it") would start there. The deferred human read-through of the frozen
surface (`AxiomAudit.lean` is its table of contents) remains the final faithfulness gate.
