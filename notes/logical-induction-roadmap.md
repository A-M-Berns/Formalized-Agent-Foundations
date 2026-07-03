# Logical Induction — Lean 4 Formalization Roadmap

*Target: a full formalization of* Logical Induction *(Garrabrant et al., arXiv:1609.03543) in Lean 4 + Mathlib, with FormalizedFormalLogic/Foundation supplying the propositional substrate.*

This document supersedes the earlier `logical-induction-blueprint.tex` skeleton at the planning level (the `.tex` remains the rendered dependency graph). It folds in the structure of the actual paper (every node below carries the paper's real `\label`) and the lessons from auditing the trust-between-inductors deference corpus, which is the **first downstream consumer** of this formalization.

---

## 0. How to use this document

- The **node ledger (§3)** is the spec. Every theorem/definition has the paper's exact label, a proposed Lean name under the `LogicalInduction` namespace, and two discipline columns (*kind*, *provenance*) that exist to stop the project from accumulating dressed-up tautologies.
- The **milestone sequence (§4)** is deliberately *property-tail-first, construction-last*. Rationale in §4 and §6.
- The **standing rules + audit protocol (§5)** are non-negotiable; they are what makes "kernel-checked" mean something.
- The **session-1 kickoff prompt (§7)** is ready to paste into Claude Code.

---

## 1. What changed versus the previous blueprint

Three substantive updates, all from the deference-corpus audit:

1. **Sequencing is now downstream-driven.** The deference work takes a specific set of LI theorems as *named hypotheses*: `thm:loe`, `thm:ccee`, `thm:ceu`, `thm:expprovind`, `thm:ec`, `thm:con`, `thm:lc`, `thm:nd`, and the criterion `def:lic` itself. Formalizing exactly these first converts an existing body of Abram's work from "assumed" to "derived." So the first property slice (M3) is chosen by downstream demand, not paper order. (Naming caution: the deference shorthand "cee" = the paper's `thm:ceu` *No Expected Net Update*; the paper's `thm:cee` is the distinct *Expected Future Expectations*. Don't conflate them.)

2. **The e.c.-certification step is load-bearing in the property tail, not just the construction.** Every property proof in the paper has the shape *assume the property fails → build a trader that exploits the failure → invoke the criterion*. The criterion only forbids **efficiently computable** traders, so each such proof must certify that the trader it constructs is e.c. — i.e. it must use the EF DSL's `cost` semantics. The deference corpus never did this (it stubbed "criterion ⇒ inequality" with one-line arithmetic). That is precisely the gap this project exists to close, and it means the property tail is genuinely harder than the deference corpus's green-and-`sorry`-free status suggests. Do not import false comfort from that corpus: it dodged exactly the trader/e.c. machinery that is the real work here.

3. **Audit and ledger are structural, not post-hoc.** `#print axioms` certifies that a proof matches its stated proposition — *not* that the proposition is the one you meant. The trust surface is therefore the **definitions, the hypotheses, and the conclusion statements**, which a human must read. The ledger columns and the scheduled adversarial audit (§5) operationalize this from day one.

---

## 2. Design decisions (carried forward, with the EF rationale now confirmed from the paper)

These are settled. If one fights Lean's type system, **surface it in the session report** rather than working around it silently — they are load-bearing.

- **`dd:fuel` — Efficiency is a fuel-clocked interpreter, not a complexity class.** `def:ec` (paper §3.3) is "computable in time polynomial in `n` (unary)," and the paper is explicitly *not wedded* to poly-time (§7.3 / `sec:bounds`); the load-bearing requirement is computable enumerability *with a clock*. The construction enumerates `(machine, integer-polynomial)` pairs and clips execution. **Never formalize `P` as a complexity class.** The reason total computable traders can't simply be quantified over is that they are not computably enumerable — the clock is what restores enumerability.

- **`dd:dsl` — Expressible features are a reified DSL with two semantics.** The paper (`def:tf`) defines an expressible feature as an algebraic expression over price features `pf φ`, rationals, `+`, `×`, `max(·,·)`, and safe reciprocation `max(1,·)⁻¹`; the footnote states the three properties that actually matter: features must be **(1) continuous, (2) compactly specifiable in poly time, (3) expressive enough**. So:
  - `EF.denote : EF → (History → ℝ)` — the continuous real-valued semantics. Feeds Brouwer (continuity is what breaks the price/trade circularity, §3.5 of the paper).
  - `EF.cost : EF → ℕ` — a syntactic size/complexity measure. Certifies efficient computability, both in the construction *and in every property proof's exploiting trader*.
  - `EF_n` (rank ≤ `n`) is a **commutative ring** — instance required.

- **`dd:abstract` — Build the concrete clocked enumeration; abstraction over a trader class is optional.** The concrete `def:emulatabletraders` (Efficiently Emulatable Sequence of Traders) is directly formalizable and is what the construction needs.

- **`dd:asymp` (NEW) — One asymptotics module.** The deference corpus redefined `Approx`/`AsympLE` identically in four files. Factor the limit vocabulary (`≈ₙ`, `≳ₙ`, "eventually within ε", "converges to") into a single `LogicalInduction.Asymptotics` module, built on Mathlib's `Tendsto (· − ·) atTop (𝓝 0)` and `∀ ε>0, ∀ᶠ n in atTop, …`. The deference corpus is good evidence these lightweight idioms carry the whole analysis layer; no heavier filter machinery is needed. Settle the **finite-stage vs. limiting** convention here too, and state each property in whichever form the downstream consumer needs (the deference work consumes the limiting form).

---

## 3. Node ledger (the dependency graph)

Mirror each `\label` in a Lean comment so status maps back to the graph. **Kind** codes: `Def` · `P` proved · `C` composition (chains named facts via real work) · `S` squeeze-over-named (conclusion ≡ a hypothesis — flag and justify) · `T` trivial stub · `N±` non-vacuity witness (genuine/degenerate). **Provenance** codes for each hypothesis: `(a)` derived in-project · `(b)` Foundation/Mathlib citation · `(c)` modeling substitution (a weaker/different object stands in for the intended one — the dangerous kind). The goal is that nothing in the final corpus is `S`/`T` with a name that promises more, and that every `(c)` is either eliminated or explicitly disclosed.

### Part I — Foundations & Criterion (`LogicalInduction.Foundations`, `.Criterion`)

| Label | Proposed Lean name | Kind | Notes |
|---|---|---|---|
| `def:lang` | `Sentence` (thin wrapper over Foundation) | Def | Inspect Foundation's *actual* API for propositional sentences, `⊢`, propositional consistency — do not assume it. |
| `def:market` / `def:world` | `Valuation`, `World` | Def | A world = propositionally consistent `{0,1}` valuation; market = computable sequence of `[0,1]`-pricings. |
| `def:worlds` (deductive process) | `DeductiveProcess` | Def | `D n ⊆ D (n+1)`, each propositionally consistent, union = theorems. |
| `def:ec` | `EfficientlyComputable` (via `dd:fuel`) | Def | Clocked interpreter; **not** a complexity class. |
| **`def:tf`** | **`EF`, `EF.denote`, `EF.cost`, `instCommRing EF_n`** | **Def (keystone)** | The DSL. `denote` continuity is *stated* here (proof can defer). This node gates both Brouwer and every e.c. certification. Invest disproportionately; add non-vacuity examples. |
| `def:valfeature` | `ValuationFeature` | Def | The semantic target `EF.denote` lands in; rank = dependence horizon. |
| `def:tradestrat` | `TradingStrategy` | Def | Affine combo `cash + Σ ef_i · φ_i`; records cash + shares. |
| `def:trader` | `Trader` | Def | Sequence of `n`-strategies. |
| `def:exploitation` | `Exploits` | Def | Plausible-world values bounded below, `sup = +∞`. The heart of the criterion; get the quantifiers exactly right. |
| **`def:lic`** | **`IsLogicalInductor` (structure / class)** | **Def** | "No e.c. trader exploits the market." This is the hypothesis the entire property tail is conditioned on. |
| `thm:li` | `exists_logical_inductor` | C | Main result — *deferred to Part IV*; states existence of a computable inductor. |

### Part II — Shared engines (`LogicalInduction.Engine`)

| Label | Proposed Lean name | Kind | Notes |
|---|---|---|---|
| `def:roi` / `app:roi` | `ReturnOnInvestment`, `roi_bound` | P | The workhorse: bounds a trader's return; nearly every property proof routes through it. Build this before any property. |
| `def:tradermag` | `Trader.magnitude` | Def | Used by ROI and budgeting. |
| `def:emulatabletraders` | `EmulatableTraders` | Def | The concrete clocked enumeration shape (`dd:abstract`). |
| `thm:affpolymax` / `app:affpolymax` | `affine_preemptive_learning` | C | **Affine master theorem.** Most affine-family properties reduce to this. One of the two "lift" hubs. |
| `lem:conluvapprox`, `lem:mesh`, `lem:limexpapprox` | `LUV.*_approx` | P | **Expectation bridge.** The LUV approximation lemmas that lift probability results to expectation results. The second "lift" hub. |

### Part III — Property tail (`LogicalInduction.Properties.*`), all conditioned on `[IsLogicalInductor P]`

Grouped by paper subsection. **Bold = M3 downstream-priority slice** (discharges deference hypotheses).

| Family | Labels |
|---|---|
| Convergence / Coherence | **`thm:con`** (Convergence), **`thm:lc`** (Limit Coherence) |
| Timely learning | **`thm:provind`** (Provability Induction), `thm:perkno`, `thm:tbo` |
| Affine lifts (via `thm:affpolymax`) | `thm:affprovind`, `thm:affcoh`, `thm:peraffkno`, `thm:affpolymax`, `thm:recunbiasedaff`, `thm:wubaff`, `thm:prandaff` |
| Calibration / unbiasedness | `thm:simcal`, `thm:recurringunbiasedness`, `thm:wub` |
| Statistical patterns | `thm:benford`, `thm:prand` |
| Logical relationships | `thm:lex` |
| Non-Dogmatism / closure | **`thm:nd`**, `thm:ifp`, `thm:obu`, `thm:ob`, `thm:dus`, `thm:strict`, `thm:scon` |
| Expectations (LUV lifts, via the approx lemmas) | **`thm:ec`**, **`thm:loe`**, `thm:ei`, **`thm:expprovind`**, `thm:expcoh`, `thm:perexpkno`, `thm:exppolymax`, `thm:recurringunbiasednessexp`, `thm:wubexp`, `thm:prandexp` |
| Trust in consistency | `thm:pac`, `thm:pazfc`, `thm:incons` |
| Halting | `thm:halts`, `thm:loops`, `thm:dontwait` |
| Introspection | `thm:ref`, `thm:lp`, `thm:epr` |
| Self-Trust | `thm:er`, **`thm:cee`**, **`thm:ceu`**, **`thm:ccee`**, **`thm:st`** |

### Part IV — Construction / existence (`LogicalInduction.Construction`) — the hard core

| Label | Proposed Lean name | Kind | Notes |
|---|---|---|---|
| `lem:fpl` | `fixed_point_lemma` | P | **Brouwer.** The price-adjustment map `adj` on compact convex `Valuations'` is continuous *because trading strategies are continuous* (this is what `EF.denote` continuity buys). ~~Use Mathlib's Brouwer~~ — Mathlib has **no** Brouwer; `LogicalInduction.brouwer_fixed_point` is now proved from scratch (`Construction/Brouwer.lean`, Sperner route, Aristotle-autoformalized). Apply that to `adj`. |
| `def:markemaker` | `MarketMaker` | C | Rational approximation to the fixed point by bounded search. |
| `lem:budgeter` | `Budgeter`, `budgeter_props` | C | Caps each enumerated trader so the firm's total worth stays bounded below. |
| `def:tradingfirm` (`sec` 2533) | `TradingFirm` | C | Combines enumerated traders with budgets. |
| `def:lia` / `alg:li` | `LIA` | Def | The concrete algorithm. |
| `thm:lia` | `LIA_is_logical_inductor` | C | Discharges `def:lic` for `LIA` → unconditionalizes the entire property tail. |

---

## 4. Milestone sequence

The ordering is **criterion → property tail → construction**, the inverse of "build the inductor first." This front-loads the tractable, downstream-relevant, *conditional* results and treats the construction as the capstone that discharges the hypothesis. (See §6 for why this is the right risk posture.)

| M | Scope | Definition of done |
|---|---|---|
| **M0** | Project stands up. Lean 4 + Lake; Mathlib + Foundation co-building under one toolchain; namespace/file scaffold mirroring Parts I–IV; `Asymptotics` module (`dd:asymp`). | Green `lake build`; pinned versions in `PROGRESS.md`. If Mathlib + Foundation won't co-build, **stop and report the conflict** — don't hack around it. |
| **M1** | **The `def:tf` keystone** + the foundation interface (`def:lang`) and the criterion definitions (`def:market`, `def:world`, `def:tradestrat`, `def:trader`, `def:exploitation`, `def:lic`). `EF.denote`/`EF.cost`/`CommRing EF_n` built; `denote` continuity *stated* (`sorry` ok). | Everything elaborates; `def:lic` stated; ≥2 genuine `EF` examples as non-vacuity witnesses (the deference corpus's clean-definition discipline starts here). |
| **M2** | The shared engine: `def:roi`/`roi_bound`, `def:tradermag`, `def:emulatabletraders`. The "assume-fail-build-trader-invoke-criterion" pattern wired once, end-to-end, on the *easiest* real property, with the trader's e.c.-ness certified via `EF.cost`. | One property proven conditionally with a **genuinely constructed, genuinely e.c.-certified** exploiting trader — no arithmetic stub standing in for the exploit. This is the proof-of-concept that the hard step is real. |
| **M3** | **Downstream-priority slice.** `thm:con`, `thm:lc`, `thm:provind`; the LUV approx lemmas; `thm:ec`, `thm:loe`, `thm:expprovind`; Self-Trust `thm:cee`/`ceu`/`ccee`/`st`; `thm:nd`. | Each stated conditionally on `[IsLogicalInductor P]`, proved (not squeezed), ledgered with kind+provenance. **Integration test:** pick one deference theorem and discharge its named hypothesis from the corresponding result here; if the interface doesn't fit, fix the statement now. |
| **M4** | The two lift hubs made reusable: `thm:affpolymax` (affine master) and the LUV bridge, each as *one* shared lemma + mechanical members. | The affine and expectation families collapse to the hubs + thin per-member glue, not member-by-member re-proof. |
| **M5** | Remainder of the property tail: calibration/unbiasedness, statistical patterns, logical relationships, closure/Non-Dogmatism remainder, halting, introspection, consistency. | Full conditional property tail green; ledger complete; adversarial audit pass (§5) run and findings triaged. |
| **M6** | Construction, Part 1: `lem:fpl` (Brouwer) + `MarketMaker`. | Fixed point established via the in-project `brouwer_fixed_point` (Mathlib has none — proved from scratch at M0, see `Construction/Brouwer.lean`); `MarketMaker` properties proven. Expect this milestone to be where real time goes. |
| **M7** | Construction, Part 2: `Budgeter`, `TradingFirm`, `LIA`, `thm:lia`, `thm:li`. Discharge `def:lic` → unconditionalize the tail. | `LIA_is_logical_inductor` proven; main existence theorem `exists_logical_inductor` follows; every M3–M5 property now holds unconditionally. |

**Scope discipline:** do only the current milestone. Do not wander into the construction during the property tail, or into the affine/expectation members before the lift hubs (M4).

---

## 5. Standing rules and the audit protocol

**Verification (the load-bearing rule):**
- **Never invent a Mathlib/Foundation lemma, def, or instance name.** Before using one, confirm it exists in the installed source: `rg` the `.lake/packages` tree, or use `#check` / `exact?` / `apply?` / `loogle`. If something you need doesn't exist, do **not** fabricate it — leave `sorry` with `-- TODO(blueprint:LABEL): need <statement>` and move on.
- `lake build` stays **green at every stopping point**. `sorry` is allowed and expected; type/elaboration errors are not. Never leave the build broken. Small compiling commits over large broken ones.

**Ledger (`PROGRESS.md`):** maps `blueprint label → Lean decl → status (stmt / sorry / done) → kind → provenance`. The last two columns are the anti-self-deception mechanism; fill them honestly as you go, not retroactively.

**Scheduled adversarial audit:** at the end of M3, M5, and M7, run a *separate* statement-level audit pass (fresh context) over the milestone's top-level theorems, hunting specifically for:
- **vacuous** theorems (hypotheses unsatisfiable or jointly unrealizable);
- **conclusion-in-hypothesis** squeezes (a hypothesis already equals the conclusion — the deference `faithful_tracking`/`conditional_tower` pattern);
- **oversold stubs** (a substantive name over an arithmetically trivial body);
- **type-(c) substitutions** (a weaker object quantified over than the prose intends — e.g. an abstract sequence where a *legal* / e.c.-certified object was meant);
- **degenerate non-vacuity** (constant-sequence witnesses that make the asymptotic content trivially true);
- **off-loaded steps** (a hand-computation where a Mathlib lemma should carry it — e.g. an integral not going through `MeasureTheory.integral`).

For each property, the non-vacuity guard should ideally be **discharged by the construction** (M7) rather than by a stand-in witness — that is the principled reason the construction is in scope at all, not just an afterthought.

**Human read-through:** the kernel covers proof bodies; it does not cover statements. Anson reads every top-level *statement* and every *definition* before a milestone is marked done. This is tractable (the trust surface is small) and is the specific discipline the deference methodology skipped.

---

## 6. Where the assurance actually lives (risk posture)

The deference audit's one-line verdict on that corpus: *it proved the implications of the theory, not the antecedents — because the market and traders were unmodeled, "criterion ⇒ the forcing inequality" was nowhere in the Lean.* This project is the photo-negative of that: the antecedents — the trader constructions and the criterion applications — **are** the content. Two consequences for how to read progress:

1. **A green property tail conditioned on `[IsLogicalInductor P]` is real and valuable** (it is exactly what unconditionalizes once M7 lands, and it is what the deference corpus needs), **but only if the exploiting traders are genuinely constructed and e.c.-certified.** A property "proof" that takes the forcing inequality as a hypothesis has formalized nothing the deference corpus didn't already assume. M2 exists to prove the hard step is being done for real before the tail is built on top of it.

2. **The construction (M6–M7) is the genuine risk and the genuine assurance.** It is the part the deference corpus dodged, so its green status there tells you nothing about tractability here. Brouwer + the clocked enumeration + budgeting is plausibly multi-month. It is reasonable to ship M0–M5 (the full *conditional* theory) as a first public artifact and treat M6–M7 as a separate campaign — but be explicit, in any writeup, that until M7 the results are conditional on the existence of a logical inductor, which is assumed, not proved.

---

## 7. Session-1 kickoff prompt (paste into Claude Code)

```
We're starting a Lean 4 formalization of the paper *Logical Induction*
(Garrabrant et al., arXiv:1609.03543). Read logical-induction-roadmap.md first
— it is the spec. Every node has the paper's real \label (e.g. def:tf,
def:lic, thm:loe) and a proposed Lean name under the `LogicalInduction`
namespace; mirror those labels in comments so status maps back to the graph.

Stack: Lean 4 + Mathlib (analysis, Brouwer, measure theory) +
FormalizedFormalLogic/Foundation (propositional syntax, ⊢, consistency).

Standing rules for the whole project:
- NEVER invent a Mathlib/Foundation lemma, def, or instance name. Confirm it
  exists in the installed source first: rg the .lake/packages tree, or use
  #check / exact? / apply? / loogle. If it doesn't exist, leave `sorry` with
  `-- TODO(blueprint:LABEL): need <statement>` — do not fabricate.
- `lake build` must stay green at every stopping point. `sorry` is allowed and
  expected; elaboration errors are not. Small compiling commits over large
  broken ones.
- Keep PROGRESS.md mapping: label → Lean decl → status (stmt/sorry/done) →
  kind → provenance. The kind/provenance columns are mandatory, not optional.

Design decisions already made (don't relitigate silently; if one fights the
type system, SURFACE it in your report rather than working around it):
- Efficiency = a fuel-clocked interpreter, NOT a complexity class (dd:fuel).
  The trader enumeration runs M(n) for f(n) steps and clips.
- Expressible features are a reified DSL (dd:dsl) with two semantics:
  EF.denote (continuous ℝ-valued fn, feeds Brouwer) and EF.cost (syntactic
  size, certifies efficient computability). EF_n is a commutative ring.
- One Asymptotics module (dd:asymp): define ≈ₙ / ≳ₙ once, on Mathlib's
  Tendsto (·−·) atTop (𝓝 0) and ∀ᶠ n in atTop. Do not redefine per file.
- Build the concrete clocked enumeration; abstraction over a trader class is
  optional (dd:abstract).

This session is scoped to M0 plus the keystone node def:tf. Do NOT touch the
construction (Part IV) or the property tail (Part III).

Goals, in order:
1. Stand up the project: init Lean 4 + Lake, add Mathlib and Foundation, find a
   toolchain that builds BOTH. Green `lake build`; pin versions in PROGRESS.md.
   If they won't co-build, STOP and report the conflict — don't hack around it.
2. Scaffold the namespace/file layout mirroring the roadmap's Parts
   (Foundations, Criterion, Engine, Properties, Construction) under
   `LogicalInduction`. Statements with `sorry` bodies are fine, but everything
   must elaborate. Include the Asymptotics module.
3. Wire the Foundation interface (def:lang). Inspect Foundation's ACTUAL source
   for how it exposes propositional sentences, ⊢, and propositional
   consistency — don't assume the API. Wrap what you need behind a thin
   `LogicalInduction.Sentence` interface.
4. Build the keystone def:tf (expressible features): an inductive `EF` syntax
   (price features pf φ, ℚ, +, ×, max(·,·), safe reciprocation max(1,·)⁻¹);
   `EF.denote` into ℝ-valued functions of a valuation history; `EF.cost`
   (syntactic size); the CommRing instance on EF_n; and the STATEMENT of
   EF.denote continuity (proof may be `sorry`). Add ≥2 concrete EF examples as
   non-vacuity witnesses. If the two-semantics framing fights the type system,
   surface it — don't force it.

Definition of done: green `lake build`; items 3–4 elaborating (sorries
allowed); PROGRESS.md with the label→decl→status→kind→provenance columns. End
with a short report: what compiles, what's sorried, the pinned versions, and
the top 2–3 friction points or design questions that need Anson before the
next session.
```

---

*Node labels verified against the paper source (`main.tex`, 6368 lines, 53 `thm:` + 35 `def:` nodes). Sequencing and audit discipline derived from the statement-level audit of the trust-between-inductors deference corpus, which consumes `thm:loe`, `thm:ceu`, `thm:ccee`, `thm:expprovind`, `thm:ec`, `thm:con`, `thm:lc`, `thm:nd`, and `def:lic` as named hypotheses.*
