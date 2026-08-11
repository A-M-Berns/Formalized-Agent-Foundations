# Boundary 2, second pass — a first-order substrate: what it would cost, what it would buy

_Read-only scoping spike, 2026-08-11. Conducted against the installed toolchain (Lean
v4.31.0; Foundation pinned at `41d20b5158e9331e9b8dd86e16dbf488cc688bdb`; Mathlib arriving
transitively through Foundation). Every existence and non-existence claim below was checked
by `rg`/`grep` against the installed source at the cited file and line, and every count is
reproducible from the scans described in "How the counts were made". Companion to
`notes/boundary-propositional-substrate.md` (which this note **corrects on one load-bearing
point**) and `notes/boundary-efficiency-model.md` (the competing programme)._

---

## Summary of findings

1. **The migration target in the earlier note is the wrong one.** "Replace
   `Sentence := Propositional.Formula ℕ` with `LO.FirstOrder.Sentence ℒₒᵣ`" is not what the
   paper does and not what the payoff needs. The paper's own §Notation says its language is
   **a propositional calculus whose atoms are the prime sentences of first-order logic**
   (`tex:562`). The repo already builds atoms out of first-order material
   (`computationClaimSentence`, `quoteAtom`). The gap is not the formula type — it is that a
   `LUV` is a black-box threshold family (`gt : ℚ → Sentence`) rather than a formula one can
   **substitute into**.

2. **The earlier note's Part 1 is half wrong, and the wrong half is the decisive one.** It
   says "first-order syntax would not dissolve the `thm:ccee` obstruction … what relates
   `⌜X·w > r⌝` to `⌜X > r/s⌝` is not the term structure but `Θ`". The relating-facts half is
   right. But the obstruction the README actually records is an **emitter** problem — the
   propositional emitter must *compute* the atom code, hence compute `w_{f(n)}` — and term
   syntax dissolves exactly that: an FO sentence can *name* `⌜w⌝(⌜f⌝(n̄))` without evaluating
   it (`tex:597`, the paper's own remark that writing `⌜f(3) > 4⌝` "does not involve
   computing the value `f(3)`"). Section 6 works this end to end.

3. **The `thm:ccee` circularity (A2) genuinely dies under FO, and so do (B) and (C).** The FO
   route needs **no deductive-process extension**: the relating facts are theorems of the
   fixed theory `T`, so the endpoint is over the **base** inductor `liaHistory (theoremDP T)`.
   That removes the market/process fixed point (A2), the `ProductAtomFresh` premise (B — the
   language guarantees freshness), and the union-rendering objection (C). It is precisely
   what the ccee adjudication demanded when it rejected the union route: *"To discharge it
   generally requires a richer typed/term syntax."*

4. **But three new obstructions replace them, all verified, and two are Foundation-scale.**
   (i) Foundation has **no strong (functional) representability** — only weak/Σ₁
   (`re_complete`); the one lemma that comes close, `code_uniq`, is *commented out* and is
   semantic rather than `T ⊢`. (ii) Foundation has **no arithmetic-internal rational order**,
   which the repo's own `LUVArithmetic.lean` docstring already records as a verified
   obstruction — and `def:luv`'s coherence facts are exactly rational-order facts. (iii)
   Foundation's numerals are **unary**, so the whole-value `Encodable` code of `n̄` is doubly
   exponential in `n`; an FO atom therefore **cannot** be carried as a single token in the
   emission calculus. (iii) makes extending the Polish-notation symbol calculus into FO
   syntax **mandatory, not a later refinement** — there is no cheap whole-value fallback,
   because the whole-value class is *empty* here, not merely weaker.

5. **Measured surface.** Of 82 `.lean` files / 95,665 LOC, **66 mention `Sentence`; 36 (53,670
   LOC) carry at least one propositional-*structural* marker; 32 mention it opaquely only**.
   The earlier note's "68 of 77 files" is therefore an overstatement of the blast radius by
   roughly a factor of two — but the 36 that remain include the entire ~10,500-line emission
   calculus, which is the cost core.

6. **Verdict: do not start this. If it is ever started, it is a Foundation contribution
   first and a LogicalInduction refactor second.** Total 10–20 months, wider error bars than
   the efficiency programme's 8–15, and it competes for the same budget while closing 3 of 5
   qualified rows instead of 2. Details and the recommendation are in §8.

---

## 1. What the paper actually requires of the substrate

Three passages fix this, and together they overturn the framing of the earlier note.

**§2 is propositional, deliberately.** `tex:668`: *"Let `ℒ` be a language of propositional
logic, and let `𝒮` be the set of all sentences written in `ℒ`."* `def:world` (`tex:720`) and
propositional consistency are stated over that. The footnote at `tex:761` is explicit that
this is a choice being made against first-order logic: *"Because PA is a first-order theory,
and the only assumption we made about `ℒ` is that it is a propositional logic, note that the
axioms of first-order logic … must be included as theorems in `DP`."*

**The atoms are prime sentences of FO.** `tex:562`, §Notation, "First order theories and
prime sentences": *"we view any first order theory as specified in a propositional calculus
whose atoms are the so-called 'prime' sentences of first order logic, i.e., quantified
sentences like `⌜∃x: ⋯⌝`, and atomic sentences like `⌜t₁=t₂⌝` and `⌜R(t₁,…,tₙ)⌝` where the
`tᵢ` are closed terms."* The worked example there also fixes the decomposition's one
subtlety: `(7 > 1+1)` is a prime sentence but does **not** occur in the prime decomposition
of a formula where it sits under a quantifier — quantifiers are opaque.

**Where first-order syntax is genuinely load-bearing.** Exactly three places, all in §4:

| paper object | needs term/formula syntax? | why |
|---|---|---|
| `def:world`, p.c., `pcworlds`, `cworlds` | **no** | Boolean algebra over primes; `tex:727` |
| markets, pricings, belief states | **no** | functions on `𝒮` |
| traders, features, `def:tf`, exploitation | **no** | functions of price histories |
| `def:ec` | **no** (but see §3.3) | a runtime bound on a sequence |
| `def:luv` (`tex:1635`) | **yes** | "any formula `X` free in one variable that defines a unique value via `Θ`" |
| the shorthand `⌜R(X₁,…,X_k)⌝` (`tex:597`) | **yes** | expands to `⌜∀x₁…x_k: X₁(x₁) ∧ ⋯ → R(x₁,…,x_k)⌝` |
| `⌜⟨f⟩(⟨n⟩)⌝`, `⌜⟨w⟩_{⟨f⟩(⟨n⟩)}⌝` (`tex:604`) | **yes** | names the representing formula `γ_f`, does not evaluate |

So the migration target is **"FO syntax for LUVs and quoted values; propositional-over-primes
for everything else"**. That is not a substrate swap; it is a change of *atom type* plus a
first-order presentation for `LUV`.

**What prime decomposition requires, and whether Foundation has it.** It requires: a decidable
predicate picking out primes; a total map `Sentence L → Propositional.Formula (Prime L)`; and
the paper's factoring of leading negations out as Boolean operators. Foundation's
`Semiformula` (`FirstOrder/Basic/Syntax/Formula.lean:23`) is in **negation normal form** —
`neg` is a defined De Morgan pushdown, not a constructor — which makes the decomposition a
plain structural recursion: `and`/`or` are Boolean, `rel`/`exs` are positive primes, and
`nrel`/`all` are their negations. Foundation supplies none of this (`grep` for
prime-sentence / propositional-consistency / Boolean-valuation notions over `FirstOrder/`
returns only number-theoretic `IsPrime`), but it is ~40 lines, not a research problem — the
probe writes it and the kernel checks it (§7).

---

## 2. The interface reality check

CLAUDE.md says Foundation internals are "wrapped behind the thin `LogicalInduction.Sentence`
interface". **Measured, that is not true, and it was never intended to be**: the interface is

```lean
abbrev Sentence : Type := LO.Propositional.Formula ℕ   -- Framework/Foundations.lean:35
```

an `abbrev`, i.e. reducible, chosen deliberately so "Foundation's instances … transfer for
free" (same docstring). Nothing is hidden; every consumer can see the constructors, and 36
files do.

### 2.1 The split

| | files | LOC |
|---|---:|---:|
| all `LogicalInduction/**/*.lean` | 82 | 95,665 |
| mention `Sentence` | 66 | — |
| **(b) carry ≥1 propositional-structural marker** | **36** | **53,670** |
| (a) mention `Sentence`, no structural marker | 32 | — |
| neither | 14 | — |

LOC is per *file*, not per structural line; the marker counts in the table below are the
honest density proxy. Markers, in five groups:

* **b1** — constructor pattern-match / `induction φ with` over `Formula`'s five constructors.
* **b2** — Boolean-valuation semantics: `Boolean.Valuation`, `Boolean.val`, `BoolPCWorld`,
  `atomBound`, `sentenceAtoms`, `bitsWorld`, `FiniteWorld`.
* **b3** — the Polish-notation symbol calculus: `rpn`, `parseRpn`, `unRpn`, `escExpand`.
* **b4** — the `ℕ`-code layout: `Formula.toNat`/`ofNat`, `decode (α := Sentence)`.
* **b5** — `Formula.atom` used to *construct* sentences (the flat-atom-space assumption).

### 2.2 The category-(b) table — this is the cost core

| file | LOC | b1 | b2 | b3 | b4 | b5 | Σ | what changes under FO |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `Construction/Witnesses/RpnConditioning.lean` | 6893 | 0 | 0 | 472 | 6 | 1 | **479** | the `thm:scon` automaton is keyed to a 5-tag grammar; FO needs variadic arity |
| `Framework/RpnSentence.lean` | 1613 | 6 | 0 | 400 | 22 | 1 | **429** | the calculus itself: alphabet, parser, round trips, splice |
| `Construction/Witnesses/BoundedEvaluation.lean` | 2857 | 7 | 99 | 13 | 80 | 1 | **195** | decidable finite-world eval + its `Primrec` certificate |
| `Construction/LIACompiler.lean` | 7366 | 11 | 0 | 20 | 104 | 0 | **135** | `Primrec` decode over `Formula.ofNat`'s layout |
| `Properties/Calibration.lean` | 3566 | 0 | 112 | 0 | 0 | 0 | **112** | `BoolPCWorld` finite-world certificate machinery |
| `Properties/AffineCoherence.lean` | 949 | 26 | 70 | 0 | 0 | 0 | **91** | `BoolPCWorld`, `eval`, `atomBound`, compactness consumers |
| `Construction/Witnesses/PrefixMachine.lean` | 2206 | 46 | 0 | 0 | 32 | 8 | **85** | prefix coding over the formula layout |
| `Properties/LimitCoherence.lean` | 793 | 16 | 58 | 0 | 1 | 0 | **71** | `sentenceAtoms`, cylinder/Gaifman measure |
| `Construction/Witnesses/RpnFreeze.lean` | 870 | 15 | 0 | 51 | 2 | 0 | **68** | freeze-stream symbol surgery |
| `Construction/Budgeter.lean` | 1445 | 28 | 13 | 0 | 0 | 0 | **38** | Boolean payout evaluation in the budgeter |
| `Framework/RpnComputation.lean` | 330 | 0 | 0 | 32 | 3 | 0 | **35** | `Primrec` mirrors of the parser/transducer |
| `Construction/Witnesses/ConditioningCompiler.lean` | 3377 | 0 | 0 | 0 | 34 | 0 | **34** | token-model rewrite over pair codes |
| `Construction/Witnesses/HistoricalMaturity.lean` | 1888 | 0 | 26 | 7 | 0 | 1 | **34** | executable maturity certificates on finite worlds |
| `Framework/Criterion.lean` | 1798 | 5 | 5 | 22 | 3 | 2 | **33** | `PCWorld`, `rpn`, `parseRpn` definitions live here |
| `Framework/RpnEmission.lean` | 413 | 0 | 0 | 27 | 0 | 0 | **27** | poly-fuelled emission bridges |
| `Construction/Witnesses/BitPrefixSyntax.lean` | 713 | 0 | 6 | 8 | 0 | 9 | **20** | the bit-prefix sentence family (`def:ec` separator) |
| `Framework/RpnSplice.lean` | 446 | 0 | 0 | 16 | 0 | 0 | **16** | variable-width disjunction blocks |
| `Construction/Witnesses/ComputationDP.lean` | 840 | 0 | 4 | 0 | 8 | 3 | **13** | `eventAtom`; would *simplify* (category c) |
| `Framework/Compactness.lean` | 119 | 6 | 5 | 0 | 0 | 1 | **12** | clopen-truth-set induction over the connectives |
| `Framework/Expectations.lean` | 472 | 0 | 5 | 0 | 0 | 7 | **12** | `LUV`, `ValuesAt`, `indicatorWitnessLUV` |
| `Construction/LIAComputation.lean` | 594 | 0 | 0 | 0 | 6 | 0 | **6** | code-layout uses |
| `Construction/Witnesses/ProductDefinition.lean` | 788 | 2 | 0 | 0 | 2 | 2 | **6** | the exact-route product atoms; would be *deleted* |
| `Properties/FinitePerturbations.lean` | 790 | 0 | 0 | 0 | 7 | 0 | **7** | code-layout uses |
| `Construction/Witnesses/ConditioningPresentation.lean` | 241 | 0 | 3 | 0 | 0 | 0 | **3** | world plumbing |
| `Construction/Witnesses/LUVDeductiveProcess.lean` | 243 | 0 | 0 | 0 | 1 | 2 | **3** | would *simplify* (category c) |
| `Construction/Witnesses/LUVExpectationCertified.lean` | 712 | 0 | 0 | 0 | 1 | 2 | **3** | would *simplify* (category c) |
| `Construction/Witnesses/QuotationAffine.lean` | 4881 | 0 | 0 | 0 | 1 | 1 | **2** | `quoteAtom`; would *simplify* (category c) |
| `Construction/Witnesses/DigitConditioning.lean` | 1695 | 0 | 0 | 0 | 2 | 0 | **2** | contracted-stream rewrite |
| `Construction/Witnesses/StrictSeparators.lean` | 1556 | 0 | 1 | 0 | 1 | 0 | **2** | separator families |
| `Construction/Witnesses/ComputationSyntax.lean` | 753 | 0 | 0 | 0 | 0 | 1 | **1** | the FO↔propositional bridge; would *shrink* (category c) |
| `Construction/Witnesses/LUVArithmetic.lean` | 412 | 0 | 0 | 0 | 0 | 1 | **1** | `dd:luv-arith`; would be *superseded* (category c) |
| `Construction/Witnesses/LUVPresentation.lean` | 138 | 0 | 0 | 0 | 0 | 1 | **1** | would *simplify* (category c) |
| `Construction/Witnesses/QuoteCodeOfMarket.lean` | 1207 | 0 | 0 | 0 | 0 | 1 | **1** | the `thm:ccee` endpoint site |
| `Construction/Witnesses/UniversalPrefix.lean` | 1506 | 0 | 0 | 0 | 1 | 0 | **1** | Occam prefix machine |
| `Construction/TraderEnumeration.lean` | 97 | 0 | 0 | 1 | 0 | 0 | **1** | enumeration over the emission model |
| `Properties/Basic.lean` | 184 | 0 | 1 | 0 | 0 | 0 | **1** | world plumbing |
| `Properties/Coherence.lean` | 425 | 0 | 1 | 0 | 0 | 0 | **1** | world plumbing |

**Reading of the table.** The distribution is extremely skewed: the top four files carry
1,238 of the ~1,800 structural markers. Two clusters dominate.

* **The emission calculus** (`RpnSentence`, `RpnComputation`, `RpnEmission`, `RpnSplice`,
  `RpnConditioning`, `RpnFreeze` = 10,565 LOC, 986 markers). This is `def:ec`'s faithful
  symbol-metering, and §3.3/§6.4 show it is the item that cannot be deferred.
* **The Boolean-world layer** (`BoundedEvaluation`, `Calibration`, `AffineCoherence`,
  `LimitCoherence`, `HistoricalMaturity`, `Budgeter` = 11,538 LOC, 541 markers). §4 shows
  this cluster transports along a change of atom type rather than being rebuilt — it is the
  cheap half.

### 2.3 Category (c) — the code that gets *simpler*

The FO↔propositional bridge exists only because the public language is propositional. It
compresses a first-order claim into an `ℕ` atom and then translates `T`-proofs back:

```lean
-- ComputationSyntax.lean:220
def computationClaimSentence (claim : ComputationClaim) : Sentence :=
  LO.Propositional.Formula.atom claim.godelCode        -- godelCode packs (kind, encode schema, input)

-- QuotationAffine.lean:158
noncomputable def quoteAtom (w : ℕ) : Sentence :=
  quotationClaimSentence universalQuotePos universalQuoteNeg w
```

with `QuotationTheoryPresentation.quote_positive_enters : ∀ code input,
T ⊢ universalQuotePos/[↑(Nat.pair code input)] → …` as the translation obligation. Under an
FO atom type the atom **is** the sentence, and the `godelCode` fold, the two fixed universal
schemas, the `dd:quote-code` indexing discipline, and the entering lemmas all collapse into
"the process enumerates the prime decompositions of `T`'s theorems".

Bridge files: `ComputationSyntax` 753 + `LUVArithmetic` 412 + `LUVPresentation` 138 +
`LUVDeductiveProcess` 243 + `ComputationDP` 840 + `FeedbackUnconditional` 138 +
`UnconditionalOverLIA` 186 = **2,710 LOC**, of which perhaps half is pure bridging. Plus
`ProductDefinition.lean` (788 LOC) is deleted outright. Call it **~2,100 LOC recovered** —
real, and roughly 4% of the 53,670 that would have to be touched.

---

## 3. Foundation's first-order assets at the pin

`Foundation/FirstOrder/` is 37,942 lines. What is there, and what is not.

### 3.1 Present, and genuinely useful

* **Syntax.** `Semiformula L ξ n` (`Basic/Syntax/Formula.lean:23`), in **NNF** (8
  constructors; `∼` and `➝` are defined, not constructors). `Sentence L := Formula L Empty`.
  `DecidableEq (Semiformula L ξ n)` at `Formula.lean:298`.
* **Coding.** `Encodable (Semiformula L ξ n)` at `Basic/Coding.lean` with explicit
  `toNat`/`ofNat`, given `[∀ k, Encodable (L.Func k)] [∀ k, Encodable (L.Rel k)]
  [Encodable ξ]`. `ℒₒᵣ` has those (`Syntax/Predicate/Language.lean:139`). So sentence codes
  exist — but see §3.3 for what they cost.
* **Proof theory.** `Entailment (Theory L) (Sentence L)` (`Basic/Calculus.lean:307`) with
  `Entailment.Compact` (:314), `Entailment.Cl` (:325), `Entailment.Axiomatized` (:327), and
  `Entailment.Deduction` (:375). One-sided LK with cut. This is a real asset — and the repo
  currently uses **none** of it, because its world layer is semantic-Boolean, not `⊢`.
* **Arithmetic.** `𝗥₀` (`Arithmetic/R0/Basic.lean:15`), `PeanoMinus`, `IOpen`, `ISigma1`,
  `HFS`, `Bootstrapping` (formalized syntax and provability), `Incompleteness`. The repo
  already imports five of these files.
* **Substitution / rewriting.** `Rew` (`Basic/Syntax/Rew.lean`), `Semiformula.free`, `/[t]`.
* **`∃!` in the object language.** `∃⁰!` with an eval lemma at `Basic/Eq.lean:344` — so
  `def:luv`'s uniqueness clause is at least *statable*.

### 3.2 Absent — and these are the decisive ones

**(a) No prime-sentence or propositional-consistency layer over FO.** Confirmed by grep;
Foundation's first-order semantics is model-theoretic throughout. The earlier note said this
and it is still true. §4/§7 show it is ~40 lines to build, so it is not the problem.

**(b) No strong (functional) representability.** `Arithmetic/R0/Representation.lean:260`
gives only

```lean
/-- Weak representation of a r.e. predicate -/
theorem re_complete {A : ℕ → Prop} (hp : REPred A) {x : ℕ} :
    A x ↔ T ⊢ (codeOfREPred A)/[‘↑x’]
```

There is no theorem of the form `T ⊢ ∀ν (γ_f(n̄, ν) ↔ ν = ⟨f n⟩)` anywhere in
`Foundation/FirstOrder/` (grep for `∃!`/`ExistsUnique`/"provably total" returns only
model-internal `Bootstrapping` uses and `Interpretation.lean`). The nearest thing,
`code_uniq`, is **inside a block comment** (lines 115–162 of that file) *and* is semantic —
`Semiformula.Evalbm M` in models of `𝗥₀` — not `T ⊢`.

Worse for the standard route: strong representability is normally derived from R₀'s axioms
Ω₄ *and* Ω₅ (`∀x (x ≤ n̄ ∨ n̄ ≤ x)`). Foundation's `R0` has **Ω₁–Ω₄ only** — no trichotomy
axiom — so the least-witness construction `γ_f(x,y) := θ_f(x,y) ∧ ∀z<y ¬θ_f(x,z)` does not
close over `𝗥₀` as Foundation defines it. Workable at a stronger `T` (`𝐏𝐀⁻`, `𝐈𝚺₁`), which
the repo already parameterises over, but it is greenfield either way.

*How much this matters:* the repo's `dd:luv-arith` sidesteps it for **computable** LUVs by
representing a *decidable* threshold predicate and its complement — `re_complete` then gives
both directions (`LUVArithmetic.lean` module docstring). That trick does not extend to a
LUV whose value is not computable (the paper's own `TwinPrime`), nor to the `thm:ccee`
product over an arbitrary e.c. source family.

**(c) No arithmetic-internal rational order.** The repo says this itself, in the file that
would know:

> **What is not reconstructed.** The fully general `def:luv` (an *arbitrary* value-defining
> formula, with rationals encoded inside `ℒₒᵣ` and its genuinely nonstandard world values) is
> *not* built: Mathlib/Foundation expose no arithmetic-internal rational order.
> — `Construction/Witnesses/LUVArithmetic.lean`

Every `def:luv` coherence fact is a rational-order fact (`⌜X > r⌝ → ⌜X > s⌝` for `s < r`), and
under FO those must become `T`-derivations rather than hypotheses. This is the item that
turns §6's payoff from "close `thm:ccee`" into "formalize enough arithmetic in `T` first".

### 3.3 The numeral problem — the single hardest measured fact

`Semiterm.Operator.numeral` (`Basic/Operator.lean:156`) is **unary**:

```lean
def numeral (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L] : ℕ → Const L
  | 0     => Zero.zero
  | n + 1 => Add.add.foldr One.one (List.replicate n One.one)
```

and `Semiterm.toNat` codes `func f v` as `Nat.pair 2 (Nat.pair k (Nat.pair (encode f)
(Matrix.vecToNat …))) + 1`. `Nat.pair a b ≥ max a b ^ 2`, so **each `+ 1` in a numeral squares
the code**: `encode n̄` has ≈ `2ⁿ` bits, i.e. the code is doubly exponential in `n`.

Two consequences, and they point in opposite directions:

* **Symbol count is fine.** `n̄` is `Θ(n)` symbols, and `def:ec` is poly in `n` *written in
  unary* (`tex:753`), so a unary numeral costs nothing against the paper's own metering. The
  `thm:ccee` product sentence `⌜∀xy (X_n(x) ∧ γ_w(⌜f⌝(n̄), y) → x·y > r)⌝` is `O(|X_n| + n)`
  symbols. Poly. Good.
* **Whole-value coding is fatal.** An RPN atom token carries `Encodable.encode` of the atom,
  whose *digit length* in the emission stream would be `≈ 2ⁿ`. Not poly — by a wide margin.

So under an FO atom type, `PolySentenceCodes`-style whole-value metering is not a weaker
fallback class, it is an **empty** one for any atom family whose numerals vary with `n`.
`RpnSentenceCodes` (symbol metering) is the only inhabitable class, and the Polish-notation
calculus must therefore be extended **into the atom**, with FO formula constructors and a
variadic term sub-calculus. That is the ~10,500-line cluster from §2.2, and it is on the
critical path, not after it.

This also bites the *existing* machinery, not just `thm:ccee`: `quoteAtom` substitutes the
numeral of `Nat.pair code input` into a fixed schema. Propositionally that is one `ℕ` atom and
costs nothing. As an FO sentence it would be `Θ(Nat.pair code input)` symbols — exponential in
the bit-length of the input. **Foundation would need a binary numeral presentation (with its
`𝗥₀`/`𝐈𝚺₁` arithmetic redone) before the repo's own quotation atoms survive the move.** No
such presentation exists at the pin.

---

## 4. The worlds problem

`PCWorld := LO.Propositional.Boolean.Valuation ℕ` (`Criterion.lean:772`), i.e. `ℕ → Prop`, with
`Holds` = Foundation's `Formula.Boolean.val`. `BoolPCWorld := ℕ → Bool`
(`AffineCoherence.lean:23`) with a decidable `eval` and an `atomBound` finite-support measure.

**The good news: both are already atom-polymorphic upstream.** Foundation defines
`Boolean.Valuation α := α → Prop` and `Formula.Boolean.val` over a general `α`
(`Propositional/Boolean/Basic.lean:12,18`), and `Encodable (Formula α)` needs only
`Encodable α`. So changing the atom type from `ℕ` to a prime-sentence type is a *change of
instantiation*, not a rebuild, for:

* `PCWorld.Holds` / `payout` / `ConsistentWith` / `ConsistentWithTheory` — unchanged;
* `Framework/Compactness.lean` — the clopen induction (5 cases, one per connective) is
  unchanged, because quantifiers are *atoms* under prime decomposition and atoms are already
  handled as coordinate-projection preimages;
* `BoolPCWorld.eval` / `atomBound` / `FiniteWorld` / `bitsWorld` / `sentenceAtoms` — unchanged
  in shape; `atomBound : Sentence → ℕ` becomes "one above the largest atom *code*", which is
  what it already is.

**Decidability of the finite checks survives.** The relevant uses are
`eval_toBoolPCWorld_restrict` (restriction to the first `B` atoms), `FiniteWorld.payoutRat`,
and the `Calibration`/`HistoricalMaturity` certificate machinery. All of them quantify over
`Fin B → Bool` for a `B` computed from the sentence. Prime sentences of FO are infinitely
many, but every *sentence* still mentions finitely many of them, and `atomBound` still bounds
their codes. Nothing here needs the atom set to be `ℕ` — only `Encodable` and `DecidableEq`,
both of which the probe confirms at `Sentence ℒₒᵣ`.

**One genuine cost.** `BoolPCWorld` is `ℕ → Bool`, and the compiled certificates route through
`List Bool` precisely because "`BoolPCWorld` is a *function* type, which admits no
`Primcodable` instance" (`AffineCoherence.lean` docstring). With atom codes now being codes of
FO sentences, the `Primrec` decoding step (`Formula.ofNat` at the new atom type) has to decode
`Semiformula.ofNat`, which uses `Matrix.getM`/`natToVec` with well-founded recursion over a
*variadic* term vector. `LIACompiler.lean` carries 104 uses of the current (binary, 5-tag)
layout; redoing them at the FO layout is the known `Primrec`-blowup zone (see the `Nat.sqrt`
whnf gotcha in `notes/consolidation.md`). **This is the highest-variance engineering item
after the emission calculus.**

---

## 5. Migration strategies, costed

Three candidates. Estimates are calibrated in §5.4.

### 5.1 (A) Big-bang `Sentence := LO.FirstOrder.Sentence ℒₒᵣ`

**Rejected on the paper, not on cost.** It is unfaithful: the paper's worlds are p.c. over
primes, not FO models, and a naive FO `Sentence` has no Boolean-over-primes layer, so the
criterion would have to be restated. It also forfeits the free reuse identified in §4. If
anyone proposes this, the answer is §1.

### 5.2 (B) Abstract the framework over a substrate interface

**Rejected on measurement.** The interface would have to expose: `DecidableEq`, `Encodable`,
a Boolean-valuation semantics, a finite-atom-support measure, *and* the whole Polish-notation
symbol calculus (alphabet, parser, round trips, splice, `Primrec` mirrors, the conditioning
automaton). That last item is 10,565 LOC and is inherently *not* interface-level: the
conditioning compiler's correctness rests on `rpn (φ ⋏ ψ) = 3 :: rpn φ ++ rpn ψ` — a specific
grammar identity, not a property any two substrates would share. An interface that abstracts
over it would have to *assume* the identity, which is the shape CLAUDE.md's rule 1 exists to
forbid. Retaining both substrates also directly violates the consolidation discipline
("no parallel classes that exist only because a definition was upgraded mid-project").

### 5.3 (C) Prime-atom refinement + a first-order `LUV` — the only viable route

Keep `LO.Propositional.Formula` as the substrate. Change what the atoms *are*, and give `LUV`
a first-order presentation it can be substituted into. Staged:

**Stage 0 — atoms become prime sentences (mechanical + disclosure).** `Sentence :=
Propositional.Formula (Prime ℒₒᵣ)` with `Prime` a decidable subtype of `Sentence ℒₒᵣ`,
`primeDecompose` (probe, §7), and `theoremDP T` re-based on it. Touches the b5 and b2 markers
(≈ 300 sites) and re-points `Framework/Foundations.lean`. **Buys nothing on its own** — this
is important: it is a pure prerequisite. *2–4 sessions.*

**Stage 1 — `Primrec` at the new layout.** Redo `LIACompiler`'s decode chain and
`BoundedEvaluation`'s `Primrec` certificates over `Semiformula.ofNat`'s variadic coding.
*4–10 sessions, high variance* (§4's last paragraph).

**Stage 2 — a first-order `LUV`, and `ValuesAt` derived rather than assumed.** A
`FOLUV := { φ : Semisentence ℒₒᵣ 1 // T ⊢ ∃⁰! φ }`, the §Notation shorthand expansion
`⌜R(X₁,…,X_k)⌝`, and `FOLUV.toLUV`. Then *derive* `PCWorld.ValuesAt` from `T`'s theorems
instead of assuming it — which needs **rational order inside `ℒₒᵣ`, provably in `T`**
(§3.2(c)). Every existing LUV construction (`arithmeticThresholdLUV`, `indicatorProductLUV`,
`meshProductLUV`, `ComputableLUV.toLUV`, the quote LUVs — 12 `def`s in `QuotationAffine`
alone, 16 in `LUVSyntax`) must be rebuilt as FO formulas with proved uniqueness clauses.
**This is a Foundation-scale contribution, not a repo refactor.** *3–6 months.*

**Stage 3 — strong representability, and `thm:ccee` exact over the base inductor.** Prove
`T ⊢ ∀ν (γ_f(n̄,ν) ↔ ν = ⟨f n⟩)` for total computable `f` at a theory with a total order
(§3.2(b)); build the product by substitution; discharge the relating facts. *1–3 months*, and
upstreamable.

**Stage 4 — the FO emission calculus (mandatory, per §3.3).** Extend the Polish alphabet with
FO formula constructors and a variadic term sub-calculus; re-prove the self-delimiting
argument with an arity-indexed pending counter; redo `parseRpnC`/`unRpnTokensC` in `Primrec`;
re-key `RpnConditioning`'s automaton. Plus a **binary numeral** presentation in Foundation
with its `𝗥₀`/`𝐈𝚺₁` arithmetic redone, without which the repo's own `quoteAtom` family
becomes unemittable. *4–9 months.* **No endpoint's efficiency certificate exists before this
completes**, so by CLAUDE.md rule 1 there is no partial credit until Stage 4 lands.

### 5.4 Calibration

Two data points from this repo, both cited from the notes:

* `notes/boundary-propositional-substrate.md` §D estimated **4.5–6 sessions** for the ccee
  exact route; it took **~1**. Estimate ran ~5× high. That estimate's table is entirely
  *lemma-confirmed* items ("re-index the schema", "lift along `DP ⊆ DP'`") — every row named a
  lemma that already existed.
* `notes/boundary-efficiency-model.md` Stage 1 estimated **2–4 weeks** and landed on schedule
  (see "What Stage 1 landed (2026-08-11)"). Also a well-scoped item, against a re-surveyed
  toolchain.
* Against which, `LogicalInduction/README.md` records that its own estimates "have twice moved
  upward on contact".

The pattern: **items whose lemmas were confirmed to exist estimate accurately or high; items
that are greenfield move upward.** Stages 2, 3 and 4 above are *all* greenfield — no
Foundation lemma exists for strong representability, rational order in `T`, binary numerals,
or an FO symbol calculus. So they should be read at the pessimistic end of their ranges, and
the total below is quoted that way.

### 5.5 Which of the 66 inventory rows move

| | count | detail |
|---|---:|---|
| rows whose **statement text** changes | 66 | all — the global model disclosure names `Formula ℕ` |
| rows whose **tier** could improve | 3 | `def:luv`, `def:blcp`, `thm:ccee` |
| rows that **cannot** move | 2 | `def:ec`, `thm:ifp` — both are `dd:fuel`, untouched by syntax |
| rows that **re-prove** | ~36 files' worth | the category-(b) surface (§2.2) |
| rows that **transport** | ~32 files' worth | category (a): sentence used as an opaque token |

Currently: 31 `universal`, 30 `instantiated`, 5 `qualified`. The FO programme's entire tier
payoff is **3 of the 5 qualified rows**.

---

## 6. Payoff audit — and the critical `thm:ccee` question

The brief asks whether the ccee obstruction **survives** FO. Worked end to end:

### 6.1 What the paper's product sentence actually is

By §Notation's shorthand (`tex:597`), `⌜⟨X_n⟩ · ⟨w⟩_{⟨f⟩(⟨n⟩)} > r⌝` abbreviates

```
⌜∀x y : X_n(x) ∧ γ_w(⌜f⌝(n̄), y) → x·y > r⌝
```

a **quantified**, hence **prime**, sentence — propositionally an atom, exactly as the earlier
note said. So the earlier note is right that the product is an atom either way.

### 6.2 Why that nevertheless changes everything

The README states the blocker as: an exact product LUV needs *"either the deferred weight's
value (unavailable to an emitter: only P-generable, deferred, and the resulting threshold's
denominator is not polynomially sized) or the infinite disjunction."*

FO defeats the first disjunct **at the syntax level**. `γ_w` is a *fixed* formula; the sentence
names the program and the day and never evaluates `w`. The paper says so in its own voice
(`tex:604`): *"writing down a sentence like `⌜f(3) > 4⌝` does not involve computing the value
`f(3)`; it merely requires writing out the definition of `γ_f`. This distinction is important
when `f` has a very slow runtime."* Symbol count `O(|X_n| + n)` — poly (§3.3).

Two things follow, and they are the whole payoff:

* **No process extension is needed.** The relating facts are theorems of the *fixed* `T`, so
  the deductive process stays `theoremDP T` and the endpoint is over the **base** market
  `liaHistory (theoremDP T)`.
* **Therefore the A2 circularity dies.** `w` is computable from `P = liaHistory (theoremDP T)`
  (that is `PGenerableRat.computable`), and `P` is a function of `T` alone. `γ_w` is built
  from that computable function. One direction; no fixed point. The (A2) dilemma —
  "narrow `w` to `PolyRatCodes`, or carry a second P-generability premise" — simply does not
  arise.
* **And (B) and (C) die with it.** `ProductAtomFresh` was the propositional restatement of a
  guarantee FO gives by the language (the earlier note says exactly this in §B); with no fresh
  atoms it is not needed. The union rendering is gone, so codex's rejection —
  *"the exact union result concerns a different constructed inductor"* — is answered on its
  own terms. Its closing sentence is the FO route's charter: *"To discharge it generally
  requires a richer typed/term syntax."*

**So: the ccee obstruction as currently documented does not survive FO.** That part of the
payoff case is real, and it is stronger than the earlier note allows.

### 6.3 What replaces it — say this loudly

The obstruction moves rather than vanishing, and it moves somewhere harder to reach:

1. **Every relating fact becomes a `T`-derivation that must be produced in Lean.** For a world
   `W` consistent with `theoremDP T` to value the product atom at `x·w`, we need
   `T ⊢ ⌜X·w > r⌝ ↔ ⌜X > r/w̄⌝`, which needs `T ⊢ ∀x (x·w̄ > r ↔ x > r/w̄)` — a **Π₁** fact
   about coded rationals. Σ₁-completeness does not give it; `re_complete` does not give it;
   it must be *proved in `T`*, and Foundation has no arithmetic-internal rational order
   (§3.2(c), the repo's own words). In the paper this step is invisible ("assume `Θ` represents
   computations"); in Lean it is the entire cost.
2. **`γ_w` needs strong representability, absent at the pin** (§3.2(b)), and the standard
   derivation does not close over Foundation's `𝗥₀` (missing Ω₅).
3. **Emission needs Stage 4 and binary numerals** (§3.3). Until then no efficiency certificate
   exists — and per CLAUDE.md rule 1, an endpoint without its trader's certificate is not done.

The honest summary: **FO trades a *modeling* obstruction (disclosed, understood, with a
non-vacuous witness at both ends) for a *formalization* obstruction (three greenfield
Foundation developments).** The first is a paragraph in a README. The second is a year.

### 6.4 Everything else that moves, and everything that does not

**Closes:** `def:luv` — `LUV` becomes the paper's "formula free in one variable that defines a
unique value via `Θ`", with the uniqueness clause carried as the paper carries it. Audit
finding **B4** closes with it, and the derivative `def:blcp` row follows. `thm:ccee` closes
*subject to* §6.3. That is the full list: **3 of 5 qualified rows.**

**Simplifies:** the ~2,100 LOC of category-(c) bridge (§2.3), and `ProductDefinition.lean`
(788 LOC) is deleted.

**Does not move:** `def:ec` and `thm:ifp`. Both are `dd:fuel`. `thm:ifp`'s blocker is the
digit calculus's failure to close under inverse operations — a property of the *efficiency
model*, not the syntax; `EfficientPrefixPatch` remains uninhabited. Only
`notes/boundary-efficiency-model.md`'s programme touches these.

**Gets worse before better:** `def:ec`'s own faithfulness. Between Stage 0 and Stage 4 the
repo would have FO atoms with no symbol calculus for them, i.e. an *empty* emission class
(§3.3) — strictly worse than today, with no green intermediate. That is the sharpest
scheduling fact in this note.

---

## 7. The probe

`LogicalInduction/Framework/FirstOrderSubstrateProbe.lean` — not imported by anything, claims
no paper node, outside the checked gates. It backs the two claims most likely to be doubted.

**Status: compiles clean under the installed toolchain** (`lake env lean`, no errors, no
`sorry`).

**P1 — the prime decomposition is definable, total, and lands in the existing world layer.**
`primeDecompose : Semiformula L ξ 0 → LO.Propositional.Formula (Semiformula L ξ 0)`, with the
paper's factoring checked: `nrel r v ↦ ∼(atom (rel r v))` and `∀⁰ φ ↦ ∼(atom (∃⁰ ∼φ))`, and
`and`/`or` the only recursive cases. Foundation's NNF makes this a structural recursion with
no normalisation step. The probe also confirms `DecidableEq (Sentence ℒₒᵣ)`,
`Encodable (Sentence ℒₒᵣ)`, and both at `Propositional.Formula (Sentence ℒₒᵣ)` — the three
instances the world layer and `def:ec` need — and exhibits `holdsFO`, showing
`Formula.Boolean.val` applies unchanged at the new atom type. **This is the note's evidence
that §4's "transports rather than rebuilds" is not optimism.**

**P2 — unary numerals make whole-value atom codes doubly exponential.** The probe pins the
unary shape definitionally (`Semiterm.Operator.numeral_add_two`, so each successor adds one
`func Add` layer) and proves `pair_sq_le : a ≤ b → a * a ≤ Nat.pair a b` — the squaring step
that turns a depth-`n` `Nat.pair` nest into a doubly exponential value. This is the measured
basis for §3.3 and for Stage 4 being mandatory.

**An unplanned third finding, and it raises the Stage-1 estimate.** The defining equations of
`primeDecompose` do **not** hold by `rfl` — only by `simp [primeDecompose]` — even with all
eight constructors spelled out, because `Semiformula L ξ n` is *indexed* by the bound-variable
arity and so compiles through a motive-carrying recursor. `LO.Propositional.Formula α` is a
plain inductive and is definitionally transparent. Relatedly, the `and` equation does not fire
on `φ ⋏ ψ`, because `⋏` at `Semiformula` is `LogicalConnective.wedge` and `simp` will not
unfold the instance. Both are trivial in a 160-line probe. Neither is trivial in
`LIACompiler.lean` (7,366 LOC) or `BoundedEvaluation.lean` (2,857 LOC), whose `Primrec`
certificates lean on exactly that transparency throughout — which is why §5.3's Stage 1 is
quoted at 4–10 sessions with high variance rather than as a mechanical port.

_The probe is committed alongside this note as the Stage-0 record, in the same role as
`Construction/Machine/TimedRespectsProbe.lean` plays for boundary 1: it is imported by
nothing, claims no paper node, and is outside the checked gates by construction._

---

## 8. Verdict

### Staged plan (if it is ever taken)

The only viable route is (C) — prime-atom refinement plus a first-order `LUV`, keeping
`LO.Propositional.Formula` as the substrate, because that is what the paper itself does
(`tex:562`).

* **Stage 0 — atoms become prime sentences.** *2–4 sessions.* Mechanical; buys nothing alone.
* **Stage 1 — `Primrec` at the new coding.** *4–10 sessions, high variance* — and the probe
  found an unplanned reason for the variance: `Semiformula` is an *indexed* inductive and is
  not definitionally transparent, which is what the existing `Primrec` layers rely on (§7).
* **Stage 2 — first-order `LUV`; `ValuesAt` derived, not assumed.** Requires rational order
  inside `ℒₒᵣ` provable in `T`. *3–6 months. Foundation contribution.*
* **Stage 3 — strong representability; `thm:ccee` exact over the base inductor.**
  *1–3 months. Upstreamable.*
* **Stage 4 — the FO emission calculus + binary numerals in Foundation.** *4–9 months.*
  **Mandatory**: no efficiency certificate — hence no completed endpoint under CLAUDE.md
  rule 1 — exists before it lands.
* **Do not attempt:** strategy (A) (unfaithful to `def:world`) or strategy (B) (the
  conditioning compiler's correctness rests on a specific grammar identity, so the symbol
  calculus cannot be interface-level; and retaining both substrates violates the
  consolidation discipline).

### Single riskiest step

**Stage 4's variadic symbol calculus, and specifically its `Primrec` mirror.** The current
`parseRpnC`/`unRpnTokensC` proofs (`Framework/RpnComputation.lean`) already sit in the
`Nat.sqrt`-whnf blowup zone recorded in `notes/consolidation.md`; the FO version must decode
an arity-indexed term vector via `Matrix.natToVec` inside `Primrec`, and it must do so for a
grammar whose self-delimiting proof (the pending-subtree counter) has to be re-established at
variable arity. And unlike Stage 3, it is not upstreamable — nobody else wants it.

*De-risking move before committing anything:* prototype the arity-indexed pending-counter
argument for a two-constructor variadic toy grammar, and attempt `Primrec` of its parser. If
that is awkward, the whole programme should stop there, because Stage 4 gates every endpoint.

### Honest total, with error bars

**10–20 months, ~15,000–30,000 lines**, of which roughly half is Foundation work (strong
representability, rational order in `ℒₒᵣ`, binary numerals) rather than LogicalInduction work.
The bars are wider than the efficiency note's because **every stage after 0 is greenfield** —
no Foundation lemma exists for any of the four new developments — and §5.4's calibration says
greenfield estimates in this repo move upward, twice on record.

### Comparison with the efficiency programme

| | efficiency model (boundary 1) | FO substrate (boundary 2) |
|---|---|---|
| estimate | 8–15 months, 8,000–13,000 lines | **10–20 months, 15,000–30,000 lines** |
| qualified rows closed | 2 (`def:ec`, `thm:ifp`) | **3** (`def:luv`, `def:blcp`, `thm:ccee`) |
| partial credit | Stage 1 already landed and is standalone-useful | **none before Stage 4** |
| intermediate state | additive, outside the gates, no strength claim changes | **regressive**: FO atoms with no symbol calculus is an *empty* emission class |
| upstream value | first closure theorems for a poly-time TM class; Mathlib has a `proof_wanted` for exactly this | strong representability + binary numerals for Foundation; real, but nobody has asked |
| de-risk probe | executed, and it *changed the decision* | executed (§7); confirms the cheap half is cheap, the expensive half is expensive, and surfaced a third cost (indexed-inductive opacity) that was not in the plan |
| worst case | Stage 3 fails; Stages 1–2 still stand | Stage 4 fails; **the repo is left worse than it started** |

The two programmes are within a factor of ~1.5 on cost. They differ decisively on **shape**:
the efficiency programme is additive with a landed first stage and a preserved fallback; the
FO programme has a long regressive middle and no green stopping point until the end.

### Recommendation

**Do not start this.** Three reasons, in order of weight:

1. **The intermediate states are worse than the current state.** Between Stages 0 and 4 the
   repo would carry FO atoms with an empty emission class — not a weaker disclosure, an
   *uninhabitable* one. Every trader certificate in the repository depends on that class. There
   is no honest place to stop, which is exactly what the efficiency programme's staging was
   designed to provide.
2. **The payoff is one paragraph, and its consumer does not need it.** `thm:ccee`'s slack is
   inert at the one known downstream interface (`notes/deference-compatibility.md`), the mesh
   endpoint keeps the row, and the earlier note's non-vacuity witnesses stand at both ends.
   `def:luv`/`def:blcp`/B4 are disclosure-quality items, honestly recorded and stable.
3. **The bulk of the work belongs upstream.** Strong representability, rational order in
   `ℒₒᵣ`, and binary numerals are Foundation's to own. If Anson wants this direction, the
   right first move is **not** a repo refactor but a Foundation PR for strong representability
   (§3.2(b)) — bounded, independently valuable, and it converts the largest unknown into a
   known before a single line of `LogicalInduction` changes.

**What to do instead, cheaply and now.** Three corrections this spike produced, none of which
costs a refactor:

* `notes/boundary-propositional-substrate.md` Part 1 should be amended: its claim that
  "first-order syntax would not dissolve the `thm:ccee` obstruction" is wrong on the emitter
  half (§6.2), and its "68 of 77 files, not stageable" cost figure overstates the blast radius
  by ~2× (§2.1). The *conclusion* — do not close this boundary — survives, and is now better
  supported.
* `LogicalInduction/README.md`'s boundary-2 paragraph should name the real mechanism: what the
  propositional substrate lacks is not the *term* but **deferred denotation** — a sentence that
  names a value without computing it.
* The `thm:ccee` row's "what would close it" should point here rather than at the union route,
  which the adjudication rejected.

---

## Appendix — how the counts were made

Reproducible from the repo root, over
`find LogicalInduction -name '*.lean' ! -name 'FirstOrderSubstrateProbe.lean'` (82 files,
95,665 LOC). A file is **category (b)** if it matches at least one of:

```
b1  \| *(Formula\.)?(atom|falsum|imp|and|or) |\| *\.(atom|falsum|imp|and|or)\b
    |\| *φ (🡒|⋏|⋎) ψ|induction φ with|Formula\.rec
b2  Boolean\.Valuation|Boolean\.val|BoolPCWorld|atomBound|sentenceAtoms
    |extendFiniteAssignment|bitsWorld|FiniteWorld
b3  \brpn\b|parseRpn|unRpn|escExpand|rpnLen|unRpnTokens|parseRpnC|rpnBlock
b4  Formula\.toNat|Formula\.ofNat|encode_atom|encode_and|encode_or|encode_imp
    |encode_falsum|decode \(α := Sentence\)
b5  Formula\.atom
```

and **category (a)** if it matches `\bSentence\b` but none of the above. The per-file numbers
in §2.2 are `grep -c` line counts per group (a line matching two groups counts once per
group), so they measure *density*, not lines-to-rewrite. Spot-checked by hand at
`RpnConditioning.lean` (b3 hits are genuine `rpn`/`parseRpn` uses, not `Rpn*` type names) and
`LIACompiler.lean` (b4 hits are genuine `Formula.ofNat`/`toNat` layout recursions).

Known imprecision, disclosed: `cases φ` and `rcases φ` were **excluded** from b1 because they
match non-`Sentence` scrutinees; a small number of constructor case-splits are therefore
missed, so 36 is a floor. Marker *counts* are line-based and undercount multi-hit lines.
Neither affects the note's conclusions, which turn on the two dominant clusters (§2.2) and on
the Foundation facts in §3, not on the exact totals.
