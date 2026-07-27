# Formalization Knowledge — Parametric Bounded Löb (Critch 2019), branch `critch-pbl`

Permanent, curated facts about this formalization. Committed with the code; read by every
harness agent before working. Add an entry only if a future fresh-context agent would act
differently for knowing it. One bullet per fact, newest last. Cross-reference finding IDs
(RN-Fxx) where an entry originated from an audit. Paper: `notes/critch2019.pdf`.
Project plan: `notes/critch-pbl-roadmap.md` — its four standing scope decisions are binding.

## Correspondence table

| Paper (§/symbol) | Lean name | Notes |
|---|---|---|
| §3.1 `BBew[m,n,k]` / `□ₖ` | `BoundedProvability.bbew : Semisentence L 2` | var 0 = bound (object-level), var 1 = formula code; helpers `prt` (bound term) / `pr` (numeral); **single-system**: one `T`, one `ProofMeasure` (R2-F04 — the T₀/μ₀ split lost the paper's re-necessitation step; the specialization is the honest interface) |
| §3.1 Eval₁ extension | `bbew₁` + class `BEvalSpec` | box over a 1-free-variable formula; what Theorem 1's parametric formula consumes |
| Property 4's boxed-box `□_z(□ₐ(φ[k]))` | `bbewInner : Semisentence L 1 → Semisentence L 3` | slots: outer bound, inner bound, argument — Eval₂ composition; inner formula has BOTH `a` and `k` unbound so Eval₁ can't express it; anchored per-numeral by `BEvalSpec.eval_spec_inner` (R2-F02) |
| §2/§4 `⊢ₖ` judgment | `ProofMeasure` (fields `Pf sound complete mono`) | abstract bounded-proof judgment; concrete measure is Phase B |
| §3.2 Property 1 | class `BImpDistr` | ONE internal theorem over `bbew₁`, `(∀k)(∀a)(∀b)` inside the turnstile, open L(1) formulas (R1-F02, R2-F01) |
| §3.2 Property 2 | class `BQuantDistr` | abstract computable ν via graph formula + **internal totality & functionality** (R1-F05, R2-F05) |
| §4 Definition 1 + Properties 3–4 | class `BExpansion` | ONE computable `e` (graph `eGraph` + spec + total + func); P3 bounded premise + `e(k)` outer bound; P4 internal over `bbewInner` (R1-F03/F06, R2-F02) |
| bundle | `BHBL` | extends the five classes |
| §4 Proposition 1 | class `ParametricDiagonalization` (`Critch/BoundedProvability/Diagonal.lean`) | fields `fixedpoint`/`diagonal`; r = 1 form; quote hypothesis `GödelNumber L (Semisentence L 1)`; ℒₒᵣ instance `instParametricDiagonalizationLOR` (`Critch/ParametricDiagonal.lean`) via Foundation's `Arithmetic.parameterized_diagonal₁` under Foundation's own names (R3-F03/R3-F08) |
| — | `Critch/Infrastructure/QuoteSentence.lean` | Sentence-level quote commutation; Foundation-upstream candidates (R1-F13) |

§-map (R1-F07): Properties 1–2 live in **§3.2**; §4 contains Definition 1, Properties 3–4,
and Theorem 1. Cite accordingly.

## Design decisions

- Roadmap standing decision 1: proof-size measure must be an internal derivation-size
  function (nodes/symbols), **not** Gödel-number magnitude. Now **empirically confirmed**,
  not just planned: see Pitfalls (2048-factor measurement, R1-F04). The concrete measure is
  a Phase B obligation; the Phase A interface stays measure-abstract via `ProofMeasure`.
- Roadmap standing decision 2: agents are sentence families via derivability conditions
  (paper eq. 6.5); program semantics/quining out of scope (mirrors the Barász boundary).
- Roadmap standing decision 3: Gödel-quote/diagonal machinery keeps unary numerals;
  efficient numerals only on the parameter-specialization path.
- Roadmap standing decision 4: numeral cost is an abstract ν(k) — never bake in O(lg k).
- ν enters Property 2's internal statement via its **graph formula** (paper §2.4
  abuse-of-notation desugaring: `□_{C+2N+ν(k)}` ≡ `(∀y)(Γ_ν[k,y] → □_{C+2N+y})`), tied to a
  meta-level `Computable ν` by a representability spec. A `Semiterm` carrier for ν was
  considered and REJECTED: L_or term values are polynomial in k, so a term equal to
  `numeral (lg k)` cannot exist — the same fake-safe trap as baking in `lg`. (R1-F05)
- `BMono` is stated internally with additive slack (`∀ a d, □ₐ → □_{a+d}`) rather than `≤`,
  keeping the core interface's language assumption to `L₀.Add`.
- If Theorem 1's proof later needs stronger νGraph↔ν coherence (e.g. internally provable
  totality), that is an interface **extension**, not a rewrite (fixer flag, round 2).

- All Theorem-1 consumers on L_S(1) formulas (BImpDistr, BMono, innerNec) are single
  internal theorems over `bbew₁`/`bbewInner` with `k` and the bounds quantified inside the
  turnstile (R2-F01/F02/F10). Closed-sentence forms are NOT stored — derivable from the
  open form + `eval_spec` at a fixed numeral; derive only when a consumer exists.
- **Graph-formula rule** (R2-F05 cross-exam, generalize it): any computable function
  entering internal statements via a §2.4 graph (ν, e, later g) must carry internal
  totality AND functionality fields, not just the per-numeral spec — `Γ ∧ Con_x(T)`
  satisfies spec + guarded conclusion vacuously at nonstandard parameters while totality
  would prove Con(T). Asymptotic comparisons stay out of the class — but NOT as external
  `Asymp ≺` facts either (R3-F01/R3-F05): the three bound weakenings (eqs 4.4/4.5/4.7)
  consume INTERNALLY provable comparisons, which external `≺` cannot supply — Con-guard
  counterexample: a computable bound that behaves like k² unless a T-contradiction proof
  of code ≤ k exists is externally k² with total functional graph, yet its internal
  eventual lower bound would prove Con(T). These comparisons enter as hypotheses of
  Theorem 1's Lean statement, stated in graph vocabulary for f, g, h (anticipated
  extension for the Theorem 1 phase), never as class fields.
- R2-F03 resolution: no internal-(∀k) eval conversion exists or is needed — pp. 6–8 stay
  in `bbew₁`/`bbewInner` form from Quantifier Distribution onward, and only the final
  modus ponens of eqs 4.6+4.7 lands box-free at `(∀k>k̂)(p[k])`. (Correction, R3-F05
  documentation remedy: this entry previously called eqs 4.6–4.7 box-free — false for
  4.7, which is `(∀k>k̂)(□_{g(k)}(ψ[k]))`.) Per-numeral `eval_spec`(+`_inner`) are honest
  §3.1 specs and vacuity anchors.
- Anticipated interface EXTENSIONS for the ParametricLöb proof phase (extensions, not
  rewrites): (a) forming the diagonal `G` before `ψ` exists needs `bbew₁` exposed as a
  code-slot instance of one code-parametric 3-var formula (§3.1 "Eval₁ is represented");
  (b) eq 4.5's weakening may need a `bbewInner`-form mono; (c) the internal bridge between
  `□_b(□_{g(k)}ψ[k])` as `bbew₁`-of-desugared-box vs `bbewInner ψ` at `a := g(k)` is a
  proof-phase obligation. Quote-instance commitments on open formulas are deliberately
  deferred to Anson's shaping.

- **Diagonal-as-hypothesis** (R3-F03/R3-F08, user ruling option (a), round 4): Proposition 1
  enters the general-`L` interface as the class `ParametricDiagonalization`, NOT as an
  ℒₒᵣ-pinned lemma and NOT as renamed re-exports of Foundation. Rationale: the paper states
  Prop 1 as an assumption-shaped input ("Suppose S is a first-order theory capable of
  representing all computable functions, as in Section 2.4"), so every external input to
  Theorem 1 now enters uniformly via an interface class discharged by grounding; the ℒₒᵣ
  instance discharges it from `𝗜𝚺₁ ⪯ T` via Foundation's `Arithmetic.parameterized_diagonal₁`
  under Foundation's own names. Sub-decisions (documented in Diagonal.lean's header): r = 1
  only (all Theorem 1 consumes; extend, don't rewrite, if general r is ever needed — Foundation
  already has it at ℒₒᵣ); quote hypothesis is exactly
  `[Semiterm.Operator.GödelNumber L (Semisentence L 1)]`; sentence-level `⊢` only — eq 4.3's
  bounded `⊢_n` comes from `ProofMeasure.complete` at the consumption site; Skolemized
  `fixedpoint` field per Foundation's `Diagonalization` precedent. Generalizing Foundation's
  diagonal machinery beyond ℒₒᵣ upstream remains a possible later contribution.

## Intentional deviations from the paper

- **Disclosed-fallback-only, NOT adopted** (R1-F04 postscript): if Phase B's node-count
  measure fails to ground additive Property 1, a linear bound algebra (`a ↦ K·a + c`, as
  measured for bit-length) could ground a weakened interface — but that changes the paper's
  statement shapes and requires a full DISCLOSURE case plus user approval first.

## Disclosures (residual modeling substitutions)

(None approved.)

## Paper errata

- §4 Theorem 1 proof, step 1: the sentence introducing `g` states only `lg ≺ g` and
  `e(g(k)) ≺ f(k)`, but the proof immediately represents `g` inside `G[n,k]` via its
  graph, which requires `g` **computable** — the paper's own example witness is
  computable, but the stated hypothesis understates the requirement. Lean's
  `HasIntermediateWitness` carries `Computable g` explicitly. (Lens B r2 + R2-F07.)
- §4 Theorem 1 proof, eq 4.4: absorbing `g(k) + h(k) + O(lg k)` into `f(k)` needs
  `g ≺ f`, which the step-1 hypotheses (`lg ≺ g`, `e(g(k)) ≺ f(k)`) yield only if `e` is
  expansive (`k ≾ e(k)`) — but Definition 1 constrains `e` only to be "large enough" for
  Properties 3–4, which a non-expansive `e` can satisfy, breaking the absorption. Lean's
  `HasIntermediateWitness` carries `g ≺ f` as an explicit conjunct instead. (R3-F04
  cross-exam.)

## Pitfalls

- **Bit-length measure is disproved, don't retry it** (Phase 0 probe, deleted per user
  ruling R1-F04; lesson retained): under `d < 2^a` (RestrictedProvable's measure), a single
  cut combining two proofs costs ×2048 = 2^11 on the bound — 11 nested Cantor pairings in
  the 5-node glue, each pairing at bit-level u landing at 2u+2. Bit-length supports only a
  linear algebra, never the paper's additive `a+b+c`.
- Foundation encodes sequents as HFS **bitsets**: `{q}` has code `Exp.exp q`, so formula
  codes entering sequents cost exponentially in code magnitude. Any Phase B size
  instrumentation must count nodes/symbols, never code magnitude, or the blowup recurs at
  every rule application. (Corollary that cut both ways in Phase 0: `Exp.exp φ = fstIdx d ≤ d`
  gives formula-size bounds free from proof bounds under magnitude measures.)
- Foundation is built with the Lean module system: its `public import`s do NOT re-export
  Mathlib tactics — files importing only Foundation lack `ring` (add
  `import Mathlib.Tactic.Ring`); `norm_num`/`push_cast`/`omega` were available.
- Foundation's Entailment notation is inverted vs. the usual convention: `T ⊢ σ` is the
  Prop (provability) and `T ⊢! σ` is the proof *Type*. Using `⊢!` in a Prop-valued
  structure field fails with a sort mismatch.
- Quoting a proof term (`⌜b⌝`, `proof_of_quote_proof`, Bootstrapping/Syntax/Proof/
  Coding.lean) needs `[L.DecidableEq]` on top of `[L.Encodable] [L.LORDefinable]`; that
  file is the standard route from meta `b : T ⊢! φ` to internal `T.Proof (⌜b⌝ : V) ⌜φ⌝`,
  with `Sentence.coe_quote_eq_quote` moving ℕ-codes into V.
- Foundation API before re-proving exp/bitset arithmetic (R1-F09..F11): `ISigma1.exp_add`
  (Exponential/Log.lean); `insert_le_of_le_of_le` (Exponential/Bit.lean — at `le_rfl le_rfl`
  it gives `insert i s ≤ s + Exp.exp i`); `le_pair_left/right`, `exp_monotone(_le)`,
  `one_le_exp`, `lt_exp`, `exp_succ`, `exp_one`. ℕ-cast monotonicity into V is
  `exact_mod_cast`. `Exp.exp 2 = 4` / `= 8` need hand proofs, `simp` won't.
- `Theory.restrictedProvable` is **Π₁** (`.mkPi`, `T.proof.pi`); a Σ₁ bounded box is its
  dual and Foundation's `RestrictedProvable.defined` instance will not transfer.
- Sentence-level quote commutation is missing upstream; recipe `simp [Sentence.quote_eq]`;
  shared lemmas in `Critch/Infrastructure/QuoteSentence.lean`.
- Deep `refine`-chains of exponent bookkeeping leave metavariable exponents `ring` cannot
  close — state each level as an explicitly-typed `have`. Arrange V-side literal bounds so
  exponent steps are `ring`-provable equalities; `norm_num` only for literal equalities.
