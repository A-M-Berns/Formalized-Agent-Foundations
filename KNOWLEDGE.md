# Formalization Knowledge — Parametric Bounded Löb (Critch 2019), branch `critch-pbl`

Permanent, curated facts about this formalization. Committed with the code; read by every
harness agent before working. Add an entry only if a future fresh-context agent would act
differently for knowing it. One bullet per fact, newest last. Cross-reference finding IDs
(RN-Fxx) where an entry originated from an audit. Paper: `notes/critch2019.pdf`.
Project plan: `notes/critch-pbl-roadmap.md` — its four standing scope decisions are binding.

## Correspondence table

| Paper (§/symbol) | Lean name | Notes |
|---|---|---|
| §3.1 `BBew[m,n,k]` / `□ₖ` | `BoundedProvability.bbew : Semisentence L₀ 2` | var 0 = bound (object-level), var 1 = formula code; helpers `prt` (bound term) / `pr` (numeral) |
| §3.1 Eval₁ extension | `bbew₁` + class `BEvalSpec` | box over a 1-free-variable formula; what Theorem 1's parametric formula consumes |
| §2/§4 `⊢ₖ` judgment | `ProofMeasure` (fields `Pf sound complete mono`) | abstract bounded-proof judgment; concrete measure is Phase B |
| §3.2 Property 1 | class `BImpDistr` | ONE internal theorem, `(∀a)(∀b)` inside the turnstile, object-level `a+b+c` (R1-F02) |
| §3.2 Property 2 | class `BQuantDistr` | abstract computable ν via graph formula `νGraph` (§2.4 desugaring); no `lg` (R1-F05) |
| §4 Definition 1 + Properties 3–4 | class `BExpansion` | ONE computable `e` serving both properties; P3 has bounded premise + `e(k)` outer bound (R1-F03/F06) |
| bundle | `BHBL` | extends the five classes |
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

## Intentional deviations from the paper

- **Disclosed-fallback-only, NOT adopted** (R1-F04 postscript): if Phase B's node-count
  measure fails to ground additive Property 1, a linear bound algebra (`a ↦ K·a + c`, as
  measured for bit-length) could ground a weakened interface — but that changes the paper's
  statement shapes and requires a full DISCLOSURE case plus user approval first.

## Disclosures (residual modeling substitutions)

(None approved.)

## Paper errata

(None found.)

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
