# M3 completion plan — remaining property-tail nodes

> Supersedes the 2026-07-07 token-emission plan (fully executed; its record lives in
> `PROGRESS.md` under OPEN RISK 4 and the `def:ec` ledger rows, and in git history).

Written 2026-07-10 for the implementing session(s), possibly a weaker model. **Read
`CLAUDE.md` and `PROGRESS.md` first — they are the law; this file is the task list.**
Phases are ordered; each phase boundary is a safe stopping point with a green build.
Do the phases in order: A → B1 → C → B2 → D → E → F. One phase (or less) per session
is the right pace; do not start a phase you can't leave green.

## 0. Context snapshot (updated 2026-07-11 — Phases A and B1 are DONE)

> **2026-07-11 session result: Phase A (all of A1–A3) and Phase B1 landed, green,
> axiom-clean, zero new `sorry`s. Next session starts at Phase C.** What changed:
> - A1 was done *generically*: `evaln_prec` + **`PolyFueled.prec`** (closure of
>   `PolyFueled` under `Code.prec` for poly-bounded states) replace the planned bespoke
>   `subAux_evaln`-style proof; `divmodc_polyFueled`, `addc_polyFueled`, `mulc_polyFueled`,
>   `PolyFueled.addConst`, `PolyFueled.of_eq` are corollaries (`Computable.lean`). Any
>   future prec combinator (B2's option (i) offsets included) is now a few lines.
> - A2 = **`ecTok_of_blockStream`** (+ `length/getD_flatMap_const_width`); A3 =
>   `histTrader_ecTok`. Both in `Computable.lean`, end of file.
> - B1 = `Properties/NonDogmatism.lean` (`lic_nonDogmatism_weak`, trader `ndTrader`,
>   pow-chain `twoPowChain` — **left-nested** so the blocks are homogeneous width-3;
>   reuse it in B2/C) + the new engine `exploits_of_bddBelow_of_unbounded`
>   (`Properties/Basic.lean`, end of file). G3's hypothesis form used and ledgered.
> - Gates: **G1/G2/G3 still await Anson** (G2 blocks Phase E only). Ledger rows all in.

- Branch `logical-induction`, build green, exactly **two `sorry`s**, both disclosed
  (unchanged from 2026-07-10):
  - `oscillation_exploitable` — `LogicalInduction/Properties/Convergence.lean:62`
  - `LUV.expect_converges` (`thm:ec`) — `LogicalInduction/Expectations.lean:83`
- **Done in M3:** `thm:provind` (fixed-φ and 𝓔𝓒-sequence forms), all three `thm:lc`
  bullets, `thm:lex` (both directions), the `thm:con` reduction
  (`exists_rat_oscillation_of_not_convergesTo`), the LUV bridge object (`def:luv`,
  `def:e`), the integration test, and the entire e.c. pipeline: the token-indexed
  `def:ec` (`EfficientlyComputableTok`, wired into `IsLogicalInductor`), all seven
  traders re-certified, and the varying-length emission toolkit
  (`ifzSel`/`predc`/`subc`/`ecTok_of_tokenFn`, validated by `deepTrader_ecTok`).
- **Remaining in M3 (roadmap §4):** the `thm:con` arbitrage trader; `thm:nd`; the
  expectation family (`thm:ec`, `thm:loe`, `thm:ei`, `thm:expprovind`) + LUV approx
  lemmas; Self-Trust (`thm:cee`/`ceu`/`ccee`/`st`); the M3-exit audit package.
- No remaining trust-surface blockers: what's left is **construction and analysis**,
  plus two modeling decisions that go to Anson (§1).

## 1. Decision gates for Anson (surface early, don't guess)

Raise these in your first report; only **G2** blocks work (and only Phase E).

- **G1 — the M3/M4 boundary for the expectation family.** The paper proves `thm:ec`
  via `thm:exppolymax`, and `thm:loe`/`thm:expprovind` via the affine machinery
  (`thm:affpolymax`, `alta`, softmax traders) — all of which the roadmap places in
  **M4** (the lift hubs). Proving them ad hoc inside M3 would duplicate M4's work.
  **Recommendation:** M3 closes with `thm:con` + `thm:nd` proved, `thm:ec` proved via
  the direct bundle-hysteresis route (Phase D2, attempted after C), and
  `loe`/`ei`/`expprovind` **stated faithfully** with proofs assigned to M4. This plan
  is written to that recommendation; if Anson wants full M3 proofs instead, M4's hub
  (`thm:affpolymax`) must be pulled forward first — a different, larger plan.
- **G2 — Self-Trust reflection modeling.** `thm:cee`/`ceu`/`ccee`/`st` quantify over
  *quoted* sentences (`⌜𝔼_{f(n)}(X_n)⌝`, `⌜P_{f(n)}(φ_n)⌝`) — first-order reflection
  our propositional `Sentence` cannot express. Phase E proposes the modeling
  (reflection as explicit payout hypotheses); **statements need Anson's sign-off
  before any proof effort**, since they are pure trust surface.
- **G3 — hypothesis form for `thm:nd`.** The paper's `Θ ⊬ ¬φ` becomes, in our
  semantic substrate, "φ-satisfying plausible worlds keep existing":
  `∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ`. This is the honest
  per-day form (weaker than one world consistent forever, hence a *stronger* theorem).
  Phase B uses it; flag it in the ledger as the `def:lang`-level rendering of `⊬` and
  let Anson veto at read-through.

## 2. API cheat sheet (verified anchors — do not re-derive, do not invent)

| What | Where |
|---|---|
| `EF` syntax + `serialize` (postfix tags 0–5; trades add `[6, ⌜φ⌝]`) | `Criterion.lean:47`, `:301`, `:408` |
| `EfficientlyComputableTok` (the `def:ec` in force) | `Criterion.lean:609` |
| `IsLogicalInductor` | `Criterion.lean:623` |
| `Trader.netWorth` = `∑_{i≤n}` of `Strategy.value` = `∑ e(V)·(w φ − Vᵢ φ)` | `Criterion.lean:515`, `:534` |
| `PolyFueled` (+`const/id/pair/succ_comp/left/right/comp`) | `Computable.lean:172`–`618` |
| Arithmetic codes: `predc`, `ifzSel`, `subc` (all poly-fueled) | `Computable.lean:306`, `:631`, `:919` |
| **`ecTok_of_tokenFn`** — varying-length e.c. workhorse | `Computable.lean:1022` |
| Worked deep-trader example: `deepTrader_ecTok` | `Computable.lean:1138` |
| Fixed-length e.c.: `ecTok_of_stream` + `PolyTokenStream` combinators | `Computable.lean:809`–`908` |
| Exploitation engines (`=` and `≥` partial-sums forms) | `Properties/Basic.lean:85`, `:122` |
| `buySignal` clipped-signal template + `PCWorld.holds_*` | `Properties/Basic.lean:28`–`72` |
| `thm:con` reduction + `sorry` + chain | `Properties/Convergence.lean:17`, `:62`, `:78` |
| LUV + `expectApprox`/`expect`/`expectSeq`, `thm:ec` `sorry` | `Expectations.lean:33`–`92` |
| Paper: `thm:nd` 1528 (sketch below it) · `thm:ec` 1688 · `thm:loe` 1700 · `thm:ei` 1719 · `thm:expprovind` 1753 · `cee/ceu/ccee/st` 2045–2092 · `def:ctsind` 1174 · `def:deferralfunc` 1240 · approx lemmas 4982/5015/5111 | `notes/1609.03543v5-main.tex` |

Recurring `EF` idioms (no new constructors exist; build from these):
`x − y` = `add x (mul (const (-1)) y)`; `min x y` = `mul (const (-1)) (max (−x) (−y))`;
the paper's continuous indicator `ctsind_δ(x < c)` = `max 0 (min 1 ((c − x)·(1/δ)))`
with δ a **rational constant** (so `1/δ` is `const`; never divide by a feature —
`safeRecip` is `1/max(1,·)` and is useless below 1).

## 3. Phase A — emission tooling: `divmodc` + repeating-block streams

**Why.** Every remaining trader is *deep*: its day-`n` feature scans history, so its
token stream is `head ++ block(0) ++ block(1) ++ … ++ block(k) ++ tail` with
fixed-width blocks, where `block(j)` contains the day index `j` (a `price φ j` node
serializes to `[0, ⌜φ⌝, j]`). To emit token `i` you must compute the block index and
offset — **division/remainder by a constant width `w`**, which the toolkit does not
yet have (`deepTrader`'s blocks were width 1). This is the one genuinely new fuel
proof; everything after it is mechanical.

- **A1 — `divmodc`.** One `Code.prec` recursion on `i` whose state is
  `Nat.pair q r` (quotient, remainder): step = "if `r+1 = w` then `pair (q+1) 0` else
  `pair q (r+1)`". Equality-with-constant tests via `subc` both ways
  (`a = w` iff `(a−w)+(w−a) = 0`) fed to `ifzSel`. Model the fuel proof on
  `subAux_evaln` (`Computable.lean:949`) — it is the same shape (nested prec: the
  step applies `subc`/`ifzSel`, themselves prec), one nesting level deeper. Deliver
  `divmodc_polyFueled : PolyFueled divmodc (fun m => Nat.pair (m.unpair.1 / m.unpair.2 …))`
  — fix the exact input convention yourself (constant `w` may be baked into the code
  per-width, like `Code.const`; that is simpler than taking `w` as input and is all
  we need). **Budget: this is the phase's hard part.** If the fuel accounting won't
  close after ~2 serious attempts, `sorry` it with `-- TODO(blueprint:def:ec): need
  poly fuel bound for divmodc`, report, and continue — downstream work stays honest
  (economics don't depend on it).
- **A2 — the block-emission workhorse.** Prove once, in `Computable.lean`:
  a trader whose day-`n` stream is `head n ++ (List.range (cnt n)).flatMap (body n)
  ++ tail n` — `head`/`tail` fixed-length lists of poly-fueled tokens, `body n j` a
  fixed-width-`w` list of poly-fueled tokens of `⟨n,j⟩`, `cnt` poly — is
  `EfficientlyComputableTok`. Proof: assemble `tokenFn` from `subc` (region tests),
  `divmodc` (block index/offset), `ifzSel` (dispatch), then apply `ecTok_of_tokenFn`.
  Follow `deepTrader_ecTok`'s assembly style and `deepStream_getD`'s region-case
  lemma style. Get the statement shape right by *first* writing A3's example and
  generalizing from it — don't design the helper in the abstract.
- **A3 — validation.** A worked size-Θ(n) example whose blocks contain the day
  index: e.g. `histSum φ n = Σ_{k<n} price φ k` (left-nested adds; stream =
  `[0,⌜φ⌝,0] ++ ([0,⌜φ⌝,k,2] blocks)`), a trader trading it, certified via A2.
  This is the direct dress rehearsal for B and C's emissions.

**Done when:** A1–A3 green, `#print axioms` clean, ledger rows
(`dd:fuel (divmodc)`, `def:ec (block workhorse)`) in the same commits.

## 4. Phase B1 — `thm:nd`, weak fragment (first real deep trader)

Easiest economics of the remaining nodes; exercises Phase A end-to-end.

- **Statement** (new file `Properties/NonDogmatism.lean`):
  under `[IsLogicalInductor P DP]`, prices in `[0,1]`, and G3's hypothesis
  `hφ : ∀ n, ∃ v, v.ConsistentWith (DP.D n) ∧ v.Holds φ`:
  `∀ᶠ n in atTop, 2^(-(n+2) : ℤ) ≤ P n φ`. Ledger as `thm:nd (weak fragment)`,
  kind `C` — it is honestly *weaker* than `thm:nd` (the bound decays); B2 is the
  real node.
- **Trader** (memoryless): day-`n` buy signal `β n = max 0 (1 − 2^(n+1)·(price φ n))`
  shares of φ. The power `2^(n+1)` is a right-nested `mul`-chain of `const 2` —
  size Θ(n), constant-content width-2 blocks + a run of `[3]` tags: A2 emits it.
  Spend on day `n` is `β·P ≤ 2^(-(n+1))` (signal support is `P < 2^(-(n+1))`), so
  total spend ≤ 1.
- **New engine** (in `Properties/Basic.lean`): the existing engines force
  world-*independent* growth; here growth happens only in φ-worlds. Add the
  definitional one:
  `exploits_of_bddBelow_of_unbounded (h1 : ∀ x ∈ Tr.plausibleAssessments P DP, −C ≤ x)`
  `(h2 : ∀ B, ∃ x ∈ Tr.plausibleAssessments P DP, B < x) : Tr.Exploits P DP` —
  a few lines from `Exploits`' definition (`BddBelow ∧ ¬BddAbove`). Kind `P`.
- **Economics.** BddBelow: in any plausible world, `netWorth = Σ βᵢ(w φ − Pᵢ) ≥
  −Σ βᵢPᵢ ≥ −1`. Unbounded: if `P n φ < 2^(-(n+2))` frequently, then `β n ≥ 1/2`
  frequently, and in the day-`n` φ-world from `hφ` every term `βᵢ(1 − Pᵢ)` is ≥ 0
  with the triggered terms ≥ 1/4 — accumulate along the frequent subsequence
  (imitate `buyDaily_exploits_freq`, `Properties/ProvabilityInduction.lean:118`).
  Conclude by contradiction with `IsLogicalInductor`.

## 5. Phase C — `oscillation_exploitable`: the `thm:con` hysteresis trader

The hardest single item and the highest-value one (it un-`sorry`s
`lic_price_convergesTo`, and `P∞` then exists for B2/D). Everything is in place:
the statement is fixed (`Properties/Convergence.lean:62` — do not weaken it), the
e.c. tooling is Phase A, the target engine is B1's. Given: rationals `a < b`,
`P n φ < a` frequently, `b < P n φ` frequently, plausible worlds daily.

- **C1 — the state feature.** Fix `δ := (b−a)/4` (rational ⇒ `const`s). Signals:
  `buyInd n = ctsind` supported **inside the gap**: `1` when `P ≤ a`, `0` when
  `P ≥ a+δ` (i.e. `max 0 (min 1 ((a+δ − price φ n)·(1/δ)))`); `sellInd n`: `1` when
  `P ≥ b`, `0` when `P ≤ b−δ`. Holdings state, recursively:
  `H 0 = buyInd 0`, `H (n+1) = max (buyInd (n+1)) (H n · (1 − sellInd (n+1)))`.
  Each day adds a constant number of nodes wrapping `H n` ⇒ size Θ(n), rank ≤ n,
  block-structured stream (A2 emits; the day-`n` trade coefficient is the EF
  `H n − H (n−1)`, with the day-0 case just `H 0`).
- **C2 — the accounting (the genuine analysis).** Denote by `h i ∈ [0,1]` the real
  value `(H i).denote P` and `Δᵢ = h i − h (i−1)` (with `Δ₀ = h 0`). Key pointwise
  facts, straight from the `max`/`ctsind` shapes:
  1. `Δᵢ > 0 → P i φ < a + δ` (buys only while `buyInd > 0`);
  2. `Δᵢ < 0 → P i φ > b − δ` (sells only while `sellInd > 0`);
  3. `P i φ < a → h i = 1` (full buy); `P i φ > b → h i = 0` (full sell).
  Then **decompose by sign** — no per-swing induction needed. With
  `B₊ = Σ_{i≤n} max Δᵢ 0` and `B₋ = Σ_{i≤n} max (−Δᵢ) 0` (so `B₊ − B₋ = h n`):
  `netWorth = Σ Δᵢ(w φ − Pᵢ) = (w φ)·h n − Σ ΔᵢPᵢ ≥ −Σ ΔᵢPᵢ`
  `≥ −(a+δ)B₊ + (b−δ)B₋ = (b−a−2δ)·B₋ − (a+δ)·h n ≥ ((b−a)/2)·B₋ − (a+δ)`.
  So plausible-world net worth ≥ `((b−a)/2)·B₋ − 1` **in every world** — BddBelow is
  immediate, and unboundedness reduces to `B₋ → ∞`.
- **C3 — `B₋ → ∞`.** From the two frequency hypotheses extract an interleaved
  sequence `n₁ < m₁ < n₂ < m₂ < …` with `P n_j φ < a` and `P m_j φ > b` (standard
  double-`extraction_of_frequently_atTop` argument). By fact 3, `h n_j = 1` and
  `h m_j = 0`, so on `(n_j, m_j]` the negative variation is ≥ 1: `B₋(m_j) ≥ j`.
  Feed C2+C3 to B1's engine; close `oscillation_exploitable`; verify
  `lic_price_convergesTo` and its downstreams drop `sorryAx` from `#print axioms`.
- **C4 — e.c.** Mechanical: write `serialize (H n)` in A2's block shape (a
  `serialize_H` lemma by induction, like `serialize_srChain`), apply the workhorse.
- **Guardrail:** C2's inequality chain is where a session can thrash. The
  decomposition above is believed correct but **re-derive it, don't transcribe it**;
  if the pointwise facts 1–2 resist your exact `ctsind` encoding after ~2 serious
  attempts, adjust the *encoding* (band placement), not the statement. A session
  that lands only C1+C2 (with C3/C4 `sorry`+TODO) is a success — commit it.

## 6. Phase B2 — full `thm:nd` (budget-halving trader)

Needs C for nothing *logically*, but do it after C — the limit-form statement wants
`P∞` and the proof reuses C's state-feature techniques.

- **Statement:** under `[IsLogicalInductor]`, prices in `[0,1]`, G3's hypothesis for
  φ ⇒ `∃ ε > 0, ∀ᶠ n, ε ≤ P n φ` (liminf form; with `thm:con`, `P∞ φ > 0` as a
  corollary — state that too, with the convergence as an explicit hypothesis, like
  `lic_limit_additive`, `Properties/Coherence.lean:337`). Dual (`Θ ⊬ φ` ⇒
  `P∞ φ < 1`): apply the first form to `∼φ`? **No** — prices of `φ` and `∼φ` are not
  linked without coherence; instead run the mirrored *sell* trader (imitate
  `sellDaily` vs `buyDaily`). Ledger `thm:nd`, kind `C`.
- **Trader (paper's sketch, rendered without dividing by a feature):** carry the
  **remaining budget** `r` as the state: `r 0 = const 1`,
  `β n = max 0 (min 1 ((r n / 2 − price φ n)·2^(n+2)))` (the `2^(n+2)` is B1's
  pow-chain — a *fixed* sharpening schedule, avoiding `1/r`),
  `r (n+1) = r n − β n·(price φ n)`. Buys `β n` shares. Support of `β n` is
  `P < (r n)/2`, so `r` never drops below half its previous positive value:
  after `m` full purchases `r ≥ 2^(−m)`, total spend `≤ 1`.
- **Economics:** BddBelow by −1 as in B1. If `liminf P n φ = 0`: show by induction
  on `m` that infinitely many *full* (`β = 1`) purchases occur — having made `m`,
  `r ≥ 2^(−m)`, and eventually `2^(−(n+2)) < 2^(−(m+3))` while `P` dips below
  `2^(−(m+3)) ≤ r/4` frequently, forcing a full trigger. Each full purchase adds
  `≥ 1 − P ≥ 1/2` of φ-world value; accumulate via B1's engine. Conclude
  `¬(liminf = 0)`, i.e. the ε exists (`Filter.liminf` API, or elementarily:
  `¬∃ε` gives the frequent dips directly — prefer the elementary route, matching
  the codebase's style).
- **e.c.:** `r n` is again a constant-nodes-per-day recursive EF ⇒ A2.
  Size note: `β n` contains the Θ(n) pow-chain *and* `r n` contains all past `β`s ⇒
  `size (r n) = Θ(n²)`. **Fine** — poly-size is all `def:ec` asks; but the A2 block
  widths are now day-dependent (block `j` embeds a Θ(j) pow-chain), so A2's
  fixed-width form does not apply directly. Two options, pick at implementation
  time: (i) generalize A2 to affinely-growing block widths (offset of block `j` is
  a quadratic in `j` — still poly-fueled arithmetic via `divmodc`-style search, but
  a real generalization); (ii) restructure: replace the pow-chain sharpening with
  the constant-width trick of tracking `s n = 2^(n+2)·(r n)/2` … — **do not decide
  in advance**; try (i), stop-and-report if it balloons. An honest B2 with the
  economics proved and the e.c. cert `sorry`+TODO is committable progress —
  Rule 1 cuts the other way here (the *trader* is real; only its cert is pending),
  but say so loudly in the ledger row.

## 7. Phase D — expectation family (statements + what's provable without M4)

- **D1 — `lem:conluvapprox`, single-LUV form** (in `Expectations.lean`). Model a
  world's LUV value: `def PCWorld.ValuesAt (v) (X : LUV) (x : ℝ) : Prop :=`
  `x ∈ Icc 0 1 ∧ ∀ r : ℚ, ((r:ℝ) < x → v.Holds (X.gt r)) ∧ (x < r → ¬ v.Holds (X.gt r))`
  (the threshold-coherence rendering of the paper's "Θ represents computations";
  disclosed type-`(c)`, ledger it). Prove: `ValuesAt v X x →`
  `|X.expectApprox (fun s => v.payout s) n − x| ≤ 1/n` — pure counting
  (`#{i < n : i/n < x}` vs `n·x`, floor arithmetic; `Nat.floor` API). Kind `P`.
  The combination (`b/n`) form waits for M4's affine layer.
- **D2 — `thm:ec` via bundle hysteresis** (only after C is green). Route:
  1. Generalize `exists_rat_oscillation_of_not_convergesTo` to an arbitrary
     `u : ℕ → ℝ` with `u ∈ [0,1]` (the proof already is that general — refactor,
     keep the φ-specialization as a corollary), apply to `expectSeq P X`.
  2. The exploiter trades the **day-`n` threshold bundle** `{(1/n)·gt(i/n)}_{i<n}`
     with C's hysteresis state driven by the *expectation* value — note
     `expect P n X` is an EF-expressible function of prices (a rational-coefficient
     sum of `price` nodes), so the signals are EFs; the bundle trade list has
     length `n` (growing trade lists are fine — `serializeTrades` handles any list;
     emission is A2-shaped with the D-block caveat of B2).
  3. New wrinkle vs C: bought day-`n` bundles are sold as day-`m` bundles; in any
     world satisfying `ValuesAt v X x` (add D1's hypothesis for plausible worlds:
     `hval : ∀ n v, v.ConsistentWith (DP.D n) → ∃ x, v.ValuesAt X x`), the two
     bundles' payouts differ by ≤ `1/n + 1/m` (D1), so late swings still bank
     ≥ `(b−a)/2 − small` — thread an `n₀` cutoff through C3's extraction.
  This is C's proof again with bookkeeping, not new ideas — but it is real work.
  **Permission to stop-and-report** after a serious attempt; `thm:ec` staying
  `sorry` with C landed is still a strong M3.
- **D3 — statements only** (kind `stmt` ledger rows, proofs → M4 per G1):
  - `thm:ei` (**relational form — do not construct a canonical indicator**):
    define
    `def LUV.IsIndicator (Y : LUV) (φ : Sentence) (DP : DeductiveProcess) : Prop :=`
    `∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∀ r : ℚ,`
    `(r < 0 → v.Holds (Y.gt r)) ∧ (0 ≤ r → r < 1 → (v.Holds (Y.gt r) ↔ v.Holds φ))`
    `∧ (1 ≤ r → ¬ v.Holds (Y.gt r))`
    and state: `IsIndicator Y φ DP → AsympEq (Y.expectSeq P) (fun n => P n φ)`.
    **Why relational:** the tempting canonical construction (`gt r := φ` on
    `[0,1)`) makes `𝔼ₙ(indicator φ) = Pₙ φ` *definitionally* — the theorem
    evaporates. That collapse is a modeling artifact: the paper's `1(φ)`
    thresholds are *distinct sentences provably linked* to `φ`, and `thm:ei`'s
    content is the inductor learning that growing bundle of equivalences
    uniformly. Quantifying over any linked family `Y` restores exactly that
    content — and note per-threshold `thm:lex` does **not** suffice (the
    threshold set grows with `n`; it needs a bundle trader, D2's shape). So:
    state now, `sorry` with TODO(M4/D2 engine), ledger `stmt` with this
    rationale. **General principle for Phases D and E:** paper-side LUV
    *constructions* (indicators, sums `aX+bY`, quoted expectations) enter our
    modeling as **relational predicates over arbitrary threshold families**,
    never as canonical `LUV` values — constructing a representative silently
    pre-discharges the learning content.
  - `thm:loe`: state with world-level hypotheses replacing `Θ ⊢ Z = aX + bY`:
    `∀ n v (h : v.ConsistentWith (DP.D n)) x y z, v.ValuesAt X x → v.ValuesAt Y y →`
    `v.ValuesAt Z z → z = a·x + b·y` ⇒ `AsympEq (a·𝔼(X) + b·𝔼(Y)) (𝔼(Z))`
    (fixed X,Y,Z first; the 𝓔𝓒-sequence form is the M4 target). `sorry`, TODO(M4).
  - `thm:expprovind`, single-LUV form: `(∀ n v, ConsistentWith → ValuesAt … ≥ b)`
    ⇒ `AsympGE (expectSeq P X) b`-style. `sorry`, TODO(M4).
  Keep every statement short and paper-checked against the anchors in §2.

## 8. Phase E — Self-Trust statements (gate G2 first)

Statements only; **do not start proofs in M3.** Propose to Anson:

- `structure DeferralFunction` — `f : ℕ → ℕ`, `n ≤ f n`, monotone(?) — check the
  paper's `def:deferralfunc` (`main.tex:1240`) for the exact conditions; carry only
  those.
- Reflection rendered as payout hypotheses (the propositional substitute for
  quoting), e.g. for `thm:ceu`: given `φ : ℕ → Sentence`, `f : DeferralFunction`,
  and a family `Y : ℕ → LUV` with
  `hrefl : ∀ n v, v.ConsistentWith (DP.D n) → v.ValuesAt (Y n) (P (f n) (φ n))`
  ("`Y n` is the LUV ⌜P_{f n}(φ n)⌝: every plausible world values it at the actual
  future price"), conclude `AsympEq (fun n => P n (φ n)) (fun n => expect P n (Y n))`.
  State `cee` (LUV version: `X : ℕ → LUV`, `Y n` reflects `expect P (f n) (X n)`),
  `ccee` (adds the `w`-weighting — needs a product-LUV modeling note), `st`
  (adds the `ctsind` conditioning) the same way. Mind the roadmap's naming caution:
  deference "cee" = paper `thm:ceu`.
- **Two sub-decisions inside G2 — flag both explicitly:**
  1. *Timing.* The sample `hrefl` above makes day-`n` plausible worlds already
     value `Y n` at the day-`f n` price. The paper only guarantees the linkage
     facts are revealed by the deductive process *eventually* (Θ proves them;
     they enter `D` at some finite day, not necessarily by day `n`). The strong
     by-day-`n` form is simpler and may serve the deference corpus; the faithful
     form carries an explicit revelation-schedule hypothesis. Anson picks.
  2. *Non-vacuity.* In the paper the quoted sentences **exist** because `P` is a
     computable rational-valued market and `Θ` represents computations. Our
     substrate has neither (`History` is arbitrary `ℝ`-valued; `DeductiveProcess`
     carries no computability — both disclosed type-`(c)`s), so the linkage
     hypothesis is where that entire mechanism is imported. It *is* satisfiable —
     take fresh atoms per `(n, q)` and a `DP` revealing the true threshold
     literals — but that witness is an oracle-like `DP` that "knows" the future
     market: exactly the **degenerate non-vacuity** the audit protocol hunts.
     The principled discharge is M7's construction, where `P` is the computable
     `LIA` and the reflective `DP` is built, not conjured. Write both facts into
     the ledger rows at statement time.
- Ledger all four as `stmt`, provenance noting the reflection hypothesis is a
  disclosed type-`(c)` substitute for first-order quoting, awaiting G2 sign-off.
  If a statement fights the types, **that is a finding** — write it up, don't force.

## 9. Phase F — M3 exit package

1. Ledger sweep: every row's status/kind/provenance current; the two old `sorry`s'
   rows updated (hopefully to `done`); milestone table row for M3 updated with an
   honest inventory: proved / stated-only / moved-to-M4 (per G1).
2. Statement inventory for Anson's read-through: append to `PROGRESS.md` a flat
   list — every M3 top-level theorem + `file:line` + one-line gloss. Definitions
   too (`ValuesAt`, `indicator`, `DeferralFunction`, the reflection hypotheses).
3. Re-run the integration test file; confirm the deference-corpus hypotheses that
   are now discharge-able actually discharge (`thm:con` should let you strengthen
   Part C — check).
4. Remind Anson to launch the **fresh-context adversarial audit** (CLAUDE.md §audit;
   it must not be run by the session that wrote the proofs). Hand it the §2 table
   and the inventory from item 2. Known audit bait to hand over explicitly:
   the relational `IsIndicator`/`ValuesAt` modeling (D1/D3 — check the linkage
   hypotheses aren't conclusion-shaped), the Self-Trust reflection hypotheses and
   their oracle-`DP` degenerate witness (E), G3's rendering of `⊬`, and any
   engine whose hypotheses were tailored to one trader.

## 10. Standing guardrails (unchanged; the failure modes this plan is designed against)

1. **Never invent a Mathlib/Foundation name.** `rg` `.lake/packages` or `#check`
   before first use; missing ⇒ `sorry` + `-- TODO(blueprint:LABEL): need <stmt>`.
2. **Green at every commit;** small commits; `lake build LogicalInduction.<Module>`
   to iterate, full `lake build` before committing.
3. **Every new theorem ships with its ledger row in the same commit**, kind and
   provenance filled at proof time.
4. **`#print axioms` every new theorem in-file** (copy the existing idiom).
5. **No arithmetic stub may stand in for a trader** (Rule 1). A `sorry` on a
   construction is honest; a fake trader is the one unforgivable move.
6. **Don't touch:** `Construction/Brouwer.lean` interior, `Barasz/`, `lakefile.lean`,
   `lean-toolchain`, `lake-manifest.json`, the Foundation pin. Never `lake update`;
   never the `import Mathlib` umbrella.
7. **Don't redefine limit vocabulary** — `Asymptotics.lean` owns it (`dd:asymp`).
8. **Stop-and-report is a success.** ~2 serious attempts, then write up what fails
   (imitate the `oscillation_exploitable` docstring) and move on.
9. ProofWidgets "failed to reuse pre-built JS" ⇒ `cd .lake/packages/proofwidgets
   && lake build` once.
10. Use the `lean4-theorem-proving` skill. Commits: no AI co-authorship lines;
    push to `origin` freely, nowhere else.
