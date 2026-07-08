# PROGRESS — Logical Induction formalization

The ledger. Maps `blueprint label → Lean decl → status → kind → provenance`. Status:
`stmt` (statement only) · `sorry` (stated, proof deferred) · `done`. **Kind:** `Def` ·
`P` proved · `C` composition · `S` squeeze-over-named (flag + justify) · `T` trivial stub
· `N±` non-vacuity witness. **Provenance** (per hypothesis): `(a)` derived in-project ·
`(b)` Foundation/Mathlib citation · `(c)` modeling substitution (disclose or eliminate).

Rule: a new theorem is not committed without its ledger row, in the same commit. Fill
kind/provenance honestly as you go — they are the anti-self-deception mechanism, not
post-hoc bookkeeping.

## Pinned versions

| Component | Pin |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.28.0-rc1` |
| Foundation | **fork** `A-M-Berns/Foundation@aada66e` (= upstream `83d98a36` + three `Matrix.*`→`vec*` renames: `map`, `forall_iff`, `exists_iff`; see OPEN RISK 1; upstreamed as PR #835) |
| Mathlib | as resolved transitively by Foundation (see `lake-manifest.json`) |

Both Mathlib and Foundation are precompiled and build under this toolchain (Foundation
already `require`s mathlib). With the Foundation fork (OPEN RISK 1, resolved) they now
co-build across the full stack, including Bochner integration and matrix-heavy analysis.

Environment note: a stale ProofWidgets JS trace blocked all Mathlib builds with
"ProofWidgets failed to reuse pre-built JS code". Fixed by building ProofWidgets' JS
locally from its own package (`cd .lake/packages/proofwidgets && lake build`; npm is
available), which sidesteps Mathlib's `errorOnBuild` guard. Re-run if it recurs.

## Milestone status

| M | Scope | Status |
|---|---|---|
| M0 | Project stands up; namespace/file scaffold; substrate verified | **done** (pending Anson's statement read-through) — scaffold, `Scratchpad`, `Asymptotics` content all green |
| M1 | `def:tf` keystone + `def:lang` + criterion defs | **done** (pending Anson's statement read-through) — keystone + all Part-I criterion defs stated & green; one **provisional type-`(c)`** in `EfficientlyComputable` |
| M2 | Engine + one e.c.-certified exploiting trader, end-to-end | **done** (pending read-through) — the loop is wired **completely and with no `sorry`**: real trader, e.c. discharged via the faithful clocked-interpreter model, exploitation proved, criterion invoked. Engine `def:tradermag`/`def:roi` defined. **`EfficientlyComputable` reconciled to the paper's poly-time `def:ec`** (OPEN RISK 3 resolved) |
| M3 | Downstream property slice + LUV bridge + integration test | **in progress (Convergence/Coherence + Timely-Learning slice largely done)** — **proved & axiom-clean:** `thm:provind` (fixed φ `→1` **and** `𝓔𝓒`-sequence form), all three **`thm:lc`** bullets (provable`→1`, disprovable`→0`, finite additivity + limit identity), **`thm:lex`** (logical equivalence `Pφ−Pψ→0` and implication/price-monotonicity `Pφ≤Pψ+ε`), the `thm:con` **reduction** (non-conv ⇒ rational oscillation). LUV/expectation bridge + integration test done. **New reusable infra:** prec-fueled `pred` (`PolyEF.pricePred`) resolving the multi-day-trader e.c. gap; `ec_of_polyEF_seq` (varying-sentence e.c.); multi-trade `Nat.pair`-tree list-encoding e.c.; world-neutral & world-dependent portfolio patterns; two exploitation engines (`exploits_of_nonneg/ge_partialSums`). **Remaining:** the `thm:con` full arbitrage trader (needs **hysteresis** — memoryless sketch retracted; e.c. ingredient now in place), the expectation family (`thm:ec/loe/ei/expprovind` — needs `thm:con` or LUV-approx infra), `thm:nd`, Self-Trust. Two disclosed `sorry`s (`thm:ec`, `oscillation_exploitable`). |
| M4–M7 | see roadmap | not started (Brouwer `lem:fpl` already proved — M6 gate cleared) |

**Update (2026-07-08):** **OPEN RISK 4 resolved** — `def:ec` redefined to the faithful poly-*size*,
token-indexed `EfficientlyComputableTok`; `IsLogicalInductor` switched to it; all seven traders
re-certified; build green, sorry count unchanged (still just `oscillation_exploitable`,
`thm:ec`). The remaining M3 nodes that were gated on this (`thm:con` trader, `thm:nd`, expectation
family) are now **unblocked** — they need *construction*, no longer a trust-surface decision.

Out-of-sequence: `brouwer_fixed_point` (the M6 gate) is already **proved**, not axiomatized;
and the faithful poly-time `def:ec` with a working responsive-trader certification pipeline
(the other multi-week risk) is **done** — the two hardest foundational items are behind us.

## Node ledger

| Label | Lean decl | Status | Kind | Provenance / notes |
|---|---|---|---|---|
| (scaffold) | `LogicalInduction.*` module skeleton | stmt | — | Parts I–IV + Asymptotics; all elaborate |
| `dd:asymp` | `AsympEq`/`AsympLE`/`AsympGE` (`≈ₙ`/`≲ₙ`/`≳ₙ`), `EventuallyWithin`, `ConvergesTo` | done | Def | thin defs over `Tendsto (·−·) atTop (𝓝 0)` / `∀ᶠ n in atTop` `(b)` |
| `dd:asymp` API | `asympEq_iff_eventuallyWithin`, `AsympEq.refl/symm/trans`, `AsympEq.asympLE/asympGE`, `AsympLE.trans`, `AsympLE.trans_asympEq`, `AsympEq.finsetSum`, `asympEq_iff_asympLE_asympGE`, `convergesTo_iff_asympEq_const` | done | P | all hypotheses `(b)`; no sorries. `AsympLE.trans`/`trans_asympEq`/`finsetSum` added to match the deference corpus's `DeferenceAsymp` combinators (integration test) |
| `def:lang` | `Sentence` (`Foundations.lean`) | done | Def | reducible `abbrev` over `LO.Propositional.Formula ℕ` `(b)`; `DecidableEq`+`Encodable` transfer for free (`example` witnesses in-file) |
| `def:market` (substrate) | `Valuation`, `History` (`Foundations.lean`) | done | Def | `Valuation := Sentence → ℝ`, `History := ℕ → Valuation`. Type-`(c)` disclosures: codomain `ℝ` not `[0,1]` (constraint imposed downstream); days indexed from `0` not `ℕ⁺` (uniform convention). Full `def:market`/`def:world`/`def:pricing` structures still TODO |
| `def:world`+p.c. | `PCWorld`, `.Holds`, `.payout`, `.ConsistentWith` | done | Def | p.c. world = Foundation Boolean model (`Formula.Boolean.val` over `ℕ → Prop`) `(b)`; `payout` the `{0,1}` share value (classical `if`) |
| `def:dedproc` | `DeductiveProcess` (`D : ℕ → Finset Sentence`, `mono`) | done | Def | type-`(c)`: computability of `D` not carried in the type (re-enters in Part IV); disclosed |
| `def:tradestrat` | `Strategy n` (`trades`, `rank_le`), `.value`, `.cost` | done | Def | paper's canonical `(eᵢ,φᵢ)` encoding; `value = Σ eᵢ(𝓥)·(w φᵢ − 𝓥ₙ φᵢ)` |
| `def:trader` | `Trader` (`strat`), `.netWorth`, `.plausibleAssessments` | done | Def | sequence of `n`-strategies; net worth `∑_{i≤n}` day-`i` values |
| `def:exploitation` | `Trader.Exploits` | done | Def | `BddBelow ∧ ¬BddAbove` of plausible assessments — quantifiers per paper `(b)` |
| `def:exploitation` (non-vac) | `Trader.zero_not_exploits` | done | **N+** | do-nothing trader (netWorth ≡ 0) does not exploit → `Exploits` is refutable, criterion non-vacuous |
| `def:lang` (codes) | `EF.toNat`/`ofNatAux`/`ofNat`, `Encodable EF` | done | **P** | hand-built **computable** encoding (no `deriving`), **`Nat.pair`-tagged (no multiplication)** so the strategy-encoding function is `Nat.Partrec.Code`-primitive-friendly (`pair`/`comp`/`const`, no `prec`) — the key to provable responsive-trader e.c. (design (B), full faithfulness preserved). Round-trip axiom-clean |
| `dd:fuel` (infra) | `Fueled` + `fueled_const/left/right/succ/pair/comp/id` (`Computable.lean`) | done | **P** | prec-free fuel combinators: `Code.pair`/`comp` don't decrement `evaln`, so a `Nat.pair`-tree code's budget composes. The hard, novel part — fuel accounting through the clocked interpreter. Axiom-clean |
| `dd:fuel` (bridge) | `IsPolyBounded` (+`of_le`/`linear`/`max`/`add_one`/`pair`), `pair_lt_sq`, `of_fueled` | done | **P** | poly-bound closure incl. `Nat.pair` (degree doubles); turns a poly-bounded `Fueled` fact into `def:ec` |
| `dd:fuel` (templates) | `PolyEF` (+`const`/`price`/`add`/`mul`/`max`/`safeRecip`), `ec_of_polyEF` | done | **P** | reusable layer: any `EF` feature template built from the constructors has an e.c. per-day code, so a single-sentence responsive trader's e.c. is a few lines (`priceTrader_ec` now one line; the responsive `max(0,c−φ*ⁿ)` buy-signal e.c. in one line). Makes the property-tail responsive-trader e.c. proofs cheap |
| `dd:fuel` (pred) | `predAux`, `predAux_evaln`, `predc`, `predc_polyFueled`, **`PolyEF.pricePred`** | done | **P** | **prec-fueled predecessor** — the one place `evaln` fuel is accounted through a genuine `Code.prec` (which decrements), since `Nat.pred` is not prec-free-expressible. `predAux = prec zero (comp left right)` computes `pred` on `pair 0 m`; induction through the prec clause bounds fuel by `32(m+1)⁴` (dominant guard `pair 0 (pair m (m-1)) ≈ (2m)⁴`). `PolyEF.pricePred`: the day-`(n-1)` feature `φ*⁽ⁿ⁻¹⁾` is e.c. valid, reusable infra for any *bounded-depth* two-day-referencing trader. (Note: this does **not** unblock `thm:con` after all — convergence needs *linear-depth* hysteresis, and depth, not the `n-1` reference, is the wall; see OPEN RISK 4.) Axiom-clean |
| `dd:fuel` (capstone) | `PolyFueled` (+`const`/`id`/`pair`/`succ_comp`), `priceTrader`, **`priceTrader_ec`** | done | **P** | **first responsive trader certified e.c. under the faithful `def:ec`** — `priceTrader φ` plays `[(φ*ⁿ,φ)]` (coefficient varies with `n`); code assembled from `PolyFueled` primitives, poly bound automatic. Axiom-clean. Validates the whole e.c. pipeline; the property-tail responsive traders now follow this pattern |
| `def:ec` (tool) | `evaln_const_self` | done | **P** | `K ∈ evaln (n+K+1) (Code.const K) n` — fuel bound for constant-strategy traders |
| `def:ec` | `EfficientlyComputable` | done | **Def, faithful for bounded-depth** | `∃ code, poly, ∀n, evaln (poly n) code n = some (encode strat)` — the paper's poly-*runtime* `def:ec` via `Nat.Partrec.Code` + `evaln` (`dd:fuel`). Faithful for the bounded-depth traders every proved property uses. ⚠️ **but not for poly-size, linear-*depth* strategies** (the `toNat` bit-length quadruples per depth level), which the paper's poly-*size* `def:ec` admits and `thm:con` needs — see **OPEN RISK 4**. So here `IsLogicalInductor` is *weaker* than the paper (excludes deep exploiters), pending a trust-surface fix. **Being retired** in favor of `EfficientlyComputableTok` (below); kept (renamed `…Val`) at the switch since its certs stay true |
| `def:ec` (flat encoding) | `EF.serialize`, `serializeTrades` | done | Def | **flat postfix (RPN) token stream** for a feature / strategy — the poly-*size* encoding replacing whole-number `toNat` emission. Length `Θ(node count)` (`serialize_length_le_cost`), tokens small (tags `0..5`/`6`, day indices, atomic `⌜φ⌝`/`⌜q⌝` codes). Resolves OPEN RISK 4's encoding wall |
| `def:ec` (honesty) | `EF.serialize_injective`, `serializeTrades_injective` (via stack machine `EF.readM` + roundtrips) | done | **P** | **the token stream determines the feature/strategy** — RPN is not prefix-free but *is* uniquely decodable; one `readM` roundtrip induction gives both. Guards against "emitting tokens" being a non-faithful representation. Axiom-clean (3 standard) |
| `def:ec` (size faithfulness) | `EF.serialize_length_le_cost` | done | **P** | `(serialize e).length ≤ 3·cost e` — poly-*size* ⇔ poly-*length*, the property that makes deep poly-size features admissible under `…Tok`. Axiom-clean |
| `dd:fuel` (dispatch) | `iterRight`, `sel`, `selFn`, `tupleEnc`, **`iterRight_evaln`** | done | Def+**P** | **runtime index selection** `sel ⟨T,i⟩ = left (right^i T) = tupleEnc⁻¹[i]`, via one genuine `Code.prec` recursion on `i` (the 2nd such in the file, after `predc`). Fuel bounded degree-2 in `pair T i` through the clocked interpreter. `selFn_tupleEnc`: selection correct on a right-nested tuple. Axiom-clean. **Scope: fixed (small) tuples only** — a right-nested tuple of a length-`Θ(n)` stream has *doubly-exponential value*, so `sel` cannot rescue varying-length emission (that needs per-index arithmetic, below) |
| `dd:fuel` (branch primitive) | `ifzSel`, `ifzSelFn`, **`ifzSel_evaln`**, `ifzSel_polyFueled` | done | Def+**P** | **branchless zero-test selector** `ifzSel ⟨pair A B, i⟩ = if i=0 then A else B` — one `Code.prec` (3rd in file) with projection-only `cf`/`cg` (`left`, `comp right left`; candidates ride in the input, no `const` in the recursion, so the fuel proof is as cheap as `iterRight`'s), degree-2 fuel. **The bottleneck primitive for varying-length (deep-trader) emission:** a size-`Θ(n)` strategy's `i`-th token is a fixed nesting of `ifzSel`s over `pred`-shifted indices. Axiom-clean |
| `dd:fuel` (subtraction) | `subAux`, `subAux_cg_eval`, `subAux_step`, **`subAux_evaln`**, `subc`, `subc_fueled`, `subc_polyFueled` | done | Def+**P** | **truncated subtraction** `subc ⟨a,b⟩ = a − b` — the one **nested** `Code.prec` in the file (recursive step applies `predc`, itself a `prec`), so the fuel proof composes `predc`'s degree-4 budget across `b` levels (explicit bound `32(a+1)⁴ + pair a (pair b a) + a + b + 9`). Completes the arithmetic toolkit (`ifzSel` branch + `predc` decrement + `subc` compare + `sel` fixed-select) for varying-length emission: a deep trader's trailing `[6,⌜φ⌝]` frame is at an `n`-dependent stream position, so emitting it needs `subc` to compare against `n`. Axiom-clean |
| `def:ec` (varying-length workhorse) | **`ecTok_of_tokenFn`** | done | **P** | the **generalization of `ecTok_of_tokenList` to growing streams**: a trader is `EfficientlyComputableTok` as soon as one poly-fueled `tokenFn` computes the `i`-th token of `serializeTrades (strat n)` from `⟨n,i⟩` and the stream length is poly. The missing helper for deep (size-`Θ(n)`) traders — their `i`-th token is a fixed arithmetic expression in `⟨n,i⟩` (from `ifzSel`/`predc`/`subc`), not a fixed-list lookup. Fuel: `PolyFueled` gives `bc ⟨n,i⟩`; a monotone poly bound with `i < len n ≤ poly` gives poly-in-`n`. Axiom-clean. **Closes the tooling gap flagged when the fixed-length limit was found** |
| `dd:fuel` (poly-closure) | `IsPolyBounded.comp`/`.add`, `PolyFueled.comp`/`.left`/`.right`, `sel_polyFueled` | done | **P** | **`PolyFueled` now closed under composition** (was only `pair`/`succ_comp`) — needed `IsPolyBounded.comp` (poly∘poly = poly). Lets the token-emitter `comp sel ((comp cV left).pair right)` be assembled and its poly fuel drop out automatically. Axiom-clean |
| `def:ec` (re-cert workhorse) | **`ecTok_of_tokenList`**, `PolyFueledTuple` (+`nil`/`cons`) | done | **P** | the reusable lemma: a trader whose day-`n` stream is a **fixed-length** list `ts.map (·n)` of poly-fueled tokens is `EfficientlyComputableTok`. Emitter builds the tuple (`cV`) then selects index `i` (`sel`); fuel poly-in-`n` via `pair n i < (n+L+1)²` and `i < L`. This is the M2-analogue "wire the whole e.c. pipeline once" for the token model. Axiom-clean. **Scope: fixed-length only** — every existing trader has a bounded-shape strategy (constant stream length, only leaf values vary). A genuinely deep trader (size-`Θ(n)`, e.g. `thm:con` hysteresis / `thm:nd` counter) has a stream length that *grows* with `n`; the **`def` admits it** (length clause allows poly growth) but this workhorse does **not** — that needs a varying-length emission helper (not yet built). So OPEN RISK 4 is resolved at the definition/trust-surface level; deep-trader e.c. still needs both the trader and a varying-length cert path |
| `def:ec` (Tok validation) | `priceTrader_ecTok` | done | **P** | the responsive `priceTrader φ` (stream `[0,⌜φ⌝,n,6,⌜φ⌝]` with the *varying* `n` token = `PolyFueled.id`) re-certified under the new def — validates the pipeline end-to-end; the template the property-file re-certs follow. Axiom-clean |
| `def:ec` (compositional re-cert) | `PolyTokenStream` (+`nil`/`append`/`const`/`idTok`/`polyTok`/`serialize_{price,const,add,mul,max}`/`trades_cons`/`trades_nil`), `ecTok_of_stream` | done | **P** | the layer that makes deep-trader re-cert tractable: `PolyTokenStream s` = "`s n` is `ts.map(·n)`, tokens poly-fueled", **closed under append**, so a re-cert mirrors the trader's `serialize` tree via combinators (no hand-written token list). `serialize_*` = one per `EF` constructor. Axiom-clean |
| `def:ec` (re-cert, all 7 traders) | `buyDaily_ec`, `sellDaily_ec`, `buySeq_ec`, `priceTrader_ecTok`, `exclTr_ec`, `eqTr_ec`, `impTr_ec` (+ `gapEF_stream`/`sigEF_stream`/`gap2EF_stream`/`sig2EF_stream`/`impSig_stream`) | done | **P/C** | **every existing trader re-certified under `EfficientlyComputableTok`** — the constant ones directly, the deep responsive ones (`exclTr`/`eqTr`/`impTr`, ~40–60-token streams) via `PolyTokenStream` combinator trees. Names kept, so property-proof call sites are unchanged. All axiom-clean |
| `def:ec` (poly-size model) | `EfficientlyComputableTok` | done | **Def** (**wired into `def:lic`**) | **token-indexed emission:** `∃ c a k, (∀n, len(serializeTrades strat n) ≤ poly) ∧ ∀ n i < len, evaln poly c ⟨n,i⟩ = some (token i)`. The faithful poly-*size* `def:ec` — emits the flat stream one token at a time, so deep poly-size traders (hysteresis, counters) are admissible. Verified against Mathlib source: `evaln`'s input guards cap a fixed code's output value at `poly(fuel)`, so whole-number emission of *any* injective packing fails; token-indexing is the fix. **Residual type-`(c)`:** token *values* ≤ `poly n`, so `⌜φ⌝` must be `poly n`-value (fixed sentences constant; varying-φ traders already carry the bound). Wiring into `def:lic` is the pending switch |
| **`def:lic`** | `IsLogicalInductor` (class over `P`, `DP`) | done | Def | "no e.c. trader exploits `P`". The property-tail hypothesis. **Now quantifies over `EfficientlyComputableTok`** (the faithful poly-*size* model), so it forbids deep poly-size exploiters too — matches the paper (OPEN RISK 4 resolved) |
| `def:trader` (M2) | `buyDaily` (buys 1 share of `φ`/day) | done | **C** | the **constructed** exploiting trader for the base case of `thm:provind`. Real EF (`[(const 1, φ)]`), not a stub |
| `def:ec` (M2 cert) | `buyDaily_ec` | done | **P** | e.c. discharged via the faithful clocked model: constant strategy ⇒ `Code.const`, affine fuel via `evaln_const_self`. Axiom-clean |
| `def:exploitation` (M2) | `buyDaily_exploits` | done | **P** | full proof: BddBelow (net worth ≥ 0 in every plausible world) ∧ ¬BddAbove (≥ (m+1)ε → ∞). No `sorry`; `#print axioms` = the 3 standard only |
| `def:luv` | `LUV` (threshold sentences `gt : ℚ → Sentence`) | done | Def | **disclosed type-`(c)`:** LUVs are first-order (formula free in one var over Θ-rep-computations); we model the `[0,1]`-LUV by its market-observable content = its threshold-sentence family `⌜X>r⌝`. No first-order syntax reconstructed |
| `def:e` | `LUV.expectApprox`, `.expect`, `.expectSeq`, `.expectInf`; `expect_mem_Icc` | done | Def+P | `𝔼ₙ(X)=(1/n)∑_{i<n}Pₙ(⌜X>i/n⌝)` — the **concrete `ℕ→ℝ` expectation** the deference corpus abstracts as `E^H_n(X)`. Bounds `∈[0,1]` proved. **This is the LUV-bridge object that closes the price→expectation level gap** |
| `thm:ec` | `LUV.expect_converges` | **sorry** | C | expectations converge; stated conditionally on `[IsLogicalInductor]`. **Deferred `sorry`** — genuine property-tail theorem (`app:ec`): needs per-threshold `thm:con` + moving-precision control (moving-threshold trader infra). Honestly ledgered |
| **integration** (expectation) | `IntegrationTest` Part C | done | **C** | closes the interface level gap: `value_argmax_asymptotic` instantiated with concrete `X.expectSeq P` for all `E_now(·)` slots — the corpus's expectation sequences **are** our objects, no adapter. LI hypotheses still assumed (= `thm:cee/expprovind`, the property-tail work `Expectations` states) |
| **integration** | `IntegrationTest.value_argmax_asymptotic`, `provind_hypothesis_discharged` | done | **C** | roadmap M3 integration test. Reproduces the deference corpus's `value_argmax_asymptotic` in our vocabulary (drop-in ✓ — `DeferenceAsymp.Approx/AsympLE` are *defeq* our `AsympEq/AsympLE`) and discharges a provind-shaped hypothesis `Approx (P·φ) 1` from `lic_deducible_tendsto_one` with no adapter. Axioms clean. **Finding:** interface matches at the *price/asymptotic* level; expectation-level hypotheses (`E^H_n`) still need the LUV bridge (M3/M4) |
| `thm:con` (reduction) | `exists_rat_oscillation_of_not_convergesTo` | done | **P** | non-convergence of a `[0,1]`-price ⇒ a **rational** oscillation (`Pₙφ < a` i.o. ∧ `> b` i.o., `a<b∈ℚ`). Contrapositive of Mathlib `tendsto_of_no_upcrossings` over the dense range of `(↑):ℚ→ℝ` (`Rat.denseRange_cast`); rationality of `a,b` is what lets the arbitrage trader use them as `EF` constants. Hyps `(b)`; axiom-clean (`propext/Choice/Quot`). The "assume-property-fails ⇒ extract-exploitable-config" half of `thm:con`, carried by a library lemma not a hand-roll |
| `thm:con` (arbitrage) | `oscillation_exploitable` | **sorry (construction task)** | — | states: a rational oscillation (+ daily plausible world) admits an **e.c. trader that exploits**. **No longer blocked by a trust-surface limit** — OPEN RISK 4 is resolved, so the **hysteresis** exploiter (buy `<a`, hold until `>b`, sell; banks `b−a` per swing regardless of smoothness) is now admissible: its "am I holding?" state is a size-`Θ(n)` linear-depth `EF`, which `EfficientlyComputableTok` (poly-*size*) admits. Bounded-depth alternatives still provably fail. What remains is **genuine construction work** (not a decision): build the running-state hysteresis `EF` (its e.c. discharges via `PolyTokenStream`/`ecTok_of_tokenList`), prove it banks `≥ b−a` per swing, feed to `exploits_of_ge_partialSums`. Per Rule 1 the `sorry` stays until that trader is built |
| `thm:con` | `lic_price_convergesTo` | **sorry** (conditional) | **C** | Convergence in the limit: `[IsLogicalInductor] ⇒ ∃L, Pₙφ → L`, for every `φ` (prices `∈[0,1]`, daily plausible world). Chains the reduction against `def:lic` via `oscillation_exploitable`. Axioms = 3 standard **+ `sorryAx`** (through the arbitrage lemma), transparently. Reduction half real & clean; the trader is the disclosed gap |
| exploitation (reusable) | `exploits_of_nonneg_partialSums` | done | **P** | factored engine: a trader whose day-`i` value **in every plausible world** is a fixed nonneg sequence `w i`, with `w ≥ ε` frequently, exploits (BddBelow by 0; ¬BddAbove by subsequence accumulation). Reused by additivity's two directions; the shared core behind `buyDaily`/`sellDaily`-style freq arguments |
| `thm:lc` bullet 3 (additivity) | `exclTr`, `exclTr_value`, `exclTr_ec`, `exclTr_exploits`, **`lic_excl_gap_tendsto_zero`** | done | **C** | **finite additivity, finite-stage form:** `⊢∼(φ∧ψ) ⇒ Pₙ(φ∨ψ)−Pₙφ−Pₙψ → 0` under a logical inductor (⇒ `P∞(φ∨ψ)=P∞φ+P∞ψ` with `thm:con`). Genuinely-constructed **world-neutral portfolio** trader `σ·[(-1,φ∨ψ),(1,φ),(1,ψ)]`: payouts cancel by exclusivity (`payout_or_of_excl`), so day value = deterministic `σ·gap`; continuous buy-signal `max(0,σ·gap−ε/2)` ⇒ bounded-below/unbounded-above (no hysteresis needed). **e.c. genuinely discharged** — first *multi-trade* (3-sentence) responsive trader, via the `Nat.pair`-tree list encoding over `PolyEF` templates (`exclTr_ec`). Both mispricing directions = one `σ`-parametrized trader. Axiom-clean |
| exploitation (≥ variant) | `exploits_of_ge_partialSums` | done | **P** | generalizes `exploits_of_nonneg_partialSums` to a **lower bound**: plausible-world net worth `≥ ∑ w` (nonneg, freq `≥ ε`) ⇒ exploits. The engine for *world-dependent* traders whose value is only bounded below by a world-independent quantity (implication learning) |
| `thm:lex` (implication) | `impTr`, `impTr_ec`, `PCWorld.payout_le_of_imp`, `impTr_value_ge`, **`lic_imp_eventually_le`** | done | **C** | **Learning logical implication / price monotonicity:** `⊢ φ→ψ` ⇒ eventually `Pₙφ ≤ Pₙψ + ε` (∀ε>0). The sell-`φ`/buy-`ψ` portfolio is **not** world-neutral — value carries a world-dependent `payout ψ − payout φ ≥ 0` (nonneg since `φ→ψ`) atop the deterministic `Pφ−Pψ`, so day value is only *bounded below* by `impSig·(Pφ−Pψ)` (world-independent) — a genuinely new trader pattern, consumed by `exploits_of_ge_partialSums`. Axiom-clean |
| `thm:lex` (equivalence) | `eqTr`, `eqTr_ec`, `PCWorld.payout_eq_of_iff`, **`lic_lex_tendsto_zero`** | done | **C** | **Learning logical equivalence:** `⊢ φ↔ψ` (both `∼φ⋎ψ`, `∼ψ⋎φ` revealed) ⇒ `Pₙφ − Pₙψ → 0` under a logical inductor. Same world-neutral-portfolio pattern as additivity but *two*-sentence `σ·[(1,φ),(-1,ψ)]`: payouts equal by equivalence (`payout_eq_of_iff`), day value = deterministic `σ·(Pφ−Pψ)`; reuses `exploits_of_nonneg_partialSums` + `exclTr`-style buy-signal. e.c. via the `Nat.pair`-tree list encoding. Axiom-clean |
| `thm:lc` bullet 2 (disprovable→0) | `lic_disprovable_tendsto_zero`, `sellDaily`, `sellDaily_exploits_freq`, `PCWorld.payout_of_disprovable` | done | **C** | Limit-Coherence dual: `∼φ` always-deducible ⇒ `Pₙ(φ)→0` under a logical inductor. Mirror **sell** trader (`[(const -1,φ)]`), constant hence e.c.-certified like `buyDaily`; frequently-overpriced accumulation. Foundation Boolean semantics gives `payout φ = 0` in `∼φ`-worlds. Axioms clean. (Bullet 1 = `lic_deducible_tendsto_one`; bullet 3, finite additivity, needs a non-constant/ROI trader — bounded-below fails for a naive constant portfolio — deferred) |
| `thm:provind` (limit, fixed φ) | `lic_deducible_tendsto_one`, `lic_deducible_eventually_ge`, `buyDaily_exploits_freq` | done | **C** | the genuine `≈ₙ 1` limiting form for a *fixed* always-deducible `φ`: **reuses the M2 e.c.-certified `buyDaily`** (no new trader/e.c.) via a frequently-underpricing accumulation argument (`extraction_of_frequently_atTop` + subset-sum). Axioms clean |
| `thm:provind` (sequence form) | `buySeq`, `buySeq_ec`, **`lic_provind_seq`**, `ec_of_polyEF_seq` | done | **C** | the `𝓔𝓒`-sequence form: for an **efficiently computable sequence** of sentences `φₙ` each deducible by day `n`, `Pₙ(φₙ) → 1`. Same constant buy trader indexed by the sequence; the new ingredient is e.c. of a **varying-sentence** trade, discharged by `ec_of_polyEF_seq` from the `𝓔𝓒`-sequence hypothesis `hφ : PolyFueled cφ (n ↦ ⌜φₙ⌝)`. Exploitation via the reusable `exploits_of_nonneg_partialSums` (world-value `1−Pₙφₙ`, `φₙ ∈ D n ⊆ D m` gives payout 1). Axiom-clean. Generalizes the fixed-`φ` form |
| `thm:provind` (base case) | `lic_deducible_price_near_one` | done | **C** | the loop closed against `def:lic`: under `[IsLogicalInductor]`, an always-deducible `φ` has `1−ε < Pₙφ` for some n, ∀ε>0. **Special case** (always-deducible, uniformly underpriced); general `thm:provind` is M3 |
| `def:tradermag` | `Strategy.magnitude`, `Trader.magnitude`, `abs_value_le_magnitude` | done | Def+P | magnitude + the `\|value\| ≤ magnitude` bound proved (needs `[0,1]` prices + `{0,1}` world) |
| `def:roi` | `HasROI` | done | Def | ε-ROI predicate over `ConvergesTo` (`dd:asymp`). The ROI⇒exploitation **lemma** is M4 |
| **`def:tf`** | `EF` (inductive), `EF.denote`, `EF.cost`, `EF.rank` (`Criterion.lean`) | done | Def | keystone DSL: price/const/add/mul/max/safeRecip. `denote` noncomputable (ℝ inv); `cost` = structural node count — **disclosed `dd:fuel` deferral:** precise unary day/code charging tying `cost` to poly-runtime is M2, when the trader e.c. cert first consumes it |
| `def:tf` (continuity) | `EF.continuous_denote` | done | **P** | continuity **proved** for the whole DSL (not left as a stated constraint), by induction; safeRecip via `max 1 · ≥ 1 > 0`. Hyps `(b)` (Mathlib `continuous_apply`/`Continuous.{add,mul,max,inv₀}`). This is what breaks the price/trade circularity for Brouwer |
| `def:tf` (ring) | `EF.ExpressibleRankLE`/`EFn`, `CommRing (EFn n)` | done | **P** | `𝔼_n` realized as a **`Subring` of `History → ℝ`** (features are functions): carrier `{denote e \| rank e ≤ n}`, closure under `+,×,neg` proved; `CommRing` inherited. Faithful to the paper's "𝔼_n is a commutative ring" `(b)` |
| `def:tf` (non-vacuity) | `EF.exMaxDiff` + 2 `example`s | done | **N+** | the paper's `max(0, φ*6−ψ*7)`: rank `= 7` and value `= 0.3` at the paper's inputs; plus safeRecip lands in `(0,1]` for all args. Genuine (non-constant) witnesses |
| `lem:fpl` (dep) | `brouwer_fixed_point` | **done** | P | **proved from scratch** (Sperner/Kuhn over the Freudenthal triangulation → fixed point on compact convex `K ⊆ EuclideanSpace ℝ (Fin d)`). Provenance: **autoformalized by Harmonic's Aristotle** (runs `1d7dc5e0`/`c712e6d9`, built there on Lean/Mathlib v4.28.0), dropped in verbatim modulo namespace + header, **revalidated on this project's toolchain** (v4.28.0-rc1, Mathlib master@58d8468): builds green, `#print axioms` = `propext, Classical.choice, Quot.sound` (checked in-file). Trust surface = the final statement only (unchanged from the M0 `sorry` version); the ~1300-line `BrouwerProof.*` interior is machine-generated proof plumbing nobody has read — the kernel has checked it, a human has not, which is exactly the division of labor the standard permits. Imports trimmed from the Aristotle original's `import Mathlib` umbrella to the 7-module minimal set found by `linter.minImports`. |

## Substrate findings (from `Scratchpad.lean`, M0)

- **`def:lang` is well-served by Foundation.** `LO.Propositional.Formula ℕ` carries
  `DecidableEq` and — the gating fact for `def:ec` — `Encodable (Formula α)`, a concrete
  `toNat` coding. So sentences have **computable codes off `ℕ` for free**; we do not need
  to build a Gödel numbering. Derivability/consistency come from `LO.Entailment`
  (`⊢` / `⊬` / `Consistent`), classical logic from `LO.Propositional.Hilbert.Cl`. Plan:
  wrap these behind a thin `LogicalInduction.Sentence` interface. Provenance `(b)`.
- **Mathlib substrate present:** `Filter.Tendsto` / `atTop` / `nhds` / `Filter.Eventually`
  (asymptotics), `IsCompact` / `Convex` / `ContinuousMap` (price space), and
  `MeasureTheory.integral` (Bochner, for the LUV bridge — present but see clash below).
- **✅ OPEN RISK 1 — Foundation/Mathlib `Matrix`-namespace clash — RESOLVED via fork (now
  the complete set).** `Foundation.Vorspiel.Matrix` (in Foundation's prelude, so *all*
  Foundation modules) extends the `Matrix` namespace with its own `Fin k → α` helpers,
  three of which shadow distinct Mathlib `Matrix.*` names, making Foundation unimportable
  alongside the corresponding Mathlib module:
    - `Matrix.map` ↔ Mathlib `Matrix.map` (via `Matrix.map.eq_1`; Bochner, matrix analysis) — found M0;
    - `Matrix.forall_iff`, `Matrix.exists_iff` ↔ `Mathlib.Data.Matrix.Reflection` — found **M1**, when
      `Foundations`/`Criterion` (which import Foundation) first shared the roll-up's import graph with
      `Construction/Brouwer` (which pulls `Matrix.Reflection` transitively via `EuclideanSpace`).
  Fixed by renaming all three to `vecMap` / `vecForall_iff` / `vecExists_iff`
  (`A-M-Berns/Foundation@aada66e`; notation `⨟` and lemma bodies unchanged, 12 call sites
  updated). Verified **complete**: intersected every `Matrix.*` decl in `Vorspiel/Matrix.lean`
  against Mathlib — no other collisions. Full roll-up (Foundation + Bochner + Brouwer) now
  builds green. Upstreamed as **PR #835**. *Discipline note kept:* still prefer targeted
  Mathlib imports over the `import Mathlib` umbrella alongside Foundation.
- **✅ OPEN RISK 2 — no Brouwer in Mathlib — RESOLVED in-project.** Installed Mathlib has
  **no Brouwer (or Schauder/Kakutani) fixed-point theorem** — only Brouwerian/Heyting
  *algebras* and Riesz–Markov–Kakutani (a measure theorem); the roadmap's "use Mathlib's
  Brouwer" (`lem:fpl`) remains false as written. Resolved instead by a from-scratch proof
  (Sperner's lemma route) in `LogicalInduction/Construction/Brouwer.lean`, autoformalized
  by Harmonic's Aristotle and revalidated on this toolchain — see the ledger row for the
  full provenance and trust-surface accounting. M6 is no longer gated. Upstreaming the
  proof to Mathlib is still desirable (and would let us delete the 1300-line vendored
  proof) but is now optional, not blocking.

- **✅ OPEN RISK 3 — `EfficientlyComputable` fidelity — RESOLVED.** The provisional
  poly-*size* stand-in has been replaced by the faithful `dd:fuel` model: a trader is e.c.
  iff a single `Nat.Partrec.Code` program, run under the clocked interpreter `evaln` for a
  *polynomial* fuel budget `a·(n+1)ᵏ+a`, outputs the encoded day-`n` strategy. This is the
  paper's poly-time (unary) `def:ec` on the nose, and the e.c. class is computably
  enumerable (over `(code, a, k)` triples) as the construction will need. It no longer
  admits uncomputable strategy sequences, so `IsLogicalInductor` now *matches* the paper
  rather than being strictly stronger — the M7 soundness risk is gone. Two pieces of new
  infrastructure made this possible: a hand-built **computable** `Encodable EF` (there is no
  `deriving Encodable`; structural `toNat` + fuel-clocked structural `ofNat` + round-trip,
  `#print axioms` clean), and `evaln_const_self` (a `Code.const` fuel bound). M2's
  `buyDaily_ec` was re-proved against the new definition with no `sorry` and a clean axiom
  footprint.

- **Faithful `def:ec` via `Nat.Partrec.Code.evaln`** (post-M2): chose to model efficient
  computability directly on `dd:fuel` — Mathlib's clocked interpreter `evaln` with a
  polynomial fuel budget — rather than keep the poly-size proxy. Required hand-building a
  **computable** `Encodable EF` (no `deriving Encodable` exists; a classical `Countable`
  one would give a non-computable decoder, which would not let a machine recover the
  strategy — so it had to be genuinely computable). Used a fuel-clocked *structural*
  decoder (`ofNatAux`) to sidestep well-founded-recursion pain (`decreasing_by` would not
  expose the match's `m % 6 = k` condition to `omega`). This closes the one genuine
  soundness gap in the stack.

- **✅ OPEN RISK 4 — RESOLVED (2026-07-08) by the token-indexed `def:ec`.** The redefinition
  Anson approved is in: `IsLogicalInductor` now quantifies over **`EfficientlyComputableTok`**,
  which emits the strategy's flat `serializeTrades` stream **one token at a time** (input `⟨n,i⟩`
  → `i`-th token) rather than the whole `Encodable.encode` as one `2^{poly n}`-value number. This
  admits deep poly-*size* strategies (linear-depth features, size-`Θ(n)`), so the e.c. class now
  matches the paper's poly-size `def:ec` and `IsLogicalInductor` is no longer artificially weak.
  Verified against Mathlib `evaln` source that whole-number emission of *any* injective packing
  hits an `O(log n)`-bit output ceiling (input guards cap a fixed code's output at `poly(fuel)`),
  so token-indexing — not a flatter single-number encoding — is the necessary fix. All seven
  existing traders were re-certified (`ecTok_of_tokenList` + the `PolyTokenStream` combinator
  layer; the nested-but-bounded-shape `exclTr`/`eqTr`/`impTr` via `serialize`-tree combinators),
  sorry count and axiom footprint unchanged. **Caveat on scope:** those seven are all
  *fixed-length* streams (bounded strategy shape; only leaf values vary with `n`). The genuinely
  size-`Θ(n)` traders OPEN RISK 4 was about (`thm:con` hysteresis, `thm:nd` counter) have
  *growing* streams; the **definition** admits them (poly-length clause), but the re-cert
  *tooling* built here is fixed-length only — deep-trader e.c. still needs a varying-length
  emission helper plus the trader itself. So what OPEN RISK 4 fixed is the **trust surface**
  (the class is now the right one); the deep constructions were always downstream work. **Residual (small, disclosed, type-`(c)`):** each token's *value* is
  still `poly n`, so a traded sentence's atomic code `⌜φ⌝` must be `poly n`-value on day `n`
  (fixed sentences constant; varying-`φₙ` traders already carry the bound) — formula-level
  sub-tokenization would remove even this and is a later refinement. `thm:con`'s
  `oscillation_exploitable` is **no longer blocked** — its hysteresis trader is now admissible;
  what remains is *constructing* it (a real trader-building task, not a trust-surface decision).

  *Original entry (kept for the record):* **⚠️ OPEN RISK 4 — `EfficientlyComputable` excludes
  poly-*size*, linear-*depth* strategies (surfaced while attempting `thm:con`; needs Anson).**
  The `dd:fuel` model (OPEN RISK 3) is
  faithful for **bounded-depth** traders but *not* for deep ones, and `thm:con` is the first
  node that needs a deep trader. Convergence's exploiter must, on a *smoothly* oscillating
  price, hold a position through each ramp and flip only at the thresholds — a **hysteresis**
  rule whose "am I holding?" state is an **unbounded look-back**, i.e. a **linear-depth**
  (`size Θ(n)`) `EF`. (Bounded-depth traders provably don't suffice: memoryless target-holding
  `T(Pₙ)−T(Pₙ₋₁)` telescopes to a path-independent state function; mean-reversion `Pₙ₋₁−Pₙ`
  only harvests quadratic variation `½Σ(ΔP)²`, which a smooth ramp drives to `0`.) But our e.c.
  requires a `Code` emitting `EF.toNat`, a `Nat.pair`-nested number whose **bit-length
  quadruples per depth level** (measured `6,23,91,362,1445` bits at depth `0..4`, `≈6·4ᵈ`); a
  linear-depth feature has a `~4ⁿ`-bit code that **no `evaln(poly n)` run can emit**. So a
  strategy that is poly-*size* (legal under the paper's `def:ec`) but linear-*depth* is wrongly
  excluded — our e.c. class is *strictly smaller* than the paper's here, `IsLogicalInductor` is
  correspondingly *weaker*, and `thm:con` does **not** follow. Fix (a **trust-surface** change,
  hence Anson's call): redefine `EfficientlyComputable` to bound the poly **size of a structural
  description** of the strategy tree (e.g. a flat prefix/list encoding), not the runtime of the
  bit-blowup `toNat`. Note this does **not** retroactively break the existing (bounded-depth)
  e.c. certs — they stay valid under either encoding; it *enlarges* the admissible class. Until
  decided, `oscillation_exploitable` / `thm:ec` stay `sorry`. The `PolyEF.pricePred` (prec-fueled
  `predc`) infra remains valid and useful (any two-day-referencing bounded-depth trader), but it
  does **not** unblock `thm:con` as earlier hoped — depth, not the `n-1` reference, is the wall.

  **Addendum (2026-07-07, pre-session analysis; verified against Mathlib source).** The gap is
  wider than depth, and the fix as originally proposed is insufficient:
  - *Output-value ceiling.* Every `evaln` clause guards its **input** by fuel (`guard (n ≤ k)`,
    `Mathlib/Computability/PartrecCode.lean:569` ff.), so intermediate values — including `prec`
    accumulators — stay ≤ fuel; the only unguarded growth is the fixed composition of `pair`s at
    the output. Hence for a fixed code `c`, `evaln k c n` outputs values ≤ `(k+1)^(2^|c|)`: with
    poly fuel, **only poly-value (O(log n)-bit) outputs are producible**. So swapping `toNat` for
    a flat/linear-bit list packing does **not** fix OPEN RISK 4 — any injective `List ℕ → ℕ`
    packing of a size-Θ(n) description has value 2^Θ(n) (Mathlib's own list encoding is
    `Nat.pair`-nested and exponentially wasteful; balanced trees don't help either — a balanced
    size-n `EF` still has an ~n·log n-bit `toNat`). The redefinition must use **token-indexed
    emission**: the code computes the `i`-th token of the day-`n` strategy's flat serialization,
    with a separate poly length bound. Precise spec in `notes/next-session.md` §2.
  - *Blast radius.* The wall gates more than `thm:con`: `thm:nd`'s budget-halving trader needs a
    purchase **counter** (unbounded look-back, size-Θ(n) EF), and bounded-depth substitutes
    provably fail (a fixed price-window rule either spends unboundedly on a price plateau or,
    day-discounted, has convergent profit). Expect **every remaining M3 node** (`thm:con`,
    `thm:nd`, the expectation family, Self-Trust) to be gated on this decision, not just
    `thm:con`.
  - *Existing certs unaffected in truth-value* (bounded-depth traders have poly-value `toNat`s,
    which is why they worked), but under the token-emission def they need mechanical
    re-certification — plan and helper-lemma sketch in `notes/next-session.md` §2 T4.
## Decisions log

- **Paper vendored into `notes/`** (M0 close-out): `1609.03543v5.pdf` and its LaTeX
  source `1609.03543v5-main.tex` (the file the roadmap's `\label`s were verified
  against), so label questions are answerable in-repo. First use: the roadmap's §7
  kickoff prompt said `def:ef` where the paper's real label is `def:tf`
  (`main.tex:786`); fixed.
- **Aristotle output accepted for `lem:fpl`'s Brouwer dependency** (M0 close-out): see
  ledger row. Statement unchanged from the hand-written `sorry` version, so the trust
  surface didn't move; only the proof body (kernel-checked, human-unread) changed status.
- **`def:tf` keystone modeling choices** (M1): (1) `EF` is *syntax*; the CommRing "`𝔼_n`"
  lives on the *semantic* side as a `Subring` of `History → ℝ` (features are functions),
  avoiding a syntax quotient — the syntax stays the object that carries `cost`. (2)
  `denote`'s domain `History := ℕ → Sentence → ℝ` uses codomain `ℝ` (not `[0,1]`) and
  0-indexed days (not `ℕ⁺`) — both disclosed type-`(c)` conveniences, ledgered. (3)
  Continuity is *proved*, not just stated (the roadmap allowed `sorry`); it was cheap and
  it strengthens the Brouwer hand-off. (4) `cost` = structural node count for now; the
  precise `dd:fuel` unary charging is deferred to M2 where the e.c. cert first needs it.
- **`def:lic` criterion definitions** (M1): worlds modeled as Foundation Boolean models
  (`PCWorld := ℕ → Prop` read through `Formula.Boolean.val`), so propositional consistency
  is free and faithful rather than hand-rolled over Foundation's connectives. Strategies use
  the paper's canonical `(eᵢ,φᵢ)`-list encoding. **The one load-bearing debt is
  `EfficientlyComputable`** — a provisional poly-*size* bound standing in for the paper's
  poly-*runtime* `def:ec`; it is *broader* than the paper's notion (so `IsLogicalInductor`
  is *stronger*), which is the single most important thing to get right in M2 before any
  property proof leans on it. Flagged loudly in the def's docstring and the ledger. This is
  a **surfaced friction**, not a silent shortcut: M2 exists precisely to wire `EF.cost`
  through a genuine efficiency notion end-to-end.
- **Extended the Foundation fork to the full clash set** (M1): the `Matrix.map` rename
  (M0) was one of three colliders; `forall_iff`/`exists_iff` surfaced when the roll-up
  first co-imported Foundation with the Brouwer file. Chose to fix the root cause now
  (rename all three, bump pin to `aada66e`, broaden PR #835) rather than decouple the
  roll-up — per Anson's call — since the construction (M6) will need Foundation+Brouwer
  together regardless.
- **Library layout flattened.** One file per Part (`LogicalInduction/<Part>.lean`) rather
  than the Mathlib `<Part>.lean` + `<Part>/` roll-up idiom, since each Part currently has
  a single file. Promote a Part to the directory idiom when it grows multiple files
  (`Properties` will be first).
