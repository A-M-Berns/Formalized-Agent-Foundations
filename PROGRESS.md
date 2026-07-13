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
| M3 | Downstream property slice + LUV bridge + integration test | **implementation complete; pending Anson's statement read-through and fresh-context audit** — proved and axiom-clean: `thm:provind`, all three `thm:lc` bullets, both `thm:lex` forms, `thm:con`, both directions and limit forms of `thm:nd`, `lem:conluvapprox`, and `thm:ec` (including every exploiting trader's `EfficientlyComputableTok` certificate). The integration test discharges both the fixed-sentence provability hypothesis and concrete LUV expectation convergence. Stated and deliberately moved to M4 per G1/G2: `thm:ei`, `thm:loe`, `thm:expprovind`, `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st` — exactly the seven remaining Lean `sorry`s. No M3 proof or e.c. certificate remains deferred. |
| M4 | Affine master + reusable LUV lift; close expectation/Self-Trust statements | **in progress (2026-07-13)** — trust-surface audit repaired the seven parked signatures and restored computable rational-market/process certificates on `IsLogicalInductor`. The affine core and the conditional repeatable-ROI construction are proved. `EF.var`/`EF.letE` provide faithful shared straight-line syntax; the shared `β₀…βₙ` program is denotationally correct, rank-legal, non-duplicating, and uniformly token-emittable. `PolyTradeEmulatable` exposes honest polynomial trade boundaries, and `sharedBudgetedTrader_ecTok` reaches `EfficientlyComputableTok`. The semantic budget argument is closed under an explicit polynomial maturity schedule and a uniform positive component-magnitude floor. The paper-facing `lem:type3` interface still needs (i) sparse/frequently-positive magnitudes and (ii) construction of that maturity schedule from the computable market/process certificates. Only after those gates close is the hub ready for `thm:affpolymax` and the seven expectation/Self-Trust statements. |
| M5–M7 | see roadmap | not started (Brouwer `lem:fpl` already proved — M6 gate cleared) |

**M3 update (2026-07-12, certificate closure):** all three outstanding e.c. certificates
are discharged. `excTrader_ecTok` and `LUV.expect_converges` are axiom-clean; the latter now
explicitly requires `LUV.PolyThresholdCodes`, the disclosed compact-code interface for the
paper's Θ-definable threshold family. The only remaining Lean `sorry`s are the seven intended
M4 statements. **Phase F is complete:** the ledger and inventory below are current, the
integration and full builds are green, and the audit handoff is written. M3 now awaits only
Anson's statement read-through and the separately run fresh-context adversarial audit.

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
| `def:ec` (legacy whole-value model) | `EfficientlyComputableVal` | done | **Def** | Retained legacy whole-number emission model. It is faithful only for bounded-depth strategies and is **not** used by `IsLogicalInductor`; the active paper-facing definition is `EfficientlyComputableTok` below. |
| `def:ec` (flat encoding) | `EF.serialize`, `serializeTrades` | done | Def | **flat postfix (RPN) token stream** for a feature / strategy — the poly-*size* encoding replacing whole-number `toNat` emission. Length `Θ(node count)` (`serialize_length_le_cost`), tokens small (tags `0..5`/`6`, day indices, atomic `⌜φ⌝`/`⌜q⌝` codes). Resolves OPEN RISK 4's encoding wall |
| `def:ec` (honesty) | `EF.serialize_injective`, `serializeTrades_injective` (via stack machine `EF.readM` + roundtrips) | done | **P** | **the token stream determines the feature/strategy** — RPN is not prefix-free but *is* uniquely decodable; one `readM` roundtrip induction gives both. Guards against "emitting tokens" being a non-faithful representation. Axiom-clean (3 standard) |
| `def:ec` (size faithfulness) | `EF.serialize_length_le_cost` | done | **P** | `(serialize e).length ≤ 3·cost e` — poly-*size* ⇔ poly-*length*, the property that makes deep poly-size features admissible under `…Tok`. Axiom-clean |
| `dd:fuel` (dispatch) | `iterRight`, `sel`, `selFn`, `tupleEnc`, **`iterRight_evaln`** | done | Def+**P** | **runtime index selection** `sel ⟨T,i⟩ = left (right^i T) = tupleEnc⁻¹[i]`, via one genuine `Code.prec` recursion on `i` (the 2nd such in the file, after `predc`). Fuel bounded degree-2 in `pair T i` through the clocked interpreter. `selFn_tupleEnc`: selection correct on a right-nested tuple. Axiom-clean. **Scope: fixed (small) tuples only** — a right-nested tuple of a length-`Θ(n)` stream has *doubly-exponential value*, so `sel` cannot rescue varying-length emission (that needs per-index arithmetic, below) |
| `dd:fuel` (branch primitive) | `ifzSel`, `ifzSelFn`, **`ifzSel_evaln`**, `ifzSel_polyFueled` | done | Def+**P** | **branchless zero-test selector** `ifzSel ⟨pair A B, i⟩ = if i=0 then A else B` — one `Code.prec` (3rd in file) with projection-only `cf`/`cg` (`left`, `comp right left`; candidates ride in the input, no `const` in the recursion, so the fuel proof is as cheap as `iterRight`'s), degree-2 fuel. **The bottleneck primitive for varying-length (deep-trader) emission:** a size-`Θ(n)` strategy's `i`-th token is a fixed nesting of `ifzSel`s over `pred`-shifted indices. Axiom-clean |
| `dd:fuel` (subtraction) | `subAux`, `subAux_cg_eval`, `subAux_step`, **`subAux_evaln`**, `subc`, `subc_fueled`, `subc_polyFueled` | done | Def+**P** | **truncated subtraction** `subc ⟨a,b⟩ = a − b` — the one **nested** `Code.prec` in the file (recursive step applies `predc`, itself a `prec`), so the fuel proof composes `predc`'s degree-4 budget across `b` levels (explicit bound `32(a+1)⁴ + pair a (pair b a) + a + b + 9`). Completes the arithmetic toolkit (`ifzSel` branch + `predc` decrement + `subc` compare + `sel` fixed-select) for varying-length emission: a deep trader's trailing `[6,⌜φ⌝]` frame is at an `n`-dependent stream position, so emitting it needs `subc` to compare against `n`. Axiom-clean |
| `def:ec` (varying-length workhorse) | **`ecTok_of_tokenFn`** | done | **P** | the **generalization of `ecTok_of_tokenList` to growing streams**: a trader is `EfficientlyComputableTok` as soon as one poly-fueled `tokenFn` computes the `i`-th token of `serializeTrades (strat n)` from `⟨n,i⟩` and the stream length is poly. The missing helper for deep (size-`Θ(n)`) traders — their `i`-th token is a fixed arithmetic expression in `⟨n,i⟩` (from `ifzSel`/`predc`/`subc`), not a fixed-list lookup. Fuel: `PolyFueled` gives `bc ⟨n,i⟩`; a monotone poly bound with `i < len n ≤ poly` gives poly-in-`n`. Axiom-clean. **Closes the tooling gap flagged when the fixed-length limit was found** |
| `def:ec` (deep-trader validation) | `srChain`, `deepTrader`, `serialize_srChain`, `deepStream_getD`, **`deepTrader_ecTok`** | done | **P** | **the first genuinely size-`Θ(n)` trader certified `EfficientlyComputableTok`** — `srChain n = safeRecip^n(const 1)` is a depth-`n` feature whose `serialize` is `[1,⌜1⌝] ++ replicate n 5` (a *growing* stream the old whole-number `def:ec` could not emit: its `toNat` is `~2^{2^n}`). Its `i`-th token is a fixed nesting of `ifzSel` over `predc`/`subc`-shifted indices; certified via `ecTok_of_tokenFn`. This is the end-to-end payoff of the `ifzSel`/`subc`/`ecTok_of_tokenFn` toolkit — proof the redefinition's new admissions are real and usable. Axiom-clean |
| `dd:fuel` (poly-closure) | `IsPolyBounded.comp`/`.add`, `PolyFueled.comp`/`.left`/`.right`, `sel_polyFueled` | done | **P** | **`PolyFueled` now closed under composition** (was only `pair`/`succ_comp`) — needed `IsPolyBounded.comp` (poly∘poly = poly). Lets the token-emitter `comp sel ((comp cV left).pair right)` be assembled and its poly fuel drop out automatically. Axiom-clean |
| `def:ec` (re-cert workhorse) | **`ecTok_of_tokenList`**, `PolyFueledTuple` (+`nil`/`cons`) | done | **P** | the reusable lemma: a trader whose day-`n` stream is a **fixed-length** list `ts.map (·n)` of poly-fueled tokens is `EfficientlyComputableTok`. Emitter builds the tuple (`cV`) then selects index `i` (`sel`); fuel poly-in-`n` via `pair n i < (n+L+1)²` and `i < L`. This is the M2-analogue "wire the whole e.c. pipeline once" for the token model. Axiom-clean. **Scope: fixed-length only** — every existing trader has a bounded-shape strategy (constant stream length, only leaf values vary). A genuinely deep trader (size-`Θ(n)`, e.g. `thm:con` hysteresis / `thm:nd` counter) has a stream length that *grows* with `n`; the **`def` admits it** (length clause allows poly growth) but this workhorse does **not** — that needs a varying-length emission helper (not yet built). So OPEN RISK 4 is resolved at the definition/trust-surface level; deep-trader e.c. still needs both the trader and a varying-length cert path |
| `def:ec` (Tok validation) | `priceTrader_ecTok` | done | **P** | the responsive `priceTrader φ` (stream `[0,⌜φ⌝,n,6,⌜φ⌝]` with the *varying* `n` token = `PolyFueled.id`) re-certified under the new def — validates the pipeline end-to-end; the template the property-file re-certs follow. Axiom-clean |
| `def:ec` (compositional re-cert) | `PolyTokenStream` (+`nil`/`append`/`const`/`idTok`/`polyTok`/`serialize_{price,const,add,mul,max}`/`trades_cons`/`trades_nil`), `ecTok_of_stream` | done | **P** | the layer that makes deep-trader re-cert tractable: `PolyTokenStream s` = "`s n` is `ts.map(·n)`, tokens poly-fueled", **closed under append**, so a re-cert mirrors the trader's `serialize` tree via combinators (no hand-written token list). `serialize_*` = one per `EF` constructor. Axiom-clean |
| `def:ec` (re-cert, all 7 traders) | `buyDaily_ec`, `sellDaily_ec`, `buySeq_ec`, `priceTrader_ecTok`, `exclTr_ec`, `eqTr_ec`, `impTr_ec` (+ `gapEF_stream`/`sigEF_stream`/`gap2EF_stream`/`sig2EF_stream`/`impSig_stream`) | done | **P/C** | **every existing trader re-certified under `EfficientlyComputableTok`** — the constant ones directly, the deep responsive ones (`exclTr`/`eqTr`/`impTr`, ~40–60-token streams) via `PolyTokenStream` combinator trees. Names kept, so property-proof call sites are unchanged. All axiom-clean |
| `dd:fuel` (generic prec closure) | `evaln_prec_zero`/`_succ`, **`evaln_prec`**, **`PolyFueled.prec`**, `PolyFueled.of_eq` | done | **P** | **the per-code fuel proofs are over** — the induction that `predAux_evaln`/`iterRight_evaln`/`ifzSel_evaln`/`subAux_evaln` each hand-rolled is done once, generically: `evaln_prec` runs any `prec cf cg` with `Fueled` base/step within `B + i` fuel (`B` a monotone majorant of every level's budget/guard), and `PolyFueled.prec` closes `PolyFueled` under `Code.prec` whenever the iterated state is poly-bounded. Deviation from the Phase-A plan (which called for a 5th bespoke `subAux_evaln`-style proof for `divmodc`): same accounting, done once — every future primitive-recursive combinator is now a corollary with zero new `evaln` reasoning. Axiom-clean |
| `dd:fuel` (arith corollaries) | `addc_polyFueled`, `PolyFueled.addConst`, `mulc_polyFueled`, **`divmodc_polyFueled`** (Phase A1) | done | **P** | `⟨a,b⟩↦a+b`, `n↦n+K`, `n↦n·W`, and **division/remainder by a constant width `w>0`** (`n ↦ ⟨n/w, n%w⟩`) — each a few-line `PolyFueled.prec` instance (divmod: state `⟨q,r⟩`, wrap test `(w−1)−r` via `subc` dispatched by `ifzSel`; constant `w` baked into the code per-width, as planned). `divmodc` is the block-index/offset primitive for repeating-block emission (Phase A2); `addc`/`mulc` are the offset arithmetic the region dispatch needs. All axiom-clean |
| `def:ec` (block workhorse, Phase A2) | `length_flatMap_const_width`, `getD_flatMap_const_width`, **`ecTok_of_blockStream`** | done | **P** | **repeating-block emission**: a trader whose day-`n` stream is `head.map (·n) ++ (range (cnt n)).flatMap (fun j => bs.map (·⟨n,j⟩)) ++ tail.map (·n)` — fixed head/tail, `cnt n` fixed-width-`W` blocks of poly-fueled tokens of `⟨n,j⟩`, `cnt` poly-fueled — is `EfficientlyComputableTok`. Emitter: region dispatch by `subc` tests through `ifzSel`, block index/offset by `divmodc`, in-region select by `sel`; tail offset needs `addc`/`mulc` (`i − (H + cnt n·W)`). This is the emission shape of **every remaining deep trader** (`thm:con` hysteresis, `thm:nd` pow-chains, D2 bundles). Axiom-clean |
| `def:ec` (segment layer, Phase C4) | `PolySegStream` (+`of_eq`/`ofTokenStream`/`append`/`blocks`), **`ecTok_of_segStream`**, `PolyTokenStream.serialize_price_comp` | done | **P** | **compositional emission**: a `PolySegStream` carries a poly-fueled emitter *and* a poly-fueled runtime length, so multi-segment streams compose — `append` dispatches on the runtime boundary (`subc`/`ifzSel`), `blocks` is the `divmodc` repeating-block case, `ofTokenStream` the fixed-tuple case. Built because the hysteresis trade serializes to **five** segments (two block runs interleaved with fixed frames), which the single-flatMap `ecTok_of_blockStream` cannot express. Any future multi-segment trader (B2 budget chains, D2 bundles) composes from these. Axiom-clean |
| `def:ec` (block validation, Phase A3) | `histSum`, `histSum_rank`, `histTrader`, `serialize_histSum`, **`histTrader_ecTok`** | done | **P** | worked size-`Θ(n)` example whose blocks **contain the day index**: `histSum φ n = Σ_{k<n} φ*ᵏ` (left-nested adds; stream `[1,⌜0⌝] ++ n×[0,⌜φ⌝,k,2] ++ [6,⌜φ⌝]`), traded daily, certified via `ecTok_of_blockStream` with the `k` token = `PolyFueled.right` of the block input `⟨n,k⟩`. Direct dress rehearsal for Phase B/C emissions. Axiom-clean |
| `def:ec` (poly-size model) | `EfficientlyComputableTok` | done | **Def** (**wired into `def:lic`**) | **token-indexed emission:** `∃ c a k, (∀n, len(serializeTrades strat n) ≤ poly) ∧ ∀ n i < len, evaln poly c ⟨n,i⟩ = some (token i)`. The faithful poly-*size* `def:ec` — emits the flat stream one token at a time, so deep poly-size traders (hysteresis, counters) are admissible. Verified against Mathlib source: `evaln`'s input guards cap a fixed code's output value at `poly(fuel)`, so whole-number emission of *any* injective packing fails; token-indexing is the fix. **Residual type-`(c)`:** token *values* ≤ `poly n`, so `⌜φ⌝` must be `poly n`-value (fixed sentences constant; varying-φ traders and LUV thresholds carry explicit polynomial-code interfaces). `IsLogicalInductor` has quantified over this definition since the OPEN RISK 4 switch. |
| **`def:lic`** | `IsLogicalInductor` (class over `P`, `DP`) | done | Def | "no e.c. trader exploits `P`". The property-tail hypothesis. **Now quantifies over `EfficientlyComputableTok`** (the faithful poly-*size* model), so it forbids deep poly-size exploiters too — matches the paper (OPEN RISK 4 resolved) |
| `def:trader` (M2) | `buyDaily` (buys 1 share of `φ`/day) | done | **C** | the **constructed** exploiting trader for the base case of `thm:provind`. Real EF (`[(const 1, φ)]`), not a stub |
| `def:ec` (M2 cert) | `buyDaily_ec` | done | **P** | e.c. discharged via the faithful clocked model: constant strategy ⇒ `Code.const`, affine fuel via `evaln_const_self`. Axiom-clean |
| `def:exploitation` (M2) | `buyDaily_exploits` | done | **P** | full proof: BddBelow (net worth ≥ 0 in every plausible world) ∧ ¬BddAbove (≥ (m+1)ε → ∞). No `sorry`; `#print axioms` = the 3 standard only |
| `def:luv` | `LUV` (threshold sentences `gt : ℚ → Sentence`) | done | Def | **disclosed type-`(c)`:** LUVs are first-order (formula free in one var over Θ-rep-computations); we model the `[0,1]`-LUV by its market-observable content = its threshold-sentence family `⌜X>r⌝`. No first-order syntax reconstructed |
| `def:ec` (M4 families) | `PolySentenceCodes`, `PolyRatCodes`, `LUV.PolyThresholdCodeSeq`, `PGenerableRat` | done | **Def** | Legal varying-family interfaces missing from the M3 statement-only forms. They expose polynomially fueled sentence/rational codes, triple-indexed threshold codes `⌜Xₙ>i/k⌝`, and the paper's market-generated rational sequences as polynomial-size EF progressions. Without these, arbitrary Lean functions can encode uncomputable diagonals no legal trader can follow. |
| `def:affcomsen` (M4 core) | `AffineCombination`, `.value`, `.price`, `.magnitude`, `.buy`, `.scale`, `.neg`; `buy_value`, `scale_value` (`Affine.lean`) | done | **Def+P** | Syntax `c+Σeᵢφᵢ`; buying omits the constant because it cancels, and is proved to value exactly as `world(A)−priceₙ(A)`. Scaling/negation laws and magnitude nonnegativity are axiom-clean. Base object for `thm:affpolymax`. |
| `def:e` | `LUV.expectApprox`, `.expect`, `.expectSeq`, `.expectInf`; `expect_mem_Icc` | done | Def+P | `𝔼ₙ(X)=(1/n)∑_{i<n}Pₙ(⌜X>i/n⌝)` — the **concrete `ℕ→ℝ` expectation** the deference corpus abstracts as `E^H_n(X)`. Bounds `∈[0,1]` proved. **This is the LUV-bridge object that closes the price→expectation level gap** |
| `thm:ec` (D2) | feature-generic layer `buyIndF`/`sellIndF`/`hystChain` (+ facts 1–3, variation `hcDelta`/`hcBpos`/`hcBneg`/`hcBneg_unbounded`), `LUV.thresholdSumEF`/`expectEF`, gated signals `excPad`/`excBuy`/`excSell`, bundle trader `excTrader`, `excTrader_netWorth_ge`, `excBneg_unbounded`, `excTrader_exploits`, `excTrader_ecTok`, **`LUV.expect_converges`** (`Properties/ExpectationConvergence.lean`) | **done — axiom-clean** | **C** | **Expectations Converge**: `𝔼ₙ(X)` converges for every `[0,1]`-LUV satisfying the explicit compact-code interface `LUV.PolyThresholdCodes`. `thm:con`'s hysteresis re-run on the expectation feature trades the day-`n` threshold bundle `{(1/n)·⌜X>i/n⌝}_{i<n}`. `lem:conluvapprox` controls the payout mismatch; a start-day gate absorbs its error. Hypotheses `hcons` and `hval` disclose the propositional import of "Θ represents computations" (principled witness: M7). The exploiting trader and its variable-width token-emission certificate are both discharged. |
| `lem:conluvapprox` (single-LUV, D1) | **`PCWorld.ValuesAt.expectApprox_near`** (`Expectations.lean`) | done | **P** | a world valuing `X` at `x` assesses `𝔼ₙ` within `1/n` of `x` (in fact one-sidedly: `x ≤ 𝔼ₙ ≤ x + 1/n`). Pure counting: thresholds `i/n < x` pay 1 (`≥ ⌈nx⌉ ≥ nx` of them, using `x ≤ 1`), thresholds `> x` pay 0 (sum `≤ ⌊nx⌋+1 ≤ nx+1`; the possible threshold `= x` is the `+1` slack — `ValuesAt` deliberately says nothing at `r = x`). `Nat.floor`/`ceil` sandwich, no filter cards. Hypothesis `0 < n` (at `n = 0`, `𝔼₀ = 0` and `1/0 = 0` in ℝ — the bound is false). The combination (`b/n`) form for affine LUVs → M4 per the plan. Axiom-clean |
| `thm:ec` (`def:ec` cert closure) | `LUV.PolyThresholdCodes`, `PolySegStream.concatVar`, **`excTrader_ecTok`** | **done — axiom-clean** | **P** | `PolyThresholdCodes` emits `⌜X>i/n⌝` from `⟨n,i⟩` with polynomial fuel (faithful type-`(c)` interface for compact Θ-definable LUV syntax). `concatVar` uses polynomially fueled prefix sums and a primitive-recursive locator for genuinely variable-width historical blocks. Inner threshold sums use fixed-width `blocks`; the outer trade bundle uses uniform `concat`. Varying `1/n` and gated rational constants are emitted by closed encoding arithmetic. |
| `def:luv` (world values, D1 modeling) | `PCWorld.ValuesAt` (`Expectations.lean`) | done | **Def** | "world `v` values LUV `X` at `x`": threshold coherence — `v` affirms `X.gt r` for every `r < x`, denies it for every `r > x`, `x ∈ [0,1]`. **Disclosed type-`(c)`:** the market-observable rendering of the paper's "Θ represents computations ⇒ consistent worlds assign LUVs their values"; no first-order syntax. Substrate for `lem:conluvapprox` (Phase D1) and every Self-Trust linkage hypothesis |
| `def:luv` (indicator, relational) | `LUV.IsIndicator` (`Expectations.lean`) | done | **Def** | **relational rendering of the paper's `1(φ)`** (D3 principle): `Y` is an indicator family iff plausible worlds hold its sub-0 thresholds, tie its `[0,1)` thresholds to `φ`, and refute its ≥1 thresholds. *Deliberately not a canonical construction*: defining `gt r := φ` on `[0,1)` would make `thm:ei` definitional — the theorem's content is the inductor learning the growing bundle of equivalences. Audit bait: check this linkage isn't conclusion-shaped |
| `thm:ei` | `lic_expectation_indicator`; `LUV.IsIndicator.valuesAt` | **stmt (sorry); world linkage proved** | **P pending** | Signature repaired for M4: adds `PolyThresholdCodes`, `[0,1]` prices, and daily plausible worlds. The old form was false for an inconsistent `DP` (all linkages vacuous, every history satisfies `def:lic`). `valuesAt` proves the relational indicator really has world value `payout φ`. Bundle proof remains. |
| `thm:loe` | `lic_linearity_of_expectation` | **stmt (sorry)** | — | Signature repaired with compact codes, price bounds, daily plausible worlds, and non-vacuous simultaneous `ValuesAt` witnesses; otherwise the affine linkage can be vacuous. Fixed `X,Y,Z` proof remains assigned to the M4 LUV hub. |
| `thm:expprovind` | `lic_expectation_provind` | **stmt (sorry)** | — | Signature repaired with compact codes, price bounds, and daily plausible worlds. Single-LUV form: plausible worlds value `X ≥ c` ⇒ `𝔼(X) ≳ₙ c`. Proof remains M4. |
| `def:deferralfunc` | `DeferralFunction` (`Properties/SelfTrust.lean`) | done | **Def** | `f n > n` + a code computing `f` within fuel polynomial **in `f n`** (the paper's "time poly in `f(n)`", faithfully weaker than poly-in-`n`), via the clocked interpreter (`dd:fuel`). Both paper conditions carried, none added |
| `def:ctsind` (real form) | `ctsInd` (`Properties/SelfTrust.lean`) | done | **Def** | `min 1 (max 0 ((x−y)/δ))` — the paper's continuous threshold indicator on reals (0 below `y`, linear on `(y,y+δ]`, 1 above); used by `thm:st`'s prescribed world-values |
| `thm:cee` | `lic_expected_future_expectations` | **stmt (sorry)** | — | `𝔼ₙ(Xₙ) ≈ₙ 𝔼ₙ(⌜𝔼_{f(n)}(Xₙ)⌝)`, quoted expectation as **relational family** `Y` + revelation-schedule linkage (below). Proof → M4 (G1). |
| `thm:ceu` | `lic_no_expected_net_update` | **stmt (sorry)** | — | `Pₙ(φₙ) ≈ₙ 𝔼ₙ(⌜P_{f(n)}(φₙ)⌝)` (deference-corpus name "cee"). Proof → M4 (paper route: cee + ei). **G2 modeling, all four Self-Trust rows (decision 2026-07-11, "the non-vacuous way"):** (i) *relational quotes* — quoted objects are arbitrary LUV families constrained by `ValuesAt` linkage hypotheses, never canonical constructions (which would pre-discharge the learning content); (ii) *faithful timing* — linkage revealed at a finite schedule day `r n`, **not** by day `n`: the by-day-`n` form's only witnesses are oracle `DP`s knowing the future market (degenerate non-vacuity); the schedule form is dischargeable by M7's construction (computable `LIA` + Θ-represented price facts entering `D` eventually). *Provenance (c)* on the linkage hypotheses: they import the paper's quoting mechanism wholesale; principled witness = M7. **Audit bait, handed over explicitly**: check the linkage hypotheses aren't conclusion-shaped, and that no oracle-`DP` shortcut re-entered |
| `thm:ccee` | `lic_no_expected_net_update_conditional` | **stmt (sorry)** | — | the `w`-weighted form; product LUVs `Z`/`Z'` linked pointwise to `X`'s world-values (`hX` non-triviality + `hZ`/`hZ'` product linkage). `w : ℕ → ℚ` is constrained to `[0,1]` and explicitly carries the paper-required `PGenerableRat P w` witness. Proof → M4 |
| `thm:st` | `lic_self_trust` | **stmt (sorry)** | — | `𝔼ₙ(⌜1(φₙ)·ctsind(P_{f(n)}φₙ > pₙ)⌝) ≳ₙ pₙ·𝔼ₙ(⌜ctsind(…)⌝)`; the indicator-LUV `A n` is valued at `payout(φₙ) · ctsInd(…)` — world-dependent by design (that *is* `1(φ)`). Proof → M4 |
| **integration** (expectation) | `IntegrationTest` Part C | done | **C** | closes the interface level gap: `value_argmax_asymptotic` instantiated with concrete `X.expectSeq P` for all `E_now(·)` slots — the corpus's expectation sequences **are** our objects, no adapter. LI hypotheses still assumed (= `thm:cee/expprovind`, the property-tail work `Expectations` states) |
| **integration** | `IntegrationTest.value_argmax_asymptotic`, `provind_hypothesis_discharged` | done | **C** | roadmap M3 integration test. Reproduces the deference corpus's `value_argmax_asymptotic` in our vocabulary (drop-in ✓ — `DeferenceAsymp.Approx/AsympLE` are *defeq* our `AsympEq/AsympLE`) and discharges a provind-shaped hypothesis `Approx (P·φ) 1` from `lic_deducible_tendsto_one` with no adapter. Axioms clean. **Finding:** interface matches at the *price/asymptotic* level; expectation-level hypotheses (`E^H_n`) still need the LUV bridge (M3/M4) |
| `thm:con` (reduction) | `exists_rat_oscillation_of_not_convergesTo` | done | **P** | non-convergence of a `[0,1]`-price ⇒ a **rational** oscillation (`Pₙφ < a` i.o. ∧ `> b` i.o., `a<b∈ℚ`). Contrapositive of Mathlib `tendsto_of_no_upcrossings` over the dense range of `(↑):ℚ→ℝ` (`Rat.denseRange_cast`); rationality of `a,b` is what lets the arbitrage trader use them as `EF` constants. Hyps `(b)`; axiom-clean (`propext/Choice/Quot`). The "assume-property-fails ⇒ extract-exploitable-config" half of `thm:con`, carried by a library lemma not a hand-roll |
| `thm:con` (hysteresis trader, C1–C4) | `buyIndEF`/`sellIndEF`/`hystN`/`hystTrader` (+ `oneMinus`/`efMin`/`clip01`), `hystTrader_netWorth_ge`, `hystBneg_unbounded`, **`hystTrader_exploits`**, **`hystTrader_ecTok`**, `oscillation_exploitable_hyst` (`Properties/Hysteresis.lean`) | **done — axiom-clean, no sorry** | **P** | the hysteresis trader **built and proved to exploit**: holdings state `H (k+1) = max (H k·(1−sellInd k)) (buyInd k)` (size-`Θ(k)` EF, recursive-branch-first so serialization has the A2 block shape), day-`n` trade `H (n+1) − H n`. C2 accounting *without per-swing induction*: sign-decompose the variation — buys only below `a+δ` (fact 1), sells only above `b−δ` (fact 2) ⇒ `netWorth ≥ (b−a−2δ)·B₋ − (a+δ)` **in every world**; C3: each dip-then-spike swing forces `h: 1 → 0` (fact 3) ⇒ `B₋ → ∞` by induction with two frequently-extractions per step (no interleaved-sequence construction needed). Engine: `exploits_of_bddBelow_of_unbounded`. e.c. discharged through the clocked interpreter via the five-segment `PolySegStream` emission — the first **linear-depth** trader certified under the poly-size `def:ec`, i.e. the exploiter OPEN RISK 4's redefinition existed for |
| `thm:con` (arbitrage) | `oscillation_exploitable` | **done — axiom-clean** | **C** | A rational oscillation plus daily plausible worlds admits an e.c. exploiting trader. It composes the real hysteresis trader `oscillation_exploitable_hyst` with its `EfficientlyComputableTok` certificate; no bounded-depth surrogate or arithmetic stub is used. |
| `thm:con` | `lic_price_convergesTo` | **done — axiom-clean** | **C** | Convergence in the limit: `[IsLogicalInductor] ⇒ ∃L, Pₙφ → L`, for every `φ` (prices in `[0,1]`, daily plausible worlds). Chains the rational-oscillation reduction with the certified hysteresis arbitrage theorem against `def:lic`. |
| exploitation (reusable) | `exploits_of_nonneg_partialSums` | done | **P** | factored engine: a trader whose day-`i` value **in every plausible world** is a fixed nonneg sequence `w i`, with `w ≥ ε` frequently, exploits (BddBelow by 0; ¬BddAbove by subsequence accumulation). Reused by additivity's two directions; the shared core behind `buyDaily`/`sellDaily`-style freq arguments |
| `thm:lc` bullet 3 (additivity) | `exclTr`, `exclTr_value`, `exclTr_ec`, `exclTr_exploits`, **`lic_excl_gap_tendsto_zero`** | done | **C** | **finite additivity, finite-stage form:** `⊢∼(φ∧ψ) ⇒ Pₙ(φ∨ψ)−Pₙφ−Pₙψ → 0` under a logical inductor (⇒ `P∞(φ∨ψ)=P∞φ+P∞ψ` with `thm:con`). Genuinely-constructed **world-neutral portfolio** trader `σ·[(-1,φ∨ψ),(1,φ),(1,ψ)]`: payouts cancel by exclusivity (`payout_or_of_excl`), so day value = deterministic `σ·gap`; continuous buy-signal `max(0,σ·gap−ε/2)` ⇒ bounded-below/unbounded-above (no hysteresis needed). **e.c. genuinely discharged** — first *multi-trade* (3-sentence) responsive trader, via the `Nat.pair`-tree list encoding over `PolyEF` templates (`exclTr_ec`). Both mispricing directions = one `σ`-parametrized trader. Axiom-clean |
| exploitation (≥ variant) | `exploits_of_ge_partialSums` | done | **P** | generalizes `exploits_of_nonneg_partialSums` to a **lower bound**: plausible-world net worth `≥ ∑ w` (nonneg, freq `≥ ε`) ⇒ exploits. The engine for *world-dependent* traders whose value is only bounded below by a world-independent quantity (implication learning) |
| engine (definitional) | `exploits_of_bddBelow_of_unbounded` (`Properties/Basic.lean`) | done | **P** | third exploitation engine: assessments bounded below by `−C` and reaching above every bound ⇒ `Exploits` — a few lines from the definition. For traders whose growth is **world-dependent** (happens only in a sub-family of worlds, e.g. `φ`-worlds), where both partial-sums engines' world-independent `w` fails. Consumed by `thm:nd`; C's hysteresis argument targets it too |
| `thm:nd` (weak fragment) | `twoPowChain`, `ndBeta`, `ndTrader`, `ndTrader_exploits`, `ndTrader_ecTok`, **`lic_nonDogmatism_weak`** (`Properties/NonDogmatism.lean`) | done | **C** | **weak Non-Dogmatism**: prices in `[0,1]` + G3's hypothesis ⇒ `∀ᶠ n, 2^{-(n+2)} ≤ Pₙφ`. Honestly *weaker* than `thm:nd` (bound decays with `n`; the liminf form is B2's budget-halving trader). **G3 disclosure (type-`(c)` on the hypothesis):** the paper's `Θ ⊬ ¬φ` is rendered semantically as "`φ`-satisfying plausible worlds keep existing" (`∀ n, ∃ v, ConsistentWith (D n) ∧ Holds φ`) — the `def:lang`-level reading of `⊬`; per-day, hence weaker hypothesis ⇒ stronger theorem. Awaiting Anson's veto at read-through. Trader real & memoryless (`β n = max 0 (1 − 2^{n+1}·φ*ⁿ)`, spend ≤ 2^{-(n+1)}/day, dips bank ≥ 1/4 in `φ`-worlds); **first Phase-A block-emission e.c. cert on a property trader** (left-nested pow-chain ⇒ homogeneous width-3 blocks; day-index in the tail). Axiom-clean |
| `thm:nd` (positive direction, B2) | `armChain` (+`_mem/_denote_of_le/_shares_sum/_rank`), `ndThr`, `ndPadThr`, `ndBuySig`, `ndShares`, `ndCoef`, `ndLadderEF`, `ndLadderTrader`, `ndLadderTrader_exploits`, `ndLadderTrader_ecTok`, **`lic_nonDogmatism`** (`Properties/NonDogmatism.lean`) | **done — axiom-clean, cert discharged 2026-07-12** | **C** | **full Non-Dogmatism, `Θ ⊬ ¬φ` side**: G3's hypothesis ⇒ `∃ ε > 0, ∀ᶠ n, ε ≤ Pₙφ`. **No price-range hypotheses** (the ladder's economics localize to its trigger bands). Trader = the paper's `app:obu` **scale-ladder** (sketch at `main.tex:1533`), *not* the plan's §6 recursive budget trader — that trader's state update uses the state twice (bare + inside the clip) ⇒ its `EF` **tree is exponential**, and no single-occurrence chain expresses it (single-occurrence recursions are monotone-or-antitone in the state; the budget update isn't). **Disclosed rescaling (dd:fuel):** paper constants `2^{-j}`/`j2^j` have exponential-*value* encodings under the fuel clock; rung `j` here buys ≤ `j³` shares below `1/j³` at weight `1/j²` (coefficient constant `j`), spend ≤ `Σ1/j² ≤ 2`, fired rung banks `≥ j−1`. Rungs padded with degenerate `δ=0` ctsind factors (identically 0, `1/0=0` in ℚ) so all rung chains have uniform width. **e.c. cert discharged** (2026-07-12): `mul_polyFueled`/`divmod1_polyFueled` (runtime arithmetic), `PolySegStream.concat` (n-fold uniform-runtime-width concatenation), and poly-fueled rung-constant emission via the **closed encoding forms** — `encode q = pair (encodeℤ q.num) q.den` is `rfl` through `Rat`'s `ofEquiv` instance, so `⌜ndThr j⌝ = pair 2 (2j³)` etc. are arithmetic (`encode_ndThr`, `encode_thrSum/thrRecip_polyFueled` with `subc`/`ifzSel` pad-live dispatch). First parametric-family emission cert; `lic_nonDogmatism` axiom-clean end-to-end |
| `thm:nd` (dual direction, B2) | `ndSellSig`, `ndSellShares`, `ndSellCoef`, `ndSellLadderEF`, `ndSellLadderTrader`, `ndSellLadderTrader_exploits`, `ndSellLadderTrader_ecTok`, **`lic_nonDogmatism_dual`** (`Properties/NonDogmatism.lean`) | **done — axiom-clean, cert discharged 2026-07-12** | **C** | **full Non-Dogmatism, `Θ ⊬ φ` side**: `φ`-falsifying plausible worlds keep existing (G3's rendering of `Θ ⊬ φ`) ⇒ `∃ ε > 0, ∀ᶠ n, Pₙφ ≤ 1 − ε`. Mirrored **sell** ladder over `sellIndEF` (spike band above `1 − 1/j³`) — *not* the positive direction applied to `∼φ` (prices of `φ`/`∼φ` are unlinked without coherence). Same `armChain` engine, same padding. **e.c. cert discharged** (2026-07-12): mirror of the buy cert, plus the **negative-numerator** band constants (`δ − b` with `b` near `1`): `encode_rat_neg_div` routes through `Int.negSucc` (`⌜−(a/b)⌝ = pair (2(a−1)+1) b`), with a rung-1 branch where the live constant collapses to `0` (`encode_sellB_polyFueled`, nested `ifzSel`). `lic_nonDogmatism_dual` axiom-clean end-to-end |
| `thm:nd` (limit form) | **`lic_limit_pos`**, **`lic_limit_lt_one`** | done — axiom-clean (certs discharged) | **C** | the paper's stated form: with the price convergent (explicit hypothesis, supplied by `thm:con`'s `lic_price_convergesTo` in context), `P∞(φ) > 0` resp. `P∞(φ) < 1`. Pure limit-passage corollaries (`ge_of_tendsto`/`le_of_tendsto`) of the two eventual-bound theorems |
| `thm:lex` (implication) | `impTr`, `impTr_ec`, `PCWorld.payout_le_of_imp`, `impTr_value_ge`, **`lic_imp_eventually_le`** | done | **C** | **Learning logical implication / price monotonicity:** `⊢ φ→ψ` ⇒ eventually `Pₙφ ≤ Pₙψ + ε` (∀ε>0). The sell-`φ`/buy-`ψ` portfolio is **not** world-neutral — value carries a world-dependent `payout ψ − payout φ ≥ 0` (nonneg since `φ→ψ`) atop the deterministic `Pφ−Pψ`, so day value is only *bounded below* by `impSig·(Pφ−Pψ)` (world-independent) — a genuinely new trader pattern, consumed by `exploits_of_ge_partialSums`. Axiom-clean |
| `thm:lex` (equivalence) | `eqTr`, `eqTr_ec`, `PCWorld.payout_eq_of_iff`, **`lic_lex_tendsto_zero`** | done | **C** | **Learning logical equivalence:** `⊢ φ↔ψ` (both `∼φ⋎ψ`, `∼ψ⋎φ` revealed) ⇒ `Pₙφ − Pₙψ → 0` under a logical inductor. Same world-neutral-portfolio pattern as additivity but *two*-sentence `σ·[(1,φ),(-1,ψ)]`: payouts equal by equivalence (`payout_eq_of_iff`), day value = deterministic `σ·(Pφ−Pψ)`; reuses `exploits_of_nonneg_partialSums` + `exclTr`-style buy-signal. e.c. via the `Nat.pair`-tree list encoding. Axiom-clean |
| `thm:lc` bullet 2 (disprovable→0) | `lic_disprovable_tendsto_zero`, `sellDaily`, `sellDaily_exploits_freq`, `PCWorld.payout_of_disprovable` | done | **C** | Limit-Coherence dual: `∼φ` always-deducible ⇒ `Pₙ(φ)→0` under a logical inductor. Mirror **sell** trader (`[(const -1,φ)]`), constant hence e.c.-certified like `buyDaily`; frequently-overpriced accumulation. Foundation Boolean semantics gives `payout φ = 0` in `∼φ`-worlds. Axioms clean. (Bullet 1 = `lic_deducible_tendsto_one`; bullet 3, finite additivity, needs a non-constant/ROI trader — bounded-below fails for a naive constant portfolio — deferred) |
| `thm:provind` (limit, fixed φ) | `lic_deducible_tendsto_one`, `lic_deducible_eventually_ge`, `buyDaily_exploits_freq` | done | **C** | the genuine `≈ₙ 1` limiting form for a *fixed* always-deducible `φ`: **reuses the M2 e.c.-certified `buyDaily`** (no new trader/e.c.) via a frequently-underpricing accumulation argument (`extraction_of_frequently_atTop` + subset-sum). Axioms clean |
| `thm:provind` (sequence form) | `buySeq`, `buySeq_ec`, **`lic_provind_seq`**, `ec_of_polyEF_seq` | done | **C** | the `𝓔𝓒`-sequence form: for an **efficiently computable sequence** of sentences `φₙ` each deducible by day `n`, `Pₙ(φₙ) → 1`. Same constant buy trader indexed by the sequence; the new ingredient is e.c. of a **varying-sentence** trade, discharged by `ec_of_polyEF_seq` from the `𝓔𝓒`-sequence hypothesis `hφ : PolyFueled cφ (n ↦ ⌜φₙ⌝)`. Exploitation via the reusable `exploits_of_nonneg_partialSums` (world-value `1−Pₙφₙ`, `φₙ ∈ D n ⊆ D m` gives payout 1). Axiom-clean. Generalizes the fixed-`φ` form |
| `thm:provind` (base case) | `lic_deducible_price_near_one` | done | **C** | the loop closed against `def:lic`: under `[IsLogicalInductor]`, an always-deducible `φ` has `1−ε < Pₙφ` for some n, ∀ε>0. **Special case** (always-deducible, uniformly underpriced); general `thm:provind` is M3 |
| `def:tradermag` | `Strategy.magnitude`, `Trader.magnitude`, `abs_value_le_magnitude` | done | Def+P | magnitude + the `\|value\| ≤ magnitude` bound proved (needs `[0,1]` prices + `{0,1}` world) |
| `def:roi` / repeatable ROI | `HasROI`; `Trader.Matured`; `EfficientlyEmulatable`; `PolyTradeEmulatable`; `ROIBudget.weight`, `sharedFeatureWeight`, `sharedBudgetedTrader`, `repeatableROI` (`Engine.lean`, `ROI.lean`) | **done — semantic + faithful e.c. hub** | **Def+P** | Complete Appendix A.2-style closure. `sharedFeatureWeight` binds each `βᵢ` once and has semantic, rank, exact-cost, and uniform-emission proofs. `sharedBudgetedTrader_polySeg` performs nested variable-width trade/component concatenation and `sharedBudgetedTrader_ecTok` closes `def:ec`. Semantically, `tail_magnitude_le_of_matured` and `netWorth_lower_of_matured` charge each closed tail to a summable tolerance; `activeAllocation_le_one` bounds current downside; `allocationPrefix_not_bddAbove` proves budget recycling is unbounded from eventual closure and a uniform positive magnitude floor. `repeatableROI` packages the same constructed trader as both `EfficientlyComputableTok` and `Exploits`. A computable maturity schedule remains an explicit premise (`PolyActiveSchedule` + `MaturitySchedule`), rather than being inferred from the bare noncomputable `DeductiveProcess`. |
| **`def:tf`** | `EF` (inductive), `EF.denote`, `EF.cost`, `EF.rank` (`Criterion.lean`) | done | Def | keystone DSL: price/const/add/mul/max/safeRecip. `denote` noncomputable (ℝ inv); `cost` = structural node count — **disclosed `dd:fuel` deferral:** precise unary day/code charging tying `cost` to poly-runtime is M2, when the trader e.c. cert first consumes it |
| `def:tf` (continuity) | `EF.continuous_denote` | done | **P** | continuity **proved** for the whole DSL (not left as a stated constraint), by induction; safeRecip via `max 1 · ≥ 1 > 0`. Hyps `(b)` (Mathlib `continuous_apply`/`Continuous.{add,mul,max,inv₀}`). This is what breaks the price/trade circularity for Brouwer |
| `def:tf` (ring) | `EF.ExpressibleRankLE`/`EFn`, `CommRing (EFn n)` | done | **P** | `𝔼_n` realized as a **`Subring` of `History → ℝ`** (features are functions): carrier `{denote e \| rank e ≤ n}`, closure under `+,×,neg` proved; `CommRing` inherited. Faithful to the paper's "𝔼_n is a commutative ring" `(b)` |
| `def:tf` (non-vacuity) | `EF.exMaxDiff` + 2 `example`s | done | **N+** | the paper's `max(0, φ*6−ψ*7)`: rank `= 7` and value `= 0.3` at the paper's inputs; plus safeRecip lands in `(0,1]` for all args. Genuine (non-constant) witnesses |
| `lem:fpl` (dep) | `brouwer_fixed_point` | **done** | P | **proved from scratch** (Sperner/Kuhn over the Freudenthal triangulation → fixed point on compact convex `K ⊆ EuclideanSpace ℝ (Fin d)`). Provenance: **autoformalized by Harmonic's Aristotle** (runs `1d7dc5e0`/`c712e6d9`, built there on Lean/Mathlib v4.28.0), dropped in verbatim modulo namespace + header, **revalidated on this project's toolchain** (v4.28.0-rc1, Mathlib master@58d8468): builds green, `#print axioms` = `propext, Classical.choice, Quot.sound` (checked in-file). Trust surface = the final statement only (unchanged from the M0 `sorry` version); the ~1300-line `BrouwerProof.*` interior is machine-generated proof plumbing nobody has read — the kernel has checked it, a human has not, which is exactly the division of labor the standard permits. Imports trimmed from the Aristotle original's `import Mathlib` umbrella to the 7-module minimal set found by `linter.minImports`. |

## M3 statement inventory and audit handoff

Flat inventory for Anson's statement read-through. These are the milestone-facing declarations;
implementation helpers and trader certificates are mapped to them in the node ledger above.
`done` means kernel-checked without `sorryAx`; `M4 statement` means its type is intentionally
present but its proof is one of the seven remaining `sorry`s.

- `lic_deducible_price_near_one` — `Properties/ProvabilityInduction.lean:94` — base finite-stage provability-induction contradiction (`done`).
- `lic_deducible_eventually_ge` — `Properties/ProvabilityInduction.lean:164` — an always-deducible fixed sentence is eventually priced above every `1−ε` (`done`).
- `lic_deducible_tendsto_one` — `Properties/ProvabilityInduction.lean:179` — fixed-sentence `thm:provind`, price converges to one (`done`).
- `lic_provind_seq` — `Properties/ProvabilityInduction.lean:230` — efficiently computable sentence-sequence form of `thm:provind` (`done`).
- `lic_disprovable_tendsto_zero` — `Properties/Coherence.lean:108` — `thm:lc` bullet 2, always-disprovable prices converge to zero (`done`).
- `lic_excl_gap_tendsto_zero` — `Properties/Coherence.lean:306` — `thm:lc` finite additivity gap tends to zero for exclusive disjuncts (`done`).
- `lic_limit_additive` — `Properties/Coherence.lean:337` — limiting beliefs are additive once the three price limits are supplied (`done`; `thm:con` supplies them).
- `lic_lex_tendsto_zero` — `Properties/Relationships.lean:144` — logically equivalent sentences acquire asymptotically equal prices (`done`).
- `lic_imp_eventually_le` — `Properties/Relationships.lean:261` — logical implication gives asymptotic price monotonicity (`done`).
- `exists_rat_oscillation_of_not_exists_convergesTo` — `Properties/Convergence.lean:20` — bounded nonconvergence yields rational upcrossings (`done`).
- `exists_rat_oscillation_of_not_convergesTo` — `Properties/Convergence.lean:33` — price-specialized rational-upcrossing reduction (`done`).
- `oscillation_exploitable_hyst` — `Properties/Hysteresis.lean:597` — the constructed, e.c.-certified hysteresis trader exploits rational oscillation (`done`).
- `oscillation_exploitable` — `Properties/Convergence.lean:56` — packages the hysteresis exploiter in the convergence interface (`done`).
- `lic_price_convergesTo` — `Properties/Convergence.lean:72` — every bounded logical-inductor price sequence converges (`done`).
- `lic_nonDogmatism_weak` — `Properties/NonDogmatism.lean:254` — preliminary day-dependent lower bound under the semantic rendering of `Θ ⊬ ¬φ` (`done`).
- `lic_nonDogmatism` — `Properties/NonDogmatism.lean:948` — full uniform positive lower bound under persistent `φ`-satisfying plausible worlds (`done`).
- `lic_nonDogmatism_dual` — `Properties/NonDogmatism.lean:1512` — full uniform upper bound below one under persistent `φ`-falsifying plausible worlds (`done`).
- `lic_limit_pos` — `Properties/NonDogmatism.lean:1532` — the convergent limit is positive in the non-dogmatism positive direction (`done`).
- `lic_limit_lt_one` — `Properties/NonDogmatism.lean:1542` — the convergent limit is below one in the dual direction (`done`).
- `PCWorld.ValuesAt.expectApprox_near` — `Expectations.lean:117` — `lem:conluvapprox`, a coherent world's threshold-bundle assessment lies within `1/n` of its LUV value (`done`).
- `LUV.expect_converges` — `Properties/ExpectationConvergence.lean:992` — `thm:ec`, concrete LUV expectations converge under the compact threshold-code and world-value interfaces (`done`).
- `lic_expectation_indicator` — `Expectations.lean:232` — expectation of a relational indicator tracks the sentence price (`M4 statement`, `thm:ei`).
- `lic_linearity_of_expectation` — `Expectations.lean:241` — world-linked affine combinations become asymptotically linear in expectation (`M4 statement`, `thm:loe`).
- `lic_expectation_provind` — `Expectations.lean:252` — a world-level lower bound forces the corresponding expectation lower bound (`M4 statement`, `thm:expprovind`).
- `lic_expected_future_expectations` — `Properties/SelfTrust.lean:72` — current and quoted future expectations agree asymptotically (`M4 statement`, `thm:cee`).
- `lic_no_expected_net_update` — `Properties/SelfTrust.lean:83` — current prices agree with expectations of their quoted future prices (`M4 statement`, `thm:ceu`).
- `lic_no_expected_net_update_conditional` — `Properties/SelfTrust.lean:100` — conditional/weighted expected future expectations agree (`M4 statement`, `thm:ccee`).
- `lic_self_trust` — `Properties/SelfTrust.lean:122` — continuous-threshold self-trust inequality (`M4 statement`, `thm:st`).
- `provind_hypothesis_discharged` — `IntegrationTest.lean:71` — plugs fixed-sentence provability induction directly into the deference asymptotic interface (`done`).
- `expectation_convergence_discharged` — `IntegrationTest.lean:105` — plugs concrete `thm:ec` into the expectation-level integration interface (`done`).
- `value_argmax_asymptotic` — `IntegrationTest.lean:50` — reproduces downstream deference algebra in this project's asymptotic vocabulary (`done`; its M4 expectation hypotheses remain explicit).

Definitions and modeling interfaces in the same read-through:

- `LUV` — `Expectations.lean:33` — a `[0,1]` LUV represented by its rational threshold-sentence family.
- `LUV.PolyThresholdCodes` — `Expectations.lean:43` — compact Θ-syntax interface: polynomially fueled emission of `⌜X > i/n⌝`.
- `LUV.expectApprox` / `expect` / `expectSeq` — `Expectations.lean:50`, `:54`, `:60` — finite threshold sum, day expectation, and expectation sequence.
- `PCWorld.ValuesAt` — `Expectations.lean:104` — relational threshold coherence between a world, an LUV, and a real value.
- `LUV.IsIndicator` — `Expectations.lean:223` — relational, non-canonical rendering of the paper's `1(φ)`.
- `DeferralFunction` — `Properties/SelfTrust.lean:45` — strict deferral plus a clocked computation polynomial in `f(n)`.
- `ctsInd` — `Properties/SelfTrust.lean:60` — real-valued continuous threshold indicator.
- Self-Trust reflection hypotheses — inside `Properties/SelfTrust.lean:72`, `:83`, `:100`, `:122` — revelation-schedule `ValuesAt` linkages for quoted expectations, prices, products, and confidence indicators; these are hypotheses rather than canonical quote constructors.

Fresh-context audit is still a separate human/session gate: the proof-writing context must not
perform it. Give the auditor the API table in `notes/next-session.md` §2 and this inventory.
Known audit bait: (1) relational `ValuesAt`/`IsIndicator` linkages must not encode their
conclusions; (2) Self-Trust reflection hypotheses must preserve delayed revelation and must not
smuggle back an oracle-`DP` witness; (3) Non-Dogmatism's persistent-world hypotheses are the
type-`(c)` rendering of `⊬`; and (4) exploitation-engine hypotheses must be reusable facts, not
inequalities tailored to a single trader. Until that fresh audit and Anson's read-through land,
M3 is implementation-complete but not human-audit-complete.

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
  *growing* streams; the **definition** admits them (poly-length clause), and the varying-length
  **tooling is now also complete** — `ifzSel`/`predc`/`subc` + `ecTok_of_tokenFn`, validated by
  the worked size-`Θ(n)` example `deepTrader_ecTok`. So both the trust surface *and* the e.c.
  machinery are done; the only downstream work left for `thm:con`/`thm:nd` is each trader's
  economic construction + exploitation proof. **Residual (small, disclosed, type-`(c)`):** each token's *value* is
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
