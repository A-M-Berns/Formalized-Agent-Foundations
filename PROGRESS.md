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
| M3 | Downstream property slice + LUV bridge + integration test | **sequence-provability defect repaired during M5 (2026-07-13)** — `lic_provind_seq` remains the valid same-day support lemma, while the new `lic_provind` is the faithful paper theorem for arbitrary e.c. theorem/disprovable sequences whose individual deductions may arrive much later. It is derived by the verified `peraffkno → affcoh → affine_provind_theory_eq` route and is axiom-clean. Remaining M3/M4 human/fresh-context audit gates are tracked separately. |
| M4 | Affine master + reusable LUV lift; close expectation/Self-Trust statements | **implementation complete (2026-07-13; pending statement read-through/audit)** — the affine master, fixed-LUV semantic lift, and all seven expectation/Self-Trust statements are axiom-clean. The repaired Self-Trust API bundles delayed `ValuesAt` semantics with an explicit normalized fixed-portfolio certificate (`AffineQuotePortfolio`, `AffineQuoteEq`/`GE`): uniform polynomial emission, exact day-`n` gap representation, and coherence only at the actual deferred day `f n`. Reusable two-sided/one-sided preemptive bridges transport that later price law back to the diagonal. **Disclosed type-`(c)` boundary:** the cross-grid field packages the paper's quotation/encoding-coherence step; M7's concrete first-order quotation mechanism remains its principled witness. No Lean `sorry` remains in `LogicalInduction/`. |
| M5 | Full remaining conditional property tail | **verified complete (2026-07-14)** — every paper node has an exact theorem or explicitly classified conditional representation lift; Anson confirmed the statement read-through; the independent fresh-context audit found and drove repairs for arbitrary-BCS affine scope, market-generated introspection endpoints, and boundary tracking, then returned PASS on correction recheck. The 1,958-job property/integration roll-up and 2,670-job full build are green; source, axiom, and diff checks pass. |
| M6 | construction Part 1: strategy fixed point + computable rational `MarketMaker` + inexploitability | **verified complete (2026-07-14)** — `fixed_point_lemma`, the exact rational fuel-clocked `MarketMaker`, and recursive-history `marketMaker_not_exploited` are proved. The search is an executable bounded recursion over decoded candidates, with a certified stopping clock obtained from rational density; it is not an opaque choice or a conclusion-bearing certificate. The statement comparison/disclosure packet is complete, the 2,426-job construction roll-up and 2,671-job full build are green, executable-hole and diff checks pass, and all M6 capstones expose only the approved three axioms. |
| M7 | budgeter, trading firm, LIA, existence, unconditionalization | **active (core construction complete 2026-07-15; witness/audit contract open)** — full completion contract below. Efficient-trader enumeration, the process-backed Budgeter, concrete exact `TradingFirm`, summable-residual dominance, recursive rational LIA, and the complete executable compiler are now proved. `Construction/LIACompiler.lean` compiles every finite layer—sentence/rational/EF encodings, process stages, raw trader programs, MarketMaker, Budgeter, exact TradingFirm cutoff/mixture, state-prefix recurrence, rational quotation, and natural output—through `Computable₂ (liaEncodedQuoteNatAtFuel process)`. `liaBoundedEvaluatorCompiler` instantiates the formerly open boundary; paper-facing `LIA_is_logical_inductor` and `exists_logical_inductor` compile and expose only `propext`, `Classical.choice`, and `Quot.sound`. The fifteen post-M5 compiler/syntax witnesses, their fully instantiated M3–M5 corollaries, paper comparison, read-through, and final audit gates remain open. |

### M7-HIST-EVALN linchpin COMPLETE (2026-07-15)

`Construction/M7Witnesses.lean` proves the universal bounded-simulator theorem
`codeEvalnNat_polyFueled : ∀ c, ∃ prog, PolyFueled prog (codeEvalnNat c)` — **no `sorry`,
axiom-clean** (`propext`/`Classical.choice`/`Quot.sound`). This is the reusable poly-clock
interpreter the M5 notes flagged as missing (Mathlib only proves `evaln` primitive recursive,
not poly-fuel in this repo's `evaln`-clocked model). It is true because the interpreted code
is *fixed* (constant nesting depth) and the output is poly-bounded (`codeEvalnNat_output_poly`).
Proof is an induction on the simulated code, all 8 constructor cases discharged:
- `zero`/`succ`/`left`/`right`: shared `polyFueled_baseGuard` (one `ifzSel` over `subc`,
  exploiting that every `evaln` clause self-guards its input).
- `pair`/`comp`: `codeEvalnNat_{pair,comp}_eq` + `_polyFueled` — the self-guard makes both a
  pure combination of the sub-code compilers at the same/output input, no fuel arithmetic.
- `prec`: `precNat` (normalized `precEvalState`) + `codeEvalnNat_prec_eq` (semantic core via
  `precEvalState_final`) + `codeEvalnNat_prec_polyFueled` (`PolyFueled.prec` over `precNat`,
  base/step from the `cf`/`cg` sub-compilers, state bounded via `codeEvalnNat_le`).
- `rfind'`: `rfindNat` (forward search where fuel and search index move together, so the
  answer is the final state at `j = clock` with no outer guard) + `rfindNat_eq` +
  `codeEvalnNat_rfind_eq` + `codeEvalnNat_rfind_polyFueled` (`PolyFueled.prec`, bound via
  `rfindNat_le`).

`PolyFueled.prec` assemblies are scoped under `attribute [local irreducible] Nat.sqrt` to
avoid the deep-product `whnf` blowup. `boundedEvalnCompiler` inhabits the `BoundedEvalnCompiler`
hub for every simulated code. Build green (2467 jobs). This unblocks the witnesses that route
through the universal simulator (`M7-HIST-EVALN`, general `M7-CE-REPETITION`, `M7-COMP-SYNTAX`,
`M7-PATIENT-CLOCK`, `M7-FEEDBACK-EMIT`), which can now bind concrete checker/enumeration codes
to a poly-fuel program instead of assuming one.

### M7-CE-REPETITION general case COMPLETE (2026-07-15)

`Construction/M7Witnesses.lean`: `EfficientRepeatedEnumeration.ofCE` inhabits the repetition
boundary for an arbitrary **code-enumerable (c.e.) source** — no polynomial-clock assumption
on the source itself (the paper's actual UND obligation, vs `ofPoly`'s poly-source case).
`CEEnumeration source` packages an enumerator code that halts on each index giving `⌜source i⌝`
and whose outputs all lie in `source`'s range. `ceRepeatSeq` dovetails on `⟨i, fuel⟩` through
the `M7-HIST-EVALN` simulator (`codeEvalnNat`, poly by `codeEvalnNat_polyFueled`), emits the
decoded bounded output and pads with `source 0` before halting — poly regardless of how
expensive `source` is. `codeEvalnNat_pair_mono` (interpreter output stable under larger fuel,
via `evaln_mono`) drives `repeats`. Axiom-clean. **2 of 15 witnesses now fully inhabited**
(`M7-HIST-EVALN`, `M7-CE-REPETITION`).

### Build-state correction (2026-07-15)

The prior session was cut off mid-proof and left `Construction/LIACompiler.lean`
**non-elaborating** (a `whnf` heartbeat timeout in `firmBudgetBreachAtDayData_prim`, the
last Budgeter-gate primrec lemma, cascading to a downstream kernel error). The M7 notes'
"targeted LIACompiler build is green" claim was therefore not actual, and the file was not
truly `sorry`-free — it simply did not compile. This session fixed two genuine bugs in the
cut-off proof (a `Primrec`-into-`Type` `hctx` ascription; a systematically mis-indexed
seven-projection block). The residual failure was then **diagnosed and fixed**: an
interactive `set_option diagnostics true` run showed the final `exact` blowing up computing
`Nat.sqrt` (~23k unfoldings) via `Nat.unpair` — i.e. isDefEq reconciling the `Primcodable`
instance of the deeply-nested product input type, *not* the budget math (`rfl`/`simp`/
`simpa`/heartbeat-bumps had all chased the wrong layer). Scoping `attribute [local
irreducible] Nat.sqrt …` around the theorem stops that reduction so the instances/leaves
match structurally; `firmBudgetBreachAtDayData_prim` is now **proved, no `sorry`**.
The compiler assembly above `firmBudgetBreachAtDayData_prim` has since landed:
`budgeterTradesFromStageTradeLists_prim`, the exact syntax-derived TradingFirm cutoff,
the component/whole-firm compilers, `liaPrefixFromTradeListsAtFuel_prim`, process-prefix
composition, quotation, and the top-level `Computable₂ liaEncodedQuoteNatAtFuel`
certificate all compile. `LIABoundedEvaluatorCompiler`, `thm:lia`, and `thm:li` are now
instantiated and axiom-clean. (Reusable lesson: for `Primrec` goals
over deep product types, an `exact`/`rfl` `whnf` blowup is usually `Nat.unpair`/`Nat.sqrt`
in the `Primcodable` instances — check `set_option diagnostics true` and scope
`irreducible Nat.sqrt` rather than bumping heartbeats.)

### Active M7 completion contract (set 2026-07-14)

M7 is complete only when all of the following are true:

1. The paper's `Budgeter` is concretely computable from a computable deductive process and
   has kernel-checked exact-trade preservation above budget, a uniform `-b` plausible-world
   floor, and exploitation preservation for some positive integer budget.
2. A concrete redundant enumeration contains every `EfficientlyComputableTok` trader; the
   daywise finite `TradingFirm` mixture is executable; and Trading Firm Dominance proves
   that it exploits every market exploited by any e.c. trader while the other components
   have one summable uniform downside bound.
3. Recursive `LIA` is the exact MarketMaker response to that firm, has an exact computable
   rational `[0,1]` market presentation for every computable deductive process, satisfies
   `IsLogicalInductor`, and yields the paper-strength `exists_logical_inductor` theorem.
4. Every explicit post-M5 construction boundary is inhabited by a concrete conclusion-free
   witness: `M7-HIST-EVALN`, `M7-COMP-SYNTAX`, `M7-QUOTE-AFFINE`,
   `M7-PATIENT-CLOCK`, `M7-FEEDBACK-EMIT`, `M7-FEEDBACK-TRUTH`,
   `M7-PREFIX-PATCH`, `M7-CE-REPETITION`, `M7-PREFIX-MACHINE`,
   `M7-DUS-APPROX`, `M7-DUS-PREFIX-SYNTAX`, `M7-STRICT-SEPARATORS`,
   `M7-SCON-COMPILER`, `M7-SCON-PRESENTATION`, and `M7-LUV-SYNTAX`.
   The advertised M3--M5 paper nodes have fully instantiated corollaries rather than hidden
   logical-inductor or representation-oracle assumptions.
5. `def/lem:budgeter`, `def:tradingfirm`, `lem:tfdom`, `def/alg:lia`, `thm:lia`, and
   `thm:li` have a line-by-line paper comparison with every indexing or modeling
   substitution disclosed. No conclusion-in-premise, vacuous, noncomputable, or merely
   bounded-but-not-enumerable stand-in counts.
6. Construction/property/integration targets and a fresh full build pass; the executable
   hole scan and `git diff --check` are clean; capstone axiom reports contain only
   `propext`, `Classical.choice`, and `Quot.sound`; Anson completes the top-level
   statement/definition read-through; and a separate fresh-context M7 adversarial audit is
   repaired and independently rechecked.

Partial infrastructure and conditional capstones do not close M7.

**M4 implementation audit (2026-07-13):** targeted Self-Trust build and full `lake build`
(2,654 jobs) are green; the source-level `sorry`/`sorryAx` searches are empty; all four
final theorems and both preemptive bridges print only `propext`, `Classical.choice`, and
`Quot.sound`. The repaired interface keeps `scale > 0`, a real polynomial emitter, uniform
risk/boundedness, and an actual later market price at `f n`; it cannot be inhabited by a
zero-normalization shortcut and it does not assert future facts in `D n`. The residual
non-vacuity boundary is explicit rather than erased: constructing each theorem-specific
quote certificate from first-order quotation is assigned to M7. A separate fresh-context
statement audit and Anson's read-through remain required by the project protocol.

**M3 update (2026-07-12, certificate closure):** all three outstanding e.c. certificates
are discharged. `excTrader_ecTok` and `LUV.expect_converges` are axiom-clean; the latter now
explicitly requires `LUV.PolyThresholdCodes`, the disclosed compact-code interface for the
paper's Θ-definable threshold family. At the M3 exit, the only Lean `sorry`s were the seven
statements intentionally moved to M4; three are now discharged. **Phase F is complete:** the ledger and inventory below are current, the
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

## Paper errata

Defects in Garrabrant et al. (arXiv:1609.03543v5) itself, as distinct from our modeling
choices. **This distinction is load-bearing:** a type-`(c)` substitution is a place *we*
weakened the paper; an erratum is a place *the paper* does not support its own statement.
Conflating them either flatters us or slanders them. Any public writeup must carry these.

| Paper node | Severity | Defect | Our disposition |
|---|---|---|---|
| `thm:ifp` | **substantive — proof gap, theorem possibly false as stated** | `app:ifp` justifies efficiency of the false-report transform `F` with: *"only finitely many constants `pt_i(phi)` are needed, and can be hard-coded into `F`."* False: finitely many **days** `i < N`, but `phi` ranges over all sentences, so the constant set is infinite. `F` must *compute* `pt_i(phi)`, and `def:marketprocess` (computable sequence of pricings — no finite support, no time bound) gives no runtime or bit-size bound. The proof does not go through for the market class it quantifies over. | Theorem kept to what is provable: `lic_iff_of_finitePerturbation` takes an `EfficientPrefixPatch` per market and is **strictly weaker than `thm:ifp`** — see below. |
| `thm:wubexp` | minor — TeX slip ⚠️ **unaudited** | Omits the good-feedback support-in-image premise used by its own appendix proof. | Lean states the intended premise explicitly. |
| `thm:recurringunbiasednessexp` | minor — TeX slip ⚠️ **unaudited** | Support in the image of an unbound `f`. | Lean proves the coherent (strictly stronger) reading: every divergent weighting. |
| `thm:pazfc` | minor — TeX slip ⚠️ **unaudited** | Uses `f` without binding it. | Lean takes an arbitrary fixed computable bound. |

> ⚠️ **The three "minor — TeX slip" rows need an in-depth verification pass and have not
> had one.** They are recorded as notation slips with an obvious intended reading, and each
> was classified from the TeX surface without working the appendix proof. **That is exactly
> how `thm:ifp` was recorded** — as a routine `(c)` modeling note — until it was worked
> through and turned out to be a substantive proof gap. The prior should therefore be that
> at least one of these three is misclassified. Until each has been re-derived against its
> appendix proof, the "minor" severity is a *hypothesis*, not a finding. Cheap to do (they
> are localized), and each is a place we claim the paper erred — the claim that most
> deserves scrutiny, since being wrong here means slandering the authors rather than
> merely overselling ourselves. Track as `M7-ERRATA-AUDIT`; fresh context, per CLAUDE.md.

### `thm:ifp` — detail, and what is open

The gap is not pedantic. Let `P'` agree with `LIA` from day 1, with
`P' 0 φ = 1 - 1/2^(2^(encode φ))` — a legal market under `def:marketprocess`. A trader whose
day-`n` strategy prices a code-`~n` sentence at day 0 freezes to a `.const` with numeral
`~2^(2^n)`, unemittable under any polynomial clock. So `EfficientPrefixPatch P' 1` is
**uninhabited**: for that market the paper's proof strategy provably fails.

Confidence, stated honestly:

- **Established (by reading the TeX):** the quoted justification is false as written.
- **Argued, not formalized — but its one load-bearing fact is now PROVED (2026-07-16).**
  The counterexample rests on: *for a fixed `Code c`, `evaln k c n` outputs a value
  `≤ p_c(k)` for a fixed polynomial `p_c`*. That is **already proved in-repo** as
  `codeEvaln_result_le` + `codeEvalBound_poly` (`Construction/M7Witnesses.lean`, from the
  M7-HIST-EVALN work) — the row's earlier "true but unformalized" was wrong; it was
  formalized all along and this session failed to find it. It is **not** implied by
  Mathlib's `evaln_bound`, which bounds the *input*
  (`n < k`) only; outputs genuinely exceed the fuel — itself now a proved theorem,
  `evaln_output_can_exceed_fuel` (kernel-checked, not `native_decide`). The polynomial ceiling comes from `pair` squaring only boundedly often
  for a fixed code, while `comp`/`prec` intermediates are input-guarded to `≤ k` and
  `rfind'` returns a guarded index. This also discharges the read-the-source claim OPEN
  RISK 4's design rests on. **Still unformalized:** the counterexample *itself* (exhibiting
  the market `P'`, the trader, and deriving the contradiction in Lean). The gap is now
  narrow — the hard general fact is in hand — but the row stays *argued* until that lands.
- **Open:** whether `thm:ifp` is *false* for general markets, or merely unproved. Suggestive
  argument: a day-`0` pricing hands an e.c. trader a free oracle to an exponential-time
  computable function — real power that `LIA`'s poly-time trader enumeration never
  anticipates — so a trader might exploit `P'` while none exploits `LIA`. **Not a claim.**
  Settling it needs an actual exploiting trader.
- **Not affected:** `exists_logical_inductor` and the M7 core depend on none of this.

Scope note for citation: for `LIA` the per-day quote table is a finite `RationalBeliefState`
entry list, so the patch is a hardcodable finite lookup with constant-size tokens — the
hypothesis is dischargeable (`M7-PREFIX-PATCH`) and the theorem is **not vacuous**. But
`lic_iff_of_finitePerturbation` does not cover every finite perturbation of a computable
market, and must never be cited as if it did.

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
| `M7-PATIENT-CLOCK` (step 14: `EF.priceQueries` compiled — the guard) | `efPriceQueries_prim` (+ private `efQueriesAppend{,_prim}`, `efPriorQueries{,_prim}`, `efQueriesNormVal{,_prim}`, `efAuxQueriesVal{,_zero,_prim}`, `efQueriesHistory_getD`, `efQueriesNormVal_history`; `efChildPair_lt` un-`private`d) (`Construction/LIACompiler.lean`) | done | **P** `(a,b)` | **The step-12 "only real work", and the guard that stops a wrong witness.** `efPriceQueries_prim : Primrec EF.priceQueries`. Course-of-values recursion on the Gödel code via `Nat.strong_rec` `(b)`, mirroring the `EF.rank` compiler (`efRankNormStep` …) — **but** carrying the list-valued result `Option (List (ℕ × Sentence))` **directly** through `strong_rec`'s polymorphic `σ`, not a normalized `ℕ`, which drops every `encode`/`decode` round-trip the rank compiler needed (`strong_rec` takes any `Primcodable σ`, a fact the rank compiler did not exploit). Reuses the private `efChildPair_lt` (un-`private`d, **not** duplicated — rule 2b corollary) for the child-index bound; the branch case-split follows `efRankNormStep_history` tag-for-tag against `EF.ofNatAux`. **Why it is load-bearing, not bookkeeping:** the settlement checker reuses the EF rational machine with the *total* table `V fuel n φ := (market.quoteAtFuel fuel n φ).getD 0`, which cannot tell a timeout from a genuine `0`; unguarded, two worlds spuriously agree at `0` and `settlementCheckAtFuel_sound` breaks (a kernel-clean program accepting **un**settled tests). `EF.denoteRatWithAtFuel_complete`'s hypothesis is literally `∀ query ∈ e.priceQueries, …`, so a `Primrec` `priceQueries` is exactly what turns "all listed queries answered" into a decidable guard. Carries no market, settlement, or economic conclusion. `LIACompiler` green at 2,436 jobs; capstones still expose only the approved three axioms. **The `Nat.sqrt`/`whnf` gotcha did not fire** (recursion is over `ℕ`/`List (Option _)`, no deep product input) — consistent with steps 5–13. |
| `M7-PATIENT-CLOCK` (step 13: `quoteAtFuel` compiled + the step-12 privates exposed) | `quoteAtFuel_prim` (`Construction/LIACompiler.lean`); `efRatCompiledEval`, `efRatCompiledEval_eq`, `efRatCompiledEval_prim`, `processStageAtFuel_prim` un-`private`d (same file) | done | **P** `(a,b)` | The two mechanical items step 12 identified, taken first so the `EF.priceQueries` grind lands against a green base. `quoteAtFuel_prim : Primrec fun p : ℕ × ℕ × Sentence => market.quoteAtFuel p.1 p.2.1 p.2.2` — step 12 confirmed by grep that no `Primrec` proof for `quoteAtFuel` existed; this builds it exactly on the `processStageAtFuel_prim` template (`Nat.Partrec.Code.primrec_evaln` + `Primrec.decode` + `Primrec.option_bind`, all `(b)`), differing only in pairing the day with the sentence code via `Primrec₂.natPair` and decoding to `ℚ` rather than `Finset Sentence`. Compiled first try; **the `Nat.sqrt`/`whnf` gotcha did not fire** (input `ℕ × ℕ × Sentence` is shallow), consistent with steps 5–11 — the handoff's advice not to pre-scatter `local irreducible` continues to hold. The four exposures are keyword deletions with **no duplication and no proof change** (rule 2b's corollary: a private-but-perfect lemma is reused, not re-derived). `LIACompiler` green at 2,436 jobs; `liaEncodedQuoteNatAtFuel_computable`, `LIA_is_logical_inductor` and `exists_logical_inductor` still expose only the approved three axioms. Carries no settlement, market, or economic content — `quoteAtFuel_prim` is pure plumbing and its `V` is still the **total** function whose timeout/genuine-`0` conflation step 12 flagged; the `priceQueries` guard (step 14) is what makes it safe to use. |
| `M7-PATIENT-CLOCK` (step 12: **scoping correction — a third `EF` recursion**) | (no new decls — a stop-and-report finding; see `notes/next-session.md` step 6) | **not started; re-scoped** | — | **Rule 6 stop-and-report.** What steps 5\u201311 left as \"one last assembly step\" is **two**, and the extra one was costed by nobody, including my own step-5 estimate. Making `settlementCheckAtFuel` `Computable` requires `EF.denoteRatWithAtFuel`, a recursion over `EF` hitting the market at its `price` leaves; **nothing in the repo compiles it.** The EF rational machine is exactly the right reuse \u2014 `efRatCompiledEval_prim` is parameterized by a context `C` and a primrec total `V` (`LIACompiler.lean:3727`), so `C := \u2115` (fuel) and `V fuel n \u03c6 := (market.quoteAtFuel fuel n \u03c6).getD 0` fits, and our `\u03c1` is always `[]` so `denoteRat` suffices. **But its `V` is total**: it substitutes `0` for an *unanswered* query and cannot distinguish a timeout from a genuine `0`. Unguarded that **breaks `settlementCheckAtFuel_sound`** \u2014 two worlds could spuriously agree at `0` and certify a false test. The guard needs `EF.priceQueries` compiled (a fresh `nat_strong_rec` over `EF` codes; template is the **`EF.rank` compiler**, `LIACompiler.lean:1428\u20131595`, ~170 lines), plus a `denoteRat` congruence lemma. Also found: `efRatCompiledEval{,_eq,_prim}` and `processStageAtFuel_prim` are all **`private`** \u2014 expose, do not duplicate (rule 2b corollary); `quoteAtFuel` has no `Primrec` proof and genuinely must be built. Recorded **before** writing any of it, so the estimate is not retrofitted. |
| `M7-PATIENT-CLOCK` (step 11: the bounded settlement check) | `AffineCombination.exists_fuel_valueRatAtFuel_list`; `AffineCombination.settlementCheckAtFuel`; `AffineCombination.settlementCheckAtFuel_{sound,complete}` (`Construction/M7Witnesses.lean`) | done | **P** `(a)` | The settlement analogue of `unitMaturityCheckAtFuel` (`Calibration.lean`) — and, unlike that one, on track to be carried through to an actual code (`unitMaturityCheckAtFuel` was never compiled, which is the shared wall `M7-FEEDBACK-EMIT`/`M7-FEEDBACK-TRUTH` also sit behind). **Conservative by construction**: any timeout — of the process program or of any single market call — reads `false`, so `true` always certifies the real test; that is what makes `_sound` hold with no side conditions. `_sound`/`_complete` together are exactly the biconditional `SettlementChecker.spec` needs, modulo turning the `Bool` function into a `Nat.Partrec.Code` (step 12). `_complete` needs one fuel serving the whole finite world enumeration at once: `exists_fuel_valueRatAtFuel_list` gets it by `max` + `mono` over `(allBitLists B).map bitsPayoutRat`, and `B` is stable under extra fuel because `stageAtFuel_mono` pins the stage. No `truth`, market-limit, or economic content. Axiom-clean, no `sorry`. |
| `M7-PATIENT-CLOCK` (step 10: the fuel layer — `valueRat` at fuel) | `affineTermsRatAtFuel`; `AffineCombination.valueRatAtFuel`; `affineTermsRatAtFuel_{sound,mono}`; `exists_fuel_affineTermsRatAtFuel`; `AffineCombination.valueRatAtFuel_{sound,mono}`; `AffineCombination.exists_fuel_valueRatAtFuel` (`Construction/M7Witnesses.lean`) | done | **P** `(a)` | **Where the shape changes.** Every leaf through step 9 is `Primrec`; `valueRat` cannot be, because it calls `EF.denoteRat Q` with `Q` the *market*, reachable only via `market.quoteAtFuel`. So the checker is fuel-clocked — which is exactly what `SettlementChecker.spec` already asks for (`\u2203 F, acceptsWithin code F \u27e8i,j\u27e9`), so the interface anticipated this rather than being bent to fit. Mirrors `Strategy.valueRatListAtFuel` (`ROI.lean:218`) exactly: the same three-part sound/mono/exists-fuel contract, built **on** the existing `EF.denoteRatWithAtFuel` rather than re-deriving it (rule 2b: the EF rational machine and its `_sound`/`_mono`/`exists_fuel` were already there). `exists_fuel` combines finitely many per-`EF` fuels by `max` + `mono`. Axiom-clean, no `sorry`. |
| `M7-PATIENT-CLOCK` (step 9: `AffineCombination` codable + support bound compiled) | `affineEquiv`; `affineCombinationPrimcodable`; `affineEquiv_prim`; `affineConst_prim`; `affineTerms_prim`; `finset_sum_eq_stageSort_sum`; `settlementAtomLimit_eq_stageSort`; `settlementAtomLimit_prim` (+ private `list_sum_prim`) (`Construction/M7Witnesses.lean`) | done | **P** `(a,b)` | `AffineCombination` is a plain pair of `const : EF` and `terms : List (EF × Sentence)`, so it inherits `Primcodable` through `Primcodable.ofEquiv` `(b)` off the existing `efPrimcodable`/`sentencePrimcodable`; projections via `Primrec.of_equiv`. `settlementAtomLimit_prim : Primrec₂ AffineCombination.settlementAtomLimit` needs the `Finset` sum as a list sum — `finset_sum_eq_stageSort_sum` gets it from `Finset.sort_eq` `(b)` (the sorted list *is* a list representation of the underlying multiset, so no reordering argument is needed), reusing `stageSort` a third time. Mathlib's `Primrec` API has no `list_sum`; `list_sum_prim` builds it from `list_foldr`. **The documented `Nat.sqrt`/`whnf` gotcha did not fire** even though `AffineCombination × Finset Sentence` is the first deep product input in this chain — noting it because the handoff predicted it would, and the next session should not pre-emptively scatter `local irreducible`. Axiom-clean, no `sorry`. |
| `M7-PATIENT-CLOCK` (step 8: stage quantifier + world enumeration compiled) | `encode_eq_encode_stageSort`; `stageSort_prim`; `stageSatBits_prim`; `allBitLists_prim` (+ private `list_all_eq_foldr`) (`Construction/M7Witnesses.lean`) | done | **P** `(a,b)` | **`stageSort` needs no sorting compiled at all.** `encode_eq_encode_stageSort : Encodable.encode stage = Encodable.encode (stageSort stage)` holds **by `rfl`** — Mathlib's `encodeMultiset` sorts by its private `enle = encode ⁻¹'o (· ≤ ·)`, and the `sentenceCodeLE` + instances picked in step 5 are defeq to it (verified by probe, not assumed). So a stage's code *is* its sorted list's code, and `stageSort_prim` is `decode ∘ encode`; the compiled test recovers the list by decoding and never runs a `Finset` operation. This retroactively vindicates the step-5 choice of `Finset.sort` over `Finset.toList` on a second, independent ground beyond `toList` being noncomputable. **Not semantic**: `mem_stageSort` pins `stageSatBits` to `∀ φ ∈ stage` whatever the order — the order buys compilability only (audit note: the step-5 concern that `stageSort` encoded an assumption about the test's range was **overstated**; it does not). `stageSatBits_prim` closes `evalBits_prim` over the stage via `Primrec.list_foldr` `(b)` (Mathlib has no `list_all`; `list_all_eq_foldr` bridges). `allBitLists_prim` is a plain `Primrec.nat_rec₁` + `list_flatMap` `(b)` — the one leaf needing no `Sentence` machinery. All axiom-clean, no `sorry`; all three compiled first try. |
| `M7-PATIENT-CLOCK` (step 7: `eval` compiled — the crux) | `evalBits_prim` (+ private `evalOp`/`evalNorm`/`evalBinary`/`evalSucc`/`evalList` and their `_prim`/`_history` lemmas) (`Construction/M7Witnesses.lean`) | done | **P** `(a,b)` | **`Primrec₂ fun (l : List Bool) (φ : Sentence) => BoolPCWorld.eval (BoolPCWorld.bitsWorld l) φ`** — the recursion the whole settlement test rests on, and the step with no precedent in the repo. Two things beyond step 6: (i) the `nat_strong_rec` parameter is the **world** (`List Bool`, where `atomBound` used `Unit`), consumed in the atom case as `eval (bitsWorld l) (.atom a) = l.getD a false` — `Primrec.list_getD` on the *parameter* rather than on the recursion history; (ii) the three binary tags genuinely differ (`🡒`/`⋏`/`⋎`) where `atomBound` maxed all three alike. (ii) **cost nothing**: `Bool` is finite, so Mathlib's `Primrec.dom_bool₂` `(b)` gives *every* `Bool → Bool → Bool` for free and `evalOp` just dispatches on the tag — the anticipated expense there did not materialize. Three-valued `Option` encoding (`0` = does not decode, `1` = false, `2` = true). **Note for the next such proof:** `PrimrecPred p` is `∃ _ : DecidablePred p, Primrec fun a => decide (p a)` — an existential over the instance, so it never unfolds to `Primrec`, and no type ascription will force it; `PrimrecPred.decide` / `Primrec.primrecPred` `(b)` are the two directions. This cost the only real debugging in the step. Axiom-clean, no `sorry`; no `Nat.sqrt` gotcha (flat input types). |
| `M7-PATIENT-CLOCK` (step 6: `atomBound` compiled) | `atomBound_prim` (+ private `atomBoundNorm`/`atomBoundBinary`/`atomBoundSucc`/`atomBoundList` and their `_prim`/`_history` lemmas) (`Construction/M7Witnesses.lean`) | done | **P** `(a)` | First of the two `Sentence` recursions the settlement test needs, and the **first `Primrec` proof over a `Sentence` recursion in the repo** (`sentencePrimcodable` compiles the *decoder*, not a function defined by recursion on formulas). `Sentence`'s recursor is not a `Primrec` combinator, so this goes by course-of-values recursion on the Gödel code via `Primrec.nat_strong_rec`, following the `sentencePrimcodable` template. Values are `Option`-encoded (`0` = code does not decode, `v+1` = decodes to `v`); the encoding is **load-bearing**, since for a binary code with one decoding and one non-decoding child the answer must be `0`, which a plain `max` fold could not distinguish from a real bound of `0` — `formulaBinaryNorm` guards identically. Cheaper than the template in one respect: all three binary tags take `max`, so one `atomBoundBinary_history` serves 2/3/4. **Confirms the template transfers** — the estimate for step 7 stands. Axiom-clean, no `sorry`; no `Nat.sqrt` gotcha hit (input type is flat `ℕ`/`List ℕ`). |
| `M7-PATIENT-CLOCK` (step 5: the test, actually compilable) | `BoolPCWorld.bitsWorld`; `BoolPCWorld.bitsPayoutRat` (`AffineCoherence.lean`); `toBoolPCWorld_bitsToFin`; `payoutRat_bitsToFin`; `bitsWorld_ofFn`; `bitsPayoutRat_ofFn`; `sentenceCodeLE` (+4 order instances); `stageSort`; `mem_stageSort`; `stageSatBits`; `stageSatBits_eq_true_iff`; `AffineCombination.SettlementTestBool` (restated); `settlementTestBool_iff` (`Calibration.lean`) | done | **P** `(a)` | **Completes the retirement the previous row claimed.** Three obstructions remained in `SettlementTestBool`'s *body*, each of which blocks `Primrec` decomposition independently: (i) it built `bitsToFin B l : Fin B → Bool` and applied `eval`/`payoutRat` to it — and the real problem is not `Fin B` but that `BoolPCWorld = ℕ → Bool` is a **function type with no `Primcodable` instance**, so `Primrec (eval v)` is not even statable; `bitsWorld : List Bool → BoolPCWorld` fixes this by keeping the world a beta-reduced intermediate, leaving every compiled quantity a function of the `Primcodable` pair `List Bool × Sentence`. (ii) `∀ φ ∈ stage` was a `Finset` quantifier; `stageSatBits` is a `List.all` over `stageSort`. **`Finset.toList` cannot be used** — it is noncomputable (picks a representative via `Multiset.toList`), which the compiler caught. `Finset.sort` under `sentenceCodeLE` is both computable and *canonical*: it is the order the stock `Finset Sentence` encoding already sorts by (`LIACompiler.lean:1949`), so `stageSort stage` is the list that stage's own code decodes to — needed for the `Primrec` step regardless. (iii) `decide` of an implication chain became `!a \|\| !b \|\| c`. `settlementTestBool_iff` re-proved against the new form; the `SettlementTest` statement and `SettlementChecker.spec` are **unchanged**, so nothing downstream moved. Axiom-clean, no `sorry`; Calibration and M7Witnesses green. |
| `M7-PATIENT-CLOCK` (dependent-type wall retired — see correction) | `allBitLists`; `mem_allBitLists`; `bitsToFin`; `bitsToFin_ofFn`; `AffineCombination.SettlementTestBool`; `settlementTestBool_iff` (`Calibration.lean`); `SettlementChecker` restated (`M7Witnesses.lean`) | done | **P** `(a)` | **Retires the one identified risk in the remaining obligation.** `SettlementTest` quantifies over `FiniteWorld B = Fin B → Bool` with `B` *computed from the input* — a dependent family that `Computable` cannot decompose, so **no code could recognize the test in that form**. (Verified by grep: no `Computable`/`Primrec` proof over a `FiniteWorld` quantifier exists anywhere in the repo; the pre-existing `unitMaturityCheckAtFuel` has the identical shape and was never compiled either — the wall had never been faced.) `SettlementTestBool` presents the same test over `List Bool`, one non-dependent `Primcodable` type; `settlementTestBool_iff` bridges them (completeness via surjectivity of `bitsToFin` onto `FiniteWorld B` through `List.ofFn`). `SettlementChecker.spec` now targets the Bool version. Lists rather than `Nat.testBit` deliberately: the list route needs only `List.ofFn` length/index lemmas, the numeric route needs bit arithmetic Mathlib does not carry. **Shared infrastructure** — the same wall blocks the maturity checker, hence `M7-FEEDBACK-EMIT`/`M7-FEEDBACK-TRUTH`. Axiom-clean. **Ledger correction (2026-07-16, by the next session): this row's title overstated — the wall was only half retired.** Making the *quantifier* non-dependent was necessary but not sufficient: the *body* still built `bitsToFin B l : Fin B → Bool` and passed it to `eval`/`payoutRat`, so a `Primrec` proof still could not decompose. The deeper obstruction is not `Fin B` at all but that `BoolPCWorld = ℕ → Bool` is a **function type, which admits no `Primcodable` instance** — `Primrec (eval v)` cannot even be *stated* for a world `v`. See the next row for the actual retirement. |
| `M7-PATIENT-CLOCK` (step 4/4: the clock, constructed) | `AffineCombination.SettlementTest` (+`Decidable` instance); `finiteWorlds_agree_of_agree`; `DeterminedViaTheory.settlementTest_iff_settled` (`Calibration.lean`); `SettlementChecker`; `SettlementChecker.toSemiDecider`; `PatientSettlementClock.ofChecker`; `SettlementSemiDecider`; `.ofSemiDecider`; `deadline*`/`acceptsWithin_mono`/`dovetailFound_mono` (`Construction/M7Witnesses.lean`) | **done modulo one named computability obligation** | **C/P** `(a)` | **`PatientSettlementClock` is constructed, not assumed** — all six fields discharged, no `sorry`, axiom-clean. `active i n := ¬deadlinePassed ∨ ¬dovetailFound`. The sole remaining input is `SettlementChecker`: **purely computational** — a code recognizing the *named decidable* `SettlementTest`, mentioning no history, `truth`, or market conclusion. Soundness/completeness are **theorems** (`settlementTest_iff_settled`, both directions, needing rationality `hQ` and consistency `hworld`), not fields. **Ledger correction (2026-07-16):** the first cut of this row overstated. It routed through `SettlementSemiDecider`, whose `sound` field *states* settlement, so `settled_of_inactive` was transported from an assumption — a conclusion-in-hypothesis shape — and step 2's `agree_of_finiteWorlds_agree` was **orphaned**, connected to the witness only in prose and in this row. `ofChecker` fixes both: step 2 is now load-bearing in the kernel (`ofChecker → toSemiDecider → settlementTest_iff_settled → agree_of_finiteWorlds_agree`). `ofSemiDecider` is kept as the general interface and flagged in its docstring. **Deadline subtlety** (real, resolved): `DeferralFunction` gives fuel poly in `f n`, not `n`, so `deferralEnvelope f i` is not poly-computable; `active_through_envelope` needs activity only *true* before the deadline, so the sound under-approximation `deadlinePassed` suffices. |
| `M7-PATIENT-CLOCK` (step 3/4: the bounded dovetail) | `acceptsWithin`; `dovetailFound`; `dovetailFound_eq_true_iff`; `polyFueled_dovetailFound` (`Construction/M7Witnesses.lean`) | done | **P** `(a)` | Discharges the paper's first `app:prandaff` bullet — *"`DefinitelySettled(n,m)` can be decided in time polynomial in `m`"* — for an **arbitrary** code, with no runtime assumption on the decider: "`c` accepts `⟨i,j⟩` within `n` steps for some `j ≤ n`" has a polynomial Boolean table in `⟨i,n⟩`. Composes the `M7-HIST-EVALN` simulator (`codeEvalnNat_polyFueled`) with `polyFueled_boundedAny`, plus a constant-equality test built from `subc`/`addc`/`ifzSel`. **Stated generically on purpose**: `PatientSettlementClock.active_codes` and `HistoricalVerifiedMaturitySchedule.check_poly` have the same shape (`check : ℕ → ℕ → Bool` + `PolyFueled` table) and neither had ever been built, so this serves `M7-FEEDBACK-EMIT`/`M7-FEEDBACK-TRUTH` too. Contains no settlement, market, or economic content. Hit the documented `Nat.sqrt`/`whnf` gotcha; fixed with scoped `local irreducible`, not heartbeats. Axiom-clean |
| `M7-PATIENT-CLOCK` (step 2/4: deciding settlement) | `AffineCombination.valueRat`; `value_eq_ratCast`; `valueRat_congr`; `settlementAtomLimit` (+`_stage_bounded`/`_terms_bounded`); `agree_of_finiteWorlds_agree`; `DeterminedViaTheory.settled_iff_agree` (`Calibration.lean`) | done | **P** `(a,b)` | Reduces the settlement test to a `decide`-able finite check. `settled_iff_agree`: settlement ⟺ plausible worlds merely *agree*, so the checker never needs `truth i` (which is a limit over the completed theory and not computable) — the paper asserts `Settled` decidable without noting this. `agree_of_finiteWorlds_agree`: agreement across the `Fintype` `FiniteWorld B = Fin B → Bool` (with exact **rational** values) implies agreement across all `PCWorld`s. **This is where rationality of `P` is load-bearing** — over an arbitrary `ℝ`-valued `History` the test is real equality, undecidable, and no clock exists; at `liaHistory` it does. Follows the existing `unitMaturityCheckAtFuel` template. Axiom-clean; no market or economic conclusion. |
| `M7-PATIENT-CLOCK` (step 1/4: settlement realizability) | `AffineCombination.exists_valueSet`; `AffineCombination.DeterminedViaTheory.exists_settled_stage` (`Calibration.lean`) | done | **P** `(a)` | The realizability core of `PatientSettlementClock.eventually_inactive`: completed-theory determination forces **exact** settlement at a *finite* stage, not merely the approximate `< ε` that `eventually_close` gives. Key fact: an `AffineCombination` has finitely many `terms`, so its value depends on a world through finitely many `{0,1}` payouts and ranges over a `Finset ℝ` (`exists_valueSet`, by induction on the term list — each term contributes `0` or its coefficient). Take `δ` = least nonzero gap to `truth i` and apply `eventually_close` at `δ`. Purely semantic — no computability claim, no market conclusion. Axiom-clean. **This is the paper's unstated premise** behind `app:prandaff`'s "let `settled` be a Turing machine deciding `Settled(n,m)`": the paper never argues settlement *occurs* at a finite stage. |
| `dd:fuel` (output bound) | `Nat.Partrec.Code.evaln_output_can_exceed_fuel` (`Computable.lean`) | done | **P** `(b)` | **The bound itself was already proved** as `codeEvaln_result_le` + `codeEvalBound_poly` (`Construction/M7Witnesses.lean`, M7-HIST-EVALN): a fixed code's `evaln` output is bounded by an explicit polynomial in the fuel. This session first re-proved it independently in `Computable.lean` before finding the original, and deleted the duplicate — recorded because it is the second rule-2 miss in one session (see also the reinvented `pair_lt_sq`, which Mathlib already had as `Nat.pair_lt_max_add_one_sq`). What survives is the accompanying *negative* fact: outputs genuinely exceed the fuel (`evaln 20 (pair succ succ) 5 = 48`), so the bound must be polynomial in the fuel rather than the fuel itself, and Mathlib's input-side `evaln_bound` does not suffice. Kernel-checked via equation lemmas — **not** `native_decide`, which would trust the compiler and add `Lean.ofReduceBool`. Together these discharge the read-the-source claim OPEN RISK 4's design rests on and the general fact the `thm:ifp` erratum needs. Axiom-clean |
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
| `def:ec` (M4 families) | `PolySentenceCodes`, `PolyRatCodes`, `LUV.PolyThresholdCodeSeq`, `GeneratedRatFeature`, `PGenerableRat` | done | **Def** | Legal varying-family interfaces missing from the M3 statement-only forms. They expose polynomially fueled sentence/rational codes, triple-indexed threshold codes `⌜Xₙ>i/k⌝`, and the paper's market-generated rational sequences as polynomial-size, rank-legal, **closed** EF progressions. The M5 `prand` audit found and repaired a missing closure clause: a free internal `EF.var` is no longer accepted as a top-level generated probability. Without these interfaces, arbitrary Lean functions can encode uncomputable diagonals no legal trader can follow. |
| `def:affcomsen` (M4 core) | `AffineCombination`, `.value`, `.price`, `.magnitude`, `.buy`, `.scale`, `.neg`, `.roundTrip`; `buy_value`, `roundTrip_netWorth`, `roundTrip_magnitude`, `roundTrip_hasROI` (`Affine.lean`) | done | **Def+P** | Syntax `c+Σeᵢφᵢ`; buying omits the constant because it cancels, and is proved to value exactly as `world(A)−priceₙ(A)`. The finite buy/sell round-trip kernel is now proved: after closing, every world values it at the realized price difference, its total share volume is exactly twice the affine magnitude, and any adequate price gain supplies `HasROI`. This is the economic kernel consumed by `thm:affpolymax`; opening weights and uniform verified closing days remain the family-level work. Axiom-clean. |
| `def:e` | `LUV.expectApprox`, `.expect`, `.expectSeq`, `.expectInf`; `expect_mem_Icc` | done | Def+P | `𝔼ₙ(X)=(1/n)∑_{i<n}Pₙ(⌜X>i/n⌝)` — the **concrete `ℕ→ℝ` expectation** the deference corpus abstracts as `E^H_n(X)`. Bounds `∈[0,1]` proved. **This is the LUV-bridge object that closes the price→expectation level gap** |
| `thm:ec` (D2) | feature-generic layer `buyIndF`/`sellIndF`/`hystChain` (+ facts 1–3, variation `hcDelta`/`hcBpos`/`hcBneg`/`hcBneg_unbounded`), `LUV.thresholdSumEF`/`expectEF`, gated signals `excPad`/`excBuy`/`excSell`, bundle trader `excTrader`, `excTrader_netWorth_ge`, `excBneg_unbounded`, `excTrader_exploits`, `excTrader_ecTok`, **`LUV.expect_converges`** (`Properties/ExpectationConvergence.lean`) | **done — axiom-clean** | **C** | **Expectations Converge**: `𝔼ₙ(X)` converges for every `[0,1]`-LUV satisfying the explicit compact-code interface `LUV.PolyThresholdCodes`. `thm:con`'s hysteresis re-run on the expectation feature trades the day-`n` threshold bundle `{(1/n)·⌜X>i/n⌝}_{i<n}`. `lem:conluvapprox` controls the payout mismatch; a start-day gate absorbs its error. Hypotheses `hcons` and `hval` disclose the propositional import of "Θ represents computations" (principled witness: M7). The exploiting trader and its variable-width token-emission certificate are both discharged. |
| `lem:conluvapprox` (single-LUV, D1) | **`PCWorld.ValuesAt.expectApprox_near`** (`Expectations.lean`) | done | **P** | a world valuing `X` at `x` assesses `𝔼ₙ` within `1/n` of `x` (in fact one-sidedly: `x ≤ 𝔼ₙ ≤ x + 1/n`). Pure counting: thresholds `i/n < x` pay 1 (`≥ ⌈nx⌉ ≥ nx` of them, using `x ≤ 1`), thresholds `> x` pay 0 (sum `≤ ⌊nx⌋+1 ≤ nx+1`; the possible threshold `= x` is the `+1` slack — `ValuesAt` deliberately says nothing at `r = x`). `Nat.floor`/`ceil` sandwich, no filter cards. Hypothesis `0 < n` (at `n = 0`, `𝔼₀ = 0` and `1/0 = 0` in ℝ — the bound is false). The combination (`b/n`) form for affine LUVs → M4 per the plan. Axiom-clean |
| `thm:ec` (`def:ec` cert closure) | `LUV.PolyThresholdCodes`, `PolySegStream.concatVar`, **`excTrader_ecTok`** | **done — axiom-clean** | **P** | `PolyThresholdCodes` emits `⌜X>i/n⌝` from `⟨n,i⟩` with polynomial fuel (faithful type-`(c)` interface for compact Θ-definable LUV syntax). `concatVar` uses polynomially fueled prefix sums and a primitive-recursive locator for genuinely variable-width historical blocks. Inner threshold sums use fixed-width `blocks`; the outer trade bundle uses uniform `concat`. Varying `1/n` and gated rational constants are emitted by closed encoding arithmetic. |
| `def:luv` (world values, D1 modeling) | `PCWorld.ValuesAt` (`Expectations.lean`) | done | **Def** | "world `v` values LUV `X` at `x`": threshold coherence — `v` affirms `X.gt r` for every `r < x`, denies it for every `r > x`, `x ∈ [0,1]`. **Disclosed type-`(c)`:** the market-observable rendering of the paper's "Θ represents computations ⇒ consistent worlds assign LUVs their values"; no first-order syntax. Substrate for `lem:conluvapprox` (Phase D1) and every Self-Trust linkage hypothesis |
| `def:luv` (indicator, relational) | `LUV.IsIndicator` (`Expectations.lean`) | done | **Def** | **relational rendering of the paper's `1(φ)`** (D3 principle): `Y` is an indicator family iff plausible worlds hold its sub-0 thresholds, tie its `[0,1)` thresholds to `φ`, and refute its ≥1 thresholds. *Deliberately not a canonical construction*: defining `gt r := φ` on `[0,1)` would make `thm:ei` definitional — the theorem's content is the inductor learning the growing bundle of equivalences. Audit bait: check this linkage isn't conclusion-shaped |
| `thm:ei` | `lic_expectation_indicator`; `LUV.IsIndicator.valuesAt` | **done — axiom-clean** | **P+C** | Signature carries `PolyThresholdCodes`, `[0,1]` prices, and daily plausible worlds. The old form was false for an inconsistent `DP`. The certified indicator-affine family plus `affine_tendsto_zero` proves the expectation/price gap vanishes. |
| `thm:loe` | `lic_linearity_of_expectation` | **done — axiom-clean** | **P+C** | Compact codes, price bounds, daily plausible worlds, and non-vacuous simultaneous `ValuesAt` witnesses feed the certified three-bundle affine family; the `1/n` semantic error is transported by `affine_tendsto_zero`. |
| `thm:expprovind` | `lic_expectation_provind` | **done — axiom-clean** | **P+C** | Plausible worlds value `X ≥ c` ⇒ `𝔼(X) ≳ₙ c`, via the certified expectation-affine family and `affine_provind`. |
| `def:deferralfunc` | `DeferralFunction` (`Properties/SelfTrust.lean`) | done | **Def** | `f n > n` + a code computing `f` within fuel polynomial **in `f n`** (the paper's "time poly in `f(n)`", faithfully weaker than poly-in-`n`), via the clocked interpreter (`dd:fuel`). Both paper conditions carried, none added |
| `def:ctsind` (real form) | `ctsInd` (`Properties/SelfTrust.lean`) | done | **Def** | `min 1 (max 0 ((x−y)/δ))` — the paper's continuous threshold indicator on reals (0 below `y`, linear on `(y,y+δ]`, 1 above); used by `thm:st`'s prescribed world-values |
| Self-Trust quote interface | `AffineQuotePortfolio`, `AffineQuoteEq`, `AffineQuoteGE`; `ExpectedFutureExpectationQuote`, `FuturePriceQuote`, `ConditionalExpectationQuote`, `SelfTrustQuote` | **done** | **Def, provenance (c)** | Repairs the audited cross-grid hole. Each theorem-specific object bundles compact syntax and delayed revelation-schedule `ValuesAt` semantics with one normalized polynomial affine family. `current_price` identifies its day-`n` price with a positive rational multiple of the target gap; `future_coherent` constrains the *same fixed portfolio* only at day `f n`. This is non-oracular with respect to `D n`, but remains an explicit type-`(c)` import of the paper's first-order quotation/encoding-coherence mechanism; principled witness = M7. Audit bait: ensure this operational field is discharged by quotation construction rather than assumed ad hoc downstream. |
| Self-Trust preemptive bridge | `AffineQuotePortfolio.preemptive_asympEq_zero`, `.gap_asympEq_zero`, `.preemptive_asympGE_zero`, `.gap_asympGE_zero` | **done — axiom-clean** | **P+C** | A deferred day satisfies `n < f n`, so its fixed-portfolio price lies between `affineFutureLow` and `affineFutureHigh`. The two operational halves of `thm:affpolymax` rule out separated diagonal gaps; positive normalization is then removed. Both two-sided and one-sided forms have only the three standard axioms. |
| `thm:cee` | `lic_expected_future_expectations` | **done — axiom-clean** | **C** | `𝔼ₙ(Xₙ) ≈ₙ 𝔼ₙ(⌜𝔼_{f(n)}(Xₙ)⌝)`, consuming `ExpectedFutureExpectationQuote`; delayed world semantics and cross-grid coherence are bundled rather than conflated. |
| `thm:ceu` | `lic_no_expected_net_update` | **done — axiom-clean** | **C** | `Pₙ(φₙ) ≈ₙ 𝔼ₙ(⌜P_{f(n)}(φₙ)⌝)` (deference-corpus name "cee"), consuming `FuturePriceQuote`. |
| `thm:ccee` | `lic_no_expected_net_update_conditional` | **done — axiom-clean** | **C** | Weighted product form; the certificate retains `[0,1]` membership, `PGenerableRat`, non-vacuous source values, product linkages, compact codes, and the fixed-portfolio future law. |
| `thm:st` | `lic_self_trust` | **done — axiom-clean** | **C** | Continuous-threshold self-trust follows from the one-sided fixed-portfolio bridge. `SelfTrustQuote` retains positive `δ`, rational-probability/code hypotheses, and the world-dependent `payout(φₙ)` product semantics. |
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
| `thm:provind` (sequence forms) | `lic_provind` (paper theorem); `buySeq`, `buySeq_ec`, `lic_provind_seq` (same-day support) | **done — faithful theorem repaired, axiom-clean** | **C/P** | `lic_provind` takes polynomial sentence codes and only requires each theorem/negation to appear at *some* deductive stage, exactly allowing the paper's much-later proof time `f(n)`. It is the one-share specialization of `affine_provind_theory_eq`, itself derived from `affcoh`. The older direct trader remains clearly labeled as the stronger-premise `φₙ ∈ Dₙ` support lemma. |
| `thm:provind` (base case) | `lic_deducible_price_near_one` | done | **C** | the loop closed against `def:lic`: under `[IsLogicalInductor]`, an always-deducible `φ` has `1−ε < Pₙφ` for some n, ∀ε>0. **Special case** (always-deducible, uniformly underpriced); general `thm:provind` is M3 |
| `def:tradermag` | `Strategy.magnitude`, `Trader.magnitude`, `abs_value_le_magnitude` | done | Def+P | magnitude + the `\|value\| ≤ magnitude` bound proved (needs `[0,1]` prices + `{0,1}` world) |
| `def:roi` / repeatable ROI | `HasROI`; `Trader.Matured`; `EfficientlyEmulatable`; `PolyTradeEmulatable`; Boolean `sharedFeatureWeight`/`repeatableROI`/`VerifiedMaturitySchedule`; continuous `fractionalWeight`, `fractionalSharedFeatureWeight`, `fractionalBudgetedTrader`, `noFractionalRepeatableReturn` (`Engine.lean`, `ROI.lean`) | **Boolean and continuous hubs done** | **Def+P** | Complete Appendix A.2-style Boolean closure plus its maturity-oracle-free continuous analogue. The fractional hub proves the unit-capital invariant for decreasing `[0,1]` occupancy, reifies every adaptive weight with a shared `letE` chain, uniformly emits the combined family trader, recycles capital when each occupancy eventually vanishes, proves exploitation from recurrent positive launch risk, and concludes launch risks converge to zero under a logical inductor. This is the correct affine specialization because `gradualRemaining` is decreasing, rank-legal price-feature syntax. Remaining work is concrete affine-family token interfaces and instantiation, not budget infrastructure. Axiom-clean. |
| `lem:type3` (sparse ROI interface) | `allocationPrefix_not_bddAbove_of_frequently`, `sharedBudgetedTrader_exploits_of_frequently`, `repeatableROI_of_frequently`, `noRepeatableROI`, `noRepeatableROI_of_verifiedMaturity` (`ROI.lean`) | **done, conditional on a domain-specific verified maturity checker** | **P+C** | Removes the provisional uniform-positive-magnitude restriction: zero-magnitude components between opportunities consume no budget, and magnitudes merely frequently bounded below force unbounded allocation. The verifier-facing theorem proves `αₖ → 0` from a `VerifiedMaturitySchedule`; its generic polynomial openness construction is complete and axiom-clean. Remaining work is concrete rather than budgeter infrastructure: build the checker's rational finite-day predicate for the affine component family from `ComputableMarket`/`ComputableDeductiveProcess`. |
| `thm:affpolymax` (analytic + continuous family construction hubs) | `NoPreemptiveUnderpricing`, `NoPreemptiveOverpricing`, `affineFutureHigh`, `affineFutureLow`, `BoundedAffinePrices`, `affpolymax_of_noPreemptiveGaps`; `AffineCombination.PolySequence` (+`.neg`); `gradualRemaining`, `gradualOccupancy`, `gradualFamily`, `gradualFamilyPolyTrade`, `gradualRisk_converges`, `noPreemptiveUnderpricing`, `noPreemptiveOverpricing`, `noPreemptiveGaps`, `affpolymax` (`Affine.lean`, `ROI.lean`, `Properties/AffinePreemptiveLearning.lean`) | **done — axiom-clean** | **P** | Exact limit equalities, gradual-sale economics, continuous capital recycling, all uniform syntax emitters, structured family emulation, and the logical-inductor contradiction forcing launch risk to zero are kernel-checked. Finite-prefix gates absorb eventual hypotheses; zero launch-risk components no longer require artificial closing days. Persistent low/high gaps force a frequently positive risk subsequence, contradict convergence. The overpricing half reuses the construction through a certified polynomial pointwise-negation transform and `Real.sSup_neg`. |
| affine semantic bridge | `PolySequence.buyBelowTrader` (+ value/e.c.), `PolySequence.affine_provind`, `PolySequence.affine_tendsto_zero` (`Properties/AffineProvability.lean`) | **done — axiom-clean** | **P+C** | A continuous buy-below affine trader turns eventual uniform plausible-world value bounds into diagonal `AsympGE`; certified negation gives the two-sided zero limit. This is the reusable semantic half of the LUV lift. |
| `thm:ei` / `thm:loe` / `thm:expprovind` | `LUV.expectAffine`, `indicatorAffine`, `linearityAffine` and their `PolySequence` certificates; `lic_expectation_indicator`, `lic_linearity_of_expectation`, `lic_expectation_provind` (`Properties/ExpectationAffine.lean`) | **done — axiom-clean** | **P+C** | Exact price/value identities plus the `1/n` world approximation discharge all three formerly parked expectation statements. The linearity family emits `3n` terms with polynomial selectors for coefficients and threshold sentences. `#print axioms` for each theorem contains only `propext`, `Classical.choice`, and `Quot.sound`. |
| `thm:cee` / `thm:ceu` / `thm:ccee` / `thm:st` | four declarations in `Properties/SelfTrust.lean` | **done — axiom-clean** | **C over disclosed quote interface** | The former cross-grid blocker is repaired by theorem-specific quote certificates carrying delayed semantics plus a fixed polynomial affine portfolio and its actual deferred-day law. The reusable preemptive bridges perform the learning step; all four theorem bodies are kernel-checked. The quotation/coherence certificate remains a disclosed M7 construction obligation, not a hidden consequence of `PolyThresholdCodeSeq`. |
| **`def:tf`** | `EF` (inductive), `EF.denote`, `EF.cost`, `EF.rank` (`Criterion.lean`) | done | Def | keystone DSL: price/const/add/mul/max/safeRecip. `denote` noncomputable (ℝ inv); `cost` = structural node count — **disclosed `dd:fuel` deferral:** precise unary day/code charging tying `cost` to poly-runtime is M2, when the trader e.c. cert first consumes it |
| `def:tf` (continuity) | `EF.continuous_denote` | done | **P** | continuity **proved** for the whole DSL (not left as a stated constraint), by induction; safeRecip via `max 1 · ≥ 1 > 0`. Hyps `(b)` (Mathlib `continuous_apply`/`Continuous.{add,mul,max,inv₀}`). This is what breaks the price/trade circularity for Brouwer |
| `def:tf` (ring) | `EF.ExpressibleRankLE`/`EFn`, `CommRing (EFn n)` | done | **P** | `𝔼_n` realized as a **`Subring` of `History → ℝ`** (features are functions): carrier `{denote e \| rank e ≤ n}`, closure under `+,×,neg` proved; `CommRing` inherited. Faithful to the paper's "𝔼_n is a commutative ring" `(b)` |
| `def:tf` (non-vacuity) | `EF.exMaxDiff` + 2 `example`s | done | **N+** | the paper's `max(0, φ*6−ψ*7)`: rank `= 7` and value `= 0.3` at the paper's inputs; plus safeRecip lands in `(0,1]` for all args. Genuine (non-constant) witnesses |
| `lem:fpl` (dep) | `brouwer_fixed_point` | **done** | P | **proved from scratch** (Sperner/Kuhn over the Freudenthal triangulation → fixed point on compact convex `K ⊆ EuclideanSpace ℝ (Fin d)`). Provenance: **autoformalized by Harmonic's Aristotle** (runs `1d7dc5e0`/`c712e6d9`, built there on Lean/Mathlib v4.28.0), dropped in verbatim modulo namespace + header, **revalidated on this project's toolchain** (v4.28.0-rc1, Mathlib master@58d8468): builds green, `#print axioms` = `propext, Classical.choice, Quot.sound` (checked in-file). Trust surface = the final statement only (unchanged from the M0 `sorry` version); the ~1300-line `BrouwerProof.*` interior is machine-generated proof plumbing nobody has read — the kernel has checked it, a human has not, which is exactly the division of labor the standard permits. Imports trimmed from the Aristotle original's `import Mathlib` umbrella to the 7-module minimal set found by `linter.minImports`. |
| `lem:fpl` (strategy finite-dimensionalization) | `Strategy.support`, `Strategy.shares`, `Strategy.value_eq_sum_support`; `strategyValuation`, `strategyHistory`, `strategyCube`, `priceAdjustment` and continuity/compactness/convexity API | **done (M6)** | Def+P | `(a,b)`; actual `Strategy n` syntax is used. Repeated occurrences of one sentence are aggregated before adjustment, so one sentence never receives conflicting coordinate prices. The cube is indexed only by the finite syntactic support; outside-support prices are exactly zero. DSL continuity is inherited from `EF.continuous_denote`; compactness/convexity and the fixed point are Mathlib/in-project foundations. |
| `lem:fpl` | `fixed_point_lemma` | **done (M6), axiom-clean** | P | `(a,b)`; for every actual day strategy and prior history, constructs a support-contained `[0,1]` valuation whose one-day value is `≤0` in every `PCWorld`. The proof uses the real aggregate price-adjustment map and `brouwer_fixed_point`, not an assumed fair-price certificate. Statement audit: paper's finite support and Boolean-world inequality are exact; repository days are 0-based and p.c. worlds use Foundation Boolean models. |
| `def:markemaker` | `RationalBeliefState`, `MarketMakerAccepts`, `marketMakerCandidate`, `marketMakerSearchIndexUpTo`, `marketMakerSearchUpTo`, `MarketMaker`, `MarketMaker_search_clock`, support/range/error laws | **done (M6)** | Def+P/C | `(a,b,c)`; a uniform executable fuel recursion decodes one finite rational association list per tick and decides all finite support-bit worlds using exact rational arithmetic. Rational density proves a stopping clock exists, and `MarketMaker_search_clock` identifies its output with the first accepted candidate. `MarketMaker` is decoded with `Option.get`, not `Classical.choose`; its proof fields only validate finite tables. Modeling substitution: the clock is exposed as a Lean recursive program plus kernel theorem rather than separately recompiled to `Nat.Partrec.Code`; this is the repository's executable witness, while the paper only requires computability. |
| `lem:mm` | `marketMakerStates`, `marketMakerHistory`, `marketMaker_day_value_le`, `sum_marketMakerError`, `marketMaker_netWorth_lt_one`, `marketMaker_not_exploited` | **done (M6)** | P/C | `(a,b,c)`; course-of-values recursion feeds each day the exact prior rational states. The 0-based allowance `2^{-(n+1)}` sums to `<1`, hence every plausible assessment is `<1` for every trader/world/day and `Exploits` is refuted for every deductive process. This is the paper's `2^{-n}` schedule after the disclosed day-index shift. No Budgeter/TradingFirm/LIA premise appears. |

### Active M6 completion contract (set 2026-07-14)

M6 is complete only when: the strategy-level fixed point, concrete uniformly clocked
rational `MarketMaker`, and recursive-history inexploitability theorem are all proved; the
paper statements `lem:fpl`, `def:markemaker`, and `lem:mm` have been compared line by line;
the flat ledger discloses every substitution; no Budgeter/TradingFirm/LIA result is counted;
targeted and full builds, executable-hole scan, `git diff --check`, and capstone axiom reports
all pass.  This is also the active tool-level goal; partial analytic progress does not close it.

The statement comparison and modeling-disclosure packet is
`notes/m6-verification-packet.md`. In particular, “clocked” here means the literal total
fuel-bounded Lean evaluator `marketMakerSearchUpTo` plus its existence/correctness theorem;
M6 does not claim a polynomial clock, and M7 remains wholly unstarted.

**M6 exit audit (2026-07-14):** `lake build LogicalInduction.Construction` passed
2,426/2,426 jobs and full `lake build` passed 2,671/2,671. The executable source scan found
no `sorry`, `admit`, or `sorryAx` (historical prose mentions excluded); `git diff --check`
passed. `#print axioms` for `fixed_point_lemma_bounded`, `fixed_point_lemma`,
`MarketMaker_search_clock`, and `marketMaker_not_exploited` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. M6 is closed; M7 is not started.

## M5 verification ledger

This is the flat acceptance inventory for the completed M5 verification goal. `pending` means
that no paper-facing declaration has yet passed statement alignment, kernel/build, axiom,
e.c., and trust-surface review. An existing hub is evidence only for the named hub, not for a
stronger consequence. Every row must become `done` with a concrete declaration and evidence
before M5 can exit.

Concrete post-M5 representation witnesses referenced below:

- **M7-HIST-EVALN:** construct a `PolyFueled` bounded universal `Code.evaln` simulator,
  compile the finite maturity checker and uniformly emulatable bias-run family to one fixed
  code, and thereby discharge `BiasRunHistoricallyVerifiable` from the logical inductor's
  market/process programs.
- **M7-COMP-SYNTAX:** instantiate `RepresentedSemidecidableClaims`,
  `RepresentedDecidableClaims`, and `InconsistentTheoryClaims` with the repository's future
  first-order/Gödel syntax, proving polynomial sentence emission and the computation-
  representation laws. These interfaces contain no prices or asymptotic conclusions.
- **M7-QUOTE-AFFINE:** construct the current/future quotation LUVs and the concrete
  `CompletedAffineQuoteEq`/`AffineQuoteEq` portfolios from first-order quotation syntax and
  encoding coherence. For `thm:ref`, the compiler must consume the closed polynomial
  `GeneratedRatFeature`s witnessing the paper's market-generated endpoints, rather than an
  independently computable rational table. The M5 interfaces expose the actual uniformly
  emitted portfolio and completed-world or deferred-price law; they do not contain the
  downstream asymptotic market conclusion.
- **M7-PATIENT-CLOCK:** compile the bounded historical settlement dovetail and the monotone
  envelope `max_{k≤i} f(k)` to the polynomial Boolean activity table used by
  `PatientSettlementClock`. Its interface exposes only decreasing activity, sound finite
  settlement, and eventual completion—no prices, divergence, bias, or diagonal conclusion.
- **M7-FEEDBACK-EMIT:** instantiate `FeedbackTraderEmissionSigns` by bounded-dovetailing
  the deferral program on day `n` and emitting the exact open/close coefficient and sentence
  streams of `feedbackTrader` for every small rational Kelly fraction and both affine signs.
  Each `FeedbackTraderEmission` reconstructs the trader's literal trade list and carries
  only polynomial token syntax—no market values, wealth, bias, or exploitation.
- **M7-FEEDBACK-TRUTH:** construct `FeedbackTruthSequence` from the paper's
  `poly(f(k+1))` completed-theory-value computation. Its member at day `f(k+1)` is the
  centered affine combination `A_{f k}-ThmValue(A_{f k})`; all other representation and
  padding choices are computational. The interface packages the paper's completed-theory
  determination premise and exposes zero completed-world value and exact diagonal syntax,
  not delayed-price accuracy (which Lean derives via `affprovind`).
- **M7-PREFIX-PATCH:** compile the concrete `EF.freezeBefore` transformation on a
  token-emitted trader, using an efficiently presented finite-day rational quote table.
  This closes the exact gap between the paper's claim that old quotes can be “hard-coded”
  and the repository's weaker `ComputableMarket` premise, whose quote program has no
  polynomial clock. The witness must establish `EfficientPrefixPatch.preserves_ec`; all
  rank, semantics, finite error accounting, exploitation transport, and the final
  biconditional are already proved independently of this compiler.
- **M7-CE-REPETITION:** instantiate `EfficientRepeatedEnumeration` from the future
  concrete code for a c.e. sentence stream by triangularly repeating every enumerated
  member and padding the emission schedule to polynomial time. The witness proves only
  polynomial sentence emission, infinite repetition, and source/target membership in
  both directions; it contains no prices, limiting beliefs, or non-dogmatism conclusion.
- **M7-PREFIX-MACHINE:** instantiate `PrefixMachinePresentation`,
  `OccamThresholdEmission`, and `PrefixNegationCompiler` from a concrete universal prefix
  machine. The witness must efficiently enumerate sentence codes, emit convergent
  from-below Kraft-weight approximations and the two derived rational gate tokens, prove
  the finite Kraft inequality/coverage, and compile syntactic negation with one fixed
  additive program-length overhead. These interfaces contain no market prices, worlds,
  exploitation, or Occam inequality.
- **M7-DUS-APPROX:** instantiate `DUSApproximationPresentation` and
  `DUSThresholdEmission` from the universal semimeasure's unrestricted lower
  approximation by the paper's bounded-simulation slowdown. The witness emits only the
  rational from-below table and the two derived gate tokens, and proves convergence to
  prefix mass; it contains no market prices, purchases, worlds, or domination conclusion.
- **M7-DUS-PREFIX-SYNTAX:** instantiate `BitPrefixSentences` with fresh independent atoms,
  polynomial prefix-sentence emission, exact bit-prefix semantics, and explicit finite
  realizability in a world consistent with each deductive stage. This supplies only the
  syntax/possible-world bridge consumed by `prefix_possible`; it contains no market price,
  trader payoff, semimeasure domination, or asymptotic conclusion.
- **M7-STRICT-SEPARATORS:** instantiate `StrictSeparatorPresentation` from the paper's
  disjoint c.e. machine-index sets `A₀,A₁`. The witness must emit their nested finite
  separator constraints, supply the existing efficient-repetition preprocessing, prove
  finite joint realizability, and formalize the computability-theory argument that every
  universal continuous semimeasure assigns their separator class mass tending to zero.
  The interface contains no market prices or strict-domination conclusion.
- **M7-SCON-COMPILER:** instantiate `GatedConditioningOperationalWitness` after the
  paper's finite-prefix denominator patch. The remaining witness must supply the positive
  rational denominator floor, the exact computable rational conditional-market program,
  and a polynomial token transducer for the concrete `Trader.conditionedTranslation`.
  The cap gate, per-position inequality, total loss `≤1`, zero value after a failed
  condition, first-failure downside floor, exploit transport, and LIC conclusion are now
  theorems outside the interface. The interface contains no wealth, boundedness,
  exploitation, or logical-inductor conclusion.
- **M7-SCON-PRESENTATION:** instantiate `ConditioningPresentation` from the concrete
  first-order conjunction compiler and combined deductive process, proving polynomial
  conjunction emission, exact stagewise union semantics, and computability of the combined
  process. It contains no conditional price program, trader, wealth, exploitation, or LIC
  conclusion; those remain in `M7-SCON-COMPILER` and the proved capstone.
- **M7-LUV-SYNTAX:** instantiate the LUV/LUV-combination representation packages used by
  the expectation tail: `PolySequence`, `WorldValued`, `ConvergencePresentation`,
  `ExactTheoryPresentation`, and `MeshSoftmaxOperationalWitness`. The witness must compile
  threshold codes and the soft-max mesh and prove their exact daily/world semantics,
  polynomiality, bounds, and magnitude. It contains no expectation limit, persistence,
  bias, pseudorandom-learning, or preemptive-learning conclusion.

| Label | Paper theorem | Lean declaration / current evidence | Status | Kind / provenance and remaining verification |
|---|---|---|---|---|
| `thm:perkno` | Persistence of Knowledge | `lic_persistence_of_knowledge`; `sentenceMinusProbability_polySequence`; one-sided wrappers and `knowledgeFutureDeviation_asympEq_zero` | **done — exact three clauses, targeted build green, axiom-clean** | **C/P** `(a,b)`; the legal centered progression `φₙ-pₙ` consumes both compact code witnesses, so the varying rational target is genuinely emitted rather than treated as an arbitrary function. Operational `peraffkno` gaps yield uniform future `sSup`/`sInf` bounds; their conjunction bounds the exact `sup_{m≥n}|P_m(φₙ)-pₙ|`. The explicit `[0,1]` rational-probability premise records the paper's word “probabilities.” |
| `thm:tbo` | Preemptive Learning | `lic_preemptive_learning`; `AffineCombination.sentenceAffine_polySequence` | **done — targeted build green, axiom-clean** | **C** `(a,c)`; exact one-share specialization of `PolySequence.affpolymax`. `PolySentenceCodes` is the disclosed token-model rendering of the paper's e.c. sentence sequence; the wrapper proves the exact `sSup`/`sInf` equalities with `m = n+j`. Explicit `[0,1]` price and plausible-world hypotheses are fields omitted from the repository's thin `History`/`DeductiveProcess` substrate, not forcing inequalities. |
| `thm:affprovind` | Affine Provability Induction | `PolySequence.affine_provind_theory_ge`; `_le`; `_eq` (with `PolySequence.affine_provind` retained as the finite-stage hub) | **done — paper completed-theory wrappers, targeted build green, axiom-clean** | **P+C** `(a,c)`; the paper premise quantifies over `ConsistentWithTheory`, not same-stage plausible worlds. `affcoh` converts its pointwise completed-world bound into the diagonal liminf/limsup bound; order theory yields the exact `≳ₙ`, `≲ₙ`, and `≈ₙ` forms. No silent identification of the two world notions remains. |
| `thm:affcoh` | Affine Coherence | `PolySequence.affcoh`; `completedTheoryLow_le_limitingValue`; `eventually_affineValue_gt_of_theory`; `PolySequence.eventualMember` | **done — exact two chains, targeted build green, axiom-clean** | **C/P** `(a,b)`; `ConsistentWithTheory` is the intersection of the finite deductive stages. The missing uniformization is proved by an actual compact-product argument over Boolean worlds: formula model sets and fixed-affine sublevel sets are closed, so arbitrarily late finite countermodels yield a completed-theory countermodel. A legal padded constant-member `PolySequence` then feeds the existing affine provability trader, establishing both pointwise world/`P∞` bounds; `peraffkno` supplies the `P∞`/diagonal links. |
| `thm:peraffkno` | Persistence of Affine Knowledge | `AffineCombination.PolySequence.peraffkno`; `noPersistenceUnderpricing`; `noPersistenceOverpricing`; `persistencePortfolioPoly` | **done — exact theorem, targeted 1,712-job build green, axiom-clean** | **P+C** `(a,b)`; both uniform future-extrema equalities. The Appendix day-indexed construction is an explicit polynomial prefix portfolio: it continuously buys every earlier underpriced member, normalizes by total entry weight, proves rank/segment/sentence emission, bounded magnitude/prices, and maps every tail dip to a non-vacuous full launch. It then consumes the already verified `affpolymax` gradual round-trip/continuous-budget trader rather than duplicating that ROI engine. The overpricing half is the uniformly emitted negation. This is not a pointwise-convergence shortcut. |
| `thm:peraffkno` (analytic/`P∞` infrastructure) | `limitingBelief`, `lic_limitingBelief_tendsto`, `AffineCombination.price_tendsto_limitingValue`, `AffineNoPersistenceGaps`, `peraffkno_of_noPersistenceGaps` | **done as support layer — targeted build green, axiom-clean** | **Def+P** `(a,b)`; canonical limiting valuation, fixed-affine convergence, extrema/limit sandwich, and exact liminf/limsup capstone. The operational no-gap premise is now discharged by the prefix-portfolio construction above. |
| `thm:affpolymax` | Affine Preemptive Learning | `BoundedCombinationSequence.affpolymax`; arbitrary-bound `PolySequence.affpolymax`; `l1Norm`; `scaleRat`; bounded-normalization transports | **done — exact BCS theorem, regression repaired, targeted build green, axiom-clean** | **P** `(a,b)`; the audit found that the former public theorem silently required unit magnitude and omitted the trailing constant from the paper's BCS norm. `BoundedCombinationSequence` now uses the full coefficient `L¹` norm, including the constant; bounded prices follow from `[0,1]`; a positive rational scale normalizes any real uniform bound; all three no-gap conditions transport back; and the exact paper extrema equalities follow. `lic_preemptive_learning` now consumes this paper-facing theorem directly. |
| `thm:recunbiasedaff` | Affine Recurring Unbiasedness | `AffineCombination.BoundedCombinationSequence.recunbiasedaff`; `BoundedCombinationSequence.unitNormalization`; `DeterminedViaTheory.recunbiasedaff_of_historicalVerifiers`; `biasRunTrader`; `biasRunTrader_polyTrade`; `BiasRunHistoricallyVerifiable` | **done as exact arbitrary-BCS conditional capstone; outer historical-dovetail M7 witness remains explicit** | **P/C** `(a,c)`; the paper-facing declaration now quantifies over the actual arbitrary-bound `BCS`, chooses one positive rational unit normalization, requests the verifier only for that concrete normalized family, invokes the fully proved unit-risk economic hub, and cancels the scale from the exact zero limit point. The hub supplies completed-theory determination, compactness, continuous capping, Abel ROI, a real uniform token certificate, both one-sided contradictions, negation transport, and vanishing-step crossing. `M7-HIST-EVALN` remains only the conclusion-free bounded universal-`evaln` simulator and outer dovetail constructor. |
| `thm:wubaff` | Affine Unbiasedness from Feedback | `AffineCombination.BoundedCombinationSequence.wubaff`; `BoundedCombinationSequence.unitNormalization`; `lic_wubaff`; `feedbackTrader_ecTok`; `feedbackTrader_netWorth_lower`; `feedbackTrader_exploits_of_frequently_positive_return`; `FeedbackTruthSequence.accurate` | **done as exact arbitrary-BCS conditional capstone; two concrete M7 witnesses remain explicit** | **P/C** `(a,c)`; the paper-facing wrapper normalizes every arbitrary `BCS`, formulates the emitter and sparse truth bridge for that canonical family, and cancels the positive scale from all-day `weightedBias ≈ₙ 0`. The unit hub's actual sparse joined trader opens `δ·Wealth·W` shares at `f k` and closes at `f(k+1)`; finite accounting proves a global floor and genuine unbounded upside. Support-image reindexing, both signs, and weighted-Cesàro transfer are proved. `M7-FEEDBACK-EMIT` and `M7-FEEDBACK-TRUTH` contain no bias or convergence. |
| `thm:prandaff` | Learning Pseudorandom Affine Sequences | `AffineCombination.BoundedCombinationSequence.prandaff_{above,below}`; `.prandaff`; `BoundedCombinationSequence.unitNormalization`; `DeterminedViaTheory.lic_prandaff_{above,below}_of_historicalVerifiers`; `deferralEnvelope`; `PatientSettlementClock`; `patientUnderpriceWeight_pgenerable`; `patientUnderpriceWeight_divergent` | **done as exact arbitrary-BCS conditional capstone in all directions; operational M7 witnesses remain explicit** | **C/P** `(a,c)`; all three paper comparison directions now quantify over an arbitrary `BCS`. The wrappers scale the determined truth and pseudorandomness by one positive rational, request the clock/verifiers for exactly that normalized family, invoke the unit selector proof, and cancel the scale from the original diagonal prices. The selector retains launches through `max_{k≤i}f(k)`, so no monotonicity of `f` is assumed; its token emitter, legal `[0,1]` weighting, patient bound, and non-vacuous divergent recycling are proved. `M7-HIST-EVALN` and `M7-PATIENT-CLOCK` contain no market conclusion. |
| `thm:simcal` | Recurring Calibration | `calibrationIndicator`; `calibrationIndicator_pgenerable`; `simcal_of_recurring_unbiasedness`; `AffineCombination.simcal_of_historicalVerifiers` | **done as exact conditional capstone; inherits `M7-HIST-EVALN`** | **P/C** `(a,c)`; the continuous selector, no-false-positive support law, divergence-aware normalization, ordinary recurring-unbiasedness specialization, and both exact calibration conclusions are green. The only operational premise is the same conclusion-free historical verifier already disclosed for `recunbiasedaff`; no calibration conclusion is stored in it. |
| `thm:recurringunbiasedness` | Recurring Unbiasedness | `weightedAverage_step_tendsto_zero`; `hasLimitPoint_zero_of_two_sided_recurring`; `AffineCombination.TheoryTruth`; `AffineCombination.recurringunbiasedness_of_historicalVerifiers` | **done as exact conditional specialization; inherits `M7-HIST-EVALN`** | **P** `(a,c)`; the one-share sentence specialization, Boolean completed-theory truth stream, economic contradiction, crossing, and exact zero limit point are green. The shared verifier boundary supplies only executable historical maturity checking and contains no bias or limit-point conclusion. |
| `thm:wub` | Unbiasedness From Feedback | `AffineCombination.lic_wub` | **done as exact conditional specialization; inherits the two explicit M7 feedback witnesses** | **P/C** `(a,c)`; the paper states this as the one-share special case of `wubaff`. `sentenceAffine_polySequence` supplies the legal affine family, `TheoryTruth` proves its completed-theory determination, and `sentenceAffine_price`/`sentenceAffine_magnitude` reduce the capstone to the ordinary weighted truth-minus-price bias. The same support, deferral, price/world bounds, `M7-FEEDBACK-EMIT`, and `M7-FEEDBACK-TRUTH` boundaries are inherited unchanged; no additional representation premise is introduced. |
| `thm:benford` | Learning Pseudorandom Frequencies | `PseudorandomFrequency`; `constantRatFeature_generated`; `PseudorandomFrequency.varied{Above,Below}_of_lt`; `PseudorandomFrequencyInfrastructure`; `lic_learning_pseudorandom_frequency_{above,below}`; `lic_learning_pseudorandom_frequency` | **done as exact conditional rational squeeze; 1,717-job roll-up green, axiom-clean** | **C** `(a,c)`; the frequency `p : ℝ` is not silently assumed rational. `PseudorandomFrequency` quantifies over every legal P-generable, divergent, `f`-patient weighting and requires its weighted truth average to converge to `p`. For each ε and interior side, Lean selects a fresh rational `q∈[0,1]`, proves the one-token closed constant feature is genuinely market-generable, derives the appropriate varied-pseudorandom premise, and invokes `prand`; `p=0` and `p=1` use the pointwise probability bounds. `PseudorandomFrequencyInfrastructure` exposes only the already ledgered settlement clocks and historical verifiers for these rational centered families—no price, pseudorandomness, convergence, or learning conclusion. |
| `thm:prand` | Learning Varied Pseudorandom Frequencies | `VariedPseudorandom{Above,Below}`; `sentenceMinusFeature`; `sentenceMinusFeature_polySequence`; `TheoryTruth.sentenceMinusFeature_determined`; `lic_learning_varied_pseudorandom_{above,below}`; `lic_learning_varied_pseudorandom` | **done as exact conditional specialization; 1,717-job roll-up green, axiom-clean** | **C** `(a,c)`; all three comparison directions specialize `prandaff` to the actual centered market-feature family `φₙ-pₙ`. The rational target is not silently strengthened to an independently computable sequence: `GeneratedRatFeature` supplies the paper's market-generated feature, uniform token stream, legal rank, closed semantics, and exact rational denotation. Completed-theory determination and the exact diagonal identity `Pₙ(φₙ)-pₙ` are separately proved. Operational verifier/settlement hypotheses are inherited unchanged from `prandaff`. |
| `thm:lex` | Learning Logical Relationships | `lic_learning_exclusive_exhaustive`; `exclusiveExhaustive_polySequence`; additional `lic_lex_tendsto_zero`, `lic_imp_eventually_le` consequences | **done — exact paper theorem restored, targeted build green, axiom-clean** | **C/P** `(a,b,c)`; the audit found that the row had mislabeled fixed equivalence/implication results as the paper theorem. The actual theorem now handles a fixed positive `k`, a genuinely uniform polynomial tuple emitter for the `k` sentence sequences, a semantic completed-theory exact-one premise, and proves the diagonal sum converges to `1`. The semantic premise is the disclosed propositional rendering of `Theory ⊢` exclusive/exhaustive and contains no price or convergence conclusion. |
| `thm:ifp` | Closure under Finite Perturbations | `EF.freezeBefore`; `Strategy.freezeBefore`; `Trader.freezeBefore`; `freezeBefore_netWorth_difference_le`; `Trader.Exploits.of_boundedDifference`; `EfficientPrefixPatch`; `lic_iff_of_finitePerturbation` | **done as a conditional biconditional that is STRICTLY WEAKER than the paper's `thm:ifp`; one concrete M7 compiler remains explicit** | **P/C** `(a)` + **paper erratum**; the paper's false-report transformation is literal syntax, never raises rank, preserves structural cost, has exact tail semantics, and differs in net worth by an explicit finite sum of magnitudes. Bounded error transports genuine bounded-downside/unbounded-upside exploitation in both directions. **Reclassified 2026-07-16 (was `(a,c)`, "exact conditional biconditional", "a real model mismatch"): this is not a `(c)` substitution — our `ComputableMarket` matches `def:marketprocess` exactly (computable sequence of pricings, no finite support: TeX line 681, and line 995 confirms the generalization is deliberate). The defect is in `app:ifp`, which asserts the freeze is e.c. because "only finitely many constants are needed" — false. See "Paper errata".** `EfficientPrefixPatch` is therefore not a routine obligation: it is **uninhabited for some legal markets**, so `lic_iff_of_finitePerturbation` does not cover every finite perturbation and must not be cited as `thm:ifp`. Non-vacuous for `LIA` (finite `RationalBeliefState` table ⇒ hardcodable lookup); `M7-PREFIX-PATCH` is that witness and contains no semantic or LIC conclusion. Targeted 1,693-job build green; all printed declarations axiom-clean. |
| `thm:nd` | Non-Dogmatism | `lic_nonDogmatism`, `lic_nonDogmatism_dual`, `lic_limit_pos`, `lic_limit_lt_one` | **done — M5 regression green, axiom-clean** | **P+C** `(a,c)`; the positive and negative scale-ladder traders retain genuine uniform token certificates and non-vacuous plausible-world upside. `lic_limit_pos` corresponds to `Theory ⊬ ¬φ`; `lic_limit_lt_one` corresponds to `Theory ⊬ φ`. Persistent satisfying/falsifying worlds are the explicit propositional rendering of those non-provability premises. Targeted 1,694-job build green. |
| `thm:obu` | Uniform Non-Dogmatism | `lic_uniform_nonDogmatism`; `lic_uniform_nonDogmatism_repeating`; `exists_obu_fire_of_low_limit`; `obuTrader_exploits`; `obuTrader_ecTok`; `EfficientRepeatedEnumeration` | **done — exact conditional capstone, targeted 1,705-job build green, axiom-clean** | **P/C** `(a,c)`; the actual varying-sentence scale ladder spends at most `1/j²` on rung `j`, has a global `-2` downside bound, and obtains unbounded plausible-world wealth from one full trigger per rung in a world satisfying the entire enumeration. Fixed-sentence convergence plus infinite repetition turns any sub-threshold limiting belief into such a trigger. The conclusion is one common positive lower bound for every source member. `EfficientRepeatedEnumeration` is the disclosed paper preprocessing boundary: it contains only a polynomial repeated sentence stream and exact source membership/coverage; `M7-CE-REPETITION` supplies the future c.e.-syntax compiler. No price or limit conclusion is assumed. |
| `thm:ob` | Occam Bounds | `prefixWeight`; `PrefixMachinePresentation`; `OccamThresholdEmission`; `PrefixNegationCompiler`; `obTrader`; `obTrader_ecTok`; `obTrader_netWorth_ge_neg_two`; `obTrader_exploits`; `lic_occam_lower`; `lic_occamBounds` | **done — exact conditional two-sided capstone, 1,951-job roll-up green, axiom-clean** | **P/C** `(a,c)`; one literal trader diagonalizes the paper's scale family: rung `j` risks at most `1/j²`, the total floor is `-2`, and a full possible-world trigger pays order `j²`. Its real token certificate traverses the variable-width day/sentence/rung/history triangle via the proved prefix scanner; no whole-strategy oracle is assumed. `lic_occam_lower` forces one common multiple of `2^{-κ(φ)}` for all unrefutable sentences. `lic_occamBounds` uses the audited exclusive–exhaustive limit theorem plus the fixed syntactic negation overhead to obtain the upper inequality with the **same** constant. `M7-PREFIX-MACHINE` is the only representation witness and carries syntax/Kraft/compiler facts only—no price or limiting conclusion. The file has no `sorry`/`admit`/`sorryAx`, `git diff --check` is clean, and every printed declaration exposes only `propext`, `Classical.choice`, and `Quot.sound`. |
| `thm:dus` | Domination of the Universal Semimeasure | `ContinuousSemimeasure`; `LowerSemicomputableContinuousSemimeasure`; `UniversalContinuousSemimeasure`; `BitPrefixSentences`; `DUSApproximationPresentation`; `DUSThresholdEmission`; `semimeasureMean_root_le_max`; `dusMeanPayoutThrough_le_prefixPurchaseMax`; `exists_consistent_dusGrossPayout_ge_mean`; `exists_dusMeanPayout_ge_of_low_limit`; `dusScaleTrader`; `dusScaleTrader_netWorth_ge_neg_one`; `dusScaleTrader_ecTok`; `dusTrader`; `dusTrader_netWorth_ge_neg_two`; `dusTrader_exploits_of_failed_scales`; `dusTrader_ecTok`; `lic_domination_universalSemimeasure` | **done — exact conditional capstone, targeted build green, axiom-clean** | **C/P** `(a,c)`; continuous mass, unrestricted `Code.evaln` lower approximation, and `MeanPayout ≤ MaxPayout` are kernel-checked. The equivalent one-prefix-per-day dovetail revisits every prefix cofinally; the shared feature recurrence has a global floor, and a violating prefix yields non-vacuous same-day plausible-world upside via an explicit maximizing branch. The diagonal trader has total downside at most `2`, unbounded upside under failed domination, and a literal token certificate. Two distinct conclusion-free M7 witnesses are now tracked: `M7-DUS-APPROX` for bounded-simulation/rational tokens and `M7-DUS-PREFIX-SYNTAX` for `BitPrefixSentences` polynomial syntax, exact independent-bit semantics, and finite realizability. |
| `thm:strict` | Strict Domination of the Universal Semimeasure | `StrictSeparatorPresentation`; `strict_domination_of_null_prefix_theory`; `lic_strict_domination_universalSemimeasure` | **done as exact conditional capstone; concrete M7 separator witness remains explicit** | **P/C** `(a,c)`; this proves genuine non-domination, not a definitional counterexample. Uniform Non-Dogmatism supplies one positive limiting-probability floor for the entire jointly possible nested separator theory; universal-semimeasure mass tending to zero then defeats every fixed positive multiplier at some finite prefix. `M7-STRICT-SEPARATORS` is the precise remaining computability-theory instantiation of the recursively inseparable c.e. sets from the paper. Its fields expose nested prefixes, unbounded length, legal repetition, finite joint realizability, and null semimeasure mass—no market price or strict-domination conclusion. Both declarations are axiom-clean. |
| `thm:scon` | Closure Under Conditioning | `conditionalQuote`; `conditionedHistory`; `conditioningBudget`; `ConditioningPresentation`; `gatedConditionalPosition_lower`; `Trader.conditionedTranslation`; `ConditioningPresentation.conditionedTranslation_preserves_floor`; `GatedConditioningOperationalWitness`; `lic_conditioned_gated` | **done as exact conditional gated capstone; two operational M7 witnesses remain explicit** | **P/C** `(a,c)`; the exact capped ratio, `[0,1]` law, stagewise union semantics, patched safe reciprocal, and recursive price-leaf rewrite are kernel-checked. The actual two-stock translator's polynomial telescoping budget yields cumulative loss `≤1`; false conditions freeze wealth at a prior combined-plausible prefix, and exploitation transport is proved. `M7-SCON-PRESENTATION` now separately tracks the conjunction/compiler/combined-process boundary, while `M7-SCON-COMPILER` tracks the finite denominator patch, conditional quote program, and trader-token transducer. Neither contains wealth, exploitation, or an LIC conclusion. |
| `thm:expcoh` | Expectation Coherence | `LUVCombination.BoundedSequence.expcoh`; `meshAffine`; `limexpapprox`; `completedExtrema_mesh_tendsto`; `PolySequence.affcoh` | **done — exact conditional lift, standalone build green, axiom-clean** | **C/P** `(a,c)`; proves the paper's two completed-world/limiting-expectation/diagonal liminf–limsup chains. `MeshSoftmaxOperationalWitness`, `WorldValued`, and `ConvergencePresentation` expose only threshold-code/world-value/convergence representation data; `M7-LUV-SYNTAX` is the concrete syntax witness. The analytic mesh approximation, completed-extrema transfer, and affine-coherence consumption are proved in Lean. |
| `thm:perexpkno` | Persistence of Expectation Knowledge | `LUVCombination.BoundedSequence.perexpkno`; `futureLow`; `futureHigh`; `limexpapprox`; `PolySequence.peraffkno` | **done — exact conditional lift, standalone build green, axiom-clean** | **C/P** `(a,c)`; both paper equalities between uniform future expectation extrema and limiting expectation are proved. The same narrowly stated LUV syntax/value/convergence boundaries are used; no persistence equality is stored in them. Threshold-mesh error is shown to vanish uniformly before the exact liminf/limsup transfer. |
| `thm:exppolymax` | Expectation Preemptive Learning | `LUVCombination.BoundedSequence.exppolymax`; `futureLow`; `futureHigh`; `mesh_independence`; `BoundedCombinationSequence.affpolymax` | **done — exact conditional lift, standalone build green, axiom-clean** | **C/P** `(a,c)`; proves both cross-day expectation extrema equalities for arbitrary bounded LUV-combination sequences. The affine mesh is a genuine polynomial bounded-combination sequence, the mesh/expectation gap tends to zero, and the repaired arbitrary-bound `affpolymax` theorem supplies the economic core. `MeshSoftmaxOperationalWitness` contains only the executable soft-max threshold family and no theorem conclusion. |
| `thm:recurringunbiasednessexp` | Expectation Recurring Unbiasedness | `LUVCombination.BoundedSequence.recurringunbiasednessexp`; `ExactTheoryPresentation`; `normalizedMesh`; `weightedAverage_tendsto_zero_of_tendsto_zero`; `DeterminedViaTheory.recunbiasedaff_of_historicalVerifiers` | **done as exact intended theorem; paper has a recorded stray-`f` erratum; inherited M7 verifier remains explicit** | **C/P** `(a,c)`; TeX mentions support in the image of an unbound `f`; the coherent intended reading, matching ordinary recurring unbiasedness and the appendix proof, is every divergent weighting, which Lean proves (strictly stronger than any fixed-support restriction). Exact truth is approximated by the completed-world mesh at `O(b/n)`; normalization, affine recurring unbiasedness, and a proved Toeplitz transfer yield the zero limit point. |
| `thm:wubexp` | Expectation Unbiasedness From Feedback | `LUVCombination.BoundedSequence.wubexp`; `normalizedMesh`; `weightedBias_const_mul`; `weightedAverage_tendsto_zero_of_tendsto_zero`; `AffineCombination.lic_wubaff` | **done as exact intended theorem; paper has a recorded omitted-support erratum; inherited feedback M7 witnesses remain explicit** | **C/P** `(a,c)`; TeX omits the good-feedback support-in-image premise used by the ordinary/affine theorem and its own proof; Lean records that necessary intended premise explicitly. The normalized mesh instantiates the real feedback trader and delayed-truth bridge, cancels scale, and transfers from mesh truth to exact truth. `M7-FEEDBACK-EMIT` and `M7-FEEDBACK-TRUTH` remain conclusion-free. |
| `thm:prandexp` | Learning Pseudorandom LUV Sequences | `LUVCombination.BoundedSequence.prandexp`; `.prandexp_below`; `.prandexp_eq`; `ExactTheoryPresentation.normalizedMeshTruth_pseudorandom{Above,Below}`; `DeterminedViaTheory.lic_prandaff_{above,below}_of_historicalVerifiers` | **done as exact conditional capstone in all three comparison directions; standalone build green, axiom-clean** | **C/P** `(a,c)`; the paper-facing `≳ₙ` theorem and its stated analogous `≲ₙ`/derived `≈ₙ` variants are all present. A reusable Toeplitz perturbation theorem transfers exact-truth pseudorandomness to the normalized threshold mesh, affine `prandaff` proves the mesh-price comparison, and positivity cancels normalization. The settlement clock and historical verifiers are precisely `M7-PATIENT-CLOCK`/`M7-HIST-EVALN`; neither contains pseudorandomness or a price conclusion. |
| `thm:pac` | Belief in Finitistic Consistency | `lic_belief_finitistic_consistency`; `RepresentedDecidableClaims` | **done — conditional representation lift, targeted roll-up green, axiom-clean** | **C** `(a,c)`; exact Provability-Induction proof for every true finite consistency search. Compact syntax for an arbitrary fixed computable bound is certified by `sentence_poly`; truth-to-theorem representation is explicit and contains no market conclusion. Concrete Gödel-syntax instantiation is `M7-COMP-SYNTAX`. |
| `thm:pazfc` | Belief in Consistency of a Stronger Theory | `lic_belief_stronger_theory_consistency`; `RepresentedDecidableClaims` | **done — exact intended conditional lift; paper has a recorded unbound-`f` erratum** | **C** `(a,c)`; TeX uses `f` without binding it; Lean implements the coherent reading for an arbitrary fixed computable bound encoded by the represented decidable-claims interface. The proof is the exact reduction for any true finitistic stronger-theory consistency predicate; concrete syntax remains `M7-COMP-SYNTAX`. |
| `thm:incons` | Disbelief in Inconsistent Theories | `lic_disbelief_inconsistent_theories`; `InconsistentTheoryClaims` | **done — exact two conclusions over explicit representation, targeted roll-up green, axiom-clean** | **C** `(a,c)`; separately polynomial inconsistency/consistency sentence families yield timely convergence to `1` and `0`. The interface exposes both eventual theoremhood facts rather than silently identifying the abstract consistency sentence with syntactic negation; concrete theory coding is `M7-COMP-SYNTAX`. |
| `thm:halts` | Learning of Halting Patterns | `CodeHalts`; `lic_learns_halting_patterns`; `RepresentedSemidecidableClaims` | **done — conditional representation lift, targeted roll-up green, axiom-clean** | **C** `(a,c)`; machines are actual `Nat.Partrec.Code`s and runtime is unrestricted. Only the represented halting-sentence sequence must have a `PolySentenceCodes` emitter; true halting yields eventual theoremhood. Concrete sentence construction is `M7-COMP-SYNTAX`. |
| `thm:loops` | Learning of Provable Non-Halting Patterns | `lic_learns_provable_nonhalting_patterns` | **done — exact provably-nonhalting premise, targeted roll-up green, axiom-clean** | **C** `(a,c)`; “provably fails to halt” is stated directly as eventual occurrence of each negated represented halting sentence. It does not assume semantic completeness for arbitrary non-halting programs. |
| `thm:dontwait` | Learning not to Anticipate Halting | `CodeHaltsWithin`; `lic_does_not_anticipate_halting`; `RepresentedDecidableClaims` | **done — conditional representation lift, targeted roll-up green, axiom-clean** | **C/P** `(a,c)`; the polynomial sentence emitter may compactly mention an arbitrary fixed computable horizon program. The proof explicitly turns a successful bounded `evaln` result into unbounded halting and contradicts actual non-halting before applying the false half of Provability Induction. Concrete compact syntax is `M7-COMP-SYNTAX`. |
| `thm:ref` | Introspection | `IntrospectionIntervalQuote`; `IntrospectionIntervalQuote.{lower,upper}_pgenerable`; `ctsInd_mem_Icc`; `lic_introspection` | **done — exact market-generated-endpoint conditional quotation theorem, targeted build green, axiom-clean** | **P/C** `(a,c)`; the endpoint fields are now closed `GeneratedRatFeature`s, hence exactly `PGenerableRat P a` and `PGenerableRat P b`, rather than the narrower independently polynomial rational tables caught by the fresh audit. The package also exposes positive computable widths, represented interval syntax, and the two completed-world-zero affine products—never an error or belief conclusion. Lean derives both daily implications and constructs positive rational `εₙ → 0`. `M7-QUOTE-AFFINE` explicitly must compile quotation syntax from those generated features. |
| `thm:lp` | Paradox Resistance | `ParadoxResistanceQuote`; `lic_paradox_resistance`; `ctsInd_eq_one_of_le_sub` | **done — conditional diagonal-quotation theorem, targeted roll-up green, axiom-clean** | **P/C** `(a,c)`; for rational `p∈(0,1)`, two concrete polynomial affine products are zero in every completed-theory world. Lean proves that any persistent price gap below or above `p` saturates the relevant continuous gate and keeps one product uniformly positive, yielding the exact `Pₙ(χₙᵖ)≈p` conclusion. The certificate contains no convergence field; diagonal syntax/portfolio construction is `M7-QUOTE-AFFINE`. |
| `thm:epr` | Expectations of Probabilities | `CurrentPriceExpectationQuote`; `CompletedAffineQuoteEq`; `lic_expectations_of_probabilities` | **done — conditional same-day quotation theorem, targeted roll-up green, axiom-clean** | **C** `(a,c)`; one explicit polynomial affine portfolio has current price `Pₙ(φₙ)-Eₙ(quote(Pₙ(φₙ)))` and value zero in every completed-theory world. `affprovind` forces its price gap to zero; positive normalization is removed analytically. Concrete quote syntax is `M7-QUOTE-AFFINE`. |
| `thm:er` | Iterated Expectations | `CurrentExpectationQuote`; `lic_iterated_expectations` | **done — conditional same-day quotation theorem, targeted roll-up green, axiom-clean** | **C** `(a,c)`; the same completed-affine quotation hub proves `Eₙ(Xₙ)≈Eₙ(quote(Eₙ(Xₙ)))`. This is a same-day completed-theory identity, distinct from the deferred Self-Trust results. Concrete quote syntax is `M7-QUOTE-AFFINE`. |

Current tranche evidence (2026-07-13): the targeted `TimelyLearning` and
`AffinePersistence` builds are green, their new public declarations report only
`propext`, `Classical.choice`, and `Quot.sound`, and a full `lake build` completed all
2,656 jobs. A syntax-shaped source scan for executable `sorry`, `admit`, or `sorryAx`
found no hits. (The broader word scan finds only “admit” in a closed documentation
comment in `Properties/Convergence.lean`.) `git diff --check` is clean. This is tranche
evidence, not M5 exit evidence: the construction and audit gates below remain open.
The completed `peraffkno` implementation and roll-up then passed a fresh targeted
1,712-job build and a fresh post-implementation full 2,656-job build; its portfolio
certificate, both economic halves, and paper-facing capstone all expose only the same
approved foundational axioms. The subsequent exact three-clause `perkno` specialization
passed its targeted file build and exposes only those same axioms. The completed
`perkno → affcoh → affprovind → provind` tranche then passed a 1,714-job roll-up/integration
build and a fresh 2,657-job full build; its new integration consumer and all printed
paper-facing declarations expose only the same approved axioms.

The first recurring-unbiasedness infrastructure tranche is now green in
`Properties/Calibration.lean` and imported by the property roll-up. Its analytic
calibration/crossing layer, completed-theory compactness bridge, capped-run summability and
full-risk proofs, Abel ROI theorem, canonical rate family, family-uniform recurrence emitter,
and `PolyTradeEmulatable` certificate are kernel-checked. The named paper nodes remain
pending because the concrete verified-maturity checker and resulting logical-inductor
contradiction have not yet been discharged. The authoritative property roll-up completed
all 1,714 jobs and the full-project regression completed all 2,658 jobs. A Lake-only
`autoImplicit := false` failure in the first attempt exposed one missing explicit history
parameter; that declaration was repaired before the green builds. The executable
`sorry`/`admit`/`sorryAx` scan is empty (its sole broad-text hit remains the documented
“admit” wording in `Properties/Convergence.lean`), and `git diff --check` is clean.

The subsequent exact-verification tranche added exact rational trader semantics, finite
Boolean restriction/payout preservation, named market/process computation presentations,
and uniqueness of every terminating clocked output. The axiom-clean
`UnitMaturitySemanticCertificate.sound` theorem now discharges the semantic heart of the
historical checker: a rational risk bound and exhaustive finite-world rational payoff bound
imply the repository's universal real-valued maturity predicate. Its axiom-clean
`nonempty_iff_matured` converse constructs an explicit aggregate atom bound and proves the
finite semantic format can certify every genuine unit-magnitude maturity witness. The name and ledger are
intentional—the proposition-valued semantic object is not itself an encoded payload. The
tranche was then extended with monotone bounded quote/stage decoding, exact bounded
whole-strategy and whole-prefix evaluation, and `unitMaturityCheckAtFuel`. The checker is
executable and exhaustive over its finite support; `unitMaturityCheckAtFuel_sound` rules out
false positives, and `unitMaturityCheckAtFuel_eventually_complete` combines all finite
market queries and the deductive stage at one fuel to rule out permanent false negatives
for genuine unit maturity. The remaining representation obligation is no longer the finite
checker: it is the `PolyFueled` universal bounded-`evaln` simulator needed by the outer
historical dovetail, plus compilation of the uniformly emulatable bias-run family into that
fixed checker.
The post-tranche targeted calibration build completed all 1,707 jobs and printed only the
approved `propext`, `Classical.choice`, and `Quot.sound` axioms for the new soundness,
completeness, clocked-uniqueness, and clocked-eventuality propositions. A fresh full-project
regression then completed all 2,658 jobs, including the property roll-up and integration
test. `git diff --check` is clean; the syntax-shaped trust scan finds no executable proof
placeholder (only pre-existing documentation prose containing the words “admit”/“sorry”).

The executable-checker extension was revalidated on 2026-07-14: the targeted calibration
build completed all 1,707 jobs and the full-project regression completed all 2,658 jobs.
The three new checker axiom reports (`certificate`, `sound`, and
`eventually_complete`) contain only `propext`, `Classical.choice`, and `Quot.sound`.
`git diff --check` remains clean, and the only broad placeholder-word scan hits are
documentation prose in `Convergence.lean`, `Criterion.lean`, and `Coherence.lean`.

The completed affine/frequency-pseudorandomness tranche was then revalidated on
2026-07-14: `lake build LogicalInduction.Properties` completed all 1,717 jobs and a fresh
full `lake build` completed all 2,661 jobs after `prandaff`, `prand`, and the arbitrary-real
`benford` squeeze. Every newly printed selector, generated-feature, one-sided, and
paper-facing capstone declaration exposes only `propext`, `Classical.choice`, and
`Quot.sound`. `git diff --check` is clean; the syntax-shaped placeholder scan has no
executable hit (the sole displayed `admit` remains closed documentation prose in
`Properties/Convergence.lean`).

The explicit affine-feedback Kelly tranche was validated later on 2026-07-14:
`lake build LogicalInduction.Properties.Pseudorandomness` completed all 1,941 jobs and a
fresh full `lake build` completed all 2,661 jobs. The constructed trader's feature
semantics, finite-sum accounting, `-1` global downside, `Wealth/2-1` feedback-day upside,
non-vacuous exploitation theorem, structured-emitter `EfficientlyComputableTok` capstone,
logical-inductor contradiction, and delayed-truth `affprovind` bridge all print only
`propext`, `Classical.choice`, and `Quot.sound`. `git diff --check` is clean and the
syntax-shaped placeholder scan of `Pseudorandomness.lean` is empty. The later capstone
pass proved the weighted-Cesàro/bias contradiction, exact support-image reindexing, sign
dual, and final conditional `lic_wubaff`; the two concrete M7 feedback witness constructors
remain open. This is completion evidence for the conditional `wubaff` node, not M5 exit
evidence.

Fresh capstone verification on 2026-07-14: the expanded `Pseudorandomness` target again
completed all 1,941 jobs, and the full project completed all 2,661 jobs. Printed axioms
for the weighted-Cesàro lemma, sparse-mass divergence, all-day support transfer, one- and
two-sided bias theorems, and `lic_wubaff` are exactly `propext`, `Classical.choice`, and
`Quot.sound`. The subsequent one-share specialization `lic_wub` passed the same 1,941-job
target and 2,661-job full regression and has the same axiom inventory.

Expectation-tail completion and current M5 mechanical exit evidence (2026-07-14):
`ExpectationProperties.lean` now contains exact `exppolymax`, `perexpkno`, `expcoh`,
`recurringunbiasednessexp`, `wubexp`, and paper-facing `prandexp`, plus the appendix's
analogous below and derived equality variants. The exact-truth transfer uses a proved
Toeplitz theorem for nonnegative divergent weights; no weighted-error convergence is hidden
in a witness. `IntegrationTest.lean` exercises that reusable hub and discharges a public
`prandexp` consumer through the roll-up. `lake build LogicalInduction.Properties
LogicalInduction.IntegrationTest` completed **1,958/1,958** jobs and a fresh `lake build`
completed **2,670/2,670** jobs. The syntax-shaped scan for executable `sorry`, `admit`, or
`sorryAx` is empty; the broad word scan finds only explanatory prose in old comments.
`git diff --check` is clean. Every newly printed expectation and integration declaration
depends only on `propext`, `Classical.choice`, and `Quot.sound`.

Accordingly, the implementation and mechanical portions of gates 1–6 are recorded.
Anson confirmed the complete statement/definition read-through in the project thread on
2026-07-14, closing gate 7. Gate 8 is now also closed:

The review checklist, paper anchors, exact Lean declarations, sign-off blocks, boundary
inventory, and author-context pre-audit are collected in
`notes/m5-verification-packet.md`.

1. **Fresh-context adversarial audit — PASS (2026-07-14).** The independent auditor found
   no kernel defect, conclusion-in-premise, trader vacuity, or unsupported economics. It did
   find two real paper-scope gaps and incomplete boundary tracking: unit-only public affine
   statistical capstones, independently polynomial rather than market-generated `thm:ref`
   endpoints, and missing concrete M7 obligations. These are repaired by the canonical BCS
   normalization wrappers, `GeneratedRatFeature` endpoint fields, and the expanded M7
   inventory. Three TeX inconsistencies (`recurringunbiasednessexp`, `wubexp`, `pazfc`) are
   explicitly triaged. The correction re-audit checked all affected declarations, found no
   new circularity/vacuity, reran the relevant Lean files, and returned PASS. Full evidence
   and exact source anchors are in `notes/m5-verification-packet.md` section B.

## M3 statement inventory and audit handoff

Flat inventory for Anson's statement read-through. These are the milestone-facing declarations;
implementation helpers and trader certificates are mapped to them in the node ledger above.
`done` means kernel-checked without `sorryAx`. The four Self-Trust types now consume the
explicit fixed-portfolio quote certificates described below; their type-`(c)` quotation
boundary remains a statement-audit target and an M7 construction obligation.

- `lic_deducible_price_near_one` — `Properties/ProvabilityInduction.lean:94` — base finite-stage provability-induction contradiction (`done`).
- `lic_deducible_eventually_ge` — `Properties/ProvabilityInduction.lean:164` — an always-deducible fixed sentence is eventually priced above every `1−ε` (`done`).
- `lic_deducible_tendsto_one` — `Properties/ProvabilityInduction.lean:179` — fixed-sentence `thm:provind`, price converges to one (`done`).
- `lic_provind` — `Properties/AffineCoherence.lean` — faithful efficiently computable theorem/disprovable sequence `thm:provind`, with deductions allowed at arbitrary later stages (`done`).
- `lic_provind_seq` — `Properties/ProvabilityInduction.lean:230` — stronger same-day-deduction support lemma, not the paper-facing theorem (`done as support`).
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
- `lic_expectation_indicator` — `Properties/ExpectationAffine.lean` — expectation of a relational indicator tracks the sentence price (`done`, `thm:ei`).
- `lic_linearity_of_expectation` — `Properties/ExpectationAffine.lean` — world-linked affine combinations become asymptotically linear in expectation (`done`, `thm:loe`).
- `lic_expectation_provind` — `Properties/ExpectationAffine.lean` — a world-level lower bound forces the corresponding expectation lower bound (`done`, `thm:expprovind`).
- `lic_expected_future_expectations` — `Properties/SelfTrust.lean` — current and quoted future expectations agree asymptotically from a certified fixed-portfolio quote (`done`, `thm:cee`).
- `lic_no_expected_net_update` — `Properties/SelfTrust.lean` — current prices agree with expectations of their quoted future prices (`done`, `thm:ceu`).
- `lic_no_expected_net_update_conditional` — `Properties/SelfTrust.lean` — conditional/weighted expected future expectations agree (`done`, `thm:ccee`).
- `lic_self_trust` — `Properties/SelfTrust.lean` — continuous-threshold self-trust inequality (`done`, `thm:st`).
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
- `AffineQuotePortfolio` / `AffineQuoteEq` / `AffineQuoteGE` — `Properties/SelfTrust.lean` — normalized fixed-portfolio syntax, uniform polynomial emission, exact current-gap identity, bounded risk, and deferred-day coherence.
- The four theorem-specific quote certificates — `Properties/SelfTrust.lean` — bundle revelation-schedule `ValuesAt` linkages, compact source syntax, and the operational cross-grid certificate; these are interfaces rather than canonical quote constructors.

Fresh-context audit is still a separate human/session gate: the proof-writing context must not
perform it. Give the auditor the API table in `notes/next-session.md` §2 and this inventory.
Known audit bait: (1) relational `ValuesAt`/`IsIndicator` linkages must not encode their
conclusions; (2) Self-Trust quote certificates must preserve delayed revelation, must not
smuggle back an oracle-`DP` witness, and their explicit fixed-portfolio `n`/`f n` law must
eventually be constructed—not merely re-assumed—by M7's quotation mechanism; (3) Non-Dogmatism's persistent-world hypotheses are the
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
