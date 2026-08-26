# complexitylib adoption — architecture / feasibility / vendoring audit

_Scoping pass, 2026-08-24. No strength claim, coverage tier, paper label, or AxiomAudit
endpoint changes in this PR; see §11._

> **Part V (below, same date) lands the machine trader class and enumeration coverage, and
> finds that Stage 3 does not close.** Two items remain, both diagnosed rather than
> half-attempted: soundness needs a clocked simulator (§V.3, 600–1,200 lines, larger than
> Part IV assumed), and the TradingFirm integration turns out to depend on Stage 2 (§V.4).
> **The recommended ordering is now Stage 2 before Stage 3's TradingFirm migration** — an
> inversion of what the earlier passes assumed. §IV.6's table is superseded by §V.6.
>
> **Part IV closes Stage-3 coverage down to the enumeration index.**
> `TM.exists_singleTape_computesInTime` — Part II's riskiest remaining theorem — landed
> upstream at 195 lines, confirming it was an exposure problem rather than new simulation
> mathematics. The chain from `f ∈ FP` to a `TMDesc` computing `f` under an explicit
> `a·(n+1)^k + a` clock is now proved end to end. Read §IV.0 for the chain and §IV.5 for the
> exact remaining plan. §III.10's table is superseded by §IV.6.
>
> **Part III is the productionization pass.** The fork is stood up and
> pinned, `DescExec` is a CI-built module, output extraction is closed, and `machineTokens`
> with `Primrec₂ machineTokens` is landed. Read §III.0 for the layered architecture as
> built, and §III.2 for the finding that FAF's import surface is 5 files / ~2.2k lines
> rather than the fork's 26k. Part II's §II.9 table is superseded by §III.10.
>
> **Part II supersedes two of Part I's estimates.** The Stage-3
> executability bottleneck is retired — see §II.0 and §II.5 — and the port cost for the
> path Stage 3 actually needs is 36 lines, not 100–250 (§II.2). Part I's §14 totals and
> §15 answers 10, 15, 16, 17 and 18 are revised in §II.9–§II.11. Everything else in
> Part I stands, including §10 on `thm:ifp`.

Audited against `SamuelSchlesinger/complexitylib` @ `b673821` (branch `dev`,
"Merge pull request #21 from BoltonBailey/feat/bitstring-encoding"), toolchain
`leanprover/lean4:v4.30.0`, Mathlib `v4.30.0`, Apache-2.0. FAF side audited at
`5ad35c4` (`origin/main`), toolchain `v4.31.0`, Mathlib `v4.31.0` (`fabf563a`).

Every claim below is cited to a declaration and file. Where a probe was compiled, the
result is reported as measured, including what did **not** build.

---

## 0. Executive summary

Six findings drive the whole recommendation.

1. **The repository is 329,048 lines across 987 files**, not the ~6k the scoping prompt
   assumed. Vendoring calculus changes accordingly.
2. **`Complexity.FP` is genuinely function-facing** — `Set (List Bool → List Bool)`, not a
   decider class. This is the right target for `def:ec`.
3. **Every public UTM theorem is decider-shaped**, but the *internal* Hoare postcondition
   and the single-tape correspondence invariant are already **function-strength**. The
   function-facing universal theorem is a thin wrapper over machinery that exists — but
   the wrapper does not exist upstream, and two intermediate links are missing.
4. **complexitylib has essentially no contact with Mathlib's `Primrec`/`Encodable` API**
   (2 hits repo-wide, both in `DescriptiveComplexity/ModelChecking`). Its tapes are
   `ℕ → Γ` *functions*. FAF's `LIACompiler` needs `Primrec₂` over the trader enumeration.
   **This is the single largest gap and it is not closed by anything upstream.**
5. **The 4.30 → 4.31 port is real but uniformly mechanical.** Measured, not guessed:
   `Classes.P.Defs` builds clean after a 4-line patch to one file; the full Stage-3+Cobham
   slice reaches 64/134 modules with 32 remaining errors in 7 files, *all* of one category.
6. **The useful slice is ~35k LOC, not "a few thousand."** For comparison, FAF's two
   existing vendored bodies are PFR at 6,071 LOC and ProvabilityLogic at 10,393 LOC.

**Recommendation: Strategy 3 — a pinned compatibility fork at FAF's Lean/Mathlib pin,
consumed as a Lake dependency** (§5). Not vendoring: 35k lines is 3.4× FAF's largest
vendored body and the port must be re-done on every toolchain bump. Not upstream-direct:
the toolchain gap is load-bearing and FAF's pin cannot move.

**One premise in the brief is wrong and should be corrected before planning:** moving
`def:ec` to genuine machine-polytime does **not** make the general `thm:ifp` inhabitable.
The obstruction there is information-theoretic (output size), not an artifact of the fuel
model, and it survives the move verbatim. See §10 — this is the most consequential
correction in this audit.

---

## 1. Audit of complexitylib

### 1.1 Scale

| area | files | LOC |
| --- | ---: | ---: |
| `Models/` | 460 | 160,348 |
| `Classes/` | 196 | 78,455 |
| `Circuits/` | 219 | 49,066 |
| `SAT/` | 59 | 28,252 |
| `Languages/` | 11 | 5,770 |
| everything else | 42 | 7,157 |
| **total** | **987** | **329,048** |

Within `Models/TuringMachine/`: `Subroutines/` 27,688 · `UTM/` 23,681 ·
`Combinators/` 7,060 · `SingleTape/` 6,676 · `Registers/` 5,951.

### 1.2 Machine core — `Complexitylib/Models/TuringMachine.lean` (905 LOC)

```lean
structure TM (n : ℕ) where          -- n work tapes + read-only input + output tape
  Q : Type                          -- ← bundled Type, NOT a Fin
  [decEq : DecidableEq Q] [finQ : Fintype Q]
  qstart qhalt : Q
  δ : Q → Γ → (Fin n → Γ) → Γ → Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3
  δ_right_of_start : …             -- no head falls off the left edge, structurally
```

Alphabet `Γ = {zero, one, blank, start}`, writable `Γw = {zero, one, blank}` — the
start marker cannot be written, enforced by the type of `δ`. `Tape` is
`{head : ℕ, cells : ℕ → Γ}`, one-sided, with writes at cell 0 a structural no-op.

The two predicates that matter (`TuringMachine.lean:529,536`):

```lean
def DecidesInTime (tm : TM n) (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ x, ∃ c' t, t ≤ T x.length ∧ tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
    (x ∈ L → c'.output.cells 1 = Γ.one) ∧ (x ∉ L → c'.output.cells 1 = Γ.zero)

def ComputesInTime (tm : TM n) (f : List Bool → List Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x, ∃ c' t, t ≤ T x.length ∧ tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
    c'.output.HasOutput (f x)
```

`reachesIn` (`:514`) is an inductive with an explicit step count — **not** a transitive
closure. This is exactly the property FAF's Stage-0 survey found missing from Mathlib
(`boundary-efficiency-model.md`: "the step count is destroyed at the statement"). It is
the single strongest reason to take complexitylib seriously.

**Note `Q : Type` is a bundled type.** A `TM n` is therefore *not* a finite object and
cannot be enumerated directly. Enumeration must route through `TMDesc` (§1.4).

### 1.3 `FP` — `Complexitylib/Classes/P/Defs.lean` (41 LOC)

```lean
def FP : Set (List Bool → List Bool) :=
  {f | ∃ (d k : ℕ) (tm : TM k) (T : ℕ → ℕ), tm.ComputesInTime f T ∧ T =O (· ^ d)}
```

Answering the brief's "we care primarily about functions": **`FP` is a function class,
stated over `ComputesInTime`, with no decider detour.** Available closure results:

| lemma | file | statement |
| --- | --- | --- |
| `mem_FP_comp` | `Classes/P/Composition.lean:24` | `f ∈ FP → g ∈ FP → g ∘ f ∈ FP` |
| `id_mem_FP` | `Classes/P.lean:63` | `id ∈ FP` |
| `mem_FP_pairWithInput` | `Classes/P/PairWithInput.lean:25` | `f ∈ FP → (x ↦ pair (f x) x) ∈ FP` |
| `ite_mem_finset_mem_FP` | `Classes/P/FinsetDomain.lean:37` | finite-support override is in `FP` |
| `mem_P_preimage` | `Classes/P/Preimage.lean:25` | `f ∈ FP → L ∈ P → f ⁻¹' L ∈ P` |
| `unaryLength_mem_FP` | `Classes/P/UnaryLength.lean:25` | `x ↦ 1^{|x|} ∈ FP` |
| — | `Classes/P/NormalForm.lean:39` | `f ∈ FP ↔ ∃ k tm (p : Polynomial ℕ), …` |

This is a usable closure kit, and `ite_mem_finset_mem_FP` is directly relevant to §10.

### 1.4 Universal simulation — the eight questions

`Complexitylib/Models/TuringMachine/UTM/` is 34 files, 23,681 LOC. Public surface is
`UTM/Universal.lean` (123 LOC), three theorems.

**(1) Function outputs or deciders only?** **Deciders only.** All three of
`utmTM_simulates_decider` (`:47`), `utmTM_universal` (`:78`), `utmTM_universal_padded`
(`:101`) conclude
`(x ∈ L → c'.output.cells 1 = Γ.one) ∧ (x ∉ L → c'.output.cells 1 = Γ.zero)` —
a single verdict cell. Confirmed mechanically: **`ComputesInTime` does not occur anywhere
in `UTM/`, `SingleTape/`, or `Deterministic.lean`.**

**(2) Can the machinery expose full output?** **Yes — and this is the decisive finding.**
The decider theorem is a *weakening of a stronger internal result*. `utmTM_hoareTime`
(`UTM/Internal/SimLoop.lean:681`) has postcondition

```lean
fun _ _ out => ∃ m, m ≤ T ∧
  mcF.output.cells (m + 1) = Γ.blank ∧
  (∀ j, j < m → mcF.output.cells (j + 1) ≠ Γ.blank) ∧
  (∀ j, j ≤ m → out.cells (j + 1) = mcF.output.cells (j + 1))
```

`m` is exactly the first-blank position, and the UTM's output agrees with the simulated
machine's on cells `1 … m+1`. That is precisely the shape of

```lean
def Tape.HasOutput (t : Tape) (y : List Bool) : Prop :=
  (∀ i (h : i < y.length), t.cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
  t.cells (y.length + 1) = Γ.blank
```

`Universal.lean:62` calls `hagree 0` and throws the rest away. Recovering `HasOutput`
needs only that `Γ.ofBool b ≠ Γ.blank` (immediate by `cases`) to identify `m = |f x|` by
uniqueness of the first blank. **Estimated 40–80 lines.**

The same holds one level down: the multi-tape → single-tape correspondence invariant
carries `outputEq : c1.output = c.output` — *full tape equality*
(`SingleTape/Internal/Correctness.lean:50`) — while the public
`TM.exists_singleTape_decidesInTime` (`Deterministic.lean`) exposes only cell 1, via a
lemma (`halts_rev_cell1`) that was deliberately "strengthened from the accept bit to the
exact cell value". Strengthening it again to the whole tape is following a path already
walked, but it is **not free**: it means re-deriving `singleTapeSim_computesInTime`,
`pad0_computesInTime`, and a `ComputesInTime` analogue of `toTM_decidesInTime` (whose
`RejectsWithZero` output-discipline side condition has no function counterpart and
should simply disappear).

**(3) Canonical finite description?** Yes. `TMDesc` (`UTM/Internal/Desc.lean:101`):
`⟨w : ℕ, qstart qhalt : ℕ, entries : List DescEntry⟩`, `DecidableEq`, first-match-wins
`lookup` with a total `defaultAct` fallback. `TM.descOfTM` (`UTM/Internal/Interp.lean:91`)
produces one from a `TM 1` — **it is `noncomputable`** (it goes through
`Fintype.equivFin`), which is fine for existence statements but is a real obstacle for
§8's effective-evaluation requirement.

**(4) Roundtrip proved?** Yes: `decodeDesc_encodeDesc` (`Desc.lean:504`) and
`decodeDesc_encodeDesc_append` (`:479`, roundtrip under arbitrary padding), both under
`TMDesc.WF` (every state field `< 2^w`), which `descOfTM_wf` (`Interp.lean:102`)
discharges for machines in range.

**(5) Overhead?** `utmTime α T n = 4*(2*|α|+2+n) + 4*|groupPairs α| + 25 + ((T+1)*utmStepTime α + 1 + (2T+9))`
— **linear in `T`** with per-description constants. The quadratic factor in
`utmTM_universal` comes solely from the single-tape reduction,
`singleTapeSimTime k T = fun n => 16*(k+1)*(T n + n + 1)^2`. Both are explicit closed
forms, not `O`-notation. Excellent for FAF's purposes.

**(6) Fixed simulator?** Yes — `utmTM` is one fixed six-work-tape machine
(`UTM/Machine.lean`), independent of the simulated program; the program arrives on the
input tape as `pair α x`.

**(7) Malformed-code safety?** Yes. `decodeDesc : List Bool → TMDesc` (`Desc.lean:394`)
is **total**, and `TMDesc.lookup` falls back to `defaultAct` (halt, write back what was
read, all heads stay). Any bitstring denotes *some* machine. Ideal for enumeration.
One caveat: `utmTM_simulates_decider` carries a `TerminatedRegion α` side condition, and
the discharging lemmas (`terminatedRegion_encodeDesc{,_plain}`) apply to *encoded*
descriptions, not to arbitrary bitstrings. An enumeration over raw bitstrings must either
route through `encodeDesc ∘ decodeDesc` (idempotent on well-formed input) or prove
`TerminatedRegion` is decidable-and-recoverable. **This is a real, unglamorous loose end.**

**(8) Enumerable as bitstrings without a normal-form theorem?** **Yes**, subject to (7).
`decodeDesc` totality is exactly the property that makes a raw-bitstring enumeration
sound with no additional machine-normal-form work. This is a genuine gift.

### 1.5 Cobham — `Classes/P/Cobham*` (38 files, 11,671 LOC in `Classes/P`)

Fully proved, **both directions, at every arity**:

```lean
theorem CobhamFP_subset_FP : CobhamFP ⊆ FP          -- Cobham.lean:79
theorem FP_subset_CobhamFP : FP ⊆ CobhamFP          -- Cobham.lean:86
theorem CobhamFP_eq_FP     : CobhamFP = FP          -- Cobham.lean:92
theorem cobham_iff_FPn {n} {f : (Fin n → List Bool) → List Bool} : Cobham f ↔ FPn f
```

The algebra: projections, `empty`, bit successors `x ↦ b :: x`, `smash x y = 1^(|x|·|y|)`,
closed under composition and **limited recursion on notation** — where the recursion's
output must be length-bounded by another function *of the class* (`Cobham.boundedRec`).
Bitstrings are LSB-first.

**Does it shorten Stage 2? On the evidence, no — recommend against.** Three reasons:

- *It does not avoid the encoding work.* `evaln`'s state is `Option ℕ` over `Nat.pair`-coded
  values; Cobham is a `List Bool` algebra. The pair/unpair and `Option` plumbing has to be
  built inside the algebra either way, and the algebra is a *less* convenient place to do
  it than a TM with subroutines, because there is no intermediate storage — only
  composition and bounded recursion.
- *`boundedRec` demands the hard half of the work up front.* Every recursive `evaln`
  case (`prec`, `rfind'`) must be accompanied by a **length bound witnessed by a Cobham
  function**. FAF's `PolyFueled` supplies `IsPolyBounded f` — a bound of the shape
  `a·(n+1)^k + a` on the *value* — so the bound exists, but transporting it into a
  member of the algebra means building polynomial length bounds out of `smash`, which is
  precisely the fiddly part of Cobham formalizations. A TM route just runs a clock.
- *It costs the most and buys a lemma we can get for free.* `Classes.P.Cobham` closes over
  **103 files / 34,140 LOC** — because `Cobham.lean` imports the non-public
  `Cobham/Internal.lean`, which carries *both* directions, and the `FP ⊆ CobhamFP`
  direction needs the whole TM simulation stack. There is no way to take only the
  soundness direction without upstream refactoring. Adding Cobham to the Stage-3 slice
  takes it from 34,698 to **54,861 LOC** — a 58% increase for a route we would not use.

Cobham's theorem is beautiful and its presence speaks well of the library. It is not
load-bearing for FAF and should be **excluded** from any slice.

---

## 2. Lean / Mathlib compatibility — measured

This was the blocking practical question, so it was tested rather than estimated.

**Setup.** `complexitylib` @ `b673821` copied to a scratch tree, `lean-toolchain` set to
`v4.31.0`, `lakefile.toml` re-pointed at **FAF's already-built Mathlib v4.31.0**
(`~/AgentFoundations/.lake/packages/mathlib`, 6.2 GB of oleans). No 6 GB download, no
second Mathlib build — this is the cheap way to run this experiment and is worth
remembering.

Note complexitylib uses Lean's **new module system** (`module` / `public import` /
`@[expose] public section`). This caused **zero** problems on 4.31; Mathlib is on it too.

### Wave 0 — minimal `FP` slice

`lake build Complexitylib.Classes.P.Defs` → **1989/1992 targets built**, one file failed:
`Complexitylib/Asymptotics.lean`, 4 errors, all from `convert … using 1` now descending
into the `Norm ℝ` instance so `ext` searched there ("No applicable extensionality theorem
found for type `Norm ℝ`").

Fix — replace `convert`+`ext` with a direct cast rewrite, e.g.

```lean
-  have key := IsBigO.mul h₁ h₂
-  convert key using 1
-  · ext n; push_cast; ring
-  · ext n; push_cast; ring
+  simpa only [Nat.cast_mul] using IsBigO.mul h₁ h₂
```

**4 such edits in 1 file** → `Build completed successfully (1992 jobs)`.

> **`Complexity.FP` and its whole import closure compile unmodified on FAF's exact
> Lean 4.31 / Mathlib v4.31.0 pin, after a 4-line mechanical patch to one unrelated
> file.** The Stage-2 target is available today.

### Waves 1–2 — full Stage-3 + Cobham slice

| | failing files | errors | slice modules built |
| --- | ---: | ---: | ---: |
| wave 1 | 7 | 13 | 58 / 134 |
| wave 2 (after 3 one-line fixes) | 7 | 32 | 64 / 134 |

Error taxonomy across both waves — **one dominant category and nothing else**:

| category | count |
| --- | ---: |
| `Type mismatch: After simplification, term …` (`simpa` definitional-unfolding drift) | 41 |
| `Tactic 'rewrite' failed: Did not find an occurrence of the pattern` | 2 |
| `unsolved goals` (a `convert … using 1`) | 1 |
| `simp made no progress` | 1 |

Every inspected instance is `simp` no longer unfolding something it used to — e.g.
`idleDir (Tape.init []).read` vs `Dir3.right`,
`(inputLengthPlusOneCounterTM idx).qstart` vs `LinearCounterPhase.scan`,
`(tm.liftTM m).6 …` vs `tm.6 …`. Three representative one-line fixes were applied and
verified to build:

```lean
-  · convert seqTM_reachesIn_of_reachesIn tm₁ tm₂ hreach₁ hhalt₁ hreach₂ using 1
+  · exact seqTM_reachesIn_of_reachesIn tm₁ tm₂ hreach₁ hhalt₁ hreach₂
-    simp only [Nat.toBits, List.cons.injEq]
+    simp only [List.length_cons, Nat.toBits, List.cons.injEq]
```

**Honest reading.** Errors arrive in waves because Lake halts dependents; 70 of 134 slice
modules are still blocked and have never been type-checked on 4.31. The 32 known errors
are a floor, not a total. But the taxonomy is uniform and shallow: **no substantive proof
breakage, no changed Mathlib definition, no missing lemma** was found in two waves. The
failures concentrate in 7 files, several of them very large
(`SingleTape/Internal/Correctness.lean` at 5,344 LOC, `Subroutines/Counter.lean`,
`Cobham/Internal/StepAlgebra.lean`).

**Estimate: 100–250 individual one-line fix sites across roughly 10–25 files, resolved
over 5–10 build waves. Two to four focused agent-days.** Mechanical throughout, but not
"modest changes" — and, critically, **repeated in full on every FAF toolchain bump** if
the code lives inside FAF.

The external Mathlib surface is reassuringly small and stable — 28 modules for the whole
Stage-3 slice: `Data.Fintype.*`, `Data.Finite.*`, `Data.List.Basic`, `Data.Nat.{Init,Log,Size}`,
`Algebra.Order.{Ring.Nat,Sub.Basic}`, `Analysis.Asymptotics.SpecificAsymptotics`, and
basic tactics. Nothing churny. This is why the drift is shallow, and it is good evidence
that the fork will stay cheap to re-bump.

---

## 3. Vendoring / dependency inventory

Transitive `import` closures computed from source (script in the PR description).

| slice (seeds) | files | LOC | ext deps |
| --- | ---: | ---: | ---: |
| `Classes/P/Defs` (**`FP` alone**) | 5 | **1,496** | 5 |
| `Models/TuringMachine` (core only) | 1 | 906 | 3 |
| `Models/TuringMachine/Combinators` | 2 | 1,941 | 4 |
| `Models/TuringMachine/Deterministic` (+ single-tape) | 11 | 10,132 | 10 |
| `Models/TuringMachine/Composition` | 29 | 12,558 | 5 |
| `UTM/Universal` | 44 | 26,461 | 28 |
| `Classes/P/Cobham` | 103 | 34,140 | 28 |
| `Classes/P` (full) | 109 | 34,613 | 28 |
| **Stage-2 slice** (`FP` + TM core + Composition + Combinators) | **33** | **13,148** | 7 |
| **Stage-3 slice** (Stage-2 + `UTM/Universal`) | **67** | **34,698** | 28 |
| Stage-3 + Cobham | 134 | 54,861 | 38 |

Per-area detail for the Stage-3 slice:

| module group | needed for | transitive role | approx LOC | port difficulty | recommend? |
| --- | --- | --- | ---: | --- | --- |
| `Models/TuringMachine.lean` | 2 & 3 | `TM`, `Tape`, `reachesIn`, `ComputesInTime` | 906 | low (clean) | **yes** |
| `Classes/{Time,Space}`, `Asymptotics` | 2 & 3 | `DTIME`, `=O` | ~590 | low (4 edits, done) | **yes** |
| `Classes/P/Defs` + closure kit | 2 & 3 | `FP`, `mem_FP_comp`, `ite_mem_finset_mem_FP` | ~1,500 | low (**partly wrong — see the correction below**) | **yes** |
| `TuringMachine/Combinators`, `Composition` | 2 & 3 | seq/if/loop, output bounds, `Hoare` | ~12,600 | medium (`Hoare`, `Lift`) | **yes** |
| `TuringMachine/Subroutines` | 3 (via UTM) | counters, pairing, emit | ~27,700 (partly in closure) | **medium-high** (`Counter`, `PairEmit`) | yes, unavoidable |
| `TuringMachine/SingleTape` | 3 | multi→single reduction; `Corr.outputEq` | 6,676 | **high** (5,344-LOC `Correctness`) | yes, unavoidable |
| `TuringMachine/UTM/**` | 3 only | `TMDesc`, `utmTM`, universality | 23,681 | medium | yes for Stage 3 |
| `Classes/P/Cobham/**` | — | machine-independent bridge | 34,140 | medium | **no** (§1.5) |
| `Models/RandomAccessMachine`, `Circuits/`, `SAT/`, `Classes/PPoly` | — | not reachable from our seeds | ~140,000 | — | **no** |

**Correction (2026-08-26).** The "builds today" verdict on the closure kit row above was
wrong, and the Cobham "no" was premature. Measured directly on this pin:
`Classes/P/Defs`, `NormalForm`, `Description`, `FinsetDomain` and `UnaryLength` build;
**`Classes/P/Composition` (`mem_FP_comp`) and `Classes/P/PairWithInput`
(`mem_FP_pairWithInput`) do not**, and neither does any of `Classes/P/Cobham/**` or
`TuringMachine/Subroutines/Binary*`. All of it funnels through the same three files and
the same taxonomy this note records in §II.2 — `Γ.ofBool true` no longer reducing to
`Γ.one` inside `simpa`, in `Subroutines/Internal.lean`; a structure projection no longer
reducing in `Lift.lean`; the same in `PairEmit/Internal.lean`. Because Lake halts
dependents, the observed error count is a floor, not a total. Stage 3 did not need these
modules, so the gap went unmeasured; the machine readings of `thm:scon` and `thm:ifp` do
need them, and `Cobham/**` in particular now looks load-bearing rather than optional —
`CobhamFP_eq_FP` plus `iterate_mem_FP`/`recFoldClamp_mem_FP` is the cheap route to
certifying a streaming transduction in `FP`, against ~1,500–3,000 lines of bespoke Turing
machine per client otherwise.

**Trap in the binary-arithmetic library, recorded because the name misleads.**
`binaryMulAddTM` is the obviously-named multiply and is **repeated addition**:
`binaryMulAddLoopTime` is a `binaryForLoopTime … rightValue 0 rightValue`, linear in the
*value* of the right operand and so exponential in bit width. It is canonical-binary in
representation, which makes its space bound look right. The genuine polynomial multiplier
is `binaryShiftMulTM` — `binaryShiftMulTime lhs rhs = 33 * w² + 170 * w + 58` for
`w = lhs.size + rhs.size`, fully framed. Anyone reaching for "the multiply in
complexitylib" must take `binaryShiftMulTM`.

**Answer to the crucial question.** The good news: the *irreducible core* is genuinely
small — **`FP` and its closure is 1,496 lines and compiles on 4.31 today**. The bad news:
**Stage 3 does not stay small.** Universal simulation drags in the single-tape reduction,
which drags in the subroutine library, for **34,698 LOC / 67 files**. That is 3.4× FAF's
largest vendored body (ProvabilityLogic, 10,393 LOC) and larger than PFR and
ProvabilityLogic combined. It does *not* drag in most of the 329k repository — `Circuits`,
`SAT`, `PPoly`, and the RAM model are all outside the closure — but "a few thousand lines"
is not on offer for Stage 3.

**This asymmetry is the single most important input to the strategy decision**, and it
suggests staging the commitment: Stage 2 needs only the 13k slice (arguably only the 1.5k
core), while Stage 3's 35k is what forces the fork.

---

## 4. Licensing / attribution

Both projects are Apache-2.0, so there is no compatibility question — the same situation
as PFR, and FAF's existing machinery applies unchanged. Ordinary Apache-2.0 §4 mechanics:

- **§4(a)** — ship the licence. Upstream's `LICENSE` is the standard Apache-2.0 text;
  copy it verbatim as `LICENSE-complexitylib` beside the vendored/forked tree.
- **§4(b)** — **modified files must carry prominent notices stating they changed.** The
  port is a modification of every file it touches. Follow the PFR precedent exactly: an
  in-place `FAF VENDOR PATCH` marker, a unified diff under `patches/`, and a
  `NOTICE.md` "Statement of modification".
- **§4(c)** — retain all copyright/attribution notices in the source. Note complexitylib
  **does** carry per-file headers, unlike PFR:
  `Copyright (c) 2025 Samuel Schlesinger` / `Copyright (c) 2026 Bolton Bailey`,
  "Released under Apache 2.0 license as described in the file LICENSE", plus `Authors:`.
  These must be preserved byte-for-byte. Bailey authors much of `Cobham/` and
  `FinsetDomain`; both names belong in the notice.
- **§4(d)** — upstream ships no `NOTICE` file, so no NOTICE-propagation duty attaches.
- **Retain upstream paths and namespaces.** PFR is kept at upstream module paths precisely
  so diffs stay readable, and the same reasoning applies with more force here, where a
  re-bump is expected. The `Complexity` / `Complexitylib` namespace should not be rewritten.

Nothing here is legal advice beyond these mechanics, and FAF already has the templates.

---

## 5. Three organization strategies

### Strategy 1 — external dependency on upstream

`require complexitylib from git … @ "dev"`.

Fatal today: upstream is on **Lean 4.30**, FAF on **4.31**, and FAF's pin is load-bearing
(`lakefile.lean` documents at length that `41d20b5` is the last Foundation commit
containing `Foundation.Modal`, which `ModalAgents` is stated over). Lake cannot reconcile
two toolchains. Also: `dev` is a moving branch, upstream churn is real (987 files, active
PRs), and FAF's auditability posture wants a pinned, diffable artifact.

Revisit **if and when upstream reaches 4.31+ and FAF's pin catches up**; at that point
this becomes the best option and the fork should be retired into it.

### Strategy 2 — vendored audited slice

`vendor/complexitylib/` (or `ComplexityTheory/Vendor/`), FAF-authored bridge kept strictly
separate, following the `ShannonInformation/vendor/` template (`PROVENANCE.md`,
`NOTICE.md`, `LICENSE-complexitylib`, `patches/`, `CLOSURE.txt`, `EXTERNAL-IMPORTS.txt`,
a `vendor-complexitylib.sh --verify`).

Good for Stage 2 (13k, arguably 1.5k). **Bad for Stage 3 at 35k lines**: it puts a body
3.4× FAF's largest vendored tree into the repo, all of it needing a 100–250-site port that
must be **redone inside FAF on every toolchain bump**, with the diff-against-upstream story
degrading each time. FAF's vendoring precedent works precisely because PFR was chosen at a
commit sharing FAF's toolchain — "the single decision that makes this vendoring cheap"
(`PROVENANCE.md`). **That decision is unavailable here**, and pretending otherwise is how
vendoring goes wrong.

### Strategy 3 — pinned compatibility fork ✅ **recommended**

`A-M-Berns/complexitylib` (or `…-faf`), branch `faf/v4.31`, forked at `b673821`, ported,
consumed as a normal pinned Lake dependency:

```lean
require complexitylib from git
  "https://github.com/A-M-Berns/complexitylib" @ "<sha on faf/v4.31>"
```

Why this wins:

- **The port lives where it belongs.** It is a *toolchain-compat* change to third-party
  code, not FAF mathematics. It should not sit in FAF's history.
- **The diff against upstream stays first-class.** `git diff b673821..faf/v4.31` is the
  audit artifact, maintained by git rather than by a `patches/` directory. For a
  100–250-site mechanical port this is a large practical difference.
- **FAF's diff stays small** — a `require` line and the FAF-authored bridge.
- **Re-bumping is a rebase**, and §2 shows the external Mathlib surface is 28 stable
  modules, so rebases should stay shallow.
- **Auditability is preserved, not weakened**: a pinned SHA on an account-controlled fork
  is exactly as reproducible as vendored source, and `lake-manifest.json` already records
  it. The one genuine loss versus vendoring — the code is not readable inside the FAF
  checkout — is mitigated by the pin plus a `PROVENANCE.md` in FAF pointing at it.
- **Upstreamable.** Every fix is a mechanical 4.31 compat fix that upstream will want.
  The fork should carry PRs back, and the endgame is Strategy 1.

Risks, stated plainly: it is a repository the project must now maintain; a stale fork is a
liability; and if upstream refactors heavily, rebasing 100–250 edits could get unpleasant.
Mitigation: keep the fork's delta strictly mechanical, upstream everything, never add FAF
mathematics to it.

**Directory discipline (applies under any strategy):** third-party source and FAF-authored
bridge code must be separated in layout *and* in trust documentation. FAF already does
this well — `PFR/` (upstream, "do not edit by hand") vs `ShannonInformation/` (the
FAF-facing consumer surface, "downstream formalizations import `ShannonInformation.API`
and should never need to name a `PFR.*` module"). **Copy that pattern exactly:** no FAF
module outside the bridge should ever name a `Complexity.*` declaration.

---

## 6. The existing counted-machine work

`Machine/Basic.lean` 363 · `Closure.lean` 385 · `Pairing.lean` 744 ·
`TimedRespectsProbe.lean` 226 — **1,718 LOC**.

```lean
structure Machine (Γ : Type) where
  K : Type    [fintypeK : Fintype K] [decEqK : DecidableEq K]   -- private stacks
  Λ : Type    [fintypeΛ : Fintype Λ]                            -- finite control
  init : Λ
  step : Prog Γ (Stack K) Λ

def RunsInTime (M : Machine Γ) (x y : List Γ) (t : ℕ) : Prop := …
def MachinePolyEC [Fintype Γ] (f : List Γ → List Γ) : Prop :=
  ∃ (M : Machine Γ) (a k : ℕ), ∀ x, RunsInTime M x (f x) (a * (x.length + 1) ^ k + a)
```

with `MachinePolyEC.comp`, `.pair`, `seq_runsInTime`, `Prog.relabel` and its frame lemmas,
and non-vacuity witnesses.

**Recommendation: Possibility C-with-a-twist — retire it from the main route, keep it
briefly as a probe, and delete it once Stage 2 lands.** This is a harder call than it
looks, and the reasoning matters:

*The honest case for keeping it (Possibility B).* Its memory is `S → List Γ` — **finite
list data**, unlike complexitylib's `ℕ → Γ` tape functions. That makes it the far better
substrate for an *executable, `Primrec`-friendly* simulator, which §8 shows is the one
thing complexitylib genuinely lacks. That is a real argument and it should not be waved
away.

*Why it nonetheless loses.* Three reasons:

1. **Its clock is not audited-honest, by its own admission.** `Basic.lean`'s header states
   that reading the step count as a time measure rests on the classical stack-machine ↔
   TM polynomial-overhead fact, which is **"standard and is not formalized here"**. So
   `MachinePolyEC → FP` is not a bridge that *uses* existing FAF work — it is exactly the
   currently-unformalized citation, and proving it is a full stack-machine-to-TM
   simulation with step accounting. That is a large piece of work whose only purpose would
   be to keep a second machine model alive.
2. **It has no finite description type.** `Machine` bundles `K : Type` and `Λ : Type`, so
   like `TM n` it is not enumerable, and unlike `TM n` it has **no `TMDesc` analogue, no
   encode/decode, no roundtrip, no universal machine**. For Stage 3 it is not a
   competitor; it would need all of `UTM/`'s 23k lines rebuilt.
3. **The brief's own criterion — "prefer the architecture with the fewest parallel notions
   of polynomial-time computation" — is decisive.** Keeping it means three notions
   (`PolyFueled`, `MachinePolyEC`, `FP`) and an unformalized citation joining two of them.

*The twist.* Its `S → List Γ` representation insight should be **carried forward into the
FAF-authored bridge**, not preserved by keeping the model. The executable simulator §8
needs is a `List`-based executable step function over `TMDesc` configurations — the same
idea, applied to complexitylib's machine. `TimedRespectsProbe.lean` (the Stage-0 de-risk
probe on Mathlib's `Respects`) is historical and can go immediately.

**Do not delete anything in this PR.** Deprecate after `PolyFueled → FP` lands and the
executable simulator has actually been built on `TMDesc`; if that simulator turns out to
be much easier over stacks than over tapes, this decision should be revisited then, and
the code will still be in git history either way.

---

## 7. Shortest Stage-2 route

### 7.0 The encoding question, which dominates everything

```lean
def PolyFueled (c : Nat.Partrec.Code) (f : ℕ → ℕ) : Prop :=
  ∃ b, Fueled c f b ∧ IsPolyBounded f ∧ IsPolyBounded b
def Fueled c f b : Prop := ∀ n, evaln (b n) c n = some (f n)
def IsPolyBounded (b : ℕ → ℕ) : Prop := ∃ a k, ∀ n, b n ≤ a * (n + 1) ^ k + a
```

**`IsPolyBounded` bounds against the numeric *value* `n`, not its bit-length.** So the
fuel is `poly(n)`, which is *exponential* in `|n|` under binary input encoding. Under a
binary day encoding, `PolyFueled ⊆ FP` is **false**, and no amount of proof effort will
fix it.

Under a **unary** day encoding `|input| = n`, the fuel is polynomial in the input length
and the inclusion is exactly right. This is not a presentational detail — it is the
correctness condition for the whole Stage-2 statement, and it is already latent in
`EfficientlyComputable`, whose clock is `fun n => a * (n + 1) ^ k + a` in the day `n`.
It also matches Logical Induction's own idiom, where the market runs day by day.
complexitylib supplies the relevant primitive: `mem_FP_unaryLength`
(`Classes/P/UnaryLength.lean:25`), `x ↦ 1^{|x|} ∈ FP`.

Output side: `IsPolyBounded f` gives `f n ≤ a(n+1)^k + a`, so the output *value* is
poly in `n` and hence its *binary length* is `O(k log n)` — comfortably polynomial. Unary
output is also fine (length poly in `n`). **Recommend unary in, binary out**, and state it
once, prominently:

```lean
def unaryDay (n : ℕ) : List Bool := List.replicate n true
lemma PolyFueled.fp {c : Nat.Partrec.Code} {f : ℕ → ℕ} (h : PolyFueled c f) :
    (fun x : List Bool => binOf (f x.length)) ∈ Complexity.FP
```

### 7.1 Route comparison

**Route A — via FAF's counted machine.** `evaln → Counted.Machine → MachinePolyEC → FP`.
Rejected: the last arrow *is* the unformalized classical citation (§6), so this route pays
for the simulator **twice** and ends with three parallel notions of polynomial time.
New LOC ~6–9k. Confidence low.

**Route C — via Cobham.** `Nat.Partrec.Code → Cobham → CobhamFP → FP`. Rejected on the
§1.5 analysis: `boundedRec`'s in-class length-bound obligation front-loads the hardest
part, the `Option`/pair plumbing is worse in a combinator algebra than on a machine with
scratch tapes, and it costs +20k LOC of slice. Its one genuine attraction — never touching
a tape — is real, and if the TM route stalls badly this is the fallback. New LOC ~3–5k,
hardest lemma the `prec` length bound. Confidence low-medium.

**Route B — direct complexitylib TM construction** ✅ **recommended.**
`evaln → complexitylib TM → ComputesInTime → FP`, by structural induction on the *fixed*
code `c`, building one machine per constructor and composing with
`Composition`/`Combinators`, then `mem_FP_comp` etc. Reuses the subroutine library
(counters, pairing, emit) that already exists for the UTM. New LOC **~2.5–4k**.
Hardest lemma: `prec` — carrying the fuel-decrement discipline through a bounded loop
while keeping the step count polynomial. Confidence **medium-high**.

**Route D — a shortcut the source suggests, worth one day of investigation first.**
`evaln` is `Primrec`, and complexitylib's `Classes/P/NormalForm.lean:39` gives
`f ∈ FP ↔ ∃ k tm (p : Polynomial ℕ), …`. If the per-constructor induction can be replaced
by *one* machine — a clocked `evaln` interpreter, which is morally what `utmTM` already
is for `TMDesc` — the whole per-constructor tranche collapses. The obstruction is that
`evaln`'s state is `Nat.pair`-coded naturals rather than a tape, so this becomes "build a
small register machine for `Nat.pair`/`unpair`", and `TuringMachine/Registers/`
(5,951 LOC: `RegisterOps`, `Arith`, `Horner`, `Emit`) is exactly that library. **Scout
`Registers/` before committing to Route B's per-constructor plan** — it may cut Stage 2
substantially.

**`evaln`'s `none` cases.** `Fueled` demands `evaln (b n) c n = some (f n)` on *every*
input — a total, always-succeeding hypothesis. So the simulator never has to *represent*
failure faithfully; it needs only to be correct on the branch the hypothesis guarantees.
Any total machine agreeing with `evaln` where `evaln` returns `some` suffices. **This is a
significant and easily-missed simplification**: the `Option` layer can be collapsed
wherever the fuel is known adequate, and `rfind'` — normally the painful case — is reached
only under a hypothesis that pins its result within `b n` steps.

---

## 8. Stage 3 — what actually remains

Target shape (do not freeze the encoding before §7.0 is settled in code):

```lean
def MachineComputableTrader (Tr : Trader) : Prop :=
  ∃ F : List Bool → List Bool, F ∈ Complexity.FP ∧
    ∀ n, decodeTraderOutput n (F (unaryDay n)) = Tr.strat n
```

**What complexitylib gives, essentially for free:** a fixed universal machine `utmTM`; a
finite description type `TMDesc` with proved roundtrip; **total** `decodeDesc`, so raw
bitstrings enumerate machines with no normal-form theorem; and explicit linear-in-`T`
overhead. Index = `(α : List Bool, a k : ℕ)`, decoded from `ℕ` by FAF's existing
`Nat.pair` idiom — structurally identical to the current `TraderProgram` (§9), which is a
good sign.

**Soundness** and **coverage** are then close to thin wrappers, *given* the function-facing
universal theorem of §1.4(2).

**Effective evaluation is the hard part, and it is where the brief's optimism should be
tempered.** FAF's `LIACompiler` needs (`LIACompiler.lean:3904`)

```lean
private lemma enumeratedTraderTrades_prim : Primrec₂ fun j n =>
    ((enumeratedTrader j).strat n).trades
```

For the fuel enumeration this is easy — `evaln` is `Primrec` and the clock is `Primrec`.
For a machine enumeration it is **not**, and nothing upstream helps:

1. **complexitylib has no `Primrec`/`Encodable` theory at all** — 2 occurrences repo-wide,
   both unrelated. This is a deliberate scope choice upstream, not an oversight.
2. **`Cfg` is not encodable data**: `Tape.cells : ℕ → Γ` is a *function*. `Primrec` cannot
   see it.
3. **`TM.descOfTM` is `noncomputable`**, so even the description-extraction direction is
   not executable as written.

So Stage 3 requires FAF to build, from scratch:

- an **executable finite-representation simulator** — `TMDesc` configurations over
  `List Γ` (head, left-stack, right-stack, or an explicit window), with an executable
  `stepExec : TMDesc → ExecCfg → Option ExecCfg`;
- a **`Primrec` certificate** for it (`Encodable` instances for `DescEntry`, `TMDesc`,
  `ExecCfg`, then `Primrec` for `stepExec` and its clocked iteration);
- an **agreement theorem** `stepExec` ↔ complexitylib's `TM.step` on the `Tape` semantics,
  which is the genuinely fiddly part (relating a windowed list to `ℕ → Γ`);
- the **`TerminatedRegion` loose end** from §1.4(7) discharged for enumerated bitstrings.

This is precisely the shape of work FAF's counted machine already does over stacks —
which is why §6 says carry the *representation insight* forward even while retiring the
model. **Estimated 2–3.5k LOC and the largest single tranche of the project.**

> **The gap between `utmTM_universal` and an LI trader enumeration is not the universal
> theorem — it is executability.** The paper needs the firm to *run* trader `i` on day `n`
> inside a computable schedule; a `Prop`-level existence theorem about a universal machine
> whose configurations are functions `ℕ → Γ` does not provide that, and cannot be made to
> without new construction.

---

## 9. Paper-facing EC vs certification technology — blast radius

Target architecture (`PolyFueled` survives as the certification DSL, `FP` becomes
paper-facing) is **sound, and the load-bearing interface is far cleaner than feared** —
but the raw counts need care.

`EfficientlyComputable` occurs **155 times across 34 files**. That is *not* the migration
cost, because most occurrences are in files that produce certificates and would keep using
`PolyFueled` unchanged (`Framework/Computable.lean` 31, `RpnEmission.lean` 24,
`Criterion.lean` 20, `Emission.lean` 7).

The real interface is **97 lines** — `Construction/TraderEnumeration.lean` — and reduces to
exactly two facts:

```lean
lemma enumeratedTrader_ec (j : ℕ) : EfficientlyComputable (enumeratedTrader j)          -- soundness
lemma exists_enumeratedTrader_eq (Tr) (hTr : EfficientlyComputable Tr) :
    ∃ j, enumeratedTrader j = Tr                                                        -- coverage
```

And — the key structural fact — **`TradingFirm.lean` (1,041 lines) is already abstracted
over coverage rather than over the class**:

```lean
theorem trading_firm_dominance_of_covered … (Tr : Trader)
    (hcov : ∃ j : ℕ, enumeratedTrader j = Tr) (hEx : Tr.Exploits P DP) : …
theorem trading_firm_dominance … (hTr : EfficientlyComputable Tr) … :=
  trading_firm_dominance_of_covered … (exists_enumeratedTrader_eq Tr hTr) hEx
```

So the entire property tail consumes `hcov`, and swapping the class means re-proving the
**one** corollary that bridges them. **This is a genuinely well-factored codebase and it
substantially de-risks the migration.**

**The caveat that must not be skipped.** The property files each import
`EfficientlyComputable` in their *hypotheses* (`Conditioning` 6, `ProvabilityInduction` 5,
`FinitePerturbations` 4, `NonDogmatism` 3, `Coherence` 3, …). Those are of the form
"for every efficiently computable trader …", and **widening the class strengthens them** —
so they stay true, but each must be re-checked for whether its *proof* constructs an
exploiter via a fuel certificate. Where it does, the certificate is still valid; it now
needs `PolyFueled.fp` applied at the end to land in the wider class. That is a small,
uniform, mechanical edit — **but it is ~15 files, not zero**, and it cannot be verified
by inspection of the definitions alone. Budget it explicitly rather than assuming
abstractness.

---

## 10. `thm:ifp` — correcting the brief's premise

The blocker is

```lean
structure EfficientPrefixPatch (P : History) (cutoff : ℕ) where
  quote : ℕ → Sentence → ℚ
  quote_exact : ∀ day < cutoff, ∀ φ, P day φ = (quote day φ : ℝ)
  preserves_ec : ∀ Tr, EfficientlyComputable Tr →
    EfficientlyComputable (Tr.freezeBefore quote cutoff)
```

The brief asks: *if `def:ec` becomes genuine machine-polytime, does `thm:ifp` become
straightforwardly inhabitable?*

**No — and the reason matters more than the answer.** `FinitePerturbations.lean:29`
records the obstruction: take `P' 0 φ = 1 - 1/2^(2^(encode φ))`. A trader whose day-`n`
strategy prices a sentence of code `≈ n` at day 0 must, once frozen, *emit* the constant
`1 - 1/2^(2^n)`. Its numeral has magnitude `2^(2^n)` — **binary length `2^n`**.

Any `f ∈ FP` obeys `tm.ComputesInTime f T` with `T =O (· ^ d)`, and a machine writing one
cell per step has `|f x| ≤ T(|x|)`. With day `n` in unary (§7.0), `|input| = n` and the
output would need `2^n` cells in `poly(n)` steps. **Impossible.** The pathology is
information-theoretic — it is about *output size*, not about the fuel calculus — and it
survives the move to `FP` completely intact.

So: **the general `thm:ifp`, quantified over arbitrary computable markets, stays
uninhabitable under any honest polynomial-time class.** This is a genuine over-generalization
in the paper (which, as `FinitePerturbations.lean:41` notes, is aware `LIA` has finite
support per day and generalizes the property tail deliberately), not an artifact FAF can
formalize away. **No coverage tier should move on the strength of adopting complexitylib**,
and the disclosure in `FinitePerturbations.lean` should be *reworded but not weakened* —
its current framing attributes the gap to `dd:fuel`, which this audit shows is too
generous to the paper.

**Where the move genuinely does help: the `LIA` instance**, which is what the repository
actually wants. For `LIA` the per-day quote table is a finite `RationalBeliefState` entry
list, so for a fixed `cutoff` the freeze is a **fixed finite table of fixed constants**.
complexitylib has precisely the right primitive:

```lean
theorem ite_mem_finset_mem_FP (g : List Bool → List Bool) (S : Finset (List Bool)) :
    (fun s => if s ∈ S then g s else []) ∈ FP        -- Classes/P/FinsetDomain.lean:37
```

— finite-support override is in `FP` **regardless of the values**, because the finite table
is hard-wired into the machine's states. Combined with `mem_FP_comp`, an `LIA`-specific
`EfficientPrefixPatch` becomes a short composition argument, where the fuel version
requires threading a polynomial output-value bound through the whole emission stack.

**Net:** adopting `FP` converts `thm:ifp` from "uninhabited, with a disclosed general
obstruction" to "uninhabited in general for a *sharper and more honestly attributed*
reason, with a tractable `LIA` instance newly in reach." That is real progress and worth
doing — but it is not the clean fix the brief hoped for, and the difference should be
reflected in the plan.

> **Superseded (2026-08-26).** This prediction was too pessimistic in one direction and
> beside the point in another. The machine-class certificate is now *inhabited*, and the
> public corrected theorem needs no certificate at all — it compiles one from the market's
> own computability. And the framing was wrong: the published unrestricted `thm:ifp` is not
> a theorem awaiting a certificate, it is **false**, and is now refuted. See Part XXV.

---

## 11. Strength claims — unchanged

No README headline claim, `def:ec` coverage tier, `thm:ifp` tier, paper label, or
`AxiomAudit` endpoint moves in this PR. §10 in fact argues one disclosure is currently
*too generous to the paper* and should be sharpened later — which is a change in
attribution, not in credit, and belongs in its own reviewed change.

---

## 12–13. Proposed architecture

```
                  complexitylib fork @ faf/v4.31   (third-party, pinned SHA)
                     Complexity.TM / ComputesInTime / FP / TMDesc / utmTM
                                      │
   ═══════════════════════════════════╪═══════════════════ trust boundary ═══
                                      │            (FAF-authored below)
                          ┌───────────┴───────────┐
                          │                       │
                      Stage 2                 Stage 3
                          │                       │
                 PolyFueled → FP        TMDesc executable simulator
                (unary day encoding)     + Primrec certificate
                          │                       │
                          └───────────┬───────────┘
                                      │
                          MachineComputableTrader
                                      │
                        universal trader enumeration
                             (soundness + coverage)
                                      │
                            TradingFirm / LIA
                     (consumes `hcov` — already abstract)
```

Module ownership:

```
lakefile.lean
    require complexitylib from git "…/A-M-Berns/complexitylib" @ "<faf/v4.31 sha>"

LogicalInduction/vendor/COMPLEXITYLIB.md        provenance, fork delta, re-bump recipe,
                                                NOTICE / Apache-2.0 §4(b) statement

LogicalInduction/Framework/
    MachineEfficiency.lean                      paper-facing machine-polytime class,
                                                unaryDay / binOf encodings, the ONLY
                                                FAF module naming `Complexity.*`
                                                besides the two below

LogicalInduction/Construction/Machine/
    FuelToFP.lean                               PolyFueled → FP  (Stage 2)
    DescExec.lean                               executable TMDesc simulator + Primrec
                                                certificate + agreement theorem (Stage 3)

LogicalInduction/Construction/
    MachineTraderEnumeration.lean               encoded machine trader enumeration;
                                                mirrors TraderEnumeration.lean's two lemmas
    TradingFirm.lean                            unchanged; already consumes `hcov`

LogicalInduction/Construction/Machine/{Basic,Closure,Pairing,TimedRespectsProbe}.lean
                                                retained, deprecated after Stage 2 (§6)
```

The trust boundary is the point: exactly three FAF modules may name `Complexity.*`, in
direct imitation of the `PFR/` ↔ `ShannonInformation.API` discipline.

---

## 14. Revised effort

| tranche | new/ported LOC | serious agent passes | architectural uncertainty |
| --- | ---: | ---: | --- |
| **A. Fork + port setup** | ~250 ported edit sites, 0 new maths | 2–4 | **low** — measured, uniform taxonomy (§2) |
| **B. Stage 2** `PolyFueled → FP` | 2.5–4k | 4–6 | **medium** — encoding settled (§7.0); Route D may cut it |
| **C. Trader-level inclusion** | 0.6–1k | 2–3 | low — mirrors existing `TraderEnumeration` |
| **D. Stage 3 enumeration + firm migration** | 2.5–3.5k | 6–9 | **high** — executability, not universality (§8) |
| **E. `thm:ifp`** (`LIA` instance only) | 0.4–0.8k | 1–2 | medium — `ite_mem_finset_mem_FP` is the right primitive; general case stays open (§10) |
| **F. Trust surface / README / coverage** | ~0.3k prose | 1–2 | low |
| **total** | **~6.5–10k new FAF LOC** + ~250 ported edits | **16–26** | — |

Against the old estimate of **8–13k new lines / research-scale**: this is a **reduction of
roughly 25–40%, not the order-of-magnitude collapse the brief hoped for.** Being precise
about why:

**What complexitylib genuinely removes** — a step-counting machine semantics; the
multi-tape→single-tape reduction (10k LOC); a finite description type with proved
roundtrip and total decode; a fixed universal machine with explicit linear overhead (24k
LOC); TM composition/Hoare/output-bounds; and an `FP` closure kit. **That is the entire
old Stage-3 "build our own universal simulator" line item — the single largest and
riskiest block in the old plan — deleted outright.** It also retires the unformalized
stack-machine↔TM citation that the counted machine rests on.

**What it does not remove** — Stage 2's `evaln` simulation still has to be written (the
library has no `Nat.Partrec.Code` contact whatsoever), and Stage 3 gains a *new* tranche
that did not exist in the old plan: making complexitylib's machine **executable and
`Primrec`** so `LIACompiler` can consume it. The old counted machine, being list-based,
would have made that cheaper. **That is the honest cost of adoption and the brief does not
anticipate it.**

---

## 15. Answers

1. **Suitable substrate?** **Yes.** Function-facing `FP`, explicit step counts, explicit
   overhead polynomials, total description decoding, Apache-2.0, per-file attribution,
   evidently careful. The one structural mismatch is its complete absence of
   `Primrec`/`Encodable` theory (§8).
2. **Ports cleanly to 4.31?** **Yes, mechanically, at real but bounded cost.** `FP` and
   its closure build *today* after 4 edits in 1 file. Full Stage-3 slice: 64/134 modules,
   32 known errors, all `simp`-unfolding drift; estimate 100–250 sites, 2–4 agent-days.
   No substantive breakage found.
3. **Dependency, fork, or vendor?** **Pinned compatibility fork** (`A-M-Berns/complexitylib`,
   branch `faf/v4.31`), consumed as a Lake dependency. Upstream-direct is blocked by the
   toolchain gap; vendoring 35k lines with a per-bump re-port is worse than a rebase.
4. **If vendored, which modules?** Not recommended — but if forced, the Stage-3 closure:
   `Models/TuringMachine.lean`, `Classes/{Asymptotics,Time,Space}`, `Classes/P/{Defs,…}`,
   `TuringMachine/{Combinators,Composition,Subroutines,SingleTape,Registers,Hoare,Lift,Frame}`,
   `TuringMachine/UTM/**`. Exclude `Cobham`, `PPoly`, `Circuits`, `SAT`, `RandomAccessMachine`.
5. **Vendored LOC?** **Stage-2 slice 13,148 (33 files); Stage-3 slice 34,698 (67 files);
   `FP` core alone 1,496 (5 files).** With Cobham, 54,861.
6. **Does Stage 2 still need FAF's counted machine?** **No.** Route B/D go directly to
   complexitylib's TM. The counted machine's own bridge to `FP` is the unformalized
   classical fact its header discloses (§6).
7. **Can Cobham shorten Stage 2?** **No — recommend excluding it.** `boundedRec`'s in-class
   length-bound obligation front-loads the hardest work, the `Option`/pair plumbing is
   worse in a combinator algebra, and it costs +20k LOC. Keep as fallback only.
8. **Shortest credible `PolyFueled → FP`?** Fix **unary day in / binary out** (§7.0), then
   structural induction on the fixed code into complexitylib TMs composed via
   `Composition`/`Combinators`, landing through `mem_FP_comp` — **but scout
   `TuringMachine/Registers/` first** (Route D), which may replace the per-constructor
   induction with a single clocked interpreter. `evaln`'s `none` cases are largely free:
   `Fueled` hypothesises `some` on every input.
9. **Arbitrary-function universal simulation?** **Only a decider-facing public theorem** —
   `ComputesInTime` appears nowhere in `UTM/`. But the *internals* are function-strength
   (`utmTM_hoareTime`'s output-region postcondition; `Corr.outputEq`), so a function-facing
   theorem is a thin wrapper (~40–80 lines) plus function analogues of the single-tape
   reduction and `descOfTM_decidesInTime` (the latter ~10 lines).
10. **Extra work to enumerate all FP traders?** The executable-simulator tranche of §8:
    `List`-based `TMDesc` step function, `Encodable`/`Primrec` certificates, agreement
    with the `Tape` semantics, and the `TerminatedRegion` side condition for raw
    bitstrings. **~2.5–3.5k LOC — the largest remaining block.**
11. **Can TradingFirm be adapted without rewriting the property tail?** **Yes.**
    `trading_firm_dominance_of_covered` already takes `hcov : ∃ j, enumeratedTrader j = Tr`;
    only the one bridging corollary is re-proved. Caveat: ~15 property files take
    `EfficientlyComputable` *hypotheses* and need a uniform mechanical touch-up (§9).
12. **Does the new class inhabit the finite-prefix-patch interface?** **For `LIA`, yes** —
    `ite_mem_finset_mem_FP` is exactly the primitive. **In general, no**, and *not* for a
    reason the class change can fix: the obstruction is output size and is
    information-theoretic (§10). **The brief's premise here is incorrect.**
13. **What counted-machine code should remain?** All of it for now; none of it long-term.
    Retire after Stage 2 lands; carry its `S → List Γ` representation insight into
    `DescExec.lean`.
14. **Deleted/deprecated eventually?** `TimedRespectsProbe.lean` immediately (historical
    Stage-0 probe); `Machine/{Basic,Closure,Pairing}.lean` after Stage 2, subject to the
    revisit condition in §6.
15. **Recommended architecture?** §12–13.
16. **Revised total effort?** **~6.5–10k new FAF LOC + ~250 ported edits, 16–26 serious
    agent passes** — a 25–40% reduction on 8–13k, not an order of magnitude. The old
    Stage-3 universal-simulator block disappears; a new executability block appears.
17. **Riskiest remaining theorem?** **The agreement theorem between an executable
    `List`-based `TMDesc` simulator and complexitylib's `Tape`-based `TM.step`**
    (§8) — the pivot on which the entire trader enumeration and `LIACompiler` integration
    turns, with no upstream support of any kind, and the one place where adopting
    complexitylib is *harder* than the counted machine would have been. Second: `prec` in
    Stage 2, if Route D does not pan out.
18. **What should the next implementation agent do first?** In order:
    1. **Finish the port** on a fork at `faf/v4.31` — purely mechanical, unblocks
       everything, and its true size is still only bounded below (§2).
    2. **Prove the function-facing universal theorem** (`utmTM_computesInTime`) from
       `utmTM_hoareTime` — small, high-information, and it validates §1.4(2), the finding
       the whole Stage-3 plan rests on. **Upstream it.**
    3. **Spike `DescExec.lean`** — the §8/§17 risk — *before* committing to Stage 2, since
       it is the item that could still change the architecture.
    4. Only then start Stage 2, after scouting `Registers/` for Route D.

---

## Evidence classification

- **Proved upstream, verified in source:** `FP` is function-facing; `reachesIn` counts
  steps; `TMDesc` roundtrip under padding; `decodeDesc` totality; explicit `utmTime` /
  `singleTapeSimTime`; `Corr.outputEq` full-tape equality; `CobhamFP = FP`;
  `mem_FP_comp`; `ite_mem_finset_mem_FP`.
- **Verified by compilation here:** `Classes.P.Defs` builds on FAF's 4.31/Mathlib pin
  after 4 edits; the Stage-3+Cobham slice reaches 64/134 with a single error taxonomy;
  three representative drift fixes verified to build.
- **Thin wrapper (argued from the internal statements, not compiled):** function-facing
  `utmTM_computesInTime`; `descOfTM_computesInTime`. **The single-tape function analogue
  is argued to be tractable, not thin** — it touches a 5,344-line correctness file.
- **Expected-standard but unformalized anywhere:** stack-machine ↔ TM polynomial overhead
  (FAF's counted machine depends on it and says so).
- **Still requires substantial formalization:** `PolyFueled → FP`; the executable
  `TMDesc` simulator and its `Primrec` certificate and agreement theorem; the machine
  trader enumeration; the `LIA` `EfficientPrefixPatch` instance.
- **Not formalized and not proposed for formalization:** the `thm:ifp` counterexample of
  §10 (the claim that no polynomial-time device emits a `2^(2^n)` numeral is argued from
  the output-length bound, not proved in Lean).

---

# Part II — Stage-3 de-risking pass (2026-08-24)

_Second pass. Scope: expose function-output universal simulation, and settle the
executability bottleneck this note's Part I identified as the largest remaining risk.
The broad adoption question is not reopened. `thm:ifp` is untouched (§10, §11 stand)._

Everything below was compiled against the ported complexitylib at Lean 4.31 /
Mathlib v4.31.0. Artifacts and a reproduction recipe: `notes/probes/README.md`.

## II.0 Headline

**Yes — and better than the framing suggested.** FAF need not implement generic
executable machine semantics. It also need not execute the fixed universal machine.
It should execute the **described** machine `TMDesc.toTM` directly, which is strictly
cheaper than both.

`TMDesc.toTM` (`UTM/Internal/Interp.lean:44`) has

```lean
Q := Fin (2 ^ d.w + 1)                       -- numeric states
δ := fun q si sw so => … d.lookup q.val si (sw 0) so …   -- a List.find? over d.entries
```

so a described machine is *already* first-order finite data. Nothing about it needs
`Fintype.equivFin`, and nothing is `noncomputable`. By contrast `utmTM` is assembled by
combinators (`seqTM`/`loopTM`/`ifTM` over `bodyTM`, `haltTestTM`, `extractTM`) with a
nested phase-inductive state type, and would be materially harder to code executably.

The three-way comparison that settles it:

| execute what | feasible? | cost |
| --- | --- | --- |
| arbitrary `TM k` | **no** — `Q : Type` is a bundled type, not finite data | — |
| the fixed `utmTM` | yes | high: combinator-built `Q`, 7 tapes |
| **`TMDesc.toTM`, uniformly in `d`** | **yes** | **low: `Fin (2^w+1)` + list lookup** |

Uniformity is not lost by dropping `utmTM`: the enumeration is indexed by descriptions,
so a *uniformly computable family* indexed by `d` is exactly what is needed, and a fixed
machine is not. This was measured, not argued: the whole executable layer is **734 lines**
(`notes/probes/DescExec.lean`), against Part I's estimate of 2,500–3,500.

`utmTM` does not disappear — it moves to the *semantic* layer, where it belongs (§II.6).

## II.1 The function-output universal theorem — landed

Part I found the public UTM theorems decider-shaped while `utmTM_hoareTime`'s
postcondition already pinned the whole output region. That is now cashed out.

Added to `UTM/Universal.lean` (`notes/probes/0001-utm-function-output.patch`):

```lean
theorem utmTM_simulates_computer {α : List Bool} (hterm : TerminatedRegion α)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : (decodeDesc α).toTM.ComputesInTime f T) (x : List Bool) :
    ∃ c' t, t ≤ utmTime α (T x.length) x.length ∧
      utmTM.reachesIn t (utmTM.initCfg (pair α x)) c' ∧
      utmTM.halted c' ∧
      c'.output.HasOutput (f x)
```

No Boolean decision anywhere in the statement; the explicit `utmTime` bound is preserved
verbatim from the decider version; `utmTM_hoareTime` is reused, not reproved. The whole
proof is **69 lines including docstring**, and the mathematical content is one lemma:

```lean
private theorem length_eq_of_hasOutput {t : Tape} {y : List Bool} {m : ℕ}
    (hy : t.HasOutput y) (hblank : t.cells (m + 1) = Γ.blank)
    (hne : ∀ j, j < m → t.cells (j + 1) ≠ Γ.blank) : m = y.length
```

— the postcondition's frontier is the output length, by uniqueness of the first blank.
Part I's "40–80 lines" estimate was accurate.

`#print axioms utmTM_simulates_computer` → `[propext, Classical.choice, Quot.sound]`,
identical to `utmTM_simulates_decider` and `utmTM_universal`.

It is written in upstream style, sits in the upstream file, and carries the upstream
copyright header: it belongs in the fork and should be offered upstream. **FAF does not
depend on it** — nothing in FAF imports Complexitylib yet.

**Deliberately not stated: the multi-tape analogue of `utmTM_universal`.** That needs a
function-shaped `TM.exists_singleTape_computesInTime`, which does not exist. The
single-tape correspondence invariant already carries full output-tape equality
(`Corr.outputEq : c1.output = c.output`), so this is a strengthening of exposure rather
than new mathematics — but it touches the 5,344-line `SingleTape/Internal/Correctness.lean`
and is not thin. It is needed for **coverage** and nothing else (§II.8).

## II.2 The port, remeasured on the path that matters

Part I reported "100–250 fix sites" for the whole Stage-3 + Cobham slice. That number is
right for that slice and **wrong for the path Stage 3 needs**, because `Counter`,
`PairEmit`, `StepAlgebra`, `Lift` and `Subroutines/Internal` are *not* on the UTM path.

Measured: **`Complexitylib.Models.TuringMachine.UTM.Universal` and
`Complexitylib.Classes.P.Defs` both build on FAF's exact pin after 36 changed lines in
6 files** (`notes/probes/0002-lean431-port-fixes.patch`):

| file | changed lines | class of fix |
| --- | ---: | --- |
| `Asymptotics.lean` | 17 | `convert`+`ext` descending into `Norm ℝ` → direct cast rewrite |
| `UTM/Internal/HaltTest.lean` | 10 | `simpa` unfolding `Γw.toΓ` into a match → `exact` (defeq) |
| `SingleTape/Internal/Correctness.lean` | 3 | `rw` of a beta-redex 4.31 already reduced → `simp only` |
| `Mathlib/NatBits.lean` | 2 | missing `List.length_cons` in a `simp only` |
| `TuringMachine/Hoare.lean` | 2 | `convert … using 1` → `exact` |
| `UTM/Internal/BodyLoop.lean` | 2 | two no-op `dsimp only` |

This includes the 5,344-line `SingleTape/Internal/Correctness.lean`, which was the file
Part I flagged as the likely hard one. It needed **one line**.

**Revised port estimate for the Stage-3 path: well under one agent-day.** The larger
figure stands only if Cobham and the wider `Subroutines` tree are also wanted, and §1.5
already recommends against Cobham.

## II.3 The exact `LIACompiler` obligation

Traced live, not recalled. The chain is

```
TraderProgram → enumeratedTrader → firmRawTrader → TradingFirm → LIACompiler
```

and the computability content is concentrated in **one** lemma
(`LIACompiler.lean:3904`):

```lean
private lemma enumeratedTraderTrades_prim : Primrec₂ fun j n =>
    ((enumeratedTrader j).strat n).trades
```

Everything above it (`traderProgram{LengthCode,TokenCode,Coefficient,Degree}_prim`,
`traderProgramClock_prim`, `clockedTokens_prim`) is private scaffolding *for* that lemma;
everything below (`firmRawTraderTrades_prim` at `:3925`, its two uses at `:5788`/`:5797`)
derives from it by an `if n < j` gate.

The decisive structural fact is that `clockedTrader` factors the token *producer* from
the strategy *decoder* (`Criterion.lean:1902`):

```lean
def clockedTrader (lengthCode tokenCode : Nat.Partrec.Code) (clock : ℕ → ℕ) : Trader where
  strat n := strategyOfTokens n (unRpn (undigitize
    (clockedTokens lengthCode tokenCode (clock n) n)))
```

`strategyOfTokens ∘ unRpn ∘ undigitize` is generic in a `List ℕ`. **Only `clockedTokens`
is fuel-specific.** So:

> **Weakest sufficient theorem.** Supply a total
> `machineTokens : ℕ → ℕ → List ℕ` (index, day) with `Primrec₂ machineTokens`, and define
> `machineTrader j : Trader where strat n := strategyOfTokens n (unRpn (undigitize
> (machineTokens j n)))`. Then `Primrec₂ fun j n => ((machineTrader j).strat n).trades`
> follows by the *same* proof as `enumeratedTraderTrades_prim`, with `clockedTokens_prim`
> replaced by `Primrec₂ machineTokens`. Nothing else in `LIACompiler` changes.

No generic computability theorem about complexitylib machines is needed — and none should
be proved. The whole obligation is `Primrec₂ machineTokens`.

**Consumers needing modification** (exhaustive, from the trace):

| file | change |
| --- | --- |
| `Construction/TraderEnumeration.lean` (97 lines) | new index/decoder + the two lemmas; the fuel version can stay beside it |
| `Construction/LIACompiler.lean` `:2833–2931`, `:3904–3937` | swap `clockedTokens_prim` for `Primrec₂ machineTokens`; ~5 private lemmas |
| `Construction/TradingFirm.lean` `:1030–1034` | the one bridging corollary (`trading_firm_dominance`) |
| `Framework/Criterion.lean` | add `machineTrader`; `clockedTrader` untouched |
| ~15 `Properties/*` files | uniform touch-up where a fuel certificate now needs transporting (Part I §9) |

`trading_firm_dominance_of_covered` and the entire 1,041-line property tail are
**unchanged** — they consume `hcov`, not the class.

## II.4 The finite configuration representation

Chosen, and it fell out of upstream rather than being invented. `Tape.init`'s cell
function (`TuringMachine.lean:243`) is

```lean
cells := fun i => if i = 0 then Γ.start else (contents[i - 1]?).getD Γ.blank
```

— exactly "finite window, blanks outside". So the decode map is upstream's own:

```lean
structure CodedTape where
  head : ℕ
  cells : List Γ          -- cells 1, 2, …; blank beyond the end

def CodedTape.decode (t : CodedTape) : Tape where
  head := t.head
  cells := fun i => if i = 0 then Γ.start else (t.cells[i - 1]?).getD Γ.blank

structure CodedCfg where
  state : ℕ               -- clamped to ≤ 2 ^ d.w, the invariant δ already maintains
  input work output : CodedTape
```

No head-motion or reachable-region bound is needed anywhere. That was the anticipated
hard part and it evaporates: the window grows with the write, so `setAt` pads on demand
and the representation is closed under stepping with no side condition. `OutputBounds.lean`
and `SpaceTime.lean` were not needed.

One deliberate design choice: `setAt` is written as a `range`/`map`, not a two-argument
recursion —

```lean
def setAt (l : List Γ) (i : ℕ) (s : Γ) : List Γ :=
  (List.range (max l.length (i + 1))).map
    fun j => if j = i then s else (l[j]?).getD Γ.blank
```

— because that form is directly primitive recursive via `Primrec.list_range` /
`list_map` / `list_getElem?`, whereas the recursive form is not without extra work. Its
whole specification is one lemma, `getElem?_setAt`.

## II.5 The vertical slice — compiled

All of the following are proved, `sorry`-free, in `notes/probes/DescExec.lean` (734 lines,
70 declarations), each with axioms `[propext, Classical.choice, Quot.sound]`.

**Simulation.**

```lean
theorem codedStep_eq (d : TMDesc) (c : CodedCfg) :
    (codedStep d c).map (CodedCfg.decode d) = (d.toTM).step (CodedCfg.decode d c)

theorem runCoded_eq (d : TMDesc) : ∀ (t : ℕ) (c c' : CodedCfg),
    runCoded d t c = some c' →
      (d.toTM).reachesIn t (CodedCfg.decode d c) (CodedCfg.decode d c')

theorem decode_initCoded (d : TMDesc) (x : List Bool) :
    CodedCfg.decode d (initCoded d x) = (d.toTM).initCfg x

theorem evalCoded_reachesIn (d : TMDesc) (t : ℕ) (x : List Bool) {c : CodedCfg}
    (h : evalCoded d t x = some c) :
    (d.toTM).reachesIn t ((d.toTM).initCfg x) (CodedCfg.decode d c)
```

The last is the end-to-end statement: from a genuine input word, `t` executable steps on
finite data are `t` real steps of the real machine.

**Primitive recursiveness.** Gödel coding is implemented, not assumed: `Primcodable`
instances for `Γ`, `Γw`, `Dir3`, `DescAct`, `DescEntry`, `TMDesc`, `CodedTape`, `CodedCfg`,
each by an explicit `Equiv` to a nested product.

```lean
theorem primrec_lookup :            -- the transition table itself
    Primrec fun z : TMDesc × ℕ × Γ × Γ × Γ => z.1.lookup z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2
theorem primrec_codedStep : Primrec fun z : TMDesc × CodedCfg => codedStep z.1 z.2
theorem primrec_runCoded : Primrec fun z : TMDesc × ℕ × CodedCfg => runCoded z.1 z.2.1 z.2.2
theorem primrec_evalCoded : Primrec fun z : TMDesc × ℕ × List Bool => evalCoded z.1 z.2.1 z.2.2
```

Two supporting facts worth keeping, both general:

* `list_find?_eq_getElem? : l.find? p = l[l.findIdx p]?`, giving
  `primrec_list_find?` from Mathlib's `list_findIdx` + `list_getElem?`. Mathlib has no
  `Primrec` lemma for `List.find?`; this is a small upstreamable gap.
* `primrec_of_gamma` / `primrec_of_gammaW` / `primrec_of_bool` — any function out of a
  fixed finite type is primitive recursive, as a constant lookup table. This is what makes
  the direction-sanitizing and `readback` cases free.

**What is not yet done in the probe:** output-word extraction
(`CodedCfg → List Bool` up to the first blank, plus its `HasOutput` agreement lemma).
It is straightforward — `takeWhile (· ≠ blank)` on the output cell list — but needs a
side condition that reachable output cells avoid `Γ.start`, which upstream's
`Tape.StartInvariant` supplies. Estimated ~80 lines. This is the only gap between the
probe and a usable `machineTokens`.

## II.6 Three layers, kept apart

The probe deliberately proves **nothing** about polynomial time, and the complexity
results prove nothing about executability. They meet only at the enumeration.

| layer | owner | content |
| --- | --- | --- |
| **semantic universality** | complexitylib (fork) | `f ∈ FP` → description → `utmTM_simulates_computer`, polynomial overhead |
| **executability** | FAF `DescExec.lean` | `Primrec₂` bounded evaluation of `TMDesc.toTM`; no complexity claim |
| **trader enumeration** | FAF `MachineTraderEnumeration.lean` | index → `Trader`; soundness + coverage |

`utmTM` and `clockedUtmTM` live only in the first layer. The executable evaluator never
mentions them, and must not: making the `Primrec` evaluator carry the polynomial-time
proof is exactly the conflation to avoid.

## II.7 Proposed enumeration index and fallback

```lean
structure MachineTraderProgram where
  desc  : List Bool     -- raw description bits; decodeDesc is total
  coeff : ℕ
  deg   : ℕ
```

encoded into `ℕ` by the existing `Nat.pair` idiom, exactly mirroring `TraderProgram.index`
/ `traderProgramAt` (`TraderEnumeration.lean:32–50`), so `traderProgramAt_index` transfers
verbatim.

```lean
def machineTokens (j n : ℕ) : List ℕ :=
  let p := machineProgramAt j
  let d := decodeDesc p.desc
  match evalCoded d (p.coeff * (n + 1) ^ p.deg + p.coeff) (unaryDay n) with
  | none   => []                       -- did not halt within the claimed clock
  | some c => outputTokens c           -- total; malformed output decodes downstream
```

**Totality holds at four independent points, three of them already upstream or in FAF:**

1. *Malformed description* — `decodeDesc : List Bool → TMDesc` is total
   (`Desc.lean:394`), and `TMDesc.lookup` falls back to `defaultAct` on a missing key.
   Every bitstring denotes some machine.
2. *Out-of-range state* — `TMDesc.toTM` clamps targets with `min _ (2^w)`; the coded
   step mirrors the clamp, which is what makes `decodeState` total.
3. *Timeout* — `evalCoded` returns `none`; we map that to `[]`.
4. *Malformed trader output* — **FAF already handles this**: `strategyOfTokens`
   (`Criterion.lean:1546`) returns the zero strategy when `deserializeTrades` fails *or*
   when the rank discipline is violated. No new fallback machinery is needed.

So the fallback is `[]` at exactly one new place, and the existing decoder absorbs the
rest.

## II.8 No clock certificate is needed — and the clamp does double duty

This is worth stating sharply, because it removes an obligation the old plan carried.

The enumeration ranges over `(desc, coeff, deg)` and simply runs for
`coeff * (n+1)^deg + coeff` steps. **We never verify that `(coeff, deg)` is a truthful
complexity bound.**

*Soundness* — every enumerated trader is genuinely polynomial-time — holds **because of**
the clamp, not despite it: a machine run for at most `p(n)` steps computes something
polynomial-time whatever `p` was claimed to be. Truncation is not merely a totality
device; it is the soundness argument. The machine witnessing it is upstream:
`clockedUtmTM : TM 7` (`UTM/ClockedUtm.lean:299`), with both branches proved —

```lean
theorem clockedUtmTM_hoareTime_halt    …  -- output agrees with the simulated machine's
theorem clockedUtmTM_hoareTime_timeout …  -- writes the timeout sentinel at cell 1
```

both within `clockedUtmTime α x V`, which is linear in `V`. One residual: `clockedUtmTM`
receives its clock as a unary register `regTape V` on tape 6, so a self-contained
`FP` membership additionally needs the clock *constructed from the input*. That is what
`UTM/ClockConstructible.lean` (2,316 LOC) is for; it has not been audited in this pass and
is the main unknown left in soundness.

*Coverage* — every genuinely polynomial-time trader appears — is where the real remaining
work sits, and it is **not** helped by the clamp. Given a machine-polytime trader we must
produce a description: `f ∈ FP` gives a `TM k`, and reaching `TMDesc` needs
`TM k → TM 1 → TMDesc`, i.e. the function-shaped single-tape reduction of §II.1 that does
not exist. Then a sufficiently large `(coeff, deg)` majorising the true bound is picked,
and `evalCoded` agrees with the unclamped run. **This is the one place the missing
single-tape-for-functions theorem is load-bearing.**

## II.9 Revised Stage-3 decomposition

Replacing Part I §14's single "D. Stage 3 enumeration / TradingFirm migration, 2.5–3.5k
LOC, 6–9 passes":

| tranche | status | LOC | passes |
| --- | --- | ---: | ---: |
| complexity theory / universality | **UPSTREAM, DONE** | 0 | 0 |
| 4.31 port of the UTM path | **DONE** (36 lines, 6 files) | ~0 | <1 |
| function-output UTM wrapper | **DONE** (69 lines, compiled) | 0 | 0 |
| finite executable coding + simulation | **DONE** (734 lines, compiled) | 0 | 0 |
| `Primrec` bounded evaluator | **DONE** (in the same file) | 0 | 0 |
| output-word extraction + `HasOutput` | remaining, straightforward | ~80 | 0.5 |
| single-tape reduction **for functions** | remaining, **the hard one** | 400–800 | 2–3 |
| clock construction / `FP` soundness | remaining, partly upstream | 200–400 | 1–2 |
| trader enumeration + two lemmas | remaining | 300–500 | 1–2 |
| `LIACompiler` swap + property touch-ups | remaining | 200–400 | 1–2 |
| **Stage-3 total** | | **~1.2–2.2k** | **6–10** |

Against Part I's 2.5–3.5k LOC: **roughly halved**, and the largest single risk item
(executability) is now retired rather than estimated.

Part I §14's overall figure of ~6.5–10k new FAF LOC becomes **~5–8k**, still dominated by
Stage 2 (`PolyFueled → FP`), which this pass did not touch.

## II.10 Revised risk

**Part I's riskiest theorem is retired.** "The agreement theorem between an executable
`List`-based simulator and complexitylib's `Tape`-based `TM.step`" is `codedStep_eq`, and
it compiles in 20 lines. The risk was mispriced because the audit assumed the target was
`TM k` or `utmTM`; against `TMDesc.toTM` it is easy.

**The new riskiest theorem is the function-shaped single-tape reduction**,

```lean
theorem TM.exists_singleTape_computesInTime {k : ℕ} (M : TM k) {f} {T}
    (h : M.ComputesInTime f T) :
    ∃ M₁ : TM 1, M₁.ComputesInTime f (NTM.singleTapeSimTime k T)
```

needed **only for coverage** (§II.8). Grounds for confidence: the correspondence invariant
already carries `outputEq : c1.output = c.output`, full tape equality, so the mathematics
is present and only its exposure is decider-shaped. Grounds for caution: realising it
means re-deriving `singleTapeSim_computesInTime`, a `ComputesInTime` analogue of
`toTM_decidesInTime` (whose `RejectsWithZero` side condition should simply vanish), and
`pad0_computesInTime`, inside a 5,344-line file. Estimated 400–800 lines. It is
upstreamable and should be offered upstream.

Second: `ClockConstructible.lean`, unaudited, on the soundness path.

## II.11 Next implementation tranche

1. **Stand up the fork** `A-M-Berns/complexitylib`, branch `faf/v4.31`, at `b673821` plus
   `0002-lean431-port-fixes.patch`; then `0001-utm-function-output.patch` as a separate
   commit, and open it upstream. Wire it into FAF's `lakefile.lean` and move
   `notes/probes/DescExec.lean` to `LogicalInduction/Construction/Machine/DescExec.lean`
   so it is built and CI-covered. **This is the only thing blocking everything else.**
2. **Output extraction** (~80 lines) — completes `machineTokens`.
3. **`TM.exists_singleTape_computesInTime`** — the risk item; do it before designing the
   coverage proof, not after.
4. **Audit `ClockConstructible.lean`** for the `FP` soundness chain.
5. Only then: the enumeration, the `LIACompiler` swap, and the property touch-ups.

Stage 2 (`PolyFueled → FP`) is unchanged by this pass and remains sequenced after, per
Part I §7 — including the still-unscouted Route D shortcut through
`TuringMachine/Registers/`.

---

# Part III — Productionization (2026-08-24)

_Third pass. Scope: stand up the pinned fork, wire it into FAF reproducibly, move the
Stage-3 spike into a CI-built module, close output extraction, and land the first bounded
total machine-token evaluator with its `Primrec₂` obligation. Coverage is explicitly out of
scope (§III.8). `thm:ifp` untouched; Part I §10–§11 stand._

## III.0 The layered architecture, as built

```
  SEMANTIC / COMPLEXITY LAYER          pinned fork, A-M-Berns/complexitylib @ faf/v4.31
    Complexity.TM / reachesIn / FP     upstream b673821 + 2 commits
    TMDesc, decodeDesc, TMDesc.toTM    FAF imports only …UTM.Internal.Interp
    utmTM_simulates_computer             (5 files / ~2.2k lines of the ~329k library)
                  │
  ════════════════╪══════════════════════ trust boundary ════════════════════════
                  │
  EXECUTABLE LAYER                     LogicalInduction/Construction/Machine/DescExec.lean
    CodedTape / CodedCfg               finite window, blanks outside
    codedStep_eq, runUntilHalt_spec    executable steps ARE real steps
    Primcodable ×8, primrec_codedStep  real Gödel coding
    codedOutput, hasOutput_outputWord  extraction = upstream Tape.HasOutput
                  │
  LI ENUMERATION LAYER                 same file, upper section
    progDesc / progCoeff / progDeg     plain functions, not projections
    machineTokens : ℕ → ℕ → List ℕ     total; [] on timeout
    primrec_machineTokens              ← the LIACompiler obligation
    machineTokens_steps_le             ← polynomial soundness, step form
    length_machineTokens_le            ← polynomial soundness, size form
                  │
  TRADING LAYER                        unchanged
    strategyOfTokens ∘ unRpn ∘ undigitize     generic in List ℕ — reused verbatim
    trading_firm_dominance_of_covered         the coverage seam, still untouched
```

The three layers are kept apart on purpose. `DescExec` proves **nothing** about polynomial
time; the complexity theory is upstream; and coverage is a third fact that neither supplies.

## III.1 The fork

| field | value |
| --- | --- |
| upstream base | `SamuelSchlesinger/complexitylib` @ `b673821` (`dev`) |
| fork | `https://github.com/A-M-Berns/complexitylib` |
| branch | `faf/v4.31` |
| head | `a16b3f568dab7183b205368bb950856a44db583c` |

Exactly two commits on top of the base, kept separate so the second can be offered upstream
on its own:

**`badc970` — `compat: port to Lean 4.31.0 / Mathlib v4.31.0`.** 36 changed lines across 6
files, plus `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` realigned to FAF's
Mathlib pin (`fabf563a`). No mathematical statement, definition or proof is altered; every
change is a tactic repair against 4.31's elaborator and simp set —
`Asymptotics.lean` (17), `UTM/Internal/HaltTest.lean` (10), `SingleTape/Internal/Correctness.lean`
(3), `Mathlib/NatBits.lean` (2), `TuringMachine/Hoare.lean` (2), `UTM/Internal/BodyLoop.lean` (2).

**`a16b3f5` — `feat(UTM): expose universal simulation for arbitrary function output`.** 69
added lines in `UTM/Universal.lean`: `utmTM_simulates_computer`, plus the private
`length_eq_of_hasOutput` it turns on. Additive; nothing existing is touched.
Axioms: `[propext, Classical.choice, Quot.sound]`, the same three as
`utmTM_simulates_decider` and `utmTM_universal`.

No FAF-specific trader or `Primrec` machinery is in the fork.

## III.2 The dependency

```lean
require complexitylib from git
  "https://github.com/A-M-Berns/complexitylib" @ "a16b3f568dab7183b205368bb950856a44db583c"
```

Pinned by commit, not by branch. `lake-manifest.json` records the same SHA. Mathlib stays at
`fabf563a` (v4.31.0) and Foundation at `41d20b51` — the new dependency reconciles with both
rather than moving either, which is what makes the pin safe.

**FAF's import surface is far narrower than the fork.** `DescExec` imports only
`Complexitylib.Models.TuringMachine.UTM.Internal.Interp`, whose closure is **5 files /
2,160 lines**:

| lines | module |
| ---: | --- |
| 906 | `Complexitylib.Models.TuringMachine` |
| 509 | `…UTM.Internal.Desc` |
| 264 | `…UTM.Encoding` |
| 264 | `…UTM.Internal.Interp` |
| 217 | `Complexitylib.Mathlib.NatBits` |

versus 44 files / 26,461 lines for `UTM.Universal`, and ~329k for the library. **Only one of
the six port-fixed files (`NatBits`, 2 lines) is inside it** — the other 34 port lines and
the UTM wrapper are upstream-useful but sit outside FAF's trust path entirely. That is a
12× reduction against Part II's assumption and worth recording as the main structural gain
of this pass.

`DescExec` is the *only* module in the repository that names a `Complexity.*` declaration,
mirroring the `PFR/` ↔ `ShannonInformation.API` discipline.

## III.3 Production module

`LogicalInduction/Construction/Machine/DescExec.lean`, imported by
`LogicalInduction/Construction/Machine.lean`, built by a new default target:

```lean
@[default_target]
lean_lib MachineExec where
  srcDir := "."
  roots := #[`LogicalInduction.Construction.Machine]
```

Two consequences worth stating plainly:

* **This directory was not previously compiled by anything.** `lean_lib LogicalInduction`
  declares no `globs`, so it builds `LogicalInduction.lean` and its import closure only, and
  `Construction/Machine.lean` is imported by nothing in it. The Stage-1 counted machine has
  therefore never been CI-built. The new target fixes that for `Basic`/`Closure`/`Pairing`
  as well as for `DescExec`.
* **It is built but load-bearing for nothing.** Still not imported by `LogicalInduction.lean`,
  still carries no paper node, still relates to `EfficientlyComputable` by no theorem.

`MachineExec` is registered in `scripts/papers.py`'s `NON_PAPER_LIBRARIES`, which the wiring
gate requires.

House convention: every declaration is a `lemma`, not a `theorem`, because
`scripts/lint_paper_labels.py` requires every `theorem` under `LogicalInduction/` to name a
paper node and nothing here renders one. **Part II's `notes/probes/DescExec.lean` violated
that gate in 43 places** — it was added to the tree without the linter being run. Moving the
module fixes it; the probe copy is deleted and the two fork patches stay in `notes/probes/`
as provenance.

## III.4 Output extraction

The gap Part II left. Upstream's convention is

```lean
def Tape.HasOutput (t : Tape) (y : List Bool) : Prop :=
  (∀ i (h : i < y.length), t.cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
  t.cells (y.length + 1) = Γ.blank
```

so extraction reads the window up to the first blank:

```lean
def CodedTape.frontier (t : CodedTape) : ℕ := t.cells.findIdx fun g => g == Γ.blank
def CodedTape.outputWord (t : CodedTape) : List Bool :=
  (List.range t.frontier).map fun j => decide ((t.cells[j]?).getD Γ.blank = Γ.one)
def codedOutput (c : CodedCfg) : List Bool := c.output.outputWord
```

Written as a `range`/`map` rather than a `takeWhile`, the same device already used for
`setAt`, because that form is directly primitive recursive.

**Correctness is an equality against upstream's convention, not a length bound:**

```lean
lemma CodedTape.hasOutput_outputWord {t : CodedTape} (ht : t.NoStart) :
    t.decode.HasOutput t.outputWord
```

The `NoStart` side condition — the window never holds the left-end marker — is discharged
rather than assumed: `δ` writes only `Γw`, which structurally excludes `Γ.start`, so
`codedStep_output_noStart` propagates it and `initCoded`'s empty output tape starts it.
Blank tails cannot leak into the output because `findIdx` returns the window length when no
blank is present, and cell `length + 1` decodes to `Γ.blank` by the decode map itself.

## III.5 The bounded evaluator

Part II's `runCoded` iterates a *fixed* number of steps and returns `none` when the machine
halts early — the opposite of what a clocked evaluator needs. Added:

```lean
def stepFrozen (d : TMDesc) (s : CodedCfg × Bool) : CodedCfg × Bool
def runUntilHalt (d : TMDesc) (t : ℕ) (c : CodedCfg) : Option CodedCfg
def evalHalted (d : TMDesc) (t : ℕ) (x : List Bool) : Option CodedCfg
```

The frozen-pair form makes the budgeted run a plain iteration, hence primitive recursive by
`Primrec.nat_iterate`. Its specification carries the step bound the soundness argument needs:

```lean
lemma evalHalted_spec (h : evalHalted d t x = some c) :
    ∃ s ≤ t, (d.toTM).reachesIn s ((d.toTM).initCfg x) (CodedCfg.decode d c) ∧
      (d.toTM).halted (CodedCfg.decode d c) ∧
      (CodedCfg.decode d c).output.HasOutput (codedOutput c)
```

## III.6 `machineTokens`

```lean
def descAt    (i : ℕ) : TMDesc := (Encodable.decode i).getD ⟨0, 0, 0, []⟩
def progDesc  (j : ℕ) : TMDesc := descAt (Nat.unpair (Nat.unpair j).1).1
def progCoeff (j : ℕ) : ℕ      := (Nat.unpair (Nat.unpair j).1).2
def progDeg   (j : ℕ) : ℕ      := (Nat.unpair j).2
def progClock (j n : ℕ) : ℕ    := progCoeff j * (n + 1) ^ progDeg j + progCoeff j

def machineTokens (j n : ℕ) : List ℕ :=
  tokensOf (evalHalted (progDesc j) (progClock j n) (unaryDay n))
```

`ℕ → ℕ → List ℕ`, matching `clockedTokens`'s convention exactly, so the decoding chain
`strategyOfTokens ∘ unRpn ∘ undigitize` is reused verbatim. The index layout mirrors
`TraderProgram.index` / `traderProgramAt`.

**Indexing by `TMDesc`, not by description bits.** Upstream's `decodeDesc : List Bool →
TMDesc` exists because the universal machine reads its program off a tape; here the described
machine is executed directly, so the index decodes straight to a `TMDesc` through the
`Primcodable` instance. That keeps `decodeDesc`, `encodeDesc`, their roundtrip, and the
`TerminatedRegion` side condition Part I flagged as a loose end off this path entirely.

**No certificate field.** `(coeff, deg)` is a *claim*, never checked (§III.7).

**One elaboration hazard, worth recording because it cost most of this pass.** `descAt` goes
through `Encodable.decode` at `TMDesc`, whose instance is a stack of `Primcodable.ofEquiv`s
down to `Fin 4`. *Any* `rfl` obligation that lets the elaborator unfold it sends `whnf` into
that stack and does not return: four builds failed on `whnf` timeouts at 200k, 1M, 2M, 4M and
8M heartbeats before the cause was clear. The fix is structural, not a bigger budget —
`descAt` is sealed `attribute [irreducible]` immediately after its `Primrec` lemma; the index
fields are plain functions rather than projections out of `MachineTraderProgram` (which
survives only as index bookkeeping for coverage); the `Option` fallback is factored into
`tokensOf : Option CodedCfg → List ℕ` so `Primrec.option_casesOn` is unified at that small
domain instead of at `ℕ × ℕ`; and every `Primrec` lemma is a bare `.comp` whose underlying
function is *syntactically* the definition it characterises, so no `of_eq` defeq check is
ever performed at a type carrying the coding stack. Anyone extending this file should keep
that discipline.

**One adapter was unavoidable and is minimal.** The machine speaks `List Bool`; the digit
layer speaks `List ℕ`. `bitsToDigits` packs three bits per digit, most significant first,
dropping a trailing partial group. It needs no validity side condition, because groups with
value `≥ 4` are exactly what `undigitizeStep` already treats as block terminators — so
*every* bitstring denotes some digit stream.

**Totality has four failure points and needed one new fallback.** Malformed description →
`decodeDesc` is total and `lookup` defaults to halting. Out-of-range state → `TMDesc.toTM`
clamps and `codedStep` mirrors the clamp. Malformed trader stream → `strategyOfTokens`
already returns the zero strategy. Only "did not halt in budget" is new, and it emits `[]`.

## III.7 Soundness at this layer

```lean
lemma machineTokens_steps_le (j n : ℕ) :          -- step form
    machineTokens j n = [] ∨ ∃ c, ∃ s ≤ (machineProgramAt j).clock n, …
lemma length_machineTokens_le (j n : ℕ) :          -- size form
    (machineTokens j n).length ≤ (machineProgramAt j).clock n
```

Both hold for **every** index, with no truthfulness assumption about `(coeff, deg)`. That is
the content of "no clock certificate is needed": truncation at the claimed polynomial is not
merely a totality device, it *is* the soundness argument, since a machine run for at most
`p n` steps computes something polynomial-time whatever `p` was claimed to be.

The size bound comes from a second invariant, `CodedTape.Bounded k := head ≤ k ∧ cells.length ≤ k`,
preserved with `k → k + 1` by each step: one executable step writes at most one cell.

**What is deliberately *not* claimed here.** These are function-level, step-counting facts.
The statement "every `machineTokens` index induces a machine-polytime trader" needs the
paper-facing machine class, which does not exist yet and would force the rest of the Stage-3
API. The exact next statement is recorded in §III.9.

## III.8 `ClockConstructible` is off the trust path

Part II flagged `UTM/ClockConstructible.lean` (2,316 lines) as unaudited and on the soundness
path. **It is not, under this architecture.** That file exists to construct a unary clock
register on a tape for `clockedUtmTM`, which matters only if the *universal machine* carries
the clock. Here the clock is a Lean-level `ℕ` consumed by `runUntilHalt`, and the described
machine is executed directly, so neither `clockedUtmTM` nor its clock construction is
imported: both are outside the 5-file closure of §III.2.

They return to relevance only for the eventual `FP` membership statement, where a *machine*
must witness the clocked computation. Recorded, not audited — there is no consumer yet.

## III.9 What remains for coverage

Unchanged from Part II §II.10 in substance, sharpened in form. The missing theorem is

```lean
lemma TM.exists_singleTape_computesInTime {k : ℕ} (M : TM k) {f} {T}
    (h : M.ComputesInTime f T) :
    ∃ M₁ : TM 1, M₁.ComputesInTime f (NTM.singleTapeSimTime k T)
```

which is what turns `f ∈ FP` into a `TMDesc` an index can name. `NTM.SingleTape.Corr.outputEq`
already carries full output-tape equality, so the mathematics is present and only its
exposure is decider-shaped; realising it means re-deriving `singleTapeSim_computesInTime`, a
`ComputesInTime` analogue of `toTM_decidesInTime` (whose `RejectsWithZero` side condition
should vanish), and `pad0_computesInTime`, inside the 5,344-line
`SingleTape/Internal/Correctness.lean`. **400–800 lines, upstreamable, belongs in the fork.**

Coverage then needs, in FAF: the paper-facing machine-trader class; `machineTrader` and its
enumeration; the soundness and coverage lemmas mirroring `enumeratedTrader_ec` and
`exists_enumeratedTrader_eq`; the `LIACompiler` swap; and the ~15 property-file touch-ups.

## III.10 Revised Stage-3 remaining

| tranche | status | LOC | passes |
| --- | --- | ---: | ---: |
| complexity theory / universality | UPSTREAM, DONE | 0 | 0 |
| 4.31 port | **DONE** (36 lines, fork) | 0 | 0 |
| function-output UTM wrapper | **DONE** (69 lines, fork) | 0 | 0 |
| fork + reproducible dependency | **DONE** | ~30 | 0 |
| production `DescExec` + CI target | **DONE** | — | 0 |
| output extraction + correctness | **DONE** | ~120 | 0 |
| `machineTokens` + `Primrec₂` | **DONE** | ~210 | 0 |
| polynomial soundness (step + size) | **DONE** | ~110 | 0 |
| single-tape reduction **for functions** | remaining, **the hard one** | 400–800 | 2–3 |
| machine-trader class + enumeration | remaining | 300–500 | 1–2 |
| `FP` membership / clock construction | remaining | 200–400 | 1–2 |
| `LIACompiler` swap + property touch-ups | remaining | 200–400 | 1–2 |
| **Stage-3 remaining** | | **1.1–2.1k** | **5–9** |

Part II projected 1.2–2.2k remaining; roughly 0.4k of that is now landed and the rest is
unchanged, so the projection is holding. Overall project remains **~5–8k**, still dominated
by Stage 2 (`PolyFueled → FP`), which no pass has touched.

## III.10a Build result

`lake build MachineExec` → **887 jobs, exit 0, no errors, no `sorry`.**
`DescExec.lean` is 1,330 lines / 134 declarations. Axiom report, from the build itself —
every endpoint exactly `[propext, Classical.choice, Quot.sound]`:

```
codedStep_eq                    runUntilHalt_spec         decode_initCoded
evalHalted_spec                 primrec_codedStep         primrec_runUntilHalt
CodedTape.hasOutput_outputWord  primrec_machineTokens
machineTokens_steps_le          length_machineTokens_le
```

Repository gates: `lint_paper_labels.py` clean (Part II's `notes/probes/DescExec.lean` had
put 43 violations into the tree; moving it to production code under the `lemma` convention
removes them), `check_paper_wiring.py` OK with `MachineExec` excused,
`check-paper-nodes.sh` OK — 68 labels, both directions, strength distribution unchanged.

## III.11 Riskiest remaining theorem

Still `TM.exists_singleTape_computesInTime` (§III.9), and now unambiguously so: everything
that stood between the spike and a working evaluator is done, and coverage is the only thing
left that is not routine. It is also the only remaining item that must be written against a
5k-line upstream file rather than in FAF.

---

# Part IV — Stage-3 coverage: the `FP → TMDesc` chain (2026-08-24)

_Fourth pass. Scope: checkpoint and fully validate Part III's tranche, then close the
coverage bottleneck as far as a coherent checkpoint allows. Stage 2 and general `thm:ifp`
untouched, per Part I §10–§11._

## IV.0 What this pass settles

Part II named `TM.exists_singleTape_computesInTime` the riskiest remaining theorem and
guessed 400–800 lines. **The hypothesis that it was an exposure problem rather than new
mathematics was correct, and it came in at 195 lines.**

The coverage chain is now proved end to end, from a genuine `FP` function down to something
an enumeration index can carry:

```
  f ∈ Complexity.FP
        │  mem_FP_iff_computesInTime_polynomial          (upstream, pre-existing)
        ▼
  some TM k computes f within p.eval, at every length
        │  TM.exists_singleTape_computesInTime           ← fork ac6b509, NEW
        ▼
  some TM 1 computes f within singleTapeSimTime k p.eval
        │  TM.exists_wf_desc_computesInTime              ← fork af8ed55, NEW
        ▼
  some well-formed TMDesc computes f within q.eval        ← exists_desc_computesInTime_polynomial
        │  exists_clock_of_polynomial                    ← FAF bce19a4, NEW
        ▼
  … within a * (n + 1) ^ k + a                            ← exists_desc_computesInTime_clock
        │
        ▼
  an index (d, a, k) that machineTokens can run
```

Every arrow is proved, `sorry`-free, with axiom surface exactly
`[propext, Classical.choice, Quot.sound]`. **The UTM is not on this path**, and neither is
`ClockConstructible`.

## IV.1 The single-tape function theorem

```lean
theorem TM.exists_singleTape_computesInTime {k : ℕ} (M : TM k)
    {f : List Bool → List Bool} {T : ℕ → ℕ} (h : M.ComputesInTime f T) :
    ∃ M₁ : TM 1, M₁.ComputesInTime f (NTM.singleTapeSimTime k T)
```

Identical time bound to the decider version, `16 * (k + 1) * (T n + n + 1) ^ 2`.

**It is a thin wrapper on a strong invariant, not new simulation mathematics.**
`NTM.SingleTape.Corr.outputEq` is `c1.output = c.output` — *full output-tape equality* — so
the simulation already transported an arbitrary finite output word; only the public
theorems projected it onto the verdict cell. Three private lemmas were cell-1 restrictions
of whole-tape facts, and the whole-tape forms are in one case *simpler*:

| cell-1 (existing) | whole-tape (added) | why the general form is no harder |
| --- | --- | --- |
| `writeAndMove_readBack_cell1` | `writeAndMove_readBack_cells` | the write-back writes what is already there, so it is a no-op on *every* cell; at cell 0 `Tape.write` is already structurally a no-op, so the case split replaces the cell-1 case analysis |
| `haltCorr_cell1` | `haltCorr_cells` | `Corr.outputEq` was always the whole tape |
| `halts_rev_cell1` | `halts_rev_cells` | same proof, final step swapped |

Transport uses the pre-existing `Tape.hasOutput_congr`, which depends only on `cells`.

Two things that made it cheaper than feared, both worth recording:

* **No `RejectsWithZero` counterpart is needed.** The decider conversion `toTM_decidesInTime`
  requires that output discipline because `NTM.DecidesInTime` encodes rejection as
  *non*-acceptance while `TM.DecidesInTime` demands an exact `0`. `ComputesInTime` already
  pins the whole output tape, so the side condition simply does not arise.
* **The `k = 0` branch is free.** `pad0_trace_init` already states full output equality, not
  a verdict-cell fact.

195 added lines, nothing existing modified. Upstream's `scripts/lint_style.py` passes.

## IV.2 The description bridge

```lean
theorem Complexity.exists_desc_computesInTime_polynomial {f} (hf : f ∈ FP) :
    ∃ (d : TMDesc) (q : Polynomial ℕ), d.WF ∧ d.toTM.ComputesInTime f q.eval
```

`FP` quantifies over machines, and a `TM k` is not finite data — bundled state `Type`,
tapes as functions `ℕ → Γ`. `TMDesc` *is* finite data, and is what an enumeration, a Gödel
coding, or `DescExec`'s interpreter can range over. The bridge assembles
`mem_FP_iff_computesInTime_polynomial` (whose bound holds at *every* input length, which is
what an indexed clock needs — an `=O` witness would not do), the single-tape theorem, and a
new `TM.descOfTM_computesInTime`.

That last one is genuinely trivial: `descCfg` only relabels the state, carrying input, work
and output tapes across verbatim, so it is the decider proof with two verdict-cell clauses
replaced by one `HasOutput`.

## IV.3 The clock normal form

The one arithmetic gap, closed FAF-side because the normal form is FAF's convention:

```lean
lemma exists_clock_of_polynomial (q : Polynomial ℕ) :
    ∃ a k : ℕ, ∀ n, q.eval n ≤ a * (n + 1) ^ k + a

lemma exists_desc_computesInTime_clock {f} (hf : f ∈ Complexity.FP) :
    ∃ (d : TMDesc) (a k : ℕ) (T : ℕ → ℕ),
      d.toTM.ComputesInTime f T ∧ ∀ n, T n ≤ a * (n + 1) ^ k + a
```

Take `a` the coefficient sum and `k` the degree; domination holds at every point, so no
eventually-quantifier enters. **Coverage is now a matter of choosing an index**, not of
proving anything further about machines.

## IV.4 Import surface

Coverage genuinely needs `FP`, so FAF's slice of the fork grows:

| | files | LOC |
| --- | ---: | ---: |
| Part III (`…UTM.Internal.Interp` only) | 5 | 2,180 |
| Part IV (`+ Classes.P.Description`) | 20 | 11,833 |
| `UTM.Universal`, for comparison | 44 | 26,461 |
| the whole library | 987 | 329,048 |

`DescExec` remains the only module in FAF naming a `Complexity.*` declaration.

## IV.5 What remains for trader-level coverage — exact plan

Four steps, all definitional plumbing over facts now proved. No further machine theory.

**1. The paper-facing class.** Derived from the existing token path, not invented:

```lean
def MachineEfficientTrader (Tr : Trader) : Prop :=
  ∃ (d : TMDesc) (a k : ℕ) (T : ℕ → ℕ),
    d.toTM.ComputesInTime (fun x => …) T ∧ (∀ n, T n ≤ a * (n + 1) ^ k + a) ∧
    ∀ n, Tr.strat n = strategyOfTokens n (unRpn (undigitize (bitsToDigits …)))
```

The day is unary (`unaryDay`), matching the paper; the decoder is the existing
`strategyOfTokens ∘ unRpn ∘ undigitize`, not a second one; malformed output keeps the
established zero-strategy semantics. Keep this *semantic* class separate from enumeration
membership until coverage is proved — they are proved equal, not defined equal.

**2. The enumeration.** `enumeratedMachineTrader i : Trader` with
`strat n := strategyOfTokens n (unRpn (undigitize (machineTokens i n)))`, mirroring
`TraderProgram.trader` exactly.

**3. Soundness.** `MachineEfficientTrader (enumeratedMachineTrader i)` for every `i` —
witnessed by `machineTokens_steps_le` and `length_machineTokens_le`, which already hold at
*every* index with no clock certificate verified. Truncation is the argument.

**4. Coverage.** `MachineEfficientTrader Tr → ∃ i, enumeratedMachineTrader i = Tr`. Take
`(d, a, k)` from the class witness, form `i := (MachineTraderProgram.index ⟨d, a, k⟩)`, and
show `machineTokens i n` reproduces the trader's token stream. The one lemma still needed is

```lean
-- evalHalted succeeds when the clock dominates the machine's actual running time
lemma evalHalted_isSome_of_le {d : TMDesc} {T : ℕ → ℕ} {f} (h : d.toTM.ComputesInTime f T)
    (x : List Bool) (t : ℕ) (ht : T x.length ≤ t) :
    ∃ c, evalHalted d t x = some c ∧ codedOutput c = f x
```

i.e. the *converse* of `runUntilHalt_spec` — the budgeted run finds the halt when the budget
is big enough. This is an induction mirroring `runUntilHalt_spec`'s, using
`TM.step`-determinism to line up the executable run with `reachesIn`. **Estimated 80–150
lines, and it is the only remaining non-plumbing item.** Then `Trader.ext` over strategy
outputs gives trader equality.

**5. TradingFirm.** `trading_firm_dominance_of_covered` is unchanged; the machine-class
theorem is its composition with step 4, exactly as `trading_firm_dominance` composes it with
`exists_enumeratedTrader_eq` today.

## IV.6 Revised Stage-3 status

| tranche | status | LOC | passes |
| --- | --- | ---: | ---: |
| complexity theory / universality | UPSTREAM, DONE | 0 | 0 |
| 4.31 port, function-output UTM wrapper | **DONE** (fork) | 0 | 0 |
| production `DescExec` + CI target | **DONE** | — | 0 |
| output extraction, `machineTokens`, `Primrec₂` | **DONE** | — | 0 |
| polynomial soundness (step + size) | **DONE** | — | 0 |
| **single-tape reduction for functions** | **DONE** (fork, 195 lines) | 0 | 0 |
| **`FP → TMDesc` under a clock** | **DONE** (fork + FAF) | 0 | 0 |
| `evalHalted` converse | remaining | 80–150 | 0.5–1 |
| trader class + enumeration + soundness | remaining | 200–350 | 1 |
| coverage + TradingFirm specialization | remaining | 150–250 | 0.5–1 |
| `LIACompiler` swap + property touch-ups | remaining | 200–400 | 1–2 |
| **Stage-3 remaining** | | **~0.6–1.2k** | **3–5** |

Part III projected 1.1–2.1k remaining over 5–9 passes; the single-tape theorem landing at
195 lines rather than 400–800 accounts for most of the reduction. Overall project remains
**~4–7k**, still dominated by Stage 2 (`PolyFueled → FP`), untouched by every pass so far.

## IV.7 Riskiest remaining theorem

No longer the single-tape reduction — that is done. The remaining risk is the
`evalHalted` converse of §IV.5 step 4, and it is *low*: it is an induction over the same
frozen-pair iteration `runUntilHalt_spec` already handles, in FAF, against a deterministic
machine, with no upstream file involved. Nothing left in Stage 3 requires touching a 5k-line
upstream proof.

## IV.8 A build-infrastructure note for the next session

Verifying fork changes needs care in a git worktree, because Lake owns `.lake/packages` and
hand-managing it fights the tool. The pattern that works:

* verify fork changes in a **standalone fork checkout** whose `lakefile.toml` has a `path`
  require to an already-built Mathlib, with the fork's own `lake-manifest.json` deleted so
  the path require is not overridden;
* let Lake own FAF's `.lake` entirely — `lake update complexitylib` after re-pinning, and
  never interrupt it mid-clone;
* never `pgrep -f` for a pattern that appears in the watcher's own command line.

---

# Part V — the machine trader class, coverage, and why Stage 3 does not yet close (2026-08-24)

_Fifth pass. Scope: the paper-facing machine trader class, its enumeration, and coverage.
Stage 2 and general `thm:ifp` untouched._

**Stage 3 is not closed.** The mathematical core landed; two items remain, and both are
diagnosed below rather than half-attempted. Read §V.3 and §V.4 before planning the next pass
— one of them changes what "finish Stage 3" costs.

## V.0 What landed

```lean
def MachineEfficientTrader (Tr : Trader) : Prop :=
  ∃ F : List Bool → List Bool, F ∈ Complexity.FP ∧
    ∀ n, strategyOfOutput n (F (unaryDay n)) = Tr.strat n

theorem exists_enumeratedMachineTrader_eq (Tr : Trader) (hTr : MachineEfficientTrader Tr) :
    ∃ i : ℕ, enumeratedMachineTrader i = Tr
```

Exact trader equality, not eventual agreement. Axioms
`[propext, Classical.choice, Quot.sound]`, no `sorry`.

Conventions, all derived from existing framework definitions rather than invented:

* **unary day** — `unaryDay n = List.replicate n true` has length exactly `n`, so a machine
  polynomial in input length is polynomial in the day and `Complexity.FP`'s asymptotics are
  the paper's; a binary rendering would silently strengthen the class;
* **token stream, not a numeral** — the class is stated over the machine's finite output
  word, so nothing has to construct a giant natural;
* **one decoder** — `strategyOfTokens ∘ unRpn ∘ undigitize ∘ bitsToDigits`, the existing
  pipeline, so malformed output keeps the established zero-strategy fallback;
* **class ≠ enumeration membership** — kept distinct, as the two are proved related, not
  defined equal.

Supporting results in `DescExec` (`runUntilHalt_complete` and friends) close the converse the
audit named as the last non-plumbing item, at ~95 lines against the projected 80–150.

One design point worth carrying forward: the budget must **strictly** exceed the running
time, because `stepFrozen` spends one iteration *noticing* that `codedStep` returned `none`.
That is absorbed by bumping the clock coefficient (`lt_clock_succ`), not by weakening the
converse.

## V.1 The chain, complete

```
f ∈ Complexity.FP
  → TM k in poly time         mem_FP_iff_computesInTime_polynomial   (upstream)
  → TM 1                      TM.exists_singleTape_computesInTime    (fork, Part IV)
  → TMDesc under q.eval       exists_desc_computesInTime_polynomial  (fork, Part IV)
  → under a·(n+1)^k + a       exists_clock_of_polynomial             (FAF, Part IV)
  → machineTokens i           machineTokens_eq_of_computesInTime     (FAF, this pass)
  → enumeratedMachineTrader i exists_enumeratedMachineTrader_eq      (FAF, this pass)
```

The UTM is not on this path. `ClockConstructible` is not on this path.

## V.2 Where the two remaining items sit

```
  MachineEfficientTrader  ──coverage ✓──▶  enumeratedMachineTrader
          ▲                                          │
          │                                          │ soundness ✗  (§V.3)
          └──────────────────────────────────────────┘

  enumeratedMachineTrader  ──?──▶  tradingFirmTrader     (§V.4)
```

## V.3 Soundness needs a clocked simulator — and that is structural

Soundness is `∀ i, MachineEfficientTrader (enumeratedMachineTrader i)`. In the fuel setting
its analogue `enumeratedTrader_ec` is `rfl`-shaped. At a machine class it is a real theorem,
and `boundary-efficiency-model.md` (line 50) already anticipated exactly that: *"At a machine
class both become theorems."*

The obstruction is precise. A bogus index — malformed description, or a clock too small for
the machine it names — denotes the machine's **truncated** behaviour. Exhibiting a
`Complexity.FP` witness for a truncation means exhibiting a machine that counts steps and
stops, i.e. a clocked simulator. There is no way around it: the truncation is what makes the
enumerated object total, and totality is what has to be certified.

complexitylib *has* the simulator — `UTM.ClockedUtm.clockedUtmTM : TM 7`, with
`clockedUtmTM_hoareTime_halt` and `clockedUtmTM_hoareTime_timeout` both proved, at a bound
linear in the clock. Reaching it costs:

| requirement | cost |
| --- | --- |
| `UTM.ClockConstructible` for the `a·(n+1)^k + a` clock register | 2,316 lines; has `clockConstructible_pow` and `mul_succ`, but scalar multiplication and addition need checking |
| `UTM.Clock`, `UTM.ClockedUtm` | 1,004 + 940 lines |
| counter subroutines beneath them | `Subroutines/Counter.lean` was among the files that failed the earlier port waves |
| description onto the UTM tape as `pair α x` | reintroduces `encodeDesc` and the `TerminatedRegion` side condition that indexing on `TMDesc` deliberately avoided |
| timeout convention mismatch | `clockedUtmTM` writes a sentinel `Γ.one` at cell 1 on timeout; `machineTokens` emits `[]` — a post-processing step |
| `HoareTime` → `ComputesInTime` → `FP` | assembly |

**Estimate 600–1,200 lines**, most of it porting and auditing modules currently outside the
trust path. That is a materially larger figure than Part IV's remaining-work table assumed,
and it is the single biggest revision this pass produces.

**Nothing downstream needs it.** `Construction/TradingFirm.lean` consumes coverage alone —
`boundary-efficiency-model.md` line 287 says so explicitly — and `enumeratedTrader_ec` is
inventoried but not depended on. Soundness is a quality claim about the enumeration, not a
premise of the dominance theorem.

## V.4 TradingFirm integration is a migration, not an integration

The good news first: `trading_firm_dominance_of_covered` uses `enumeratedTrader` **only
opaquely** — through `firmRawTrader j = (enumeratedTrader j).gate j` and
`Trader.gate_strat_of_lt`, both generic in the trader. Its 1,041-line proof does not depend
on the definition and would survive a redefinition untouched. The `hcov` seam is doing
exactly the job it was designed for.

The blocker is that `tradingFirmTrader` is hard-wired to `enumeratedTrader`. Two routes:

**(a) Redefine `enumeratedTrader`** to interleave the fuel and machine enumerations (even
indices one, odd the other). TradingFirm survives; fuel coverage survives via one branch;
machine coverage arrives via the other. But:

* `enumeratedTrader_ec : EfficientlyComputable (enumeratedTrader j)` becomes **false as
  stated** — a machine-enumerated trader need not be *fuel*-efficiently-computable — and it
  is an inventoried `AxiomAudit` endpoint, so this moves the trust surface;
* `LIACompiler.enumeratedTraderTrades_prim` needs reproving as a case split (both halves are
  `Primrec`, so this part is routine).

**(b) Parameterise TradingFirm** over the enumeration. Surgical in principle, but the
signature change propagates through `firmRawTrader`, `tradingFirmTotalBound`,
`tradingFirmComponentAt`, `tradingFirmTrader` and their ~55 mentions across
`TradingFirm`/`LIAComputation`/`LIACompiler`/`LIA`, and changes `tradingFirmTrader`'s type,
which the property tail consumes.

Neither is an integration; both are migrations, and both are the kind of global API churn
that should wait for Stage 2's `PolyFueled → Complexity.FP` transport. With that transport in
hand, route (a) becomes clean: `enumeratedTrader_ec` can be restated at the machine class and
the fuel branch retired, rather than the two coexisting awkwardly.

**Recommendation: do Stage 2 before finishing Stage 3's TradingFirm integration.** That
inverts the ordering the earlier passes assumed, and it is the main planning consequence of
this pass.

## V.5 What `dd:fuel` means now

| question | status |
| --- | --- |
| does a genuine machine trader class exist in FAF? | **yes** — `MachineEfficientTrader`, over `Complexity.FP` |
| is it effectively enumerable? | **yes** — `enumeratedMachineTrader`, total, `Primrec₂` evaluator |
| is every member covered by the enumeration? | **yes** — exact equality |
| is every enumerated item in the class? | **not yet** — §V.3 |
| does the LIA construction range over it? | **not yet** — §V.4 |
| is `dd:fuel` eliminated? | **no**, and it should not be described as such |

`PolyFueled`/`EfficientlyComputable` remain the internal certification technology every
concrete property proof uses, exactly as before. What changed is that the machine class and
its coverage now exist as theorems, so the remaining distance is a migration plus one
simulator, not open research.

## V.6 Revised remaining work

| item | LOC | passes |
| --- | ---: | ---: |
| Stage 2: `PolyFueled → Complexity.FP` | 2.5–4k | 4–6 |
| Stage 3 soundness (clocked simulator, §V.3) | 0.6–1.2k | 2–3 |
| Stage 3 TradingFirm migration (§V.4, after Stage 2) | 0.3–0.6k | 1–2 |
| `LIACompiler` swap + property touch-ups | 0.2–0.4k | 1–2 |
| **total** | **3.6–6.2k** | **8–13** |

Part IV projected ~0.6–1.2k for all of Stage 3's remainder; §V.3 alone is that size, and
§V.4 turns out to depend on Stage 2. The overall project figure is roughly unchanged
(~4–7k) because Stage 2 always dominated it — what moved is the *ordering*.

---

# Part VI — Stage 2: route decision and the interpreter time bound (2026-08-24)

_Sixth pass. Scope: choose a route for `PolyFueled`/`EfficientlyComputable → Complexity.FP`,
and land the foundational fact that route needs. Stage 3 untouched; general `thm:ifp`
untouched._

**Stage 2 is not closed.** What landed is the route decision, grounded in measurement, and
the conceptual theorem §13 of the brief asked to test — which came out affirmative.

## VI.0 A correction to the target, before anything else

The brief frames Stage 2 as `PolyFueled → FP`. Checking the definitions, that is **not the
theorem the trader-level capstone needs**:

```lean
def EfficientlyComputable (Tr : Trader) : Prop :=
  ∃ (lengthCode tokenCode : Nat.Partrec.Code) (a k : ℕ),
    clockedTrader lengthCode tokenCode (fun n => a * (n + 1) ^ k + a) = Tr
```

`EfficientlyComputable` quantifies over **arbitrary** codes under a polynomial clock — it
never mentions `PolyFueled`. So `EfficientlyComputable Tr → MachineEfficientTrader Tr`
requires clocked `evaln` on *arbitrary* codes to be `FP`, not just on the `PolyFueled`
fragment. `PolyFueled` is how FAF's concrete certificates are *built*; it is not what the
class quantifies over.

Consequence for §8 of the brief: the "which constructor fragment do LI certificates use?"
question does not reduce scope the way it was hoped to. The certificates do use `prec`
heavily (`addc`, `mulc`, `divmodc`, `mul`, `divmod1`, `gcdc` all go through
`PolyFueled.prec`) and `PolyFueled` has no `rfind'` introduction rule at all — but that only
constrains the *certificates*, not the class. **`rfind'` must be handled**, because
`EfficientlyComputable`'s codes are arbitrary.

There is a fallback if that proves too costly: prove the transport for `PolyFueled`-derived
traders only, and state the trader capstone over a restricted class. That weakens the public
claim and should be a last resort, not a plan.

## VI.1 Route comparison

| route | new LOC | hardest lemma | reuse | risk | verdict |
| --- | ---: | --- | --- | --- | --- |
| **A** counted machine bridge | 3–5k | stack-machine → TM with step accounting | `MachinePolyEC.comp`/`.pair` | high | **reject** |
| **B** direct `evaln` → complexitylib TM | 2.5–4k | `prec` loop with time recurrence | `Registers` library | medium | **accept** |
| **C** Cobham | 3–5k + 20k import | `rfind'` as bounded recursion on notation | `CobhamFP_eq_FP` | high | **reject** |

**A rejected.** `Machine/Basic.lean`'s own header states that reading its step count as a
time measure rests on the stack-machine ↔ TM polynomial-overhead fact, which is *"standard
and is not formalized here"*. So route A pays for that simulation **and** the
`evaln` → stack-machine compiler: two bridges where B needs one, and it leaves three machine
models alive. Sunk cost is not a reason.

**C rejected** (brief §18-D). `Cobham.boundedRec` requires the recursion's output to be
length-bounded by a function *already in the algebra*. For `evaln`'s `prec` ladder that is
plausible via `codeEvalBound`, but `rfind'` has no natural reading as recursion on notation —
its argument *grows* while fuel shrinks (`KNOWLEDGE.md`: "its guard failures are real") — and
the `Option` plumbing has no home in a `List Bool` algebra. It also costs +20k lines of
import surface for a class equality we would use in one direction.

**B accepted.** complexitylib's register library is a real head start:
`incRegTM`, `clearRegTM`, `addIntoTM`, `copyIntoTM`, `mulAddIntoTM`, `forRegTM`, `iterTM` —
each with a `HoareTime` specification. Missing and needed: subtraction, comparison, and
`Nat.sqrt` (for `unpair`).

**Representation.** complexitylib's registers are **unary** — `IsReg v t` puts `v` cells of
`Γ.one` on the tape. That is acceptable here and it is worth being explicit about why:
`PolyFueled` bounds values polynomially in the day `n`, the day is presented in unary, and
`Nat.pair` of two polynomially-bounded values is again polynomially bounded, so every
intermediate stays polynomial in the input length. Unary keeps the arithmetic machines and
their Hoare bounds simple, and `FP` does not care about the exponent. Should a nested loop
turn out to square the degree once too often, the fallback is a binary register layer, but
nothing so far suggests it is needed.

## VI.2 The theorem §13 asked us to test — and it holds

The brief's §13 asked whether fixed-code `evaln` has a structural polynomial time bound, and
said to test rather than assume. It does, and `LogicalInduction/Framework/Machine/CodeSteps.lean`
proves it:

```lean
def codeEvalSteps : Nat.Partrec.Code → ℕ → ℕ        -- interpreter invocations
lemma codeEvalSteps_poly (c : Nat.Partrec.Code) : IsPolyBounded (codeEvalSteps c)
```

The reason it is true is a genuine asymmetry in `evaln`'s own recursion:

* `pair` and `comp` recurse into **structurally smaller codes at unchanged fuel**;
* `prec` and `rfind'` recurse into the **same code with one less fuel**.

So for a fixed code the fuel-consuming clauses unroll into a sum over fuel levels, and their
nesting depth becomes the polynomial's exponent. The proof bounds each sub-count by the
*monotone majorant* its own polynomial bound supplies (avoiding a separate monotonicity
induction over the lexicographic order the definition uses), then sums.

This is the **time** half of the calibration. `Framework/Emission.lean` already had the
**value** half — `codeEvalBound`, `codeEvalBound_poly`, `codeEvaln_result_le` — and the model
card is right that the two must not be conflated: a small answer can cost enormous work. Both
now exist.

Also added, because the `prec` case needs it and `Framework/Computable.lean` lacked it:
`IsPolyBounded.mul` (two-function product) and `IsPolyBounded.add'`. `KNOWLEDGE.md` had
already flagged the missing `.mul` as something `exists_clock_loop` would need.

**Why this dissolves the `dd:fuel` worry rather than repairing it.** Compose
`codeEvalSteps_poly` with either `PolyFueled`'s fuel bound or `EfficientlyComputable`'s
explicit clock `a·(n+1)^k + a`, and the interpreter's step count is polynomial in the day `n`.
Because the paper presents the day in **unary**, polynomial in `n` *is* polynomial in the
input length. The historical concern was that value-polynomial bounds in a numeric parameter
might not be time-polynomial bounds — and under the paper's own unary convention they are.

## VI.3 What remains for Stage 2

Route B's remaining work, now against a settled time bound rather than an open question:

| item | LOC | notes |
| --- | ---: | --- |
| unary arithmetic: compare, subtract, `Nat.sqrt` | 400–700 | on top of `Registers`; `sqrt` is a bounded search via `forRegTM` |
| `Nat.pair` / `Nat.unpair` machines + Hoare specs | 300–500 | `pair` from `mulAddIntoTM`; `unpair` needs `sqrt` |
| structural compiler, 8 constructors | 900–1,500 | `prec` and `rfind'` are the loops; the rest compose |
| time recurrence → `ComputesInTime` | 300–500 | `codeEvalSteps_poly` supplies the combinatorics |
| `PolyFueled.toFP` / clocked-`evaln` capstone | 200–300 | assembly |
| `EfficientlyComputableTok` → `FP`, trader capstone | 300–500 | reuses `unaryDay`/`strategyOfOutput` from Stage 3 |
| **total** | **2.4–4.0k** | matching the original estimate |

The estimate did **not** improve — §2 of the brief hoped to beat 2.5–4k and the audit says
no. What improved is the risk: the conceptual question (is fixed-code clocked `evaln` even
polynomial-time?) is now answered in Lean rather than assumed, and the register library
removes the lowest layer of machine construction.

## VI.4 Interaction with Stage-3 soundness

Worth recording because the brief (§18-E) asked. Stage-3 soundness needs "a clocked run of a
`TMDesc` is `FP`"; Stage 2 needs "a clocked run of a `Nat.Partrec.Code` is `FP`". These are
different interpreters, so no single theorem discharges both. But the *technique* is shared —
a bounded loop with a step counter, built from `forRegTM`/`iterTM`, with a time bound — and
the arithmetic layer above is common. Building Stage 2's machine layer should therefore make
Stage-3 soundness materially cheaper than its standalone 600–1,200 line estimate. Not a
collapse; a genuine shared substrate.

---

# Part VII — Stage 2A: the arithmetic substrate (2026-08-24)

_Seventh pass. Scope: the concrete arithmetic machines the `evaln → FP` compiler needs.
Stage 3 untouched; general `thm:ifp` untouched; no migration._

**Stage 2 is not closed.** This pass landed the first missing arithmetic primitive and, more
importantly, measured what the rest costs. The measurement is the main output, and it is
worse than Part VI assumed — see §VII.4.

## VII.1 What `evaln` actually demands

From Mathlib's definitions (`Mathlib/Data/Nat/Pairing.lean`):

```
Nat.pair a b  = if a < b then b * b + a else a * a + a + b
Nat.unpair n  = let s := sqrt n
                if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)
```

so the primitive-operation table is:

| `Code` constructor | concrete operations |
| --- | --- |
| `zero`, `const` | write a constant register |
| `succ` | increment |
| `left`, `right` | `sqrt`, squaring, truncated subtraction, comparison |
| `pair` | comparison, squaring, addition |
| `comp` | sequencing, temporary registers |
| `prec` | comparison, decrement, bounded loop, carried state |
| `rfind'` | comparison, increment, decrement, search state, `Option` tag |

`Nat.pair`'s exact formula forces squaring and comparison; `unpair`'s forces `sqrt` and
truncated subtraction. None of these is avoidable by choosing a different pairing — the
theorem must match *Mathlib's* `pair`/`unpair`, since `evaln` is defined over them.

## VII.2 Representation, frozen

complexitylib's registers, unchanged: `IsReg v t` puts `v` cells of `Γ.one` on a work tape
at cells `1 … v`, head parked at 1, blank beyond (`regTape`, `regCells`). Values are
**unary**. That is sound here for the reason Part VI gave — everything is polynomially
bounded in a unary day — and it keeps every Hoare bound elementary.

Registers live on work tapes indexed by `Fin n`; temporaries are extra tape indices;
one machine step is one `TM.step`. Costs compose through `HoareTime`.

## VII.3 Substrate inventory, after this pass

| operation | source | status |
| --- | --- | --- |
| increment | `Registers.RegisterOps.incRegTM` | upstream ✓ |
| decrement (truncated) | `Registers.DecReg.decRegTM` | upstream ✓ |
| clear | `Registers.RegisterOps.clearRegTM` | upstream ✓ |
| bounded loop | `Registers.ForReg.forRegTM` | upstream ✓ |
| addition | `Registers.Arith.addIntoTM` | upstream ✓ |
| copy | `Registers.Arith.copyIntoTM` | upstream ✓ |
| multiply-accumulate | `Registers.Arith.mulAddIntoTM` | upstream ✓ |
| **truncated subtraction** | `Registers.Arith.subIntoTM` | **added this pass** ✓ |
| comparison | — | **missing** |
| zero test | `UTM.Clock.zeroTestTM` exists but sits in the UTM tree | needs extraction |
| integer `sqrt` | — | **missing** |
| `Nat.pair` machine | — | **missing** |
| `Nat.unpair` machine | — | **missing** |

Added upstream (fork `df9c431`), generic, nothing FAF-specific:

```lean
def subIntoTM (src dst : Fin n) : TM n := forRegTM (decRegTM dst) src

theorem subIntoTM_hoareTime (src dst) (hne : src ≠ dst) (a b) … :
    (subIntoTM src dst).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update work₀ dst (regTape (b - a))) ys)
      (a * ((2 * b + 4) + 2) + (a + 2))
```

Truncation is inherited from `decRegTM`, which floors at zero, so **no underflow test phase
is needed** — the loop simply decrements an already-empty register. That is a small but real
simplification over what the operation table suggested.

The same commit completes the 4.31 port of `Subroutines/Counter.lean`, which had been left
failing since the original port waves and blocks `Registers.Arith` transitively. Four sites,
all the familiar drift (`simpa` comparing syntactically where the sides are defeq:
`idleDir (Tape.init []).read` vs `Dir3.right`; `qstart` vs `LinearCounterPhase.scan`).

## VII.4 The measurement, and why it is bad news

`addIntoTM_hoareTime` — the *simplest* derived operation, a bounded loop around a primitive
that already has its own Hoare spec — is **70 lines**. `subIntoTM_hoareTime`, written as its
mirror, is **75**. That is the cost of one operation whose proof is a direct analogy to an
existing one.

Extrapolating honestly to the operations that have no such analogy:

| operation | shape | estimate |
| --- | --- | --- |
| zero test / comparison | branch on a register, or extract `zeroTestTM` from the UTM tree | 150–300 |
| squaring | `copyIntoTM` + `mulAddIntoTM` | 80–150 |
| `sqrt` | loop maintaining `k` and `k²`, comparison each step | 300–500 |
| `Nat.pair` | comparison + branch + squaring + additions | 250–400 |
| `Nat.unpair` | `sqrt` + two subtractions + comparison + branch | 300–500 |
| frame/composition glue for multi-register machines | — | 200–400 |
| **arithmetic substrate total** | | **1.3–2.3k** |

and that is *before* the eight-constructor compiler (900–1,500) and the time recurrence
(300–500). **Revised Stage-2 total: 2.5–4.3k lines, 5–8 sessions** — at the top of Part VI's
range rather than the bottom, and the arithmetic layer alone is a session or two.

The reason is structural, not incidental: every operation must carry a `HoareTime`
specification threading `Parked` invariants and `Function.update` frame conditions through
each register, and those obligations do not shrink with familiarity. complexitylib's own
`Registers` directory is ~6k lines for the handful of operations it provides, which is the
same ratio.

## VII.5 `Option ℕ` representation, decided now

Deciding this before the hard constructors, as the brief asks, because deferring it forces a
refactor. The compiled interpreter carries a **tag register** alongside the value register:

```
tag = 0        ↦  none
tag = 1, val   ↦  some val
```

Both are ordinary unary registers, so every existing operation applies to them, and the tag
is a zero-test away from a branch. `comp` propagates a `none` by testing the callee's tag
before running the caller; `prec` and `rfind'` test it each iteration and exit early. No new
machinery is needed beyond the comparison/zero-test that the arithmetic already requires.

## VII.6 Status

```
abstract complexity
  codeEvalSteps_poly                      ✓  (Part VI)
  codeEvalBound_poly, codeEvaln_result_le ✓  (pre-existing)

concrete arithmetic
  inc / dec / clear / loop / add / copy / mulAdd  ✓  upstream
  truncated subtraction                            ✓  this pass
  comparison, sqrt, pair, unpair                   open

Code compiler
  every constructor                                open

PolyFueled / EfficientlyComputable → FP            open
```

The headline question for this tranche — *do we now have a substrate on which the compiler
can be built without remaining uncertainty about pair/unpair complexity?* — is **no**.
`pair`/`unpair` are not built, and the two operations they rest on (comparison, `sqrt`) are
not built either. What *is* settled is that no conceptual obstacle remains: every missing
piece is a bounded loop over unary registers with an elementary time bound, and the pattern
for writing them is now demonstrated twice.

## VII.7 Reuse for Stage-3 soundness

`subIntoTM`, and the comparison/zero-test that comes next, are stated over generic registers
with no `Nat.Partrec.Code` anywhere — deliberately, per the brief. The clocked `TMDesc`
simulator that Stage-3 soundness needs uses the same `forRegTM`/`decRegTM` counter idiom, so
this layer should serve both. Keeping the arithmetic free of interpreter-specific structure
is the one design constraint worth defending as the layer grows.

---

# Part VIII — Stage 2A: `sqrt` deleted from the route (2026-08-24)

_Eighth pass. Scope: test whether `Nat.unpair` can be implemented extensionally as an
iterated successor, avoiding integer square root. Stage 3 untouched; no migration._

**The probe succeeded.** `sqrt` is gone from the Stage-2 machine route, and the arithmetic
substrate estimate drops accordingly. This is the first estimate revision in this project
that goes *down*.

## VIII.0 The idea, and why it works

Part VII priced an integer-`sqrt` machine at 300–500 Hoare-specified lines, because Mathlib
defines

```
Nat.unpair n = let s := sqrt n
               if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)
```

But the machine only has to be **extensionally** equal to `Nat.unpair`. It is under no
obligation to compute it the way Mathlib defines it.

`Nat.pair a b = if a < b then b*b + a else a*a + a + b` enumerates pairs in shells indexed by
`s = max a b`:

```
shell s :  (0,s) (1,s) … (s-1,s) (s,0) (s,1) … (s,s)
indices :   s²    s²+1  …  s²+s-1  s²+s  …        s²+2s = (s+1)²-1
```

so the *successor* in this enumeration is a four-case comparison with no arithmetic beyond
`+1`:

```lean
def pairNext : ℕ × ℕ → ℕ × ℕ
  | (a, b) =>
      if a < b then (if a + 1 < b then (a + 1, b) else (b, 0))
      else if b < a then (a, b + 1)
      else (0, a + 1)
```

— step along the ascending leg, turn at the corner, step along the descending leg, open the
next shell at the diagonal.

## VIII.1 What is proved

`LogicalInduction/Construction/Machine/PairSucc.lean`, **117 lines, no `sorry`**, axioms
`[propext, Classical.choice, Quot.sound]`:

```lean
theorem pair_pairNext (a b : ℕ) :
    Nat.pair (pairNext (a, b)).1 (pairNext (a, b)).2 = Nat.pair a b + 1

theorem pair_pairIter (n : ℕ) : Nat.pair (pairIter n).1 (pairIter n).2 = n

theorem pairIter_eq_unpair (n : ℕ) : pairIter n = Nat.unpair n

theorem pairIter_le (n : ℕ) : (pairIter n).1 ≤ n ∧ (pairIter n).2 ≤ n
```

The transition proposed in the tranche brief was **correct as written** — all four cases
check out against Mathlib's actual formula, with the corner case `a + 1 = b ↦ (b, 0)` and the
diagonal `a = b ↦ (0, a+1)` both exact.

`pairIter_eq_unpair` needs no reasoning about `sqrt` at all: it follows from
`pair_pairIter` and Mathlib's `Nat.unpair_pair`, i.e. from the fact that `unpair` inverts
`pair`. That is the whole trick — extensional equality via the inverse, rather than
operational agreement with the definition.

`pairIter_le` is the sizing lemma the machine layer needs: after `n` steps neither coordinate
exceeds `n`, so every register stays bounded by the input.

## VIII.2 The revised cost

| operation | Part VII estimate (sqrt route) | Part VIII (successor route) |
| --- | ---: | ---: |
| pure `pairNext` arithmetic | — | **117 ✓ done** |
| zero test / comparison | 150–300 | 150–300 |
| squaring | 80–150 | 80–150 |
| **`sqrt`** | **300–500** | **0 — deleted** |
| `Nat.pair` machine | 250–400 | 250–400 |
| `Nat.unpair` machine | 300–500 | 200–350 (loop `pairNextTM` `n` times) |
| frame/composition glue | 200–400 | 200–400 |
| **arithmetic total** | **1.3–2.3k** | **0.9–1.6k** |

**Roughly 400–700 lines removed**, and one of the two hardest machines (`sqrt`, with its own
correctness recurrence) disappears entirely. The `unpair` machine also gets simpler: a
`forRegTM` loop around `pairNextTM`, whose correctness routes through `pairIter_eq_unpair`
rather than through any arithmetic identity.

Revised Stage-2 total: **2.1–3.6k lines over 4–7 sessions**, down from Part VII's 2.5–4.3k
over 5–8.

## VIII.3 Runtime shape for the eventual machine

The composition the `unpair` machine will need, all of it now available:

```
n iterations                       (forRegTM over the input register)
× poly(n) work per pairNext        (comparison + increment on registers ≤ n, by pairIter_le)
= poly(n)
```

`pairIter_le` is what makes the per-iteration cost uniform: without it the registers could in
principle grow, and the product bound would not close.

## VIII.4 What did not land

The machine layer itself. `pairNextTM`, `compareTM`, `pairTM`, `unpairTM` are **not built** —
this pass bought the *design* that makes them cheaper, not the machines. Comparison is still
the next prerequisite, and it gates everything else.

Status:

```
pure arithmetic
  pairNext / pairIter / unpair equivalence      ✓ this pass
  codeEvalSteps_poly                            ✓ Part VI

machine arithmetic
  inc / dec / clear / loop / add / copy / mulAdd ✓ upstream
  subIntoTM                                      ✓ Part VII
  comparison, pairNextTM, pairTM, unpairTM       open

Code compiler                                    open
PolyFueled / EfficientlyComputable → FP          open
```

The decisive question this tranche asked — *can `sqrt` be deleted from the Stage-2 compiler
entirely?* — is **yes**, and the architecture is committed.

---

# Part IX — Stage 2A: the branch problem, and its cheap resolution (2026-08-24)

_Ninth pass. Scope: comparison, `pairNextTM`, `pairTM`, `unpairTM`. Stage 3 untouched; no
migration._

**The checkpoint did not complete.** Comparison's gating primitive landed; `pairNextTM`,
`pairTM` and `unpairTM` are not built. But the pass found and resolved an architectural
problem that would have derailed all three, and the resolution is much cheaper than the
obvious fix.

## IX.0 The problem: the output tape is doing double duty

complexitylib has a general branch combinator, `ifTM`, with a full Hoare specification
(`Hoare.lean`, bound `b_test + p_bound + max b_then b_else + 5`). It looked like the obvious
control-flow primitive for `pairNext`'s four-way case split.

**It cannot be used with the register library.** `ifTM tmTest tmThen tmElse` branches on the
**output tape's** cell 1: the test machine writes `Γ.one` there, and the branches receive
`⟨1, out.cells⟩`. But the register arithmetic is all stated over `EmitPred inp₀ work₀ ys`,
whose third conjunct is

```lean
def OutAcc (ys : List Bool) (out : Tape) : Prop :=
  out.head = ys.length + 1 ∧ out.cells 0 = Γ.start ∧
  (∀ i, (h : i < ys.length) → out.cells (i + 1) = Γ.ofBool ys[i]) ∧
  (∀ j, ys.length + 1 ≤ j → out.cells j = Γ.blank)
```

— the output tape is an append-only *emission accumulator*, and every cell past `|ys|` must
be blank. A test writing `Γ.one` into cell 1 invalidates `OutAcc []` outright. The two
conventions are incompatible, and no amount of frame plumbing reconciles them.

The obvious fix — write a register-level branch combinator `ifRegTM` in the shape of
`forRegTM` — would cost 250–400 lines: `forRegTM` itself takes 489 lines to reach its Hoare
spec.

## IX.1 The resolution: a flag, not a branch

`forRegTM body r` branches on a **work register** — its test phase reads `wHeads r` and
dispatches, never touching the output tape. So a register holding `0` or `1` *already is* a
conditional:

```
forRegTM body flag   runs body once when flag = 1, and skips it when flag = 0
```

The missing primitive is therefore not a branch combinator but a **flag**, and building one
needs no new control flow at all:

```lean
def setOneTM (q : Fin n) : TM n := seqTM (clearRegTM q) (incRegTM q)
def flagNonzeroTM (src flag : Fin n) : TM n :=
  seqTM (clearRegTM flag) (forRegTM (setOneTM flag) src)

theorem flagNonzeroTM_hoareTime … :
    (flagNonzeroTM src flag).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update work₀ flag (regTape (min v 1))) ys)
      (2 * d + 4 + 1 + (v * ((2 * 1 + 4 + 1 + (2 * 0 + 4)) + 2) + (v + 2)))
```

`setOneTM` is idempotent, so looping it `v` times lands on `min v 1`; correctness is a single
`forRegTM_hoareTime` application with the invariant `flag = min i 1`. **122 lines instead of
250–400, and no new combinator to maintain.**

Comparison then falls out of this plus `subIntoTM`: `a < b` iff `min (b - a) 1 = 1`.

## IX.2 What this buys the rest of the layer

Every remaining machine needs conditionals, so the pattern now fixed determines all of them:

| machine | shape |
| --- | --- |
| `ltFlagTM a b flag` | copy `b`, `subIntoTM a`, `flagNonzeroTM` |
| `pairNextTM` | three flags, then `forRegTM`-guarded arms for the four cases |
| `pairTM` | one flag, two guarded arms, `mulAddIntoTM` for the square |
| `unpairTM` | `forRegTM pairNextTM n`, correctness via `pairIter_eq_unpair` |

None needs `ifTM`, none needs the output tape, and all reuse `forRegTM_hoareTime`.

## IX.3 Status and revised estimate

```
pure arithmetic
  pairNext / pairIter / unpair equivalence  ✓ Part VIII
  codeEvalSteps_poly                        ✓ Part VI

machine arithmetic
  inc / dec / clear / loop / add / copy / mulAdd  ✓ upstream
  subIntoTM                                       ✓ Part VII
  setOneTM, flagNonzeroTM                         ✓ this pass
  ltFlagTM, pairNextTM, pairTM, unpairTM          open

Code compiler                                     open
PolyFueled / EfficientlyComputable → FP           open
```

| item | estimate |
| --- | ---: |
| `ltFlagTM` (copy + sub + flag) | 100–150 |
| `pairNextTM` | 250–400 |
| `pairTM` | 200–350 |
| `unpairTM` + loop invariant | 250–400 |
| **arithmetic remaining** | **0.8–1.3k** |

Stage-2 total remaining: **1.9–3.4k over 4–6 sessions**, essentially unchanged from Part
VIII's 2.1–3.6k — the flag trick saved roughly the cost of the branch combinator it replaced,
which is what kept the estimate from rising after a pass that produced only 122 lines.

## IX.4 The cost model, confirmed again

`flagNonzeroTM_hoareTime` took four build cycles: two rounds of `HoareTime.consequence`
misuse leaving the bound as a metavariable, and two `Function.update_of_ne` direction errors
(reading `src` out of an update at `flag` needs `src ≠ flag`, not its symm). None was
conceptual. This is the same ~70-line-per-operation plumbing tax Part VII measured, and it
does not appear to shrink with familiarity — the errors change, the volume does not.

Worth recording for whoever writes `pairNextTM`: the recurring hazards are (i) state the
theorem's time bound to match the combinator's output *exactly* rather than reaching for
`consequence`, and (ii) `Function.update_of_ne h` wants `readIndex ≠ updateIndex`, which is
`hne` or `hne.symm` depending on which register is being read.

---

# Part X — Stage 2A: comparison, guarded commands, and the pairing successor (2026-08-24)

_Tenth pass. Scope: `ltFlagTM`, `pairNextTM`. Stage 3 untouched; no migration._

**Checkpoint 1 is complete.** `ltFlagTM` and `pairNextTM` are both built, with exact
correctness and polynomial runtime, and the no-`ifTM` control-flow architecture is
validated end to end: nothing in either machine touches the output tape.

## X.0 The architectural question this pass existed to answer

Part IX ended with a flag primitive and a claim: that `forRegTM` guarded by a `{0,1}`
register replaces `ifTM` for register arithmetic. That was one lemma and an argument, not
evidence. `pairNextTM` — nine sequential guard computations feeding five guarded arms, all
under `EmitPred`'s frame — is the first construction big enough to falsify it.

It did not falsify it. `OutAcc ys` is carried through all fourteen stages unchanged, by
construction rather than by proof effort: no combinator in the chain reads or writes the
output tape, so the accumulator is never in play. The guard idiom composes.

## X.1 Comparison

```lean
def ltFlagTM (ra rb sc flag : Fin n) : TM n :=
  seqTM (copyIntoTM rb sc) (seqTM (subIntoTM ra sc) (flagNonzeroTM sc flag))

theorem ltFlagTM_hoareTime … :
    (ltFlagTM ra rb sc flag).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update (Function.update work₀ sc (regTape (b - a))) flag
        (regTape (if a < b then 1 else 0))) ys)
      (ltFlagTime a b s f)

lemma ltFlagTime_le : a ≤ B → b ≤ B → s ≤ B → f ≤ B →
    ltFlagTime a b s f ≤ 40 * (B + 1) ^ 2
```

`a < b` iff `min (b - a) 1 = 1`; truncated subtraction floors at zero, so no underflow test
is needed. The postcondition updates only `sc` and `flag`, so `ra`, `rb` and every other
register are read straight back out of `work₀` — the composition-friendliness §4 asked for.

The normalization against a single size parameter is the more useful half. A two-variable
runtime formula is tighter and useless; `40 * (B + 1) ^ 2` is what an iterated caller can
multiply by a loop count.

## X.2 The reformulation that made `pairNextTM` cheap

Written case-by-case the pairing successor has four arms:

```
a < b,  a+1 < b   ↦  (a+1, b)        a < b,  a+1 = b   ↦  (b, 0)
b < a             ↦  (a, b+1)        a = b             ↦  (0, a+1)
```

Two of those copy a live register over another, which is where §9's copy-before-clear
hazard lives.

Splitting on `a < b` alone removes it entirely. In the first half of a shell the first
component always advances; in the second half the second component always advances:

```
a < b   ↦  a := a + 1,  and b := 0 when a + 1 = b
b ≤ a   ↦  b := b + 1,  and a := 0 when a = b
```

Same function — when `a + 1 = b` the pair `(a+1, 0)` *is* `(b, 0)`; when `a = b` the pair
`(0, b+1)` *is* `(0, a+1)`. But now **every arm is a single `incRegTM` or `clearRegTM`**.
No arm copies anything, so §9's hazard does not arise and §8's "build the arms separately"
advice costs four one-line machines instead of four composite ones.

`pairNextFst_eq` and `pairNextSnd_eq` state the reformulation as the sum of the guarded
increments the machine performs, which is what the correctness proof consumes directly.

## X.3 The guards, and why there are only two comparisons

```
gLT = [a < b]    gGT = [b < a]    gEQ = [a = b]    gB1 = [a + 1 = b]
```

`gLT` and `gGT` are two `ltFlagTM` calls. The other two are arithmetic on those — no third
comparison, and no Boolean-algebra machinery (§6):

* `gEQ = 1 - gLT - gGT`, by trichotomy;
* `gB1 = gLT - min (b - a - 1) 1`, **reusing the `b - a` that `ltFlagTM` already leaves in
  its scratch register**. `a + 1 = b` is exactly "`b - a` is nonzero but `b - a - 1` is
  not", so one `decRegTM` and one `flagNonzeroTM` on a value already computed suffice.

Arm `b += gGE` is split into two arms guarded by `gGT` and `gEQ` separately, which removes
the need to materialize `gGE = 1 - gLT` at all: since the guards are disjoint, `b` is
incremented at most once either way.

## X.4 Structure of the machine and its proof

```lean
def pairNextTM (r : PairRegs n) : TM n := seqTM (pairGuardTM r) (pairArmsTM r)
```

Nine guard stages, five arm stages. Splitting into two phases halved the proof risk: each
half is a separately-stated theorem that could be brought green on its own.

```lean
theorem pairNextTM_hoareTime (r : PairRegs n) (v : Fin 9 → ℕ) (B : ℕ) … (hB : ∀ k, v k ≤ B) :
    (pairNextTM r).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (pairNextVals v)) ys)
      (80 * (B + 1) ^ 2 + 32 * B + 147)

theorem pairNextTM_hoareTime_poly … (400 * (B + 1) ^ 2)

theorem pair_pairNext (a b : ℕ) :
    Nat.pair (pairNextFst a b) (pairNextSnd a b) = Nat.pair a b + 1
```

`pairNextVals` names the final state of **all nine** registers explicitly, and every entry
is determined — no existential, no choice. That is deliberate: iterating this machine for
`unpairTM` needs a definite `w : ℕ → Fin n → Tape` family, which an existential
postcondition could not supply.

## X.5 The three abstractions that made a fourteen-stage proof tractable

The plumbing tax Part VII measured at ~70 lines per operation would have put this
construction at 900–1,000 lines. It came in around 480. Three extractions did that, each
meeting §17's "already cost duplicated lines twice" threshold before it was written:

| extraction | replaces | used |
| --- | --- | ---: |
| `parked_update`, `seqEmit` | a five-line `by_cases` and a four-line frame closure per stage | ~20× |
| `regsWork` + `regsWork_update` | a `Function.update_of_ne` chain per register read, quadratic in stage count | ~60× |
| `guardRegArm` | the full `guardTM_hoareTime` instantiation per arm | 5× |

`regsWork` is the one that mattered. Naming a work state by its **vector of register
values** rather than by a chain of `Function.update`s turns "update the state" into "update
one entry of `v : Fin 9 → ℕ`" — finite data — and turns "read a register" into one
rewrite. Without it the fourteen-stage bookkeeping is quadratic; with it, linear.

## X.6 Two failure modes worth recording

**`omega` atomizes nested indicator guards.** Reads stated as
`U1 0 = u 0 + (if u 4 = 0 then 0 else 1)`, with `u 4` itself an indicator, produce
conditions of the form `(if v 0 < v 1 then 1 else 0) = 0`. `omega` will not descend into an
`ite` sitting inside another `ite`'s condition; it abstracts the whole thing as an opaque
atom and reports an unprovable goal whose counterexample lists the atoms. Restating every
read in terms of the underlying *proposition* —
`U1 0 = if v 0 < v 1 then v 0 + 1 else v 0` — fixed all of it at once.

**A monolithic `simp only` over nine chained `set` bodies exceeds the heartbeat budget.**
`funext k; simp only [hU5, …, hU1, hu, …]; fin_cases k <;> simp` hit the same
`whnf`/`isDefEq` timeout as `DescExec`. Replacing it with level-by-level reads —
`U5 0 = f (U4 0)`, `U4 0 = f (U3 0)`, … — each proved by a two-line `by_cases`, elaborates
without raising any limit. Same lesson as Part V: **the fix for a heartbeat timeout is
structural, not a bigger budget.**

## X.7 Status and revised estimate

```
pure arithmetic
  pairNext / pairIter / unpair equivalence  ✓ Part VIII
  codeEvalSteps_poly                        ✓ Part VI

machine arithmetic
  inc / dec / clear / loop / add / copy / mulAdd  ✓ upstream
  subIntoTM                                       ✓ Part VII
  setOneTM, flagNonzeroTM                         ✓ Part IX
  guardTM, ltFlagTM                               ✓ this pass
  pairNextTM (+ correctness, runtime)             ✓ this pass
  pairTM, unpairTM                                open

Code compiler                                     open
PolyFueled / EfficientlyComputable → FP           open
```

| item | estimate |
| --- | ---: |
| `pairTM` (one flag, two guarded arms, `mulAddIntoTM`) | 150–250 |
| `unpairTM` (`forRegTM pairNextTM`, loop invariant) | 200–350 |
| **arithmetic remaining** | **0.35–0.6k** |

Stage-2 total remaining: **1.4–2.6k over 3–5 sessions**, down from Part IX's 1.9–3.4k.

This is the first pass where the estimate fell rather than held. The reason is not that the
plumbing tax dropped — `pairNextTM` still cost roughly what a fourteen-stage composition
should. It is that `regsWork` and `guardRegArm` are *reusable*: `pairTM` and `unpairTM` are
the same shape and inherit all three abstractions, so their per-stage cost is now
measured — about 12 lines — rather than projected.

## X.8 On the machine-load guard

`safe-lake.sh` deadlocked this pass. `resource-guard.sh` reads swap use from
`vm.swapusage`, which on macOS counts pages allocated to the swap *file* — and macOS never
shrinks that file. It sat pinned at 13.6G/14.3G (94–95%) for the entire session with **zero
Lean workers and 45% RAM free**, so `wait 900` could never clear and every build refused to
start after a fifteen-minute stall.

Builds here ran with `CLAUDE_MAX_SWAP_PCT=97` and `CLAUDE_LAKE_JOBS=3` — the raised swap
threshold paired with a hard cap on elaborator fan-out well below the default `ncpu - 2 = 8`,
which bounds peak memory more tightly than the default configuration would have. The memory,
disk and load thresholds and the global cross-session build lock were left untouched.

Worth fixing properly in the guard: swap *pressure* is `vm_stat`'s swapin/swapout **rate**,
not `vm.swapusage`'s high-water allocation. As written the check becomes a permanent
false positive on any machine that has ever swapped hard, which is every machine that has
built mathlib.

---

# Part XI — Stage 2A complete: `Nat.pair`, `Nat.unpair`, and one arithmetic cost (2026-08-24)

_Eleventh pass. Scope: `pairTM`, `unpairTM`, common cost polynomial. No `Code` compiler._

**The arithmetic substrate is finished.** Exact ordinary-TM implementations of Mathlib's
`Nat.pair` and `Nat.unpair` over unary registers, with correctness against the exact
Mathlib definitions, `HoareTime` specifications, normalized polynomial runtimes, and a
single polynomial dominating every operation in the directory. Integer square root never
appeared. `OutAcc` is untouched throughout.

## XI.0 `pairTM` needs no branch at all

The tranche's plan was a two-armed guarded computation: `out := b*b + a` under `[a < b]`,
`out := a*a + a + b` otherwise. That is not necessary.

`Nat.pair a b = if a < b then b*b + a else a*a + a + b`. Writing `m = max a b`, **both**
arms are

```
m*m + a + (if a < b then 0 else b)
```

— when `a < b` we have `m = b` and the last term vanishes; otherwise `m = a`, so
`m*m + a + b` is `a*a + a + b`. And over truncated arithmetic `max a b = a + (b - a)`,
where `b - a` is *exactly what `ltFlagTM` already leaves in its scratch register*. So the
maximum costs one `addIntoTM` on a value already computed, and the trailing conditional
term is applied by **multiplying by the `0/1` flag** rather than by guarding an arm:

```lean
def pairTM (r : PairingRegs n) : TM n :=
  seqTM (ltFlagTM (r 0) (r 1) (r 2) (r 3)) <|      -- gLT, and b - a in scratch
  seqTM (copyIntoTM (r 0) (r 4)) <| seqTM (addIntoTM (r 2) (r 4)) <|   -- m := a + (b - a)
  seqTM (copyIntoTM (r 4) (r 5)) <|                -- mulAddIntoTM needs distinct factors
  seqTM (clearRegTM (r 6)) <| seqTM (mulAddIntoTM (r 4) (r 5) (r 6)) <|  -- out := m*m
  seqTM (addIntoTM (r 0) (r 6)) <|                 -- out += a
  seqTM (setOneTM (r 7)) <| seqTM (subIntoTM (r 3) (r 7))                -- gGE := 1 - gLT
        (mulAddIntoTM (r 7) (r 1) (r 6))           -- out += gGE * b
```

Ten straight-line stages, no guarded arm, no `ifTM`, no case split in the machine at all.
Correctness (`pair_eq_max`) is against the exact Mathlib definition, not via `Nat.unpair`.

Runtime is `500 * (B + 1) ^ 4`. The degree is **quartic, not cubic** — I had estimated
cubic and was wrong. `mulAddIntoTM` is a loop of `addIntoTM`s, each itself linear in the
accumulated value, so squaring an `O(B)`-length unary register costs `O(B⁴)`. This is
inherent to the unary representation and nothing here tries to fix it.

## XI.1 `unpairTM` and the extensional inverse

```lean
def unpairTM (r : PairRegs n) (ctr : Fin n) : TM n :=
  seqTM (clearRegTM (r 0)) (seqTM (clearRegTM (r 1)) (forRegTM (pairNextTM r) ctr))
```

Correctness factors exactly as designed — machine iteration, then pure identity:

```lean
lemma pair_pairStepIter    : Nat.pair (pairStep^[j] (0,0)).1 (pairStep^[j] (0,0)).2 = j
lemma unpair_eq_pairStepIter : Nat.unpair j = pairStep^[j] (0, 0)
```

The second is one line from the first plus `Nat.unpair_pair`. **The machine never evaluates
`Nat.unpair`'s square-root definition; it computes a function equal to it.** That is the
whole reason sqrt is absent, and it is now discharged rather than promised.

Two things fell out better than planned:

* **The input is preserved for free.** `forRegTM` uses the *head position* on its fuel
  register as the counter and never writes that register's cells. So the counter still
  holds `n` when the loop exits, and `Code.left` / `Code.right` will find it there.
* **The runtime invariant is Mathlib's own.** I expected to need FAF's `pairIter_le`.
  Composing `unpair_eq_pairStepIter` with `Nat.unpair_left_le` / `unpair_right_le` gives
  `a_j, b_j ≤ j` directly, so no FAF-side lemma is used and no new pure fact was needed.

One adapter was required, exactly where §9 predicted an interface mismatch might appear:

```lean
lemma regsWork_update_of_ne (hi : ∀ k, r k ≠ i) :
    regsWork r (Function.update w₀ i t) v = Function.update (regsWork r w₀ v) i t
```

`forRegTM` hands the body a state in which the counter carries the loop cursor rather than
a register tape; this frames a register-indexed state past that update. Twelve lines, and
it is the *only* glue between `pairNextTM_hoareTime` and `forRegTM_hoareTime`.

Runtime `500 * (B + 1) ^ 3` — cubic: `n` iterations of a quadratic successor.

## XI.2 One polynomial for the layer

```lean
def evalnArithmeticCost (B : ℕ) : ℕ := 500 * (B + 1) ^ 4
```

dominates `incRegTM`, `decRegTM`, `clearRegTM`, `setOneTM`, `addIntoTM`, `subIntoTM`,
`copyIntoTM`, `mulAddIntoTM`, `flagNonzeroTM`, `ltFlagTM`, `pairNextTM`, `pairTM` and
`unpairTM` on values bounded by `B`. Primitives get numeric domination lemmas (the compiler
composes those); the three capstones get `HoareTime` versions at the common bound.

This is the shape §15's global argument wants:

```
concrete runtime ≤ codeEvalSteps c fuel * evalnArithmeticCost (codeEvalBound c fuel input) + overhead
```

with both factors polynomial for fixed `c`.

## XI.3 `regsWork` scaled, and was generalized

`regsWork` continued to work exactly as Part X measured — per-stage cost stayed around a
dozen lines across `pairTM`'s ten stages. It was generalized from `Fin 9` to arbitrary
arity (`Regs m n`) so `pairTM` (8 registers) and `unpairTM` (9 plus an external counter)
share it; every existing lemma generalized verbatim.

## XI.4 Failure modes recorded

**`omega` cannot relate `v k` to `v 0` with symbolic `k`.** `guardVals_le` failed on the
fall-through branch because omega saw `v k` as an atom unrelated to `v 0`, `v 1` even
though it had derived `k ≤ 1`. `fin_cases k` makes the indices literal and the goals close
immediately. The Part X lesson generalizes: *when omega reports a counterexample whose atom
list contains a function application you expected to be resolved, the index is symbolic.*

**Bound expressions must match the combinator's output exactly, argument for argument.**
`addIntoTM`'s bound is `a * ((2 * (b + a) + 4) + 2) + (a + 2)` where `b` is the
*destination's current value*; I wrote the S7 bound with `b = m*m` instead of `m*m + a` and
got a type mismatch several stages later. Same hazard as Part IX's, in a new dress.

## XI.5 Status

```
machine arithmetic
  inc / dec / clear / loop / add / copy / mulAdd  ✓ upstream
  subIntoTM, setOneTM, flagNonzeroTM              ✓ Parts VII, IX
  guardTM, ltFlagTM, pairNextTM                   ✓ Part X
  pairTM, unpairTM                                ✓ this pass
  evalnArithmeticCost                             ✓ this pass
  ARITHMETIC SUBSTRATE COMPLETE

Code compiler (left/right/pair/comp/prec/rfind')  open
PolyFueled / EfficientlyComputable → FP           open
```

| item | estimate |
| --- | ---: |
| `left` / `right` / `pair` / `zero` / `succ` | 250–400 |
| `comp` | 150–300 |
| `prec` (bounded recursion over a register) | 300–500 |
| `rfind'` (the unbounded search, clocked) | 300–500 |
| assembling `evaln` + the global time bound | 300–500 |
| `PolyFueled` / `EfficientlyComputable → FP` | 200–400 |
| **Stage-2 remaining** | **1.5–2.6k over 3–5 sessions** |

Essentially flat against Part X's 1.4–2.6k, and that is the honest reading: this pass spent
its budget finishing arithmetic rather than reducing what follows. What did change is that
*none* of the remaining work is arithmetic — the next tranche is purely about
`Nat.Partrec.Code`.

No `Code` constructor probe was attempted: the arithmetic capstones and the cost theorem
consumed the pass, and §16 makes the probe explicitly optional.

---

# Part XII — Stage 2B: the `Code` compiler begins (2026-08-24)

_Twelfth pass. Scope: result convention, register layout, the shared guard, and the four
non-recursive constructors. `pair` and `comp` did **not** land._

## XII.0 What `evaln` actually says

Read off Mathlib's definition rather than from memory, as the tranche insisted — and two
of the tranche's own premises were wrong.

**There is no `const` constructor.** `Nat.Partrec.Code` has exactly eight: `zero`, `succ`,
`left`, `right`, `pair`, `comp`, `prec`, `rfind'`. `Code.const` is a *derived definition*
built from `zero`/`succ`, not a case to compile.

**The guard is universal and uniform.** At fuel `0` every code is `none`; at fuel `k + 1`
*every* constructor begins with the same `guard (n ≤ k)`. Since `n ≤ k ↔ n < k + 1` and
`n < 0` is false, the single test

```
n < fuel
```

is the entire guard, fuel-`0` case included. So the tranche's §4 Route B is not merely
convenient — it is forced by the shape of the definition. `evaln_zero_eq` and its three
siblings state each constructor as `if n < k then … else none`, and each compiled machine
opens with that one test.

Centralizing does *not* mean hoisting out of the recursion: `pair`, `comp`, `prec` and
`rfind'` all re-guard their own sub-calls, so every compiled machine carries its own copy.

## XII.1 The compiler has no control flow

The tranche expected guarded arms for the `none` case. They are not needed. Each machine
computes its constructor's answer **unconditionally** and multiplies both result registers
by the `0/1` guard flag:

```lean
lemma resultTag_ite : resultTag (if p then o else none) = (if p then 1 else 0) * resultTag o
lemma resultVal_ite : resultVal (if p then o else none) = (if p then 1 else 0) * resultVal o
```

This is the same multiplicative mask that removed the branch from `pairTM` in Part XI, and
it generalizes: `zero`, `succ`, `left` and `right` are each a *straight line* of three to
five register operations, with no `guardTM` and no `ifTM` anywhere. `OutAcc ys` is carried
through untouched by construction rather than by proof effort.

The price is that a compiled machine does its work even when the guard fails and the answer
is discarded. That is bounded work on a bounded tree, so it costs a constant factor in the
eventual polynomial and nothing in the argument's shape.

## XII.2 The conventions, frozen

**Result.** `tag = 0` is `none`, `tag = 1` is `some`. The value register under `none` is
**canonically `0`**, not a don't-care — because the postcondition of a compiled machine is
a *definite* register-value vector, and §XII.4 below shows why definiteness is
load-bearing.

**Registers.** Sixteen, as `CodeRegs n = Regs 16 n`:

| index | role |
| ---: | --- |
| `0` | input `n` |
| `1` | fuel `k` |
| `2` | result tag |
| `3` | result value |
| `4` | guard flag `[n < k]` |
| `5` | guard scratch (`k - n`) |
| `6`–`15` | body scratch — ten registers, enough for `unpairTM` (nine plus an external counter) and `pairTM` (eight) |

**Correctness shape.** Every constructor proves the same predicate:

```lean
def EncodesEvaln (c : Code) (v u : Fin 16 → ℕ) : Prop :=
  u 2 = resultTag (evaln (v 1) c (v 0)) ∧ u 3 = resultVal (evaln (v 1) c (v 0))
```

paired with a `HoareTime` from `regsWork r w₀ v` to `regsWork r w₀ (…Vals v)` at
`m * evalnArithmeticCost B + (m - 1)` for an `m`-stage machine. Semantics and timing stay
separate, as §13 asked, and all arithmetic cost cites the Part XI capstone — no new
asymptotics were derived.

## XII.3 What landed

| constructor | machine | stages | proved |
| --- | --- | ---: | --- |
| `zero` | guard; `tag := gflag`; `val := 0` | 3 | ✓ |
| `succ` | guard; `sc := n+1`; `tag := gflag`; `val := gflag · sc` | 6 | ✓ |
| `left` | guard; `unpairTM`; `tag := gflag`; `val := gflag · unpair.1` | 5 | ✓ |
| `right` | same machine, window index `1` | 5 | ✓ |

`left` and `right` share one machine `compileProj r wj` parameterized by the window index,
so the Hoare proof is written once. `Nat.unpair` is never unfolded: the proof cites
`unpairTM_hoareTime_arith` and `unpairVals_zero` / `unpairVals_one`.

**`pair` and `comp` did not land.** They are the tranche's headline and I did not reach
them; see XII.5 for the design they need.

## XII.4 New infrastructure: register sub-windows

`left` runs `unpairTM` — a nine-register machine — inside the sixteen-register compiled
layout. That needed a way to move a register-indexed state across a window boundary, which
is now upstream and generic:

```lean
regsWork_restrict : regsWork r w₀ v = regsWork (shift.trans r) (regsWork r w₀ v) (v ∘ shift)
regsWork_window   : regsWork (shift.trans r) (regsWork r w₀ v) u
                      = regsWork r w₀ (writeWindow shift v u)
```

`restrict` turns the caller's state into the sub-machine's precondition; `window` turns the
sub-machine's postcondition back. Together they are the whole caller-side interface, and
they generalize Part XI's `regsWork_update_of_ne` from one register to an arbitrary window.

This is the piece that makes the recursive constructors tractable, and it is why the
postcondition must stay **definite**: a `forRegTM` loop body — which is what `prec` and
`rfind'` will be — needs an explicit `w : ℕ → Fin n → Tape` family, which an existential
postcondition cannot supply. `unpairTM` already demonstrated the pattern with `pairNextTM`
as its body.

## XII.5 Interface sanity check against `prec` and `rfind'`

Both recurse **on fuel, not on code structure**:

```
prec cf cg : evaln k (prec cf cg) (pair a y)      -- same code, fuel k
rfind' cf  : evaln k (rfind' cf)  (pair a (m+1))  -- same code, fuel k
```

Answering the tranche's six questions:

1. **Same code, smaller fuel** — yes, both.
2. **Surviving each iteration:** `prec` needs `a`, the index `y`, the running value `i`, and
   the current fuel; `rfind'` needs `a`, the search index `m`, and the current fuel.
3. **Nested result slots:** none. The self-recursion is a *chain* of depth ≤ fuel, not a
   nest, so a fixed number of slots suffices.
4. **Tag/value convention:** sufficient — each step yields one `Option ℕ`.
5. **Call/return discipline:** not needed. Because the self-call decreases fuel and fuel is
   a unary register, the recursion unrolls into a **bounded loop** driven by `forRegTM`.
6. **`forRegTM` fits** both.

The load-bearing consequence: since the self-call is at the *same* code, `compileCode`
cannot recurse into itself there — but it does not need to. `prec cf cg` compiles to a loop
whose *body* uses compiled `cf` and `cg`, both structurally smaller. **So `compileCode`
remains a plain structural recursion on `Code`**, and the interface holds.

## XII.6 The design `pair` and `comp` need

The one thing this pass did not resolve by construction. `pair cf cg` runs compiled `cf`,
saves `x`, then runs compiled `cg` — and `cg` will clobber the shared scratch, including
wherever `x` sits, since every compiled machine uses the same sixteen registers.

The resolution is the window machinery from XII.4: give each nesting level its **own
sixteen-register block**. Depth `d` occupies registers `16d … 16d+15`; a parent copies its
input and fuel down into the child's registers `0`/`1`, runs the child through
`childWindow.trans r`, and reads the answer back out of the child's `2`/`3`. The parent's
own registers are untouched *by construction* rather than by a frame argument, so no save
slots and no ordering hazards exist at all.

Register count becomes `16 * (codeDepth c + 1)` — linear in the code's nesting depth, which
is fine for a fixed code. `comp` is the cheaper of the two (it needs no saved value: `cg`'s
output becomes `cf`'s input, and the original `n` is dead afterwards).

## XII.7 Status and estimate

```
Code compiler
  result/register conventions, shared guard   ✓ this pass
  zero, succ, left, right                     ✓ this pass
  register sub-windows (upstream)             ✓ this pass
  pair, comp                                  open — design fixed, XII.6
  prec, rfind'                                open — interface validated, XII.5
PolyFueled / EfficientlyComputable → FP       open
```

| item | estimate |
| --- | ---: |
| per-depth register blocks + `compileCode` recursion | 200–350 |
| `pair` | 250–400 |
| `comp` | 200–350 |
| `prec` (fuel loop) | 400–600 |
| `rfind'` (fuel loop) | 350–550 |
| global time bound + `PolyFueled`/`EfficientlyComputable → FP` | 400–700 |
| **Stage-2 remaining** | **1.8–3.0k over 4–6 sessions** |

Up from Part XI's 1.5–2.6k. The increase is honest rather than a miss: Part XI's estimate
was made before reading the `evaln` equations, and the per-depth register-block layer is
real work that had not been costed. What came *down* is risk — the two design questions
that could have forced a redesign (does `compileCode` recurse structurally? does the
result convention survive the loop constructors?) are both answered yes.

---

# Part XIII — Stage 2B: the mask architecture, proved (2026-08-24)

_Thirteenth pass. Scope: `codeDepth`/block allocation, `pair`, `comp`. The **semantic**
layer for `pair` and `comp` landed; the **machine** layer did not._

## XIII.0 The decisive result

Part XII conjectured (§17 of that tranche) that every constructor subcomputation could run
*unconditionally*, with semantic dependency implemented by result masks rather than
control-flow suppression. That is now a theorem rather than a hope:

```lean
lemma pair_mask_tag : resultTag (evaln k (cf.pair cg) m)
  = [m < k] * resultTag (evaln k cf m) * resultTag (evaln k cg m)
lemma pair_mask_val : resultVal (evaln k (cf.pair cg) m)
  = [m < k] * resultTag (evaln k cf m) * resultTag (evaln k cg m)
      * Nat.pair (resultVal (evaln k cf m)) (resultVal (evaln k cg m))

lemma comp_mask_tag : resultTag (evaln k (cf.comp cg) m)
  = [m < k] * resultTag (evaln k cg m)
      * resultTag (evaln k cf (resultVal (evaln k cg m)))
lemma comp_mask_val : … * resultVal (evaln k cf (resultVal (evaln k cg m)))
```

The `comp` mask is the interesting one. `cf` is applied to `resultVal` of `cg`'s answer,
which is `0` *exactly* when `cg` failed — so the machine may run `cf` on garbage input and
still be exactly right, because the `cg` tag factor zeroes the product. **This is what the
canonical `none`-value convention buys**, and it retroactively justifies calling that
convention load-bearing rather than cosmetic in Part XII.

Consequence: `pair` and `comp` need no branch, no guarded arm and no `ifTM` — only
arithmetic masks. The same should hold inside the `prec` and `rfind'` loop bodies.

## XIII.1 Fuel, checked rather than assumed

The tranche's §18 asked specifically. From the definition:

```
| k + 1, pair cf cg => guard (n ≤ k); Nat.pair <$> evaln (k+1) cf n <*> evaln (k+1) cg n
| k + 1, comp cf cg => guard (n ≤ k); let x ← evaln (k+1) cg n; evaln (k+1) cf x
```

**Both children receive the parent's fuel undecremented.** No `fuel - 1` anywhere. Only
`prec` and `rfind'` decrement, and only for their *self*-calls. So the parent's fuel
register can be copied to a child verbatim, and stays pristine.

## XIII.2 New upstream plumbing

```lean
regsWork_restrict / regsWork_window / writeWindow   -- Part XII, sub-windows
shiftEmb / shiftEmb_disj / shiftEmb_trans_disj      -- this pass, offset sub-tuples
```

`shiftEmb o` names the `m` registers starting at offset `o` of a tuple of `M`. Composed
with a `Regs M n` it yields a `Regs m n`, so the *existing* `Regs 16 n`-based constructor
machines can be instantiated at any offset of a larger register file **without being
rewritten** — which was the point. Block disjointness reduces to arithmetic on offsets.

## XIII.3 Why the machine layer did not land: the indexing problem

The composition theorem for `pair` needs the two children's specs as hypotheses. Each child
occupies its own block, and — because a child may itself be a `pair` — the *size* of a
child's block depends on its code. So the ambient register file has arity `16 * size c`,
and a child's spec is stated over a different arity than its parent's.

That forces a choice, and both options are real infrastructure work that should be decided
at the *start* of a session rather than the end of one:

**(a) Arity-polymorphic `Fin` indexing.** State everything over one ambient `Regs N n` with
`N` symbolic, indexing registers as `R ⟨base + i, _⟩`. Every index carries a proof
obligation, and the final register-vector identification can no longer use `fin_cases`
(which needs a literal arity) — it becomes pointwise reasoning with `omega` on indices.
Workable, but it taxes every line of a ~300-line proof.

**(b) A ℕ-indexed register state.** Replace `regsWork (r : Regs m n) (v : Fin m → ℕ)` with a
variant taking `v : ℕ → ℕ` and a register naming function defined on an initial segment.
This removes `Fin` arithmetic from the compiler entirely. It is the cleaner answer and is
what I would build first next pass, but it means adding a second state abstraction upstream
alongside `regsWork` and relating the two.

I chose to stop at this decision point rather than commit to one under time pressure and
half-build it — the tranche's Stop A is exactly this situation ("the whole point is to pay
this cost once"), and §26 warns against leaving partial work uncommitted.

**Nothing about the architecture is in doubt.** The masks are proved, the fuel is checked,
the window and offset plumbing is green and pushed. What remains for `pair`/`comp` is
mechanical composition once the indexing scheme is fixed.

## XIII.4 A note on `codeDepth`

I did not define it, and on reflection **size-based allocation is better than depth-based**
for this compiler. With blocks allocated as disjoint intervals — `size (pair cf cg) =
1 + size cf + size cg`, child blocks at `base + 1` and `base + 1 + size cf` — every block in
the whole tree is pairwise disjoint by construction, and no sequential-reuse argument is
needed. Depth-based allocation needs two blocks per depth (so siblings do not collide) plus
an argument that a completed sibling's subtree may be overwritten; interval allocation needs
neither. Registers are `16 * size c` rather than `16 * (depth c + 1)` — larger, and
irrelevant, since `c` is fixed (XIII.5).

## XIII.5 Machine size versus runtime complexity

Worth stating where the allocator will live: the register count `16 * size c` is a function
of the *code*, which is fixed before the machine exists. It contributes a code-dependent
constant to the eventual bound and must never enter the runtime variable. There is no
obligation of the form `size c ≤ poly(input)` and no such thing should be attempted.

## XIII.6 Status

```
Code compiler
  conventions, guard, zero/succ/left/right     ✓ Part XII
  pair/comp exact equations + mask formulas    ✓ this pass
  register sub-windows, offset sub-tuples      ✓ Parts XII–XIII (upstream)
  block allocator + pair/comp machines         open — blocked on the indexing choice
  prec, rfind'                                 open — interface validated Part XII
PolyFueled / EfficientlyComputable → FP        open
```

| item | estimate |
| --- | ---: |
| ℕ-indexed register state (option b) | 200–300 |
| interval block allocator + `compileCode` | 150–250 |
| `pair` machine | 250–350 |
| `comp` machine | 200–300 |
| `prec` | 400–600 |
| `rfind'` | 350–550 |
| global bound + FP transport | 400–700 |
| **Stage-2 remaining** | **2.0–3.1k over 4–6 sessions** |

Essentially flat against Part XII's 1.8–3.0k. The mask lemmas removed real risk from
`pair`/`comp` (no branching machinery is needed at all), and the indexing layer added an
equivalent amount of newly-visible work.

---

# Part XIV — Stage 2B: ambient arity works; nested compilation proved (2026-08-25)

_Fourteenth pass. Scope: the indexing decision, then `pair` and `comp`. The indexing
question is settled and the nested-invocation phase of `pair` is proved; the remaining
phases are not._

## XIV.0 The previous pass's conclusion was wrong

Part XIII stopped at an "indexing problem": child and parent compiler theorems appeared not
to compose because they lived at different arities, and I proposed replacing `regsWork`
with an ℕ-indexed state model. **That was a misanalysis, and the tranche was right to
push back on it.**

A child's ambient block is `(shiftEmb 16 h).trans R` — a *sub-window of the parent's own
ambient `R`*. So `regsWork_restrict` applies directly, parent and children are all `TM n`
for the same ambient `n`, and ordinary `seqTM` composes them. The experiment that settles
it is three lines:

```lean
have h := compileZero_hoareTime ((shiftEmb 16 _).trans R) (V ∘ shiftEmb 16 _) B …
rw [regsWork_restrict R (shiftEmb 16 _) w₀ V, ← regsWork_window]
exact h
```

No second state model. `Fin` stayed manageable throughout; nothing needed `fin_cases` on a
symbolic arity, because every *local* block is a `Regs 16 n` and only the ambient vector
carries the symbolic index — and that is manipulated by `writeWindow`, not by enumeration.

## XIV.1 The child-call theorem

The interface collapses to one upstream lemma:

```lean
lemma runChild (W : Fin m ↪ Fin A) (R : Regs A n) (M : TM n) (F) (t B) … :
    M.HoareTime (EmitPred inp₀ (regsWork R w₀ V) ys)
                (EmitPred inp₀ (regsWork R w₀ (writeWindow W V (F (V ∘ W)))) ys) t
```

with `runChild_frame` giving "outside the window is untouched" and `writeWindow_bounded`
carrying value bounds through. **A caller's registers are preserved structurally**, by
disjointness of index intervals — no save/restore, no frame argument, no sibling-reuse
reasoning. That is what §11 of the tranche asked for and it is what the allocation buys.

## XIV.2 Size-based allocation

Depth-based allocation (the tranche's §5 suggestion, and Part XIII's own proposal) is not
what I built. Size-based interval allocation is simpler and strictly better:

```
codeSize (pair cf cg) = 1 + codeSize cf + codeSize cg
ambient arity         = 16 * codeSize c
self [0,16)   cf subtree [16, 16+af)   cg subtree [16+af, 16+af+ag)
```

Every block in the whole tree is pairwise disjoint *by construction*. Depth-based needs two
blocks per depth so siblings do not collide, plus an argument that a finished sibling's
subtree may be overwritten; intervals need neither. Index disequalities all reduce to
arithmetic on the three offsets `0`, `16`, `16 + af` (`amb_ne`).

## XIV.3 What is proved

Both machines are defined and both semantic closures are proved:

```lean
compilePairTM   -- 16 straight-line stages, three of them submachine calls
compileCompTM   -- 13 stages; cg runs first, its value feeds cf
pair_encodes    -- gflag * tagF * tagG, and tag * Nat.pair valF valG, are evaln
comp_encodes    -- gflag * tagG * tagF, and tag * valF,                are evaln
```

Neither uses a branch or a guard machine, and `comp` runs `cf` unconditionally even when
`cg` returned `none` — on the canonical `0`, with the `cg` tag factor discarding the
answer.

And the hard half of `pair`'s machine proof:

```lean
lemma pairPhaseA_hoareTime :
    (pairPhaseA af ag haf hag R Mf Mg).HoareTime
      (EmitPred inp₀ (regsWork R w₀ V) ys)
      (EmitPred inp₀ (regsWork R w₀ (pairPhaseAVec af ag haf hag Ff Fg V)) ys)
      (4 * evalnArithmeticCost B + tf + tg + 5)
```

Both children are fed the parent's *original* input and fuel (undecremented — checked
against the equation, Part XIII), both run in their own subtrees, the parent's block is
preserved, and the timing composes. **This is the phase that exercises nested compilation**,
at full generality in `af`, `ag`, the child machines and their specs.

## XIV.4 What is not

`pair`'s phase B (ten stages: two copies, `pairTM`, the guard, and three
clear/multiply-accumulate pairs) and all of `comp`'s thirteen. Every one of those stages is
a *single-register* operation over one ambient vector — the same shape proved twice already
in `compileSucc` (six stages) and `compileProj` (five). There is no remaining architectural
question in them; they are the per-stage plumbing tax.

## XIV.5 Status and estimate

```
Code compiler
  conventions, guard, zero/succ/left/right      ✓ Part XII
  pair/comp equations + mask formulas           ✓ Part XIII
  ambient arity, runChild, size-based blocks    ✓ this pass
  pair/comp machines + semantic closure         ✓ this pass
  pair phase A (nested invocation)              ✓ this pass
  pair phase B, comp machine proof              open — mechanical
  prec, rfind'                                  open — interface validated
PolyFueled / EfficientlyComputable → FP         open
```

| item | estimate |
| --- | ---: |
| `pair` phase B | 150–250 |
| `comp` machine proof | 200–300 |
| `compileCodeAt` assembly + structural theorem | 150–250 |
| `prec` | 400–600 |
| `rfind'` | 350–550 |
| global bound + FP transport | 400–700 |
| **Stage-2 remaining** | **1.7–2.7k over 3–5 sessions** |

Down from Part XIII's 2.0–3.1k, and for the first time the reduction is because a
*structural* risk was retired rather than because work was deferred: there is no longer any
open design question in the non-looping fragment.

---

# Part XV — Stage 2B closed: the non-looping fragment is complete (2026-08-25)

_Fifteenth pass. Scope: finish `pair` and `comp`, assemble the compiler. All three done._

## XV.0 The checkpoint, three passes deferred, is met

All six non-fuel-recursive `Nat.Partrec.Code` constructors now compile to ordinary
`complexitylib` Turing machines and are proved exactly against `evaln`:

```
zero  succ  left  right      Part XII
pair  comp                   this pass
```

under one architecture: canonical `Option` results, the universal `n < fuel` guard,
mask-based failure propagation, size-indexed disjoint register intervals, ambient-arity
subtree composition, `OutAcc` untouched, composable `HoareTime` bounds.

## XV.1 `pair`

```lean
compilePairTM := seqTM (pairPhaseA …) (pairPhaseB …)
compilePairTM_hoareTime : … (14 * evalnArithmeticCost B + tf + tg + 15)
```

Phase A (Part XIV) feeds and runs both children. Phase B is ten single-register stages plus
the nested `pairTM` call: copy each child's value into `pairTM`'s slots, pair them, compute
the outer guard, build `gflag * tagF * tagG` into the tag register and multiply it into the
value.

Phase B is stated over an *arbitrary* entry vector rather than over Phase A's output, so it
composes by instantiation instead of by threading — and would survive a change to Phase A's
allocation unchanged.

Two facts are hypotheses rather than derived, both discharged by the caller at the global
step where `codeEvalBound` supplies `B`:

* **`pairTM`'s output fits.** `Nat.pair` of two values `< B` is quadratic in them, so *no*
  single `B` is closed under it. This is not a defect of the bound discipline; it is the
  real growth of the pairing bijection, and it has to be paid for by choosing `B` at the
  top.
* **The children's tags are `0/1`.**

Everything else stays inside `B`, including through the pair window (`pairVals_lt`) — which
needs `2 ≤ B`, because `pairTM`'s `gGE` register holds `1` when its internal guard fails.

## XV.2 `comp`

```lean
compileCompTM := seqTM (compPhaseA …) (compPhaseB …)
compileCompTM_hoareTime : … (11 * evalnArithmeticCost B + tf + tg + 12)
```

Phase A is the one place a child's *input* is another child's output: `cg` runs on the
parent's input and fuel, its value register is copied into `cf`'s input register, `cf` gets
the parent's fuel — undecremented, as the equation requires — and `cf` runs. Both use
`runChild`, so the parent's block and the sibling subtree are preserved by interval
disjointness, not by framing arguments.

**`cf` runs unconditionally.** When `cg` returned `none` its value register holds the
canonical `0`, `cf` computes on that, and Phase B's mask `gflag * tagG * tagF` discards the
answer. There is no branch, no guard machine, and **no case split on `cg`'s tag anywhere in
the machine proof** — the semantic case analysis lives entirely in `comp_mask_tag` /
`comp_mask_val`, proved once in Part XIII.

Phase B is simpler than `pair`'s: with no `pairTM` there is no value growth, so no fitting
hypothesis is needed at all.

## XV.3 The compiler API

```lean
def codeRegs : Code → ℕ
  | .zero | .succ | .left | .right => 16
  | .pair cf cg | .comp cf cg | .prec cf cg => 16 + codeRegs cf + codeRegs cg
  | .rfind' cf => 16 + codeRegs cf

def compileCodeAt : (c : Code) → Regs (codeRegs c) n → Option (TM n)
```

`codeRegs` is defined **directly** rather than as `16 * codeSize c`. That matters: it makes
`codeRegs (pair cf cg)` reduce to `16 + codeRegs cf + codeRegs cg` *definitionally*, so a
recursive call needs no transport along an arity equation. With the multiplicative
definition every case of the assembly would carry a cast, and the dependent-type friction
would spread through everything downstream.

The result is an `Option`, with `none` for `prec` and `rfind'`. This is deliberate and
worth stating plainly: a placeholder machine returning canonical `none` would typecheck,
would let a full structural definition be written today, and would be **silently wrong** for
those codes — precisely the class of stub this repository's standards exist to catch.
`none` says "not compiled", never "compiles to failure".

**Not assembled:** the structural correctness theorem over `compileCodeAt` — an induction
tying the six per-constructor theorems to the definition. The case theorems stand and are
what the next pass will consume; §20 of the tranche explicitly permits leaving the
packaging.

## XV.4 What the ambient-arity architecture cost

Nothing beyond the plumbing tax. Across `pair` (16 stages) and `comp` (13), symbolic `Fin`
never became the obstacle Part XIII feared: every *local* block is a `Regs 16 n`, so all
per-stage reasoning uses `Fin 16` literals, and only the ambient vector carries the symbolic
index — manipulated by `writeWindow`, never enumerated. `fin_cases` was not needed once.

The recurring costs were the ordinary ones, and both were already in the gotcha log:
`Function.update_of_ne` direction errors, and bound side conditions needing a fact
(`0 < B`, `2 ≤ B`) that no hypothesis supplied.

## XV.5 Status and estimate

```
Code compiler
  zero, succ, left, right                       ✓ Part XII
  pair/comp equations, masks, semantic closure  ✓ Parts XIII, XIV
  ambient arity, runChild, size-based blocks    ✓ Part XIV
  pair, comp                                    ✓ this pass
  compileCodeAt API                             ✓ this pass
  structural correctness theorem                open — packaging only
  prec, rfind'                                  open — interface validated
PolyFueled / EfficientlyComputable → FP         open
```

| item | estimate |
| --- | ---: |
| structural `compileCodeAt` correctness | 150–250 |
| `prec` (fuel loop) | 400–600 |
| `rfind'` (fuel loop) | 350–550 |
| global time bound + FP transport | 400–700 |
| **Stage-2 remaining** | **1.3–2.1k over 3–4 sessions** |

Down from Part XIV's 1.7–2.7k. **The non-looping fragment is closed**; the only remaining
semantic constructors are the two fuel-recursive ones, and their interface was validated in
Part XII and has not been disturbed since.

---

# Part XVI — Stage 2C: the fuel recursion, factored (2026-08-25)

_Sixteenth pass. Scope: `prec`, `rfind'`, full structural correctness. The **pure recursion
layer** for both landed; neither machine did._

## XVI.0 The equations, read again

Both loop constructors were re-audited against Mathlib rather than from memory, and the
fuel discipline is the part worth writing down.

**`prec`**, at fuel `k+1` on input `n`:

```
guard (n ≤ k)
n.unpaired fun a n' => n'.casesOn (evaln (k+1) cf a) fun y => do
  let i ← evaln k (prec cf cg) (Nat.pair a y)
  evaln (k+1) cg (Nat.pair a (Nat.pair y i))
```

**Both children run at the parent's own fuel**, and fuel decreases *only* in the self-call.
Unrolling therefore walks the index down and the fuel down together:

```
(a, m) at fuel f   needs   (a, m-1) at fuel f-1   …   (a, 0) at fuel f-m
```

so the base case runs at fuel `f - m`, and level `j` counting *up* from the base runs at
fuel `f - m + j`. The machine must iterate **upward from the base**, and its loop bound is
the unpaired index `m`.

**`rfind'`**, at fuel `k+1`:

```
guard (n ≤ k)
n.unpaired fun a m => do
  let x ← evaln (k+1) cf (Nat.pair a m)
  if x = 0 then pure m else evaln k (rfind' cf) (Nat.pair a (m+1))
```

The self-call decreases fuel while *increasing* the index, so unrolling walks
`(f, m) → (f-1, m+1) → …` and the loop bound is the **fuel**, not the input.

**The two constructors iterate in opposite directions.** That is the single most important
fact for whoever implements them, and it is why one shared loop skeleton will not serve
both.

## XVI.1 The pure layer

```lean
def precRun  (cf cg) (a f) : ℕ → Option ℕ        -- structural on the index
def rfindRun (cf)    (a)   : ℕ → ℕ → Option ℕ    -- structural on the fuel

precRun_eq       : precRun cf cg a f j = evaln (f + j) (cf.prec cg) (Nat.pair a j)
precRun_eq_evaln : m ≤ fuel → precRun cf cg a (fuel - m) m
                     = evaln fuel (cf.prec cg) (Nat.pair a m)
rfindRun_eq      : rfindRun cf a f m = evaln f cf.rfind' (Nat.pair a m)
rfindRun_succ    : one step, in the form a loop invariant consumes
```

Neither iterator recurses on `Code` — both are plain structural recursions on a numeral.
That is what makes them implementable as bounded `forRegTM` loops whose *bodies* invoke the
compiled structurally-smaller children, and it re-confirms (now against the equations
rather than by argument) that `compileCodeAt` stays a structural recursion on `Code`.

`precRun_eq_evaln` is the theorem the machine's loop will close against: `m` iterations
from base fuel `fuel - m` compute the answer at fuel `fuel`. Its `m ≤ fuel` side condition
is free — when it fails the outer guard `Nat.pair a m < fuel` fails too, and the result is
canonical `none` regardless.

## XVI.2 Why the machines did not land, and a corrected estimate

I under-estimated `prec` badly in Parts XII–XV, and working through its register
requirements for the first time is what corrected it. Per loop iteration the body must:

* advance the level fuel and the index;
* build `Nat.pair j v` — a `pairTM` call;
* build `Nat.pair a (that)` — a second `pairTM` call;
* copy that and the level fuel into `cg`'s block, and run `cg`;
* build `Nat.pair a (j+1)` for that level's guard — a third `pairTM` call;
* compute the guard and fold three factors into the `alive` mask, then mask the value.

That is roughly twenty stages *inside the loop body*, three of them nested submachine
calls, under a six-component loop invariant — before the setup (unpair, `fuel - m`, run
`cf`, initialise) and the final masking. `prec` is closer to 800 lines than the 400–600 I
had been carrying, and `rfind'` to 500–600.

| item | estimate |
| --- | ---: |
| `prec` machine + semantic closure | 700–900 |
| `rfind'` machine + semantic closure | 500–700 |
| structural `compileCodeAt` correctness | 250–350 |
| global runtime bound + FP transport | 400–700 |
| **Stage-2 remaining** | **1.9–2.7k over 4–5 sessions** |

**This is up from Part XV's 1.3–2.1k.** I have now revised this estimate down twice and up
once; the honest reading is that the earlier reductions were partly real (retired design
risk) and partly optimism about work I had not yet costed. The loop constructors are the
largest single items left in Stage 2, and `prec` alone is comparable to `pair` and `comp`
combined.

## XVI.3 Status

```
Code compiler
  zero, succ, left, right, pair, comp        ✓ Parts XII–XV
  compileCodeAt API                          ✓ Part XV
  prec/rfind' exact equations + pure iterators ✓ this pass
  prec machine, rfind' machine               open
  structural correctness theorem             open
PolyFueled / EfficientlyComputable → FP      open
```

Nothing in the architecture moved: the result encoding, ambient arity, size-based
allocation, `runChild`, mask discipline and fuel convention are all as frozen in Part XV,
and the pure layer confirms rather than strains them.

---

# Part XVII — Stage 2C1: `prec`'s semantics and body (2026-08-25)

_Seventeenth pass. Scope: `Code.prec` only. The semantic layer, register layout and loop
body landed; the body Hoare proof, loop, setup and closure did not._

## XVII.0 The level guards are free

The pass's one real discovery, and it shrinks the machine before it is written.

`precRun` re-checks `Nat.pair a j < f + j` at every level. **The machine does not have to.**
`Nat.pair a ·` is strictly increasing, so the index grows by at least `1` per level while
the level fuel grows by exactly `1`:

```lean
pair_lt_pair_succ : Nat.pair a b < Nat.pair a (b + 1)
pair_add_le       : j ≤ m → Nat.pair a j + (m - j) ≤ Nat.pair a m
level_guard       : j ≤ m → Nat.pair a m < f + m → Nat.pair a j < f + j
```

So the outer guard at level `m` implies every level guard beneath it, and the loop body
needs **no guard test at all** — removing one `pairTM` call and one `ltFlagTM` comparison
per iteration, roughly twenty stages down to sixteen.

Two smaller simplifications fell out:

* the `m ≤ fuel` side condition of `precRun_eq_evaln` is *implied* by the outer guard,
  since `m ≤ Nat.pair a m` — so the finish phase has only the standard `input < fuel` test;
* `evaln_eq_none_of_not_guard`, proved from Mathlib's `evaln_bound` and stated for **any**
  code, handles the failing-guard branch uniformly.

## XVII.1 The step is `comp`'s shape

```lean
precRunG_succ_tag : resultTag (precRunG cf cg a f (j+1))
  = resultTag (precRunG cf cg a f j)
      * resultTag (evaln (f + (j+1)) cg (Nat.pair a (Nat.pair j (resultVal (precRunG … j)))))
precRunG_succ_val : … * resultVal (…)
```

The previous level's result is bound into a child's input — exactly `comp`. So the same
masking argument applies: `cg` runs unconditionally on `resultVal` of the previous level,
which is the canonical `0` when that level failed, and the `alive` factor discards the
answer. **No branch, no early termination, fixed loop length.**

Checked against the definition: **`cf` appears only in the base case.** It is setup-only,
and the loop body invokes `cg` alone — which is worth stating, because the natural guess is
that a primitive-recursion loop calls both children per iteration.

## XVII.2 Layout and body

`prec` needs more than sixteen registers of its own, so its node block is **thirty-two**
wide. The first four keep the standard interface, so a parent reads a `prec` child exactly
like any other constructor.

```
0–5  interface + outer guard      6 a   7 m (loop counter)   8 baseFuel
9 j  10 alive  11 acc  12 curFuel   13–15 temps   16–24 pair/unpair window
```

The loop counter sits in the node's own block, outside every child subtree, so `forRegTM`
never touches a child window.

`precBodyTM` is sixteen stages: two `pairTM` calls (building `Nat.pair j acc` then
`Nat.pair a (that)`), advancing `j` and `curFuel`, a `runChild` on `cg`, and the two mask
updates. `precBodyVals` is the vector it produces; `precLoopVals` is its `j`-fold iterate.

## XVII.3 What is not proved

`precBody_hoareTime`, and everything after it: the loop, setup, finish and closure.

Stages 1–3 of the body proof were probed and elaborate cleanly, which is the part that
carried risk — it exercises the `runChild`-on-`pairTM` idiom (a submachine window *inside*
the node's own block rather than in a child subtree) and the bound threading through a
`pairTM` output. The remaining thirteen stages are patterns already proved in `pair`'s and
`comp`'s phase proofs.

## XVII.4 Estimate

| item | estimate |
| --- | ---: |
| `precBody_hoareTime` (13 stages remain) | 200–250 |
| `prec` loop (`forRegTM` + semantic invariant) | 200–300 |
| `prec` setup (unpair, `baseFuel`, base child, init) | 250–300 |
| `prec` finish + closure | 150–200 |
| `rfind'` (machine + closure) | 500–700 |
| structural `compileCodeAt` correctness | 250–350 |
| global runtime bound + FP transport | 400–700 |
| **Stage-2 remaining** | **1.9–2.8k over 4–6 sessions** |

Essentially flat against Part XVI's 1.9–2.7k. The guard elimination genuinely removed work
from the body, and the semantic layer is done; that was offset by this pass not reaching
the machine proofs.

`prec` remains the single largest item. Its own four phases are ~800–1050 lines — comparable
to `pair` and `comp` combined, which took a full session each.

---

# Part XVIII — Stage 2C: `prec` and `rfind'` compiled; the compiler is total (2026-08-25)

_Eighteenth pass. Scope: finish `prec`, build `rfind'` end to end, and close
`compileCodeAt` over all eight constructors. Everything below is green with no `sorry`._

## XVIII.0 The loop counter must live outside the block

The one structural discovery, and it is what unblocked both remaining constructors.

`forRegTM`'s Hoare rule specifies its body against the loop register's *mid-iteration
cursor* tape `⟨i+2, regCells v⟩`, not a `regTape`. A `regsWork R w₀ V` state cannot carry
that: `regsWork` writes a `regTape` at every register `R` names. So a body written over the
same block as its own counter cannot be specified at all in this idiom.

The fix is in complexitylib already, and its docstring says so:

```
regsWork_update_of_ne : (∀ k, r k ≠ i) →
  regsWork r (Function.update w₀ i t) v = Function.update (regsWork r w₀ v) i t
  -- "what lets a machine over `r` run inside a loop whose counter lives in a register
  --  `r` does not name"
```

So the counter goes **outside** the block, and the body's obligation becomes its ordinary
`regsWork` specification with the ambient family adjusted. That is `forRegs_hoareTime`, a
generic register-block loop rule (a candidate for upstreaming). It costs one extra register
per looping node: `codeRegs (prec cf cg) = 33 + …`, `codeRegs (rfind' cf) = 33 + …`, with
the thirty-third addressed by `precLoopIdx` / `rfLoopIdx` and the working block by
`precMain` / `rfMain`. `regsWork_precMain` / `regsWork_rfMain` bridge the parent's
thirty-three-wide view and the node's thirty-two-wide working view.

Putting the counter at the *end* is what makes the bridge cheap: the working block is
`shiftEmb 0`, so every existing index lemma is reused verbatim, with no re-indexing of the
sixteen-stage body proof.

## XVIII.1 `prec`, complete

`precBody_hoareTime` (sixteen stages), then the loop, setup, finish and assembly:

* `precLoop_hoareTime` — `m` iterations off the outside counter, with the per-level side
  conditions bundled as `PrecBodyOK`;
* `precSetup_hoareTime` — unpair, `baseFuel := fuel - m`, run `cf`, seed `j`, `alive`,
  `acc`, `curFuel`, copy `m` to the counter (twelve stages), with `precSetupVals_lt`;
* `precFinish_hoareTime` — the outer guard and two masks, one level shorter than `comp`'s
  because `alive` has already absorbed `cf`'s tag and every level's;
* `precTM_hoareTime` — the three composed.

## XVIII.2 `rfind'`

The level guards here are **not** free, unlike `prec`: `Nat.pair a (m+t)` grows while the
level fuel `k+1-t` shrinks, so a guard can fail part-way down and the machine must test it.

The semantic layer is `rfLevel` / `rfIter`, and `rfIter_spec` says running the loop for
exactly `fuel` levels computes `evaln fuel (rfind' cf)` in both components, with the
incoming `searching` flag multiplying the whole answer:

```lean
(rfIter cf a (s, fo, r) f m f).2.1 = fo + s * resultTag (evaln f cf.rfind' (Nat.pair a m))
(rfIter cf a (s, fo, r) f m f).2.2 = r  + s * resultVal (evaln f cf.rfind' (Nat.pair a m))
```

Three registers carry the search — `searching`, `found`, `result` — and the guard, the
child's tag and the zero test all enter multiplicatively, so there is still no branch and
the loop has fixed length `fuel`. The body is twenty-three stages, split
`rfPhaseA` (7) / `rfPhaseB1` (7) / `rfPhaseB2` (9); the split is not cosmetic — the
monolithic sixteen-plus-stage proof timed out at four million heartbeats.

## XVIII.3 A tactic that paid for itself

```lean
lemma rfSelf_update_apply (i j : Fin 32) (X x) :
    Function.update X (rfSelf af j) x (rfSelf af i)
      = if (i : ℕ) = (j : ℕ) then x else X (rfSelf af i)
```

Reading a node register out of an update to a node register becomes a *numeric* test, so
`simp only [thisVals, rfSelf_update_apply, rfLoc_update_apply]` followed by `norm_num`
evaluates an entire stage chain automatically. Before this, each read-off was a hand-ordered
`rw` chain of eight `Function.update_of_ne`s that broke whenever the unfolding order
changed. `prec`'s read-offs should be migrated to it.

## XVIII.4 The compiler is total

`compileCodeAt` now returns `some` on all eight constructors, and
`compileCodeAt_isSome` proves it by structural induction. No self-interpreter, no call
stack: the recursion is on the `Code` term, and parent and every descendant inhabit the
same `TM n`, differing only in which registers they name.

## XVIII.5 What is not proved

The **semantic** tie-up. Every phase specification is parametric in the child's semantics
`Ff` / `Fg`; nothing yet instantiates those with `evaln`. Concretely:

* a uniform `codeVals c` and the structural correctness induction (`EncodesEvaln`);
* discharging `PrecBodyOK` and `RfBodyOK` at every loop state, which needs the global size
  bound `B` from `codeEvalBound` — so Stage C and Stage D are entangled and should land
  together;
* the runtime bound and the `Complexity.FP` transport.

## XVIII.6 Estimate

| item | estimate |
| --- | ---: |
| `codeVals` + structural correctness + loop invariants | 600–900 |
| global runtime bound + FP transport | 400–700 |
| **Stage-2 remaining** | **1.0–1.6k over 2–3 sessions** |

Down from Part XVII's 1.9–2.8k: the machine layer is finished, and what is left is
semantics and arithmetic rather than register bookkeeping.

---

# Part XIX — Stage 2C: the semantic layer begins (2026-08-25)

_Same session as Part XVIII, after the machine layer closed. Scope: the vocabulary the
structural correctness induction will be stated in._

## XIX.1 `codeVals`

`codeVals c` mirrors `compileCodeAt c` clause for clause: each constructor's own phase
vector with the children's `codeVals` substituted for the abstract child semantics the
phase specifications are parametric in. For `prec` and `rfind'` the clause writes the
thirty-two-wide working block back through `precMain` / `rfMain` and sets the loop counter
separately, since those nodes are thirty-three wide.

`codeLocal c : Fin 16 ↪ Fin (codeRegs c)` is the node's own interface block, uniformly at
offset `0` — the same for all eight constructors, which is what lets `EncodesEvaln` be
stated once.

## XIX.2 The read-off toolkit

Reading one named register out of an update to another is a *numeric* index test:

```lean
selfW_update_apply (i j : Fin 16) :
  Function.update X (selfW af ag j) x (selfW af ag i)
    = if (i : ℕ) = (j : ℕ) then x else X (selfW af ag i)
pairVals_apply     -- `pairTM`'s output vector, index test numeric
pairWin_selfW_apply -- the pairing window as a total read-off, slots 6–13
```

so `simp only [thisVals, …_update_apply, …]; norm_num` evaluates an entire stage chain.
The `Fin.mk`-shaped indices that come out of window lemmas are exactly why the *numeric*
form matters: a `Fin`-literal simp lemma does not fire on `⟨6, _⟩`.

With that, `pair` and `comp` have their full semantic read-offs — what each child sees
(`pairLeftIn` / `pairRightIn`, `compRightIn` / `compLeftIn`, with their interface entries
identified) and what the node leaves (`…PhaseBVec_tag` / `_val`, each exactly the shape
`pair_encodes` / `comp_encodes` consume).

## XIX.3 What is not proved

`codeVals_encodes`. For `pair` and `comp` every ingredient is now in place; for `prec` and
`rfind'` the missing piece is the **loop invariant** — that the machine's loop state after
`i` iterations is `precRunG` / `rfIter` at level `i`. That cannot be proved standalone: the
level-`i` statement mentions the child's answer on the level-`i` input, so it needs the
structural induction hypothesis and must be proved inside it. The same induction needs the
global size bound `B` to discharge `PrecBodyOK` / `RfBodyOK` at every level, so Stage C and
Stage D stay entangled.

---

# Part XX — `prec` and `rfind'` are finished (2026-08-25)

_Twentieth pass. Scope: the semantic completion of the two looping constructors. Their
machines and Hoare specifications landed in Part XVIII; what was missing was the tie from
the register vectors to `evaln`, and that is what this pass proves._

## XX.1 The shape that makes it self-contained

The obstacle recorded at the end of Part XIX was that a loop invariant "mentions the
child's answer on the level-`i` input, so it needs the structural induction hypothesis."
That is true, but the hypothesis can be *named* rather than waited for:

```lean
def ChildEncodes (m : ℕ) (hm : 16 ≤ m) (c : Nat.Partrec.Code)
    (F : (Fin m → ℕ) → Fin m → ℕ) : Prop :=
  ∀ u, F u ⟨2, _⟩ = resultTag (evaln (u ⟨1, _⟩) c (u ⟨0, _⟩)) ∧
       F u ⟨3, _⟩ = resultVal (evaln (u ⟨1, _⟩) c (u ⟨0, _⟩))
```

This is exactly what the structural induction will supply for a child, and taking it as a
hypothesis makes both constructors provable now, standalone. It also decouples the
semantic layer from the size bound `B` entirely: `precVals` and `rfindVals` are pure
functions of register vectors, so their correctness needs no bound at all. Only the
*timing* theorems need `B`. Part XIX's "Stage C and Stage D stay entangled" was too
pessimistic — the entanglement is only in the runtime half.

## XX.2 `rfind'`

```lean
lemma rfindVals_encodes (haf) (cf) (Ff) (hFf : ChildEncodes af haf cf Ff) (V) :
    rfindVals af haf Ff V (rfSelf af 2) = resultTag (evaln (V (rfSelf af 1)) cf.rfind' (V (rfSelf af 0))) ∧
    rfindVals af haf Ff V (rfSelf af 3) = resultVal (evaln (V (rfSelf af 1)) cf.rfind' (V (rfSelf af 0)))
```

Three steps: `rfBodyVals_isLevel` (the machine's level **is** `rfLevel`), `rfLoopVals_spec`
(the state after `i` levels is `rfIter` at `i`, by induction on `i`), then `rfIter_spec`
from Part XVIII turns `fuel` levels into `evaln fuel (rfind' cf)`. The outer guard needs no
separate treatment: it is level `0`'s own guard, already inside the loop.

One lemma was needed that the pure layer did not have — `rfIter_succ'`, the iterate
unfolded from the *right*, since the machine's induction adds a level at the end while
`rfIter`'s definition peels one off the front.

## XX.3 `prec`

```lean
lemma precVals_encodes (haf) (hag) (cf cg) (Ff) (Fg)
    (hFf : ChildEncodes af haf cf Ff) (hFg : ChildEncodes ag hag cg Fg) (V) : …
```

Same three steps — `precBodyVals_isLevel`, `precLoopVals_spec`, then `precRunG_eq_evaln` —
plus one thing `rfind'` did not need: the **outer guard is separate** here, because
`precRunG_eq_evaln` presupposes it. So the finish splits on `V 0 < V 1`, with
`evaln_eq_none_of_not_guard` covering the failing branch, and the two sides meet because
the guard flag multiplies the answer in exactly the way the mask identities predict.

The base case is `cf`, run in the setup at fuel `fuel - m` on `a` — which is `precRunG`'s
own base case, so the invariant's `i = 0` case is `hFf` applied to `precBaseIn`.

## XX.4 Two refactors this needed

Both constructors' vector definitions were split at the point where the child runs, so the
child's input vector is nameable:

* `rfPhaseAPair` / `rfPhaseAPre` — the level's `Nat.pair a m`, then the state handed to `cf`;
* `precBodyPre` — the state handed to `cg` (input, level fuel, counter already advanced);
* `precSetupPre` — the state handed to `cf` in the setup.

The splits are definitional, so every Hoare proof kept working untouched. Without them the
read-off lemmas have to quote thirty-line update chains in their statements, which is how
the first attempt at `rfPhaseAVals_guard_val` went — and it was unmaintainable on sight.

The second refactor is the numeric-index read-off mechanism from Part XIX, extended to
`prec`'s layout (`precSelf_update_apply`, `precPairWin_selfW_apply`,
`precUnpairWin_selfW_apply`, and the `leftLoc`/`rightLoc` pairs). It is what makes a
sixteen-stage read-off a two-line `simp only` + `norm_num`.

## XX.5 What is left

`codeVals_encodes` — the structural induction that discharges `ChildEncodes` for each
child. All eight constructors now have their per-node semantic lemma or (for the four base
constructors) had one already; the induction is the glue. After that, Stage D's runtime
bound and Stage E's `Complexity.FP` transport.

---

# Part XXI — The compiler is correct (2026-08-25)

_Stage 2, item 3. `codeVals_encodes`: for every `c : Nat.Partrec.Code`, the compiled
register vector holds the canonical encoding of `evaln` in the node's tag and value
registers._

```lean
lemma codeVals_encodes : ∀ c : Nat.Partrec.Code,
    ChildEncodes (codeRegs c) (codeRegs_ge c) c (codeVals c)
```

The induction is thin, because Part XX put every constructor's semantics behind a
`ChildEncodes` hypothesis: each case applies that constructor's own lemma to the two
induction hypotheses. `pair` and `comp` needed their assembled lemmas
(`pairVals_encodes`, `compVals_encodes`) — the read-offs from Part XIX plus the
`pair_encodes` / `comp_encodes` mask identities.

## XXI.1 The one friction: index forms

A node's interface registers sit at offset `0` of its block in every layout, so for six of
the eight constructors `⟨2, _⟩` and `selfW … 2` are *definitionally* equal and the case is
`exact`. The two looping constructors are not: their block is thirty-three wide, the
vector is written back through `precMain` / `rfMain`, and neither `writeWindow` (a `dif`
on `∃ j, shift j = k`) nor `Function.update` (a `Decidable` equality on a symbolic `Fin`)
reduces. So those reads need real rewriting — and `rw` then fails on the arity, because
`codeRegs (cf.prec cg)` and `33 + codeRegs cf + codeRegs cg` are defeq but not
syntactically equal, and unification at `instances` transparency will not bridge them.

The fix is to name the block vector — `precBlockVals` / `rfBlockVals`, stated over
variables `af ag`, with `codeRegs` nowhere in sight — and prove the read-off there
(`precBlockVals_self`, `rfBlockVals_self`). The main proof then reaches it with a `show`,
which *does* accept a definitional change. This is the third time in this development that
naming an intermediate has been the difference between a two-line proof and an
unmaintainable one.

## XXI.2 Where Stage 2 stands

Items 1–3 of the five are done: `prec`, `rfind'`, and the compiler's structural
correctness. Items 4 (concrete polynomial runtime) and 5 (the `Complexity.FP` transport)
remain, and they are larger than the machine work was. See Part XXII for the sizing.

---

# Part XXII — Stage 2 item 4: the register bound, and a hypothesis that cannot be discharged (2026-08-25)

## XXII.1 The bound

`codeEvalBound` bounds a *successful call's returned value*. The compiled machine needs
more, because two registers exceed any node's own answer by construction:

* `prec`'s body forms `Nat.pair a (Nat.pair j acc)` before invoking `cg`, while
  `codeEvalBound (prec cf cg) k` is only `max (codeEvalBound cf k) (codeEvalBound cg k)`;
* `rfind'`'s body forms `Nat.pair a m` with `m` advancing one per level, so `m` reaches
  `m₀ + fuel` — past the input.

`codeRegBound c s` (`Framework/Machine/EvalnRegBound.lean`) is the machine's own bound,
with `s` a common bound on the node's input and fuel registers. Every pair the machine
forms appears in the definition, so nothing here assumes an arbitrary bound is closed under
`Nat.pair`. It is monotone (`codeRegBound_mono`) and polynomial per fixed code
(`codeRegBound_poly`), and both loops are shown to stay inside it:

```lean
precLoopVals_ok : ∀ i ≤ m, PrecBodyOK af ag B (precLoopVals … i)
rfLoopVals_ok   : ∀ i ≤ fuel, RfBodyOK af B haf (rfLoopVals … i)
```

Those rest on two new pure facts — `precRunG_val_le` (a level's accumulator is one of the
children's answers at a fuel the level bounds) and `rfIter_ok` (`searching` and `found` are
mutually exclusive flags and `result` never passes the current index, because the single
level that writes `result` is the one that clears `searching`).

One re-entrancy fix landed with it: `precSetup_hoareTime` / `rfSetup_hoareTime` assumed the
loop counter *starts at zero*. A looping child is re-invoked once per level of its parent's
loop, and after the first level its counter still holds the previous `m`. The hypothesis is
now "holds some value `≤ B`", which is what re-entrancy actually needs.

## XXII.2 The blocker: `hFfB` is not satisfiable

Every composite Hoare theorem carries

```lean
(hFfB : ∀ u : Fin af → ℕ, (∀ k, u k < B) → ∀ k, Ff u k < B)
```

and the structural timing induction must discharge it at `Ff := codeVals cf`. **It cannot
be.** Take `cf = pair succ succ` and any `B ≥ 3`; choose `u 0 = B - 2`, `u 1 = B - 1`, all
other components `0`. Then `∀ k, u k < B`, but by `codeVals_encodes` the value register is

```
resultVal (evaln (B-1) (pair succ succ) (B-2)) = Nat.pair (B-1) (B-1) = (B-1)² + (B-1) ≥ B.
```

So the hypothesis is false for that `Ff` at *every* usable `B`. Nothing already proved is
wrong — the theorems are true conditionally — but they are stated in a form the induction
cannot feed.

The cause is that `hFfB` quantifies over *all* bounded child vectors, whereas the machine
only ever runs a child on **one** vector: the one the parent's phase A writes, whose input
and fuel registers are the parent's own. The same over-quantification appears in `hMf` /
`hMg`, and it comes from `runChild`, whose hypothesis is `∀ Wb u, … → (∀ k, u k < B) → …`
even though it instantiates `u` at a single value.

**The fix** is specialization, not weakening: give `runChild` a variant whose hypothesis is
the single instance it uses (generic, and a candidate for upstreaming), then restate the six
composite theorems' child hypotheses at `pairLeftIn` / `pairRightIn` / `compRightIn` /
`compLeftIn` / `precChildIn` / `precBaseIn` / `rfChildIn` — the vectors Part XIX–XX already
name. The theorems get *stronger* (fewer hypotheses to satisfy) and become usable by the
induction.

This is why item 4 is larger than the goal's framing suggests: it is not plumbing on top of
the existing timing theorems, it is a restatement of them.

---

# Part XXIII — Stage 2 is closed (2026-08-25)

_Seventh pass. Scope: items 4 and 5 of the Stage-2 work order — the concrete polynomial
runtime, and the `Complexity.FP` transport. Stage 3 untouched, as instructed._

**Stage 2 is closed.** `LogicalInduction/Framework/MachineEfficiency.lean`:

```lean
theorem EfficientlyComputable.toMachine {Tr : Trader} (h : EfficientlyComputable Tr) :
    MachineEfficientTrader Tr
```

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`), no `sorry` anywhere on the
chain, full build and all gates green.

## XXIII.1 Item 4: the register bound and the timing theorem

Part XXII's blocker was discharged as it predicted: `runChildFixed` replaces `runChild`'s
over-quantified child hypothesis with the single instance the machine actually uses, and the
six composite theorems were restated at the vectors the semantic layer already names. With
that, three things landed in `EvalnRegBound.lean`:

* `codeRegBound c s` — a bound on **every** register a compiled node holds, not just its
  answer. It carries each `Nat.pair` the machine forms explicitly (`precWindowBound`,
  `rfWindowBound`), because no useful `B` is closed under pairing; `codeVals_lt` proves the
  compiled vector stays inside it, for all eight constructors.
* `codeMachineTime c s A` — the step bound, mirroring each constructor's Hoare bound with
  the size parameter `s` standing in for the two data-dependent level counts (the `prec`
  counter is bounded by the input, the `rfind'` counter by the fuel). Monotone in both
  arguments; `codeMachineTime_arith_poly` makes it polynomial in `s` for each fixed code.
* `compiledTM_hoareTime` — the structural theorem: the compiled machine meets that bound,
  at the real arithmetic cost `evalnArithmeticCost (codeRegBound c s)`.

Two loop invariants had to be restated *conditionally* (`∀ u, bounded → input ≤ s' →
fuel ≤ s' → …`) rather than per-level: in per-level form the caller must know the level's
bound before it can supply the hypothesis that proves it, which is circular. The
conditional form is both satisfiable and non-circular, with the per-level instance derived
inside the induction from what it has already established.

One friction worth recording. `rw` matches at `instances` transparency, so it will not see
through `codeRegs (cf.prec cg)` to `33 + codeRegs cf + codeRegs cg`; the two looping
constructors' assembly therefore lives in its own lemma, phrased in the `33 + af + ag`
world the loop counter inhabits, and the induction reaches it by `exact` (which does check
definitional equality). That is `precBlock_hoareTime` / `rfBlock_hoareTime`.

## XXIII.2 Item 5: the trader machine

The transport needed an actual machine, built in the fork's register calculus.
`TraderMachine.lean` is ~1,100 lines in four layers.

**Register operations as vector updates.** Each fork register machine restated over a
`regsWork` state as a `Function.update` of the value vector under the common arithmetic
budget. A stage of a straight-line register program is then one line, and the whole
development is a chain of `set`s with a `funext` at the end. This is what made the rest
tractable; without it each stage costs five lines of `regsWork_update` plumbing.

**Guarded emission.** The fork's `guardTM` rule keeps the output accumulator fixed.
`guardEmit_hoareTime` is the emitting counterpart: a `{0,1}` register decides whether a
fixed word is appended. That single rule is how a *data-dependent* bit stream is built out
of fixed-word emitters — no branching, in keeping with the frozen architecture.
`runChildFixed` and `forRegs_hoareTime` were generalized the same way, to let the
accumulator grow across a child call and across a loop level.

**The digit block.** Ten registers turn a token value into three bits. The token values are
arbitrary naturals and do not fit in three bits — they do not have to: `undigitizeStep`
tests a digit only against `4`, so every value from `4` up is the same block terminator, and
`undigitize_map_min_four` (in `DigitBits.lean`) says clamping at `4` leaves the token
stream, hence the trader, alone. So the block computes `min d 4` by `a - (a - b)`, derives
five equality flags from four comparisons and four differences, and fires exactly one of
five guarded three-bit emitters.

**The machine.** Thirty-two working registers, then the length program's block, then the
token program's; the loop counter sits one register beyond all of them, because `forRegTM`
consumes its counter and `forRegs_hoareTime` needs it outside the block. The setup measures
the day with `inputLenRegTM`, evaluates the clock polynomial with `polyEvalTM`, runs the
length program, and derives the digit count as the tag masking the length clamped to the
clock — the mask is what makes the `none` case emit nothing without a branch. Each
iteration pairs the day with the index, runs the token program, and emits one clamped
digit.

**Polynomiality.** Every budget in sight is loose on purpose: `FP` quantifies the degree
existentially. The size parameter is `Nat.pair N C + C` — it dominates the day, the clock,
and every paired index the loop forms — and the register bound is a polynomial in it. The
one place this needed care is `polyEvalTM`'s Horner-prefix obligation, which is not implied
by the polynomial's value at the point: the prefixes are bounded by
`hornerFold_take_le`, and `hornerCap` carries that bound into the register bound.

`mem_FP_iff_computesInTime_polynomial` then turns the `IsPolyBounded` step bound into `FP`
membership directly, without touching the `=O` layer.

## XXIII.3 What this settles, and what it does not

It settles the **inclusion**: nothing certified in the fuel model is outside the machine
model. Every exploiting trader the property tail constructs is thereby a genuine
machine-polynomial-time trader — the direction the property tail consumes.

It settles nothing about the converse, and per `notes/boundary-efficiency-model.md`
("What the deliverable must NOT say") it licenses **no** model-card edit and **no** strength
upgrade. `thm:li` is still stated over `EfficientlyComputable`; `dd:fuel`'s
lower-calibration item is still open; the disclosure in `LogicalInduction/README.md` stands
as written. What changed is the staging language in
`Construction/Machine.lean` and `Construction/MachineTraderEnumeration.lean`, which said the
inclusion was "not started".

## XXIII.4 What Stage 3 now needs

Unchanged from §V.4 and §V.6, minus the dependency that blocked it:

| item | LOC | note |
| --- | ---: | --- |
| Stage 3 soundness (clocked simulator, §V.3) | 0.6–1.2k | independent of this pass |
| Stage 3 `TradingFirm` migration (§V.4) | 0.3–0.6k | was blocked on Stage 2; now unblocked |
| `LIACompiler` swap + property touch-ups | 0.2–0.4k | follows the migration |

With the transport in hand, route (a) of §V.4 is the clean one: `enumeratedTrader_ec` can be
restated at the machine class and the fuel branch retired, rather than the two coexisting.

---

# Part XXIV — Stage 3 is closed: the machine class is canonical (2026-08-25)

_Eighth pass. Scope: enumeration soundness, the canonical-enumeration migration, the
effective construction, and the criterion. Stage 2 untouched._

**Stage 3 is closed.** The Logical Induction construction now enumerates ordinary
machine-polynomial-time traders, end to end, and the paper-facing capstone is stated at that
class:

```lean
theorem LIA_isMachineLogicalInductor (DP) (hDP : ComputableDeductiveProcess DP) :
    IsMachineLogicalInductor (liaHistory DP) DP

theorem exists_machine_logical_inductor (DP) (hDP) :
    ∃ P : History, IsMachineLogicalInductor P DP
```

Axiom-clean, no `sorry`, full build and all gates green.

## XXIV.1 Soundness: the missing half

§V.3 diagnosed the missing theorem and priced it at 0.6–1.2k lines through
`UTM.ClockedUtm`. The route taken is different and cheaper, and the reason is worth
recording: **an index names a *fixed* description**, so no interpreter is needed. The
simulator's control states are the described machine's own states, and one of its
transitions performs one transition of the described machine while advancing a unary clock
head by one cell:

```lean
def simδ ... | Sum.inl q =>
  if wHeads 1 ≠ Γ.one then timeout
  else if q = (d.toTM).qhalt then halt
  else let r := (d.toTM).δ q iHead (fun _ => wHeads 0) oHead; ...
```

Three phases, in `Machine/ClockedSim.lean`: a `pre` transition that walks the shared heads
back to cell 0 (the combinators deliver tapes parked at cell 1, and the described machine's
first transition is the one that reads `▷` — this is where that offset is paid back); the
simulation; and a `rewind`/`wipe` pair that blanks output cell 1 on timeout, which is all
`HasOutput []` asks for.

Two details decided the design:

* **The clock check comes before the halt check.** `runUntilHalt` reports a halt only when
  the budget *strictly* exceeds the running time — `stepFrozen` spends one iteration
  noticing that `codedStep` returned `none` — so a machine halting exactly at step `V` must
  read as a timeout. Checking the clock first makes the simulator agree with the evaluator
  at every index, including that boundary. `runUntilHalt_spec` and `evalHalted_spec` were
  strengthened from `s ≤ t` to `s < t` to say what the evaluator actually delivers.
* **The scratch tapes must be parked, the simulated ones need not be.** The simulation step
  needs only the clock and scratch reads; the input, work and output tapes are handled by
  the described machine's own transition. The phase transitions idle them, so they arrive
  transformed by `transitionInput`/`transitionTape` — identities on their cells, which is
  all the output invariants need.

`Complexity.mem_FP_iff_computesInTime_polynomial` then turns the step bound into `FP`
membership directly: the bound is assembled as an actual `Polynomial ℕ`
(`clockedTimePoly`), so no `=O` reasoning is needed anywhere.

## XXIV.2 The migration

`enumeratedTrader` **is** the finite-description enumeration. The fuel emulator that used to
carry that name is deleted: coverage now comes from `EfficientlyComputable.toMachine`
composed with `exists_enumeratedTrader_eq`, so nothing needed it. `TraderEnumeration.lean`
is gone; `LIACompiler`'s dead `traderProgram*_prim`/`clockedTokens_prim`/`codeAt_prim`
helpers went with it.

`TradingFirm`'s ~1000-line analytic argument was not touched — it is enumeration-agnostic
except for its coverage input, exactly as designed, and the migration was one hypothesis on
`trading_firm_dominance`. The main `LogicalInduction` library now depends on `complexitylib`,
which is the point.

**The effective construction moved with it.** `LIACompiler.enumeratedTraderTrades_prim` is
reproved on `MachineExec.primrec_machineTokens`, so the LIA compiler runs the same budgeted
execution the soundness proof reasons about. There is one simulator all the way down; no
old-enumeration/new-enumeration split survives.

## XXIV.3 The criterion, and what it cost

Forcing `IsLogicalInductor.noExploit` to the machine class in place does not work, and the
reason is structural rather than incidental. For a theorem of the shape `LI(P) → property(P)`
the bridge machine-LI ⟹ fuel-LI is enough, and every property-tail theorem transfers
untouched. For a *closure* theorem — `LI(P) → LI(P')` — it is not, because the proof
transports an arbitrary trader backwards across the market change and certifies the
transported trader. Those certificates (`ConditioningTraderCompiler.translate_ec`,
`EfficientPrefixPatch.preserves_ec`) live in the fuel calculus, and `thm:scon`'s are
*inhabited*. Restating those at the machine class would have replaced proved content with
unproved hypotheses.

So the architecture is two-level, with the machine reading primary:

```text
IsMachineLogicalInductor   def:lic at the paper's quantifier   ← the construction proves this
        │ instance, via EfficientlyComputable.toMachine
        ▼
IsLogicalInductor          fuel-class compatibility predicate  ← the property tail consumes this
```

Nothing is weakened: `LIA_is_logical_inductor` is now *derived* from the machine capstone,
and `exists_computable_beliefSequence_logical_inductor` — the paper's main theorem in full
belief-sequence form — carries the machine conjunct.

What remains is two specific machine-class *transport* theorems, neither of which is a
converse inclusion:

| wanted | shape |
| --- | --- |
| machine `thm:scon` | `MachineEfficientTrader Tr → MachineEfficientTrader (conditioning translation of Tr)` |
| machine corrected `thm:ifp` | the same for a finite-*support* perturbation |

Each asks for `Complexity.FP` closure under a specific transformation of the strategy
serialization — an `FP`-level parser and emitter, on the scale of Stage 2 item 5. The
unrestricted finite-day `thm:ifp` is *not* on that list: it is separately under revision as
overgeneral (arbitrary finite-day perturbations can encode unbounded computational advice),
and its intended endpoint is a corrected finite-support theorem plus a formal counterexample
to the published statement, not a machine-strength restoration of it.

## XXIV.4 Where the efficiency model lives now

`Framework/Machine/` and `Framework/MachineEfficiency.lean`. The compiler chain defines the
paper's reading of `def:ec`, so it belongs beside `EfficientlyComputable` rather than in the
§5 construction directory; `Construction/Machine/` keeps the executable side (`DescExec`,
`ClockedSim`) and the retired counted-machine spike.

`dd:fuel` is closed as a modeling substitution. The label now marks a *sufficient
certification device*: the class the construction quantifies over is
`MachineEfficientTrader`, and the fuel certificate implies membership in it. The model
card's lower calibration — machine ⟹ fuel — remains open, costs nothing paper-facing, and is
not claimed.

---

# Part XXV — the perturbation branch closes (2026-08-26)

Stage 3 left two statements whose *conclusion* is the criterion sitting at the fuel class,
because restating them needs the machine class closed under a trader translation. Both are
now resolved, and they resolved differently.

## XXV.1 `thm:scon` — closed at the machine quantifier

`conditionedTranslation_preserves_machine` and
`eventualConditionedTranslation_preserves_machine` are the `Complexity.FP` transports, under
the *same* `RpnSentenceCodes` hypothesis on the condition as their fuel counterparts — so
nothing is weakened and the trader hypothesis is strictly stronger. The endpoints
`lic_conditioned_machine`, `lic_conditioned_gated_machine` and
`lic_conditioned_eventual_machine` conclude `IsMachineLogicalInductor`. The fuel endpoints
and their inhabited witnesses are untouched beside them: this is a strengthening, not a
replacement.

The transduction is six `Complexity.FP` passes over one word-level automaton — price, guard,
count, budget rendering, acceptance, frame — built on a fold combinator (`TokenFold`) that
did not exist before this branch. Two disclosed clamps were introduced and then *discharged*
rather than left standing: the conditioning emitter draws its block at `min D n`, and the
guard pass is what makes that exact.

## XXV.2 `thm:ifp` — the published statement is false

Not a formalization gap. `not_overgeneral_ifp` refutes the unrestricted finite-day statement
at the paper's own quantifier, closed but for the deductive process. The mechanism is that a
single changed pricing day is an infinite computable function: `def:marketprocess` bounds
neither its runtime nor its output size, so one perturbed day can publish advice that an
efficient trader reads through historical price features without ever computing it. The
diagonal price family the repo already had (`ParadoxResistanceQuote`) supplies a sequence on
which knowing one bit is worth a certain `1/2` per settled round.

The corrected theorem is finite *support*: `machine_lic_iff_of_recognizableSupport`, taking
two computable markets and a perturbation and nothing else. Its one residual hypothesis is a
condition on the syntax of the finitely many moved sentences, standing for two `FP`
primitives this toolkit lacks — integer square root and a structured-payload parser — both
proved necessary rather than convenient.

## XXV.3 What the port cost

The FP closure kit (`mem_FP_comp`, `mem_FP_pairWithInput`, the whole `Cobham` subtree, the
binary-arithmetic subroutines) had never been type-checked on this pin; Stage 3 needed none
of it, and both transports run through it. Eight mechanical commits in the fork cleared it,
of which seven additive `rfl` simp lemmas carry most of the work. The pin moved
`964ce2d → 1b0d107`.

## XXV.4 The `dd:fuel` ledger, final

The fuel class is a certification device throughout. Every machine-facing endpoint in this
branch takes machine hypotheses; none falls back to `IsLogicalInductor`. The fuel-class
freeze certificates remain uninhabited, and the reason is now attributed rather than open:
the fuel calculus does not close over the escape-leaf decode — the inverse-operation ceiling
this note predicted, binding exactly where it was predicted to.
