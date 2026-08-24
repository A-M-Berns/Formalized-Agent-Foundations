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
| `Classes/P/Defs` + closure kit | 2 & 3 | `FP`, `mem_FP_comp`, `ite_mem_finset_mem_FP` | ~1,500 | low (builds today) | **yes** |
| `TuringMachine/Combinators`, `Composition` | 2 & 3 | seq/if/loop, output bounds, `Hoare` | ~12,600 | medium (`Hoare`, `Lift`) | **yes** |
| `TuringMachine/Subroutines` | 3 (via UTM) | counters, pairing, emit | ~27,700 (partly in closure) | **medium-high** (`Counter`, `PairEmit`) | yes, unavoidable |
| `TuringMachine/SingleTape` | 3 | multi→single reduction; `Corr.outputEq` | 6,676 | **high** (5,344-LOC `Correctness`) | yes, unavoidable |
| `TuringMachine/UTM/**` | 3 only | `TMDesc`, `utmTM`, universality | 23,681 | medium | yes for Stage 3 |
| `Classes/P/Cobham/**` | — | machine-independent bridge | 34,140 | medium | **no** (§1.5) |
| `Models/RandomAccessMachine`, `Circuits/`, `SAT/`, `Classes/PPoly` | — | not reachable from our seeds | ~140,000 | — | **no** |

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
said to test rather than assume. It does, and `LogicalInduction/Construction/Machine/CodeSteps.lean`
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
