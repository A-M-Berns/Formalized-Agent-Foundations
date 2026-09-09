# Formalization knowledge — Logical Induction (arXiv:1609.03543)

Facts about this formalization that a reader working on it would otherwise have to
rediscover: the paper-to-Lean correspondence at the points where the names do not match,
and the design decisions that are settled and should not be relitigated. It deliberately
does not duplicate the canonical documents — read those first.

- Trust surface, disclosures and strength claims: `LogicalInduction/README.md`
- Recommended consumer import and its boundaries: `LogicalInduction/API.lean`
- `dd:*` design-decision glossary, naming conventions, endpoint-suffix ladder:
  `LogicalInduction.lean`
- `dd:fuel` model card: `Framework/Emission/Computable.lean` ("### `dd:fuel` model card")
- Defects in the source paper: `notes/paper-errata.md`
- Lean and toolchain traps: `notes/lean-gotchas.md` — the single home for pitfalls
- Checked endpoint inventory and axiom accounting: `AxiomAudit.lean`

**Names that moved.** A consolidation pass over the whole library deleted several hundred
unreferenced internal declarations, renamed 26, and demoted 22 `theorem`s to `lemma` (names
and types unchanged — the demotions are keyword-only, and every one is still under the
statement freeze). Nothing on the trust surface changed: the freeze diff over every
`Paper node:`-annotated declaration, every `AxiomAudit.lean` inventory name, every `theorem`
under `LogicalInduction/` and every `API.lean` declaration reports the renames and nothing
else. If a name in this file, in a docstring, or in your own notes does not resolve, it was
either renamed or deleted as debris: look the name up in the tree rather than trusting the
note. The renames worth knowing without looking them up:
`IsPolyBounded.add' → .add`, `TraderMachine.sizeOf' → .sizeParam` (and its three lemmas),
`FeedbackTruth.sequence → .feedbackResidualSeq` (and its seven dependents),
`ComputableLUV.lhs`/`.rhs → .thresholdLhs`/`.thresholdRhs`,
`MachineExec.regCells_zero → regCells_zero_eq_init_nil`,
`parseStructuredPaperPrime_encode → parseStructuredPaperPrime_leaf`, and the eight general
analysis lemmas that left the `LUVCombination` namespace for the root one.

**Paths that moved.** A layout pass then re-grouped the tree by subject without touching a
single declaration name or elaborated type: roughly a hundred modules changed address, several
were merged or split, and `Construction/Witnesses/` and `Construction/Machine/` are gone. The freeze diff
over the whole statement surface came back clean at every wave, with an empty rename map. So a
*path* in an old note, docstring, or commit message may be stale even though every name in it
still resolves: look the name up rather than the file. The addresses that most often catch a reader out:
each module of `Construction/Witnesses/` is now in one of the nine `Construction/` lane
directories; `Construction/Machine/` split between `Framework/Machine/` (the `def:ec` machine
reading) and `Construction/Conditioning/` (the trader translation); `Properties/Basic.lean` and
`Properties/Hysteresis.lean` dissolved into `Properties/Support/Exploitation.lean` and
`Properties/Coherence.lean`; `Framework/RationalCut.lean` and
`Framework/Machine/SentenceCodes.lean` folded into `Framework/Expectations.lean` and
`Framework/Machine/WriteOutMachine.lean`; and `Construction/Quotation/Schema.lean` is
`Construction/Quotation/Packages.lean`. A later structural pass moved six more things:
`Framework/Machine/Descriptions.lean` and `Framework/Machine/ClockedSim.lean` are
`Construction/Descriptions.lean` and `Construction/ClockedSim.lean` (beside their only
consumer, `MachineTraderEnumeration`); the general half of
`Construction/LIACompiler.lean` — every `Primcodable` instance, the rational and `EF`
arithmetic certificates, and every parser certificate — is `Construction/Primcodable.lean`,
leaving `LIACompiler.lean` the §5 compiler alone; `sentenceAtomCodes` with its substitution
lemma is `Framework/BooleanWorlds.lean`; `semanticPrimeTag` and `SemanticPrimeFreshSentence`
are `Construction/Knowledge/Syntax.lean`; `DeferralFunction.graphFlag_ruler` and
`.tendsto_atTop` are `Properties/SelfTrust.lean`, beside the structure; and
`DivergentWeighting` is `Properties/Calibration.lean`. One rename went with it: the old name
`lia_learns_halting_patterns_unconditional` no longer exists and is now
`lic_learns_halting_patterns_unconditional`, which is the `lic_<node>` rule the rest of the
surface follows.

**A certificate lemma's name states its metering lane, and the two must agree.** On a
development whose central audit question is which lane a certificate sits in, a name asserting
the wrong one is a live source of mis-reading — treat a mismatch as a defect, not a cosmetic
issue. The lanes that a reader is most likely to look for under an old spelling: the seven
`dus*_rpnSpliceStream` lemmas are `*_machineSpliceStream` (`Properties/UniversalSemimeasure.lean`,
matching the `ob*_machineSpliceStream` siblings); the whole `liftedRpn*` family is
`liftedMachine*` (`Construction/SemanticExtension/LanguageCopy.lean`), which is what the
canonical `thm:ccee` statement prints; and the `*_polyFueled` / `*_polySeg` schedule and
feedback-emission certificates are `unaryRuler_*` / `machineDigits_*` /
`machineSentenceCodes_*` / `machineSpliceStream_*` (`Construction/Statistics/FeedbackEmission.lean`,
`Construction/Quotation/DeferralFibre.lean`). Also gone, with no replacement:
`rpnGuardedConditionRun_polySegStream_of`, `computationClaimSentence_digits` and
`strict_domination_of_null_separator_class` — all three were consumer-less, and the first
carried a `Paper node:` line only because it was inventoried. Also new: `LUV.indicatorOf` with
`LUV.indicatorOf_gt_ne`, `LUV.indicatorOf_isIndicator` and
`LUV.indicatorOf_machineThresholdCodeSeq`;
`lic_expectation_indicator_unconditional` (the canonical `thm:ei` at the paper's own
quantifier, which constructs `1(φ)` for an arbitrary e.c. `φ` rather than taking the
indicator family as data — its `[0,1)` thresholds are `φ ⋏ ∼∼φ`, *not* `φ`, and
`expectation_indicator_not_identity` is the market that prices the two apart);
`Trader.Exploits` as `def:exploitation`'s annotated carrier;
`PCWorld.ConsistentWithTheory.holds_of_mem_stage`; `PolyMachineCodes.toDigitMachineCodes`;
`presentedLUVSeq`; `polyPositiveWidths_two_pow_inv`; `doublingDeferral` with
`not_polyFueled_doublingDeferral`; `UnaryRuler.two_pow_min`; and `unboundedTruth` with
`unboundedFeedbackTruthComputation_nonempty` / `exists_unbounded_feedbackTruthComputation`.

## Layout

**One directory, one reason to exist**, stated in that directory's own map module, and legible
from its name. The library is 160 modules; the full tree is in `LogicalInduction/README.md`'s
*Layout* section, whose four graded entry points elaborate 40 / 58 / 148 / 159 of them. What
belongs here is the rule that decides where a new module goes:

* `Framework/` — the paper's §2–3 objects plus the substrate the later directories consume; a
  module belongs here when it is one of those objects or serves `Properties/`, `Construction/`
  or both, and several of them (all of `Theory/`, `Emission/RpnComputation`) serve only
  `Construction/`. `Framework/Theory/` is the background
  first-order theory Θ and the proof theory over it; `Framework/Emission/` is the `dd:fuel`
  certificate calculus rendering `def:ec`; `Framework/Machine/` compiles a certificate into the
  `Complexity.FP` machine the criterion actually quantifies over. The decisive rule is closure:
  nothing in `Framework/` imports `Properties/` or `Construction/`.
* `Properties/` — §4 theorems over an arbitrary `[IsLogicalInductor P DP]`, one file per
  theorem family, in the paper's own subsection order. **Nothing here imports
  `Construction/`**, and that is a load-bearing invariant, not a preference: it is what lets a
  downstream client take the §4 library without the §5 construction. Shared §4 proof
  technology that renders no paper node goes in `Properties/Support/`.
* `Construction/` — §5, plus one lane directory per §4 family the construction discharges over
  the single market `liaHistory (paperDP T)`. A lane is named after the paper family, never
  after a role: there is no `Witnesses/`, no `Certified…`, no `…II`. Six of the nine lanes end
  in an `Endpoints.lean` holding exactly the statements over that market. Three top-level
  modules of `Construction/` are not §5 mathematics but the substrate §5 runs on, and they are
  here rather than in `Framework/` because their subject matter is declared here:
  `Descriptions` and `ClockedSim` (the executable machine-description interpreter and its
  clocked simulator, which make the trader enumeration effective) sit beside
  `MachineTraderEnumeration`, their only consumer, and `Primcodable` carries the concrete
  `Primcodable` instances and parser certificates — a `Primcodable RationalBeliefState`
  instance cannot live under `Framework/`, since `RationalBeliefState` is `MarketMaker`'s.

Two consequences worth stating because they were each derived the hard way. A module that
*consumes* the criterion belongs in `Properties/`; a module whose conclusion *is* the criterion
(the conditioning and freeze transports) belongs in `Construction/`, because it must be closed
under the trader translation it performs and therefore reaches the construction. And placement
is decided by the import DAG in both directions before a move: several plausible groupings
turn out to be non-convex in the DAG (the `SemanticExtension/` Source/Quote grouping, the
`ExactProduct ← ProductDefinition` merge), and the boundary to cut on is the convex one.

A third consequence, and the rule that dissolved the `Quotation/` ↔ `Statistics/` pair: **when
two lanes need the same object, the object goes up beside its own definition, not into either
lane.** `scheduledValue`, `scheduledMatch` and `deadlineRun` are stated in
`Properties/SelfTrust.lean`, next to `DeferralFunction`, because both lanes test a deferral
deadline; there is no `Framework/` home for them, since `DeferralFunction` is a `Properties/`
object and `Framework/` is closed. The general shape: the lowest legal home for shared §5
substrate is the `Properties/` module that declares the type it is about.

## Correspondence table

The full paper-to-Lean correspondence is carried by the `Paper node:` docstring lines and
checked two-way by `scripts/check-paper-nodes.sh`. Listed here are only the places where the
name does not say what the object is.

| Paper (§/symbol) | Lean name | What to know |
|---|---|---|
| `def:ec`, §3.3 (`sec:efc`, tex:749) | `EfficientlyComputable` (`Framework/Criterion.lean`) | Ordinary polynomial time via `Complexity.FP`, over the **unary** day. This is the class the construction enumerates and dominates and the class `def:lic` quantifies over; `PolyFueledTrader` beside it is the `dd:fuel` certificate, landed inside it by `PolyFueledTrader.toEfficientlyComputable` (`Framework/Efficiency.lean`). |
| `def:ec`, certification | `PolyFueledTrader` / `PolyFueled` (`Framework/Emission/Computable.lean`) | Fuel-clocked `Nat.Partrec.Code` certificates (`dd:fuel`). A *sufficient* route into the machine class (`PolyFueledTrader.toEfficientlyComputable`), not a definition of it. Fuel meters the **value** `n`, not its bit length, which is sound only because the day is unary. |
| `def:ec`, e.c. machine sequence (tex:1931) | `DigitMachineCodes` (`Framework/Emission/WriteOut.lean`) = `BigDigits (Code.sourceNat ∘ m)` | Machines are `Nat.Partrec.Code`, **named by `Code.sourceNat`** (`Framework/Emission/CodeSource.lean`): the postfix tag stream (1=zero … 8=rfind', 0 = pad, never emitted) read base-16. Linear in the syntax tree (`len4_sourceNat_le : len4 c.sourceNat ≤ 2 * c.size`), total primitive-recursive decoder `ofSource` with `ofSource_sourceNat`. `Encodable.encode` is **not** used for naming anywhere on the claim-name path (see intentional deviations). `UniversalCodeHalts z := ((Code.ofSource z.unpair.1).eval z.unpair.2).Dom` decodes the source *inside* the represented computation. |
| `def:ec`, e.c. bitstrings / naturals | `BigDigits` (`Framework/Emission/DigitArith.lean`) | Two `PolyFueled` programs (base-4 length, digit access). `PolyFueled` bounds the *output value* too, so `len4 (x m)` is polynomially bounded: a `BigDigits` family is writable in poly fuel. A length-`n` bitstring has `~n/2` base-4 digits. Refuting `BigDigits` for a family reduces to a superpolynomial base-4 length (`not_polyFueled_two_pow` shape). |
| `def:ec`, e.c. sentences / rationals / emission | `BigSentenceCodes`, `DigitRatCodes`, `BigTokenStream`/`BigSpliceStream` (`Framework/Emission/WriteOut.lean`) | The write-out ladder. Value-bounded predecessors: `PolyNatCodes`/`PolyMachineCodes` (whole value; kept only as strictness foils, no `Paper node`) and `RpnSentenceCodes`/`RpnThresholdCodeSeq` (per-token value). `RpnSentenceCodes` is *not* purely symbol-metered: `PolySegStream` bounds every emitted token's value, so a single atom with exponential index is excluded by `Rpn` and admitted by `Big`. **The threshold classes a statement takes are `LUV.MachineThresholdCodes` / `LUV.MachineThresholdCodeSeq`** (`Framework/Machine/ThresholdMachine.lean`); the write-out pair `LUV.BigThresholdCodes(Seq)` and the token pair `LUV.RpnThresholdCodes(Seq)` (`Framework/Expectations.lean`, with `LUV.RpnThresholdCodes(Seq).toBig` the embeddings) are producer routes only — **no binder on any canonical endpoint, and no field of any structure one binds, is at either pair**, the single-LUV expectation surface (`LUV.expect_converges`, `lic_linearity_of_expectation`), `LUVCombinationSyntax.threshold_poly` and `ConvergencePresentation.threshold_code` included. `LUV.RpnThresholdCodeSeq` survives only inside proofs, as the route in via `RpnSentenceCodes.toMachine ∘ LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq`. `Construction/LUV/SourceCodec.lean` splices Gödel codes out of small tokens (`PaperLUVSeq.source_valued_and_machineThresholdCodeSeq`). `PaperLUVSeq.structural : MachineArithmeticSourceSeq` meters one token per source node — the paper's own symbol count. Foundation's `Operator.numeral` is unary — a Foundation artifact; the paper never fixes a numeral notation (it writes numerals positionally, tex:614, tex:757). That artifact does not narrow the class, because the *value* is nameable compactly inside ℒₒᵣ: large values are named by compact terms (Horner `binNumeral`, O(log v) nodes) or by definitions (tex:614: writing ⌜f(3)⌝ 'merely requires writing out the definition of γ_f' — e.g. Foundation's Δ₀ `exponentialDef`), and those renderings are admissible. Witnesses: `unitFracPaperLUVSeq` (`1/(n+1)`), `dyadicPaperLUVSeq` (`2⁻ⁿ`). On numerals the class is fine. **The class is NOT coextensive with `def:ec` on connectives:** the paper's language has `⟺` primitive (tex:560); Foundation's NNF `Semiformula` has none and `a 🡘 b = (a 🡒 b) ⋏ (b 🡒 a)` duplicates both sides (`3 + 2|a| + 2|b|` tokens), so a left-nested `⟺` chain is O(n) in the paper and ≥ 2ⁿ tokens here — `iffChain_not_polyArithmeticFormulaSeq`. `→` and `¬` are linear. That gap is what `dd:nnf` was originally about; the faithful repair is a compact formula SOURCE language with `iff`/`imp`/`neg` primitives decoded to NNF for semantics (the `Code.sourceNat` pattern applied to formulas — the correct target of that idea; a binary-numeral source node was rejected as a permissive widening). DONE in: `ArithSource` (`Construction/LUV/ArithmeticSource.lean`) is that source language, and the same source metering is reused for `thm:incons`. `dd:nnf` is therefore **not** a charged substitution any more: it names the two-layer architecture (paper-source metering, normal form inside the parser), and `PolyArithmeticFormulaSeq` is kept only as the strictness foil. |
| `def:ece` / `def:fuz` | `GeneratedRatFeature` (`Framework/Expectations.lean`) and `PGenerableWeighting` (`Properties/Calibration.lean`) are both `def:ece`; `def:fuz` is `DivergentWeighting` (`Properties/Calibration.lean`) | `def:fuz` is tex:1212-1214 — a `[0,1]`-valued sequence with divergent sum — and *not* "def:ece minus the denotation clause", which is what `PGenerableWeighting` is; the two conditions are conjoined at every use, and only the conjunction is the paper's "ℙ-generable divergent weighting". Both `def:ece` emission fields are `BigSpliceStream`; that shared meter is what makes `pGenerableWeighting_iff` statable — keep them at the same meter. General `PGenerableRat` constructor: `PGenerableRat.ofMachineRatCodes`; `ofPolyRatCodes` (`Construction/Quotation/ProductDefinition.lean`) is the derived value-bounded corollary. `ratCodeFeature`/`ratCodeFeature_generated` live in `Expectations.lean` at `MachineRatCodes` strength, which that module can state because it imports the machine splice suite. A constant leaf `EF.const q` serializes to `[1, encode q]` — one token whose value *is* the code — which is why the old `RpnSpliceStream` field silently excluded the paper's `2⁻ⁿ`. |
| §4.9 nodes (`thm:halts`/`loops`/`dontwait`), endpoint stack | `lic_learns_halting_patterns` (`Properties/MetaLearning.lean`) → `*_ofComputation` (`Construction/Knowledge/Syntax.lean`) → `*_unconditional` (`Construction/Paper/ComputationDP.lean`) | Three layers, all present: generic (no theory hypotheses, arbitrary `P`/`DP`), syntax layer (`[IsLogicalInductor P DP]` + `ComputationTheoryPresentation`), canonical instantiation over `liaHistory (theoremDP T)`. An auditor who sees only the canonical row wrongly concludes no arbitrary-inductor endpoint exists. `⌜f⌝(⌜n⌝)` → `boundedHaltingClaimInput m x hh.program n`, with `⌜f⌝` a constant and `n` unevaluated. `CodeHaltsWithin` meters by `evaln` fuel, not Turing steps — harmless at `thm:dontwait`, live if a positive bounded-runtime result is ever stated. |
| Foundation `re_complete` | `Foundation/FirstOrder/Arithmetic/R0/Representation.lean:260` | An **iff** stated under `[T.SoundOnHierarchy 𝚺 1]`; only `.mpr` (provable ⇒ true-in-ℕ) uses soundness. `.mp` is `sigma_one_completeness` (`R0/Basic.lean:143`, `[𝗥₀ ⪯ T]` only) — a soundness-free `re_complete_mp` compiles in six lines. `Entailment.Consistent T` is derived from the soundness instance (`Basic/Hierarchy.lean:481`), so every `inferInstance` for consistency silently routes through it. The transport that lifts `codeOfREPred_spec` to standard-model truth of a schema instance is inlined in `re_complete_mp` (`Construction/Knowledge/Syntax.lean`); the named standalone lemma of that shape is `models_valueSchema` (`Framework/Theory/QuoteRepresentability.lean`), and the two schema instances are `universalHaltingSchema_spec` and `universalBoundedHaltingSchema_spec`. |
| `def:lic` | `IsLogicalInductor` (`Framework/Criterion.lean`) | The criterion the construction proves, over `EfficientlyComputable` (`def:ec`, ordinary polynomial time), and what the whole §4 tail is stated against. It is the only criterion class: nothing here states the criterion over the fuel certificates. |

### The fuel/machine pairs, in one place

`def:ec` is read on ordinary machines, and every class the endpoint surface takes is the
`Complexity.FP` reading. Beside each such class stands a fuel-clocked one with the same
subject matter, and the pair is a *calibration*, not two versions of one thing: producers
build the fuel certificate where that is convenient, cross once by the named bridge, and the
statement is at the machine class. **Every bridge runs fuel → machine and no converse is
claimed anywhere.**

| what is metered | machine class (what statements take) | fuel/token class (what producers build) | bridge |
|---|---|---|---|
| an emitted token run | `MachineTokenStream` | `BigTokenStream`, `PolySegStream` | `BigTokenStream.toMachine`, `BigTokenStream.ofPolySegStream` |
| a sentence family | `MachineSentenceCodes` | `BigSentenceCodes`, `RpnSentenceCodes` | `.toMachine` on each |
| an emission (splice) surface | `MachineSpliceStream` | `BigSpliceStream`, `RpnSpliceStream` | `BigSpliceStream.toMachine` |
| a natural written out | `MachineDigits` | `BigDigits` | `BigDigits.toMachine` |
| a rational written out | `MachineRatCodes` | `DigitRatCodes`, `PolyRatCodes` | `DigitRatCodes.ofPolyRatCodes`, `.toMachine` |
| a machine's source | `MachineMachineCodes` | `DigitMachineCodes`, `PolyMachineCodes` | `DigitMachineCodes.toMachine` |
| a LUV threshold family | `LUV.MachineThresholdCodes(Seq)` | `LUV.BigThresholdCodes(Seq)`, `LUV.RpnThresholdCodeSeq` | `.toMachine` on each |
| a paper formula's source run | `MachineArithmeticSourceSeq` | `PolyArithmeticSourceSeq` | `PolyArithmeticSourceSeq.toMachine` |
| a count that reindexes | `UnaryRuler` | `∃ c, PolyFueled c f` | `UnaryRuler.of_polyFueled` |
| a trader | `EfficientlyComputable` (`def:ec`) | `PolyFueledTrader` (`dd:fuel`) | `PolyFueledTrader.toEfficientlyComputable` |

The criterion over the trader row's machine class is `IsLogicalInductor` (`def:lic`), and there is no second
criterion class: nothing here states a §4 theorem over `PolyFueledTrader`, because closure of
the certification engine's own class is a fact about `dd:fuel` and not a paper claim.
`MachineDigits` is the one pair whose two halves name *different objects* — the emitted digit
block against random access to a value's digits — and that divergence is disclosed at the
definition; the forward inclusion still holds. Two classes have no machine reading and are
not meant to: `PolyMachineCodes` and `PolyNatCodes` are whole-value strictness foils, refuted
by `digitMachineCodes_nest_not_polyMachineCodes` and `bigDigits_two_pow_not_polyNatCodes`.

- **Day indexing: Lean day `n` = paper day `n+1`, throughout the criterion layer.**
  `Trader.netWorth` sums over `Finset.range (n+1)` (days `0..n`) against the paper's `∑_{i≤n}`
  over ℕ⁺, and `Strategy n`'s `rank_le ≤ n` lets a day-`n` strategy see `V 0 … V n` = the
  paper's `𝒱₁ … 𝒱_{n+1}`. `unaryDay 0 = []`, so day 0 gets a constant time budget, matching the
  paper's `poly(1)` at its first day. A day-indexed premise must therefore hold at Lean day 0
  as well; premises guarded by `0 < n` do not transfer.
- `def:ec` is paper **§3.3**, not §2.2 — §2 is Notation, §3 is the Criterion.
- `evaln_output_can_exceed_fuel` (`Framework/Emission/Computable.lean:51`), `codeEvalBound`,
  `codeEvalBound_poly` and `codeEvaln_result_le` (`Framework/Emission/Emission.lean:21–78`) are
  **repo** lemmas, not Mathlib. Grepping Mathlib for them finds nothing.

### The two output-sensitive clocks, and how `Complexity.FP` states them

Two paper conditions bound a runtime in the **value the program returns** rather than in the
day it is given: `def:deferralfunc`'s condition 2, "`f(n)` computable in time polynomial in
`f(n)`" (tex:1243), and `thm:wub`'s feedback clause, "`Th(φ_{f(n)})` computable in `O(f(n+1))`
time" (tex:1251). `Complexity.FP` meters the length of its *input*, so it has no form of
either condition of a machine handed the day alone — but it has one of a machine handed the
**unary pair**, whose length dominates the value. That is the whole trick, and it is worth
stating once because it is the mechanism by which an input-length class expresses an
output-sensitive bound: `TokenFold.unaryPair_mem_FP` emits
`List.replicate (Nat.pair (A z).length (B z).length) true`, and `Nat.pair n m ≥ max n m`, so
picking the input that carries the bound is enough — no new FP primitive is needed, and
`UnaryRuler g` composed with `UnaryRuler.pair` is the same thing.

| paper clause | Lean field | shape |
|---|---|---|
| `def:deferralfunc` cond. 2 (tex:1243) | `DeferralFunction.graph_fp` (`Properties/SelfTrust.lean`) | `∃ G ∈ Complexity.FP, ∀ n m, G (unary ⟨n,m⟩) = ⟦f n = m⟧` — the *graph* is decided, on an input of length `Nat.pair n m ≥ m` |
| `thm:wub` feedback (tex:1251) | `FeedbackTruth.FeedbackTruthComputation.computes` + `.computes_at` (`Construction/Statistics/FeedbackTruth.lean`) | `MachineDigits code` with `∀ k, code ⟨k, f (k+1)⟩ = ⌜value k⌝` |

**The two are not symmetric and must not be described in one breath.** `graph_fp` is
*equivalent* to the printed clause in both directions (forward: run the `h (f n)`-clocked
program for `h m` steps, a timeout implying `f n > m`; backward: scan `m = n+1 … f n`, each
test polynomial in `m ≤ f n` and at most `f n` of them — only the forward direction is used in
Lean, every consumer going through `DeferralFunction.graphFlag_ruler`). `computes` is a **relaxation**: the
paper asks for *linear* `O(f(n+1))` time, `Complexity.FP` is a polynomial-time class with no
linear-time form, and the implication runs paper ⟹ field only. That is the safe direction — a
weaker hypothesis, so the six `thm:wub`/`wubaff`/`wubexp` endpoints are *stronger* than
printed — and it must never drift back to "is". `computes` is also **total**, metering every
paired index rather than only the deferred ones, which costs nothing (clock a program meeting
the paper's clause by the same polynomial at every input, answering `0` on timeout) and is
what the single consumer needs: `machineDigits_truthCodeAt` composes it with the ruler
`m ↦ ⟨feedbackIndex f m, m⟩`, so the emitter needs metering at every paired index. If a
refactor drops `computes`, the residual-family emitter loses its `PolySequence`.

Deciding the graph on the unary pair is strictly **wider** than any whole-value fuel clock: a
`PolyFueled` field on `f` itself excludes every super-polynomially growing `f`
(`not_polyFueled_two_pow`), which `def:deferralfunc` explicitly allows, so the 23 endpoints
binding a `DeferralFunction` are correspondingly stronger. The second consequence is that the
day-bounded deferral schedule is **exact**, not an approximation:
`deadlinePassed f i n = true ↔ ∀ k ≤ i, f k < n` holds on the nose and
`scheduledMatch_eq_one_iff` is unconditional, because the graph scan decides `f k = m` for
every `m ≤ n` exactly. There is consequently no clock parameter and no `hspec` hypothesis
anywhere on the `scheduled*` / `deadline*` lane; prose calling `deadlineRun` / `deadlinePassed`
a "sound under-approximation of the undecidable deadline" is describing a budgeted `evaln` run
and is wrong about this code.

**Twenty-three canonical endpoints bind a `DeferralFunction`**, six of them a
`FeedbackTruthComputation` as well (the twenty-four-row census block counts `DeferralFunction`
itself as `def:deferralfunc`'s carrier): the three `thm:prandaff`, three `thm:prandexp`, three
`thm:benford`, three `thm:prand`, two each of `thm:wub`/`wubaff`/`wubexp`, plus `thm:cee`,
`thm:ceu`, two `thm:ccee` and `thm:st`. Anyone quoting "ten" is quoting an audit note, not the
source.

### §4.9–§4.10, the arithmetized lanes

**The Con substrate.** `Framework/Theory/BoundedConsistency.lean`: `BProv T φ k` (bounded
provability, `∃ d, Proof T d φ ∧ dSize d ≤ k`, the bound **inclusive** as the paper's is),
`conWithin T k` (= the paper's `Con(T)(k)`), `bprovValue T : ℕ → ℕ` (the decider),
`conRunValue T f` (the universal decider `thm:pac` represents), `conWithin_of_consistent`,
`conWithin_anti`, plus `ProofPacked`/`proofPacked_sigmaOne`/`not_proofPacked_sigmaOne`/
`proofPacked_computable` and `bProv_iff_bounded`, which is where `le_G_dSize` is spent.
`Construction/Knowledge/Endpoints.lean` carries the claim family: `conClaimArg`, `conClaimSentence`,
`conGamma`/`conGamma_spec`, `representedConClaims`, `conClaimSentence_ne_of_day_ne`.

**The Con family is parametric in TWO theories, and `thm:pac` is the diagonal.**
`exists_reprAll_conRunValue`, `conGamma`, `conGamma_spec` and `representedConClaims` all take
`(T T' : ArithmeticTheory)`: `T` represents (the market's theory, the paper's Θ), `T'` is
metered (the paper's Θ′). `thm:pac`'s sentence is `conClaimSentence (conGamma T T hh) n` —
the DOUBLED argument; a one-theory spelling `conGamma T hh` is wrong.
`representedConClaims` takes `Entailment.Consistent T'` explicitly; at the diagonal `thm:pac`
supplies `RepresentsComputations.consistent T`.

Signatures: `lic_belief_finitistic_consistency_unconditional` reads
`(T) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [RepresentsComputations T] (horizons) (hh : ComputableHorizon horizons)`
and concludes `liaHistory (paperDP T) n (conClaimSentence (conGamma T T hh) n) ≈ₙ 1`.
`lic_belief_stronger_theory_consistency_unconditional` adds `(T' : ArithmeticTheory) [T'.Δ₁]`
and `(hcons : Entailment.Consistent T')`, concluding at `conGamma T T' hh`: the market is Θ's,
the claims are about Θ′. Both route through `lic_belief_finitistic_consistency`
(`Properties/MetaLearning.lean`). Witnessed in-file at Θ = 𝗜𝚺₁, Θ′ = 𝗣𝗔, horizon `ack n n`.

**§4.10 paper↔Lean map.** `Con(Θ′)(ν)` ↦ `conWithin T' ν`; the *represented* object is
`conRunValue T' f` (a universal bounded-provability decider at the packed
`⟨sentence code, day⟩`), not `conWithin` itself; the day-`n` claim ↦
`conClaimSentence (conGamma T T' hh) n`; `⌜Θ′ₙ⌝ is inconsistent` ↦
`(representedInconsistentTheoryClaims …).inconsistencySentence n`, its negation ↦
`.consistencySentence n` (definitionally `∼`). The paper's Θ is the first theory argument,
Θ′ the second.

**`thm:incons` is about machine-enumerated theories.**
`theoryOf (m : Nat.Partrec.Code) : ArithmeticTheory :=
{σ | ∃ (b i : ℕ) (s : ArithSource 0), evaln b m i = some s.sourceNat ∧ compile s = ↑σ}`;
the represented predicate is
`MachineTheoryInconsistent z := ∃ w, ProvableCode ∅ (negWindowCode z w)` — over the **empty**
theory, mentioning no base theory anywhere. The endpoint reads
`(T) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Consistent T] (m : ℕ → Nat.Partrec.Code) (hm : DigitMachineCodes m)
(hinc : ∀ n, ¬Consistent (theoryOf (m n)))` and delivers both paper conjuncts;
`inconsistencySchema_mentions_zero` and `_ne_of_arg_ne` are HYPOTHESIS-FREE. Supporting
modules: `Construction/Knowledge/SourceWindow.lean` (`verumSourceNat`, `combineTokens`/`combineSourceNats`,
`conjSource`, `compile_conjSource`, `axiomWindow`, `negWindowCode`) and `Construction/Knowledge/DayMachine.lean`
(`dayMachine F n = curry F n`, `digitMachineCodes_dayMachine` — the computing day-varying
`DigitMachineCodes` witness); in `BoundedConsistency.lean`, `listConj`, `consistent_empty`,
`exists_inconsistent_list`, `provable_neg_listConj_of_not_consistent`, `provable_listConj`.
Witnesses: `thm_incons_applied_deep` (source `5n+7` tokens written, `≥ 2^n` compiled nodes,
every-pair separation) and `thm_incons_applied_infinite` (INFINITE day axiom sets — a
deduction family adjoining one sentence cannot express these).

`InconsistentTheoryClaims` is a THREE-field structure — `inconsistencySentence`,
`inconsistency_poly`, `inconsistency_provable`; `consistencySentence` is a `def`
(`∼inconsistencySentence`). Six-field spellings, `#assert_fields` included, are wrong.

**The window gate, and why it is needed.** `machineTheoryInconsistent_iff m :
MachineTheoryInconsistent m.sourceNat ↔ ¬Consistent (theoryOf m)` is sound AND complete. An
UNgated window leaks in three independent ways: `tokensOfNat` keeps digits below the first
63-sentinel, so numbers that name nothing decode like shorter names (`8138` decodes like
`4042 = (leaf ⊥).sourceNat`); the token splice is list surgery, so two *incomplete* runs
concatenate into one complete refutable run (`tokenListNat [20]` ++ `tokenListNat [9,9]`);
and — the one that is easy to miss — a genuine `ArithSource 0` can compile to a
FREE-VARIABLE formula (`∅` refutes `&0 ≠ &0`, which is no sentence of any theory), so a
parse-consumed-everything gate is insufficient. Each makes `MachineTheoryInconsistent` hold
of machines whose `theoryOf` is EMPTY. The gate is per entry, in `Construction/Knowledge/SourceWindow.lean`:
`AdmissibleName v := tokenListNat (tokensOfNat v) = v ∧ sourceRun … = some []`, `gateName`,
`axiomWindow`, with `exists_sources_axiomWindow` (every window IS `ss.map sourceNat` of
sentence-valued sources). The recognizer is
`Construction/Knowledge/SourceRecognizer.lean` (~1435 lines): `sourceRun`/`sourceTermRun`
(depth-tracking, free-variable-rejecting), `exists_source_of_sourceRun` (soundness = a
reconstruction theorem), `sourceRun_sourceTokens` (completeness), canonical-only
`structuredNatRun`, level-function factoring, full `Primrec` certificates. The endpoint's
signature is untouched by all of this; what the gate buys is that the day sentence's content
*equals* the `dd:machinetheory` claim. Also here: `theoryOf_const_ofNNF` (every one-axiom
theory realized exactly; uniform surjectivity honestly scoped as not formalized),
`not_provableCode_zero`, and `ArithSource.compile_eq_of_sourceTokens_eq` — `sourceTokens` is
NOT injective (leaf `(φ⋏ψ)` vs `and (leaf φ) (leaf ψ)`) but equal runs compile equally.
`machineTheoryInconsistent_iff` and `theoryOf_const_ofNNF` are `Paper node: thm:incons`
carriers.

**Why `theoryOf` is NOT realigned to parser semantics, though that is the first design one
reaches for.** `parseStructuredArithmeticFormula` returns a CODE, ignores its depth argument,
accepts the free-variable tag, and the development has no parser-completeness theorem — so
parse-consumed-everything cannot yield `⌜σ⌝` for any sentence. Closing the converse through
the parser would need parser fuel-monotonicity + a parse-append lemma (neither exists) + a
Foundation `Provable T x → ∃ σ, x = ⌜σ⌝` (does not exist). A purpose-built recognizer whose
soundness is a RECONSTRUCTION theorem keeps `theoryOf` at its paper-facing spelling, leaves
every splice lemma applicable, and delivers the full iff. A token-whitelist guard of the kind the memo below rejects hits
the same wall.

**Uniform-in-theory-code derivability stays a VERIFIED OBSTRUCTION, and `thm:incons` does not
depend on it.** External machines plus compactness never form a uniform internal predicate.
A verified obstruction being real is not the same as its being binding on a given statement,
and collapsing that distinction is the easiest mistake to make on a re-read.

**What the paper actually asks of `thm:incons` (quoted anchors, for re-audits).** `def:ec`
(tex:754-756) is ONE polymorphic definition; tex:1931 is the interpretive key ("write out the
source code specifying mₙ in time polynomial in n; the runtime of an individual mₙ is
immaterial"), tex:1905 confirms it for incons ("efficiently named"). Must not narrow: (i)
Θ′ₙ is FREESTANDING and may be stronger than the market's Θ (tex:1882, tex:1889); (ii) axiom
sets may be INFINITE (the paper's examples are 𝗣𝗔, 𝗭𝗙𝗖); (iii) the believed sentence is the
UNBOUNDED existential. "Recursively axiomatizable" is never defined in the paper; the
r.e.-axiom-set reading narrows nothing.

**`γ.Mentions 0` IS derivable from the representation spec** whenever the represented function
is non-constant — `mentions_zero_of_repr_ne` (`Framework/Theory/RepresentsComputations.lean`, ~10
lines via `Semiformula.rew_eq_of_not_mentions`: a γ ignoring `#0` makes `reprAll γ y z`
z-independent, so the biconditional forces `g z = g z'`). The `f ≡ 0` counterexample is sound
but bounds the claim to CONSTANT deciders. Con-lane discharges: `conGamma_mentions_zero`
(non-constancy), `conGamma_mentions_zero_of_horizon_unbounded` (the usable form: ⊤ provable ⇒
some derivation code exists; an unbounded horizon exceeds it),
`conGamma_mentions_zero_ackermann` (fully discharged at 𝗜𝚺₁/ack).

### The §4.10 symbol measure

`Framework/Theory/DerivationSize.lean`: `idxLen`, `pl`/`pr`/`arg`/`tail`, `tvAux` (mode-packed
term/vector recursion) with `tSize`/`tvSize`, `fSize`, `sSize`, `dSize`; the tower `G` with
`G_mono`, `self_le_G`, `le_G_tSize`/`tvSize`/`fSize`, `lt_two_pow_G_sSize`, `le_G_dSize`;
faithfulness equations `dSize_axL/verumIntro/andIntro/orIntro/allIntro/exsIntro/wkRule/
shiftRule/cutRule/axm`, `fSize_qq*`, `tSize_qq*`, `tvSize_adjoin`, `exp_nat_eq`,
`mem_iff_testBit`, `fSize_le_sSize(_of_mem)`, and `dSize_pos {d} (h : 0 < d)` (`dSize 0 = 0`
is the only zero). The same file's computability half carries the `_primrec` /
`_computable` pairs plus `computable_boundedSearchValue`.

**Faithfulness is enforced by nothing but the `@[simp]` equations.** All ten derivation tags
match Foundation (`axL = 0 … axm = 9`, `Bootstrapping/Syntax/Proof/Basic.lean`); formula tags
`qqRel = 0 … qqExs = 7`; term tags `qqBvar = 0`, `qqFvar = 1`, `qqFunc = 2`. No constructor
drops written material (`wk`/`shift` count `sSize s + dSize d`; `cut` counts the cut formula
and both premises; `verumIntro`'s trailing `0` is a placeholder costing nothing). Any future
`dSize` edit must be re-checked against those Foundation files **by hand**.

**Verified, do not re-search: Foundation has NO size/length/height/symbol count on derivation
codes** anywhere in `FirstOrder/Bootstrapping`. `formulaComplexity` (connective complexity,
atoms ↦ 0) and `bv` are V-valued formula recursions, unusable as an external computable
`ℕ → ℕ`. `DerivationSize.lean` duplicates nothing upstream.

**`Bootstrapping.Proof T d φ` is `DerivationOf T d {φ}`** — the conclusion sequent is exactly
the singleton. So `conWithin T k` is "no derivation concluding exactly `{⌜⊥⌝}` in ≤ k
symbols", which differs from the paper's "proof of ⊥" by at most one `wkRule` node: truth is
unaffected, but the convention matters at the ±1-node margin.

**The measure's decidability rests on `le_G_dSize`, in the negative polarity.** `dSize d ≤ d`
is the useless direction. `bProv_iff_bounded` is sound because `d ≤ G (dSize d) ≤ G k` by
`G_mono`; both polarities are genuinely decided; the junk branch is unobservable twice over
(the Fixpoint forces well-formedness, and truth never mentions `dSize`); `BProv` is
non-vacuous (`conGamma_mentions_zero_of_horizon_unbounded` manufactures `BProv T' ⌜⊤⌝`).

**Foundation facts these lanes rest on.** `instance : Entailment.Consistent 𝗣𝗔`
(`Arithmetic/Schemata.lean`, via `consistent_of_sound` at the standard model);
`PA_delta1Definable` / `ISigma1_delta1Definable`
(`Incompleteness/InductionSchemeDelta1.lean`); `PeanoMinus.delta1`. `Entailment.Consistent
𝗭𝗙𝗖` exists (`SetTheory/Universe.lean`) but 𝗭𝗙𝗖 is not an `ArithmeticTheory`, so the paper's
ZFC illustration is NOT directly instantiable — 𝗣𝗔 is the right second theory, and the
soundness route stays confined to the witness `example` while the endpoint takes consistency
as a hypothesis. Foundation's sequences are cons lists at the numeral level (`x ∷ v = ⟪x, v⟫ +
1`, nil `= 0`, `HFS/Vec.lean`), so external recursion over a coded vector needs only
`Nat.unpair`; sequent membership `p ∈ s` is `s.testBit p` at ℕ (`Exponential/Bit.lean`), so a
`Finset.range`-bounded sum guarded by `testBit` is both honest and primrec-friendly.
`Theory.Δ₁` has an EMPTY-theory instance (`Δ₁.empty`, `ch := ⊥`,
`Bootstrapping/Syntax/Theory.lean`), so `ProvableCode ∅`, `provableCode_re ∅` and
`proofPacked_computable ∅` all elaborate: the provability engine runs at PURE LOGIC, with no
base theory. `Δ₁.add`/`singleton`/`ofList`/`ofFinite` and instances for `∪`/`{φ}`/`insert`
are installed; `σ ∷ T` is `rfl`-equal to `insert σ T`; `Consistent (∅ : ArithmeticTheory)` via
`consistent_of_sound ∅ (Eq ⊥) rfl`.

**Foundation HAS compactness for `FirstOrder.Theory`, in the strongest form — the proof object
carries its axioms.** `structure Theory.Proof` (`FirstOrder/Basic/Calculus.lean`) has fields
`axioms : List (Sentence L)`, `axioms_mem`, `derivation`; `T ⊢ φ = Nonempty (T ⊢! φ)`, so the
finite axiom set is `rcases h with ⟨d⟩` — no induction. Packaged: the `Entailment.Compact`
instance, `Compact.finite_provable` (`Logic/Entailment.lean`),
`inconsistent_compact`/`consistent_compact`, `Theory.provable_iff`/`inconsistent_iff` in List
form. No Finset-indexed form exists; do not hand-roll finitization.

### Metering vocabulary, the market, and the tag spaces

**The four metering words, and which one a statement uses.** *Machine-metered* is the only one
a paper-facing statement takes: the `Machine*` classes plus `UnaryRuler`, all `Complexity.FP`
of the unary day. The other three name the certification calculus. *Write-out*: `BigDigits`, `BigSentenceCodes`, `DigitRatCodes`,
`DigitMachineCodes`, `BigTokenStream`/`BigSpliceStream` — magnitude unrestricted, only the
emitted symbol count bounded, which is what `def:ec` meters. *Token-metered*:
`PolyFueledTrader`, `RpnSentenceCodes`, `RpnThresholdCodes(Seq)`, `RpnSpliceStream`,
`PolySegStream` — a per-token value clause on top of the length bound. *Whole-value*:
`PolySentenceCodes`, `PolyThresholdCode(Seq)`, `PolyRatCodes`, `PolyNatCodes`,
`PolyMachineCodes` — a bound on the Gödel *value*, strictly narrower than `def:ec` and
carried by no paper-facing row. "Symbol-metered" as a tier name means the token-metered tier;
where the phrase appears at `BoundedConsistency.lean` and in the README it means the paper's
own symbol count instead, so read it in context. A docstring calling a `Machine*` premise
"token-metered" is simply wrong — that word belongs to the `Rpn*`/fuel layer, and the two are
adjacent enough that the mislabel reads plausibly.
`AffineCombination.PolySequence` is **machine-metered in every field** — `termCount_poly :
UnaryRuler`, `const_poly`/`coefficient_poly : MachineSpliceStream`, `sentence_poly :
MachineSentenceCodes` (`Framework/Affine.lean`). Any note calling it a write-out class is
wrong; read the fields.

**The machine readings of the write-out tier, and the two roles a `ℕ → ℕ` parameter plays.**
`Framework/Machine/` carries the `Complexity.FP` reading of the whole write-out ladder, so an
efficiency argument can run at `def:ec`'s own class with no fuel certificate in it. Six classes
in `Framework/Machine/WriteOutMachine.lean` — `MachineTokenStream`, `MachineSentenceCodes`,
`MachineSpliceStream`, `MachineDigits`, `MachineMachineCodes`, `MachineRatCodes` — plus
`LUV.MachineThresholdCodes(Seq)` in the leaf `Framework/Machine/ThresholdMachine.lean` — a
leaf of its own so that `SentenceMachine.lean` does not reach `Framework/Expectations.lean`,
which lets the edge run the other way: `Expectations` imports
`Framework/Machine/SpliceMachine.lean` and states its `def:ece` constructors at
`MachineRatCodes`. Two closure suites mirror the fuel ones one for one (`SentenceMachine.lean` ↔
`BigSentenceCodes.*`, `SpliceMachine.lean` ↔ `BigSpliceStream.*`); two capstones close at the
trader (`EfficientlyComputable.ofSingleTradeBlocksBig`, `.ofTradeBlocksBig`, over
`MachineSpliceStream.ec`); `APITests/LogicalInduction.lean` has two examples certifying a
trader with no fuel certificate in the derivation; `Framework/Machine/Witnesses.lean` inhabits
every one of the six classes with a day-varying family plus its `_nonconstant` lemma.
**Every fuel-side `PolyFueled c f` parameter has TWO machine renderings and picking the wrong
one wastes a proof.** Where `f` REINDEXES (dispatch test, segment count, day map) the reading
is a *unary ruler* `fun z ↦ List.replicate (f z.length) false ∈ Complexity.FP`, from
`UnaryRuler.of_polyFueled` or `UnaryRuler.id`. Where `f`'s VALUE is written into the stream the
reading is `MachineDigits f`, strictly more general (a ruler's own word is polynomially long,
`MachineDigits` admits exponential values); `MachineDigits.ofUnaryRuler` goes ruler → value and
there is no way back. Ruler hypotheses do NOT unify higher-order — pass `(f := …)` /
`(cnt := …)` explicitly. **`MachineDigits` is NOT the pointwise translation of `BigDigits`**:
it is the emitted digit *block*, `MachineTokenStream (fun n ↦ [x n])`, not random access to a
value's digits — the random-access spelling has no consumer and no cheap bridge, so the two
calibrations differ in what they NAME, not only in how they meter. **The value lane is
complete**: `MachineRatCodes.toMachineDigits` and `MachineDigits.natPair` rest on
`DigitFP.mulW` (`Framework/Machine/DigitArithFP.lean`), base-four word multiplication as a
Horner loop under `Cobham.iterate_mem_FP` whose running product is TRUNCATED at a ruler built
from the two operands — that truncation, not any length bound on `addW`, is what keeps the
iterated state bounded, since `addW` writes a run three bits wider than its whole argument
and `output_length_poly_of_mem_FP` compounds to p^n inside an iterate. The unary route
(`TokenFold.uMul_mem_FP`) is unsound at exponential values and is not it. Nothing inside the
mirror consumes those two lemmas; what they unblock is the machine restatement of the
§4.6–§4.10 endpoints whose emission premise would otherwise be `DigitRatCodes` or the
`DigitMachineCodes`/`BigDigits` pair. **No converse
is claimed** at any class: every bridge runs fuel → machine. The restatement is finished:
**the ledger's `def:ec` row is `exact`**, no canonical endpoint binds an emission class
outside the machine ladder (printed or through a boundary structure), and the two premises
that are not emission premises — `def:deferralfunc`'s clock and `thm:wub`'s feedback clock —
are machine-metered too, on the unary pair.

**The §4 property tail has exactly ONE funnel into trader efficiency: `BigSpliceStream.ec`
(`Framework/Emission/WriteOut.lean`).** Every data class converts into
`BigSpliceStream`/`BigSentenceCodes`, packs into `AffineCombination.PolySequence` or
`PolyTradeEmulatable`, and reaches `PolyFueledTrader` through four trader bridges (plus
`ofSingleTradeBlocksBig`). The certificate is consumed as EMISSION DATA — the splice opens it
— not as an opaque predicate, so the hypothesis class cannot be swapped without rebuilding
the splice.

**The single market is `paperDP` = `(theoremDP T).union (paperTheoryDP T)`**
(`Construction/Paper/TheoremDP.lean`). Neither census below is restated here, because
neither is owned here: the market census over the canonical endpoints belongs to *The single
market* section of `scripts/coverage-classification.md`, where
`scripts/check_li_rollcall.py` recomputes it, and the binder census belongs to
`AxiomAudit.lean`'s *Concrete arithmetic instantiation* note, which measures it by
elaborating `#check` over the canonical block rather than by grepping the sources. The two
things worth carrying in your head are that **no endpoint takes `SoundOnHierarchy`** and that
the endpoints carrying `𝗜𝚺₁ ⪯ T` are named in `LogicalInduction/README.md` under a marker the
checker reads. Substrate: `paperDP_computable`/`_hworld`/`_nonvacuous`,
`paperDPComputation`, `paperQuotationPresentation` (= `quotationPresentation.mono`, where
`QuotationTheoryPresentation.mono` lives in `Construction/Quotation/Packages.lean`, beside the structure it lifts),
`paperLIA`, `paperMarketComputation`, `paperDP_covers_of_paperTheoryDP`. The self-reference
lane lives in `Construction/Paper/Market.lean`, forced by the import DAG:
`paperTheoryDP` is DOWNSTREAM of `Quotation/MarketQuoteCodes`. `theoremDP` and `paperTheoryDP` survive
only as construction ingredients and as the CCEE lane's ruled base, not as a parallel endpoint
lane. There is no cut-law union process: the `paperCutLawDP` / `paperBaseDP` lane, with its
computability, coverage and model-soundness lemmas, does not exist — nothing imported it, no
endpoint priced against it, and folding it into the
endpoints would have dragged the semantic-source lane into each of them. Its one design
fact, the public-negation/NNF ABI gap, is a section of `Construction/SemanticExtension/Source.lean`'s module
docstring: public negation is an implication into `⊥`, so it does not commute with
first-order NNF negation definitionally, and a process wanting the public negation or
implication of prime-decomposed sentences must publish them literally from an r.e.
provability gate.

One endpoint still names `theoremDP`: `lic_no_expected_net_update_conditional_exact_canonical`
does so in a HYPOTHESIS (`source_valued` quantified over `ConsistentWithTheory (theoremDP T)`
worlds) while concluding at `canonicalCCEEDP`. A premise over a smaller process's worlds is
the *stronger* premise (a superset of worlds), and it is the form that proof needs.

**THREE distinct tag spaces — do not conflate.** (1) `ComputationClaimKind.godelCode` (two
constructors). (2) `theoremDP`'s EVENT tags, gapless `0`–`5`: `0`/`1` halting ±, `2`/`3`
bounded halting ±, `4`/`5` quotation ±. `ComputationTheoryPresentation` freezes six field
names accordingly, and carries no inconsistency/consistency fields. (3) The GLOBAL
atom-payload first component, gapless `0`–`6`: computation `0`–`1`, product `3`,
semanticPrime `4`, paperPrime `5`, oldLanguage `6`, with `bitAtomTag = 7` and
`FinitePerturbationCounterexample`'s advice tags at `7`/`8` — strictly above the payload
space rather than colliding with it, so the disjointness argument is numeric. The
authoritative table is at `ComputationClaimKind.godelCode`. Each atom family carries a
freshness lemma.

**A word-level FP serialization kit exists in `Construction/Conditioning/TransductionFrame.lean`** (`wConst`/`wAdd`/`wMul`/
`wMax`/`wSafeRecip`/`wPriceSym`/…, their FP lemmas, and the `BlockWF` algebra), mirroring the
`serialize_*` family one for one. Anyone contemplating machine-side emission lifts these
first; it cuts the estimate roughly in half.

**complexitylib proves Cobham's theorem** (`CobhamFP_eq_FP`, `Classes/P/Cobham.lean`):
machine-independent induction over FP (projections, bit successors, smash, LIMITED recursion
on notation) — the right tool for "every FP function has property P" without TM programming.
Its PUBLIC FP surface is ~7 lemmas; the real string kit is proof-internal in
`Cobham/Internal.lean` (this repo imports it anyway, disclosed at `FPFold.lean`); no value
arithmetic exists as `_ ∈ FP`.

**What `Complexity.FP` actually unfolds to, verified rather than assumed** (complexitylib
`Classes/P/Defs.lean`): `∃ d k (tm : TM k) T, tm.ComputesInTime f T ∧ T =O (·^d)`, where
`ComputesInTime` (`Models/TuringMachine.lean`) quantifies over ALL inputs and demands halting
within `T |x|` with `f x` on the output tape, and `=O` is Mathlib's `IsBigO` at `atTop`. So it
is genuine total deterministic poly time — there is no degenerate reading to worry about, and
the unconstrained small-length values of `T` are finite and harmless (the paper's `poly(1)` is
also just a constant). Two consequences the machine layer leans on: FP membership alone bounds
output length by a polynomial in input length (`Cobham.output_length_poly_of_mem_FP`,
`Cobham/Internal.lean`), which is why no machine class needs a length-polynomial field of its
own; and `Cobham.exists_exact_ruler` really produces a word of length exactly `p.eval |z|`,
which is what makes `UnaryRuler.of_polyFueled`'s clamped read-back sound.

**`UnaryRuler f` is spelled with `false` marks** (`List.replicate (f z.length) false ∈
Complexity.FP`, `Framework/Machine/Ruler.lean`) while `unaryDay` and
`Complexity.unaryLength_mem_FP` use `true` marks, so every ruler lemma ends with a recolouring
step, `Complexity.Cobham.mulLenFn_mem_FP h (FPFold.constFn_mem_FP [true])`. Expect to need it
in any new ruler lemma; it is not a proof smell. `UnaryRuler` also unfolds *definitionally* to
that FP membership, which is why `succDeferral.graph_fp` can be discharged by handing a
`UnaryRuler.eqFlag …` term straight into the `∃ G ∈ Complexity.FP` slot with no coercion lemma
— note the mixed convention there, input `replicate _ true` and output `replicate _ false`.
Being delta-reducible is also a hazard: a raw `List.replicate`-spelled goal still typechecks
and hides which lemma you meant.

**Two FP-combinator arguments that look dead and are not.** `traderOutput`
(`Framework/Machine/TraderMachine.lean`) emits `digitsToBits (map (min · 4) tokens)`, and the
clamp is load-bearing rather than cosmetic: `digitBits` is three bits, so a digit ≥ 8 would not
round-trip through `bitsToDigits`. That is why `PolySegStream.exists_FP_rawWord` takes `d ≤ 4`
(not `d < 4` — 4 is the block terminator and survives the clamp verbatim) and why
`undigitize_map_min_four` is needed in the non-raw recipe. And `TokenFold.natFold_mem_FP`'s
`Wf`/`hW` parameter looks unused at both current clients (`MachineDigits.ofTokenListNat` and
`MachineTokenStream.lengthRuler` pass steps that ignore `W`), but the emission budget `hEbnd`
is `qQ.eval W.length + k * (…)`: `W` is what the per-step polynomial is evaluated at. Do not
simplify either away.

### Cleared suspicions — verified, and not to be re-raised

Criterion core: `EF.rank` is a sound over-approximation (see the bullet below).
`thm:li` delivers a genuine `def:belseq`. `thm:lp`'s diagonal is real Kleene recursion
(`parameterizedDiagonalQuoteCodeOfMarket_public_fixedpoint`). `hworld` on every §4 endpoint is
NECESSARY — stage-unsatisfiable processes make the criterion vacuous
(`isLogicalInductor_of_stage_unsatisfiable`). `HasROI`'s `Summable` clause is load-bearing
(Mathlib's `tsum` of a divergent series is `0`) and disclosed; it is not canonical. For
`thm:obu` read the `_ofCE` endpoint (the paper's own premise; `EfficientRepeatedEnumeration.ofCE`
dovetails). `thm:benford` sits at `thm:prand` strength (a patience-restricted quantifier is a
weaker hypothesis). `limitingBelief`/`expectInf` are TOTAL limsup stand-ins, proved equal to
genuine limits under the inductor hypotheses. `AffineQuoteEq.future_coherent` is derived on the
closed lane, not assumed. Pseudorandomness' `DeferralPatient` narrows a ∀-hypothesis, hence
strengthens. `paperDP` publishes only on `T`-provability — nothing is smuggled in as a bare
literal — and its two components use DISJOINT atom families, so "m halts on x" has two
unrelated propositional representations in the one market. The suffix ladder in practice:
`_ofX` conditional / `_unconditional` discharged over `paperDP` / `_closed` also constructs the
quote portfolio; canonical names are the innermost discharged form, often in a
`Construction/` lane rather than `Properties/`. `lint_paper_labels` enforces
theorem ⇒ label only, not label ⇒ claim: construction-machinery `theorem`s carrying `def:ec`
are a disclosed convention. `check-paper-nodes.sh` for LogicalInduction likewise enforces only
(1) that every backticked `kind:label` token resolves to a real `\label` / `dd:` entry /
`tex:NNNN`, and (2) that every `AxiomAudit`-inventoried declaration carries a `Paper node:`
line — unlike the Cartesian Frames / ModalAgents / Finite Factored Sets checkers it enforces
no `theorem`-iff-paper-facing discipline and no declaration-kind check, so a `lemma` carrying
`Paper node:` (e.g. `Strategy.serializeTrades_length_le_cost`) is within convention here. It
also cannot see prose that misdescribes a *type* or cites a name that no longer exists. `lic_iff_of_finiteSupport` covers finite COORDINATE
support, not the paper's finitely-many-DAYS — deliberately, since the whole-day case is exactly
what `not_overgeneral_ifp` refutes. `kappaU` is safe only because `uLenSet` is provably
nonempty: preserve `uLenSet_sInf_mem` under any refactor.
`PrefixMachinePresentation`'s whole-value + surjective pair is satisfiable because
`prefixSentenceEnum` is indexed BY the code (`encode (sentence n) ≤ n` — the trap needs
index ≪ code). The threshold certificate on paper LUVs avoids emitting exponential codes
because `structuredPaperSourceDecomposeAll_machineSentenceCodes`
(`Construction/LUV/ArithmeticSource.lean`) emits the SOURCE block and `parseRpn` contracts to
the tag atom; the family-level form is `PaperLUVSeq.source_valued_and_machineThresholdCodeSeq`
and the single-LUV corollary is `PaperLUV.machineThresholdCodes`. `codeEvalnNat_polyFueled` is true despite bounding
values, because Mathlib's `evaln` guards `n < k` at every `prec`/`rfind'`, so `codeEvalBound`
is polynomial in the fuel for a fixed code. There is no `PaperLUVCombination.worldValued`
convenience — clients hand-assemble via `paperTheoryDP_subset_paperDP` + `Classical.epsilon`.
`not_polySentenceCodes_bitPrefixSentence`'s emptiness proof is the MODEL for discharging the
metering trap: when a value-metered field appears on day-indexed syntax, ask for the
*emptiness* proof, not an inhabitation proof.

More cleared points, each with the argument that clears it, so the next reader need not
re-derive them:

* **`EfficientlyComputable` demands `F ∈ Complexity.FP` as a TOTAL function on `List Bool`,
  while the paper constrains only the inputs `1ⁿ`.** That looks like a silent strengthening —
  a narrower trader class, hence a weaker no-exploitation theorem. It is not: any tally-poly
  `g` extends to `x ↦ if x = 1^{|x|} then g x else []`, which tests "all true" in linear time
  and is in FP, so the two trader classes coincide. No lemma in the repo records this, so it
  has to be redone each time it is questioned.
* **`EF.rank` is the SYNTACTIC max over the tree, not the paper's semantic rank** (tex:766,
  "depends only on 𝒱≤n"), and the two genuinely differ: `safeRecip (price φ (n+1))` is
  constant `1` on `[0,1]`-valued histories, so the paper ranks it `0` and Lean ranks it `n+1`.
  It is still not a narrowing of the trader class: for any expressible ξ of semantic rank ≤ n,
  replacing every price feature of day > n by `const 0` yields a syntactic-rank-≤ n term with
  the same denotation on market (i.e. `[0,1]`-valued) histories, and `Strategy.value` only
  evaluates `denote` at the market. The soundness half is `EF.denote_eq_of_eqUpTo` /
  `Strategy.value_eq_of_eqUpTo` in `Construction/MarketMaker.lean` — an unexpected home.
* **`strategyOfOutput`'s surjectivity onto `Strategy n` is nowhere proved**, and it matters in
  principle: a non-surjective decoder would silently shrink `EfficientlyComputable` and so
  weaken `def:lic`/`thm:lia`. A manual check found no counterexample — every `serializeTrades l`
  has an RPN pre-image (`0 :: rpn φ ++ [d]` for a price leaf, `6 :: rpn φ` for a trade frame;
  tags 1 and 7 skip one literal payload token, so `const q` and `var i` payloads are protected),
  and `bitsToDigits` reaches every value `0..7`, so any digit stream is emittable. The missing
  lemma, if a later round wants it closed, is `∀ n (T : Strategy n), ∃ w, strategyOfOutput n w = T`.
* **`parseRpn`'s escape branch looks ambiguous and is not.** On tag `1` it matches
  `rest` as `0 :: payload => parseStructuredPaperPrime payload` *before* `c :: tail => decode c`,
  so a sentence whose Gödel code were `0` would be swallowed by the structured-arithmetic
  escape. It cannot happen: `parseRpn_escape` (`Framework/Emission/RpnSentence.lean`) proves
  `Encodable.encode φ ≠ 0` from `LO.Propositional.Formula.toNat φ ≠ 0` by `cases φ`. Do not
  weaken the `Formula.toNat` encoding without revisiting it.
* **`thm:benford`'s `∀ f : DeferralFunction, PseudorandomFrequency …` hypothesis is equivalent
  to the paper's unrestricted one**, not stronger. A divergent weighting is `[0,1]`-valued
  (`Properties/Calibration.lean`), so the window sum over `Icc n (f n)` is at most 2 for
  `f = succDeferral`: every ℙ-generable divergent weighting is `succDeferral`-patient, and
  instantiating `f := succDeferral` recovers the paper's hypothesis exactly.
* **`thm:affcoh` / `thm:affprovind` take `PolySequence + BoundedAffinePrices +
  (∃ C, magnitude ≤ C)` rather than the `def:bap` carrier**, and that is the safe direction:
  `BoundedCombinationSequence.boundedPrices` (`Properties/AffinePreemptiveLearning.lean`) plus
  `magnitude_le_l1Norm` derive both from a paper BCS given `IsLogicalInductor`'s `[0,1]` price
  range, so the Lean hypothesis set is *implied* by the paper's.
* **`hshare : ∀ n, (As n).shareNorm P ≤ b` on `luv_wubexp_ofComputation` is not extra
  generality lost**: `LUVCombination.BoundedSequence.exists_rat_shareBound`
  (`Properties/ExpectationProperties.lean`) derives it from the `def:blcp` L¹ bound, and the
  `_ofBounded` / `_unconditional` forms do exactly that.
* **`MachineDigits` / `MachineTokenStream` do not smuggle a value bound in through the length
  bound.** FP on `unaryDay d` bounds the emitted *word*, so token values up to `4^poly(d)` are
  admitted — witnessed by `machineDigits_two_pow` and `machineRatCodes_two_pow_inv`, which are
  exactly the exponential-value families the classes exist to admit. The two paired-index
  classes (`LUV.MachineThresholdCodeSeq` at `⟨n, ⟨k, i⟩⟩`, `MachineSpliceStream` at `⟨n, j⟩`)
  are read at `unaryDay` of the *paired* index, longer than either component, so they are
  weaker rather than unsatisfiable.
* **`thm:ccee`'s rational weight (`PGenerableRat`) versus the paper's ℙ-generable real weight**
  is not a narrowing: markets price into `ℚ ∩ [0,1]` and `def:tf` features evaluate to
  rationals there, so the classes coincide (argued at `Construction/Quotation/ExactCCEE.lean`).
* **`RationalQuoteCode` pins the quoted LUV only off the exact value** (`pos_complete` for
  `r < value`, `neg_complete` for `value < r`, nothing at `r = value`). That is the same
  cut-shaped slack `PCWorld.ValuesAt` has and the same one the paper's `lem:conluvapprox`
  absorbs; it does not leak into the endpoints.
* **`IntrospectionIntervalQuote.inside_affine` / `outside_affine` look like
  conclusion-in-hypothesis and are not**: they supply the portfolio whose completed-theory
  value is 0, and the vanishing of *its price* is what affine provability induction — hence the
  criterion — proves.
* **`EventualConditioningFloor` is not a vacuous premise.** `positive_floor : ∀ d ∉ zeroDays,
  ε ≤ P d (ψ d)` looks unsatisfiable for a real inductor, since a day with `0 < P d (ψ d) < ε`
  is in neither branch. The exceptional set is finite, so `ε` is shrunk below the minimum of
  the finitely many positive prefix quotes: `eventualConditioningFloor_nonempty_of_tail`
  (`Construction/Conditioning/Compiler.lean`) does exactly that, and
  `eventualConditioningFloorOfJointConsistency` derives the whole certificate from `thm:obu`
  plus `thm:tbo`.
* **`IsLogicalInductor.noExploitTok` (`Framework/Efficiency.lean`) crosses in the sound
  direction** (`EfficientlyComputableTok → EfficientlyComputable`), so its uses do not weaken
  the criterion.
* **The two ROI maturity schedules' `check_poly : ∃ c, PolyFueled c …` fields are constructed
  internally by the endpoints that need them** (`AffineCombination.recurringunbiasedness`, via
  `Construction/Statistics/HistoricalMaturity.lean`) and are never bound as premises, which is
  why `Framework/Machine/WriteOutMachine.lean`'s header can say both "no canonical endpoint has
  a fuel- or value-metered data premise" and "the deliberate fuel residue is the two ROI
  schedules' schedule predicate" without contradiction. The metered function is 0/1-valued
  anyway, so the value clause is vacuous.
* **`FeedbackTruthComputation`'s generic witnesses do not inhabit `luv_wubexp_ofComputation`'s
  premise.** That endpoint's `C` is at
  `FeedbackTruthComputation (LUVCombination.normalizedMeshTruth As P DP hworld b) f` — the
  truth stream is *pinned* by `As`/`P`/`DP`, so neither `ordinaryFeedbackTruthComputation` nor
  `alternatingFeedbackTruthComputation_nonempty` (free `truth`) reaches it. A joint witness
  would need a concrete `As` whose mesh truth is a computable rational stream. The generic
  witnesses establish satisfiability of the *class*, not of that endpoint's premise conjunction
  — a distinction worth keeping when counting non-vacuity.

## `thm:scon`, `thm:ccee`, `thm:ifp` — the strongest forms, and what they cost

These three nodes each have several renderings, and which one is the paper's is not
guessable from the names. This section says which, and records the facts that a reader
reconstructing the reasoning is most likely to get wrong.

**A write-out stream DOES supply its own clock.** The `thm:scon` conditioning lane is at
`MachineSentenceCodes`; the fact below is what first got it off the token-metered class, and
is kept because the general lesson is live.  Reaching `BigSentenceCodes`
from `RpnSentenceCodes` costs exactly one ~12-line lemma,
`BigTokenStream.digitizeStream : BigTokenStream t → PolySegStream (fun n ↦ digitize (t n))`
(`Framework/Emission/WriteOut.lean`), proved from `PolySegStream.undigitizeTokens` +
`BigDigits.blockSeg` + `concatVar`. The tempting diagnosis — that widening needs a
`BigSentenceCodes → MachineSentenceBlocks` FP re-blocking "at the scale of ~50 `_mem_FP`
lemmas" — is wrong twice over: `TokenFold.mem_digitize_le_four` bounds `digitize ts` for an
*arbitrary* token list (the clamp re-reads DIGITS, it does not bound a VALUE), and the
write-out certificate carries its own clock. General lesson: before recording a metering
retention as forced, check whether the clamp bounds a value or re-reads digits.

Names on that lane: `machineSentenceBlocks_of_machine` (there is no `_of_rpn` and no
`_of_big`) and `EfficientRepeatedEnumeration.ofMachineCodes`. Both
`condition_codes` structure fields (`ConditioningPresentation`,
`CompactConditioningProcessComputation`) are `MachineSentenceCodes`. Neither
`RpnSentenceCodes` nor `BigSentenceCodes` binds an endpoint on this lane; each survives as a
narrower sufficient subclass, reached by `RpnSentenceCodes.toMachine` /
`BigSentenceCodes.toMachine`.

**No token-metered carrier remains on the surface, and the census trap that hides one.**
Every threshold field a canonical endpoint reaches is at `LUV.MachineThresholdCodes(Seq)`:
`LUVCombinationSyntax.threshold_poly` (`Construction/LUV/Syntax.lean`),
`ConvergencePresentation.threshold_code` (`Properties/ExpectationProperties.lean`),
`SelfTrustQuote.product_codes`/`.confidence_codes` (`Properties/SelfTrust.lean`), and the
thm:cee/ceu/ccee/epr/er quote structures; `lic_expectation_indicator` (thm:ei) takes
`LUV.MachineThresholdCodeSeq` and `MachineSentenceCodes`; `LUV.expect_converges` (thm:ec) and
`lic_linearity_of_expectation` take `LUV.MachineThresholdCodes`. `LUV.RpnThresholdCodeSeq`
occurs only *inside* proofs, as the route in
(`RpnSentenceCodes.toMachine ∘ LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq`).
**The trap that made this hard to see:** a signature grep for the string `RpnSentenceCodes`
misses every threshold occurrence, because `LUV.RpnThresholdCodes(Seq)` is *defined as*
`RpnSentenceCodes` (`Framework/Expectations.lean`). Grep the string `RpnThreshold` as well (a
name prefix, not a declaration), and expand structure fields — a binder census cannot see a
premise that a structure field carries.

**scon.** The paper-facing conditioning theorems assume `MachineSentenceCodes`. What would
hold such a field at `BigSentenceCodes` is a sibling fuel-typed translation certificate, not
a missing combinator — there is none here. The `_ecRpn` / `_ecDigit` suffixes on
`RpnConditioning.*_preserves_ecRpn` / `ConditioningCompile.*_preserves_ecDigit` name the
*symbol model* the compiler emits in (RPN vs digit), NOT a sentence class; do not
"consolidate" them to `_preserves_ec`, which would collide the two lanes. The `_ecRpn` pair
itself is **gone** — retired with the `translation_ec` fields it filled — but its
`PolySegStream` support chain in `FramePass.lean` stays, because the machine pass
(`Transduction.lean`) imports the module for the shared automaton and scalars. Widening
needed zero proof-body edits because `hs.digitizeStream` re-resolves by dot notation from
`PolySegStream.digitizeStream` to `BigTokenStream.digitizeStream` — two distinct lemmas with
the same base name, so grep both namespaces.

**scon, growing form, at the paper's own quantifier.**
`ConditioningCompile.lic_conditioned_growing_ofSequence` (`Construction/Conditioning/Endpoints.lean`,
`Paper node: thm:scon`) renders the growing clause for an **arbitrary** `MachineSentenceCodes ψ`,
conditioning on the prefix conjunctions `ψ₀⋏…⋏ψₙ` (harmless `⊤` tail), over
`DP.union (prefixProcess ψ)`. It **derives** the prefix-conjunction certificate
rather than taking it as data; `lic_conditioned_growing_ofProcessComputation` stays as
the general process-quantified form. The enabling combinators are
**`RpnSentenceCodes.bigAnd` / `BigSentenceCodes.bigAnd` / `MachineSentenceCodes.bigAnd`**
(`RpnSplice.lean` / `WriteOut.lean` / `SentenceMachine.lean`,
`Paper node: def:ec`, mirrors of `bigOr`): the terminator closing the fold is the fixed
three-token block `[2,0,0] = imp ⊥ ⊥ = ⊤` (`Formula.top_def`, `rfl`;
`sentenceConjunction [] = ⊤`), so **no positivity hypothesis on the width** is needed.
`parseRpn_conjChain` (`RpnSplice.lean`, NOT `private` — reused cross-file) is the shared parse
induction.
- **Genuine obstruction, side-stepped rather than solved:** the certificate is emitted through
  `ConditioningPresentation`'s FREE `condition` field in **index order**
  (`sentenceConjunction ((range (n+1)).map ψ)`), NOT through
  `deductiveStageCondition (extra.D n) = (extra.D n).toList.conj₂`. The latter is genuinely
  **not poly-writable** for a growing family: `Finset.toList` order is recoverable only from
  exponential Gödel codes and `conj₂` is not permutation-invariant, so the Finset erases the
  emittable index order. The `Finset` `prefixProcess` is kept only for the order-insensitive
  `holds_condition` (`List.mem_toFinset`) and the union. Do not retry the
  `deductiveStageCondition` route — it is impossible at this cost.
- Pitfalls this lane surfaced: a `def` returning a code-carrying structure cannot `obtain` from
  a Prop `∃` (`Exists.casesOn` → Prop only) — split into `exists_prefixProcessCode` + `.choose`.
  There is no `List.toFinset` `Primrec`; use `sentenceListFinsetNorm` (dedup + code-sort, spec
  via `List.toFinset_sort`). `Construction/Conditioning/Endpoints.lean` is NOT reachable from `LogicalInduction.API`
  (import-graph BFS), so these endpoints are trust-surface only and their non-vacuity client
  (`ψ = atom i`, injective ⇒ conjunctions strictly grow) lives in-file.

**ccee — three renderings, differing in two dimensions.**
`lic_no_expected_net_update_conditional_paperLUV_closed` is **the paper rendering**: exact,
zero-slack, market `liaHistory (paperDP T)`, literal `PaperLUVSeq T` source, binders
`[T.Δ₁] [𝗜𝚺₁ ⪯ T] [RepresentsComputations T]` (𝗣𝗔 instantiates), in
`Construction/Quotation/{ExactProduct,RepresentedWeight,ExactCCEE}.lean`.
`lic_no_expected_net_update_conditional_exact_canonical` is exact over an arbitrary
threshold-only source but prices in `canonicalCCEEDP T` — the **generalized
semantic-extension** result, not the paper rendering.
`lic_no_expected_net_update_conditional_closed` carries the `dd:mesh` slack `1/(n+1)` over an
arbitrary source at the `paperDP` market — the general-input approximate form. `dd:mesh` is a
property of that endpoint, not of the node.
Three renderings and no more. The certified-source front end that once stood in
`Construction/SemanticExtension/Registry.lean` is **deleted**, and none of the names in this
sentence resolves any more (`lic_no_expected_net_update_conditional_registryCertified`,
`_registryCertified_closed`, `_registry_rightClosed`, `_certifiedSource_closed`, together
with the `theoremQuoteSemanticRegistryProductDP` substrate, the `CertifiedSourceLUVSeq`
activation instances and `semanticRegistryProductLUV_valuesAt`) is **deleted** — endpoint-
shaped names on no census are a faithfulness smell. What the canonical route actually
consumes from that module is exactly `semanticSchemaProductLUV`, its `_gt` simp form,
`semanticSchemaProductLUV_machineThresholdCodeSeq`, `semanticSchemaProductLUV_valuesAt` and
`rationalQuote_semanticHandle_valuesAt`; factor admission is supplied only in the primitive
`∀ limit, ∃ fuel, semanticFactorPrefixValidAtFuel …` form.
The product is exact for literal LUVs because a `PaperLUV` names its value by an unreduced
numerator/denominator pair code, so `(a/b)·(c/d)` is named by `(a·c)/(b·d)` — no gcd, no new
DP atom; the abstract `LUV` interface names no value, which is why mesh exists there. **The DP
does not grow for the weight:** `paperTheoryDP_covers_outer_provable` is universal, so the
representing formula `γ` is chosen after `f, w` are fixed. The weight is *represented*
(`RepresentsComputations` + `polyArithmeticFormulaSeq_subst_numeral`, metering only the day
numeral), never numeral-rendered — its values are computable but not `2^poly`-bounded.
`[RepresentsComputations T]` is the paper's own §2 premise (tex:600-606), anti-monotone in `T`
so it must stay an instance binder. The `.choose`-built weight family is
extension-determined (equal-extension weights give identical formulas by `rfl`) — benign, and
prose must say it represents the weight's *values / pair function*, not its *program*.

**ifp.** The corrected finite-perturbation theorem is
`FreezeOracle.lic_iff_of_finiteSupport`: finite `(day, sentence)`-coordinate support
(`FiniteSupportPerturbation`, a `Finset` of PAIRS — not finite-days) + `ComputableMarket` on
both, **no** `Recognizable`/`BotFree`/`NoReserved`, no caller freeze certificate.
`lic_iff_of_noReservedSupport` / `_of_recognizableSupport` are strictly weaker
corollaries via `.toFiniteSupport`; `finiteSupportPatch` takes no condition on `S`.
`NoReserved`/`BotFree` are discharged by BUILDING the FP machinery they stand for, in six
modules (`StructuredPatterns`, `CounterAutomaton`, `PayloadAutomaton`, `SegmentAutomaton`,
`SegmentCounter`, `SegmentRecognizer`): a per-target recognizer of exactly the token runs that
`parseRpn` maps to a fixed sentence (characterization `StructPat.parseRpn_iff_segMatch`, both
directions proved). `NoReserved` is really TWO devices — the aⁿbⁿ unary length field (a counter
machine `CtrAuto.ctrMachine`) AND the payload language of a fixed formula code (an
obligation-stack parser `PayAuto`, finite by a potential argument, never evaluated). The
published finite-DAYS theorem is FALSE (`not_overgeneral_ifp`, PE1); `tail_agree` +
`tailAgree_not_finiteSupport` pin the one-way implication so the corrected theorem cannot
re-derive the refuted one. **Disclosed residual:** the recognizer is compiled *per frozen
sentence*, so its FP witness carries constants depending on that sentence — the paper's own
"finitely many constants can be hard-coded" step, sound because the support is finite (the day
index enters only as the trader-machine input, no per-day blowup). Documented at the
FreezeOracle boundary note, API, README, errata PE1, coverage-classification. Strictness is
proved at the PERTURBATION level (`not_recognizableSupport_hardPoint` /
`not_noReservedSupport_reservedPoint`) — note that `RecognizableSupportPerturbation` is an
existential over `S`, so a sentence-level negative alone does not rule the restricted endpoint
out; the differing coordinate has to be forced into every admissible `S` via
`pointHistory_ne_at`.

**Non-vacuity witnesses worth knowing about.** `def:deferralfunc` is inhabited at **both ends
of the growth range its output-sensitive clause admits**, and that pairing is the pattern, not
a redundancy: `succDeferral` (`f := (·+1)`, `graph_fp` the equality flag ruler
`UnaryRuler.eqFlag UnaryRuler.unpairFst.succ UnaryRuler.unpairSnd` read as an FP function of
the unary pair) and `doublingDeferral` (`f n = 2 ^ n`, decided through `UnaryRuler.two_pow_min`
— a doubling loop truncated at the candidate value every step), with
`not_polyFueled_doublingDeferral` proving the fast one lies beyond every whole-value fuel
clock. The general lesson: a definition whose efficiency clause is *growth-sensitive* needs a
witness at both ends, or the whole reason the clause is output-sensitive stays uninhabited and
every endpoint binding it is exercised only by schedules the superseded metering could also
have carried. `canonicalCCEE_weight_nonvacuous` is the ccee one. The general toolkit for any weight premise (`Construction/Quotation/ProductDefinition.lean`) is
`harmonicWeight_polyRatCodes`/`_mem`/`_not_constant` + `PGenerableRat.ofPolyRatCodes`, which is
history-arbitrary and so discharges `weight_generable` in one line at any market; also
`pGenerableRat_two_pow_inv P` (returns a conjunction — take `.1`).

## Settled design decisions

**`thm:provind` is stated at the paper's semantic quantifier, and stage membership is strictly
stronger.** `lic_provind` takes `∀ n v, v.ConsistentWithTheory DP → v.Holds (φ n)`, which is
what Θ-completeness (tex:740) makes "φ is a theorem" mean under §4's standing setting. The
literal `∃ k, φ n ∈ DP.D k` is a *narrowing*, because `DeductiveProcess.D` is an arbitrary
nondecreasing `Finset` family with no closure condition — a process enumerating only Θ's
axioms is Θ-complete and contains no derived theorem. The one-way bridge is
`PCWorld.ConsistentWithTheory.holds_of_mem_stage`. `DeductiveProcess.exists_stage_entails`
(`Framework/Compactness.lean`) goes the OTHER way and lands on stage *entailment*, not
membership; it is not needed here, because the affine parent
`PolySequence.affine_provind_theory_eq` was already at the semantic form and moving to it
shortens the proofs. `lic_provind_seq`, whose `hded : ∀ n, φ n ∈ DP.D n` is the stronger
stage-indexed premise, is a `lemma` and carries no `Paper node:` line: a declaration whose
docstring disclaims a node must not be anchored to it.

**"The unary pair" means the unary numeral of `Nat.pair`, and it is the general device for
stating a polynomial-in-the-OUTPUT bound in an input-length class.** See *The two
output-sensitive clocks* above for the two paper conditions that need it. The general
bounded-search form is `UnaryRuler.segPrefix lenFn n k = Σ_{j<k} lenFn ⟨n,j⟩`, a ruler
whenever `lenFn` is: any bounded search over an FP-decided predicate is machine-computable
that way. `scheduledValue f ⟨n,k⟩ = if f k ≤ n then f k else 0` recovers `f k` from its graph
inside a day-`n` budget by summing `m·⟦f k = m⟧`; `deadlinePassed` uses the dual, a prefix sum
of failure flags tested against zero (`segPrefix_eq_zero_iff`). The **uncapped** `2 ^ a n` is
not a ruler and can never be one — a ruler's output word *is* its value, so an exponential
count is an exponentially long output, which `Complexity.FP` forbids — so exponential growth
in the ruler calculus must be capped first (`UnaryRuler.two_pow_min`); the cap is not a
convenience.

**`def:fuz` is `DivergentWeighting`, not `PGenerableWeighting`.** The paper's Divergent
Weighting (tex:1212-1214) is a `[0,1]`-valued sequence whose sum diverges — no emission
content at all — and that is `DivergentWeighting` (`Properties/Calibration.lean`).
`PGenerableWeighting` is `def:ece`'s progression data *minus* the denotation clause, related
to `GeneratedRatFeature` by `pGenerableWeighting_iff`; it carried the `def:fuz` annotation for
a long time and no longer does. Every §4.3–4.5 statement that says "ℙ-generable divergent
weighting" takes the two conditions conjoined, so nothing about the statements changed when
the label moved — but the canonical endpoint for `def:fuz` did, and `PGenerableWeighting` is
now axiom-checked in a topical block rather than in `LI-CANONICAL`.

**The `_of_historicalVerifiers` and other conditional forms are `lemma`s, not `theorem`s.**
`theorem` means "renders a paper claim". A form that still carries the maturity-verifier
hypothesis renders no claim: the claim is the unconditional sibling in
`Construction/Statistics/HistoricalMaturity.lean`, which discharges it. The same reading
demotes the analytic consumers named after a node (`simcal_of_recurring_unbiasedness`,
`BoundedSequence.limexpapprox`, `BoundedCombinationSequence.wubaff`) — `lem:limexpapprox` is
one of the eight excused appendix labels, and `thm:wubaff`'s node is carried by
`FeedbackTruth.boundedCombination_wubaff_ofComputation`. The rule is enforced by
`scripts/lint_paper_labels.py`, which fails on any `theorem` under `LogicalInduction/`
with no paper label; the one `theorem` under `Properties/` with no `Paper node:` line is
`not_overgeneral_ifp_of_advice`, which *refutes* rather than renders `thm:ifp` and says so at
the declaration.

**The two efficiency classes, and which way the inclusion runs.**

- `PolyFueledTrader Tr → EfficientlyComputable Tr` is proved
  (`PolyFueledTrader.toEfficientlyComputable`). The converse is **not** proved, and the honest
  wording for it is "not attempted; structurally blocked" — never "false as stated" or
  "provably fails". The block is a **workspace** bound, not a toolkit gap: at a fixed code
  `PolyFueled` is poly-time with `O(log n)` workspace while `Complexity.FP` is poly-time with
  polynomial workspace, so the converse is a P-versus-L-flavoured containment over tally
  inputs. Naming the inverse digit operations (`sqrt`, `unpair`, big-divisor `div`) as *the*
  obstruction understates it — all three are logspace-computable — and `RpnFreeze` itself says
  the claim holds in the intended complexity model; `not_polyFueled_two_pow`
  (`Framework/Emission/Computable.lean`) separates only `PolyFueled`, by output size. The
  model card's "Lower calibration" wording is authoritative.
- The fuel bound is polynomial in the **day**, and the day is unary, so composing
  `codeEvalSteps_poly` (`Framework/Machine/CodeSteps.lean`) with either the `PolyFueled`
  bound or `PolyFueledTrader`'s explicit clock `a * (n + 1) ^ k + a` gives a step count
  polynomial in the input length. A binary day rendering would silently strengthen the class.
- The clock normal form's `+ a` summand and `(n + 1)` base are load-bearing for
  satisfiability at degenerate inputs: `|output| ≤ |input| + t` at `w = []` needs
  `clock 0 ≥ output length`, which `2a` supplies and a bare `a · n ^ k` would not.
- The `IsPolyBounded f` conjunct of `PolyFueled` is derivable from the other two, via
  `codeEvaln_result_le` + `codeEvalBound_poly` + `IsPolyBounded.comp`.
- `codeEvalBound c k` is polynomial in the fuel **per fixed code** — the degree grows with
  the code, since `pair` doubles it. The `n ≤ k` guard caps every value passed onward, which
  is why exponential-growth codes return `none` rather than break the bound.
- `IsPolyBounded.add` and `.mul` sit together in `Framework/Emission/Computable.lean`
  with the rest of the closure suite; neither has a primed variant.

**Serialization and the decoding pipeline.**

- `Trader` is a one-field structure, so `PolyFueledTrader`'s witness equality
  `clockedTrader lc tc clock = Tr` is interchangeable with the pointwise form
  `∀ n, strategyOfTokens n (unRpn (undigitize (clockedTokens lc tc (clock n) n))) = Tr.strat n`.
  Machine-side bridges consume the pointwise form.
- In that chain `clockedTokens` emits the **digit** stream — one digit per `tokenCode` call —
  not tokens. Clamping digits by `min · 4` is semantics-preserving, because
  `undigitizeStep` branches only on `d < 4` and treats every `d ≥ 4` as a block terminator
  (`undigitize_map_min_four`). That clamp is what lets the machine emit a fixed three bits
  per digit.
- The clamp lemma `undigitize ∘ map (min · 4) = undigitize` is a one-line `blockSplit`
  invariance from `undigitize_eq_blockSplit` (`Framework/Emission/DigitArith.lean`) plus
  `blockStep`, not a from-scratch induction.
- **Degenerate inhabitants are not evidence of content.** The interpretation chain's empty
  conventions cooperate — `undigitize [] = []`, `unRpn [] = []`,
  `deserializeTrades [] = some []`, `strategyOfTokens n [] = ⟨[], _⟩` — so
  `strategyOfTokens n (unRpn (undigitize [])) = Trader.zero.strat n` closes by `rfl`, and any
  class of the shape `∃ F, «F is efficient» ∧ interp ∘ F = Tr.strat` is inhabited by the
  constant-`[]` witness. `EfficientlyComputable` included. Never cite such a witness as
  evidence that a machine statement has content.

**The `evaln` simulation.**

- `evaln`'s `prec` ladder never underflows, and no intermediate guard fails once the
  top-level `guard (n ≤ k)` passes (`y ≤ Nat.pair a y ≤ k`, and
  `Nat.pair a j + (y − j) ≤ Nat.pair a y`); the base `cf` guard is free too, since
  `a ≤ Nat.pair a 0`. The live `none` sources in a `prec` simulation are: fuel `0`, the top
  guard, `cf`/`cg` *internal* failure, and `cg`'s own guard on the assembled argument
  `Nat.pair a (Nat.pair y i)` — which is genuinely unbounded by `n` and genuinely fails. No
  underflow test phase is needed. `rfind'` contrasts: its argument grows while fuel shrinks,
  so its guard failures are real.
- Failure **order** within a level is irrelevant to extensional agreement: every branch is a
  total `Option` computation, so an upward `prec` loop need not mirror the downward
  recursion's detection order, only its value.
- `Nat.pair` monotonicity for guard arithmetic is in Mathlib: `Nat.left_le_pair`,
  `Nat.right_le_pair`, `Nat.pair_lt_pair_left`, `Nat.pair_lt_pair_right`,
  `Nat.add_le_pair` (`Mathlib/Data/Nat/Pairing.lean:102–148`). Cite, do not re-derive.

**Layering in the executable machine side.**

- `Construction/Descriptions.lean` is indexed by machine **descriptions**, not machines:
  `LIACompiler` needs the enumeration to be primitive recursive, and a `Complexity.TM k`
  bundles its state type and its tapes as functions, neither of which `Primrec` can see.
- Executability (`Primrec`), polynomial-time soundness of each indexed computation, and
  coverage of every polynomial-time trader are three different facts, and the modules are
  split along exactly those lines. Making the primitive-recursive evaluator carry the
  complexity proof is the conflation to avoid.
- The semantic class and the enumeration are kept apart on purpose:
  `EfficientlyComputable` is not defined as "occurs in the enumeration"; that every member
  does occur is the content of `exists_enumeratedTrader_eq`.

**Renames — every name left of an arrow below is gone; grepping it finds nothing.** `buySeq_ec_rpn` →
`buySeq_ec`; `rpnSentenceCodes_bitPrefixSentence` →
`bigSentenceCodes_bitPrefixSentence`; `digitMachineCodes_twoPowMachine_not_polyMachineCodes` →
`digitMachineCodes_nest_not_polyMachineCodes` with the witness changed to
`Nat.Partrec.Code.nest`; `ratCodeFeature`/`toWeighting` moved up into `Framework`/`Properties`.

**Σ₁-soundness is assumed nowhere, and object-level exclusivity is what makes that
possible.** No declaration in `LogicalInduction/` takes a `SoundOnHierarchy` instance
*binder*: the elaborated `#check` census over the canonical endpoints reports 0 of 107, and
the only occurrence of the name in Lean source outside prose is `loopsTheory_soundOnSigma1`
(`Construction/Knowledge/Endpoints.lean`), an `inferInstance` fact about the *concrete*
witness theory for `thm:loops` rather than a hypothesis on anybody's `Θ`. What the quotation
layer needs — that the positive and negative quote schemas cannot both be proved at one
argument — is a **theorem of `T`**, not a fact about `ℕ`: the two schemas are the
value-`1`/value-`0` fibers of one Foundation `code` formula, `code_uniq` gives
single-valuedness in every model of `𝗣𝗔⁻`, and Gödel completeness turns that into
`T ⊢ ∼(pos ⋏ neg)`. The general lemma is `valueSchema_exclusive_prov`
(`Framework/Theory/QuoteRepresentability.lean`) and its quotation instance is
`universalQuote_exclusive_prov` (`Construction/Quotation/Packages.lean`); together they are
what lets `theoremDP_hworld` be *proved* from consistency of `T` alone
(`Construction/Paper/ComputationDP.lean`, whose header says so). The LUV provability world is
closed the same way, by publishing complementary literals over *one* sentence instead of two
schemas: `luvWorld_consistent` (`Construction/LUV/Presentation.lean`) elaborates
`[𝗥₀ ⪯ T] [T.Δ₁] [RepresentsComputations T] [Entailment.Consistent T]` and nothing semantic.
On the syntax side the `.mp`-only half of Foundation's `re_complete` is `re_complete_mp`
(`Construction/Knowledge/Syntax.lean`, `[𝗥₀ ⪯ T]` only), which is why the represented lanes
never acquire the instance either. Where a *semantic* world is genuinely wanted it is built
soundness-free: `paperPrimeWorld` (`Construction/Paper/FirstOrder.lean`) through
`Theory.small_satisfiable_of_consistent`. The historical record below says what this replaced
and which names to stop looking for.

**Charging rule for a Σ₁-soundness demotion.** A row is `qualified` iff *no*
canonical endpoint of that label renders the printed statement on the paper's own hypotheses.
No canonical endpoint needs the instance today, so nothing is charged on this rule; it is
recorded because it is the rule a future soundness binder would be judged by.
`thm:scon`/`wub`/`wubaff`/`wubexp` are the shape that makes it bite: each curates a
universal `_ofComputation` endpoint with no theory premise that *is* the printed theorem,
so the label stays `exact` even when some other carrier of it is heavier. The live tier
counts belong to `scripts/coverage-classification.md`'s `## Headline counts`, which
`scripts/check_endpoint_coverage.py` re-derives. Blast-radius method: `#check @name` over the
`LI-CANONICAL-BEGIN/END` names in one scratch file and read the *elaborated* signatures —
grepping is useless (100+ hits, mostly witnesses).

**`thm:loops`'s `hloops` witness is by axiom fiat, and why no natural theory discharges it
*here*.** `ComputationTheoryPresentation` has `boundedFailure_refutes` but no `halting_fails`;
bounded failure is r.e. with its own complementary schema, unbounded non-halting is Π₁. The
witness `loopsTheory := insert (∼σ) 𝗜𝚺₁` is consistent, Σ₁-sound, `Δ₁`, and discharges every
instance (`Theory.Delta1.insert`, `WeakerThan.ofSubset`, and `[ℕ ⊧* T] → T.SoundOn` gives
soundness *and* consistency free). **The reason a natural `T` (`𝗜𝚺₁`, `𝗣𝗔`) cannot be
exhibited is opacity, not impossibility**: Σ₁-soundness
does *not* forbid refuting a false Σ₁ sentence (that is proving a true Π₁ one, which `𝗣𝗔`
does routinely), and `incomplete_of_REPred_not_ComputablePred_Nat'` refutes only the
*uniform* negative principle, saying nothing about one instance — `𝗜𝚺₁` would refute a
natural arithmetization of `rfind' succ` diverging by a one-line induction. What blocks it is
that `universalHaltingSchema := codeOfREPred UniversalCodeHalts` is chosen by
`Classical.epsilon` (`R0/Representation.lean:232-247`), so the formula's shape is unreachable
from Foundation's API and the only bridges to `T ⊢` are positive. Three honest
strengthenings: a `halting_fails` field; Π₁-reflection on `T`; or a hand-rolled halting
formula with its own representability lemma . Do not spend prover time on it *with the installed substrate*.

**Widening a sentence-codes hypothesis.** A hypothesis used only via `.primrec`/`.exists_code`
can be widened `RpnSentenceCodes → BigSentenceCodes` (both classes have them). Consumers that
*block* widening: `.comp`/`.and`/`.bigOr` on the symbol-metered class, and anything
destructuring a `PolySegStream` (the conditioning compiler, `LUV.RpnThresholdCodeSeq`
producers: `Quotation/MarketQuoteCodes`, `Quotation/ProductDefinition`,
`SemanticExtension/Prime`, `SemanticExtension/Product`, `LUV/SourceCodec`). Never sweep the rename globally; widen the affine/trader lane and wrap
with `BigSentenceCodes.ofRpnSentenceCodes` at each Rpn-producer → Big-consumer site.
`thm:st`'s threshold premises are `SelfTrustQuote.product_codes` and `.confidence_codes`
(`Properties/SelfTrust.lean`), both at `LUV.MachineThresholdCodeSeq`; its sentence premise
`hφ` is `MachineSentenceCodes` and its rational premise `hd` is `MachineRatCodes`
(`Construction/Paper/Market.lean`).
`EfficientRepeatedEnumeration.ofMachineCodes` and `.ofCE` (`Construction/NonDogmatism/RepeatedEnumeration.lean`) are the two constructors; each keeps its own source argument and wraps internally.
**Strictness ledger (never reprove).** `not_polyFueled_two_pow`, `bigDigits_two_pow_not_polyFueled`,
`bigTokenStream_not_polySegStream`, `digitRatCodes_two_pow_inv_not_polyRatCodes`,
`bigSpliceStream_two_pow_inv_not_rpnSpliceStream`, `bigDigits_two_pow_not_polyNatCodes`,
`digitMachineCodes_nest_not_polyMachineCodes`, `not_polyNatCodes_ack`,
`not_polySentenceCodes_bitPrefixSentence`. `BigSentenceCodes ⊇ RpnSentenceCodes` has **no**
strictness proof (the canonical Polish route already admits exponential codes; only an
unbounded single token separates) — never describe it as strict. `BigDigits.primrec` and
`BigSentenceCodes.primrec` legitimately reassemble the whole value (`Primrec` has no time
budget); that is not a leak unless the result is used as a `PolyFueled`/`FP` certificate.

**`ofSource` design.** Peels `len4 n` base-16 digits, with tag 0 a no-op pad
(`sourceStep_pad`); `ofSource_peelSteps` gives the exact step count and
`sourceNat_peelSteps_le` bounds it by `2 * c.size`. The fuel-adequacy side condition the
roundtrip needs is `size_le_len4_sourceNat : c.size ≤ len4 c.sourceNat` — there is no lemma named
`size_le_sourceNat` anywhere in the tree. Linearity is an *inequality* (`len4_sourceNat_le : len4 c.sourceNat ≤
2 * c.size`) with the matching lower bound `pow_pred_le_sourceNat`.

**`ofDigits_div_pow_mod`** (`Framework/Emission/CodeSource.lean`) duplicates `ofDigits_digit`
(`Construction/NonDogmatism/PrefixMachine.lean`, downstream, cannot import upward); the Framework one is more general.
Delete PrefixMachine's if the dependency direction ever permits.

**Cleared suspicions — verified, do not re-raise.** `GeneratedRatFeature.rank_le : (feature n).rank ≤ n`
is exact under the day shift (`EF.price φ j` denotes `V j φ` at Lean day `j`; do not 'fix' to
`≤ n+1`). `ofSource`'s garbage→`zero` convention is unexploitable: claim names are
`Nat.pair (sourceNat m) x`, only the first component is decoded, `ofSource_sourceNat` makes it
exact, `sourceNat_injective` keeps machines on distinct atoms. `DUSThresholdEmission`'s
whole-value `PolyRatCodes` fields are inhabited because the dovetail's stage table is
clock-truncated (`dusApprox_polyRatCodes`), argued not-charged at the `thm:dus` row.
`SelfTrustQuote.product_reflected`/`confidence_reflected` are discharged at
`lic_self_trust_closed` (`Construction/Quotation/MarketQuoteCodes.lean`), one level above the `_ofRepresentation`
layers. `bitStringEnumeration` and `Dovetail.dusString` are literally the same definition
(hence `hB := fun _ ↦ rfl`). `lem:conluvapprox` is assigned to
`Properties/ExpectationConvergence.lean` by the coverage map; the `Expectations.lean` mentions
are prose-only by design. The `_closed` canonical endpoints for `thm:epr/ref/st` live in
`Construction/Quotation/MarketQuoteCodes.lean`, not `Construction/Paper/ComputationDP.lean`.

**`ofSource` is a correctness decoder; its cost is what its own lemma says.** It peeled `n`
digits from the value `n` — that would be ≥ 2ᵏ steps for `nest k`; the
repaired decoder peels the digit count. `Primrec` carries no time budget — never cite a
`Primrec` lemma as evidence of efficiency.

**The metering taxonomy has three tiers, and the middle one is easy to mislabel.**
Whole-value (`PolySentenceCodes`, `PolyRatCodes`, `PolyNatCodes`, `PolyMachineCodes` —
`IsPolyBounded` on the Gödel value); per-token-value-metered, called "symbol-metered" in
older prose (`RpnSentenceCodes`, `RpnThresholdCodes(Seq)`, `PolySegStream` — poly many
tokens, each of poly *value*); write-out (`BigSentenceCodes`, `BigDigits`, `DigitRatCodes`,
`DigitMachineCodes`, `BigTokenStream`/`BigSpliceStream` — poly many tokens, individual
tokens unbounded). `BigSentenceCodes` lives in `Framework/Emission/WriteOut.lean`, not `RpnSplice.lean`.

**Where the LUV-threshold class enters the §4 tail.** Follow the metering through the
structures, not the binder list: `AffineCombination.PolySequence.sentence_poly` is
`MachineSentenceCodes` and `LUVCombination.PolySequence` is only `mesh_poly`, so
`LUVCombination.BoundedSequence` carries no threshold hypothesis at all (thm:loe,
thm:expprovind, thm:prandexp are clean); `LUVCombinationSyntax.threshold_poly` is what
carries the class into the `_ofSyntax` endpoints (`Construction/LUV/Syntax.lean`), at
`LUV.MachineThresholdCodeSeq`, as is `thm:ei`'s own `hcode`; `thm:ec`'s `hcode` is the
non-sequence `LUV.MachineThresholdCodes`. thm:ceu/thm:ref construct their threshold codes.
Nothing here is at a token- or write-out class, so no row is charged for the threshold
rendering.

**`thm:loe`'s coefficients are `a b : ℕ → EF`, not `ℕ → ℚ`, and storing `.const (a n)` is a
real narrowing rather than a spelling.** `lic_linearity_of_expectation_seq` /
`linearityLUVComb` (`Construction/LUV/Endpoints.lean`) build the combination's terms as
`[(a n, X n), (b n, Y n), (.const (-1), Z n)]` and read the coefficient value the way
`LUVCombination.expect` does, `(a n).denote P`. The reason is the emission certificate:
`AffineCombination.PolySequence.coefficient_poly` serializes the coefficient **EF**, so
wrapping a rational as `.const (a n)` makes the trader write out that rational's *digits*,
which excludes ℙ-generable sequences with short features and long values — `2^(−2ⁿ)` by
repeated squaring is the paper's own kind of example (`def:ece`, tex:1218, tex:1701). The
rational form is the instance `fun n => .const (a n)`, so the `EF` statement is strictly
more general and no rational corollary is kept. The fixed-`X Y Z` sibling
`lic_linearity_of_expectation` deliberately keeps `a b : ℚ`: it fixes two numbers rather
than ranging over generable sequences. Since a feature denotes a real, the sequence form
also covers `def:ece`'s ℝ-sequence case (tex:1220), a strengthening over the printed
rational quantifier. The general trap: **whenever a coefficient reaches an emission field,
check what that field serializes before writing `.const (`.**

**Sparing rule for a charged class.** A row is spared iff some shown
endpoint is BOTH instance-free AND at the paper's printed hypotheses; "not the curated
endpoint" is a curation fact and never a reason. `lic_learns_halting_patterns` takes
`RepresentedSemidecidableClaims` — the conclusion of the paper's representability step
handed in as data — so thm:halts/loops/dontwait stay demoted for Σ₁-soundness, while
thm:scon/wub/wubaff/wubexp's universal endpoints take the paper's own truth bridge and are
spared.

**Compiler-guided instance removal must go in import order.** `lake env lean` on a
downstream file elaborates against the STALE olean of the file just edited, so a removed
upstream instance is still visible and the downstream check passes for the wrong reason.
Regenerate each olean before moving downstream. And after any bulk regex rewrite, grep for
the old name: `[^)]*` silently skipped two nested-paren `(x := Nat.pair …)` sites.

**The inventory contract is fail-closed both ways.** `check-paper-nodes.sh` rejects any
`#assert_axioms_clean` member without a `Paper node` line; `check_endpoint_coverage.py`
requires the `LI-CANONICAL-BEGIN/END` region to equal the classification's endpoint set.
Internal supporting lemmas therefore cannot be inventoried; they are named in the carrier's
block note and axiom-checked by `#print axioms` blocks (`DigitMachineCodes` / `CodeSource`
supports).

**`PolySegStream` on the arithmetic-formula codec is a LENGTH condition.** Its per-token
value clause is vacuous along the `PaperLUVSeq` route because the emitted-token audit pins
every token to a constant (`encodeArithmeticFormulaSymbols_lt`: payload `< 19`;
`structuredPaperPrimeBlock_span`: framing `0/1/19`), so `PolyArithmeticFormulaSeq` equals
write-out there. The Gödel code is built by parser contraction and never emitted. The
residual `dd:fuel` charge is separate and levied at def:ec only.

**Compact numerals in ℒₒᵣ.** `binNumeral : ℕ → Semiterm.Const ℒₒᵣ` (Horner over `0/1/+/·`,
`Construction/LUV/SourceCodec.lean` §Compact numerals) has `binNumeralEnc_length_le : ≤ 8·log₂ v + 7`
tokens — derived from the sharp form `binNumeralEnc_length : = 16 · binNumeralLen v - 9`
via `binNumeralLen_le_log`, so quote the sharp one when the constant matters — and
`binNumeral_val` (value `v` in every model of `𝗣𝗔⁻`). Define compact numerals as
`Semiterm.Const` operators, not raw terms, so `!!d` and the `Rew`-normal form behave like
the unary numeral code. `invFormula`/`invPaperLUV` is the shared `1/d` template (unique/unit
proved once); `unitFracPaperLUV` and `dyadicPaperLUV` are instances. A poly-fueled count of
a repeated fixed-width token block is `PolySegStream.blocks` — the combinator that makes a
superpolynomial VALUE emittable when its NAME is a repeating pattern.

**Substitution lemma.** `polyArithmeticFormulaSeq_subst_arg` IS proved
(`Construction/Knowledge/SubstEmission.lean`) for an arbitrary closed-term stream `τ : ℕ → Semiterm.Const ℒₒᵣ` with an
arity-quantified emission certificate; the feared `bShift`/`Rew.q` obstruction is discharged by
Foundation's `@[simp] Rew.const : ω c = c` for closed operator constants. The earlier entry claiming
it was blocked was wrong and cost time.

**Two different 'source language' ideas — do not conflate.** A binary-numeral source node
was REJECTED (it admits strings the paper's def:ec writer cannot produce in poly time — a
permissive widening; numerals are already compactly nameable inside ℒₒᵣ via `binNumeral`).
The `iff`/`imp`/`neg` formula-source language is the repair that was taken for `dd:nnf`: `⟺`
is one of the paper's primitives, so restoring it costs no permissiveness. Route into `thm:ec`:
`PaperLUV.machineThresholdCodes` (`Construction/LUV/ArithmeticSource.lean`) takes a single
literal paper LUV into the non-sequence `LUV.MachineThresholdCodes`, which is exactly
`LUV.expect_converges`'s own hypothesis — no embedding step in between.

**`[𝗜𝚺₁ ⪯ T]` on the arithmetic-theory endpoints is a SECOND strengthening beyond the paper.** It exists only because `provable_instances_re` (`Construction/Paper/ComputationDP.lean`)
proves r.e.-ness of `{φ | T ⊢ φ}` through Foundation's internal `Bootstrapping.Provable` +
`definability` + `internalize_provability`, which need `𝗜𝚺₁`. On the r.e. lane the binder is UNUSED — instance-free restatements of
`provable_instances_re`, `paperTheoremFires_re`, `exists_paperTheoremCode` compile axiom-clean, because the
proofs instantiate `V := ℕ` and `internalize_provability`/`Provable.sound` need `ℕ ⊧* 𝗜𝚺₁`, not `𝗜𝚺₁ ⪯ T`.
Removal = targeted binder deletion + import-ordered propagation; the instance IS load-bearing in
`Construction/LUV/PaperLUV.lean` (rational-cut arithmetic inside `T`) and at `thm:lp`'s
diagonal, which is where it survives today; `QuotationTheoryPresentation` no longer has a
theory-strength field for the closed quotation endpoints to inherit it from. A derivation-enumeration codec is NOT needed (it would require an `Encodable` for Foundation's
`Derivation2`, absent — an upstream project). Disclose beside the Σ₁-soundness charge until removed; `[T.Δ₁]` (= the
paper's c.e. axiomatization) is representation infrastructure and stays.

**Part II plan — `RepresentsComputations T` renders tex:600-606 directly** (for every
total computable `f`, `∃ γ, ∀ n y, y = f n ↔ T ⊢ ∀⁰ (γ/[n̄,#0] 🡘 “#0 = ȳ”)`). The negative
literal `T ⊢ ∼γ/[z̄,1̄]` from the representation at value 0 compiles under `[𝗥₀ ⪯ T]` alone
(`R0.Ω₃` gives `T ⊢ 0̄ ≠ 1̄`; `Theory.Proof.specialize` for ∀-instantiation; Foundation has NO
external ∃-introduction for `T ⊢`). Under Style 1 the composite `n ↦ evalWithin(m,x,f n)` is one
total function, so the deferred-horizon compound and the whole `UniversalBoundedFailure` apparatus
were deleted rather than ported, and none of those names resolves today. Architectural risk: an existentially given `γ` has no source text, so the
structured emitter cannot write it symbol-by-symbol and `theoremDP`'s fixed-schema c.e. route
breaks — exits: `paperTheoryDP` (enumerates all provable propositions), or keep the fixed
`codeOfREPred` schema with a Style-2 negative field that IS the paper's tex:4515 premise instance.
Concrete instantiation: revive Foundation's commented `codeAux_uniq`/`code_uniq` (stated for every
model of `𝗥₀`) + `models_code` + completeness ⇒ `RepresentsComputations 𝗥₀` ⇒ `𝗜𝚺₁`, `𝗣𝗔` —
a DIFFERENT object from the ruled-out `codeOfREPred` strong representability.

**The paper's formula source language** (`Construction/LUV/ArithmeticSource.lean`):
`ArithSource k` (leaf/and/or/all/exs/not/imp/iff), `compile` into Foundation NNF (`not/imp/iff` by
`∼/🡒/🡘`, rfl), `ofNNF := .leaf` (compile ∘ ofNNF = id and sourceTokens ∘ ofNNF =
encodeArithmeticFormulaSymbols, both rfl), `SourceEval` with a genuine metalevel `↔` at `iff`
(spelling it `(→)∧(→)` would trivialize the correctness theorem), `eval_compile`, tags 20/21/22
for not/imp/iff (19 stays the reserved terminator; the conditioning automaton clamps at 20 so they
are opaque payload), roundtrip `parseStructuredArithmeticFormula_sourceTokens`, and the
source-metered class `PolyArithmeticSourceSeq` — the paper's def:ec class on formulas.
`PolyArithmeticFormulaSeq` remains as the strictness foil (`PolyArithmeticFormulaSeq.toSource`
embeds it). `negFormulaCode` (De Morgan involution on Foundation formula codes) lives in
`Framework/Criterion.lean`, its spec in `ArithmeticSource.lean`, and its `Primrec` proof `negFormulaCode_prim` is public in
`Construction/Primcodable.lean`. The Gödel code of an n-deep `iff` source is ~2^(2^n) and is never emitted —
the same trade as `Code.sourceNat`; no value-metered class may ever sit on this path.
`parseStructuredArithmeticFormula_consumed_lt` now concludes `x ≠ 19` (was `< 19`).

**Literal-LUV frontend lives in `Construction/LUV/ArithmeticSource.lean`** (moved from `Construction/LUV/SourceCodec.lean`,
an earlier pass; import direction forces it — `ArithmeticSource` imports `StructuredPaperRpn` for the
encoders and round trips). `PaperLUVSeq = ⟨luv, source : ℕ → ArithSource 1, compiles, structural :
PolyArithmeticSourceSeq source⟩`; threshold body is a source `imp` node (`paperThresholdSource`),
which deleted the whole `negArithTok` token-map lane. `RpnThresholdCodeSeq` unchanged (Option 1).
Capstone `iffPaperLUVSeq`/`iffPaperLUVSeq_frontend`: formula `invFormula (numeral 1) ⋏ iffChain (2n+1)`
(odd chain is valid by parity ⇒ no-op conjunct; `invPaperLUVWith` is a SIBLING of `invPaperLUV`,
not a generalization — the latter's formula must stay literally `invFormula d` for the numeral
encoding lemmas). The family is constant in VALUE (1) and varies in written size — it witnesses
the metering class, not value variation (`unitFracPaperLUVSeq` and `dyadicPaperLUVSeq` do that). Strictness ledger addition:
`iffChain_not_polyArithmeticFormulaSeq` now reads as `PolyArithmeticFormulaSeq ⊊ PolyArithmeticSourceSeq`.

**`RepresentsComputations T`** (`Framework/Theory/RepresentsComputations.lean`) renders
tex:600-606 verbatim: `∀ f, Computable f → ∃ γ, ∀ n y, y = f n ↔ T ⊢ ∀⁰ (γ/[n̄,#0] 🡘 “#0 = ȳ”)`.
Derived: `represents_proves`, `represents_refutes` (negative literal at a substituted instance),
`represents_refutes_all` (∀-form), `RepresentsComputations.consistent` (the paper's line-604 remark —
no separate consistency carry needed), `reprBody`/`reprAll`/`reprAllSchema` (the claim family IS
the numeral-instance family of ONE fixed schema, so `provable_instances_re` enumerates it even
though γ is existential). Instantiated at `𝗣𝗔⁻`, `𝗜𝚺₁`, `𝗣𝗔` (`Framework/Theory/R0Instances.lean`,
`representsComputations_of_peanoMinus` via a local restatement of Foundation's commented
`code_uniq` + `models_code` + completeness) — NOT at `𝗥₀` (no trichotomy ⇒ the `rfind` case of
single-valuedness fails). Wrong belief corrected: existentially supplied formulas block neither
c.e.-ness (`provable_instances_re` takes φ as a parameter) nor emission (`PolySegStream.constList`
accepts any fixed list) — opacity only blocks uniformity over a FAMILY of formulas. Represented
claims are carried by `paperTheoryDP` (every provable proposition; no fixed schema); choose the
day-n claim at value 0 (`∀⁰(γ(n̄,ν) ↔ ν = 0̄)`) so `paperPrimeDecompose` yields literal
complements with no double negation. LUV lane migrated: `thresholdSchema T := reprAllSchema
(thresholdGamma T) 0`, `luvWorld` is the provability world, `luvWorld_consistent` from consistency;
`truthWorld` is the standard-truth world still used by `gridDP`. Two spellings of the soundness
instance coexist (`𝚺 1` and `SigmaSymbol.sigma 1`) — grep `SoundOnHierarchy` alone.

**Part II outcome.** Tag 3 (bounded claims) closes from consistency: the represented
claim family's def:ec certificate is built on the SOURCE language (`Construction/Knowledge/SubstEmission.lean`:
`reprBodySource = .iff (.leaf γ(n̄,ν)) (.leaf (ν = 0̄))`, wrapped `.exs (.not …)`, emitted by
`structuredPaperSourcePrimeBlock true`; the bridge to `representedClaimSentence` is rfl), and
`thm:dontwait`/`thm:pac`/`thm:pazfc` live in `Construction/Knowledge/Endpoints.lean` over `paperTheoryDP T`
under `[T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗥₀ ⪯ T] [RepresentsComputations T]` — no soundness.
`paperTheoryDP_nonvacuous` was ALWAYS soundness-free (needs only `[Entailment.Consistent T]`).
Retired: the whole `UniversalBoundedFailure` apparatus. Dead-but-inhabited surface for a
consolidation pass: `UniversalBoundedHalts`, `universalBoundedHaltingSchema`, `theoremDP` tags 2/3,
`ComputationTheoryPresentation.boundedHalting_enters/boundedFailure_refutes` (no consumer now).
**The quotation tag closes from consistency, and the 'architectural obstruction'
diagnosis of it is simply wrong.** The universal quote evaluation never needed a
`RepresentsComputations` γ (per-decider ⇒ paper-prime atom ⇒ import reorganization — every step
after the first was unnecessary). It has a Foundation `code` formula (`Nat.ArithPart₁.exists_code`,
which takes a PARTIAL `Nat.Partrec'`), and ONE such formula carries both literals as two value fibers:
`Framework/Theory/QuoteRepresentability.lean` `valueSchema c y := (code c)/[‘↑y’, #0]`,
`universalQuotePos := valueSchema universalQuoteCode 1`, `universalQuoteNeg := … 0`;
`valueSchema_prov` (`[𝗥₀ ⪯ T]`, both literals by Σ₁-completeness — the negative as cheap as the
positive) and `valueSchema_exclusive_prov` (`[𝗣𝗔⁻ ⪯ T]`, proved semantically in one shot:
`Arithmetic.complete` + `code_uniq` + `numeral_inj_iff`). `theoremDP_hworld`'s quotation tag (tag **5** in the gapless `0`-`5` event space) closes from
`Entailment.Consistent` like the halting and bounded-halting tags, so every endpoint that
would otherwise inherit a soundness binder carries `[Entailment.Consistent T]` instead
(the elaborated binder census is in `AxiomAudit.lean`), and `thm:lp` survives the
arrangement because the schemas are compile-time constants.
**Σ₁-soundness is on 0 of 107 canonical endpoints**; the only `SoundOnHierarchy` left is
`loopsTheory_soundOnSigma1` (concrete witness theory). General lesson: when two schemas must be
provably exclusive, reach for ONE `code` formula read at two values, never for two `codeOfREPred`s
or a `RepresentsComputations` γ. `QuoteRepresentability.lean` now owns the single copy of
`codeAux_uniq`/`code_uniq`. So "Σ₁-soundness is a live strengthening" is not true of this lane.

**Instantiation asymmetry of `RepresentsComputations`.** `representsComputations_of_peanoMinus`
takes `[𝗣𝗔⁻ ⪯ U]` AND `[ℕ↓[ℒₒᵣ] ⊧* U]` — standard-model truth VERIFIES the premise for the
registered instances (`𝗣𝗔⁻`, `𝗜𝚺₁`, `𝗣𝗔`) and is used by no consumer. A Σ₁-unsound theory such as
`𝗣𝗔 + ¬Con(𝗣𝗔)` satisfies the paper's assumption but is not witnessed here (a syntactic proof of
representability without the standard model would be needed — a Foundation-upstream item).
`check-paper-nodes.sh` blocks inventorying an unannotated interface or supporting lemma; such
lemmas are covered transitively by the annotated endpoints (same ruling as for the other supporting layers). `dd:nnf` now names an
architecture, not a substitution.

**Public atom tag inventory.** The authoritative table is the docstring of
`ComputationClaimKind.godelCode` (`Construction/Knowledge/Syntax.lean`), which allocates every
value `0`–`7`: `0`/`1` computation claims, `2` quotation (`quotationClaimCode`), `3`
`productTag`, `4` `semanticPrimeTag`, `5` `paperPrimeTag`, `6` `oldLanguageTag`, `7`
`bitAtomTag`. Every "atoms are fresh for tag X" lemma is a case split over that table
(`Construction/Quotation/ProductDefinition.lean`, `Construction/SemanticExtension/Product.lean`,
`Construction/SemanticExtension/LanguageCopy.lean`, `Construction/Paper/TheoremDP.lean`), and
the two tag-ownership lemmas those splits open with now live with the atom families they are
about: `sentenceAtomCodes_computationClaimSentence` in `Construction/Knowledge/Syntax.lean` and
`sentenceAtomCodes_quoteAtom` in `Construction/Quotation/Packages.lean`. `semanticPrimeTag` and
`SemanticPrimeFreshSentence` are declared beside the table for the same reason: the
first-order lane has to prove its own compiled atoms avoid the tag, and holding them there is
what lets `Construction/Paper/FirstOrder.lean` import `Knowledge/Syntax.lean` instead of
`SemanticExtension/Prime.lean` — the edge that used to put the whole `Paper/` lane downstream
of the semantic-extension lane, and is now cut.

**A formula-metered atom CAN carry a machine/input pair — as a compact numeral (CORRECTED
2026-08-30).** The constraint is on the substituted term's TOKEN RUN (must be a `PolySegStream`),
not on its VALUE: Foundation's unary `numeral` costs its value, but `binNumeral` (now base-4 uniform
Horner, two constant-width runs driven by `len4`/`dig4`) costs O(log v), so a `BigDigits` value
stream is admissible — `polySegStream_binNumeralEnc (hv : BigDigits v)`. This is exactly how the argument-term repair
was fixed: `haltingArgClaimSentence machines inputs n := universalHaltingSchema/[binNumeral
(haltingClaimInput (mₙ) (xₙ))]` and, for the bounded lane, ONE γ per horizon program for the
universal decider `universalRunValue steps` at `binNumeral (boundedArg machines inputs n)`; value
transfer by `provable_subst_iff_of_val` (completeness both ways, needs only `𝗣𝗔⁻ ⪯ T`).
`hm`/`hi` are load-bearing (deleting them breaks the `BigDigits` certificate). Anti-vacuity:
`haltingArgClaimSentence_ne_of_halts_ne`, `representedClaimSentence_ne_of_runValue_ne`. Why base 4:
`PolySegStream.blocks` needs a constant block width; base-2 Horner branches on parity.

**EXTENSIONALITY TRAP — the single most dangerous failure mode on the represented lanes.** Foundation's
`codeOfREPred (A : ℕ → Prop)` and `RepresentsComputations.repr f` depend only on the EXTENSION of the
predicate/function. A claim family built as `codeOfREPred (fun n => P (mₙ) (xₙ))` or `repr
(boundedRunValue …)` collapses to one fixed sentence family as soon as an endpoint hypothesis pins the
extension (`∀ n, halts` ⇒ `fun _ => True` by funext+propext; `hnever` ⇒ const 0; `hconsistent` ⇒
const 1) — the sentence then names NO machine and the e.c. hypotheses `hm`/`hi` are provably decorative.
The `paperTheoryDP` rendering of `thm:dontwait`/`thm:pac`/`thm:pazfc` (and of `thm:halts`/`thm:loops`) once did
exactly this, and five vacuous renderings passed two audits as improvements. The paper's sentence names the machine (`⌜m⌝`, `⌜f⌝(⌜n⌝)`, tex:606/1931). Correct design:
represent the UNIVERSAL evaluator once (one γ per horizon `f`, or the fixed universal r.e. halting
schema) and write the pair `Nat.pair (sourceNat mₙ) xₙ` into the sentence as a compact
`binNumeral` (O(|source|) tokens — what `BigDigits` bounds), emitted digit-by-digit from the
`BigDigits` certificate. Standing test for any represented claim family: substitute two sequences with
the same extension but different programs — if the sentences coincide, the rendering is extensional.

**Machine dependence, as it now stands.** Machine dependence of the §4.9/§4.10 sentences is
DEFINITIONAL (`binNumeral (haltingClaimInput (mₙ) (xₙ))` substituted into a fixed schema; `binNumeral`
and `sourceNat` injective), and `hm`/`hi` are the only route to `sentence_poly` — but the two
anti-vacuity lemmas (`haltingArgClaimSentence_ne_of_halts_ne`, `representedClaimSentence_ne_of_runValue_ne`)
separate sentences only when BEHAVIOUR differs; the full "same extension, different program ⇒ different
sentence" statement is true but unprovable with the installed substrate: it needs a syntactic
substitution-injectivity/occurrence lemma (σ mentions `#0` ⇒ `σ/[t] ≠ σ/[t']` for `t ≠ t'`), absent from
Foundation (`Foundation/FirstOrder/Syntax` has no `subst_injective`). It is now in the repo (see the next entry): a local proof by induction on formulas, and an
upstream candidate. Argument-INsensitivity of the opaque schema IS
refutable from `universalHaltingSchema_spec` (non-constant `UniversalCodeHalts`).
`[T.Δ₁]` (a Δ₁ axiom SET) is strictly stronger than the paper's "c.e." — Craig's trick gives a deductively
equivalent Δ₁ axiomatization, so every `T ⊢`-statement transfers, but that is not formalized; disclosed
as representation infrastructure (a global charge, and a judgment call). Day indexing is ℕ from 0 while
the paper's is ℕ⁺: a day-indexed premise must hold at day 0 too — the retired `ordinaryBoundedComputation`'s
`0 < n` predicate failed there and could not witness `hconsistent` (that carrier is deleted; the point stands). `thm:pac` and `thm:pazfc` were, at this point, the same theorem by `rfl`
at every layer, which the two-theory Con family separates. thm:dontwait's γ represents the
COMPOSITE decider `universalRunValue f` (⌜g⌝(⟨⟨m,x⟩,n⟩) ≠ 0), not `f` alone — no new hypothesis.

**`[𝗜𝚺₁ ⪯ T]` does not reach `provable_instances_re`'s consumers** — all but the four endpoints
named in `LogicalInduction/README.md` are free of it: the r.e. lane never needed it — `internalize_provability`/`Provable.sound` are
instantiated at `V := ℕ`, so the side condition is `ℕ ⊧* 𝗜𝚺₁`, and `definability` needs only `T.Δ₁`.
Represented lane and `theoremDP_hworld` now read `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`
(`𝗥₀` is strictly too weak for `provable_subst_binNumeral_iff`; `𝗜𝚺₁ ⪯ T` gives `𝗣𝗔⁻`/`𝗥₀` by
instance search but `𝗥₀ ⪯ T` does NOT give `𝗣𝗔⁻ ⪯ T`). Genuine survivors: `unitFracPaperLUV*`
(rational-cut arithmetic INSIDE `T`), `thm:lp` (Foundation's `parameterized_diagonal₁` lives at
`𝗜𝚺₁`); the seven closed quotation rows carried it only through the field
`QuotationTheoryPresentation.theory_sigmaOne` (two consumers, both on the diagonal) — moved to a
binder on those two lemmas. **Substitution injectivity is now in the repo:**
`Framework/Theory/SubstOccurrence.lean` (`Semiformula.Mentions`, `rew_eq_of_not_mentions`,
`eq_of_rew_eq_of_mentions`, `subst_injective_of_mentions`, Foundation-only imports; the
occurrence-restricted refinement of `rew_eq_of_funEqOn`); `universalHaltingSchema_mentions_zero`;
and the FULL anti-extensionality test is a theorem: `haltingArgClaimSentence_ne_of_source_ne`
(distinct `sourceNat` ⇒ distinct sentence, no behavioural hypothesis, invocable inside one family);
bounded lane `representedClaimSentence_ne_of_arg_ne` takes `γ.Mentions 0` as a hypothesis (γ is
existential). Foundation has `Semiterm.bv` but no formula occurrence notion and no
`bShift_injective` (derive via `Rew.map_inj (Fin.succ_injective n) Function.injective_id`).
`Scratchpad.lean` at the repo root is TRACKED — never use it as scratch.

**Ruling (Anson): `thm:lp`'s `[𝗜𝚺₁ ⪯ T]` is representation infrastructure.** The paper
invokes "the diagonal lemma" for any theory representing computations; Foundation's
`parameterized_diagonal₁` is stated at `𝗜𝚺₁`, so the instance is the ambient theory of a borrowed
lemma, not a strengthening of the theorem's premise. Charged once globally beside `[T.Δ₁]`
(Craig's trick) — neither lowers a row. With Σ₁-soundness gone and the r.e.-lane `𝗜𝚺₁` deleted,
the eleven quotation/computation rows classify `exact`, and so do the §4.10 three
(`thm:pac`, `thm:pazfc`, `thm:incons`): no theorem row is `qualified` today.

**§4.10 substrate map (all names `#check`-verified).** Paper `Con(Θ′)(ν)`
(tex:1855-1866) ↔ `¬∃ d < ν, Bootstrapping.Proof T d ⌜(⊥ : ArithmeticSentence)⌝` at `V := ℕ`
(`Bootstrapping/Syntax/Proof/Basic.lean:465`); `⌜Θ′⌝` ↔ `⌜U.Δ₁ch.val⌝ : ℕ` (`Theory.lean:13,18`);
soundness bridge `Bootstrapping.provable_of_standard_proof` (`RosserProvability.lean:52`; at `V := ℕ`
bridge `↑n` with `Nat.cast_id`/`simpa`, set `maxHeartbeats`). A COMPUTABLE bounded-derivability decider
needs no proof checker: `Proof.definable'` gives both polarities, so `∃ d < k, Proof T d ⌜⊥⌝` and its
negation are `𝚺₁-Predicate` by `definability`, then `re_iff_sigma1` + `ComputablePred.computable_iff_re_compl_re`
(compiled). Measure = derivation Gödel number, not symbols (no size function on internal derivations;
`Semiformula.bv` is the only template) → proposed `dd:proofcode`. TRAP: represent bounded PROVABILITY
(φcode in the argument), never bounded consistency — constantly 1 for every consistent Θ′, so the γ would
not name the theory. Put the DAY in the argument; evaluate `f` inside (f may be Ackermann). `thm:incons`
needs uniform-in-theory-code derivability, which Foundation lacks (`Derivation T` takes `T` as a META
parameter via `(construction T).Fixpoint`); the honest restriction is the deduction-theorem family
`Θ′ₙ := Θ₀ ∪ {σₙ}` (`Theory.Δ₁.insert`), inconsistent ⟺ `Θ₀ ⊢ ∼σₙ`, uniform in `⌜σₙ⌝` — disclosed
paraphrase; decorative naming is rejected. Where the paper uses one sentence and its negation (tex:1863-1866), a rendering with two
DISTINCT tagged claim atoms would need collapsing via `paperPrimeDecompose`; `ComputationClaimKind`
carries no such pair, so nothing here has to. `RestrictedProvability.lean` has no olean in this checkout and is not needed.

**`QuotationTheoryPresentation` carries no `theory_sigmaOne` field** (its fields are
`toComputationTheoryPresentation quote_positive_enters quote_negative_refutes`), so the seven
closed quotation endpoints read `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]` and
`lic_introspection_closed` instantiates at `𝗣𝗔⁻` itself, where no `𝗜𝚺₁` instance exists in the
elaboration at all. The diagonal's two consumers take an ordinary `[𝗜𝚺₁ ⪯ T]` of their own;
`thm:lp` prints a redundant `𝗣𝗔⁻` beside it, because `omit` cannot drop a referenced section
variable. The binder census itself lives in `AxiomAudit.lean` and the endpoints carrying
`𝗜𝚺₁ ⪯ T` are named in `LogicalInduction/README.md`, where `scripts/check_li_rollcall.py` gates
them. TRAP: `𝗜𝚺₁ ⪯ T` is spelled
`[ISigma 1 ⪯ T]` across the semantic-lifted lane (64 sites) — grep BOTH spellings (likewise
`PeanoMinus`/`R0`). Foundation registers the weakening chain as instances (`𝗣𝗔 ⪯ T → 𝗣𝗔⁻ ⪯ T`,
`𝗜𝚺₁ ⪯ T → 𝗣𝗔⁻ ⪯ T`, `𝗣𝗔⁻ ⪯ T → 𝗥₀ ⪯ T`): state the single strongest binder a proof spends.
`Construction/Freeze/Counterexample.lean` keeps `𝗜𝚺₁` in a section variable, because its
`cxQuote` runs the diagonal; the lane's canonical endpoint `not_overgeneral_ifp` mentions no
theory, so the binder is not included in it. Touching
`Construction/SemanticExtension/Quote.lean` costs ~1h per rebuild (`SemanticExtension/Registry.lean` and
`SemanticExtension/Endpoints.lean` at
`maxHeartbeats 2000000`, silent for ~20 min).

**Read the binder census from the elaborated signatures, never from a grep** — the word "Consistent"
alone matches `PCWorld.ConsistentWith*` and inflates several-fold, and `𝗜𝚺₁ ⪯ T` has a second
ASCII spelling. The census itself is taken and recorded in `AxiomAudit.lean`'s *Concrete
arithmetic instantiation* note; do not keep a second copy here. **`[𝗣𝗔⁻ ⪯ T]` is a genuine strengthening
beyond the paper**: representability yields `Θ ⊬ n̄ = m̄` but never `Θ ⊢ n̄ ≠ m̄` (Ω₃); Robinson's R
represents all computable functions without containing 𝗣𝗔⁻. It is load-bearing for exactly two
things — `provable_subst_iff_of_val` (the compact `binNumeral` spelling def:ec forces) and
`code_uniq`'s `rfind` case (object-level exclusivity at the quotation tag, tag 5; the PAPER's exclusivity is
metatheoretic via the representability biconditional's ← direction and needs no Θ-arithmetic; ours
is object-level to keep the stage-world proof constructive without soundness). Never write that
𝗣𝗔⁻/𝗥₀ is "presupposed by representability". Also: `RepresentsComputations` is over `f : ℕ → ℕ`
where the paper is ℕ⁺→ℕ⁺ (at-least-as-strong; disclosed); `valueSchema`'s `code c` carries the
VALUE at `#0` and the ARGUMENT at `#1` — opposite of the `reprAll` convention (hence `swapArgs`);
[Historical record — resolved by construction; the single market is `paperDP`:] the canonical surface once ran three markets (`theoremDP` 13, `paperTheoryDP` 6, `canonicalCCEEDP` 1 at the canonical block (2026-08-31 recount; 86 abstract))
while the paper fixes one 𝕡. The union, `paperDP`, is the market; the question is closed.


**The propositional rendering of `Con(Θ)(ν)` is a NEGATED atom, and this is forced, not chosen.** `representedClaimSentence γ t` is the paper-prime of `reprAllTerm γ 0 t`; `paperPrimeDecompose (reprAllTerm γ 0 t) = ∼representedClaimSentence γ t`, because a universal sentence is not prime and its ∃-negation is. So `conClaimSentence γ n := ∼representedClaimSentence γ (binNumeral (conClaimArg n))`, and the DP publishes it through `paperDP_covers_representedClaim_neg` (`Construction/Knowledge/Endpoints.lean`) (from `T ⊢` the value-0 sentence). Do not reach for the un-negated atom: that one is "the bounded search SUCCEEDS" and would give `≈ₙ 0`, not the paper's `≈ₙ 1`.

**Stage (ii) shape for thm:pazfc, from the stage-(i) substrate.** `BProv`/`conWithin`/`conRunValue` already take the theory as an ordinary parameter, so `conRunValue T' horizons` represented IN `T` is the whole construction — no new substrate. The one genuinely new obligation is the positive literal: `conWithin_of_consistent` gives truth of the `T'` claims from `Consistent T'`, and `RepresentsComputations T` converts truth into `T ⊢` since the decider is total computable. Stage (ii) needs NO soundness premise — only `Entailment.Consistent T'` as an explicit hypothesis on the second theory, exactly the paper's own premise for Θ′.

**[Correction worth keeping: the paper NEVER assumes `Θ ⊆ Θ′` — tex:1881-1886 says 'any recursively axiomatizable consistent theory'; the Lean statement MATCHES the paper's hypotheses, and no 'more general than the paper' claim is earned. The remainder of this entry records the (sound) dependency analysis only.]** Verified unused: `conRunValue_computable` needs only `[T'.Δ₁]`, `RepresentsComputations T` is about T, `conWithin_of_consistent T' hcons` about T′ — no step relates the theories. Dropping it strengthens the theorem in the harmless direction and keeps typeclass assumptions minimal; disclosed in the endpoint docstring ("More general than the paper"). Do not "restore" it as a fix — the inclusion is what makes the paper's result *interesting* (why Θ cannot prove Con(Θ′)), not what makes it true; the 𝗜𝚺₁/𝗣𝗔 example carries that interest concretely.

**[All seven of the superseded carriers are deleted; `thm:pac`/`thm:pazfc` each have one carrier.]** Verified by grep (list): Zero consumers apart from `#print axioms`/`AxiomAudit`: `alwaysBoundedComputation`, `ordinaryBoundedComputation` (`Construction/Knowledge/Syntax.lean:670,648`), `BoundedComputation` (`:596`), `representedDecidableClaimsOfComputation` (`Construction/Knowledge/Endpoints.lean:541`), `lic_belief_finitistic_consistency_ofComputation` (`:752`), `lic_belief_stronger_theory_consistency_ofComputation` (`:773`), abstract `lic_belief_stronger_theory_consistency` (`Properties/MetaLearning.lean:80`). CONTRAST: `lic_belief_finitistic_consistency` (`MetaLearning.lean:66`) is LIVE — both `_unconditional` endpoints route through it. No separate `consistentWithin` definition exists; `conWithin` is the live §4.10 predicate. Retirement also shrinks `AxiomAudit.lean:848,1012-1014` and `#assert_fields BoundedComputation` at `:1284`.

**The LI-CANONICAL block is a curated view, not the superset of the topical `#assert_axioms_clean` blocks.** Retiring seven declarations named only in topical blocks changed the LI-CANONICAL count by zero: LI-CANONICAL names exactly what `scripts/coverage-classification.md`'s endpoints table names (enforced two-way), while topical blocks are internal axiom regressions. Before budgeting a census-prose edit for a retirement, check which block the name is in; measure with `sed -n` between the real marker lines — an `awk /BEGIN/` sweep also matches the prose mentions of the markers and silently inflates the count.

**`thm:incons` does NOT charge `dd:proofcode`.** Its sentence is the *unbounded* existential over proofs (the paper's `⌜Θ′⌝ is inconsistent` is the negation of the universal generalization of `Con(Θ′)(ν)`, tex:1863-1866): nothing is metered, so the symbol-count-vs-Gödel-number substitution does not arise. If any ledger text charges it there, drop it.

**The `thm:incons` theory sequence is the deduction family `Θ′ₙ := Θ₀ ∪ {σₙ}`, disclosed.** The paraphrase stands as a disclosed charge, backed by a verified obstruction rather than by an unfinished plan.** Forced by Foundation: `Bootstrapping.Derivation T` is `(construction T).Fixpoint` with `T` a META parameter — no uniform-in-theory-code derivability predicate exists, so a sequence of theories cannot enter one sentence as an argument. The deduction theorem collapses the day's theory to one sentence code, which is genuinely named. 

**Write-out class for a sentence-code family goes on the NEGATION codes.** The day's sentence writes out `⌜∼(σ n)⌝`, so a `BigDigits` premise belongs on *that* family rather than on `fun n => ⌜σₙ⌝`. Deriving it from `BigDigits (fun n => ⌜σₙ⌝)` is NOT free: `∼` on arithmetic `Semiformula` is NNF recursion, not the propositional `φ 🡒 ⊥` that `BigSentenceCodes.neg` exploits. Foundation has a code-level negation with a Σ₁ graph (`neg L`, `negGraph L`, used by `Theory.RosserProvable`) if it is ever needed.

**The `thm:incons` witness is constant in the day (`σₙ := ⊥`), a considered choice.** A day-varying refutable family needs `BigDigits` for formulas containing the day's numeral (digit-count over unary numerals, well over 50 lines). Day-variation of the rendering is a theorem instead: `inconsistencyArgClaimSentence_ne_of_arg_ne` separates any two distinct adjoined-axiom codes with no behavioural hypothesis.

**[Historical record — the premise is now `PolyArithmeticSourceSeq` on the written source.]** Before that change, `hσ : BigDigits (deductionFamilyArg σ)` was strictly stronger than `def:ec`: `BigDigits` bounds a base-4 digit count — the paper's write-out meter only when the number IS the object's written form. `⌜∼σₙ⌝` is a formula's Gödel code; Foundation's encoding pairs at every node, so digits ~ 2^depth — the same failure mode that disqualified `Encodable.encode` as a machine-naming map. The class admits only O(log n)-depth families and EXCLUDES paper-admissible short-source/deep-parse (`iffChain`-style) ones. SECOND charge on the thm:incons row, beside the deduction-family paraphrase. Faithful repair: state the premise on `PolyArithmeticSourceSeq` (`polySegStream_binNumeralEnc` already admits the family); queued with the 9-series.

**Naming a token run: digit concatenation with a sentinel, never a pairing tree.** `tokenListNat ts := Nat.ofDigits 64 (ts ++ [63])` — base 64 = 4³ (base-4 digit theory transfers) and fits the alphabet `0..18, 20..22`; sentinel `63` is above every alphabet, so injectivity, no lost high digit, and a decoder terminator. Base-4 digit count `3·len + 3`, linear in the written text. Same doctrine as `Code.sourceNat`.

**Efficiency lives on the emission side only; the decoder may be slow.** `negSourceFormulaCode` runs inside the represented predicate, where only r.e. is asked — `tokensOfNat` may scan `List.range (v+1)` with no `PolyFueled` certificate. All `def:ec` content: `PolyArithmeticSourceSeq` → `sourceNat` → `BigDigits` → `polySegStream_binNumeral_const`. Conflating the two sides is what made the code-metered premise look necessary.

**A `BigDigits` primitive-recursion combinator is not worth writing** — its only intended consumer, a code-digit certificate for a day-varying `thm:incons` family, is mooted by the source route. Related `Primrec` trivia: `tokensOfNat`'s foldr IS `takeWhile (· ≠ 63)` in the shape `Primrec.list_foldr` accepts (a literal `takeWhile` breaks the proof); `(· ^ ·)` needs `Primrec₂.unpaired'.1 Nat.Primrec.pow` (no `Primrec.nat_pow` in Mathlib).

**`dd:proofcode` is RETIRED, replaced by `dd:symbolcount` — a convention, not a substitution.** §4.10 meters the paper's own quantity (symbols, inclusive bound). Residue: the paper fixes neither encoding nor alphabet, so a counting convention was chosen — one symbol per rule name/connective/quantifier/predicate/function symbol/variable occurrence, one separator per argument-list entry, and the WRITTEN BINARY DIGIT LENGTH (`idxLen`) of every index. The index clause is FORCED: counting `^&x` as one symbol makes the measure infinite-fibred (unboundedly many derivations of count 1) and the negative polarity undecidable. Any residual error over-counts, so `conWithin T k` is if anything WEAKER — never stronger. The glossary bullet was REPLACED, not stubbed (consolidation rule; the convention is a live decision deserving a live entry).

**The trick that makes the converse bound cheap: ill-formed codes get their own value** (`dSize n = n` on the junk branch), so `n ≤ G (dSize n)` is unconditional and the induction never threads `IsUFormula`/`Derivation` well-formedness through four layers. The junk branch is unobservable — every use sits under `Bootstrapping.Proof`. Bounding only well-formed codes was abandoned; it costs the whole side-condition apparatus.

**Mode-packed single WF recursion beats `mutual` for size functions over code trees:** `tvAux : ℕ → ℕ → ℕ`, `termination_by` the second arg, projections `tSize n := tvAux 0 n` etc. Know: (a) the strong-induction proof must quantify the mode (`∀ n mode`, induct on `n`, `intro mode` inside); (b) projection equation lemmas need `rw [tvAux]` + trailing `rfl`, and `have … from rfl` inside `rw [show …]` diverges in whnf — hoist to top-level lemmas.

**Retiring a global `dd:` marker does not move any row** — residuals live in the justification cell, never the status column, so `thm:pac`/`thm:pazfc` are `exact` either way, and the tier counts do not move. And a retired marker must NOT leave a "retired" stub bullet in the README modeling boundary when its replacement is a live design decision — the stub reads as structural evidence of a previous version; item 4 stays live, relabelled "Convention, not substitution".

**`thm:incons` reaches `exact` through an external, compact rendering, which sidesteps the uniformity obstruction rather than contradicting it.** The design: day-theories presented by `m : ℕ → Nat.Partrec.Code` enumerating `ArithSource.sourceNat` names of axioms; `theoryOf m := {σ | ∃ b i s, evaln b m i = some s.sourceNat ∧ compile s = ↑σ}` (surjective onto r.e. sentence sets, since `ArithSource.ofNNF` writes every sentence); represented predicate `∃ b, ProvableCode ∅ (negSourceFormulaCode (combineSourceNats (axiomOutputs (Code.ofSource z) b)))` — r.e. via `Partrec.rfind`+`dom_re` over the COMPUTABLE `ProofPacked ∅` (no r.e.-projection lemma exists in Mathlib — verified absence); premises `hm : DigitMachineCodes m` + `hinc : ∀ n, ¬Consistent (theoryOf (m n))`. RETIRES the deduction paraphrase outright; drops `T'`, `[T'.Δ₁]`, `σ`, `s`, `hs`, `hcompile`; `_mentions_zero` loses its `Consistent` hypothesis. Estimated ~1200-1600 lines / ~20-28 cycles; riskiest step = the base-64 token-splice `combineTokens`/`combineSourceNats` + primrec (delegable, disjoint file). One un-verified spelling: the `∃ w` rfind projection + S4 conjunction bridge (blocked behind a build lock at probe time) — "very likely", tactic-spelling risk only. This entry is the durable record.

**Conjoin written formulas at TOKEN level, never at code level.** `sourceTokens (.and a b) = 15 :: (sourceTokens a ++ sourceTokens b)` — folding a list of sources into a conjunction is list concatenation, and `parseStructuredArithmeticFormula_sourceTokens` already takes a suffix argument. The repo exposes NO code-level `⋏` constructor with a spec (only `negFormulaCode`); building one would re-import the `Nat.pair`-squaring defect that source metering exists to avoid.

**`dd:machinetheory` (new live glossary bullet):** the presentation convention reading a machine as a theory — outputs are `sourceNat` names of axiom SOURCES; an output naming no source contributes nothing; the budget-b window at inputs `is` is `is.map (fun i => (evaln b m i).getD verumSourceNat)`. Convention, not substitution (same status as dd:symbolcount): SURJECTIVE onto the r.a. theories via `ArithSource.ofNNF`, and the paper never defines "recursively axiomatizable".

**A token-whitelist junk-guard is WRONG, is not in the landed code, and should not be re-derived.** Junk-mapping-to-⊤ needs the parser to DECIDE "names a source", which parse success cannot certify (grammar completeness unproved). The working design: the window takes an explicit INPUT LIST (`axiomWindow z w` maps over `Denumerable.ofNat (List ℕ) w.unpair.2` with `.getD verumSourceNat`), so the truth direction CHOOSES good inputs and the window is literally `ss.map sourceNat` — junk never enters the spec; `combineTokens` is a bare foldr. Collapsed the memo's riskiest step to ~170 lines / one cycle.

**Why `theoryOf` is NOT realigned to parser semantics, though that is the first design one reaches for.** `parseStructuredArithmeticFormula` returns a CODE, ignores its depth argument, accepts the free-variable tag, and the development has no parser-completeness theorem — so parse-consumed-everything cannot yield `⌜σ⌝` for any sentence; closing the converse through the parser would need parser fuel-monotonicity + a parse-append lemma (neither exists) + a Foundation `Provable T x → ∃ σ, x = ⌜σ⌝` (does not exist). A purpose-built recognizer whose soundness is a RECONSTRUCTION theorem keeps `theoryOf` at its paper-facing spelling, leaves every splice lemma applicable, and delivers the full iff. A `validTokens`-style guard hits the same wall.

**Coverage-through-witnesses pattern:** `#assert_axioms_clean` members must carry `Paper node:` lines, so internal downstream layers can't be asserted directly without bogus annotations. When the layer is downstream of a universally-quantified endpoint, assert an APPLIED WITNESS whose STATEMENT names the layer — genuinely transitive coverage (precedent: `loopsTheory`). Adding endpoints under an existing label does not disturb the README headline counts (per-label).

**`[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are both charged globally** — decision briefs live in classification § *Arithmetic-theory hypotheses* → *Representation infrastructure, charged once and never per row* and README § *The residuals, named once*; rows carry ONE standard pointer sentence and no argumentation. Do not reintroduce per-row binder discussion. Row-specific facts retained deliberately: `[T'.Δ₁]` at thm:pazfc; thm:lp's separate `[𝗜𝚺₁ ⪯ T]` paragraph (a different binder; it carries the omit-rejection fact). The app:incons erratum (tex:4487-4491) is the load-bearing justification that 𝗣𝗔⁻ is not foreign to the paper — cite it as the proof's gap, not the statement's.

**One idiom, one home — where the shared machinery lives.** Grep the home before
re-proving; several of these had two to four copies.
* `Framework/Emission/Computable.lean`: the whole `IsPolyBounded` closure algebra (`of_le`, `linear`,
  `max`, `add_one`, `pair`, `add`, `mul`, `const`, `const_mul`, `monomial`,
  `isPolyBounded_id`, `isPolyBounded_fst/snd`, `comp`); `evaln_isSome_mono` (every dovetailing
  process's stage-monotonicity step); `list_range_map_sum` (the `List.range`/`Finset.range`
  sum bridge — it replaced a private duplicate of the same fact in `Framework/ROI.lean`);
  `length_flatMap_eq_segPrefix` / `getD_flatMap_of_prefix`, now generic in the element type,
  which subsumes `AffineCombination`'s `_any` pair; and `Primrec.of_courseOfValues`,
  `Primrec.nat_strong_rec` with its dummy parameter discharged.
* `Framework/Criterion.lean`: `PCWorld.holds_atom/top/neg/or/and` (the Boolean payout laws —
  none of them `@[simp]` at the declaration; `Construction/Paper/ComputationDP.lean`
  marks `holds_atom` and `holds_neg` `simp` for the deductive-process lane, which is the
  scope the old in-file `holds_atom`/`holds_not` had); `payout_mem_Icc`;
  `EF.streamReadFrom_none`; `ComputableMarket.ofComputableTable`, the constructor every
  concrete market witness wants.
* `Framework/Asymptotics.lean`: `asympGE_zero_of_const_mul_pos`, `asympLE_…`, `asympEq_…`.
* `Framework/ROI.lean`: `ROIBudget.prodFeatures` and its four laws, beside `sumFeatures`.
* `Framework/Emission/RpnSentence.lean`: `parseRpn_strip` (one copy; `StructPat`'s is gone),
  `first19_split_unique`, and the *generic* `UnRpnContractsTo` algebra (`of_eq`, `single`,
  `payload`, `nil`, `self`). The **raw-combinator** half (`constTok` … `lowerSafeRecipTok`)
  cannot live there: it is stated over `Construction/Conditioning/Compiler.lean`'s `raw…Tokens`, so it
  lives beside them.
* `Construction/Statistics/SettlementCompiler.lean`: `encode_toFinset_eq`, beside
  `encode_eq_encode_stageSort` and `stageSort`, which it needs. `Construction/LIACompiler.lean`
  (PLAN's stated home) cannot see those.
* `Properties/Support/Exploitation.lean`: `exploits_of_ge_partialSums_from`, the partial-sums
  engine whose
  lower bound starts at day `k`; it is what lets a derivability hypothesis be the paper's
  `∃ k, χ ∈ DP.D k` rather than the day-0 `∀ n, χ ∈ DP.D n`.
  `Properties/Support/Exploitation.lean` imports
  `Framework/Affine.lean` for `Trader.abs_netWorth_le_partialMagnitude`, which bounds the
  finitely many pre-`k` days.
* `UnRpnContractsTo.unRpn_eq` now concludes `unRpn ts = out`, not `unRpn ts = out ++ unRpn []`;
  its seven consumers no longer strip the tail by hand. Its proof needs `simpa [unRpn_nil]` —
  `unRpn_nil` is not a `simp` lemma.
* Deleted with no replacement: `strategy_ext_trades` (`Construction/Conditioning/Compiler.lean`) — it is
  `Strategy.ext`, which is `@[ext]` in `Framework/Criterion.lean`.

## Intentional deviations from the paper

The standing modeling choices are the `dd:*` labels in `LogicalInduction.lean`. Which
boundary, if any, a given paper node carries is recorded in that node's own row in
`scripts/coverage-classification.md`; `LogicalInduction/README.md` explains the categories.
Entries there are not audit findings unless the justification itself is wrong.

- **`CertifiedSourceLUVSeq` has no inhabitant, and its satisfiability is open.**
  (`Construction/SemanticExtension/Source.lean`.) Three of its four fields are routine;
  `cut_certificate : SourceCutCertificate DP toLUV` asks every world consistent with the
  completed theory to rationally cut every member of the family at a caller-chosen `DP`, and
  the naive universal route is REFUTED by `no_nonvacuous_worldValued_presented_of_rpn`
  (`SemanticExtension/Prime.lean`). An inhabitant would have to name a specific process with
  the cut property. Everything stated over the structure is therefore conditional on a caller
  supplying one; the interface is proof-carrying by design, not vacuous by oversight. Its
  knock-on is closed: `presentedLUVSeq e` inhabits `PresentedLUVSeq` unconditionally at any
  emitter schema, so `PresentedLUVSeq` does not depend on the open question.
- **The licence for `EF`'s `letE`/`var` sharing (`dd:dsl`) is a paper footnote, and citing it
  is what keeps the extension from reading as an undisclosed enlargement of `def:ec`.**
  tex:788, under `def:tf`: "expressible features are a generalization of arithmetic circuits.
  The specific definition is somewhat arbitrary; what matters is that expressible features be
  (1) continuous; (2) compactly specifiable in polynomial time; (3) expressive enough…".
  Sharing enlarges `EfficientlyComputable` relative to a literal tree reading, hence
  *strengthens* `IsLogicalInductor`, so the direction is safe; the citation is what makes it
  disclosed rather than silent.
- **`FeedbackTruthComputation.computes` is a relaxation of tex:1251, and `DeferralFunction.graph_fp`
  is an equivalent of tex:1243.** The asymmetry is deliberate and permanent (`Complexity.FP`
  has no linear-time form); it is set out at *The two output-sensitive clocks* above and must
  not be flattened into one sentence.
- **Machine naming is not Mathlib's `Encodable.encode`**. `encodeCode`
  emits `2*(2*Nat.pair (encode cf) (encode cg))+4` per `pair`/`comp`/`prec` node, so the value
  *squares* per node: for `nest 0 = zero, nest (n+1) = pair (nest n) zero` (`2n+1` nodes) the
  base-4 digit counts are exactly `0, 2, 4, 8, 16, 33, 67, 134` (`#eval`-verified). The paper
  admits `nest` (poly time to write the source); `BigDigits ∘ encode` excluded it. Machines are
  therefore named by the linear `Code.sourceNat`. This is a representation choice of the same
  kind as RPN for sentences, disclosed at `DigitMachineCodes` and `sourceNat`; the user's
  ruling is that it classifies `exact`, with no obligation to formalize that all reasonable
  programming languages are polynomially equivalent.
- **Σ₁-soundness would be stronger than the paper's hypothesis, and no endpoint takes it.**
  The paper assumes Θ consistent, c.e., and *represents computations*
  (tex:600-606, tex:993-997) and treats soundness as a *further* assumption (tex:2673);
  its §4.9 proofs use Σ₁-completeness and consistency only, so a `[T.SoundOnHierarchy 𝚺 1]`
  binder would be a strengthening rather than a rendering — never write that it is what the
  paper assumes. The instance is on **0 of the 107 canonical endpoints**; the only
  `SoundOnHierarchy` left in Lean source is `loopsTheory_soundOnSigma1`, an `inferInstance`
  fact about a concrete witness theory. The charging rule is kept for a hypothetical future
  binder, not applied to anything today.
- **The `dd:fuel` charge is levied once at `def:ec`** as a *certification device*, not as a
  modeling substitution: no `evaln` clock survives in any paper-facing statement, so the
  `def:ec` row is `exact`. A downstream row not repeating the caveat is not a defect.
- **`strengthened` compares against the PRINTED statement, and against nothing else.**
  A Lean statement stronger than some *other declaration in this development* — a bare
  existence form, a fuel-class projection, a variant that assumes what the canonical form
  derives — is `exact`, not `strengthened`; the contrast with the weaker sibling belongs in
  the row's prose. Two rows drifted onto the internal comparison and were ruled back to
  `exact` on 2026-09-06: `thm:affpolymax` (bare `BoundedCombinationSequence`, which *is*
  `def:bap`; the contrast was with `PolySequence.affpolymax`) and `thm:li` (the `def:belseq`
  emission conjunct; the contrast was with `exists_logical_inductor`). The five
  that survive and what each actually weakens: `thm:scon` drops §4's standing consistency
  assumption on `Θ` (tex:993-997, carried elsewhere as the stagewise `hworld`) — **not**
  universality over an inductor, which the printed form has too; `thm:nd` weakens the
  syntactic `Θ ⊬ ∼φ` to the stagewise world condition the paper's own appendix derives from
  it (tex:2933), the printed limit conclusion being proved outright by
  `lic_exists_limit_pos`; `lem:tfdom` weakens `def:belstate`'s computable finite-support
  belief states to a bare exactly-rational `[0,1]` history — **not** the exploiter class,
  since `EfficientlyComputable` *is* `def:ec` at the paper's meter; `thm:benford` weakens
  the printed "all `𝗣`-generable divergent weightings" to the additionally
  `DeferralPatient` ones; `thm:lp` constructs the paradoxical sequence the printed statement
  assumes. Counts after the ruling: 45 exact / 5 strengthened / 2 corrected / 1 refuted /
  0 qualified over 53 theorem-and-lemma nodes.


**`thm:pac` and `thm:pazfc` are NO LONGER the same theorem;** the `rfl` example recording their identity has been deleted. `thm:pac` is now about the arithmetized `Con(Θ)` family at Θ itself; `thm:pazfc` (pre stage-ii) still takes a caller-supplied `BoundedComputation`. `lic_belief_finitistic_consistency_ofComputation` survives unchanged and still carries `Paper node: thm:pac`, A node may legitimately have several carriers; the checkers do not object.

**`dd:proofcode` is a live type-`(c)` substitution disclosed globally** (ledger *Global model disclosure*, README modeling-boundary item 4, `LogicalInduction.lean` glossary): §4.10's finite proof searches are metered by the derivation's Gödel number, not the paper's symbol count, because Foundation's internal derivations expose no size function (`Semiformula.bv` measures a formula, not a derivation). Charged once globally on the `dd:fuel` precedent rather than against `thm:pac`, which is why that row reads `exact`. Queued for retirement by the Foundation symbol-measure work.

**The paper has NO `Θ ⊆ Θ′` hypothesis in `thm:pazfc`** — tex:1881-1886 assumes only "a stronger consistent recursively axiomatizable theory" (the "stronger" is informal prose). Every repo passage claiming the Lean statement is "more general than the paper" for omitting containment asserted a premise the paper never had; the Lean statement MATCHES the paper's hypotheses. No `.lean` docstring, ledger row, README line or `LI_READING` note asserts it.

**There is no two-valued `thm:incons` witness, and none is needed.** `alternatingInconsistentAxiom`/`thm_incons_applied_alternating` would exist only because the code-metered class could not admit an unboundedly day-varying family; `deepInconsistentSource n` is distinct on every day and `inconsistencyArgClaimSentence_deep_ne` separates every pair — keeping the dominated witness would be structural evidence of a previous version. `deductionFamilyArg_ne_of_ne` (quote injectivity) → `ArithSource.sourceNat_ne_of_sourceTokens_ne` (naming-map injectivity, no quotation needed).

**The `thm:incons` endpoint docstring records the obstruction at the declaration:** the deduction-family paraphrase STANDS as a disclosed charge backed by a verified obstruction, not a queued repair; the middle rendering is an optional upstream item pending a user ruling; earlier retire-later claims withdrawn.

**The `def:ec` lower-calibration obstruction, stated sharply: the open half is open on a WORKSPACE bound, not on a missing compiler — and nothing on the paper surface waits on it, so the `def:ec` row is `exact`.** At the *value*-metered target the converse is FALSE, not open: `Complexity.FP f → ∃ c, PolyFueled c f` is refuted in-repo by `not_polyFueled_two_pow` together with `n ↦ 2^n` binary-from-unary being FP (PolyFueled bounds VALUE, FP bounds LENGTH). At the *length*-metered target it is open, and the reason is structural. At a FIXED code `c`, `PolyFueled c f` says `f` is computed by a fixed finite `evaln` program in which every value ever handled is at most `poly n` — `O(log n)` BITS — because `evaln`'s `n ≤ k` guard caps every value passed to a sub-code by the fuel and `IsPolyBounded` caps the fuel and the output, and the code being fixed makes the `prec`/`rfind'` nest constant-depth. That is a **poly-time, O(log n)-workspace** device; `Complexity.FP` is poly-time with POLYNOMIAL workspace. So `MachineTokenStream t → BigTokenStream t` says every poly-time write-out over tally inputs is a logspace write-out — a **P-versus-L-flavoured containment**, a complexity conjecture rather than a lemma, and equally not refutable here. **A TM → `Nat.Partrec.Code` compiler carrying fuel accounting would NOT close it**: even a perfect compiler yields a code whose `evaln` run needs fuel at least as large as the configuration VALUE, `2 ^ Θ(poly n)` for a poly-length tape window over complexitylib's four-symbol alphabet. Cobham's `comp` case is a SYMPTOM of that bound, not an independent obstacle, and a polynomial step count does not help — step count buys fuel, and the guard needs fuel ≥ the intermediate VALUE. The bound is visible in the class's one loop combinator: `PolyFueled.prec`'s `hst` bounds the iterated state's VALUE where `FPFold.foldlBits_mem_FP`'s `hbnd` bounds its LENGTH, and the two signatures sit side by side as `example`s in `Framework/Machine/WriteOutMachine.lean`. A SECOND, INDEPENDENT gap stands behind it: `BigTokenStream`'s middle conjunct `(blockSplit (ds n)).2 = []` is not supplied by the machine reading, and truncating to the last complete block is a bounded maximization the `PolyFueled` suite has no combinator for. **Two plausible-looking claims about this are FALSE and must not be re-acted on: (a) "no proof anywhere that a TM step function is `Primrec`" — `primrec_codedStep` (`Construction/Descriptions.lean`) is exactly that, with the whole clocked lane `Primrec` (`primrec_stepFrozen`, `primrec_runUntilHalt`, `primrec_evalHalted`) and the output extractor `primrec_codedOutput`; the claim holds of upstream Mathlib and complexitylib, not of this repo. (b) "`LUV.BigThresholdCodeSeq` doesn't exist" — it is in `Framework/Expectations.lean` with `LUV.BigThresholdCodes` beside it and both `.toBig` embeddings, though every structural threshold carrier is at the machine pair and nothing binds the write-out one.** What upstream really lacks: Mathlib has only code→TM (`Turing.PartrecToTM2`, explicitly without step accounting) and `TM2ComputableInPolyTime` has the identity as its only inhabitant plus a `proof_wanted` composition; complexitylib has ~zero `evaln` contact. The reachable direction was the FP mirror of the emission suite, not the converse; that mirror exists in full (see *The machine readings of the write-out tier* above), every canonical endpoint is stated over it, and the converse stays out of reach. Census, over the 107 canonical endpoints: **zero** carry a `Big*`/`Rpn*`/`Digit*`/`Poly*` data binder, printed or through a boundary structure; 22 print `MachineSentenceCodes` (23 occurrences), and the only fuel-typed names left on the canonical block are `PolyFueledTrader` and `PolyFueledTrader.toEfficientlyComputable`, the `def:ec` calibration carriers themselves rather than data premises of anything. Exactly five structures library-wide carry a fuel-metered field — `DigitRatCodes`, the two ROI maturity schedules, and the two whole-value foils `PolyMachineCodes`/`PolyNatCodes` — and none is reachable from a canonical endpoint. Any note quoting a "64 of 105" fuel-binder census, or `BigSentenceCodes`/`BigSpliceStream` endpoint counts, is describing a surface that no longer exists.

**CORRECTION to the `code_uniq` story (QuoteRepresentability.lean docstring + earlier KNOWLEDGE entries): Foundation's `codeAux_uniq`/`code_uniq` were ORIGINALLY over 𝗣𝗔⁻.** Commit `593d63d8` ("Redefine Tait-Claculus", #130, 2024-09-01) block-commented the `section model` block AND weakened its ambient theory 𝐏𝐀⁻→𝐑₀ in one stroke; at `2a76397a` the block was live with `[M ⊧ₘ* 𝐏𝐀⁻]`. The 𝗥₀ text now visible is dead code that never compiled (the `rfind` case needs `<` linear). LI's revival RESTORES the original hypothesis — the docstring currently oversells the change as ours; fix it in the next .lean pass.

## Paper errata

`notes/paper-errata.md` is the ledger. The one a reader must know before using §4.6: the
published `thm:ifp` is **false**, and the repository proves it false; what is available is
the corrected finite-support theorem `FreezeOracle.lic_iff_of_finiteSupport`, with
`lic_iff_of_recognizableSupport` / `lic_iff_of_noReservedSupport` as strictly weaker
corollaries. **Neither the corrected theorem nor the refutation covers the paper's own
illustration of the node** — "completely ruin its beliefs on the 23rd day" (tex:1526) is a
whole pricing row, hence infinitely many `(day, sentence)` coordinates, outside
`FiniteSupportPerturbation`; and `not_overgeneral_ifp` is existential, exhibiting *one*
tail-agreeing perturbation that breaks the criterion rather than proving every whole-row one
does. That is a coverage gap inside a well-disclosed erratum, not a further defect, and it
should not be read off the node table as "fully accounted for".
The refutation is real rather than an artifact of the Lean rendering: the printed proof
(tex:6046-6050) claims "only finitely many constants `p_i(φ)` are needed, and can be
hard-coded into `F`", which is false because for each `i < N` the trader's later strategies
mention unboundedly many `φ`; and `not_overgeneral_ifp` negates the statement at exactly the
paper's own quantifiers (`ComputableMarket` is `def:marketprocess`).

## Pitfalls

**A WRONG BELIEF that stood in this library for a long time, and the shape of its repair.** The
claim was that a `MachineDigits` certificate on a *rational* value stream needs an arithmetic
normal form for `Encodable ℚ`'s `Denumerable` bijection, so an unboundedly-many-valued
feedback stream is out of reach. It is false, and was false when written: `MachineDigits`
meters the SYMBOLS a poly-time writer emits, never the magnitude of the value written, so an
unbounded value stream is no harder than a constant one. `ratNatCast_machineDigits`
(`Properties/OccamBounds.lean`) certifies `k ↦ (k : ℚ)` from any ruler via
`encode_rat_natCast : ⌜(n : ℚ)⌝ = ⟪2n, 1⟫`, and `MachineRatCodes.toMachineDigits`
(`Framework/Machine/WriteOutMachine.lean`) is the general route for a freely varying rational
stream; neither needs a fuel certificate. **The methodological point is the expensive one:**
the first repair narrowed the claim from "no non-constant certificate" to "no unbounded
certificate" — which *looked* like a fix, read as diligence, and passed review while still
being false. When retiring a disclosure, check whether the residue is true, not merely
smaller.

**A metering census that scans for class NAMES cannot see an inline clock.** Both
output-sensitive clocks were spelled as bare `evaln` bounds inside a structure field rather
than as a named `PolyFueled` class, so every name-based scan reported the surface clean. The
complementary check is a scan for interpreter contact in a field's *type* — and it must search
`evaln` **case-insensitively**, or name the wrappers explicitly: `codeEvalnNat` has a capital
E, and that single-letter gap hid `CEEnumeration.outputs_sound` from the census through
several rounds. Run that scan before asserting any strengthened census sentence. Its two
current survivors, `LowerSemicomputableContinuousSemimeasure.approximation_computes` and
`CEEnumeration.halts`, are `∃ fuel, …` — semicomputability and c.e.-ness, the paper's own
conditions, with no polynomial bound and hence no metering claim.

**A checker can pass for the wrong reason after a demotion.** `lint_paper_labels.py` requires
every `theorem` in a paper library to name a node, so demoting a `theorem` to `lemma`
*silences* that requirement rather than satisfying it. The two-way gate is
`check-paper-nodes.sh` (inventory → annotation) plus `check_endpoint_coverage.py`
(annotation → inventory), and only names in an `#assert_axioms_clean` block are covered by it;
`check-paper-nodes.sh` additionally requires every inventoried member to carry a `Paper node:`
line, so demoting an inventoried declaration forces a choice between dropping it from the
inventory (losing axiom checking) and adding a justified name to that script's **exempt
table**. That table is the sanctioned way to inventory a declaration that must NOT carry an
annotation (refutations, non-vacuity witnesses, repo-side computability interfaces); it is
checked both ways, so it is self-cleaning. TRAP: it lives in a `cat > … <<'EOF'` heredoc and a
`#` comment line INSIDE the heredoc is read as a name and fails as a stale exemption — put
commentary above the `cat`. A demotion also drops the name out of any statement-freeze
snapshot keyed on the `theorem` keyword, silently — record it wherever that snapshot is kept.

**`LUV.MachineThresholdCodeSeq X` unfolds to
`MachineSentenceCodes (fun m => (X m.unpair.1).gt (i/k))`.** So for any family that ignores
the threshold, `hφ.comp UnaryRuler.unpairFst` IS a threshold certificate, definitionally —
that is the whole proof of the day-varying APITests example and the skeleton of
`LUV.indicatorOf_machineThresholdCodeSeq`. For the indicator the branch test is the ruler
`((i+1) - k) * k`, which vanishes exactly when `k = 0` (where `i/k = 0 < 1`) or `i < k`: the
`* k` factor is what handles division by zero, and omitting it silently gets the `k = 0` case
wrong. Threshold indices are `i/k ≥ 0`, so the `r < 0` branch of any indicator family is
unreachable and the dispatch is two-way, not three-way.

**A constructed indicator whose `[0,1)` threshold is literally `φ` turns `thm:ei` into an
identity, and the identity is invisible in the Lean statement.** `𝔼ₙ` averages the prices of
the thresholds at the grid points `i/(n+1)`, `i < n+1`, every one of which lies in `[0,1)`;
at `gt r := φ` that average is `(1/(n+1))·∑ Pₙ(φₙ) = Pₙ(φₙ)` for *every* market, so
`AsympEq (fun n => (Y n).expect P n) (fun n => P n (φ n))` holds by arithmetic and the
`[IsLogicalInductor]` binder does no work — while the statement still reads exactly like the
paper's. The rendering that keeps the content is a threshold **propositionally equivalent to
`φ` and syntactically distinct from it**: `LUV.indicatorOf φ` uses `φ ⋏ ∼∼φ`, so
`IsIndicator` holds in every world with no deductive-process hypothesis (`holds_and` +
`holds_neg` twice, then `tauto`), the codes follow from `φ`'s by `MachineSentenceCodes.and`
and `.neg`, and a market may still price the two sentences apart. Two facts keep this
honest and must be kept beside any such construction: `LUV.indicatorOf_gt_ne`, the
term-level `≠` (proved from `LO.Propositional.Formula.complexity` — `φ ⋏ ∼∼φ` is three
connectives bigger — since `simp`/`decide` will not see the inequality), and
`expectation_indicator_not_identity`, a two-point market refuting the conclusion off the
criterion. Without the second, nothing on the gate distinguishes the good construction from
the degenerate one.

**The compact conditioning interface cannot carry a process that grows at every day, and that
is a recorded obstruction rather than laziness.** `CompactConditioningProcessComputation`
needs `MachineSentenceCodes (fun n => deductiveStageCondition (extra.D n))`, and
`deductiveStageCondition` is `(extra.D n).toList.conj₂`: a `Finset` stage erases the index
order the emitter needs (`Finset.toList` order is recoverable only from exponential Gödel
codes, and `conj₂` is not permutation-invariant). Growth at every day is reachable only
through `ConditioningPresentation.condition` in index order — `prefixProcess` +
`lic_conditioned_growing_ofSequence`. So `growingConditionProcess` changing exactly once is
forced by the interface, and prose describing it as strictly growing is describing the other
route.

**`thm:loops` cannot get a client at `Code.nest`, and the reason is not schema opacity.**
`codeHalts_nest` proves those machines halt; Σ₁-completeness then gives `T ⊢ σ` for each
halting instance, so `hloops : ∀ n, T ⊢ ∼σₙ` contradicts the ambient
`[Entailment.Consistent T]` — the premise is unsatisfiable and such an example exhibits
nothing. The separate schema-opacity story (a `codeOfREPred` schema is `Classical.epsilon`-
chosen, so no natural `T` can be SHOWN to refute a particular false instance) is true, but it
is about `loopsTheory`'s premise, not about this one. Do not let the two arguments swap places.

**`Cobham.iterate_mem_FP` cannot express a bounded loop whose step needs a PARAMETER.** Its
step is `F : List Bool → List Bool` applied to the state alone, so a cap, a day index or any
other `z`-derived datum is invisible to it unless smuggled into the state and re-projected
every iteration. `FPFold.foldlBits_mem_FP` is the combinator that has this: its step is
applied to `Complexity.pair (W z) st`, so `fstBlock` is the parameter block and `sndBlock` the
state. Reach for `foldlBits`, not `iterate`, whenever the loop body reads anything but the
state (`UnaryRuler.two_pow_min` is the worked example).

**There is no `Complexity.FP → PolyFueled` bridge and there will not be a cheap one** (the
P-versus-L-flavoured obstruction the `dd:fuel` model card records) — but a machine-class
migration that breaks a downstream `Computable`/`Primrec` consumer has a route that is *not* a
general `FP ⊆ Primrec`: `UnaryRuler.primrec` (`Construction/MachineTraderEnumeration.lean`,
proved via that file's coverage bridge) gives `Primrec f` from `UnaryRuler f`, and that is
enough for `Computable` of a function given only by its graph: `Partrec.rfind` on
`fun n m => Part.some (decide (graphFlag ⟨n,m⟩ = 1))`, closed by `Nat.mem_rfind`. (No
declaration in the tree currently needs that step — `DeferralFunction` exposes no `Computable`
field — but it is the route if a machine-class migration ever strands one.)

**A machine-metered premise is cheap to install when the surrounding emission lane is already
machine-metered.** Before estimating a class migration as a large rewrite, check whether the
*consumers' conclusions* are already at the target class and only their *inputs* are not: the
fix is then `s/UnaryRuler.of_polyFueled h/hR/` plus binder cleanup, not a fifty-file rewrite.
The deferral-clock lane looked fuel-certified because the index certificates were fuel and
bridged up; every emission certificate on it was already `MachineSpliceStream` /
`MachineSentenceCodes` / `UnaryRuler`.

**A type ascription does not steer dot notation.** `((fun _ => False) : PCWorld).Holds φ` fails
with "The environment does not contain `Function.Holds`" — the elaborator resolves `.Holds`
against the lambda's inferred type before applying the ascription. Write
`PCWorld.Holds (fun _ => False) φ`. Related, and worth knowing for semantic-separation
arguments: `PCWorld` is `LO.Propositional.Boolean.Valuation ℕ = ℕ → Prop`, so a world is just a
predicate on atom indices, and `PCWorld.holds_atom v m : v.Holds (atom m) ↔ v m` makes "this
formula holds here and not there, so they differ" a one-liner — far cheaper than structural
induction on right-nested conjunctions.

**`PrimrecPred p` does not unify with `Primrec (fun a => decide (p a))`** — the `Decidable`
instance differs, and `PrimrecRel.comp Primrec.eq …` fails with a bare type mismatch. Use
`PrimrecPred.decide` (Mathlib, `Computability/Primrec/Basic.lean`). Separately, dot-notation
`.of_eq` on a term of type `PrimrecPred …` resolves to `PrimrecPred.of_eq` and yields
`PrimrecPred ?m` against an expected `Primrec …`; write `Primrec.of_eq` long-hand. Same family
as the `X.toMachine` trap.

**Scripted binder deletion must balance parentheses, and `\b` does not stop at an apostrophe.**
Deleting a multi-line binder with a non-greedy `(?s).*?some \(f k\)\)` regex silently swallows
a whole declaration wherever the binder is followed by another on the same line
(`some (f k)) (n : ℕ) :`), merging two lemmas into one — and it compiles far enough to give a
confusing `unsolved goals` rather than a parse error. Use a paren-balancing scanner. And
`re.sub(r' hspec\b', '', s)` rewrites `hspec'` to `'`, producing `have' :=` / `exact'.2` and an
`unknown tactic`; grep for `have'` / `exact'` / `^ [^ ]` after any such pass.

**`attribute [local irreducible] Nat.sqrt` is only needed where `PolyFueled`/`Primrec`
elaboration happens over nested `Primcodable` products.** A surviving guard in a file that is
now fully machine-metered is stale scaffolding — `FeedbackEmission.lean` needs none;
`SettlementClock.lean` and `FeedbackTruth.lean` still do (`polyFueled_dovetailFound`, the
alternating-value witness).

**The `BigDigits`-as-tape route to a machine→fuel converse looks promising and dies.** Complexitylib's tape alphabet has exactly four symbols (`Models/TuringMachine.lean`: `zero`, `one`, `blank`, `start`), so a tape *is* a base-4 digit string and `BigDigits`' `dig4`/`len4` vocabulary fits it exactly; one step is a local edit — read one cell, write one cell, move the head by at most one — with `O(log n)`-sized control. It dies on the dependency structure, not on sizes: digit `j` of the tape at time `t` needs the last time the head visited `j`, hence the whole head trajectory, hence the tape at all earlier times. A course-of-values recursion would fix that, but its table is `poly n` entries of `Θ(log n)` bits — `Θ(poly n)` bits, exponential VALUE, and `PolyFueled.prec` carries one number. A fixed-radius window does not help either: the head moves one cell per step, so a radius-`r` window at time `t-1` supports only radius `r-1` at time `t`, and `T` steps would need radius `T`. Every variant lands back on the `O(log n)`-workspace bound. The four-symbol coincidence is what makes this look better than it is.

**The re-blocking obligation survives any miracle at the workspace step.** `MachineTokenStream t` yields only `TokenFold.decodeBits w = t n`, i.e. `undigitize (bitsToDigits w) = t n`, while `BigTokenStream t` additionally demands `(blockSplit (ds n)).2 = []`. `bitsToDigits` drops a trailing partial bit group and `undigitize` then drops a trailing partial block, so a converse must truncate the digit stream to its last complete block — find the largest `i` with `ds i ≥ 4`, a bounded maximization. The `PolyFueled` combinator suite has NO bounded-search combinator: `const`, `id`, `pair`, `comp`, `succ_comp`, `left`, `right`, `of_eq`, `addConst` and `prec` is the whole list. This is the fuel-side twin of the `MachineSentenceCodes` → `MachineSentenceBlocks` re-blocking precondition, and it is independent of the workspace bound — granting the workspace step leaves it standing. **It is a converse-direction obligation only.** Going forward, block-completeness is *carried*, not recovered: `MachineTokenStream` has the `∀ d, TokenFold.BlockWF (F (unaryDay d))` conjunct (the shape `CondStep.MachineSentenceBlocks` already had), every constructor produces a `BlockWF` word by construction (`blockWF_tokBits`, `blockWF_run`, `blockWF_unaryBlock`, `BlockWF.append`, `BlockWF.nil`), and `decodeBits_append` is the only fact about the discipline any combinator needs. So no bounded maximization ever arises on the forward side — which is also why the conjunct has to be in the class: without it `decodeBits_append` cannot fire and the class admits no `append`.

See `notes/lean-gotchas.md`. Process pitfalls that are not Lean traps: when auditing a
class swap, grep docstrings separately from code (a rename can rewrite prose where the
code did not change; no gate catches it); `#assert_fields` freezes field *names* only, so a
field-type widening passes silently — record it in the comment above the freeze; the
`lint_paper_labels.py`'s `DECL` regex must admit attribute prefixes, or `@[simp] private theorem`
slips through, and its docstring walk-back must demand a `/--` opener, or a `/-! -/` section
header above a `theorem` is accepted as its docstring; size a field widening by grepping the *field*, not the
structure; and `check-paper-nodes.sh` requires every inventoried declaration to carry a
`Paper node:` line, so internal helpers stay out of the inventory with the reason recorded.

**Foundation's arithmetic pairing IS Mathlib's at ℕ — the key that unlocks §4.10.** `LO.FirstOrder.Arithmetic.IOpen.nat_pair_eq : ⟪n, m⟫ = Nat.pair n m` is already in Foundation (IOpen/Basic.lean:761); the projections follow in three lines from it and `pair_unpair` (`π₁ z = z.unpair.1`, by `conv_rhs => rw [← h]; simp`). `definability` cannot see through `Nat.unpair` but handles `π₁`/`π₂` (they carry 𝚺₀ definability instances), while `Computable`/`Primrec` want `Nat.unpair`. State the definable predicate with `π₁`/`π₂`, the computable function with `Nat.pair`, bridge with `pi₁_nat`/`pi₂_nat`. No `Nat.sqrt` `Primrec` work is involved anywhere — computability comes entirely from `re_iff_sigma1`.

**The §4.10 bounded-derivability decider is cheap, not a proof-checker project.** `∃ d < π₂ z, Bootstrapping.Proof (V := ℕ) T d (π₁ z)` and its negation are BOTH closed by a bare `unfold; definability` (from `Proof.definable'`), then `ComputablePred.computable_iff_re_compl_re'` (the PRIMED form — the unprimed one wants a `DecidablePred` instance you do not have) with `re_iff_sigma1` on each side. `provable_of_standard_proof` needed only `refine ... (n := d) ?_; simpa [Nat.cast_id] using h` under `maxHeartbeats 1000000`. Whole module: under 30 minutes. No proof checker is needed at all.

**`BigSentenceCodes.neg` is public, in `Framework/Emission/WriteOut.lean` beside `and`.** Foundation's `∼φ = φ 🡒 ⊥` is `rfl` and `rpn` tags `imp` with `2`, so the proof is `BigSentenceCodes.and`'s verbatim with `3 ↦ 2`, second stream `BigSentenceCodes.const ⊥`, one fewer `if_neg`. Keeping such a lemma private in a downstream file to dodge a `WriteOut.lean` full-library rebuild is a false economy — the rebuild cost ~10 min, not the ~1h it was budgeted at.

**`γ.Mentions 0` IS derivable from the representation spec on the Con lane**, by `mentions_zero_of_repr_ne`, whenever the represented decider is non-constant. The apparent counterexample bounds the claim to CONSTANT deciders only: at a horizon constantly `0`, `BProv T φ 0` is `∃ d < 0, …`, always false, so the represented function is the constant `0` and a `γ` ignoring its first argument represents it correctly. So "representation at two arguments with different values forces mentions" cannot be instantiated within a constant family, and `conClaimSentence_ne_of_day_ne` keeps `γ.Mentions 0` as a hypothesis, exactly like `representedClaimSentence_ne_of_arg_ne`. Every unbounded horizon, the paper's `Ack` included, is on the derivable side.

**The strength column of `scripts/coverage-classification.md` is a closed vocabulary.** `check_endpoint_coverage.py` defines `STATUSES = {exact, strengthened, corrected, refuted, qualified}` and fails any other value, and `gen-trust-surface.py` indexes `counts[status]` directly, so a decorated status like `exact (dd:proofcode)` is a hard failure in two places. Disclosure qualifiers belong in the justification cell, not the status cell.

**The trust-surface page's per-node prose is NOT in `docs/`.** `docs/trust-surface.html` is generated by `scripts/gen-trust-surface.py`; the LI "How the panes line up" reading notes are the `LI_READING` dict literal in that script, and the "What to check" footer comes from the ledger's justification column. Edit the ledger and/or the generator, then run `python3 scripts/gen-trust-surface.py` and `python3 scripts/check_trust_surface.py`.

**The headline audit numbers live in the ledger, not the README, and are gated there.** `check_headline_counts` in `scripts/check_endpoint_coverage.py` re-derives `scripts/coverage-classification.md`'s `## Headline counts` from its own tables, matching regexes on the *prose shape*. Changing one node's status therefore forces edits at several places in that file — the status table row and, for `instantiated` nodes, the "Of the 53, N are also instantiated … X at exact or strengthened, Y at qualified" sentence — and the check is fail-closed on the pattern too: rewording that sentence out of shape fails like a wrong number does. The README states no audit count of its own; `scripts/check_li_rollcall.py` gates the few endpoint-level numbers it does state.

**A change whose intermediate step cannot compile must not be split into two commits.** Generalizing `conGamma` to two theories immediately breaks `thm:pac`'s call site in the same file, so a parametrize-only commit would be red. Where a planned commit split implies a red intermediate, prefer one green commit and say so.

**`lake build APITests` is NOT a whole-library gate.** It reports MORE jobs (3647) than `lake build LogicalInduction` (2953) while covering LESS of the library: modules outside the API import closure (e.g. `Construction/Paper/ComputationDP.lean`) are never recompiled, and a later `lake env lean` probe then reads a stale olean — an already-deleted binder printed as still present. Tell: `stat` the .lean vs its .olean. Gate library-wide changes with `lake build LogicalInduction`; treat APITests as an additional, narrower target.

**Explicit `[𝗥₀ ⪯ T]` beside `[𝗣𝗔⁻ ⪯ T]` is always droppable** through Foundation's `instance [𝗣𝗔⁻ ⪯ T] : 𝗥₀ ⪯ T` (`Arithmetic/Schemata.lean:396`); `⪯` is a Prop class, so proof irrelevance means data-valued definitions cannot change under the swap. UNLIKE the `lic_paradox_resistance_ofDiagonal_unconditional` case, where the redundant binder is a section variable the proof term references and `omit` is rejected. Explicit binder → droppable; referenced section variable → not.

**A BOUNDED decider is the WRONG substrate for `thm:incons`.** The bounded lane (`conRunValue`, one γ per horizon) fits `thm:pac`/`thm:pazfc`, whose claim IS a finite search. `thm:incons`'s claim is Σ₁ and unbounded — a horizon-based rendering needs a proof-fits-under-the-bound premise the paper lacks. Correct shape: the HALTING lane's — one fixed `codeOfREPred` schema, day's data in the argument via `binNumeral`, positive literal by `re_complete_mp`. Structurally `thm:incons` is a sibling of `thm:halts`, not of `thm:pac`.

**Foundation already has the arithmetized provability predicate AND both bridges.** `Bootstrapping.Provable T (φ : V) := ∃ d, Proof T d φ` (`Syntax/Proof/Basic.lean:467`) with `Provable.definable : 𝚺₁-Predicate` (`:525` → `REPred` via `re_iff_sigma1` in one line), and `@[simp] provable_iff_provable [T.Δ₁] : Provable T (⌜φ⌝ : ℕ) ↔ T ⊢ φ` (`DerivabilityCondition/D1.lean:34`) — BOTH directions, no consistency hypothesis. An earlier note claiming that only `provable_of_standard_proof` exists was incomplete. (Manual route at `V ≠ ℕ`: inside `rosser_internalize`, `let n : ℕ := ⌜h.get⌝; simp [coe_quote_proof_eq]`.)

**Deduction theorem: adjoin is spelled `σ ∷ T`.** `Entailment.deduction_iff : φ ∷ 𝓢 ⊢ ψ ↔ 𝓢 ⊢ φ 🡒 ψ` (`Logic/Entailment.lean:484`) applies to `Theory L` via the instance at `FirstOrder/Basic/Calculus.lean:375`. `¬Consistent (σ ∷ T) ↔ T ⊢ ∼σ` is four rewrites: `not_consistent_iff_inconsistent`, `inconsistent_iff_provable_bot`, `deduction_iff`, `← LO.Entailment.N!_iff_CO!`. Adjoining needs no `Δ₁` instance — the adjoined theory appears only in the premise.

**`lic_provind_false` at a negated sentence needs the double negation discharged semantically, not syntactically.** Its premise is now the *semantic* one (`∀ v, v.ConsistentWithTheory DP → v.Holds (∼ψ n)`), so at `ψ = ∼φ` it asks for `v ⊨ ∼∼φ` — free in a propositionally consistent world, even though `paperPrimeDecompose` never emits the *sentence* `∼∼φ` (range = {atom, ∼atom}), which is why the syntactic route `∼ψ ∈ DP.D k` fails. The wrapper is `provind_neg_false` (private, `Properties/MetaLearning.lean`): `lic_provind_false` at `fun n => ∼φ n` with `hφ.neg` for codes and the world premise discharged by `(PCWorld.holds_neg v (φ n)).mp` under `hv.holds_of_mem_stage`. No new premise — the negation conjunct is free from the positive one.

**`omit [inst] in` must precede the DOCSTRING.** `/-- doc -/` then `omit [...] in` then `lemma` is a parse error (`unexpected token 'omit'`) that only surfaces in a full `lake build`. Order: `omit [...] in` / `/-- doc -/` / `lemma`.

**Changing `theoremDP`'s tag-keyed atoms is a `ComputationDP` refactor, not a deletion.** The kinds are enumerated by `theoremDP` itself in six places, so removing one renumbers the tag space and reworks `theoremDP_hworld`. Budget it as a work item of its own.

**Ledger rows in `scripts/coverage-classification.md` are strictly ONE LINE each** — no fenced blocks, no `<br>`, no continuation rows; quoted Lean signatures must be flattened into one inline code span (as the `thm:incons` row does), or the table parse the endpoint-coverage checker depends on breaks.

**`_ofComputation` is NOT a single lane.** The §4.10 members are gone; the §4.12 feedback-truth family — `lic_wub_ofComputation`, `boundedCombination_wubaff_ofComputation`, `luv_wubexp_ofComputation` and their `_unconditional` forms — is live, curated, and is the shown endpoint for `thm:wub`/`thm:wubaff`/`thm:wubexp`. Qualify any sentence about "the `_ofComputation` lane" by §.

**`LI_READING` notes in `gen-trust-surface.py` drift independently of the ledger** and nothing cross-checks them: `check_trust_surface.py` verifies page-matches-inputs, not prose-matches-status. Three notes survived several passes asserting "[𝗜𝚺₁ ⪯ Θ] keeps this row qualified" after those rows went exact. When a row's status or binders move, grep `LI_READING` for that label explicitly.

**Why the code-digit route to a day-varying witness is not worth taking** (`deepInconsistentSource` delivers it via the source route instead). For `σₙ := "binNumeral n ≠ binNumeral n"` the code's bit length is Θ(√n), so `BigDigits (fun n => ⌜∼σₙ⌝)` is TRUE — but Foundation's `toNat` pairs at every node, so the code is a `Nat.pair` shell iterated Θ(log n) times over Horner recursion, and every `BigDigits` closure (`const`, `natPair`, `succ`, `add`, `mul`, `ifZero`, `comp`) composes only constantly many times; `PolyFueled.prec` forbids bignum state; `ofBase16Digits` doesn't apply (`Nat.pair` isn't digit concatenation). Needed: a `BigDigits` primitive-recursion combinator (never written) plus base-4 digit theory of `Nat.pair` at unbounded nesting — surveyed at 800-1500 lines. Do not re-scope without reading this.

**Quote injectivity for `ArithmeticSentence` at `V := ℕ`: neither `decide` nor `Nat.cast_id`/`Nat.cast_inj` works.** `decide` sticks on `Nat.beq` (noncomputable def); the `↑` from `quote_eq_encode` resists both cast lemmas. Working one-liner: `Sentence.quote_def` is `rfl` — state at the Semiproposition quote by type ascription, use `@[simp] Semiformula.quote_inj_iff` + `Rewriting.emb_injective`. The worked example this was written against, a separation lemma for the deduction-family argument, no longer exists.

**`one_ne_zero` is ambiguous inside `LogicalInduction` with `LO.FirstOrder.Arithmetic` open** — spell `_root_.one_ne_zero`. `T ⊢ ⊤ ⋎ ⊤` is not closed by `simp`; `cl_prover` closes it (via `Foundation.Meta.ClProver`).

**After editing an UPSTREAM file, `lake env lean` on a downstream file reads stale oleans.** Cheap iteration: `safe-lake.sh build <leaf module target>` (e.g. `LogicalInduction.Construction.Knowledge.Endpoints`) rebuilds the chain then iterates at ~1-3 min. Budget the four full gates (~1h serialized on a loaded machine), not the proofs.

**Cleared suspicions on the Con lane — do not re-raise.** (1) The horizon `f` is never metered and never enters a sentence: `conRunValue T' f` evaluates it inside the decider, the day-argument is `⟨⌜⊥⌝, n⟩` (poly-valued, `conClaimArg_digits`) — `ack` genuinely admissible. (2) The Con sentence is a NEGATED atom while incons is a BARE atom — correct, not an inconsistency: Con(Θ′)(ν) is a ∀-sentence (∃-negation is the prime), inconsistency is itself Σ₁; "normalising" polarities breaks the `paperTheoryDP_covers_*` bridges. (3) `provind_neg_false`'s world use at arbitrary stage is fine — the affine callback hands back a `ConsistentWithTheory DP` world (all stages). (4) `thm:incons`'s sentence is `Prov_{Θ₀}(⌜∼σₙ⌝)`, related to `Θ′ₙ ⊢ ⊥` only via the EXTERNAL deduction theorem — disclosed, and provability induction needs no internal one. (5) `codeOfREPred` is `Classical.epsilon`-chosen, so `schemaArgClaim`'s vacuous existential wrapper exists purely to give `paperPrimeDecompose` a reachable head constructor; `provable_schemaArgClaim_iff` shows T never sees it. (6) `conGamma T T' hh` takes the `ComputableHorizon` BUNDLE — not extensional in the function; clients must thread the same `hh` term through endpoint and sentence.

**In-file `example`s under `section Endpoints` variables can look like inhabitation witnesses without being ones.** Examples stated at the section VARIABLE `T` discharge only explicit arguments; only examples naming a concrete theory (𝗜𝚺₁/𝗣𝗔) discharge the instances. Check which kind before counting an example as a witness (the thm:dontwait applied example is the variable kind).

**tex thm:pazfc displays `⌜f⌝(⌜n⌝)` but never binds `f`** — it is inherited informally from thm:pac; the Lean statement correctly binds both `T'` and `horizons`. Do not read the missing binder as drift (paper-side blemish, not worth an errata row).

**Uniform-in-theory-code derivability is a VERIFIED OBSTRUCTION in Foundation.** `Theory.Δ₁.ch` is a meta-level formula spliced bodily into `Derivation.blueprint`'s axiom clause (`Bootstrapping/Syntax/Theory.lean:13-18`, `Syntax/Proof/Basic.lean:345,~377,403`); `⌜U.Δ₁ch.val⌝` is never formed or consumed anywhere in Foundation. A provability predicate uniform in a coded axiom-set FORMULA needs satisfaction over coded formulas in `V`; Foundation has no truth predicate over codes of any class (Tarski.lean is undefinability only), and for Σ₁ codes it is Σ₁-complete — it can never sit in a `Fixpoint.Blueprint`'s mandatory 𝚫₀/𝚫₁ core. The FEASIBLE middle: `Fixpoint.Blueprint k` is already parametric (`Arithmetic/HFS/Fixpoint.lean:18,49,177`; `Derivation` just instantiates `k=0`), so uniformity over coded FINITE axiom sets (HFS `∈` in the core) works — but adds ~nothing extensionally over the deduction paraphrase (`not_consistent_adjoin_iff` already collapses finite extensions); the gain is intensional presentation-naming only. Costs: upstream PR ~300-500 lines; LI-side clone ~800-1200 with a near-duplicate of an 851-line Foundation file (against duplication discipline); full uniformity = a 2000+-line truth-predicate project. Standing recommendation: keep the disclosed thm:incons paraphrase; the middle rendering is an OPTIONAL upstream-PR item, pending user ruling. This entry is the durable record.

**The symbol measure is FEASIBLE LI-side — no obstruction.** A Foundation derivation code is a TREE: node = `⟪sequent, rule-tag 0-9, data…⟫ + 1`, sub-derivations nested inline (`Bootstrapping/Syntax/Proof/Basic.lean:134-152`); pairing = quadratic pair = `Nat.pair` at ℕ; sequents are BITSETS (`Exponential/Bit.lean:21-23`), exponential in the largest formula code; every component provably `< d` (Proof/Basic.lean:199-252) and `Derivation.case_iff` (:534) supports plain external strong induction at ℕ. Design: define total symbol count `dSize : ℕ → ℕ` by EXTERNAL strong recursion (skip internal definability entirely — LI meters at `V := ℕ` and consumes only `Computable`), prove `Computable dSize` via Mathlib's `Computable.nat_strong_rec`, decider via the existing `bProvPacked_sigmaOne`/`re_iff_sigma1` pattern. LOAD-BEARING: the converse bound `d ≤ g (dSize d)` (computable tower-sized `g`) keeps the bounded-search negative polarity decidable — `dSize d ≤ d` is the WRONG direction and trivializes nothing. Node count is REJECTED (breaks decidability — cut formulas unbounded at fixed node budget — and is not symbol-equivalent); code bit-length only renames the disclosure. Total symbol count leaves only the symbol-counting convention as a residue, and no Gödel-code metering; `conWithin_of_consistent` and the non-collapse lane survive verbatim. Estimate ~500-800 lines, 4-8 build cycles, medium risk (Primrec course-of-values grind; the g-bound bitset-sum induction). Upstream `Derivation.size` is a public good (400-700 blueprint-grade lines), not the critical path.

**A lemma existing is not the same as it being citable — the gap the search-before-prove rule leaves open.** Several `Primrec` certificates in `Construction/Primcodable.lean` were once `private`; a downstream file can find the exact fact and still be unable to use it. Correct move: EXPORT the lemma (drop `private`, docstring naming the consumer) — never re-prove it, never Batteries' `open private ... from ...` (compiles, but hides the dependency from endpoint/axiom accounting). `negFormulaCode_prim` is ~110 lines of strong recursion that would otherwise have been duplicated.

**The source parser was already there, Primrec, and hidden.** `parseStructuredArithmeticFormula` (`Framework/Criterion.lean`) parses a token run — including source-only tags 20/21/22 — directly to the Gödel code of the COMPILED NNF formula, with `ArithSource.parseStructuredArithmeticFormula_sourceTokens` proving correctness on emitted runs. "Computability of `compile`" is a non-problem: no `Computable (encode ∘ compile)` is needed. The feasibility probe was four greps.

**Two source-metering designs that DON'T work.** (1) Gödel-numbering an `ArithSource` tree by pairing reproduces the defect: `Nat.pair` squares, `log(code) ~ 2^depth`, and `iffChain` is a linear chain with depth = node count. Only digit concatenation over the token run is safe. (2) Naming the code by a short arithmetic TERM (Horner over `Nat.pair`) is unsound: `Nat.pair` is a case split, and ℒₒᵣ terms have no case analysis — `Nat.pair` is formula-definable, not term-definable.

**`PolySegStream`'s token function is only specified BELOW the length; the `ofBase*Digits` bridges need every index.** Bridge with a three-way clamp (`< len → tok`, `= len → sentinel`, `> len → 0`) from two `subc_polyFueled` tests + nested `ifzSel_polyFueled`, as `BigDigits.blockSeg` does. This surfaces only when you apply the bridge.

**`Semiformula.encode_emb` is the sentence/ℕ-formula bridge and already exists** (`Foundation/FirstOrder/Basic/Coding.lean:189,196`; term version :68). Don't hand-roll the induction. The idiom for carrying a source beside the sentence it denotes is `PaperLUVSeq`'s `(source, compiles)` pair — the `thm:incons` endpoint's `(s, hcompile)` copies it deliberately.

**Tactic traps from the base-64 layer.** (1) Never `rw [← Nat.pair_unpair z]` in a `PolyFueled .of_eq` goal — it rewrites inside `z.unpair.1` and diverges; rewrite the hypothesis forward. (2) `Nat.ofDigits_append`/`_singleton` carry NO `Nat.cast` at ℕ/ℕ — a `Nat.cast_id` simp arg is inert. (3) In base-64→base-4 digit splitting the `j % 3 = 2` leg is SHORTER than `j % 3 = 1` (`Nat.mod_mul_right_div_self a 16 4` already ends mod 4). (4) `List.getD_eq_getElem` is Mathlib's, not core's, and takes an `n < l.length` hypothesis; without it, go `List.getD_eq_getElem?_getD` → `List.getElem?_eq_getElem` → `Option.getD_some`. (5) Don't `set M := <expr>` when you'll `rw` inside a `getElem` on `M` — use a `private def` + `:= rfl` unfolding lemma.

**`safe-lake.sh` takes the machine-wide lock BEFORE `resource-guard.sh wait`.** When the guard is LOADED for a non-transient reason (e.g. DISK below `CLAUDE_MIN_DISK_GB`, default 15), every queued build sits idle holding the lock, emits zero Lean output, and starves the machine. An empty build log is NOT evidence about the code — diagnose with `resource-guard.sh check` + `ps aux | grep safe-lake`, and kill a build immediately on learning the machine is loaded (releases the lock). AgentFoundations worktrees run 2-9GB each; a few stale `agent-*` trees can seize the whole disk. Watcher pattern: loop `resource-guard.sh check` WITHOUT invoking safe-lake, and only call safe-lake once the guard passes.

**`have h : PolyFueled _ f := by tac` cannot work — the code metavariable is unassignable.** The ascribed type elaborates to completion BEFORE the tactic block, so the `_` for the `Code` witness is a postponed metavariable nothing will solve (`don't know how to synthesize placeholder for argument c` at the `_`, plus a cascading `unsolved goals` on the enclosing declaration from the truncated block — don't chase the second error). Use term mode: bind composites unascribed (`have hinner := ifzSel_polyFueled.comp …`) and finish `houter.of_eq (fun z => by …)` — `BigDigits.blockSeg`'s discipline (`DigitArith.lean:944`).

**Foundation registers `)[` as a TOKEN** (`FirstOrder/Basic/BinderNotation.lean:159,338`), so `(f x)[n]` is a parse error (`unexpected token ')['`) in any module importing binder notation — and parses fine in modules that don't, which looks non-deterministic. Write `getElem l n h`; a space does not help (getElem is `noWs`).

**Two different `quote_eq_encode`s** (`Bootstrapping/Syntax/Formula/Coding.lean:224,296`): `Semiformula.quote_eq_encode` is for `Semiproposition`, `Sentence.quote_eq_encode` for `Semisentence`. The wrong one gives a bare "simp made no progress". With the right one, `Semiformula.encode_emb` + `encode_inj_sentence` (both simp) finish the emb/encode bookkeeping.

**`Rewriting.emb` does not commute with `Semiformula.all` by `rfl`** — needs `Rew.q_emb`; and `Rewriting.app_all` is stated at `∀⁰`, which simp won't match against `Semiformula.all`. Incantation: `have h := Rewriting.app_all (Rew.emb : Rew ℒₒᵣ Empty 0 ℕ 0) ψ; rw [Rew.q_emb] at h; exact h`. NOTE `simpa using` that term FAILS (simp reduces the hypothesis to `True`).

**`simp` won't reduce `encodeArithmeticFormulaSymbols ⊥`** (`⊥` isn't syntactically the `.falsum` arm): supply `have hbot : … = [10] := rfl`. Same for `⊤`/`.verum`.

**`provableCode_quote_iff` takes the theory as an explicit leading argument** — `.mpr` on the bare name fails (`Unknown constant`), and `(… _).mpr` fills T not φ. Spell both: `(provableCode_quote_iff T' (⊥ : ArithmeticSentence)).mpr`. `rw` hides this by unifying leading args.

**Foundation's `≤`, `/`, `%` on a MODEL are scoped instances that are NOT Nat's even at `V := ℕ`** (`LE M := ⟨fun x y => x = y ∨ x < y⟩` PeanoMinus/Basic.lean:163; noncomputable `Div`/`Mod` IOpen/Basic.lean:86,260; `+`,`*`,`<` ARE shared). Inside `open LO.FirstOrder.Arithmetic`, a `≤`/`/` YOU write elaborates to Nat's while one from a Foundation lemma is Foundation's — `exact` fails on instance mismatch. Idioms: (i) state bridging lemmas BEFORE the `open` and reach them with `refine` (a `have` re-elaborates with Nat's instance); (ii) convert with `le_def` + `Nat.le_of_eq`/`le_of_lt`. Worked example: `mem_iff_testBit` in DerivationSize.lean. Cost ~6 build cycles in 9a.

**`nat_pair_eq`'s arguments are SWAPPED vs its conclusion:** `nat_pair_eq m n : ⟪n, m⟫ = Nat.pair n m` — the natural-order bridge is `nat_pair_eq b a`.

**`PrimrecPred`/`PrimrecRel` package `Decidable` existentially** in this Mathlib, so `.to_comp` fails with `Invalid field to_comp: … Exists`; use `PrimrecPred.decide Primrec.nat_le` first.

**`G (1 + x)` will not unify with `G (?N + 1)` — and the failure is a whnf heartbeat timeout,** not a clean error, plus cascading `unsolved goals`. Normalise first: `rw [show 1 + e = e + 1 by omega]`.

**`interval_cases` needs `import Mathlib.Tactic.IntervalCases`** (error otherwise: `unknown tactic` + misleading bullet cascade); `Nat.size`/`Nat.lt_size_self` need `Mathlib.Data.Nat.Size` (not pulled by `Computability.Partrec`).

**`Primrec.comp`/`Primrec₂.comp` unfold the goal's function for HO unification and the error names a constant you never wrote** (`Option.getD` for a `List.getD` goal, `Nat.binaryRec 0` + bogus Primcodable complaint for `Nat.size`, `tvAux` for `tvPacked`). Supply `(f := …)` explicitly or route through a helper with the function as an explicit parameter; `Primrec.list_foldl`'s step must be passed `(h := …)`.

**`private` restricts name resolution, not reducibility:** downstream `rfl` still unfolds a private def (`G (N+1) = Gstep (G N)` proved by `rfl` from another file). Don't de-privatise just to state an unfolding. (`P^[6] y` = six squarings.)

**Mathlib has no `Primrec Nat.size`, no `Nat.log` primrec lemma, and no `Computable.list_map/foldr`** (only `Primrec` versions). Reuse `LogicalInduction.prim_natSize` (from `Nat.size n = Nat.size (n/2) + 1` via `nat_strong_rec`) and `LogicalInduction.computable_boundedSearchValue` (bounded ∃ over a computable binary predicate with computable bound; decidability hypothesis CURRIED `[∀ a d, Decidable (p a d)]` — pair-shaped `DecidablePred` blocks `Nat.decidableExistsLE`).

**The trust-surface page's per-node text has TWO independent sources:** the reading note from `LI_READING` (gen-trust-surface.py) and the "What to check" footer from the row's justification cell (classification). Editing one and regenerating leaves the other stale, and `check_trust_surface.py` still passes — it checks page-vs-inputs, never input-vs-input (the README isn't an input at all). Always edit both for a node.

**Row-cell surgery mechanics:** justification cells are single physical lines thousands of characters long; enumerated residual lists ((i)/(ii)/(iii)) renumber by hand; identical strings can occur in BOTH pac and pazfc rows, so count replacements explicitly (a single-occurrence assert fires, a global replace is what's wanted). Verify one-line survival with `awk -F'|' '/^\| thm:pac /{print NF}'` (expect 6).

**Cleared suspicions on the symbol measure — do not re-raise.** (1) The ill-formed catch-alls (`else m + 1`) are provably unreachable under `Bootstrapping.Proof`: `Derivation.Phi` (Proof/Basic.lean:280-291) forces `IsFormulaSet` at every node, pins `d` to a constructor ten ways, and forces `IsTerm` in exsIntro. They exist only so `le_G_dSize` needs no well-formedness hypothesis. (2) Zero-costing (`tSize 0 = 0` etc.) does NOT create infinite fibres — `le_G_dSize` is unconditional, so `{d | dSize d ≤ k} ⊆ {d | d ≤ G k}` is finite; don't re-raise without a counterexample to that lemma. (3) `sSize` charges NO separator per sequent member while `tvSize` charges one per vector entry — deliberate asymmetry; the glossary's "one separator per argument-list entry" is about term vectors only. CAUTION: `idxLen` reads as a genuine digit count and is not one — `idxLen n = Nat.size n + 1` is digit-count PLUS ONE (`idxLen 1 = 2`), and the convention text discloses that +1 as a per-index marker token.

**`#print axioms` is a LOGGING command — it never fails a build.** For substrate modules whose declarations carry no `Paper node:` line (DerivationSize, BoundedConsistency), the entire axiom accounting is a human reading build logs, and `check_endpoint_coverage.py` checks only the annotated-label direction — a name dropped from a `#print axioms` list is caught by nothing. An AxiomAudit prose block can claim coverage a name does not have. The blocks now say what actually gates each name — direct assertion or transitivity through a named endpoint — and a claim of the form "axiom-checked by the footer" is always false, since a `#print axioms` footer gates nothing.

**tex:1859's `Con(PA)(Ack)` gloss is off by one against its own definition** (tex:1857: "no proof with ν or fewer symbols" ⇒ "requires MORE than", not "at least"). Recorded in `notes/paper-errata.md`; the Lean follows the definition (inclusive `dSize d ≤ k`). A faithfulness auditor reading the gloss will think the inclusive bound is drift — it is not.

**`check-paper-nodes.sh` scans every backticked `xx:yy` token on ANY line containing `Paper node:`** — including prose in section comments that merely mentions the string. "this module carries no `Paper node:` annotation — the `dd:symbolcount` convention" on one line yields `INVALID LABEL: dd:symbolcount`. Never put a colon-token on the same physical line as the words `Paper node:`; write "paper-node annotation". And check its exit code unpiped (`| tail` masks it).

**The bare `git stash`/`pop` hazard.** With a clean tree, `git stash` saves nothing and the following `pop` popped ANOTHER SESSION'S stash (`agent/fol-luv-frontend`), leaving six `UU` conflicts. Recovery: `git reset --hard HEAD` (a failed pop keeps the entry — nothing lost). For baseline comparisons use `git show HEAD~1:<path>` into scratch, never the stash stack. (This is the standing CLAUDE.md rule.)

**`Theory.Δ₁` is a DEFINABILITY class — Foundation states NO computability fact about a Δ₁ theory's axiom set** (verified absences). Membership becomes decidable only absorbed into `Proof`'s Δ₁-ness; reach for `proofPacked_computable`, never the axiom set.

**Mathlib has NO r.e.-projection lemma** (`REPred p → REPred (∃ w, …)` does not exist — RE.lean verified). Workaround when the matrix is DECIDABLE: `Partrec.rfind` + `Partrec.dom_re` + `.of_eq (by simp [Nat.rfind_dom])`. Spelling trap: carry the matrix as `f : ℕ → ℕ → Bool` with `Computable fun p : ℕ × ℕ => f p.1 p.2`, NOT as a Prop with a paired `DecidablePred` — the latter fails to synthesize `Decidable (Q z w)` inside the rfind.

**Shared-`.lake` hazard with two agents on one checkout:** a `lake env lean` probe can hit a MID-REBUILD tree ("olean does not exist" beside siblings from two build generations — read the mtimes). `safe-lake.sh`'s lock serializes builds but does not protect a READER from a half-written tree. Probe workaround: import the lowest module with a current olean.

**`omit [inst] in` cannot drop an instance the STATEMENT can reach** — it errors `cannot omit referenced section variable`, and instance search prefers a one-step derivation from a local section instance over two steps from a stronger binder (thm:lp's `paperDiagonalQuoteCode` needs `𝗥₀ ⪯ T`: one step from local 𝗣𝗔⁻, two from 𝗜𝚺₁). To actually drop a redundant binder, put the `variable` line inside a named `section`/`end` and declare the endpoint BELOW the `end`, recovering the weaker instance in the proof via `haveI := inferInstance`. Also: an `omit … in` on a paper-facing declaration must sit ABOVE the docstring or `check-paper-nodes.sh` reads the endpoint as un-annotated.

**A `#print axioms` footer in a build log is NOT evidence the declaration elaborated** — a failing declaration's footer still prints, and prints *"does not depend on any axioms"*, which reads as clean. Grep for `error:` before believing axiom footers.

**In a shared worktree, a bare `git commit` commits the ENTIRE INDEX — including another agent's staged files.** Explicit `git add <paths>` does not protect you if the index already holds someone else's staging: one agent's knowledge commit can sweep another's 24 staged files (content fine, per-item trail lost). Rule: while another agent is active in the worktree, commit with `git commit -- <paths>` (pathspec form) or not at all; better, wait until its work lands.

**Naming collision to keep straight:** "token-metered" (the tier) vs "token model / digit model" (a distinct certificate-format contrast, e.g. `RpnEmission.lean:208`). Two notions, adjacent names.

**Census parsing traps (DEFEC probe, cost ~20 min).** (1) The `#check @name` grep must match DOTTED qualifiers — `(?:[A-Za-z_][\w']*\.)*NAME` — or projection notation (`X.RpnThresholdCodes`, `AffineCombination.PolySequence As`) silently undercounts (22 of 107 missed). (2) The census is incomplete without a STRUCTURE-EXPANSION pass: `AffineCombination.PolySequence.affcoh` shows no data class in its binder list and carries four; the carriers to `#print` are PolySequence/BoundedCombinationSequence/LUVCombination.*/LUVCombinationSyntax/GeneratedRatFeature/PGenerableWeighting/PaperLUVSeq. `DeductiveProcessComputation` is NOT a fuel class (bare code + eval spec = the paper's own c.e.).

**`Properties`/`Construction` do NOT transitively import the machine data classes** — only `LogicalInduction.Framework` does (`Framework.lean:61`); scratch probes need `import LogicalInduction.Framework`. And `BigTokenStream.toMachine` must be applied prefix when its argument comes from `obtain` on a `BigSpliceStream` (destructuring leaves the unfolded ∃-type).

**Estimate anchors for FP work:** `Conditioning/{Transduction,TransductionFrame}.lean` are together the largest single `_mem_FP` block in the library for ONE transducer; the fuel→machine compiler chain = ~19,500 lines. "Just port the combinators to FP" is a multi-thousand-line project; the fuel-side suite to mirror is ~70 lemmas, hardest single one `BigSpliceStream.concatVar` (variable-count flatMap needing `runFold_mem_FP` with per-step length bounds).

**Machine-theory tactic/API traps.** `Entailment.weakening!` is exported only as `Entailment.wk!` (Axiomatized namespace; exact? won't find it from ⊆-goals). `∃ b i (s : T),` does not parse — write `∃ (b i : ℕ) (s : T),`. `evaln_mono` is Option-membership-stated but `= some` coerces silently. The r.e.-projection incantation compiles: Bool matrix from `ComputablePred.computable_iff.mp (proofPacked_computable ∅)`, pack ⟨d,w⟩ via `proofPacked_pair_iff`, then `((Partrec.rfind hF.partrec₂).dom_re).of_eq` + `simp [Nat.rfind_dom, key z]`; the Partrec₂ coercion is `Computable₂.partrec₂`. Day-varying `DigitMachineCodes` witness = `dayMachine F n := Code.curry F n` (curry embeds only the DAY as a unary const — Θ(n) tags; NEVER `Code.const v` for a payload, Θ(v) tags; `Code.nest` computes constant 0, useless as computation). Repo source family → Code: `PolyArithmeticSourceSeq` unfolds to `PolySegStream (sourceTokens ∘ s)`, `.primrec` ∘ `tokenListNat_primrec` gives `Primrec (sourceNat ∘ s)`, then `exists_code.mp (Partrec.nat_iff.mp hf.to_comp.partrec)`. `lake env lean` with same-session NEW upstream lemmas cascades `Unknown identifier` + autoImplicit noise — build the upstream module first; genuine errors are the ones NOT mentioning an unknown identifier. `PolySegStream.constList` lives in `Construction/LUV/SourceCodec.lean:657` DOWNSTREAM of Framework — constrains module placement (which is why `Construction/Knowledge/DayMachine.lean` sits in `Construction/` rather than in `Framework/`). `ifzSel_polyFueled.comp ((A.pair B).pair test)` = if test = 0 then A else B (ZERO branch FIRST). Mathlib has NO Primrec lemma for `Nat.ofDigits` (verified) — reuse `tokenListNat_primrec`; use ℕ-specific `Nat.ofDigits_cons` (rfl), never the Semiring `ofDigits_eq_foldr`. Right-growing constructor runs (`Code.const`): `simp only [replicate_succ, cons_append, nil_append, append_assoc, cons.injEq, true_and]` then `rw [← replicate_succ', replicate_succ]`.

**`git add <directory>` in a shared worktree is unsafe** — swept a concurrent KNOWLEDGE.md edit into an unrelated commit; recovery (no --amend): copy aside, `git checkout <base> -- <path>`, pathspec-commit the back-out, restore working-tree content. Per-file pathspecs on every add; `git status --porcelain` immediately before each commit.

**An ungated window has TWO leak mechanisms, both cross-family corroborated.** (1) Splice-across-entries: incomplete-source outputs (`tokenListNat [20]`, `tokenListNat [9,9]`) concatenate into a complete refutable source `[15,20,15,9,9,9]`. (2) Prefix truncation: `tokensOfNat` keeps digits below the FIRST 63-sentinel, so non-names decode to legal runs (`8138` = digits `[10,63,1]` decodes like `4042 = (leaf ⊥).sourceNat`). Both make `MachineTheoryInconsistent` true for machines whose `theoryOf` is EMPTY (consistent) — the soundness direction is FALSE as stated, not merely unproved. Endpoint conclusions survive (only the inconsistency→predicate direction is consumed, under `hinc`), but the sentence content is broader than the `dd:machinetheory` convention claims. Repair: per-entry gate = exact round-trip name test (`tokenListNat (tokensOfNat v) = v`, kills (2)) AND complete-parse test (parser consumes the whole run, kills (1)), verum-substitute failures; align `theoryOf` semantics with the parser (an output contributes the formula the parser reads off it in full) so window-refutability ⇒ contributed formulas ∈ theory ⇒ theory inconsistent — full extensional agreement; surjectivity survives via `parseStructuredArithmeticFormula_sourceTokens` on genuine names. Also verified: `∼claim` polarity/paperPrime handling is fine; `DigitMachineCodes` is write-out not runtime (don't re-raise); `negSourceFormulaCode`'s junk-to-0 justification ("code 0 never provable") is prose with no lemma — don't cite as established.

**Node-gate and coverage records.** (1) "Covered transitively by the endpoint" is NEVER true for applied witnesses — they are downstream of a universally-quantified endpoint; only upstream substrate is transitively covered. Verify with a `getUsedConstants` closure walk, not by reading the ledger — and pick fresh names for the walk, since `closure`/`contains` collide with Mathlib. (2) A per-LABEL reverse node gate is unsound: a second `Paper node:`-annotated carrier for an inventoried label passes every checker while sitting in no assert block. LI's gate is per-declaration for that reason, as CF/MA/FFS's are. (3) LI has NO blanket sorry/axiom gate: `check_sorry_ledger.py` is Condensation-only; `lake build AxiomAudit` reaches exactly the names in `#assert_axioms_clean`; `#print axioms` footers are non-failing info commands. (4) Verified sound, and not to be re-raised: the truth chain routes compactness → common budget (`evaln_mono`) → splice spec → `provable_neg_listConj_of_not_consistent` with no represented-literal assumption; `negWindowCode_eq_quote` takes the window shape as a HYPOTHESIS so the `getD` default only ever discharges at `verumSourceNat`; `sourceTags_dayMachine`'s closed form is kernel-checked via `curry = comp c (pair (const n) id)` and `id = pair left right` (five-tag frame `[3,4,5,5,6]`).

**Docs-surgery pitfalls.** Python `\U0001d5e3` escapes produce WRONG sans-serif glyphs (`𝗣𝗠` for `𝗣𝗔` etc.) and no checker catches it — harvest glyphs from the target file by regex, never type escapes; `𝗭𝗙𝗖` appears in no docs file (spell plain ZFC). Check G's instantiated sentence compares BOTH numbers (`X at exact or strengthened, Y at qualified`) — moving one node changes both (pattern list at check_endpoint_coverage.py:340-357). Strength rows are 2-8KB single lines: locate with `grep -n '^| label '`, edit by exact-string replace, never `sed -n` a range (blows the output budget); cells must contain no raw `|`; regenerate the page LAST.

**Recognizer traps (reuse, don't re-derive).** `parseStructuredNat` is NOT injective on runs (`[1,0]`,`[1,1,0]`,… all decode 0) — the canonical-only `structuredNatRun` (side condition `p.1 ≠ 0` on tag 1) characterizes the encode image exactly. Binder depth cannot ride a `Primrec.nat_strong_rec` index (it GROWS at quantifiers; `Nat.pair` monotone per-argument only) — factor through bottom-up LEVEL functions + one `if p.1 ≤ k` at top. `PrimrecPred p` is an ∃ over the Decidable instance — a `Primrec fun a => decide (p a)` lemma won't `exact`-unify; wrap `⟨inferInstance, h⟩`. Foundation family-abbrev coercions make `Rewriting.emb` rw-lemmas SILENTLY no-op when the RHS is spelled `↑τ` (different family stamps) — spell `(Rewriting.emb τ : …)`; diagnose with `pp.explicit`. `simp [encodeArithmeticFormulaSymbols]` can't unfold under `Rewriting.emb` — push the emb through the constructor first (`coe_rel`/`coe_nrel` exist; and/or/all/exs need local rfl lemmas via `app_all`/`app_exs` + `Rew.q_emb`). `Semiformula.eq_and_iff` etc. take the rewriting ω EXPLICITLY (`(eq_and_iff Rew.emb).mp`); `eq_neg_iff` is for `🡒`, not `∼` (use `map_neg` + `neg_neg`; for `🡘` rewrite `iff_eq` first). `Provable T x → 0 < x` IS four lines (`isFormulaSet` + `IsFormulaSet.singleton` + `IsSemiformula.pos`; `fstIdx` resolves UNQUALIFIED; `_root_.lt_irrefl`); `Provable T x → ∃ σ, x = ⌜σ⌝` was searched for and does NOT exist. `split_ifs at h` auto-closes `none = some` branches (drop the old `· simp at h` bullets); `simp only [Option.bind_some] at h` BEFORE `rcases hq :` (lambda shadowing). Gate non-vacuity was checked by EVALUATION too (accepts ∀-sentences and ⟺; rejects the three audit leak shapes) — a gate rejecting everything would also be 'sound'.

**Worktree Bash-guard trap (cost a subagent ~250 finished lines):** the guard refuses compound commands ('too complex to verify'), aborting the WHOLE command — a heredoc write inside never happens, but a follow-up `lake env lean` on the stale file succeeds and the loss surfaces two steps later as `unknown identifier`. Keep writes single-command (or Write tool) and re-verify file contents after every write.

**Docs-mirror records.** The `dd:machinetheory` convention text lives in SIX places that must move together: the glossary bullet (LogicalInduction.lean), Construction/Knowledge/Endpoints.lean's §4.10 header + `theoryOf`/`MachineTheoryInconsistent` docstrings, AxiomAudit's thm:incons block, the README's standing-modeling-choices section, the classification's global bullet AND its thm:incons row cell, and `LI_READING['thm:incons']` (page regenerated from the last two). Glyph-harvest refinement: check `git show HEAD:<file> | grep -c <glyph>` (working-copy greps count your own edits — false confirmation); `↔` is absent from gen-trust-surface.py and `↑` from all three docs files — state such facts in words. The scoped-surjectivity phrasing is now everywhere; do NOT restore the old unqualified "surjective onto the r.a. theories". General lesson: a docs mirror of a soundness repair is LONGER than what it replaces — the old text asserted a claim that becomes true only BY the new mechanism, so the mechanism must be named, not just the wording swapped.

**Residual looseness, recorded not fixed: `check_endpoint_coverage.declarations()` walks back to the nearest `/--` WITHOUT stopping at `/-! -/` headers or intervening declarations** — an unannotated declaration after a section header inherits an earlier docstring's labels (`size_succ_le`/`unpair_fst_le_sqrt` falsely reported as thm:ob carriers). Checks C/D and `gen-trust-surface.py` consume that map, so a canonical endpoint can pass check D on an INHERITED label. Use `paper_nodes.scan` + `following_declaration` for anything that must be right; fixing `declarations()` is queued.

**AxiomAudit.lean (and EVERY registered library's .lean file) is a hashed trust-surface input** — any inventory or Lean edit reds `check_trust_surface.py` until the generator reruns; a work plan forbidding `docs/` while requiring that checker green is self-contradictory whenever it touches Lean. Plan one regeneration after integration; resolve conflicts in the page by rerunning the generator, never by hand.

**AxiomAudit entry-name resolution needs a unique-dotted-suffix leg:** the file is inside `namespace LogicalInduction` and `open`s four namespaces, so ~12 entries are written relative; and `_root_.`-prefixed declarations must have the namespace prefix DISCARDED, not prepended. See `_resolve_entry`.

**Upstream-prep pitfalls.** `git log -S` cannot find removal-by-commenting (occurrence count unchanged) — pickaxe structurally with `-G '^section model$'` without a path filter, then resolve paths per commit. Shadow-olean recipe for building modified Foundation modules without lake: `cp -Rc` the installed build (APFS hardlinks, instant), shadow FIRST on LEAN_PATH, re-emit with `lean --root=<clone> -o <shadow>/<Module>.olean` — and **`rm` each shadow file before re-emitting: they are HARDLINKS to the installed package's oleans and writing through them corrupts the installed build**. `-o` requires `--root=`. Old commented Foundation code may `open LO.Arithmetic` — a dead namespace now (material moved to `LO.FirstOrder.Arithmetic`); strip stale opens when reviving. Porting LI→Foundation is header/doc work, not proof work (same pin): module-system header, drop `#print axioms`/provenance lines, promote useful privates, commit style `<type>(scope): <subject>`, re-run `mk_all` for alphabetical registration.

**Regex-deleting one bullet from an `rcases` case chain is a trap:** non-greedy `(?:.*\n)*?` anchored on the shared bullet prefix matches from the FIRST bullet — locate the target's index, `rindex` back to the bullet start, and re-read the edited proof before building.

**Market-migration pitfalls (reuse).** Market migration is mechanical IFF the lane is generic-plus-instantiation (13 quotation endpoints, ZERO repairs — swap presentation/market/hworld); budget by the IMPORT DAG, not the proofs — compute upstream/incomparable/downstream splits first. Atom-payload tag numerals are spelled LITERALLY in emitters/parsers in grep-proof forms (`PolyFueled.const 4`, `Nat.pair 7 (Nat.pair w.1.1.2.1 w.2.1)`, …) — the COMPILER is the only oracle (each sits in a definitional `of_eq`); budget 4-6 whack-a-mole cycles, and in a mixed change the renumbering half is the LARGER half (6 of 7 cycles, measured). Verified look-alikes NOT to touch: EF serialize tags (Criterion:348), Foundation qq codes (negFormulaCode), DerivationSize rule codes, RPN token opcodes (`t = 1 ∨ t = 7`), theoremDP EVENT tag at ComputationDP:112 vs the PAYLOAD tag ten lines away, `Formula.or`'s constructor tag (ProductDefinition:813). File surgery by line range truncates docstrings SILENTLY (build stays green; only the node checker catches the orphaned `def`) — run the node checker after any split. `quotation_presentation_nonvacuous` still witnesses at `theoremDP` correctly (existential statement, internal witness choice).

**Market-unification docs-mirror records.** Market unification is NOT a safe sed: two docs sentences became FALSE, not stale — thm:pazfc's "trained on that process and nothing else" (the union adds theoremDP's atoms; honest repair: "trained on Θ's own commitments and on nothing about Θ′") and a README list putting thm:ccee among the shared-market nodes. Only reading the surrounding clause catches falsity. NOT every `paperTheoryDP` in docs is a market claim: the PaperLUV `source_valued` completed-world premises genuinely still run over `paperTheoryDP` (ArithmeticSource.lean:1194/1242/1606) — verified and left alone; blanket renames would introduce errors. `scripts/trust-surface-template.html` carries a HAND-WRITTEN vocabulary legend (~line 386) that is a generator input but not gen-trust-surface.py — a change scoped to the generator misses it and `check_trust_surface.py` passes on the faithfully-stale render; a faithfully-stale render can carry a retired process name and a wrong binder past it. The 𝗣𝗔⁻/Σ₁-soundness paragraph is copy-pasted into 8 ledger rows AND 7 LI_READING notes with two independent "tag 7" spellings each — a tag rename needs four global replacements and the two files' wordings differ.

**Binder-documentation pitfalls.** The classification has TWO global sections — `## Global model disclosure` (substrate/dd:fuel/dd:symbolcount) and `## Arithmetic-theory hypotheses` (binders and the soundness argument) — cross-references must target the second for binder pointers or they dangle. The binder paragraph is copy-pasted: two shared blocks (×8, ×3) plus three one-offs in the ledger, and four `LI_READING` notes — count with an asserting script rather than by eye. Glyph trap: `𝚺` (U+1D6BA) vs `𝚪`-family mis-types make exact-match finds silently 0 — harvest from the file, assert counts, exit before writing. Quote style is MIXED (ASCII vs typographic) and load-bearing for exact strings. `docs/trust-surface.html` renders all six papers — Condensation's "pending a ruling" scope note is a standing false positive for LI ruling sweeps.

**Confirmed defects worth remembering as a class.** (1) `LimitCoherence.lean:20-25` duplicates Mathlib's `Prop.instMeasurableSpace`/`instMeasurableSingletonClass` and SHADOWS them repo-wide (declared later) — the rule-2b failure mode at instance level; delete and cite. (2) thm:wubexp endpoints take the support hypothesis the printed node lacks — a VERIFIED paper transposition (errata: support condition belongs on the feedback theorems; the affine twins prove it) — but the docstrings DENY the extra premise; declare the correction instead. (3) `FeedbackTruthComputation` has ONE inhabitant, constant truth ≡ 1: the §4.12 lane's non-vacuity is degenerate and undisclosed at its five endpoints. (4) `lic_self_trust_closed` is the ONE endpoint the write-out migration left at `RpnSentenceCodes` (docstring mislabels it def:ec); the narrowing enters via the quote-code lane + the nonexistent `LUV.BigThresholdCodeSeq`. (5) thm:scon's growing form hides the same class in `CompactConditioningProcessComputation.condition_codes` — structure fields are invisible to binder censuses (the standing structure-expansion lesson, now with a concrete miss). (6) thm:lp's width bundle: inhabited but never discharged in the shown example.

**Two new VERIFIED paper errata (final audit):** the thm:recurringunbiasednessexp/thm:wubexp support-condition transposition (affine twins prove the intended placement; recurringunbiasednessexp's statement references an f it never introduces), and def:seqprand's above/below sign (printed `p − ThmInd` contradicts thm:prand's pairing; counterexample = all-refutable at p=1/2; Lean's `ThmInd − p` is correct). Both in notes/paper-errata.md.

**FW pitfalls (reuse).** Import-induced PARSE breakage: adding a Construction/Paper/TheoremDP import to a low-level module made an UNMODIFIED file's `xs[k]'h` unparseable (LO notation after a ?-subterm); looks nothing like an import problem and hides behind stale oleans — probe with a two-line import-only file; fix by LAYERING, never by rewriting the victim; "no consumer references a changed name" does NOT make an added import safe (notation, not names). Namespaced-grep false negatives: before recording "structure X has no witness", grep the TYPE NAME in def/instance position across namespaces. The two `#assert_axioms_clean` rules cut in OPPOSITE directions (per-declaration gate forces annotated decls IN; block membership forces unannotated decls OUT) — check annotation status before adding a name. `Entailment.Consistent` needs `open LO` (not just LO.FirstOrder...) — fails only at the third binder and reads like a missing import; copy Construction/Paper/TheoremDP.lean's full open list. `sentenceAtomCodes` and `PCWorld.holds_congr_atomCodes` live in `Framework/BooleanWorlds.lean`; `ProductDefinition.lean` only uses them, and adds the tag-`3` freshness layer over them — grep the statement shape, not the directory. Emitter chains generalize over an index-renaming map essentially for FREE (proofs transport the index without casing); tagging = `(PolyFueled.const tag).pair PolyFueled.id`. `PolyFueled` is a Prop — a/degree can't be projected; nonconstant-witness lemmas must be `Nonempty` LEMMAS. Truth-assignment defs: prefer explicit `if ∃ k, f k = n ∧ …` over `Function.invFun` (Classical junk off-image blocks TheoryTruth). Calibration: every FW budget overshot in the CHEAP direction because primitives existed — inventory combinators (`rg 'PolyFueled' | rg 'lemma |def '`) before writing; the unbudgeted cost was INTEGRATION (the parse regression outcost every fix). Errata-vs-docstring drift: when an errata entry postdates a statement's docstring, nothing gates their agreement — sweep the statements when recording an erratum.

**Docs-mirror records.** `RpnSentenceCodes` binds ZERO canonical endpoints, and so does every other token-, write-out- and value-metered class: there are **no** token retentions anywhere on the surface, the quotation `_ofRepresentation` layer and thm:scon's `condition_codes` included. thm:dus axis moved universal→instantiated on `lic_domination_everyLowerSemicomputable_paperDP` (README instantiated 18→19; the axis is gated only through the README sub-count regexes — flip both numbers in the same commit). The three `_paperDP` dus endpoints are deliberately NOT in the 107-census (parity with LI-CANONICAL + the def:ec class counts computed against it; annotated-but-noncanonical is legal if asserted). The ledger's whole-value structure list drifts silently and has been wrong about the same structures more than once (`IntrospectionIntervalQuote.inverse_width_codes` is `MachineRatCodes`, `SelfTrustQuote.{product,confidence}_codes` are `LUV.MachineThresholdCodeSeq`, `ParadoxResistanceQuote.sentence_codes` is `MachineSentenceCodes` and never had a width-code field, `DUSApproximationPresentation` has no `approximation_codes` field at all): metering prose can be stale in the CLASS NAME while reading perfectly plausibly, so check elaborated signatures, never the sentence. `Rpn ⊊ Big` for sentence codes has NO strictness lemma (README records it) — write "argued, not carried by a lemma". PE2 has TWO halves (wubexp carries the unprinted clause; recurringunbiasednessexp prints it with no f) — docs stating one half are wrong. Names on that lane: `indicatorProductLUV_machineThresholdCodeSeq` (`Construction/Quotation/MarketQuoteCodes.lean`, used at `Construction/Paper/Market.lean`); the `_big` spelling exists nowhere.

**Metering-class migration traps, as a group.** (1) A binder census cannot see a premise a
*structure field* carries — read the declaration census and the field census together, or a
"clean" surface hides a fuel premise one projection down. (2) The statement snapshot prints
field TYPES, so a retype IS caught there even though `#assert_fields` (names only) misses it;
a structure that is not a snapshot member is invisible to both. (3) Before declaring a class
has "no twin", read the target namespace's combinator list — there is no
`MachineSpliceStream.const`, and what a caller wants is `tag` / `tradeSlot` /
`serialize_const` composed with `.of_eq`. (4) Probe the DOWNSTREAM computability consumers
(`.primrec`, `.computable`) before moving a class: they read primitive recursiveness off the
fuel certificate and need a machine twin of their own. (5) A residual `[IsLogicalInductor]`
after a move is the STRONGER theorem, not a gap.

**When two meterings share one structural induction, generalize the induction, not the
proofs.** Where a `const`/`append`/`of_eq` induction has to be run at both a fuel and a
machine class, state it once over a small interface carrying those three operations and
instantiate it twice (the `EmissionCalculus` pattern in `Construction/Knowledge/SubstEmission.lean`);
mirroring the proof body is the same theorem twice and the second copy silently drifts.

**Word-arithmetic shapes that work, and two that do not.** Bound an iterated word computation
by *ruler truncation* at a fixed width derived from the input, never by a sharp inner bound:
`Cobham.output_length_poly_of_mem_FP` compounds to `p^n` inside an iterate and cannot
substitute. Dispatch on a digit's unary LENGTH (`TokenFold.ifEqLen_mem_FP`), never on its raw
bits. Check the radix before reaching for multiplication — `64 = 4 ^ 3`, so a base-64 Horner
accumulation over base-four digit runs is *concatenation*. And a `dgFold` client that
PREPENDS its per-step emission yields most-significant-first order out of a
least-significant-first fold, which is why the compact numeral emitter needs no reversal and
no random access into the emitted word.

**Elaboration traps around the machine classes.** `UnaryRuler` is delta-reducible, so a raw
`List.replicate`-spelled goal still typechecks and hides which lemma you meant. Machine-class
hypotheses do not unify higher-order: pass `(f := …)` / `(cnt := …)` / `(D := …)` explicitly,
and make the function argument match the UNREDUCED one (normalize with `.of_eq` first).
`X.toMachine` dot-notation fails on a class that is a def unfolding to `∃ …` — write it
long-hand. `Classical.choose` on a `Complexity.FP` membership elaborates and fails later, at
the first projection. `▸` cannot rewrite into a def-wrapped `Prop`: use `show …; rwa`.
`rw [show … from by …]` leaves a metavariable — hoist the `show` into a `have`.
`Complexity.id_mem_FP` is `id ∈ FP`, not a ruler; inside `TokenFold` reach for
`mem_FP_pairWithInput`. `simp [List.replicate_add]` loops. `X.foo` written inside
`namespace X` resolves to `X.X.foo` before the global `foo`, so give a variant the suffix
rather than the prefix.

**Adding a `Framework/Machine/` module costs four wirings**, and three of them are silent: the
`Framework.lean` import and map entry, the `API.lean` import (a new module is invisible to the
API import closure until that widens), and the module counts printed in `README.md` and
`API.lean`. `check_li_file_closure.py` catches only the first.

**Non-vacuity of a machine class is two lemmas, not one:** a membership lemma and a
non-constancy lemma saying the family varies with the day. `Framework/Machine/Witnesses.lean`
is the first place to look for an example of any of the machine classes, and the pattern to
copy when adding one.

**The README's shape.** It is organized around the finished object (What is this / How it is modeled / What differs / How to use / Where the accounting lives / Layout); ALL audit statistics now live ONLY in `scripts/coverage-classification.md`'s `## Headline counts` (check G reads that file; README counts are gone and the checker will NOT catch a reintroduced count — don't). Public wrapper `LogicalInduction.lic_iff_of_finiteSupportPerturbation` (API.lean) = the supported name for corrected thm:ifp, definitionally `FreezeOracle.lic_iff_of_finiteSupport`; `lic_iff_of_noReservedSupportPerturbation` and `lic_iff_of_recognizableSupportPerturbation` are the strictly weaker wrappers beside it, and `RecognizableSupportPerturbation` + atom helpers are exported unqualified. `import LogicalInduction.API` brings WriteOut transitively — the old add-this-import advice was wrong (the "import" grep hit was inside a doc fence). APITests is a numbered client session ending in the endpoint roll-call; `buyOneDaily`'s certificate is fully discharged from the API import alone (`ofSingleTradeBlocksBig` + `BigSentenceCodes.const` + `serialize_const`). Lean traps: docstrings can't precede `export` (use `/-! -/`); never cite paper labels from memory (def:tf not def:ef; def:exploitation; alg:li+def:lia share a line; def:affcomsen) — nothing gates README labels. The errata ledger is consolidated (duplicates folded into PE2/PE5, process narration stripped); it runs PE1-PE9, PE9 being the deferred rational coding at `def:luv`/tex:1655.

## Working on this library at scale (process notes)

This section is environment knowledge, not knowledge about the formalization: how the
build, the tooling and the editing at this scale actually behave, and what past work
here has cost against what it was predicted to cost. Nothing below bears on whether a
statement matches the paper — read it before planning a pass, not before reading a
theorem.

**Consolidation-pass pitfalls (build, tooling, process).** These cost real time across the
whole library and none of them announces itself.

*Builds and logs.* `safe-lake.sh` exits **0** when it cannot take the lock and when run
under `nohup … &` — read the log, never the exit code; a `cmd | tee log | tail` pipeline
reports `tail`'s status, and `${PIPESTATUS[0]}` is unreliable under a background task, so
redirect and `echo $?` instead. Grep the log for `Build completed successfully` and for
`^error:` **separately**. The lock has no queue, so starvation is real: set
`CLAUDE_LAKE_LOCK_TIMEOUT=14400`; the "held by pid N" line goes stale, so read
`/tmp/claude-lake.lock/pid`. Its two give-up paths look like hangs and are neither a red
build: the lock timeout, and `resource-guard wait` exiting "STILL LOADED" on the disk floor.
The scratchpad is shared between concurrent agents in one worktree — prefix scratch files
with a per-pass identifier, or `census.out` and `build.log` get clobbered, and a log written by
another worktree's build can be read as your own (authenticate a verdict by the log's header
line, the `trace:` paths, and olean mtimes). Elaboration is seconds; queueing is hours —
budget build cycles, not proofs, and batch every edit before the first full build.

*Seeded oleans.* A `cp -Rc`-seeded `.lake` keeps mtimes, so lake replays modules built
against a different source tree — compare olean against source mtime and check that the
`.trace` names your worktree. `cp -RP` deep-copies complexitylib (~16 GB); use `cp -RPc`. A
truncated `.lake/packages` seed makes lake re-clone the packages. `du` overcounts APFS
clones; use `df`. A cloned `.lake/build` also replays stale *linter* state, so pre-existing
`unusedSimpArgs` warnings reappear.

*The right gate.* The directory roll-up is the gate, not a hand-picked importer list — a
spot-check list misses importers and ships a red module as green. `Framework/*` gates with
`LogicalInduction.Framework`, `Properties/*` with `LogicalInduction.Properties`,
`Construction/*` with `LogicalInduction.Construction`. `lake env lean` is a lock-free smoke
test and not a gate: it auto-binds implicits and reads stale upstream oleans. Lake prints
`Built`/`Replayed` only for modules with diagnostics — absence is not evidence of skipping.
Never edit a file while its build is queued; lake reads at lock acquisition.

*Editing at scale.* Deleting by line range swallows load-bearing declarations — run a
declaration-name diff against base after every block move, and a comment-stripped token diff
to catch dropped tactic bullets, which a name diff misses. Patch bottom-up and review every
removed line. A "dead code" scan by name is unreliable in both directions: `grep` without
`-w` matches a name inside a longer one that merely extends it, so a bare
prefix looks used when only its suffixed sibling is; a usage lookbehind must ADMIT a preceding
dot; declaration-regex inventories hit prose lines inside docstrings; and 15 `EvalnCompiler`
lemmas with zero textual references are live through `@[simp]`, while several Brouwer lemmas
are reached only by `grind`/`aesop`. The "unused `have`" scan is ~90% false positive because
`linarith`/`nlinarith`/`omega`/`positivity` read the context — only ∀-quantified `have`s (the
`hP` idiom, spelled `∀ n s` / `∀ n φ` / `∀ n ψ` per file) may be deleted on a name scan, and
even then per occurrence. Delete `#print` blocks *before* running a dead-name scan, and
exclude the scratch and bookkeeping directories from it.

*Statement freeze ≠ safety.* A downstream `rw [thatDef]` or `simp [thatDef]` depends on the
def body's **spelling**, so abstracting a definition can break importers with a byte-identical
statement surface; definitional equality is not enough for a downstream `simp` set. Collapsing
a `def` into an instance of a general one is defeq-safe and simp-unsafe — keep the direct body
plus an `rfl` bridge. Merging sections with different instance binders is a freeze hazard.
Cross-section moves change signatures through differing `variable` lists.

*The checkers, not lake, gate docstring surgery.* `lake build` stays green through any
docstring damage. Cross-reference rot — a backticked declaration name that no longer exists —
is invisible to every checker, so sweep backticks mechanically, section headers included.
Column limits are counted in **characters**; `awk`'s `length` counts bytes and over-reports
by 3-4× on any line with a theory glyph. Never retype `𝗜𝚺₁` (U+1D5DC U+1D6BA) — copy it; a
mistyped glyph passes every gate.

*Worktree hygiene.* Sub-agents inherit the parent's worktree. An agent worktree can be
reclaimed mid-session with Bash still pinned to the old path; recover by gating in the new
tree and applying a verified patch to the integration head, staging only owned paths. Never
`git commit --amend` in a checkout another agent is committing to. Always re-read the
integration branch's tip with `git rev-parse` — a worktree may be provisioned from the base
rather than the tip.

**Estimate calibration, adding a second theory parameter: one build cycle.** The stage-(i) substrate was already theory-parametric (`variable (T : ArithmeticTheory) [T.Δ₁]`), so the second theory required ZERO changes to `BoundedConsistency.lean` — only the four representation-layer declarations hardwired `T' = T`. If a future stage looks like "add a second theory parameter", check whether the substrate is already parametric before budgeting.

**Estimate calibration, a new represented lane: build cycles are the whole cost.** Substrate + collapse + new lane each compiled on the first or second `lake env lean`; three full serialized `lake build` cycles (~30-45 min each) dominated. Budget build cycles, not proof effort — batch every file edit before the first full build.

**Calibration, first compile of a ~900-line work-in-progress module:** six edits, all proof-local, none touching a statement; the authors' suspicions (a),(b),(d)-(g) were sound as written and only (c) had a defect — an elaboration-order failure, not math. Budget elaboration-order and notation-token failures ahead of mathematical ones.

**Estimate calibration, the §4.10 symbol measure:** predicted 500-800 lines / 4-8 cycles, medium risk at the g-bound. Actual ~1350 lines / ~12 cycles; the g-bound was EASY (2 cycles, junk-branch trick); the expensive pockets were Foundation-vs-Nat scoped instances (~6 cycles, one 12-line lemma) and the ~580-line Primrec grind (worth delegating to a disjoint file). Budget instance-mismatch and unification pathologies ahead of the mathematics.

**Estimate calibration, the machine-theory rendering:** predicted 1200-1600 lines / 20-28 cycles with S1 riskiest; actual ~1220 lines / ~8 cycles with S1 CHEAPEST (the input-list redesign deleted the risk; `curry`+`curry_inj` already existed). The real sink was build-lock queueing. When a design carries a "junk guard", first ask whether an explicit witness list makes the guard unnecessary.

**Estimate calibration, certified deciders:** the honest window fix was not a ~50-line per-entry parser test but a ~1435-line recognizer + ~250 lines of wiring (~60% `nat_strong_rec` boilerplate adaptable from `LIACompiler.lean`'s). Budget three strong recursions per new fuel-recursive certified decider; the design analysis ruling out lighter options is itself a major fraction and is recorded above.

**Calibration:** "two witnesses slipped through" was the anecdote; the census found 166. Budget the census, not the anecdote (the fix was still cheap: ~7-13s AxiomAudit rebuild, ~1.5s scan).

**Calibration, ComputationDP tag refactor:** budgeted as a work item of its own; actual ~2h across 10 files, ZERO proof repair (surviving branches byte-identical); cost = three sequential full builds under the lake lock. Budget build wall-clock.
