# Formalization knowledge — Logical Induction (arXiv:1609.03543)

Facts about this formalization that a reader working on it would otherwise have to
rediscover: the paper-to-Lean correspondence at the points where the names do not match,
and the design decisions that are settled and should not be relitigated. It deliberately
does not duplicate the canonical documents — read those first.

- Trust surface, disclosures and strength claims: `LogicalInduction/README.md`
- Recommended consumer import and its boundaries: `LogicalInduction/API.lean`
- `dd:*` design-decision glossary, naming conventions, endpoint-suffix ladder:
  `LogicalInduction.lean`
- `dd:fuel` model card: `Framework/Computable.lean` ("### `dd:fuel` model card")
- Defects in the source paper: `notes/paper-errata.md`
- Lean and toolchain traps: `notes/lean-gotchas.md` — the single home for pitfalls
- Checked endpoint inventory and axiom accounting: `AxiomAudit.lean`

## Correspondence table

The full paper-to-Lean correspondence is carried by the `Paper node:` docstring lines and
checked two-way by `scripts/check-paper-nodes.sh`. Listed here are only the places where the
name does not say what the object is.

| Paper (§/symbol) | Lean name | What to know |
|---|---|---|
| `def:ec`, §3.3 (`sec:efc`, tex:749) | `MachineEfficientTrader` (`Framework/Criterion.lean`) | The paper's own quantifier: ordinary machine polynomial time via `Complexity.FP`, over the **unary** day. This is the class the construction enumerates and dominates. |
| `def:ec`, certification | `EfficientlyComputable` / `PolyFueled` (`Framework/Computable.lean`) | Fuel-clocked `Nat.Partrec.Code` certificates (`dd:fuel`). A *sufficient* route into the machine class (`EfficientlyComputable.toMachine`), not a definition of it. Fuel meters the **value** `n`, not its bit length, which is sound only because the day is unary. |
| `def:ec`, e.c. machine sequence (tex:1931) | `DigitMachineCodes` (`Framework/WriteOut.lean`) = `BigDigits (Code.sourceNat ∘ m)` | Machines are `Nat.Partrec.Code`, **named by `Code.sourceNat`** (`Framework/CodeSource.lean`): the postfix tag stream (1=zero … 8=rfind', 0 = pad, never emitted) read base-16. Linear in the syntax tree (`len4_sourceNat_le : len4 c.sourceNat ≤ 2 * c.size`), total primitive-recursive decoder `ofSource` with `ofSource_sourceNat`. `Encodable.encode` is **not** used for naming anywhere on the claim-name path (see intentional deviations). `UniversalCodeHalts z := ((Code.ofSource z.unpair.1).eval z.unpair.2).Dom` decodes the source *inside* the represented computation. |
| `def:ec`, e.c. bitstrings / naturals | `BigDigits` (`Framework/DigitArith.lean`) | Two `PolyFueled` programs (base-4 length, digit access). `PolyFueled` bounds the *output value* too, so `len4 (x m)` is polynomially bounded: a `BigDigits` family is writable in poly fuel. A length-`n` bitstring has `~n/2` base-4 digits. Refuting `BigDigits` for a family reduces to a superpolynomial base-4 length (`not_polyFueled_two_pow` shape). |
| `def:ec`, e.c. sentences / rationals / emission | `BigSentenceCodes`, `DigitRatCodes`, `BigTokenStream`/`BigSpliceStream` (`Framework/WriteOut.lean`) | The write-out ladder. Value-bounded predecessors: `PolyNatCodes`/`PolyMachineCodes` (whole value; kept only as strictness foils, no `Paper node`) and `RpnSentenceCodes`/`RpnThresholdCodeSeq` (per-token value). `RpnSentenceCodes` is *not* purely symbol-metered: `PolySegStream` bounds every emitted token's value, so a single atom with exponential index is excluded by `Rpn` and admitted by `Big`. **There is no write-out class for LUV thresholds**: `LUV.RpnThresholdCodeSeq` (`Framework/Expectations.lean`) is the only one. `StructuredPaperRpn.lean` splices Gödel codes out of small tokens (`PaperLUVSeq.source_valued_and_rpnThresholdCodeSeq`), **but only for `PaperLUVSeq`, whose `structural : PolyArithmeticFormulaSeq` field meters Foundation's numerals in UNARY** (`numeral v` costs `2v−1` symbols, `encodeArithmeticTermSymbols_numeral`): a paper LUV whose formula names a superpolynomial constant (`X > 2⁻ⁿ` with the numeral `2ⁿ`) is excluded (R3-F19, compiled refutation via `not_isPolyBounded_two_pow`). `unitFracPaperLUVSeq` (`1/(n+1)`) is admissible. The round-1 'cleared suspicion' was wrong in exactly this way; the faithful repair is a write-out arithmetic-formula meter naming numerals in binary — the `Code.sourceNat` pattern applied to `ArithmeticSemiformula` — identified, not done. |
| `def:ece` / `def:fuz` | `GeneratedRatFeature` (`Framework/Expectations.lean`) / `PGenerableWeighting` (`Properties/Calibration.lean`) | Both emission fields are `BigSpliceStream`; that shared meter is what makes `pGenerableWeighting_iff` (def:fuz = def:ece minus the denotation clause) statable — keep them at the same meter. General `PGenerableRat` constructor: `PGenerableRat.ofDigitRatCodes`; `ofPolyRatCodes` (`ProductDefinition.lean`) is the derived value-bounded corollary. `ratCodeFeature`/`ratCodeFeature_generated` live in `Expectations.lean` at `DigitRatCodes` strength. A constant leaf `EF.const q` serializes to `[1, encode q]` — one token whose value *is* the code — which is why the old `RpnSpliceStream` field silently excluded the paper's `2⁻ⁿ`. |
| §4.9 nodes (`thm:halts`/`loops`/`dontwait`), endpoint stack | `lic_learns_halting_patterns` (`Properties/MetaLearning.lean`) → `*_ofComputation` (`ComputationSyntax.lean`) → `*_unconditional` (`ComputationDP.lean`) | Three layers, all present: generic (no theory hypotheses, arbitrary `P`/`DP`), syntax layer (`[IsLogicalInductor P DP]` + `ComputationTheoryPresentation`), canonical instantiation over `liaHistory (theoremDP T)`. An auditor who sees only the canonical row wrongly concludes no arbitrary-inductor endpoint exists. `⌜f⌝(⌜n⌝)` → `boundedHaltingClaimInput m x hh.program n`, with `⌜f⌝` a constant and `n` unevaluated. `CodeHaltsWithin` meters by `evaln` fuel, not Turing steps — harmless at `thm:dontwait`, live if a positive bounded-runtime result is ever stated. |
| Foundation `re_complete` | `Foundation/FirstOrder/Arithmetic/R0/Representation.lean:260` | An **iff** stated under `[T.SoundOnHierarchy 𝚺 1]`; only `.mpr` (provable ⇒ true-in-ℕ) uses soundness. `.mp` is `sigma_one_completeness` (`R0/Basic.lean:143`, `[𝗥₀ ⪯ T]` only) — a soundness-free `re_complete_mp` compiles in six lines. `Entailment.Consistent T` is derived from the soundness instance (`Basic/Hierarchy.lean:481`), so every `inferInstance` for consistency silently routes through it. The transport `models_haltingSchema_iff` (`ComputationDP.lean`) lifts `codeOfREPred_spec` to standard-model truth of a schema instance. |
| `def:lic` | `IsMachineLogicalInductor` (`Framework/MachineEfficiency.lean`) | The criterion the construction proves. `IsLogicalInductor` is the same criterion over the fuel class, kept as the compatibility predicate the §4 tail is stated against. |

- `def:ec` is paper **§3.3**, not §2.2 — §2 is Notation, §3 is the Criterion.
- `evaln_output_can_exceed_fuel` (`Framework/Computable.lean:51`), `codeEvalBound`,
  `codeEvalBound_poly` and `codeEvaln_result_le` (`Framework/Emission.lean:21–78`) are
  **repo** lemmas, not Mathlib. Grepping Mathlib for them finds nothing.

## Settled design decisions

**The two efficiency classes, and which way the inclusion runs.**

- `EfficientlyComputable Tr → MachineEfficientTrader Tr` is proved
  (`EfficientlyComputable.toMachine`). The converse is **not** proved, and the honest
  wording for it is "not attempted; structurally blocked in the fuel calculus's toolkit" —
  never "false as stated" or "provably fails". `RpnFreeze` records a *structural toolkit*
  obstruction (`BigDigits` is closed under forward polynomial carry recurrences and open
  under inverses) and itself says the claim holds in the intended complexity model;
  `not_polyFueled_two_pow` (`Framework/Computable.lean:1679`) separates only `PolyFueled`,
  by output size. The model card's "Lower calibration — OPEN" wording is authoritative.
- The fuel bound is polynomial in the **day**, and the day is unary, so composing
  `codeEvalSteps_poly` (`Framework/Machine/CodeSteps.lean`) with either the `PolyFueled`
  bound or `EfficientlyComputable`'s explicit clock `a * (n + 1) ^ k + a` gives a step count
  polynomial in the input length. A binary day rendering would silently strengthen the class.
- The clock normal form's `+ a` summand and `(n + 1)` base are load-bearing for
  satisfiability at degenerate inputs: `|output| ≤ |input| + t` at `w = []` needs
  `clock 0 ≥ output length`, which `2a` supplies and a bare `a · n ^ k` would not.
- The `IsPolyBounded f` conjunct of `PolyFueled` is derivable from the other two, via
  `codeEvaln_result_le` + `codeEvalBound_poly` + `IsPolyBounded.comp`.
- `codeEvalBound c k` is polynomial in the fuel **per fixed code** — the degree grows with
  the code, since `pair` doubles it. The `n ≤ k` guard caps every value passed onward, which
  is why exponential-growth codes return `none` rather than break the bound.
- `IsPolyBounded.mul` lives in `Framework/Machine/CodeSteps.lean`, not beside the other
  closure lemmas in `Framework/Computable.lean`: the `prec` step count is what needed it.

**Serialization and the decoding pipeline.**

- `Trader` is a one-field structure, so `EfficientlyComputable`'s witness equality
  `clockedTrader lc tc clock = Tr` is interchangeable with the pointwise form
  `∀ n, strategyOfTokens n (unRpn (undigitize (clockedTokens lc tc (clock n) n))) = Tr.strat n`.
  Machine-side bridges consume the pointwise form.
- In that chain `clockedTokens` emits the **digit** stream — one digit per `tokenCode` call —
  not tokens. Clamping digits by `min · 4` is semantics-preserving, because
  `undigitizeStep` branches only on `d < 4` and treats every `d ≥ 4` as a block terminator
  (`undigitize_map_min_four`). That clamp is what lets the machine emit a fixed three bits
  per digit.
- The clamp lemma `undigitize ∘ map (min · 4) = undigitize` is a one-line `blockSplit`
  invariance from `undigitize_eq_blockSplit` (`Framework/DigitArith.lean:934`) plus
  `blockStep`, not a from-scratch induction.
- **Degenerate inhabitants are not evidence of content.** The interpretation chain's empty
  conventions cooperate — `undigitize [] = []`, `unRpn [] = []`,
  `deserializeTrades [] = some []`, `strategyOfTokens n [] = ⟨[], _⟩` — so
  `strategyOfTokens n (unRpn (undigitize [])) = Trader.zero.strat n` closes by `rfl`, and any
  class of the shape `∃ F, «F is efficient» ∧ interp ∘ F = Tr.strat` is inhabited by the
  constant-`[]` witness. `MachineEfficientTrader` included. Never cite such a witness as
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

- `Construction/Machine/DescExec.lean` is indexed by machine **descriptions**, not machines:
  `LIACompiler` needs the enumeration to be primitive recursive, and a `Complexity.TM k`
  bundles its state type and its tapes as functions, neither of which `Primrec` can see.
- Executability (`Primrec`), polynomial-time soundness of each indexed computation, and
  coverage of every polynomial-time trader are three different facts, and the modules are
  split along exactly those lines. Making the primitive-recursive evaluator carry the
  complexity proof is the conflation to avoid.
- The semantic class and the enumeration are kept apart on purpose:
  `MachineEfficientTrader` is not defined as "occurs in the enumeration"; that every member
  does occur is the content of `exists_enumeratedTrader_eq`.

**Renames landed 2026-08-28 (grepping old names finds nothing).** `buySeq_ec_rpn` →
`buySeq_ec_big` (`buySeq_ec` is a *different* lemma); `rpnSentenceCodes_bitPrefixSentence` →
`bigSentenceCodes_bitPrefixSentence`; `digitMachineCodes_twoPowMachine_not_polyMachineCodes` →
`digitMachineCodes_nest_not_polyMachineCodes` with the witness changed to
`Nat.Partrec.Code.nest`; `ratCodeFeature`/`toWeighting` moved up into `Framework`/`Properties`.

**Σ₁-soundness: where it is load-bearing, and why the model route does not remove it
(scoped 2026-08-28).** `provabilityWorld` (`ComputationDP.lean`) is already a *provability*
world (`T ⊢ …`), not standard-model truth — only `luvWorld`
(`LUVDeductiveProcess.lean`) is literal ℕ-truth. Soundness is consumed at exactly two sites:
`theoremDP_hworld` tags 3/7 and `luvWorld_consistent`, and for one reason: complementary
claims are two *independent* `codeOfREPred` Σ₁ schemas
(`universalBoundedHaltingSchema`/`universalBoundedFailureSchema`, `universalQuotePos`/`Neg`)
whose exclusivity is a standard-model fact only (`universalBoundedSchemas_exclusive` is
stated with `Evalb` in ℕ). Tag 1 fires on `T ⊢ ∼schema` and is discharged from consistency
alone — the pattern the other tags do not follow. A model-of-`T` or Lindenbaum world does
**not** help: the residual obligation `M ⊨ failure → M ⊭ halts` needs `T ⊢ ∼(σ ⋏ τ)`, and if
some consistent `T` proved both schemas at one `z` the stage would contain `atom` and
`∼atom`, so `hworld` would be *false*. The faithful fix (fire negatives on `T ⊢ ∼σ`, as tag 1
does) needs strong representability — Foundation's `code_uniq` is in a commented-out block
(`Representation.lean:115-162`), `codeOfREPred` picks its formula by `Classical.epsilon` so
its shape is unreachable, and the bounded claim is Σ₁ (deferred horizon), not Δ₀. Foundation
also has no first-order Lindenbaum lemma. Recorded as a verified obstruction **scoped to those two sites only** — the syntax layer
(`represented*`, `*_ofComputation`) and every `.mp`-only representation lemma are
soundness-free via `re_complete_mp` (R3-F14, 2026-08-28); the cheap
alternative (a bespoke "`T` never proves both schemas" hypothesis) is a new type-`(c)`
substitution and was not taken. Unscoped idea for a future pass: minimization-trick functional
graph formulas (`γ := θ ⋏ ∀z<y ∼θ[z]`, uniqueness provable in `𝗜𝚺₁` without inspecting `θ`)
plus a Δ₁ evaluator via Bootstrapping's internal-model definability. The model route *is*
already used where it works: `paperPrimeWorld` (`PaperFirstOrder.lean`) via
`Theory.small_satisfiable_of_consistent`, soundness-free because `.nrel` maps to the negation
of the *same* atom. After R3-F14 the instance is charged ONLY at `theoremDP_hworld`, `luvWorld_consistent`,
`luvThresholdDP_hworld`, `quotation_presentation_nonvacuous`, `loopsTheory_soundOnSigma1`
and the `_unconditional` instantiations (8 declarations); 43 declarations across 5 files
dropped it via `re_complete_mp` (`ComputationSyntax.lean`, `[𝗥₀ ⪯ T]` only — the only
importer of Foundation's `R0.Representation`). Calibration: the grep-based '187 signature
lines' estimate over-counted ~4×, and the predicted `[Entailment.Consistent T]` breakage did
not occur (the one consumer of derived consistency also uses `.mpr`).

**Charging rule for the Σ₁-soundness demotions (2026-08-28).** A row is `qualified` iff *no*
canonical endpoint of that label renders the printed statement on the paper's own hypotheses.
19 of 105 canonical endpoints need the instance. `thm:scon`/`wub`/`wubaff`/`wubexp` were
deliberately **not** demoted because each also curates a universal `_ofComputation` endpoint
with no theory premise that *is* the printed theorem; reversing that is four cells
(exact 26 / qualified 17 / strengthened 5). Blast-radius method: `#check @name` over the
`LI-CANONICAL-BEGIN/END` names in one scratch file and read the *elaborated* signatures —
grepping is useless (100+ hits, mostly witnesses).

**`thm:loops`'s `hloops` witness is by axiom fiat, and why no natural theory discharges it
*here*.** `ComputationTheoryPresentation` has `boundedFailure_refutes` but no `halting_fails`;
bounded failure is r.e. with its own complementary schema, unbounded non-halting is Π₁. The
witness `loopsTheory := insert (∼σ) 𝗜𝚺₁` is consistent, Σ₁-sound, `Δ₁`, and discharges every
instance (`Theory.Delta1.insert`, `WeakerThan.ofSubset`, and `[ℕ ⊧* T] → T.SoundOn` gives
soundness *and* consistency free). **The reason a natural `T` (`𝗜𝚺₁`, `𝗣𝗔`) cannot be
exhibited is opacity, not impossibility** (corrected 2026-08-28, R3-F01/F12): Σ₁-soundness
does *not* forbid refuting a false Σ₁ sentence (that is proving a true Π₁ one, which `𝗣𝗔`
does routinely), and `incomplete_of_REPred_not_ComputablePred_Nat'` refutes only the
*uniform* negative principle, saying nothing about one instance — `𝗜𝚺₁` would refute a
natural arithmetization of `rfind' succ` diverging by a one-line induction. What blocks it is
that `universalHaltingSchema := codeOfREPred UniversalCodeHalts` is chosen by
`Classical.epsilon` (`R0/Representation.lean:232-247`), so the formula's shape is unreachable
from Foundation's API and the only bridges to `T ⊢` are positive. Three honest
strengthenings: a `halting_fails` field; Π₁-reflection on `T`; or a hand-rolled halting
formula with its own representability lemma (which would also address the LUV-frontend
numeral problem below). Do not spend prover time on it *with the installed substrate*.

**Widening a sentence-codes hypothesis.** A hypothesis used only via `.primrec`/`.exists_code`
can be widened `RpnSentenceCodes → BigSentenceCodes` (both classes have them). Consumers that
*block* widening: `.comp`/`.and`/`.bigOr` on the symbol-metered class, and anything
destructuring a `PolySegStream` (the conditioning compiler, `LUV.RpnThresholdCodeSeq`
producers: `QuoteCodeOfMarket`, `ProductDefinition`, `SemanticSource`, `SemanticJoint`,
`StructuredPaperRpn`). Never sweep the rename globally; widen the affine/trader lane and wrap
with `BigSentenceCodes.ofRpnSentenceCodes` at each Rpn-producer → Big-consumer site.
`thm:st` is pinned at `Rpn` one level down (no `LUV.BigThresholdCodeSeq` exists).
`EfficientRepeatedEnumeration.ofRpn` keeps its `Rpn` argument and wraps internally.

**Strictness ledger (never reprove).** `not_polyFueled_two_pow`, `bigDigits_two_pow_not_polyFueled`,
`bigTokenStream_not_polySegStream`, `digitRatCodes_two_pow_inv_not_polyRatCodes`,
`bigSpliceStream_two_pow_inv_not_rpnSpliceStream`, `bigDigits_two_pow_not_polyNatCodes`,
`digitMachineCodes_nest_not_polyMachineCodes`, `not_polyNatCodes_ack`,
`not_polySentenceCodes_bitPrefixSentence`. `BigSentenceCodes ⊇ RpnSentenceCodes` has **no**
strictness proof (the canonical Polish route already admits exponential codes; only an
unbounded single token separates) — never describe it as strict. `BigDigits.primrec` and
`BigSentenceCodes.primrec` legitimately reassemble the whole value (`Primrec` has no time
budget); that is not a leak unless the result is used as a `PolyFueled`/`FP` certificate.

**`ofSource` design.** Peels `n` base-16 digits from `n` itself with no zero-guard; safe
because tag 0 is a no-op pad (`sourceStep_pad`). The roundtrip needs
`size_le_sourceNat`; linearity is an *inequality* (`len4 ≤ 2·size`) with the matching lower
bound `pow_pred_le_sourceNat`.

**`ofDigits_div_pow_mod`** (`Framework/CodeSource.lean`) duplicates `ofDigits_digit`
(`PrefixMachine.lean`, downstream, cannot import upward); the Framework one is more general.
Delete PrefixMachine's if the dependency direction ever permits.

**Cleared suspicions (round 3, do not re-raise).** `GeneratedRatFeature.rank_le : (feature n).rank ≤ n`
is exact under the day shift (`EF.price φ j` denotes `V j φ` at Lean day `j`; do not 'fix' to
`≤ n+1`). `ofSource`'s garbage→`zero` convention is unexploitable: claim names are
`Nat.pair (sourceNat m) x`, only the first component is decoded, `ofSource_sourceNat` makes it
exact, `sourceNat_injective` keeps machines on distinct atoms. `DUSThresholdEmission`'s
whole-value `PolyRatCodes` fields are inhabited because the dovetail's stage table is
clock-truncated (`dusApprox_polyRatCodes`), argued not-charged at the `thm:dus` row.
`SelfTrustQuote.product_reflected`/`confidence_reflected` are discharged at
`lic_self_trust_closed` (`QuoteCodeOfMarket.lean`), one level above the `_ofRepresentation`
layers. `bitStringEnumeration` and `Dovetail.dusString` are literally the same definition
(hence `hB := fun _ ↦ rfl`). `lem:conluvapprox` is assigned to
`Properties/ExpectationConvergence.lean` by the coverage map; the `Expectations.lean` mentions
are prose-only by design. The `_closed` canonical endpoints for `thm:epr/ref/st` live in
`QuoteCodeOfMarket.lean`, not `ComputationDP.lean`.

**`ofSource` is a correctness decoder; its cost is what its own lemma says.** It peeled `n`
digits from the value `n` until 2026-08-28 (≥ 2ᵏ steps for `nest k`; R3-F02/F06/F13); the
repaired decoder peels the digit count. `Primrec` carries no time budget — never cite a
`Primrec` lemma as evidence of efficiency.

**The metering taxonomy has three tiers, and the middle one is easy to mislabel.**
Whole-value (`PolySentenceCodes`, `PolyRatCodes`, `PolyNatCodes`, `PolyMachineCodes` —
`IsPolyBounded` on the Gödel value); per-token-value-metered, called "symbol-metered" in
older prose (`RpnSentenceCodes`, `RpnThresholdCodes(Seq)`, `PolySegStream` — poly many
tokens, each of poly *value*); write-out (`BigSentenceCodes`, `BigDigits`, `DigitRatCodes`,
`DigitMachineCodes`, `BigTokenStream`/`BigSpliceStream` — poly many tokens, individual
tokens unbounded). `BigSentenceCodes` lives in `Framework/WriteOut.lean`, not `RpnSplice.lean`.

**Which §4-tail rows the LUV-threshold class actually charges.** Follow the metering through
the structures, not the binder list: `AffineCombination.PolySequence.sentence_poly` is
`BigSentenceCodes` and `LUVCombination.PolySequence` is only `mesh_poly`, so
`LUVCombination.BoundedSequence` carries no threshold hypothesis (thm:loe, thm:expprovind,
thm:prandexp are clean); `LUVCombinationSyntax.threshold_poly : LUV.RpnThresholdCodeSeq`
(`LUVSyntax.lean:35`) is what carries it, so only the `_ofSyntax` endpoints (thm:expcoh,
thm:exppolymax, thm:perexpkno) plus the direct `hcode` binders (thm:ec, thm:ei) demote —
five rows, not eight. thm:ceu/thm:ref construct their threshold codes and are not charged.

**Sparing rule for a charged class (stated 2026-08-28).** A row is spared iff some shown
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
supports, R3-F24). `SemidecidableComputation` serves only `thm:incons`,
`BoundedComputation` only `thm:pac`/`thm:pazfc`; the §4.9 nodes never pass through them.

**Known dead weight.** `PolyEF` (`Framework/Computable.lean:258`) is a dead-end layer:
consumed only by other `PolyEF` lemmas, never converted to any emission class. It is a
consolidation candidate, recorded here so it is not mistaken for load-bearing.

## Intentional deviations from the paper

The standing modeling choices are the `dd:*` labels in `LogicalInduction.lean`. Which
boundary, if any, a given paper node carries is recorded in that node's own row in
`scripts/coverage-classification.md`; `LogicalInduction/README.md` explains the categories.
Entries there are not audit findings unless the justification itself is wrong.

- **Machine naming is not Mathlib's `Encodable.encode`** (R2-F16, 2026-08-28). `encodeCode`
  emits `2*(2*Nat.pair (encode cf) (encode cg))+4` per `pair`/`comp`/`prec` node, so the value
  *squares* per node: for `nest 0 = zero, nest (n+1) = pair (nest n) zero` (`2n+1` nodes) the
  base-4 digit counts are exactly `0, 2, 4, 8, 16, 33, 67, 134` (`#eval`-verified). The paper
  admits `nest` (poly time to write the source); `BigDigits ∘ encode` excluded it. Machines are
  therefore named by the linear `Code.sourceNat`. This is a representation choice of the same
  kind as RPN for sentences, disclosed at `DigitMachineCodes` and `sourceNat`; the user's
  ruling is that it classifies `exact`, with no obligation to formalize that all reasonable
  programming languages are polynomially equivalent.
- **Σ₁-soundness is stronger than the paper's hypothesis, and the rows say so** (R2-F02,
  2026-08-28). The paper assumes Θ consistent, c.e., and *represents computations*
  (tex:600-606, tex:993-997) and treats soundness as a *further* assumption (tex:2673);
  its §4.9 proofs use Σ₁-completeness and consistency only. `[T.SoundOnHierarchy 𝚺 1]` on the
  instantiated endpoints is a strengthening, not a rendering. `README.md` and the axis legend
  asserted the opposite until this date — do not restore that claim. Removal is a verified
  obstruction (see design decisions), not a promise.
- **The `dd:fuel` charge is levied once at `def:ec`** (classification legend "Global model
  disclosure"); a downstream row not repeating the caveat is not a defect.

## Paper errata

`notes/paper-errata.md` is the ledger. The one a reader must know before using §4.6: the
published `thm:ifp` is **false**, and the repository proves it false; what is available is
the corrected finite-support theorem
`FreezeOracle.machine_lic_iff_of_recognizableSupport`.

## Pitfalls

See `notes/lean-gotchas.md`. Harness-process pitfalls that are not Lean traps: when auditing a
class-swap round, grep docstrings separately from code (a rename can rewrite prose where the
code did not change; no gate catches it); `#assert_fields` freezes field *names* only, so a
field-type widening passes silently — record it in the comment above the freeze; the
`lint_paper_labels.py` `DECL` regex must admit attribute prefixes or `@[simp] private theorem`
slips through (fixed 2026-08-28); size a field widening by grepping the *field*, not the
structure; and `check-paper-nodes.sh` requires every inventoried declaration to carry a
`Paper node:` line, so internal helpers stay out of the inventory with the reason recorded.
