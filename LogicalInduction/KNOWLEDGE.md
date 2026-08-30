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
| `def:ec`, e.c. sentences / rationals / emission | `BigSentenceCodes`, `DigitRatCodes`, `BigTokenStream`/`BigSpliceStream` (`Framework/WriteOut.lean`) | The write-out ladder. Value-bounded predecessors: `PolyNatCodes`/`PolyMachineCodes` (whole value; kept only as strictness foils, no `Paper node`) and `RpnSentenceCodes`/`RpnThresholdCodeSeq` (per-token value). `RpnSentenceCodes` is *not* purely symbol-metered: `PolySegStream` bounds every emitted token's value, so a single atom with exponential index is excluded by `Rpn` and admitted by `Big`. **There is no write-out class for LUV thresholds**, and none is needed: `LUV.RpnThresholdCodeSeq` (`Framework/Expectations.lean`) is the only one, and `StructuredPaperRpn.lean` splices Gödel codes out of small tokens (`PaperLUVSeq.source_valued_and_rpnThresholdCodeSeq`). **Corrected 2026-08-29 (R4-F01, reversing R3-F19):** `PaperLUVSeq.structural : PolyArithmeticFormulaSeq` meters one token per ℒₒᵣ node — the paper's own symbol count. Foundation's `Operator.numeral` is unary — a Foundation artifact; the paper never fixes a numeral notation (it writes numerals positionally, tex:614, tex:757). That artifact does not narrow the class, because the *value* is nameable compactly inside ℒₒᵣ: large values are named by compact terms (Horner `binNumeral`, O(log v) nodes) or by definitions (tex:614: writing ⌜f(3)⌝ 'merely requires writing out the definition of γ_f' — e.g. Foundation's Δ₀ `exponentialDef`), and those renderings are admissible. Witnesses: `unitFracPaperLUVSeq` (`1/(n+1)`), `dyadicPaperLUVSeq` (`2⁻ⁿ`). On numerals the class is fine. **The class is NOT coextensive with def:ec on connectives (R4-F04, blind audit, verified):** the paper's language has `⟺` primitive (tex:560); Foundation's NNF `Semiformula` has none and `a 🡘 b = (a 🡒 b) ⋏ (b 🡒 a)` duplicates both sides (`3 + 2|a| + 2|b|` tokens), so a left-nested `⟺` chain is O(n) in the paper and ≥ 2ⁿ tokens here — `iffChain_not_polyArithmeticFormulaSeq`. `→` and `¬` are linear. Ruling 2026-08-29: disclosed as an object-language substrate substitution `dd:nnf`, charged once globally (like `dd:fuel`), not per row; the faithful repair is a compact formula SOURCE language with `iff`/`imp`/`neg` primitives decoded to NNF for semantics (the `Code.sourceNat` pattern applied to formulas — the correct target of that idea; a binary-numeral source node was rejected as a permissive widening). Identified, not done. |
| `def:ece` / `def:fuz` | `GeneratedRatFeature` (`Framework/Expectations.lean`) / `PGenerableWeighting` (`Properties/Calibration.lean`) | Both emission fields are `BigSpliceStream`; that shared meter is what makes `pGenerableWeighting_iff` (def:fuz = def:ece minus the denotation clause) statable — keep them at the same meter. General `PGenerableRat` constructor: `PGenerableRat.ofDigitRatCodes`; `ofPolyRatCodes` (`ProductDefinition.lean`) is the derived value-bounded corollary. `ratCodeFeature`/`ratCodeFeature_generated` live in `Expectations.lean` at `DigitRatCodes` strength. A constant leaf `EF.const q` serializes to `[1, encode q]` — one token whose value *is* the code — which is why the old `RpnSpliceStream` field silently excluded the paper's `2⁻ⁿ`. |
| §4.9 nodes (`thm:halts`/`loops`/`dontwait`), endpoint stack | `lic_learns_halting_patterns` (`Properties/MetaLearning.lean`) → `*_ofComputation` (`ComputationSyntax.lean`) → `*_unconditional` (`ComputationDP.lean`) | Three layers, all present: generic (no theory hypotheses, arbitrary `P`/`DP`), syntax layer (`[IsLogicalInductor P DP]` + `ComputationTheoryPresentation`), canonical instantiation over `liaHistory (theoremDP T)`. An auditor who sees only the canonical row wrongly concludes no arbitrary-inductor endpoint exists. `⌜f⌝(⌜n⌝)` → `boundedHaltingClaimInput m x hh.program n`, with `⌜f⌝` a constant and `n` unevaluated. `CodeHaltsWithin` meters by `evaln` fuel, not Turing steps — harmless at `thm:dontwait`, live if a positive bounded-runtime result is ever stated. |
| Foundation `re_complete` | `Foundation/FirstOrder/Arithmetic/R0/Representation.lean:260` | An **iff** stated under `[T.SoundOnHierarchy 𝚺 1]`; only `.mpr` (provable ⇒ true-in-ℕ) uses soundness. `.mp` is `sigma_one_completeness` (`R0/Basic.lean:143`, `[𝗥₀ ⪯ T]` only) — a soundness-free `re_complete_mp` compiles in six lines. `Entailment.Consistent T` is derived from the soundness instance (`Basic/Hierarchy.lean:481`), so every `inferInstance` for consistency silently routes through it. The transport `models_haltingSchema_iff` (`ComputationDP.lean`) lifts `codeOfREPred_spec` to standard-model truth of a schema instance. |
| `def:lic` | `IsMachineLogicalInductor` (`Framework/MachineEfficiency.lean`) | The criterion the construction proves. `IsLogicalInductor` is the same criterion over the fuel class, kept as the compatibility predicate the §4 tail is stated against. |

- `def:ec` is paper **§3.3**, not §2.2 — §2 is Notation, §3 is the Criterion.
- `evaln_output_can_exceed_fuel` (`Framework/Computable.lean:51`), `codeEvalBound`,
  `codeEvalBound_poly` and `codeEvaln_result_le` (`Framework/Emission.lean:21–78`) are
  **repo** lemmas, not Mathlib. Grepping Mathlib for them finds nothing.


**§4.10 Con substrate (T8/i).** `Framework/BoundedConsistency.lean`: `BProv T φcode k` (bounded provability, `dd:proofcode`), `conWithin T k` (= paper `Con(T)(k)`), `bprovValue T : ℕ → ℕ` (the decider), `conRunValue T f` (the universal decider `thm:pac` represents), `conWithin_of_consistent`, `conWithin_anti`. `ComputationRepresented.lean`: `conClaimArg`, `conClaimSentence`, `conGamma`/`conGamma_spec`, `representedConClaims`, `conClaimSentence_ne_of_day_ne`. `lic_belief_finitistic_consistency_unconditional` now reads `(T) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [RepresentsComputations T] (horizons) (hh : ComputableHorizon horizons)` and concludes `liaHistory (paperTheoryDP T) n (conClaimSentence (conGamma T T hh) n) ≈ₙ 1` — no `consistentWithin`, no `BoundedComputation`, no `hconsistent`. *(Spelling updated T8/ii: `conGamma` takes two theory arguments; pac is the diagonal.)*

**`thm:pac` carrier keying (T8).** `thm:pac` is keyed to `lic_belief_finitistic_consistency_unconditional` (the arithmetized `Con(Θ)` family). `lic_belief_finitistic_consistency_ofComputation` still carries the same `Paper node: thm:pac` docstring but is the SUPERSEDED second carrier, retiring in stage (iii) with `BoundedComputation`; the ledger's claim is keyed to `_unconditional`.

**T8/ii: `thm:pazfc` is a genuine second theory.** `lic_belief_stronger_theory_consistency_unconditional` now reads `(T T' : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [RepresentsComputations T] [T'.Δ₁] (hcons : Entailment.Consistent T') (horizons) (hh : ComputableHorizon horizons)`, concluding `(fun n => liaHistory (paperTheoryDP T) n (conClaimSentence (conGamma T T' hh) n)) ≈ₙ fun _ => 1`. The market is Θ's; the claims are about Θ′. `BoundedComputation`/`strongerConsistentWithin`/`hconsistent` are gone from it. Witnessed in-file at Θ = 𝗜𝚺₁, Θ′ = 𝗣𝗔, horizon `ack n n`.

**The §4.10 Con family is parametric in TWO theories, and `thm:pac` is the diagonal.** `exists_reprAll_conRunValue`, `conGamma`, `conGamma_spec` and `representedConClaims` all take `(T T' : ArithmeticTheory)`: `T` represents (the market's theory, paper's Θ), `T'` is metered (paper's Θ′). `thm:pac`'s sentence is `conClaimSentence (conGamma T T hh) n` — the DOUBLED argument; any text carrying the old one-theory spelling `conGamma T hh` is stale. `representedConClaims` takes `Entailment.Consistent T'` explicitly; at the diagonal, `thm:pac` supplies `RepresentsComputations.consistent T`.

**Foundation already has the consistency and Δ₁ facts the §4.10 witnesses need.** `instance : Entailment.Consistent 𝗣𝗔` (Foundation `Arithmetic/Schemata.lean:392`, via `consistent_of_sound` at the standard model); `PA_delta1Definable`/`ISigma1_delta1Definable` (`Incompleteness/InductionSchemeDelta1.lean:1380,1383`); `PeanoMinus.delta1` (:768). The 𝗜𝚺₁/𝗣𝗔 witness discharges `Consistent 𝗣𝗔` by `inferInstance`. `Entailment.Consistent 𝗭𝗙𝗖` exists (`SetTheory/Universe.lean:326`) but 𝗭𝗙𝗖 is not an `ArithmeticTheory`, so the paper's ZFC illustration is NOT directly instantiable; 𝗣𝗔 is the right second theory. The soundness route is confined to the witness `example`; the endpoint takes consistency as a hypothesis.

**Both `thm:pac` and `thm:pazfc` temporarily have two `Paper node:` carriers** — the live `_unconditional` endpoints and the superseded `_ofComputation` layers. All four checkers pass in that state (a node may have several carriers); debt cleared in stage (iii).

**T8/iii retirements executed.** Gone from the library: `BoundedComputation`, `ordinaryBoundedComputation`, `alwaysBoundedComputation`, `representedDecidableClaimsOfComputation`, `lic_belief_finitistic_consistency_ofComputation`, `lic_belief_stronger_theory_consistency_ofComputation`, abstract `lic_belief_stronger_theory_consistency`. `lic_belief_finitistic_consistency` (`MetaLearning.lean:66`) survives — both `_unconditional` §4.10 endpoints route through it. `BigSentenceCodes.neg` is public in `Framework/WriteOut.lean`. `lic_disbelief_inconsistent_theories_unconditional` no longer carries `[𝗥₀ ⪯ T]` (resolves via Foundation's `[𝗣𝗔⁻ ⪯ T] : 𝗥₀ ⪯ T` instance, `Arithmetic/Schemata.lean:396`); the census 𝗥₀ count is 0 of 105.

**T8/iv: `thm:incons` is now about theories.** `lic_disbelief_inconsistent_theories_unconditional` (moved to `ComputationRepresented.lean`, over `paperTheoryDP`) reads `(T) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] (T') [T'.Δ₁] (σ : ℕ → ArithmeticSentence) (hσ : BigDigits (deductionFamilyArg σ)) (hinc : ∀ n, ¬Entailment.Consistent (σ n ∷ T'))`, concluding both paper conjuncts at `(representedInconsistentTheoryClaims T T' σ hσ).inconsistencySentence`/`.consistencySentence`. New: `ProvableCode`, `provableCode_re`, `provableCode_quote_iff`, `not_consistent_adjoin_iff`, `provableCode_neg_iff_not_consistent_adjoin`, `provableCode_quote_verum`, `not_provableCode_quote_falsum` (`Framework/BoundedConsistency.lean`); `inconsistencySchema(+_spec/_not_argument_insensitive/_mentions_zero)`, `deductionFamilyArg`, `inconsistencyArgClaimSentence(+Instance/_ne_of_arg_ne)`, `representedInconsistentTheoryClaims` (`ComputationRepresented.lean`). GONE: `SemidecidableComputation`, `ordinarySemidecidableComputation` (+ `positiveHalt*` helpers), `inconsistentTheoryClaimsOfComputation`, `lic_disbelief_inconsistent_theories_ofComputation`, the old `theoremDP` endpoint.

**`InconsistentTheoryClaims` is a THREE-field structure** — `inconsistencySentence inconsistency_poly inconsistency_provable`; `consistencySentence` is a `def` (`∼inconsistencySentence`), `consistency_poly`/`consistency_disprovable` gone. Old six-field spellings are stale, `#assert_fields` included.

**After T8, `thm:incons` is the single `qualified` theorem/lemma node** in the LI ledger; its sole charge is the deduction-family paraphrase (Θ′ₙ = Θ₀ ∪ {σₙ}), retired by tranche 9b. Prose speaking of "both remaining qualified nodes" or "the §4.10 gap shared with thm:pac/thm:pazfc" is pre-T8.

**CORRECTION (R7, reversing the stage-(i) entry): `γ.Mentions 0` IS derivable from the representation spec** whenever the represented function is non-constant. `mentions_zero_of_repr_ne` (`Framework/RepresentsComputations.lean`, ~10 lines via `Semiformula.rew_eq_of_not_mentions`: a γ ignoring `#0` makes `reprAll γ y z` z-independent, so the biconditional forces `g z = g z'`). The f≡0 counterexample is sound but bounds the old claim to CONSTANT deciders; "do not spend prover time on it" was wrong. Con lane discharges: `conGamma_mentions_zero` (non-constancy), `conGamma_mentions_zero_of_horizon_unbounded` (usable form: ⊤ provable ⇒ some derivation code; unbounded horizon exceeds it), `conGamma_mentions_zero_ackermann` (fully discharged, 𝗜𝚺₁/ack). New import: `RepresentsComputations.lean` ← `SubstOccurrence.lean`.

**New R7 names.** `mentions_zero_of_repr_ne` (`Framework/RepresentsComputations.lean`); in `ComputationRepresented.lean`: `conGamma_mentions_zero{,_of_bProv,_of_horizon_unbounded,_ackermann}`, `deductionFamilyArg_ne_of_ne`, `alternatingInconsistentAxiom{,_digits,_inconsistent}`, `thm_incons_applied_alternating` (carries `Paper node: thm:incons`; day-varying two-value witness, day-separation exercised at days 0/1).

**§4.10 paper↔Lean map (R7 audit, consolidated).** `Con(Θ′)(ν)` ↦ `conWithin T' ν`; the *represented* object is `conRunValue T' f` (universal bounded-provability decider at packed `⟨sentence code, day⟩`), not `conWithin` itself; day-`n` claim ↦ `conClaimSentence (conGamma T T' hh) n`; `⌜Θ′ₙ⌝ is inconsistent` ↦ `(representedInconsistentTheoryClaims T T' σ hσ).inconsistencySentence n`, its negation ↦ `.consistencySentence n` (definitionally `∼`). Paper's Θ = first theory argument `T`, Θ′ = second `T'`.

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
and the `_unconditional` instantiations (8 LOAD-BEARING declarations; `grep SoundOnHierarchy` still finds ~148 signature lines in 23
files, almost all inherited-removable — size by occurrences, not by the 8); 43 declarations across 5 files
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
formula with its own representability lemma . Do not spend prover time on it *with the installed substrate*.

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
supports, R3-F24). `SemidecidableComputation` served only `thm:incons`,
`BoundedComputation` only `thm:pac`/`thm:pazfc` (both structures RETIRED in tranche 8); the §4.9 nodes never passed through them.

**`PolySegStream` on the arithmetic-formula codec is a LENGTH condition.** Its per-token
value clause is vacuous along the `PaperLUVSeq` route because the emitted-token audit pins
every token to a constant (`encodeArithmeticFormulaSymbols_lt`: payload `< 19`;
`structuredPaperPrimeBlock_span`: framing `0/1/19`), so `PolyArithmeticFormulaSeq` equals
write-out there. The Gödel code is built by parser contraction and never emitted. The
residual `dd:fuel` charge is separate and levied at def:ec only.

**Compact numerals in ℒₒᵣ.** `binNumeral : ℕ → Semiterm.Const ℒₒᵣ` (Horner over `0/1/+/·`,
`StructuredPaperRpn.lean` §Compact numerals) has `binNumeralEnc_length_le : ≤ 6·log₂ v + 1`
tokens and `binNumeral_val` (value `v` in every model of `𝗣𝗔⁻`). Define compact numerals as
`Semiterm.Const` operators, not raw terms, so `!!d` and the `Rew`-normal form behave like
the unary numeral code. `invFormula`/`invPaperLUV` is the shared `1/d` template (unique/unit
proved once); `unitFracPaperLUV` and `dyadicPaperLUV` are instances. A poly-fueled count of
a repeated fixed-width token block is `PolySegStream.blocks` — the combinator that makes a
superpolynomial VALUE emittable when its NAME is a repeating pattern.

**`PaperLUVSeq` is not on the consumer API** (`API.lean` imports `Properties` + `FreezeOracle`,
nothing reaches `StructuredPaperRpn`), so witness-consumption demos for that layer are
in-file `example`s; exposing the first-order frontend is an `API.lean` decision to take
deliberately.

**Substitution lemma (CORRECTED 2026-08-30):** `polyArithmeticFormulaSeq_subst_arg` IS proved
(`SubstEmission.lean`) for an arbitrary closed-term stream `τ : ℕ → Semiterm.Const ℒₒᵣ` with an
arity-quantified emission certificate; the feared `bShift`/`Rew.q` obstruction is discharged by
Foundation's `@[simp] Rew.const : ω c = c` for closed operator constants. The earlier entry claiming
it was blocked was wrong and cost time.

**Two different 'source language' ideas — do not conflate.** A binary-numeral source node
was REJECTED (it admits strings the paper's def:ec writer cannot produce in poly time — a
permissive widening; numerals are already compactly nameable inside ℒₒᵣ via `binNumeral`).
The `iff`/`imp`/`neg` formula-source language is the CORRECT identified-not-done repair for
`dd:nnf`: `⟺` is one of the paper's primitives, so restoring it costs no permissiveness.
New route: `PaperLUV.rpnThresholdCodes` takes a single literal paper LUV into the
non-sequence `LUV.RpnThresholdCodes` that `LUV.expect_converges` (thm:ec) requires.

**`[𝗜𝚺₁ ⪯ T]` on the arithmetic-theory endpoints is a SECOND strengthening beyond the paper
(R5-F01, 2026-08-29).** It exists only because `provable_instances_re` (`ComputationDP.lean:47`)
proves r.e.-ness of `{φ | T ⊢ φ}` through Foundation's internal `Bootstrapping.Provable` +
`definability` + `internalize_provability`, which need `𝗜𝚺₁`. CORRECTION 2026-08-30: on the r.e. lane the binder is UNUSED — instance-free restatements of
`provable_instances_re`, `paperTheoremFires_re`, `exists_paperTheoremCode` compile axiom-clean, because the
proofs instantiate `V := ℕ` and `internalize_provability`/`Provable.sound` need `ℕ ⊧* 𝗜𝚺₁`, not `𝗜𝚺₁ ⪯ T`.
Removal = targeted binder deletion + import-ordered propagation; the instance IS load-bearing at
`PaperLUV.lean:91` (arithmetic inside `T`) and `QuotationTheoryPresentation.theory_sigmaOne` (thm:lp's
diagonal). A derivation-enumeration codec is NOT needed (it would require an `Encodable` for Foundation's
`Derivation2`, absent — an upstream project). Disclose beside the Σ₁-soundness charge until removed; `[T.Δ₁]` (= the
paper's c.e. axiomatization) is representation infrastructure and stays.

**Part II plan (tranche 5) — `RepresentsComputations T` renders tex:600-606 directly** (for every
total computable `f`, `∃ γ, ∀ n y, y = f n ↔ T ⊢ ∀⁰ (γ/[n̄,#0] 🡘 “#0 = ȳ”)`). The negative
literal `T ⊢ ∼γ/[z̄,1̄]` from the representation at value 0 compiles under `[𝗥₀ ⪯ T]` alone
(`R0.Ω₃` gives `T ⊢ 0̄ ≠ 1̄`; `Theory.Proof.specialize` for ∀-instantiation; Foundation has NO
external ∃-introduction for `T ⊢`). Under Style 1 the composite `n ↦ evalWithin(m,x,f n)` is one
total function, so the deferred-horizon compound and the whole `UniversalBoundedFailure` apparatus
are deleted, not ported. Architectural risk: an existentially given `γ` has no source text, so the
structured emitter cannot write it symbol-by-symbol and `theoremDP`'s fixed-schema c.e. route
breaks — exits: `paperTheoryDP` (enumerates all provable propositions), or keep the fixed
`codeOfREPred` schema with a Style-2 negative field that IS the paper's tex:4515 premise instance.
Concrete instantiation: revive Foundation's commented `codeAux_uniq`/`code_uniq` (stated for every
model of `𝗥₀`) + `models_code` + completeness ⇒ `RepresentsComputations 𝗥₀` ⇒ `𝗜𝚺₁`, `𝗣𝗔` —
a DIFFERENT object from the ruled-out `codeOfREPred` strong representability.

**The paper's formula source language** (`Construction/Witnesses/ArithmeticSource.lean`, tranche 5):
`ArithSource k` (leaf/and/or/all/exs/not/imp/iff), `compile` into Foundation NNF (`not/imp/iff` by
`∼/🡒/🡘`, rfl), `ofNNF := .leaf` (compile ∘ ofNNF = id and sourceTokens ∘ ofNNF =
encodeArithmeticFormulaSymbols, both rfl), `SourceEval` with a genuine metalevel `↔` at `iff`
(spelling it `(→)∧(→)` would trivialize the correctness theorem), `eval_compile`, tags 20/21/22
for not/imp/iff (19 stays the reserved terminator; the conditioning automaton clamps at 20 so they
are opaque payload), roundtrip `parseStructuredArithmeticFormula_sourceTokens`, and the
source-metered class `PolyArithmeticSourceSeq` — the paper's def:ec class on formulas.
`PolyArithmeticFormulaSeq` remains as the strictness foil (`PolyArithmeticFormulaSeq.toSource`
embeds it). `negFormulaCode` (De Morgan involution on Foundation formula codes) lives in
`Framework/Criterion.lean`, its spec in `ArithmeticSource.lean`, its `Primrec` proof privately in
`LIACompiler.lean`. The Gödel code of an n-deep `iff` source is ~2^(2^n) and is never emitted —
the same trade as `Code.sourceNat`; no value-metered class may ever sit on this path.
`parseStructuredArithmeticFormula_consumed_lt` now concludes `x ≠ 19` (was `< 19`).

**Literal-LUV frontend lives in `ArithmeticSource.lean`** (moved from `StructuredPaperRpn.lean`,
tranche 5; import direction forces it — `ArithmeticSource` imports `StructuredPaperRpn` for the
encoders and round trips). `PaperLUVSeq = ⟨luv, source : ℕ → ArithSource 1, compiles, structural :
PolyArithmeticSourceSeq source⟩`; threshold body is a source `imp` node (`paperThresholdSource`),
which deleted the whole `negArithTok` token-map lane. `RpnThresholdCodeSeq` unchanged (Option 1).
Capstone `iffPaperLUVSeq`/`iffPaperLUVSeq_frontend`: formula `invFormula (numeral 1) ⋏ iffChain (2n+1)`
(odd chain is valid by parity ⇒ no-op conjunct; `invPaperLUVWith` is a SIBLING of `invPaperLUV`,
not a generalization — the latter's formula must stay literally `invFormula d` for the numeral
encoding lemmas). The family is constant in VALUE (1) and varies in written size — it witnesses
the metering class, not value variation (`unitFrac`/`dyadic` do that). Strictness ledger addition:
`iffChain_not_polyArithmeticFormulaSeq` now reads as `PolyArithmeticFormulaSeq ⊊ PolyArithmeticSourceSeq`.

**`RepresentsComputations T`** (`Framework/RepresentsComputations.lean`, tranche 5 Part II) renders
tex:600-606 verbatim: `∀ f, Computable f → ∃ γ, ∀ n y, y = f n ↔ T ⊢ ∀⁰ (γ/[n̄,#0] 🡘 “#0 = ȳ”)`.
Derived: `represents_proves`, `represents_refutes` (negative literal at a substituted instance),
`represents_refutes_all` (∀-form), `RepresentsComputations.consistent` (the paper's line-604 remark —
no separate consistency carry needed), `reprBody`/`reprAll`/`reprAllSchema` (the claim family IS
the numeral-instance family of ONE fixed schema, so `provable_instances_re` enumerates it even
though γ is existential). Instantiated at `𝗣𝗔⁻`, `𝗜𝚺₁`, `𝗣𝗔` (`R0Representability.lean`,
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

**Part II outcome (tranche 5).** Tag 3 (bounded claims) closes from consistency: the represented
claim family's def:ec certificate is built on the SOURCE language (`SubstEmission.lean`:
`reprBodySource = .iff (.leaf γ(n̄,ν)) (.leaf (ν = 0̄))`, wrapped `.exs (.not …)`, emitted by
`structuredPaperSourcePrimeBlock true`; the bridge to `representedClaimSentence` is rfl), and
`thm:dontwait`/`thm:pac`/`thm:pazfc` live in `ComputationRepresented.lean` over `paperTheoryDP T`
under `[T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗥₀ ⪯ T] [RepresentsComputations T]` — no soundness.
`paperTheoryDP_nonvacuous` was ALWAYS soundness-free (needs only `[Entailment.Consistent T]`).
Retired: the whole `UniversalBoundedFailure` apparatus. Dead-but-inhabited surface for a
consolidation pass: `UniversalBoundedHalts`, `universalBoundedHaltingSchema`, `theoremDP` tags 2/3,
`ComputationTheoryPresentation.boundedHalting_enters/boundedFailure_refutes` (no consumer now).
**Tag 7 (quotation) CLOSED — tranche 6, 2026-08-30 — and the earlier 'architectural obstruction'
diagnosis was WRONG, not superseded.** The universal quote evaluation never needed a
`RepresentsComputations` γ (per-decider ⇒ paper-prime atom ⇒ import reorganization — every step
after the first was unnecessary). It has a Foundation `code` formula (`Nat.ArithPart₁.exists_code`,
which takes a PARTIAL `Nat.Partrec'`), and ONE such formula carries both literals as two value fibers:
`Framework/QuoteRepresentability.lean` `valueSchema c y := (code c)/[‘↑y’, #0]`,
`universalQuotePos := valueSchema universalQuoteCode 1`, `universalQuoteNeg := … 0`;
`valueSchema_prov` (`[𝗥₀ ⪯ T]`, both literals by Σ₁-completeness — the negative is now as cheap as the
positive) and `valueSchema_exclusive_prov` (`[𝗣𝗔⁻ ⪯ T]`, proved semantically in one shot:
`Arithmetic.complete` + `code_uniq` + `numeral_inj_iff`). `theoremDP_hworld` tag 7 closes from
`Entailment.Consistent` like tags 1/3; 87 inherited binders became `[Entailment.Consistent T]` with
zero proof breakage; `thm:lp` survived because the schemas are still compile-time constants.
**Σ₁-soundness is on 0 of 105 canonical endpoints**; the only `SoundOnHierarchy` left is
`loopsTheory_soundOnSigma1` (concrete witness theory). General lesson: when two schemas must be
provably exclusive, reach for ONE `code` formula read at two values, never for two `codeOfREPred`s
or a `RepresentsComputations` γ. `QuoteRepresentability.lean` now owns the single copy of
`codeAux_uniq`/`code_uniq`. The R2-F02 'Σ₁-soundness is a live strengthening' entry is HISTORICAL.

**Instantiation asymmetry of `RepresentsComputations`.** `representsComputations_of_peanoMinus`
takes `[𝗣𝗔⁻ ⪯ U]` AND `[ℕ↓[ℒₒᵣ] ⊧* U]` — standard-model truth VERIFIES the premise for the
registered instances (`𝗣𝗔⁻`, `𝗜𝚺₁`, `𝗣𝗔`) and is used by no consumer. A Σ₁-unsound theory such as
`𝗣𝗔 + ¬Con(𝗣𝗔)` satisfies the paper's assumption but is not witnessed here (a syntactic proof of
representability without the standard model would be needed — a Foundation-upstream item).
`check-paper-nodes.sh` blocks inventorying the 36 unannotated interface/supporting lemmas; they are
covered transitively by the annotated endpoints (same ruling as R3-F24). `dd:nnf` now names an
architecture, not a substitution.

**Public atom tag inventory** (scattered `*Tag` defs): 0–3 computation claims, 4 quotation
(`quotationClaimCode`), 5 `productTag`, 6 `semanticPrimeTag`, 7 `paperPrimeTag`, 8 `oldLanguageTag`.
Every "atoms are fresh for tag X" lemma is a case split over this table (`ProductDefinition.lean:194`,
`SemanticProduct.lean:286`, `OldLanguageLift.lean:108`, `PaperTheoryDP.lean:301`). Cutting two import
edges (`PaperFirstOrder.lean:1 → SemanticSource`, used only by `paperPrimeDecompose_semanticPrimeFresh`;
`PaperTheoryDP.lean:2 → ComputationDP`, used only by the 'Joint compatibility' section :300-419)
collapses the QuotationAffine reordering to 8 modules — recorded in case route (a) is ever needed.

**A formula-metered atom CAN carry a machine/input pair — as a compact numeral (CORRECTED
2026-08-30).** The constraint is on the substituted term's TOKEN RUN (must be a `PolySegStream`),
not on its VALUE: Foundation's unary `numeral` costs its value, but `binNumeral` (now base-4 uniform
Horner, two constant-width runs driven by `len4`/`dig4`) costs O(log v), so a `BigDigits` value
stream is admissible — `polySegStream_binNumeralEnc (hv : BigDigits v)`. This is exactly how R5-F08
was fixed: `haltingArgClaimSentence machines inputs n := universalHaltingSchema/[binNumeral
(haltingClaimInput (mₙ) (xₙ))]` and, for the bounded lane, ONE γ per horizon program for the
universal decider `universalRunValue steps` at `binNumeral (boundedArg machines inputs n)`; value
transfer by `provable_subst_iff_of_val` (completeness both ways, needs only `𝗣𝗔⁻ ⪯ T`).
`hm`/`hi` are load-bearing (deleting them breaks the `BigDigits` certificate). Anti-vacuity:
`haltingArgClaimSentence_ne_of_halts_ne`, `representedClaimSentence_ne_of_runValue_ne`. Why base 4:
`PolySegStream.blocks` needs a constant block width; base-2 Horner branches on parity.

**EXTENSIONALITY TRAP (R5-F08/F09, blind audit 2026-08-30 — the worst find of the run).** Foundation's
`codeOfREPred (A : ℕ → Prop)` and `RepresentsComputations.repr f` depend only on the EXTENSION of the
predicate/function. A claim family built as `codeOfREPred (fun n => P (mₙ) (xₙ))` or `repr
(boundedRunValue …)` collapses to one fixed sentence family as soon as an endpoint hypothesis pins the
extension (`∀ n, halts` ⇒ `fun _ => True` by funext+propext; `hnever` ⇒ const 0; `hconsistent` ⇒
const 1) — the sentence then names NO machine and the e.c. hypotheses `hm`/`hi` are provably decorative.
The tranche-5 `paperTheoryDP` migration of thm:dontwait/pac/pazfc (and Part II/H's halts/loops) did
exactly this and shipped five vacuous renderings that two rounds of fixers and the orchestrator called
improvements. The paper's sentence names the machine (`⌜m⌝`, `⌜f⌝(⌜n⌝)`, tex:606/1931). Correct design:
represent the UNIVERSAL evaluator once (one γ per horizon `f`, or the fixed universal r.e. halting
schema) and write the pair `Nat.pair (sourceNat mₙ) xₙ` into the sentence as a compact
`binNumeral` (O(|source|) tokens — what `BigDigits` bounds), emitted digit-by-digit from the
`BigDigits` certificate. Standing test for any represented claim family: substitute two sequences with
the same extension but different programs — if the sentences coincide, the rendering is extensional.

**After the R5-F08 fix (blind re-test 2026-08-30).** Machine dependence of the §4.9/§4.10 sentences is
DEFINITIONAL (`binNumeral (haltingClaimInput (mₙ) (xₙ))` substituted into a fixed schema; `binNumeral`
and `sourceNat` injective), and `hm`/`hi` are the only route to `sentence_poly` — but the two
anti-vacuity lemmas (`haltingArgClaimSentence_ne_of_halts_ne`, `representedClaimSentence_ne_of_runValue_ne`)
separate sentences only when BEHAVIOUR differs; the full "same extension, different program ⇒ different
sentence" statement is true but unprovable with the installed substrate: it needs a syntactic
substitution-injectivity/occurrence lemma (σ mentions `#0` ⇒ `σ/[t] ≠ σ/[t']` for `t ≠ t'`), absent from
Foundation (`Foundation/FirstOrder/Syntax` has no `subst_injective`). Queued as tranche-7 infrastructure
(local proof by induction on formulas; upstream candidate). Argument-INsensitivity of the opaque schema IS
refutable from `universalHaltingSchema_spec` (non-constant `UniversalCodeHalts`).
`[T.Δ₁]` (a Δ₁ axiom SET) is strictly stronger than the paper's "c.e." — Craig's trick gives a deductively
equivalent Δ₁ axiomatization, so every `T ⊢`-statement transfers, but that is not formalized; disclosed
2026-08-30 as representation infrastructure (global charge, judgment call). Day indexing is ℕ from 0 while
the paper's is ℕ⁺: a day-indexed premise must hold at day 0 too — the retired `ordinaryBoundedComputation`'s
`0 < n` predicate failed there and could not witness `hconsistent` (carrier deleted in T8, the point stands). `thm:pac` and `thm:pazfc` were, at this point, the same theorem by `rfl`
at every layer — SUPERSEDED in tranche 8, which separated them (see the T8 entries below). thm:dontwait's γ represents the
COMPOSITE decider `universalRunValue f` (⌜g⌝(⟨⟨m,x⟩,n⟩) ≠ 0), not `f` alone — no new hypothesis.

**Tranche 7 (2026-08-30).** `[𝗜𝚺₁ ⪯ T]` deleted at `provable_instances_re` and propagated (94/105
endpoints free): the r.e. lane never needed it — `internalize_provability`/`Provable.sound` are
instantiated at `V := ℕ`, so the side condition is `ℕ ⊧* 𝗜𝚺₁`, and `definability` needs only `T.Δ₁`.
Represented lane and `theoremDP_hworld` now read `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`
(`𝗥₀` is strictly too weak for `provable_subst_binNumeral_iff`; `𝗜𝚺₁ ⪯ T` gives `𝗣𝗔⁻`/`𝗥₀` by
instance search but `𝗥₀ ⪯ T` does NOT give `𝗣𝗔⁻ ⪯ T`). Genuine survivors: `unitFracPaperLUV*`
(rational-cut arithmetic INSIDE `T`), `thm:lp` (Foundation's `parameterized_diagonal₁` lives at
`𝗜𝚺₁`); the seven closed quotation rows carried it only through the field
`QuotationTheoryPresentation.theory_sigmaOne` (two consumers, both on the diagonal) — moved to a
binder on those two lemmas in T7/D. **Substitution injectivity is now in the repo:**
`Framework/SubstOccurrence.lean` (`Semiformula.Mentions`, `rew_eq_of_not_mentions`,
`eq_of_rew_eq_of_mentions`, `subst_injective_of_mentions`, Foundation-only imports; the
occurrence-restricted refinement of `rew_eq_of_funEqOn`); `universalHaltingSchema_mentions_zero`;
and the FULL anti-extensionality test is a theorem: `haltingArgClaimSentence_ne_of_source_ne`
(distinct `sourceNat` ⇒ distinct sentence, no behavioural hypothesis, invocable inside one family);
bounded lane `representedClaimSentence_ne_of_arg_ne` takes `γ.Mentions 0` as a hypothesis (γ is
existential). Foundation has `Semiterm.bv` but no formula occurrence notion and no
`bShift_injective` (derive via `Rew.map_inj (Fin.succ_injective n) Function.injective_id`).
`Scratchpad.lean` at the repo root is TRACKED — never use it as scratch.

**Ruling (Anson, 2026-08-30): `thm:lp`'s `[𝗜𝚺₁ ⪯ T]` is representation infrastructure.** The paper
invokes "the diagonal lemma" for any theory representing computations; Foundation's
`parameterized_diagonal₁` is stated at `𝗜𝚺₁`, so the instance is the ambient theory of a borrowed
lemma, not a strengthening of the theorem's premise. Charged once globally beside `[T.Δ₁]`
(Craig's trick) — neither lowers a row. With Σ₁-soundness gone and the r.e.-lane `𝗜𝚺₁` deleted,
the eleven quotation/computation rows classify `exact`; the remaining qualified rows are the §4.10
three (`thm:pac`, `thm:pazfc`, `thm:incons`).

**§4.10 substrate map (tranche 8 scoping, 2026-08-30; all names #check-verified).** Paper `Con(Θ′)(ν)`
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
paraphrase; decorative naming is rejected. `inconsistencyClaim`/`consistencyClaim` are two DISTINCT tagged
atoms where the paper uses one sentence and its negation (tex:1863-1866) — collapse via
`paperPrimeDecompose`. `RestrictedProvability.lean` has no olean in this checkout and is not needed.

**T7/D (2026-08-30): `QuotationTheoryPresentation.theory_sigmaOne` retired** (fields now
`toComputationTheoryPresentation quote_positive_enters quote_negative_refutes`); the diagonal's two
consumers take an ordinary `[𝗜𝚺₁ ⪯ T]`. The seven closed quotation endpoints read
`[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`; `lic_introspection_closed` instantiates at `𝗣𝗔⁻` itself
(no `𝗜𝚺₁` exists in that elaboration) — a genuine widening. Census (elaborated `#check` over the 105
canonical names): `SoundOnHierarchy` 0; `𝗜𝚺₁ ⪯` exactly 3 — `unitFracPaperLUVSeq`,
`unitFracPaperLUVBoundedSequence` (arithmetic inside `T`), `thm:lp` (`parameterized_diagonal₁`; prints
a redundant `𝗣𝗔⁻` too — `omit` cannot drop a referenced section variable). TRAP: `𝗜𝚺₁ ⪯ T` is spelled
`[ISigma 1 ⪯ T]` across the semantic-lifted lane (64 sites) — grep BOTH spellings (likewise
`PeanoMinus`/`R0`). Foundation registers the weakening chain as instances (`𝗣𝗔 ⪯ T → 𝗣𝗔⁻ ⪯ T`,
`𝗜𝚺₁ ⪯ T → 𝗣𝗔⁻ ⪯ T`, `𝗣𝗔⁻ ⪯ T → 𝗥₀ ⪯ T`): state the single strongest binder a proof spends.
`FinitePerturbationWitness.lean:36` keeps `𝗜𝚺₁` (its `cxQuote` runs the diagonal). Touching
`SemanticQuote.lean` costs ~1h per rebuild (SemanticRegistryProduct/SemanticLiftedCCEE at
`maxHeartbeats 2000000`, silent for ~20 min).

**Round-6 blind audit (2026-08-30): structure verified; one real residual found.** Census: soundness
0/105; `𝗜𝚺₁ ⪯` 3/105; `[T.Δ₁]` 23; `[𝗣𝗔⁻ ⪯ T]` 18; `[RepresentsComputations T]` 3;
`[Entailment.Consistent T]` 14 (grep the elaborated signatures, never the word "Consistent" — it
matches `PCWorld.ConsistentWith*` and inflates to ~60). **`[𝗣𝗔⁻ ⪯ T]` is a genuine strengthening
beyond the paper**: representability yields `Θ ⊬ n̄ = m̄` but never `Θ ⊢ n̄ ≠ m̄` (Ω₃); Robinson's R
represents all computable functions without containing 𝗣𝗔⁻. It is load-bearing for exactly two
things — `provable_subst_iff_of_val` (the compact `binNumeral` spelling def:ec forces) and
`code_uniq`'s `rfind` case (object-level tag-7 exclusivity; the PAPER's exclusivity is
metatheoretic via the representability biconditional's ← direction and needs no Θ-arithmetic; ours
is object-level to keep the stage-world proof constructive without soundness). Never write that
𝗣𝗔⁻/𝗥₀ is "presupposed by representability". Also: `RepresentsComputations` is over `f : ℕ → ℕ`
where the paper is ℕ⁺→ℕ⁺ (at-least-as-strong; disclosed); `valueSchema`'s `code c` carries the
VALUE at `#0` and the ARGUMENT at `#1` — opposite of the `reprAll` convention (hence `swapArgs`);
the canonical surface runs THREE markets (`theoremDP` 42, `paperTheoryDP` 5, `canonicalCCEEDP` 3)
while the paper fixes one 𝕡 — the union `theoremPaperDP` exists unused; a consolidation question.

**Known dead weight.** `PolyEF` (`Framework/Computable.lean:258`) is a dead-end layer:
consumed only by other `PolyEF` lemmas, never converted to any emission class. It is a
consolidation candidate, recorded here so it is not mistaken for load-bearing.


**The propositional rendering of `Con(Θ)(ν)` is a NEGATED atom, and this is forced, not chosen.** `representedClaimSentence γ t` is the paper-prime of `reprAllTerm γ 0 t`; `paperPrimeDecompose (reprAllTerm γ 0 t) = ∼representedClaimSentence γ t`, because a universal sentence is not prime and its ∃-negation is. So `conClaimSentence γ n := ∼representedClaimSentence γ (binNumeral (conClaimArg n))`, and the DP publishes it through `paperTheoryDP_covers_representedClaim_neg` (from `T ⊢` the value-0 sentence). Do not reach for the un-negated atom: that one is "the bounded search SUCCEEDS" and would give `≈ₙ 0`, not the paper's `≈ₙ 1`.

**Stage (ii) shape for thm:pazfc, from the stage-(i) substrate.** `BProv`/`conWithin`/`conRunValue` already take the theory as an ordinary parameter, so `conRunValue T' horizons` represented IN `T` is the whole construction — no new substrate. The one genuinely new obligation is the positive literal: `conWithin_of_consistent` gives truth of the `T'` claims from `Consistent T'`, and `RepresentsComputations T` converts truth into `T ⊢` since the decider is total computable. Stage (ii) needs NO soundness premise — only `Entailment.Consistent T'` as an explicit hypothesis on the second theory, exactly the paper's own premise for Θ′.

**[CORRECTED R7: the paper NEVER assumes `Θ ⊆ Θ′` — tex:1881-1886 says 'any recursively axiomatizable consistent theory'; the Lean statement MATCHES the paper's hypotheses, and no 'more general than the paper' claim is earned. The remainder of this entry records the (sound) dependency analysis only.]** Verified unused: `conRunValue_computable` needs only `[T'.Δ₁]`, `RepresentsComputations T` is about T, `conWithin_of_consistent T' hcons` about T′ — no step relates the theories. Dropping it strengthens the theorem in the harmless direction and keeps typeclass assumptions minimal; disclosed in the endpoint docstring ("More general than the paper"). Do not "restore" it as a fix — the inclusion is what makes the paper's result *interesting* (why Θ cannot prove Con(Θ′)), not what makes it true; the 𝗜𝚺₁/𝗣𝗔 example carries that interest concretely.

**[EXECUTED T8/iii — all seven deleted; `thm:pac`/`thm:pazfc` each have one carrier again.]** Dead after T8/ii, verified by grep (stage-(iii) retirement list): Zero consumers apart from `#print axioms`/`AxiomAudit`: `alwaysBoundedComputation`, `ordinaryBoundedComputation` (`ComputationSyntax.lean:670,648`), `BoundedComputation` (`:596`), `representedDecidableClaimsOfComputation` (`ComputationRepresented.lean:541`), `lic_belief_finitistic_consistency_ofComputation` (`:752`), `lic_belief_stronger_theory_consistency_ofComputation` (`:773`), abstract `lic_belief_stronger_theory_consistency` (`Properties/MetaLearning.lean:80`). CONTRAST: `lic_belief_finitistic_consistency` (`MetaLearning.lean:66`) is LIVE — both `_unconditional` endpoints route through it. No separate `consistentWithin` definition exists; `conWithin` is the live §4.10 predicate. Retirement also shrinks `AxiomAudit.lean:848,1012-1014` and `#assert_fields BoundedComputation` at `:1284`.

**The LI-CANONICAL block is a curated view, not the superset of the topical `#assert_axioms_clean` blocks.** Retiring seven declarations named only in topical blocks changed the LI-CANONICAL count by zero: LI-CANONICAL names exactly what `scripts/coverage-classification.md`'s endpoints table names (enforced two-way), while topical blocks are internal axiom regressions. Before budgeting a census-prose edit for a retirement, check which block the name is in; measure with `sed -n` between the real marker lines — an `awk /BEGIN/` sweep also matches the prose mentions of the markers and silently inflates the count.

**`thm:incons` does NOT charge `dd:proofcode`.** Its sentence is the *unbounded* existential over proofs (the paper's `⌜Θ′⌝ is inconsistent` is the negation of the universal generalization of `Con(Θ′)(ν)`, tex:1863-1866): nothing is metered, so the symbol-count-vs-Gödel-number substitution does not arise. If any ledger text charges it there, drop it.

**The `thm:incons` theory sequence is the deduction family `Θ′ₙ := Θ₀ ∪ {σₙ}`, disclosed.** Forced by Foundation: `Bootstrapping.Derivation T` is `(construction T).Fixpoint` with `T` a META parameter — no uniform-in-theory-code derivability predicate exists, so a sequence of theories cannot enter one sentence as an argument. The deduction theorem collapses the day's theory to one sentence code, which is genuinely named. Retired by the uniform-in-theory-code work (9b).

**Write-out class for a sentence-code family goes on the NEGATION codes.** `hσ : BigDigits (deductionFamilyArg σ)` with `deductionFamilyArg σ n = ⌜∼(σ n)⌝` — that code is what the day's sentence writes out. Deriving it from `BigDigits (fun n => ⌜σₙ⌝)` is NOT free: `∼` on arithmetic `Semiformula` is NNF recursion, not the propositional `φ 🡒 ⊥` that `BigSentenceCodes.neg` exploits. Foundation has a code-level negation with a Σ₁ graph (`neg L`, `negGraph L`, used by `Theory.RosserProvable`) if it is ever needed.

**The `thm:incons` witness is constant in the day (`σₙ := ⊥`), a considered choice.** A day-varying refutable family needs `BigDigits` for formulas containing the day's numeral (digit-count over unary numerals, well over 50 lines). Day-variation of the rendering is a theorem instead: `inconsistencyArgClaimSentence_ne_of_arg_ne` separates any two distinct adjoined-axiom codes with no behavioural hypothesis.

**`hσ : BigDigits (deductionFamilyArg σ)` on `thm:incons` is STRICTLY STRONGER than `def:ec` (R7-C1).** `BigDigits` bounds a base-4 digit count — the paper's write-out meter only when the number IS the object's written form. `⌜∼σₙ⌝` is a formula's Gödel code; Foundation's encoding pairs at every node, so digits ~ 2^depth — the same failure mode that disqualified `Encodable.encode` as a machine-naming map. The class admits only O(log n)-depth families and EXCLUDES paper-admissible short-source/deep-parse (`iffChain`-style) ones. SECOND charge on the thm:incons row, beside the deduction-family paraphrase. Faithful repair: state the premise on `PolyArithmeticSourceSeq` (`polySegStream_binNumeralEnc` already admits the family); queued with the 9-series.

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


**`thm:pac` and `thm:pazfc` are NO LONGER the same theorem (T8/i);** the `rfl` example recording their identity has been deleted. `thm:pac` is now about the arithmetized `Con(Θ)` family at Θ itself; `thm:pazfc` (pre stage-ii) still takes a caller-supplied `BoundedComputation`. `lic_belief_finitistic_consistency_ofComputation` survives unchanged and still carries `Paper node: thm:pac`, so that node temporarily has two carriers — it is the superseded generic lane, retired in stage (iii) with `BoundedComputation`.

**`dd:proofcode` is a live type-`(c)` substitution disclosed globally** (ledger *Global model disclosure*, README modeling-boundary item 4, `LogicalInduction.lean` glossary): §4.10's finite proof searches are metered by the derivation's Gödel number, not the paper's symbol count, because Foundation's internal derivations expose no size function (`Semiformula.bv` measures a formula, not a derivation). Charged once globally on the `dd:fuel` precedent rather than against `thm:pac`, which is why that row reads `exact`. Queued for retirement by the Foundation symbol-measure work (tranche 9a).

**The paper has NO `Θ ⊆ Θ′` hypothesis in `thm:pazfc`** — tex:1881-1886 assumes only "a stronger consistent recursively axiomatizable theory" (the "stronger" is informal prose). Every repo passage claiming the Lean statement is "more general than the paper" for omitting containment asserted a premise the paper never had; the Lean statement MATCHES the paper's hypotheses. Deleted from the `.lean` docstrings in R7; ledger/README/LI_READING copies corrected in the R7 docs pass.

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

**Foundation's arithmetic pairing IS Mathlib's at ℕ — the key that unlocks §4.10.** `LO.FirstOrder.Arithmetic.IOpen.nat_pair_eq : ⟪n, m⟫ = Nat.pair n m` is already in Foundation (IOpen/Basic.lean:761); the projections follow in three lines from it and `pair_unpair` (`π₁ z = z.unpair.1`, by `conv_rhs => rw [← h]; simp`). `definability` cannot see through `Nat.unpair` but handles `π₁`/`π₂` (they carry 𝚺₀ definability instances), while `Computable`/`Primrec` want `Nat.unpair`. State the definable predicate with `π₁`/`π₂`, the computable function with `Nat.pair`, bridge with `pi₁_nat`/`pi₂_nat`. No `Nat.sqrt` `Primrec` work is involved anywhere — computability comes entirely from `re_iff_sigma1`.

**The §4.10 bounded-derivability decider is cheap, not a proof-checker project.** `∃ d < π₂ z, Bootstrapping.Proof (V := ℕ) T d (π₁ z)` and its negation are BOTH closed by a bare `unfold; definability` (from `Proof.definable'`), then `ComputablePred.computable_iff_re_compl_re'` (the PRIMED form — the unprimed one wants a `DecidablePred` instance you do not have) with `re_iff_sigma1` on each side. `provable_of_standard_proof` needed only `refine ... (n := d) ?_; simpa [Nat.cast_id] using h` under `maxHeartbeats 1000000`. Whole module: under 30 minutes. No proof checker is needed at all.

**[DISCHARGED T8/iii — the lemma is now public `BigSentenceCodes.neg` in `Framework/WriteOut.lean` beside `and`; rebuild cost was ~10 min, not ~1h.]** Historical:  Foundation's `∼φ = φ 🡒 ⊥` is `rfl` and `rpn` tags `imp` with `2`, so the proof is `BigSentenceCodes.and`'s verbatim with `3 ↦ 2`, second stream `BigSentenceCodes.const ⊥`, one fewer `if_neg`. It sits private in `ComputationRepresented.lean` purely to avoid the ~1h WriteOut.lean full-library rebuild; it belongs in `WriteOut.lean`'s `BigSentenceCodes` namespace next to `and` — move it during a tranche that already pays that rebuild.

**[REFUTED R7 — `mentions_zero_of_repr_ne` derives it from the spec + non-constancy; see the R7 correction entry. The counterexample below bounds the claim to CONSTANT deciders only.]** Historical claim: `γ.Mentions 0` is not derivable from the representation spec on the Con lane — concrete counterexample, not missing infrastructure: at a horizon constantly `0`, `BProv T φ 0` is `∃ d < 0, …`, always false, so the represented function is the constant `0` and a `γ` ignoring its first argument represents it correctly. The prose "representation at two arguments with different values forces mentions" cannot be instantiated within one family. `conClaimSentence_ne_of_day_ne` takes `γ.Mentions 0` as a hypothesis, exactly like `representedClaimSentence_ne_of_arg_ne`. Do not spend prover time trying to discharge it.

**The strength column of `scripts/coverage-classification.md` is a closed vocabulary.** `check_endpoint_coverage.py` defines `STATUSES = {exact, strengthened, corrected, refuted, qualified}` and fails any other value, and `gen-trust-surface.py` indexes `counts[status]` directly, so a decorated status like `exact (dd:proofcode)` is a hard failure in two places. Disclosure qualifiers belong in the justification cell, not the status cell.

**The trust-surface page's per-node prose is NOT in `docs/`.** `docs/trust-surface.html` is generated by `scripts/gen-trust-surface.py`; the LI "How the panes line up" reading notes are the `LI_READING` dict literal (~lines 890-900 of that script), and the "What to check" footer comes from the ledger's justification column. Edit the ledger and/or the generator, then run `python3 scripts/gen-trust-surface.py` and `python3 scripts/check_trust_surface.py`.

**`LogicalInduction/README.md`'s headline numbers are machine-re-derived** from the ledger by `check_readme_counts` in `check_endpoint_coverage.py`, matched by regexes on the *prose shape*. Changing one node's status forces edits at several places: the status table row and — for `instantiated` nodes — the "Of the 53, N are also instantiated … X at exact or strengthened, Y at qualified" sentence. The check is fail-closed on the pattern too: rewording that sentence out of shape fails like a wrong number does.

**Estimate calibration, T8/ii: the whole stage was one build cycle.** The stage-(i) substrate was already theory-parametric (`variable (T : ArithmeticTheory) [T.Δ₁]`), so the second theory required ZERO changes to `BoundedConsistency.lean` — only the four representation-layer declarations hardwired `T' = T`. If a future stage looks like "add a second theory parameter", check whether the substrate is already parametric before budgeting.

**A tranche whose intermediate step cannot compile must not be split into two commits.** Generalizing `conGamma` to two theories immediately breaks `thm:pac`'s call site in the same file, so a parametrize-only commit would be red. Where a packet's commit split implies a red intermediate, prefer one green commit and say so.

**`lake build APITests` is NOT a whole-library gate.** It reports MORE jobs (3647) than `lake build LogicalInduction` (2953) while covering LESS of the library: modules outside the API import closure (e.g. `ComputationDP.lean`) are never recompiled, and a later `lake env lean` probe then reads a stale olean — an already-deleted binder printed as still present. Tell: `stat` the .lean vs its .olean. Gate library-wide changes with `lake build LogicalInduction`; treat APITests as an additional, narrower target.

**Explicit `[𝗥₀ ⪯ T]` beside `[𝗣𝗔⁻ ⪯ T]` is always droppable** through Foundation's `instance [𝗣𝗔⁻ ⪯ T] : 𝗥₀ ⪯ T` (`Arithmetic/Schemata.lean:396`); `⪯` is a Prop class, so proof irrelevance means data-valued definitions cannot change under the swap. UNLIKE the `lic_paradox_resistance_ofDiagonal_unconditional` case, where the redundant binder is a section variable the proof term references and `omit` is rejected. Explicit binder → droppable; referenced section variable → not.

**A BOUNDED decider is the WRONG substrate for `thm:incons`.** The bounded lane (`conRunValue`, one γ per horizon) fits `thm:pac`/`thm:pazfc`, whose claim IS a finite search. `thm:incons`'s claim is Σ₁ and unbounded — a horizon-based rendering needs a proof-fits-under-the-bound premise the paper lacks. Correct shape: the HALTING lane's — one fixed `codeOfREPred` schema, day's data in the argument via `binNumeral`, positive literal by `re_complete_mp`. Structurally `thm:incons` is a sibling of `thm:halts`, not of `thm:pac`.

**Foundation already has the arithmetized provability predicate AND both bridges.** `Bootstrapping.Provable T (φ : V) := ∃ d, Proof T d φ` (`Syntax/Proof/Basic.lean:467`) with `Provable.definable : 𝚺₁-Predicate` (`:525` → `REPred` via `re_iff_sigma1` in one line), and `@[simp] provable_iff_provable [T.Δ₁] : Provable T (⌜φ⌝ : ℕ) ↔ T ⊢ φ` (`DerivabilityCondition/D1.lean:34`) — BOTH directions, no consistency hypothesis. The tranche-8 scoping note that only `provable_of_standard_proof` exists was incomplete. (Manual route at `V ≠ ℕ`: inside `rosser_internalize`, `let n : ℕ := ⌜h.get⌝; simp [coe_quote_proof_eq]`.)

**Deduction theorem: adjoin is spelled `σ ∷ T`.** `Entailment.deduction_iff : φ ∷ 𝓢 ⊢ ψ ↔ 𝓢 ⊢ φ 🡒 ψ` (`Logic/Entailment.lean:484`) applies to `Theory L` via the instance at `FirstOrder/Basic/Calculus.lean:375`. `¬Consistent (σ ∷ T) ↔ T ⊢ ∼σ` is four rewrites: `not_consistent_iff_inconsistent`, `inconsistent_iff_provable_bot`, `deduction_iff`, `← LO.Entailment.N!_iff_CO!`. Adjoining needs no `Δ₁` instance — the adjoined theory appears only in the premise.

**`lic_provind_false` cannot deliver the second conjunct of a collapsed negation pair.** It wants `∼ψ ∈ DP.D k`; at `ψ = ∼φ` that is `∼∼φ`, which `paperPrimeDecompose` never emits (range = {atom, ∼atom}). Fix: `provind_neg_false` (private, `Properties/MetaLearning.lean`), same `affine_provind_theory_eq` skeleton with `hφ.neg` for codes, payout via `(PCWorld.holds_neg v (φ n)).mp`. No new premise — the negation conjunct is free from the positive one.

**`omit [inst] in` must precede the DOCSTRING.** `/-- doc -/` then `omit [...] in` then `lemma` is a parse error (`unexpected token 'omit'`) that only surfaces in a full `lake build`. Order: `omit [...] in` / `/-- doc -/` / `lemma`.

**Retiring the `thm:incons` tag-keyed atoms is a `ComputationDP` refactor, not a deletion.** `ComputationClaimKind.inconsistency`/`.consistency` are enumerated by `theoremDP` itself (`ComputationDP.lean:85-86,141-142,243-250,282-297,407-409`), so removal renumbers the tag space and reworks `theoremDP_hworld`. Budget it as its own tranche.

**Estimate calibration, T8/iv: build cycles were the whole cost.** Substrate + collapse + new lane each compiled on the first or second `lake env lean`; three full serialized `lake build` cycles (~30-45 min each) dominated. Budget build cycles, not proof effort — batch every file edit before the first full build.

**Ledger rows in `scripts/coverage-classification.md` are strictly ONE LINE each** — no fenced blocks, no `<br>`, no continuation rows; quoted Lean signatures must be flattened into one inline code span (as the T8/iv `thm:incons` row does), or the table parse the endpoint-coverage checker depends on breaks.

**`_ofComputation` is NOT a single retired lane.** Tranche 8 retired only the §4.10 members. The §4.12 feedback-truth family — `lic_wub_ofComputation`, `boundedCombination_wubaff_ofComputation`, `luv_wubexp_ofComputation` and their `_unconditional` forms — is live, curated, and is the shown endpoint for `thm:wub`/`thm:wubaff`/`thm:wubexp`. Qualify any "the `_ofComputation` lane was retired" sentence by §.

**`LI_READING` notes in `gen-trust-surface.py` drift independently of the ledger** and nothing cross-checks them: `check_trust_surface.py` verifies page-matches-inputs, not prose-matches-status. Three notes survived multiple tranches asserting "[𝗜𝚺₁ ⪯ Θ] keeps this row qualified" after those rows went exact. When a row's status or binders move, grep `LI_READING` for that label explicitly.

**Day-varying `thm:incons` witness at unbounded description length is blocked on a MISSING COMBINATOR, not size.** For `σₙ := "binNumeral n ≠ binNumeral n"` the code's bit length is Θ(√n), so `BigDigits (fun n => ⌜∼σₙ⌝)` is TRUE — but Foundation's `toNat` pairs at every node, so the code is a `Nat.pair` shell iterated Θ(log n) times over Horner recursion, and every `BigDigits` closure (`const`, `natPair`, `succ`, `add`, `mul`, `ifZero`, `comp`) composes only constantly many times; `PolyFueled.prec` forbids bignum state; `ofBase16Digits` doesn't apply (`Nat.pair` isn't digit concatenation). Needed: `BigDigits.precBig` + base-4 digit theory of `Nat.pair` at unbounded nesting — surveyed at 800-1500 lines. Do not re-scope without reading this.

**Quote injectivity for `ArithmeticSentence` at `V := ℕ`: neither `decide` nor `Nat.cast_id`/`Nat.cast_inj` works.** `decide` sticks on `Nat.beq` (noncomputable def); the `↑` from `quote_eq_encode` resists both cast lemmas. Working one-liner: `Sentence.quote_def` is `rfl` — state at the Semiproposition quote by type ascription, use `@[simp] Semiformula.quote_inj_iff` + `Rewriting.emb_injective`. See `deductionFamilyArg_ne_of_ne`.

**`one_ne_zero` is ambiguous inside `LogicalInduction` with `LO.FirstOrder.Arithmetic` open** — spell `_root_.one_ne_zero`. `T ⊢ ⊤ ⋎ ⊤` is not closed by `simp`; `cl_prover` closes it (via `Foundation.Meta.ClProver`).

**After editing an UPSTREAM file, `lake env lean` on a downstream file reads stale oleans.** Cheap iteration: `safe-lake.sh build <leaf module target>` (e.g. `LogicalInduction.Construction.Witnesses.ComputationRepresented`) rebuilds the chain then iterates at ~1-3 min. Budget the four full gates (~1h serialized on a loaded machine), not the proofs.

**Cleared suspicions from the R7 blind audit — do not re-raise.** (1) The horizon `f` is never metered and never enters a sentence: `conRunValue T' f` evaluates it inside the decider, the day-argument is `⟨⌜⊥⌝, n⟩` (poly-valued, `conClaimArg_digits`) — `ack` genuinely admissible. (2) The Con sentence is a NEGATED atom while incons is a BARE atom — correct, not an inconsistency: Con(Θ′)(ν) is a ∀-sentence (∃-negation is the prime), inconsistency is itself Σ₁; "normalising" polarities breaks the `paperTheoryDP_covers_*` bridges. (3) `provind_neg_false`'s world use at arbitrary stage is fine — the affine callback hands back a `ConsistentWithTheory DP` world (all stages). (4) `thm:incons`'s sentence is `Prov_{Θ₀}(⌜∼σₙ⌝)`, related to `Θ′ₙ ⊢ ⊥` only via the EXTERNAL deduction theorem — disclosed, and provability induction needs no internal one. (5) `codeOfREPred` is `Classical.epsilon`-chosen, so `schemaArgClaim`'s vacuous existential wrapper exists purely to give `paperPrimeDecompose` a reachable head constructor; `provable_schemaArgClaim_iff` shows T never sees it. (6) `conGamma T T' hh` takes the `ComputableHorizon` BUNDLE — not extensional in the function; clients must thread the same `hh` term through endpoint and sentence.

**In-file `example`s under `section Endpoints` variables can look like inhabitation witnesses without being ones.** Examples stated at the section VARIABLE `T` discharge only explicit arguments; only examples naming a concrete theory (𝗜𝚺₁/𝗣𝗔) discharge the instances. Check which kind before counting an example as a witness (the thm:dontwait applied example is the variable kind).

**tex thm:pazfc displays `⌜f⌝(⌜n⌝)` but never binds `f`** — it is inherited informally from thm:pac; the Lean statement correctly binds both `T'` and `horizons`. Do not read the missing binder as drift (paper-side blemish, not worth an errata row).
