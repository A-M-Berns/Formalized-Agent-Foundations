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
| `def:ec`, e.c. sentences / rationals / emission | `BigSentenceCodes`, `DigitRatCodes`, `BigTokenStream`/`BigSpliceStream` (`Framework/WriteOut.lean`) | The write-out ladder. Value-bounded predecessors: `PolyNatCodes`/`PolyMachineCodes` (whole value; kept only as strictness foils, no `Paper node`) and `RpnSentenceCodes`/`RpnThresholdCodeSeq` (per-token value). `RpnSentenceCodes` is *not* purely symbol-metered: `PolySegStream` bounds every emitted token's value, so a single atom with exponential index is excluded by `Rpn` and admitted by `Big`. **There is no write-out class for LUV thresholds**, and none is needed: `LUV.RpnThresholdCodeSeq` (`Framework/Expectations.lean`) is the only one, and `StructuredPaperRpn.lean` splices Gödel codes out of small tokens (`PaperLUVSeq.source_valued_and_rpnThresholdCodeSeq`). **Corrected 2026-08-29 (R4-F01, reversing R3-F19):** `PaperLUVSeq.structural : PolyArithmeticFormulaSeq` meters one token per ℒₒᵣ node — the paper's own symbol count. Foundation's `Operator.numeral` is unary — a Foundation artifact; the paper never fixes a numeral notation (it writes numerals positionally, tex:614, tex:757). That artifact does not narrow the class, because the *value* is nameable compactly inside ℒₒᵣ: large values are named by compact terms (Horner `binNumeral`, O(log v) nodes) or by definitions (tex:614: writing ⌜f(3)⌝ 'merely requires writing out the definition of γ_f' — e.g. Foundation's Δ₀ `exponentialDef`), and those renderings are admissible. Witnesses: `unitFracPaperLUVSeq` (`1/(n+1)`), `dyadicPaperLUVSeq` (`2⁻ⁿ`). On numerals the class is fine. **The class is NOT coextensive with def:ec on connectives (R4-F04, blind audit, verified):** the paper's language has `⟺` primitive (tex:560); Foundation's NNF `Semiformula` has none and `a 🡘 b = (a 🡒 b) ⋏ (b 🡒 a)` duplicates both sides (`3 + 2|a| + 2|b|` tokens), so a left-nested `⟺` chain is O(n) in the paper and ≥ 2ⁿ tokens here — `iffChain_not_polyArithmeticFormulaSeq`. `→` and `¬` are linear. Ruling 2026-08-29: disclosed as an object-language substrate substitution `dd:nnf`, charged once globally (like `dd:fuel`), not per row; the faithful repair is a compact formula SOURCE language with `iff`/`imp`/`neg` primitives decoded to NNF for semantics (the `Code.sourceNat` pattern applied to formulas — the correct target of that idea; a binary-numeral source node was rejected as a permissive widening). DONE in tranche 5: `ArithSource` (`Construction/Witnesses/ArithmeticSource.lean`) is that source language, `dd:nnf` is retired, and T9p reuses the same source metering for `thm:incons`. |
| `def:ece` / `def:fuz` | `GeneratedRatFeature` (`Framework/Expectations.lean`) / `PGenerableWeighting` (`Properties/Calibration.lean`) | Both emission fields are `BigSpliceStream`; that shared meter is what makes `pGenerableWeighting_iff` (def:fuz = def:ece minus the denotation clause) statable — keep them at the same meter. General `PGenerableRat` constructor: `PGenerableRat.ofDigitRatCodes`; `ofPolyRatCodes` (`ProductDefinition.lean`) is the derived value-bounded corollary. `ratCodeFeature`/`ratCodeFeature_generated` live in `Expectations.lean` at `DigitRatCodes` strength. A constant leaf `EF.const q` serializes to `[1, encode q]` — one token whose value *is* the code — which is why the old `RpnSpliceStream` field silently excluded the paper's `2⁻ⁿ`. |
| §4.9 nodes (`thm:halts`/`loops`/`dontwait`), endpoint stack | `lic_learns_halting_patterns` (`Properties/MetaLearning.lean`) → `*_ofComputation` (`ComputationSyntax.lean`) → `*_unconditional` (`ComputationDP.lean`) | Three layers, all present: generic (no theory hypotheses, arbitrary `P`/`DP`), syntax layer (`[IsLogicalInductor P DP]` + `ComputationTheoryPresentation`), canonical instantiation over `liaHistory (theoremDP T)`. An auditor who sees only the canonical row wrongly concludes no arbitrary-inductor endpoint exists. `⌜f⌝(⌜n⌝)` → `boundedHaltingClaimInput m x hh.program n`, with `⌜f⌝` a constant and `n` unevaluated. `CodeHaltsWithin` meters by `evaln` fuel, not Turing steps — harmless at `thm:dontwait`, live if a positive bounded-runtime result is ever stated. |
| Foundation `re_complete` | `Foundation/FirstOrder/Arithmetic/R0/Representation.lean:260` | An **iff** stated under `[T.SoundOnHierarchy 𝚺 1]`; only `.mpr` (provable ⇒ true-in-ℕ) uses soundness. `.mp` is `sigma_one_completeness` (`R0/Basic.lean:143`, `[𝗥₀ ⪯ T]` only) — a soundness-free `re_complete_mp` compiles in six lines. `Entailment.Consistent T` is derived from the soundness instance (`Basic/Hierarchy.lean:481`), so every `inferInstance` for consistency silently routes through it. The transport `models_haltingSchema_iff` (`ComputationDP.lean`) lifts `codeOfREPred_spec` to standard-model truth of a schema instance. |
| `def:lic` | `IsMachineLogicalInductor` (`Framework/MachineEfficiency.lean`) | The criterion the construction proves. `IsLogicalInductor` is the same criterion over the fuel class, kept as the compatibility predicate the §4 tail is stated against. |

- `def:ec` is paper **§3.3**, not §2.2 — §2 is Notation, §3 is the Criterion.
- `evaln_output_can_exceed_fuel` (`Framework/Computable.lean:51`), `codeEvalBound`,
  `codeEvalBound_poly` and `codeEvaln_result_le` (`Framework/Emission.lean:21–78`) are
  **repo** lemmas, not Mathlib. Grepping Mathlib for them finds nothing.


**§4.10 Con substrate (T8/i; metering superseded in 9a — `BProv` now bounds `dSize`, the symbol count, and `dd:proofcode` is retired).** `Framework/BoundedConsistency.lean`: `BProv T φcode k` (bounded provability), `conWithin T k` (= paper `Con(T)(k)`), `bprovValue T : ℕ → ℕ` (the decider), `conRunValue T f` (the universal decider `thm:pac` represents), `conWithin_of_consistent`, `conWithin_anti`. `ComputationRepresented.lean`: `conClaimArg`, `conClaimSentence`, `conGamma`/`conGamma_spec`, `representedConClaims`, `conClaimSentence_ne_of_day_ne`. `lic_belief_finitistic_consistency_unconditional` now reads `(T) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [RepresentsComputations T] (horizons) (hh : ComputableHorizon horizons)` and concludes `liaHistory (paperTheoryDP T) n (conClaimSentence (conGamma T T hh) n) ≈ₙ 1` — no `consistentWithin`, no `BoundedComputation`, no `hconsistent`. *(Spelling updated T8/ii: `conGamma` takes two theory arguments; pac is the diagonal.)*

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

**T9p: `thm:incons` metered on the written source (VERIFIED 2026-08-31: full gates green after six proof-local repairs, commit 66bec50).** Endpoint: `(T) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Consistent T] (T') [T'.Δ₁] (σ : ℕ → ArithmeticSentence) (s : ℕ → ArithSource 0) (hs : PolyArithmeticSourceSeq s) (hcompile : ∀ n, ArithSource.compile (s n) = ↑(σ n)) (hinc : ∀ n, ¬Consistent (σ n ∷ T'))`. NEW in `Framework/CodeSource.lean`: `tokenListNat`, `tokenListNat_digit{,_lt,_length}`, `length_lt_tokenListNat`, `tokenListNat_injective`, `dig4_ofDigits_sixtyFour`, `BigDigits.ofBase64Digits`, `BigDigits.ofTokenListNat`; `ofDigits_div_pow_mod` generalized base-16 → `{b} (1 < b)`. NEW in `ArithmeticSource.lean`: `ArithSource.sourceNat`, `sourceTokens_lt_63`, `sourceNat_ne_of_sourceTokens_ne`, `PolyArithmeticSourceSeq.bigDigits_sourceNat`. NEW module `SourceNumbering.lean`: `tokensOfNat{,_tokenListNat,_primrec}`, `negSourceFormulaCode{,_computable,_sourceNat}`. NEW in `ComputationRepresented.lean`: `provableCode_negSource_re`, `negSourceFormulaCode_sourceNat_of_sentence`, `falsumSource`, `deepInconsistentSource`, `deepInconsistentAxiom`, `thm_incons_applied_deep`, `inconsistencyArgClaimSentence_deep_ne`. EXPORTED from `LIACompiler.lean` (were private): `negFormulaCode_prim`, `parseStructuredArithmeticFormula_prim`. GONE: `alternatingInconsistentAxiom{,_digits,_inconsistent}`, `thm_incons_applied_alternating`, `deductionFamilyArg_ne_of_ne`; `deductionFamilyArg` now takes `ℕ → ArithSource 0`, computable.

**Tranche 9a landed the §4.10 symbol measure (VERIFIED, commit 9dc1743).** NEW `Framework/DerivationSize.lean`: `idxLen`, `pl`/`pr`/`arg`/`tail`, `tvAux` (mode-packed term/vector recursion) with `tSize`/`tvSize`, `fSize`, `sSize`, `dSize`; `G`, `G_mono`, `self_le_G`, `le_G_tSize/tvSize/fSize`, `lt_two_pow_G_sSize`, `le_G_dSize`; faithfulness equations `dSize_axL/verumIntro/andIntro/orIntro/allIntro/exsIntro/wkRule/shiftRule/cutRule/axm`, `fSize_qq*`, `tSize_qq*`, `tvSize_adjoin`, `exp_nat_eq`, `mem_iff_testBit`, `fSize_le_sSize(_of_mem)`. NEW `Framework/DerivationSizeComputable.lean`: the `_primrec`/`_computable` pairs + `computable_boundedSearchValue`. `BoundedConsistency.lean`: `bProvPacked_*` trio GONE → `ProofPacked`/`proofPacked_sigmaOne`/`not_proofPacked_sigmaOne`/`proofPacked_computable` (+ `proofPacked_iff`, `proofPacked_pair_iff`, `bProv_iff_bounded` — where `le_G_dSize` is spent). `BProv T φ k := ∃ d, Proof T d φ ∧ dSize d ≤ k` (INCLUSIVE). `conWithin*`, `bprovValue*`, `conRunValue*`, `ProvableCode*` keep names/shapes; only `conGamma_mentions_zero_of_horizon_unbounded`'s proof changed (unboundedness applied to `dSize d`).

**Verified (do not re-search): Foundation has NO size/length/height/symbol count on derivation codes** anywhere in `FirstOrder/Bootstrapping`. `formulaComplexity` (connective complexity, atoms ↦ 0) and `bv` are V-valued formula recursions, unusable as external computable `ℕ → ℕ`. `DerivationSize.lean` duplicates nothing upstream.

**Foundation's sequences are cons lists at the numeral level** — `x ∷ v = ⟪x, v⟫ + 1`, nil `= 0` (`HFS/Vec.lean:18-24`) — so external recursion over a coded vector needs only `Nat.unpair`, no `len`/`nth` computability. Sequent membership `p ∈ s` is `s.testBit p` at ℕ (`Exponential/Bit.lean:21-23`, `Pow2.lean:112`); a `Finset.range`-bounded sum guarded by `testBit` is both honest and primrec-friendly.

**`dd:proofcode` has zero live claims left in the docs surface (9a docs pass).** Remaining greps hit only deliberate past-tense supersession clauses (classification 2, README 1, generated page 2). `thm:pac`/`thm:pazfc` rows open "Status: `exact`." with the metering described as the paper's own symbol count under `dd:symbolcount`; residual lists renumbered ([T.Δ₁] = (i), pending-𝗣𝗔⁻ = (ii)).

**R9 lens-A verification record (dSize faithfulness).** All ten derivation tags match Foundation (`axL=0 … axm=9`, Proof/Basic.lean:134-152); formula tags qqRel=0…qqExs=7; term tags qqBvar=0, qqFvar=1, qqFunc=2. No constructor drops written material (wk/shift count `sSize s + dSize d`; cut counts the cut formula and both premises; verumIntro's trailing `0` is a placeholder costing nothing). NOTHING in the build enforces this correspondence beyond the `@[simp]` equations — any future `dSize` edit must be re-checked against those two Foundation files by hand.

**`Bootstrapping.Proof T d φ` is `DerivationOf T d {φ}`** — conclusion sequent exactly the singleton `{φ}`. `conWithin T k` = "no derivation concluding exactly `{⌜⊥⌝}` in ≤ k symbols" — differs from the paper's "proof of ⊥" by at most one `wkRule` node; truth unaffected, but convention-sensitive at the ±1-node margin.

**R9 lens-B verification record.** Constructor coverage complete (ten derivation tags, eight formula tags, three term tags — audited against Foundation, nothing dropped); `bProv_iff_bounded` sound (`d ≤ G (dSize d) ≤ G k` by `G_mono`); both polarities genuinely decided; junk branch unobservable twice over (Fixpoint forces well-formedness; truth never mentions `dSize`); `BProv` non-vacuous (`conGamma_mentions_zero_of_horizon_unbounded` manufactures `BProv T' ⌜⊤⌝`); the 𝗜𝚺₁/𝗣𝗔 witnesses are genuinely instance-free at named theories (they mention no section variable `T` — the thm:dontwait witness DOES mention `T` and is parametric); keyword discipline clean; delegated module clean (no decide-bypass, no unsafe/partial/implemented_by).

**R9 fix wave landed.** `dSize_pos {d} (h : 0 < d) : 0 < dSize d` (general; `dSize 0 = 0` the only zero; `dSize_pos_of_axL` retired). Full-surface `#print axioms` footers: DerivationSize 61 names, DerivationSizeComputable 13, all clean; both modules carry NOT-YET-INVENTORIED dispositions in AxiomAudit (no `Paper node:` lines by design — anyone adding a public declaration must extend the footer). The +1 marker token disclosed at all Lean sites AND the six docs sites (classification bullet + pac/pazfc rows, LI_READING ×2, README).

**Foundation HAS compactness for `FirstOrder.Theory`, in the strongest form — the proof object carries its axioms (T10 probe, verified compiling).** `structure Theory.Proof` (`FirstOrder/Basic/Calculus.lean:300-308`) has fields `axioms : List (Sentence L)`, `axioms_mem`, `derivation`; `T ⊢ φ = Nonempty (T ⊢! φ)`, so the finite axiom set is `rcases h with ⟨d⟩` — no induction. Packaged: `Entailment.Compact` instance (`:314`), `Compact.finite_provable` (`Logic/Entailment.lean:431`), `inconsistent_compact`/`consistent_compact` (`:449,453`), `Theory.provable_iff`/`inconsistent_iff` in List form (`Calculus.lean:336,339`). No Finset-indexed form exists; don't hand-roll finitization.

**`Theory.Δ₁` has an EMPTY-theory instance** (`Δ₁.empty`, `ch := ⊥`, `Bootstrapping/Syntax/Theory.lean:79`) — `ProvableCode ∅`, `provableCode_re ∅`, `proofPacked_computable ∅` all elaborate: the provability engine runs at PURE LOGIC, no base theory. Also installed: `Δ₁.add/singleton/ofList/ofFinite` (`:66-104`) and instances for `∪`/`{φ}`/`insert`; `σ ∷ T` is `rfl`-equal to `insert σ T`. `Consistent (∅ : ArithmeticTheory)` via `consistent_of_sound ∅ (Eq ⊥) rfl`.

**What the paper actually asks of `thm:incons` (quoted anchors, for re-audits).** `def:ec` (tex:754-756) is ONE polymorphic definition; tex:1931 is the interpretive key ("write out the source code specifying mₙ in time polynomial in n; the runtime of an individual mₙ is immaterial"), tex:1905 confirms for incons ("efficiently named"). Must not narrow: (i) Θ′ₙ FREESTANDING (may be stronger than the market's Θ — tex:1882, 1889); (ii) axiom sets may be INFINITE (examples 𝗣𝗔, 𝗭𝗙𝗖); (iii) the believed sentence is the UNBOUNDED existential. "Recursively axiomatizable" is never defined in the paper; the r.e.-axiom-set reading narrows nothing.

**Consolidation sweep (round 10) landed.** Tier rename: the middle metering tier is **token-metered** (covers `EfficientlyComputable`, `RpnSentenceCodes`, `RpnThresholdCodeSeq`, `RpnSpliceStream`, `PolySegStream`); the old "symbol-metered" name survives in exactly two deliberate places (def:ec class docstring; classification taxonomy), and the two remaining "symbol-metered" uses (`BoundedConsistency.lean:50`, README:685) genuinely mean the paper's symbol count. `PolyEF` + its four certificate lemmas DELETED (dead island; `predc`/`predAux`/`predc_polyFueled` kept — real consumers). `thm:lp` now elaborates `[T.Δ₁] [Consistent T] [𝗜𝚺₁ ⪯ T]` — 𝗣𝗔⁻ binder gone via a section restructure; 𝗣𝗔⁻ census is **16 of 105** (derived: exactly one endpoint changed). All four `*ClaimSentence_digits` generators + `computationClaimSentence_digits` + `boundedHaltingClaimInput_digits` have zero consumers, retained pending the tag-space ruling (section note in-file states the graph); `haltingClaimInput_digits` is live. `AffineCombination.PolySequence` is a WRITE-OUT class (BigSentenceCodes/BigSpliceStream), mislabeled before. `notes/semantic-source-repair.md` deleted (one load-bearing paragraph folded into README item 2). Phase tags cleaned from non-audit prose.

**`MachineSentenceCodes` and `MachineTokenStream` are UNWIRED** — zero consumers; only inclusion lemmas point in. The def:ec row's "consumed only at thm:scon" is FALSE (also at trust-surface): thm:scon's machine transports consume `RpnSentenceCodes` and route through the separately-defined `CondStep.MachineSentenceBlocks` (`CondStep.lean:2487`) via `machineSentenceBlocks_of_rpn`. Row corrections queued (doc-only): fix that claim; the stale class list (`RpnSentenceCodes` binds ONE endpoint, `lic_self_trust_closed`; the charge is carried by BigSentenceCodes/BigSpliceStream); "converse inclusion is open" → open at the length-metered target, FALSE at the value-metered one, comp-case obstruction named. ALSO: the direct threshold-binder list in this file saying "thm:ec, thm:ei" is wrong — census finds five (adds thm:er, thm:cee, thm:ccee).

**The §4 property tail has exactly ONE funnel into trader efficiency: `BigSpliceStream.ec` (`WriteOut.lean:532`).** Every data class converts into BigSpliceStream/BigSentenceCodes, packs into `AffineCombination.PolySequence` or `PolyTradeEmulatable`, and reaches `EfficientlyComputable` through four trader bridges (+`ofSingleTradeBlocksBig`). The certificate is consumed as EMISSION DATA (the splice opens it), not an opaque predicate — you cannot swap the hypothesis class without rebuilding the splice.

**A word-level FP serialization kit already exists in the wrong place:** `CondStep.lean:1583-1760` (`wConst/wAdd/wMul/wMax/wSafeRecip/wPriceSym/…`, FP lemmas :2284-2332, BlockWF algebra :1592-1600), mirroring `serialize_*` one-for-one. Anyone contemplating machine-side emission lifts these first (cuts the estimate to 4K-10K lines from 10K-20K).

**complexitylib proves Cobham's theorem** (`CobhamFP_eq_FP`, `Classes/P/Cobham.lean:92`): machine-independent induction over FP (projections, bit successors, smash, LIMITED recursion on notation) — the right tool for "every FP function has property P" without TM programming. Its PUBLIC FP surface is ~7 lemmas; the real string kit is proof-internal in `Cobham/Internal.lean` (this repo imports it anyway, disclosed at `FPFold.lean:30-35`); no value arithmetic exists as `_ in FP`.

**T10 landed (VERIFIED): `thm:incons` at arbitrary machine-enumerated r.a. theories.** `theoryOf (m : Nat.Partrec.Code) : ArithmeticTheory := {σ | ∃ (b i : ℕ) (s : ArithSource 0), evaln b m i = some s.sourceNat ∧ compile s = ↑σ}`; represented predicate `MachineTheoryInconsistent z := ∃ w, ProvableCode (∅) (negWindowCode z w)` — empty theory, no base anywhere. Endpoint `(T) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Consistent T] (m : ℕ → Nat.Partrec.Code) (hm : DigitMachineCodes m) (hinc : ∀ n, ¬Consistent (theoryOf (m n)))`, both paper conjuncts. `inconsistencySchema_mentions_zero` + `_ne_of_arg_ne` HYPOTHESIS-FREE. NEW modules `SourceWindow.lean` (verumSourceNat, combineTokens/SourceNats, conjSource, compile_conjSource, axiomWindow, negWindowCode + certificates) and `DayMachine.lean` (`dayMachine F n = curry F n`, `digitMachineCodes_dayMachine` — the first COMPUTING day-varying DigitMachineCodes witness); new in BoundedConsistency: `listConj`, `consistent_empty`, `exists_inconsistent_list`, `provable_neg_listConj_of_not_consistent`, `provable_listConj`; `tokenListNat_primrec` + `BigDigits.ofBase16PolySegStream` in CodeSource; `iffChain_injective`. Witnesses: `thm_incons_applied_deep` (5n+7 written / ≥2^n compiled, every-pair separation) and `thm_incons_applied_infinite` (INFINITE day axiom sets — inexpressible under the deduction family). GONE: `deductionFamilyArg`, `provableCode_negSource_re`, `falsumSource_polyArithmeticSourceSeq`, `deepInconsistentSource_sourceNat_ne`, `deepInconsistentAxiom_inconsistent`, `provableCode_neg_iff_not_consistent_adjoin`, `not_provableCode_quote_falsum`. Open judgment call: `not_consistent_adjoin_iff` kept consumer-less (general deduction bridge; rows §6 asks for a ruling).

**R11 docs pass landed: theorem counts 43/7/0, instantiated 18/0; def:ec sole qualified row, obstruction-backed.** `MachineSentenceCodes` has ZERO consumers (only its def + two producers); thm:scon consumes `RpnSentenceCodes` through the separately-defined `CondStep.MachineSentenceBlocks` — the two names look interchangeable and the false claim survived two editions. def:ec census (transitive through bound structures): BigSentenceCodes 51, BigSpliceStream 52, 64/105 total; `RpnSentenceCodes` binds exactly ONE endpoint (`lic_self_trust_closed`); the PAGE prints shallow signatures (19/2/1) — never use it as the census.

**The 9b obstruction is NOT withdrawn by T10 and must not be deleted from the ledger.** `thm:incons` stopped DEPENDING on it (external machines + compactness never form a uniform internal predicate); a verified obstruction being real ≠ being binding on a given statement — that distinction is the whole content of the T10 move, and is easy to collapse on a re-read.

**def:ec's converse question is TWO questions (R11 docs):** OPEN at the length-metered target (missing TM→code compiler with fuel accounting; evaln decrements per constructor vs symbol-counted machine cost — comp case irreconcilable), FALSE at the value-metered one (`not_polyFueled_two_pow`; binary `2^n` ∈ FP). Same missing compiler both directions; closure = redefining `dd:fuel`.

**Orchestrator ruling (R11): `not_consistent_adjoin_iff` is KEPT** despite zero consumers — it is a natural consumer-surface lemma (the deduction-theorem bridge `¬Consistent (σ ∷ T) ↔ T ⊢ ∼σ`), general, documented, and exactly the kind of client tool the consumer-readiness standard endorses; deleting it would force downstream re-derivation. It stays in the BoundedConsistency footer.

**R11 fix wave landed (VERIFIED): the thm:incons window is sound AND complete — `machineTheoryInconsistent_iff m : MachineTheoryInconsistent m.sourceNat ↔ ¬Consistent (theoryOf m)`.** THREE leak mechanisms closed (the audit's two + a third found while proving the converse: a genuine `ArithSource 0` can compile to a FREE-VARIABLE formula — `∅` refutes `&0 ≠ &0`, no sentence, no theory — so a parse-consumed-everything gate is insufficient; the repair rejects tag 4 and reconstructs a SEMISENTENCE). NEW module `Construction/Witnesses/SourceRecognizer.lean` (~1435 lines): `sourceRun`/`sourceTermRun` (depth-tracking, free-variable-rejecting), `exists_source_of_sourceRun` (soundness = reconstruction), `sourceRun_sourceTokens` (completeness), canonical-only `structuredNatRun`, level-function factoring, full Primrec certificates. Gate in `SourceWindow.lean`: `AdmissibleName v := tokenListNat (tokensOfNat v) = v ∧ sourceRun … = some []`; `gateName`; `axiomWindow` gates every entry; `exists_sources_axiomWindow` (every window IS `ss.map sourceNat` of sentence-valued sources). `theoryOf`, `MachineTheoryInconsistent`, `inconsistencySchema`, and the ENDPOINT SIGNATURE are all unchanged — only the day sentence's content tightened to exactly the convention's claim. Also landed: `theoryOf_const_ofNNF` (every one-axiom theory realized exactly; uniform surjectivity honestly scoped as not-formalized), `not_provableCode_zero` (proved, not hedged), `ArithSource.compile_eq_of_sourceTokens_eq` (`sourceTokens` NOT injective — leaf (φ⋏ψ) vs and(leaf φ)(leaf ψ) — but equal runs compile equally), assert block `machineTheoryInconsistent_iff theoryOf_const_ofNNF thm_incons_applied_deep thm_incons_applied_infinite`. TWO NEW `Paper node: thm:incons` carriers (`machineTheoryInconsistent_iff`, `theoryOf_const_ofNNF`) — deliberate, flagged for the human read-through.

**R12: LI's reverse node gate is per-DECLARATION (check A2, `check_endpoint_coverage.py`), closing the R11 lens-B loophole.** Rule: annotated ⇒ named in an `#assert_axioms_clean` block; `#assert_fields` deliberately does NOT satisfy it (freezes field names, calls no collectAxioms — 62 boundary structures were annotated, frozen, and axiom-UNCHECKED until R12 asserted them). 166 gaps closed by assertion, zero exemptions (the exemption dict is empty and self-checked stale in both directions). New AxiomAudit section `/-! ## Per-declaration axiom coverage -/` (39 blocks, 166 names) — internal regression assertions, NOT public trust surface; LI-CANONICAL unchanged (105/66). All 166 resolved and axiom-clean on first assertion. Mutation-tested fail-closed (4 tests). `check-paper-nodes.sh` now exits loudly (final FAIL line + EXIT trap).

**Foundation upstream bundle PREPARED (2026-08-31, local only — never pushed):** branch `li-upstream-bundle` in the harness scratchpad clone of pin `41d20b51`; commits `6dbc43c4` (new `FirstOrder/Basic/Syntax/Occurrence.lean` = LI's SubstOccurrence, `bShift_injective` promoted public), `ffea0e3e` (`code_uniq` revival in `R0/Representation.lean` over 𝗣𝗔⁻ + PeanoMinus import, layering alternative offered), `916b6faa` (`re_complete_mp` before the soundness variable line, explicit binders). PR-DESCRIPTION.md + VERIFICATION.md beside the clone. Verified per-file via a shadow-olean tree; whole-library check impossible locally (host built only LI's slice — not a cache symptom). If any item lands upstream, DELETE the LI copy (same `LO.FirstOrder` namespace — collision, not shadowing). Opener must run real `lake build Foundation` + `mk_all`.

**T8/8 landed (VERIFIED, 93b93df).** `theoremDP`'s event tag space gapless `0-5`: 0/1 halting ±, 2/3 bounded halting ±, 4/5 quotation ± (were 6/7). GONE: `ComputationClaimKind.inconsistency`/`.consistency` (enum now two constructors), `inconsistencyClaim(Sentence)(_digits)`, `consistencyClaim(Sentence)(_digits)`, `boundedHaltingClaimInput_digits`, `provabilityWorld_inconsistency`/`_consistency`, the two `ComputationTheoryPresentation` fields (freeze now six names). NO endpoint signature changed; `ComputationTheoryPresentation` strictly weaker → consumers strengthened. `thm:incons` dropped from its Paper-node line (renders no part of the node now). Dated audit prose pre-2026-08-31 saying "tag 7"/"tag-3 case" means the OLD numbering — the mapping is recorded at the freeze site.

**THREE distinct tag spaces — do not conflate:** (1) `ComputationClaimKind.godelCode` (now 0/1); (2) `theoremDP`'s EVENT tags (0-5, the T8/8 renumbering); (3) the GLOBAL atom-payload first component: computation 0-1, quotation 4, product 5, semanticPrime 6, paperPrime 7, oldLanguage 8, + `FinitePerturbationCounterexample.schedAtom`'s fresh 6/7 (numerically colliding, tolerated — no process emits them). Space (3) now has 2/3 unassigned; closing it forces quotation 4→2 … oldLanguage 8→6 which COLLIDES with schedAtom 6, so the counterexample's advice tags must be re-picked. ORCHESTRATOR RULING: fold the gapless payload renumbering into the market-unification tranche (that layer is redesigned there anyway).

**R13 landed (VERIFIED, 40823bba): THE SINGLE MARKET IS `paperDP`** = `(theoremDP T).union (paperTheoryDP T)` (`PaperTheoryDP.lean`; collapsed from the zero-consumer `theoremPaperDP`, no layered survivor). All 18 market-bearing canonical endpoints read `liaHistory (paperDP T)`; census: 18 paperDP + 1 canonicalCCEEDP (ruled) + 86 abstract; binder counts IDENTICAL before/after (𝗣𝗔⁻ 16, 𝗜𝚺₁ 3, Δ₁ 23, Consistent 15 — NOTE: 15, not the 14 an earlier round-6 entry recorded; discrepancy predates R13 — RepresentsComputations 3, Sound 0, 𝗥₀ 0). Substrate: `paperDP_computable/_hworld/_nonvacuous`, `paperDPComputation`, `paperQuotationPresentation` (= `quotationPresentation.mono` — `QuotationTheoryPresentation.mono` lives in ProductDefinition.lean, easy to miss), `paperLIA`, `paperMarketComputation`, `paperDP_covers_of_paperTheoryDP`; renames `theorem*QuoteCode`→`paper*QuoteCode`, `paperTheoryDP_covers_*`→`paperDP_covers_*`; self-reference lane in NEW `Construction/Witnesses/PaperMarket.lean` (forced by the import DAG — paperTheoryDP is DOWNSTREAM of QuoteCodeOfMarket). `theoremDP`/`paperTheoryDP` survive only as construction ingredients + the CCEE lane's ruled base — not a parallel endpoint lane. `paperBaseDP` (∪ cut-law) still unconsumed DELIBERATELY: folding it drags the semantic lane into every endpoint file (~1h rebuilds); clean follow-up, no new math needed. Payload space gapless 0-6, advice tags 7/8, authoritative table at `ComputationClaimKind.godelCode`.

**AUDIT FLAG for the final blind audit (from R13):** `lic_no_expected_net_update_conditional_exact_canonical` is the only canonical endpoint still naming `theoremDP` — in a HYPOTHESIS (`source_valued` quantified over `ConsistentWithTheory (theoremDP T)` worlds) while concluding at `canonicalCCEEDP`. Predates R13, left under the CCEE ruling; a premise over a SMALLER process's worlds is weaker — the final audit should examine it on its own terms. The final audit must also specifically check the 18 unified-market statements against the paper's single-𝕡 reading.

**FINAL-audit verification records (lenses A/B/D, 2026-08-31) — cleared suspicions, do not re-raise.** Criterion core: `EF.rank` is a sound over-approximation (safe, denotationally lossless); the rank-soundness lemmas live in `Construction/MarketMaker.lean:1309-1328`, NOT Criterion.lean. `thm:li` delivers a genuine `def:belseq`. thm:lp's diagonal is real Kleene recursion (`parameterizedDiagonalQuoteCodeOfMarket_public_fixedpoint`). `hworld` on every §4 endpoint is NECESSARY (stage-unsatisfiable processes make the criterion vacuous — `isLogicalInductor_of_stage_unsatisfiable`). `HasROI`'s Summable clause is load-bearing (Mathlib tsum of divergent series = 0) and disclosed; not canonical. thm:obu: read the `_ofCE` endpoint (paper's own premise; `EfficientRepeatedEnumeration.ofCE` dovetails). thm:benford at thm:prand strength (patience-restricted quantifier = weaker hypothesis). `limitingBelief`/`expectInf` are TOTAL limsup stand-ins proved equal to genuine limits under the inductor hypotheses. `AffineQuoteEq.future_coherent` is derived on the closed lane, not assumed. Pseudorandom's `DeferralPatient` narrows a ∀-hypothesis = strengthens. paperDP publishes only on T-provability (nothing smuggled as bare literals); its two components use DISJOINT atom families, so 'm halts on x' has two unrelated propositional representations in the one market. CCEE's `source_valued` over theoremDP-worlds is a STRONGER premise (superset of worlds), and the form the proof needs. The suffix ladder in practice: `_ofX` conditional / `_unconditional` discharged over paperDP / `_closed` also constructs the quote-portfolio; canonical names are the innermost discharged form, often in `Construction/Witnesses/` not `Properties/`. `lint_paper_labels` enforces theorem⇒label only, not label⇒claim: construction machinery `theorem`s carrying `def:ec` are a disclosed convention. `machine_lic_iff_of_recognizableSupport` covers finite COORDINATE support, not the paper's finitely-many-DAYS — deliberately, since the whole-day case is exactly what `not_overgeneral_ifp` refutes. `kappaU` is safe only because `uLenSet` is provably nonempty — preserve `uLenSet_sInf_mem` under any refactor.

**FINAL-audit lens C verification records.** The write-out migration is complete on the day-indexed surface EXCEPT the two disclosed token-metered retentions (thm:st's hφ; conditioning's condition_codes — AxiomAudit:1929-1946). Cleared traps: `PrefixMachinePresentation`'s whole-value + surjective pair is satisfiable because `prefixSentenceEnum` is indexed BY the code (`encode (sentence n) ≤ n` — the trap needs index ≪ code); `LUV.RpnThresholdCodeSeq` on paper LUVs avoids emitting exponential codes because `structuredPaperSourceDecomposeAll_rpnSentenceCodes` emits the SOURCE block and `parseRpn` contracts to the tag atom; `codeEvalnNat_polyFueled` is true despite bounding values — Mathlib's `evaln` guards `n < k` at every prec/rfind', so `codeEvalBound` is poly in fuel for fixed code. Client-probe compiles verified for pac/pazfc/ob/expcoh at named theories. Missing convenience: no `PaperLUVCombination.worldValued` — clients hand-assemble via `paperTheoryDP_subset_paperDP` + Classical.epsilon (four-line recipe verified). The `not_polySentenceCodes_bitPrefixSentence` emptiness proof is the MODEL for discharging the metering trap — ask for the emptiness proof, not an inhabitation proof, when a value-metered field appears on day-indexed syntax. Full verified-inhabitant table is in the lens-C report (verdicts-FINAL context).

**FINAL-audit additional confirmed defects (fix wave F7/F8):** thm:lp's four width binders are DEAD — a width-free derivation COMPILES (internal width (2^n)⁻¹ + digitRatCodes_two_pow_inv); collapse to the width-free statement. The thm:dus/thm:strict boundary's sole inhabitant lives over `emptyBitDeductiveProcess` (every stage ∅, realizable vacuous) signposted as "the non-vacuity witness" without the house degeneracy caveat; the row discloses Θ=∅ as degenerate but the witness/audit notes don't; stretch fix = IndependentBitAtoms over paperDP via payload-tag disjointness.

**FINAL fix wave landed (VERIFIED, 9072691+785e202).** F1 duplicate Prop instances deleted (Mathlib cited). F3/PE2 declared at all three statements (the mirror half was SILENT — a second unlisted defect, now declared). F4 mixed-truth witness `alternatingFeedbackTruthComputation_nonempty` LANDED (~75 lines; the old "no non-constant certificate available" docstring was a scope error — finitely-valued streams need only constant codes + ifzSel; family has EIGHT endpoints, not five). F5 `lic_self_trust_closed` widened to `BigSentenceCodes` (token form consumed NOWHERE on the lane; `LUV.BigThresholdCodeSeq` built + `.toBig`/`.reindex`; `indicatorProductLUV_bigThresholdCodeSeq` collapsed rename). F6 STALLED-DISCLOSED: conditioning is the ONLY token-metered retention left — `machineSentenceBlocks_of_rpn` opens the certificate as emission data and its digit clamp is the identity only under a VALUE-bounded stream; widening = BigSentenceCodes→MachineSentenceBlocks re-blocking in FP (~50 lemmas); false def:ec claims corrected at BOTH sites incl. the sibling at Properties/Conditioning.lean:1805. F7 thm:lp width binders collapsed (width-free takes the plain name; the QuotationAffine conditional twin KEEPS its widths — genuinely consumed). F8: empty-process witnesses re-signposted "inhabitation only" AND the stretch landed — `bitAtomTag := 7`, `paperIndependentBitAtoms` with substantive realizability over paperDP, plus `lic_domination_dovetailSemimeasure_paperDP`/`lic_domination_everyLowerSemicomputable_paperDP` closing thm:dus with NO caller input (the "no DUSApproximationPresentation witness" claim was a namespaced-grep false negative — `Dovetail.dusApproximationPresentation` exists and was already consumed). Atom-tag registry: product 3, semanticPrime 4, paperPrime 5, oldLanguage 6, bitAtom 7; NEXT FREE = 8; each carries a freshness lemma.

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
[RESOLVED BY CONSTRUCTION, R13 — the single market is `paperDP`; historical question:] the canonical surface USED TO run three markets (`theoremDP` 13, `paperTheoryDP` 6, `canonicalCCEEDP` 1 at the canonical block (2026-08-31 recount; 86 abstract))
while the paper fixes one 𝕡 — the union (renamed `paperDP` in R13) now IS the market; question closed.

**Known dead weight.** `PolyEF` (`Framework/Computable.lean:258`) is a dead-end layer:
consumed only by other `PolyEF` lemmas, never converted to any emission class. It is a
consolidation candidate, recorded here so it is not mistaken for load-bearing.


**The propositional rendering of `Con(Θ)(ν)` is a NEGATED atom, and this is forced, not chosen.** `representedClaimSentence γ t` is the paper-prime of `reprAllTerm γ 0 t`; `paperPrimeDecompose (reprAllTerm γ 0 t) = ∼representedClaimSentence γ t`, because a universal sentence is not prime and its ∃-negation is. So `conClaimSentence γ n := ∼representedClaimSentence γ (binNumeral (conClaimArg n))`, and the DP publishes it through `paperTheoryDP_covers_representedClaim_neg` (from `T ⊢` the value-0 sentence). Do not reach for the un-negated atom: that one is "the bounded search SUCCEEDS" and would give `≈ₙ 0`, not the paper's `≈ₙ 1`.

**Stage (ii) shape for thm:pazfc, from the stage-(i) substrate.** `BProv`/`conWithin`/`conRunValue` already take the theory as an ordinary parameter, so `conRunValue T' horizons` represented IN `T` is the whole construction — no new substrate. The one genuinely new obligation is the positive literal: `conWithin_of_consistent` gives truth of the `T'` claims from `Consistent T'`, and `RepresentsComputations T` converts truth into `T ⊢` since the decider is total computable. Stage (ii) needs NO soundness premise — only `Entailment.Consistent T'` as an explicit hypothesis on the second theory, exactly the paper's own premise for Θ′.

**[CORRECTED R7: the paper NEVER assumes `Θ ⊆ Θ′` — tex:1881-1886 says 'any recursively axiomatizable consistent theory'; the Lean statement MATCHES the paper's hypotheses, and no 'more general than the paper' claim is earned. The remainder of this entry records the (sound) dependency analysis only.]** Verified unused: `conRunValue_computable` needs only `[T'.Δ₁]`, `RepresentsComputations T` is about T, `conWithin_of_consistent T' hcons` about T′ — no step relates the theories. Dropping it strengthens the theorem in the harmless direction and keeps typeclass assumptions minimal; disclosed in the endpoint docstring ("More general than the paper"). Do not "restore" it as a fix — the inclusion is what makes the paper's result *interesting* (why Θ cannot prove Con(Θ′)), not what makes it true; the 𝗜𝚺₁/𝗣𝗔 example carries that interest concretely.

**[EXECUTED T8/iii — all seven deleted; `thm:pac`/`thm:pazfc` each have one carrier again.]** Dead after T8/ii, verified by grep (stage-(iii) retirement list): Zero consumers apart from `#print axioms`/`AxiomAudit`: `alwaysBoundedComputation`, `ordinaryBoundedComputation` (`ComputationSyntax.lean:670,648`), `BoundedComputation` (`:596`), `representedDecidableClaimsOfComputation` (`ComputationRepresented.lean:541`), `lic_belief_finitistic_consistency_ofComputation` (`:752`), `lic_belief_stronger_theory_consistency_ofComputation` (`:773`), abstract `lic_belief_stronger_theory_consistency` (`Properties/MetaLearning.lean:80`). CONTRAST: `lic_belief_finitistic_consistency` (`MetaLearning.lean:66`) is LIVE — both `_unconditional` endpoints route through it. No separate `consistentWithin` definition exists; `conWithin` is the live §4.10 predicate. Retirement also shrinks `AxiomAudit.lean:848,1012-1014` and `#assert_fields BoundedComputation` at `:1284`.

**The LI-CANONICAL block is a curated view, not the superset of the topical `#assert_axioms_clean` blocks.** Retiring seven declarations named only in topical blocks changed the LI-CANONICAL count by zero: LI-CANONICAL names exactly what `scripts/coverage-classification.md`'s endpoints table names (enforced two-way), while topical blocks are internal axiom regressions. Before budgeting a census-prose edit for a retirement, check which block the name is in; measure with `sed -n` between the real marker lines — an `awk /BEGIN/` sweep also matches the prose mentions of the markers and silently inflates the count.

**`thm:incons` does NOT charge `dd:proofcode`.** Its sentence is the *unbounded* existential over proofs (the paper's `⌜Θ′⌝ is inconsistent` is the negation of the universal generalization of `Con(Θ′)(ν)`, tex:1863-1866): nothing is metered, so the symbol-count-vs-Gödel-number substitution does not arise. If any ledger text charges it there, drop it.

**The `thm:incons` theory sequence is the deduction family `Θ′ₙ := Θ₀ ∪ {σₙ}`, disclosed — [charge status updated: scope-9b found a VERIFIED OBSTRUCTION, so the paraphrase STANDS disclosed; the closing '9b will retire it' reading is WITHDRAWN, middle rendering optional upstream, pending user ruling].** Forced by Foundation: `Bootstrapping.Derivation T` is `(construction T).Fixpoint` with `T` a META parameter — no uniform-in-theory-code derivability predicate exists, so a sequence of theories cannot enter one sentence as an argument. The deduction theorem collapses the day's theory to one sentence code, which is genuinely named. 

**Write-out class for a sentence-code family goes on the NEGATION codes.** `hσ : BigDigits (deductionFamilyArg σ)` with `deductionFamilyArg σ n = ⌜∼(σ n)⌝` — that code is what the day's sentence writes out. Deriving it from `BigDigits (fun n => ⌜σₙ⌝)` is NOT free: `∼` on arithmetic `Semiformula` is NNF recursion, not the propositional `φ 🡒 ⊥` that `BigSentenceCodes.neg` exploits. Foundation has a code-level negation with a Σ₁ graph (`neg L`, `negGraph L`, used by `Theory.RosserProvable`) if it is ever needed.

**The `thm:incons` witness is constant in the day (`σₙ := ⊥`), a considered choice.** A day-varying refutable family needs `BigDigits` for formulas containing the day's numeral (digit-count over unary numerals, well over 50 lines). Day-variation of the rendering is a theorem instead: `inconsistencyArgClaimSentence_ne_of_arg_ne` separates any two distinct adjoined-axiom codes with no behavioural hypothesis.

**[RETIRED T9p — premise is now `PolyArithmeticSourceSeq` on the written source; historical record of R7-C1.]** Pre-T9p, `hσ : BigDigits (deductionFamilyArg σ)` was strictly stronger than `def:ec`: `BigDigits` bounds a base-4 digit count — the paper's write-out meter only when the number IS the object's written form. `⌜∼σₙ⌝` is a formula's Gödel code; Foundation's encoding pairs at every node, so digits ~ 2^depth — the same failure mode that disqualified `Encodable.encode` as a machine-naming map. The class admits only O(log n)-depth families and EXCLUDES paper-admissible short-source/deep-parse (`iffChain`-style) ones. SECOND charge on the thm:incons row, beside the deduction-family paraphrase. Faithful repair: state the premise on `PolyArithmeticSourceSeq` (`polySegStream_binNumeralEnc` already admits the family); queued with the 9-series.

**Naming a token run: digit concatenation with a sentinel, never a pairing tree.** `tokenListNat ts := Nat.ofDigits 64 (ts ++ [63])` — base 64 = 4³ (base-4 digit theory transfers) and fits the alphabet `0..18, 20..22`; sentinel `63` is above every alphabet, so injectivity, no lost high digit, and a decoder terminator. Base-4 digit count `3·len + 3`, linear in the written text. Same doctrine as `Code.sourceNat`.

**Efficiency lives on the emission side only; the decoder may be slow.** `negSourceFormulaCode` runs inside the represented predicate, where only r.e. is asked — `tokensOfNat` may scan `List.range (v+1)` with no `PolyFueled` certificate. All `def:ec` content: `PolyArithmeticSourceSeq` → `sourceNat` → `BigDigits` → `polySegStream_binNumeral_const`. Conflating the two sides is what made the code-metered premise look necessary.

**`BigDigits.precBig` is OFF the queue** — its sole intended consumer (code-digit certificate for a day-varying incons family) is mooted by the source route; strike the 800-1500-line estimate. Related `Primrec` trivia: `tokensOfNat`'s foldr IS `takeWhile (· ≠ 63)` in the shape `Primrec.list_foldr` accepts (a literal `takeWhile` breaks the proof); `(· ^ ·)` needs `Primrec₂.unpaired'.1 Nat.Primrec.pow` (no `Primrec.nat_pow` in Mathlib).

**`dd:proofcode` is RETIRED, replaced by `dd:symbolcount` — a convention, not a substitution (9a).** §4.10 meters the paper's own quantity (symbols, inclusive bound). Residue: the paper fixes neither encoding nor alphabet, so a counting convention was chosen — one symbol per rule name/connective/quantifier/predicate/function symbol/variable occurrence, one separator per argument-list entry, and the WRITTEN BINARY DIGIT LENGTH (`idxLen`) of every index. The index clause is FORCED: counting `^&x` as one symbol makes the measure infinite-fibred (unboundedly many derivations of count 1) and the negative polarity undecidable. Any residual error over-counts, so `conWithin T k` is if anything WEAKER — never stronger. The glossary bullet was REPLACED, not stubbed (consolidation rule; the convention is a live decision deserving a live entry).

**The trick that made the 9a converse bound cheap: ill-formed codes get their own value** (`dSize n = n` on the junk branch), so `n ≤ G (dSize n)` is unconditional and the induction never threads `IsUFormula`/`Derivation` well-formedness through four layers. The junk branch is unobservable — every use sits under `Bootstrapping.Proof`. Bounding only well-formed codes was abandoned; it costs the whole side-condition apparatus.

**Mode-packed single WF recursion beats `mutual` for size functions over code trees:** `tvAux : ℕ → ℕ → ℕ`, `termination_by` the second arg, projections `tSize n := tvAux 0 n` etc. Know: (a) the strong-induction proof must quantify the mode (`∀ n mode`, induct on `n`, `intro mode` inside); (b) projection equation lemmas need `rw [tvAux]` + trailing `rfl`, and `have … from rfl` inside `rw [show …]` diverges in whnf — hoist to top-level lemmas.

**Retiring a global `dd:` marker does not move any row** — residuals live in the justification cell, never the status column, so pac/pazfc were `exact` before 9a and after, and the 42/7/1 counts are invariant across the whole tranche. And a retired marker must NOT leave a "retired" stub bullet in the README modeling boundary when its replacement is a live design decision — the stub reads as structural evidence of a previous version; item 4 stays live, relabelled "Convention, not substitution".

**T10 GO (probe 2026-08-31): `thm:incons` unqualifies via external + compact — the 9b obstruction sidestepped, not contradicted.** Design: day-theories presented by `m : ℕ → Nat.Partrec.Code` enumerating `ArithSource.sourceNat` names of axioms; `theoryOf m := {σ | ∃ b i s, evaln b m i = some s.sourceNat ∧ compile s = ↑σ}` (surjective onto r.e. sentence sets, since `ArithSource.ofNNF` writes every sentence); represented predicate `∃ b, ProvableCode ∅ (negSourceFormulaCode (combineSourceNats (axiomOutputs (Code.ofSource z) b)))` — r.e. via `Partrec.rfind`+`dom_re` over the COMPUTABLE `ProofPacked ∅` (no r.e.-projection lemma exists in Mathlib — verified absence); premises `hm : DigitMachineCodes m` + `hinc : ∀ n, ¬Consistent (theoryOf (m n))`. RETIRES the deduction paraphrase outright; drops `T'`, `[T'.Δ₁]`, `σ`, `s`, `hs`, `hcompile`; `_mentions_zero` loses its `Consistent` hypothesis. Estimate 9a-calibrated ~1200-1600 lines / ~20-28 cycles; riskiest step = the base-64 token-splice `combineTokens`/`combineSourceNats` + primrec (delegable, disjoint file). One un-verified spelling: the `∃ w` rfind projection + S4 conjunction bridge (blocked behind a build lock at probe time) — "very likely", tactic-spelling risk only. Memo: scratchpad T10-design.md; this entry is the durable record.

**Conjoin written formulas at TOKEN level, never at code level.** `sourceTokens (.and a b) = 15 :: (sourceTokens a ++ sourceTokens b)` — folding a list of sources into a conjunction is list concatenation, and `parseStructuredArithmeticFormula_sourceTokens` already takes a suffix argument. The repo exposes NO code-level `⋏` constructor with a spec (only `negFormulaCode`); building one would re-import the `Nat.pair`-squaring defect that source metering exists to avoid.

**`dd:machinetheory` (new live glossary bullet):** the presentation convention reading a machine as a theory — outputs are `sourceNat` names of axiom SOURCES; an output naming no source contributes nothing; the budget-b window at inputs `is` is `is.map (fun i => (evaln b m i).getD verumSourceNat)`. Convention, not substitution (same status as dd:symbolcount): SURJECTIVE onto the r.a. theories via `ArithSource.ofNNF`, and the paper never defines "recursively axiomatizable".

**The T10 memo's `validTokens` junk-guard is WRONG — not in the landed code, do not re-derive.** Junk-mapping-to-⊤ needs the parser to DECIDE "names a source", which parse success cannot certify (grammar completeness unproved). The working design: the window takes an explicit INPUT LIST (`axiomWindow z w` maps over `Denumerable.ofNat (List ℕ) w.unpair.2` with `.getD verumSourceNat`), so the truth direction CHOOSES good inputs and the window is literally `ss.map sourceNat` — junk never enters the spec; `combineTokens` is a bare foldr. Collapsed the memo's riskiest step to ~170 lines / one cycle.

**Why the R11 repair did NOT realign `theoryOf` to parser semantics (the first-proposed design).** `parseStructuredArithmeticFormula` returns a CODE, ignores its depth argument, accepts the free-variable tag, and the development has no parser-completeness theorem — so parse-consumed-everything cannot yield `⌜σ⌝` for any sentence; closing the converse through the parser would need parser fuel-monotonicity + a parse-append lemma (neither exists) + a Foundation `Provable T x → ∃ σ, x = ⌜σ⌝` (does not exist). A purpose-built recognizer whose soundness is a RECONSTRUCTION theorem keeps `theoryOf` at its paper-facing spelling, leaves every splice lemma applicable, and delivers the full iff. Same wall the T10 `validTokens` guard hit; this is the resolution.

**Coverage-through-witnesses pattern (R11-B1/B2 resolution):** `#assert_axioms_clean` members must carry `Paper node:` lines, so internal downstream layers can't be asserted directly without bogus annotations. When the layer is downstream of a universally-quantified endpoint, assert an APPLIED WITNESS whose STATEMENT names the layer — genuinely transitive coverage (precedent: `loopsTheory`). Adding endpoints under an existing label does not disturb the README headline counts (per-label).

**FINAL BINDER RULING APPLIED (R14, f9706da): `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are both charged globally** — decision briefs live in classification § *Arithmetic-theory hypotheses* → *Representation infrastructure, charged once and never per row* and README § *The residuals, named once*; rows carry ONE standard pointer sentence and no argumentation. Do not reintroduce per-row binder discussion. Row-specific facts retained deliberately: `[T'.Δ₁]` at thm:pazfc; thm:lp's separate `[𝗜𝚺₁ ⪯ T]` paragraph (different binder, 2026-08-30 ruling, carries the omit-rejection fact). The app:incons erratum (tex:4487-4491) is the load-bearing justification that 𝗣𝗔⁻ is not foreign to the paper — cite it as the proof's gap, not the statement's.

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

**The R7 two-valued `thm:incons` witness was retired, not ported (T9p).** `alternatingInconsistentAxiom`/`thm_incons_applied_alternating` existed only because the code-metered class could not admit an unboundedly day-varying family; `deepInconsistentSource n` is distinct on every day and `inconsistencyArgClaimSentence_deep_ne` separates every pair — keeping the dominated witness would be structural evidence of a previous version. `deductionFamilyArg_ne_of_ne` (quote injectivity) → `ArithSource.sourceNat_ne_of_sourceTokens_ne` (naming-map injectivity, no quotation needed).

**The `thm:incons` endpoint docstring now records the 9b finding at the declaration (9a):** the deduction-family paraphrase STANDS as a disclosed charge backed by a verified obstruction, not a queued repair; the middle rendering is an optional upstream item pending a user ruling; earlier retire-later claims withdrawn.

**The `def:ec` lower-calibration obstruction, stated sharply (DEFEC probe, verified 2026-08-31): the data half CANNOT be closed in either direction, and `def:ec` stays `qualified` on a verified obstruction.** BOTH directions need the same missing object — a TM → `Nat.Partrec.Code` compiler with fuel accounting. Mathlib has only code→TM (`Turing.PartrecToTM2`, explicitly without step accounting); no proof anywhere that a TM step function is `Primrec`; `TM2ComputableInPolyTime` has the identity as its only inhabitant + a `proof_wanted` composition. complexitylib has ~zero `evaln` contact. The naive coextension `Complexity.FP f → ∃ c b, PolyFueled c f b` is FALSE in-repo (`not_polyFueled_two_pow` + `n ↦ 2^n` binary-from-unary is FP: PolyFueled bounds VALUE, FP bounds LENGTH). Sharpest form: even Cobham's theorem (`CobhamFP_eq_FP`, machine-independent induction, dodges the compiler) has NO IMAGE at the `comp` case — `evaln`'s guard bounds sub-code inputs by fuel while composed poly-LENGTH words are exponential-VALUE numbers; this is the general RpnFreeze inverse-operation ceiling. Closing it = a DIFFERENT certification device (index-oracle codes), i.e. redefining `dd:fuel`, not a lemma. MIGRATION additionally gated by: (i) six §4.9/4.10 + incons endpoints consume certificates for `Computable`/numeral-spelling, needing machine→Primrec (the compiler from the other side); (ii) `LUV.BigThresholdCodeSeq` doesn't exist; (iii) `MachineSentenceCodes → MachineSentenceBlocks` (BlockWF re-blocking in FP) is an unsettled precondition — thm:scon's transport needs block discipline only the fuel witness supplies. Census: 64 of 105 endpoints carry a fuel data-class binder (BigSentenceCodes 51, BigSpliceStream 52, RpnThresholdCodes 9, DigitRatCodes 4, digits/machine 3, source 2, RpnSentenceCodes 1). Memo: scratchpad DEFEC-design.md; this entry is the durable record.

**CORRECTION to the `code_uniq` story (QuoteRepresentability.lean docstring + earlier KNOWLEDGE entries): Foundation's `codeAux_uniq`/`code_uniq` were ORIGINALLY over 𝗣𝗔⁻.** Commit `593d63d8` ("Redefine Tait-Claculus", #130, 2024-09-01) block-commented the `section model` block AND weakened its ambient theory 𝐏𝐀⁻→𝐑₀ in one stroke; at `2a76397a` the block was live with `[M ⊧ₘ* 𝐏𝐀⁻]`. The 𝗥₀ text now visible is dead code that never compiled (the `rfind` case needs `<` linear). LI's revival RESTORES the original hypothesis — the docstring currently oversells the change as ours; fix it in the next .lean pass.

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

**[SUPERSEDED T9p — `deepInconsistentSource` delivers the unbounded day-varying witness via the source route; `BigDigits.precBig` is off the queue. Historical analysis of the code-digit route:]** For `σₙ := "binNumeral n ≠ binNumeral n"` the code's bit length is Θ(√n), so `BigDigits (fun n => ⌜∼σₙ⌝)` is TRUE — but Foundation's `toNat` pairs at every node, so the code is a `Nat.pair` shell iterated Θ(log n) times over Horner recursion, and every `BigDigits` closure (`const`, `natPair`, `succ`, `add`, `mul`, `ifZero`, `comp`) composes only constantly many times; `PolyFueled.prec` forbids bignum state; `ofBase16Digits` doesn't apply (`Nat.pair` isn't digit concatenation). Needed: `BigDigits.precBig` + base-4 digit theory of `Nat.pair` at unbounded nesting — surveyed at 800-1500 lines. Do not re-scope without reading this.

**Quote injectivity for `ArithmeticSentence` at `V := ℕ`: neither `decide` nor `Nat.cast_id`/`Nat.cast_inj` works.** `decide` sticks on `Nat.beq` (noncomputable def); the `↑` from `quote_eq_encode` resists both cast lemmas. Working one-liner: `Sentence.quote_def` is `rfl` — state at the Semiproposition quote by type ascription, use `@[simp] Semiformula.quote_inj_iff` + `Rewriting.emb_injective`. See `deductionFamilyArg_ne_of_ne`.

**`one_ne_zero` is ambiguous inside `LogicalInduction` with `LO.FirstOrder.Arithmetic` open** — spell `_root_.one_ne_zero`. `T ⊢ ⊤ ⋎ ⊤` is not closed by `simp`; `cl_prover` closes it (via `Foundation.Meta.ClProver`).

**After editing an UPSTREAM file, `lake env lean` on a downstream file reads stale oleans.** Cheap iteration: `safe-lake.sh build <leaf module target>` (e.g. `LogicalInduction.Construction.Witnesses.ComputationRepresented`) rebuilds the chain then iterates at ~1-3 min. Budget the four full gates (~1h serialized on a loaded machine), not the proofs.

**Cleared suspicions from the R7 blind audit — do not re-raise.** (1) The horizon `f` is never metered and never enters a sentence: `conRunValue T' f` evaluates it inside the decider, the day-argument is `⟨⌜⊥⌝, n⟩` (poly-valued, `conClaimArg_digits`) — `ack` genuinely admissible. (2) The Con sentence is a NEGATED atom while incons is a BARE atom — correct, not an inconsistency: Con(Θ′)(ν) is a ∀-sentence (∃-negation is the prime), inconsistency is itself Σ₁; "normalising" polarities breaks the `paperTheoryDP_covers_*` bridges. (3) `provind_neg_false`'s world use at arbitrary stage is fine — the affine callback hands back a `ConsistentWithTheory DP` world (all stages). (4) `thm:incons`'s sentence is `Prov_{Θ₀}(⌜∼σₙ⌝)`, related to `Θ′ₙ ⊢ ⊥` only via the EXTERNAL deduction theorem — disclosed, and provability induction needs no internal one. (5) `codeOfREPred` is `Classical.epsilon`-chosen, so `schemaArgClaim`'s vacuous existential wrapper exists purely to give `paperPrimeDecompose` a reachable head constructor; `provable_schemaArgClaim_iff` shows T never sees it. (6) `conGamma T T' hh` takes the `ComputableHorizon` BUNDLE — not extensional in the function; clients must thread the same `hh` term through endpoint and sentence.

**In-file `example`s under `section Endpoints` variables can look like inhabitation witnesses without being ones.** Examples stated at the section VARIABLE `T` discharge only explicit arguments; only examples naming a concrete theory (𝗜𝚺₁/𝗣𝗔) discharge the instances. Check which kind before counting an example as a witness (the thm:dontwait applied example is the variable kind).

**tex thm:pazfc displays `⌜f⌝(⌜n⌝)` but never binds `f`** — it is inherited informally from thm:pac; the Lean statement correctly binds both `T'` and `horizons`. Do not read the missing binder as drift (paper-side blemish, not worth an errata row).

**Uniform-in-theory-code derivability is a VERIFIED OBSTRUCTION in Foundation (scope-9b, 2026-08-30).** `Theory.Δ₁.ch` is a meta-level formula spliced bodily into `Derivation.blueprint`'s axiom clause (`Bootstrapping/Syntax/Theory.lean:13-18`, `Syntax/Proof/Basic.lean:345,~377,403`); `⌜U.Δ₁ch.val⌝` is never formed or consumed anywhere in Foundation. A provability predicate uniform in a coded axiom-set FORMULA needs satisfaction over coded formulas in `V`; Foundation has no truth predicate over codes of any class (Tarski.lean is undefinability only), and for Σ₁ codes it is Σ₁-complete — it can never sit in a `Fixpoint.Blueprint`'s mandatory 𝚫₀/𝚫₁ core. The FEASIBLE middle: `Fixpoint.Blueprint k` is already parametric (`Arithmetic/HFS/Fixpoint.lean:18,49,177`; `Derivation` just instantiates `k=0`), so uniformity over coded FINITE axiom sets (HFS `∈` in the core) works — but adds ~nothing extensionally over the deduction paraphrase (`not_consistent_adjoin_iff` already collapses finite extensions); the gain is intensional presentation-naming only. Costs: upstream PR ~300-500 lines; LI-side clone ~800-1200 with a near-duplicate of an 851-line Foundation file (against duplication discipline); full uniformity = a 2000+-line truth-predicate project. Standing recommendation: keep the disclosed thm:incons paraphrase; the middle rendering is an OPTIONAL upstream-PR item, pending user ruling. Full memo: harness scratchpad scope-9b.md (session-local; this entry is the durable record).

**The 9a symbol measure is FEASIBLE LI-side — no obstruction (scope-9a, 2026-08-30).** A Foundation derivation code is a TREE: node = `⟪sequent, rule-tag 0-9, data…⟫ + 1`, sub-derivations nested inline (`Bootstrapping/Syntax/Proof/Basic.lean:134-152`); pairing = quadratic pair = `Nat.pair` at ℕ; sequents are BITSETS (`Exponential/Bit.lean:21-23`), exponential in the largest formula code; every component provably `< d` (Proof/Basic.lean:199-252) and `Derivation.case_iff` (:534) supports plain external strong induction at ℕ. Design: define total symbol count `dSize : ℕ → ℕ` by EXTERNAL strong recursion (skip internal definability entirely — LI meters at `V := ℕ` and consumes only `Computable`), prove `Computable dSize` via Mathlib's `Computable.nat_strong_rec`, decider via the existing `bProvPacked_sigmaOne`/`re_iff_sigma1` pattern. LOAD-BEARING: the converse bound `d ≤ g (dSize d)` (computable tower-sized `g`) keeps the bounded-search negative polarity decidable — `dSize d ≤ d` is the WRONG direction and trivializes nothing. Node count is REJECTED (breaks decidability — cut formulas unbounded at fixed node budget — and is not symbol-equivalent); code bit-length only renames the disclosure. Total symbol count fully retires `dd:proofcode` (residue: symbol-counting convention only); `conWithin_of_consistent` and the non-collapse lane survive verbatim. Estimate ~500-800 lines, 4-8 build cycles, medium risk (Primrec course-of-values grind; the g-bound bitset-sum induction). Upstream `Derivation.size` is a public good (400-700 blueprint-grade lines), not the critical path. Memo: harness scratchpad scope-9a.md (session-local; this entry is the durable record).

**A lemma existing is not the same as it being citable — the gap the search-before-prove rule leaves open.** Several `Primrec` certificates in `Construction/LIACompiler.lean` were `private`; a downstream file can find the exact fact and still be unable to use it. Correct move: EXPORT the lemma (drop `private`, docstring naming the consumer) — never re-prove it, never Batteries' `open private ... from ...` (compiles, but hides the dependency from endpoint/axiom accounting). `negFormulaCode_prim` is ~110 lines of strong recursion that would otherwise have been duplicated.

**The source parser was already there, Primrec, and hidden.** `parseStructuredArithmeticFormula` (`Framework/Criterion.lean:1799`) parses a token run — including source-only tags 20/21/22 — directly to the Gödel code of the COMPILED NNF formula, with `ArithSource.parseStructuredArithmeticFormula_sourceTokens` proving correctness on emitted runs. "Computability of `compile`" is a non-problem: no `Computable (encode ∘ compile)` is needed. The feasibility probe was four greps.

**Two source-metering designs that DON'T work.** (1) Gödel-numbering an `ArithSource` tree by pairing reproduces the defect: `Nat.pair` squares, `log(code) ~ 2^depth`, and `iffChain` is a linear chain with depth = node count. Only digit concatenation over the token run is safe. (2) Naming the code by a short arithmetic TERM (Horner over `Nat.pair`) is unsound: `Nat.pair` is a case split, and ℒₒᵣ terms have no case analysis — `Nat.pair` is formula-definable, not term-definable.

**`PolySegStream`'s token function is only specified BELOW the length; the `ofBase*Digits` bridges need every index.** Bridge with a three-way clamp (`< len → tok`, `= len → sentinel`, `> len → 0`) from two `subc_polyFueled` tests + nested `ifzSel_polyFueled`, as `BigDigits.blockSeg` does. This surfaces only when you apply the bridge.

**`Semiformula.encode_emb` is the sentence/ℕ-formula bridge and already exists** (`Foundation/FirstOrder/Basic/Coding.lean:189,196`; term version :68). Don't hand-roll the induction. The idiom for carrying a source beside the sentence it denotes is `PaperLUVSeq`'s `(source, compiles)` pair — the T9p endpoint's `(s, hcompile)` copies it deliberately.

**Tactic traps from the base-64 layer (T9p).** (1) Never `rw [← Nat.pair_unpair z]` in a `PolyFueled .of_eq` goal — it rewrites inside `z.unpair.1` and diverges; rewrite the hypothesis forward. (2) `Nat.ofDigits_append`/`_singleton` carry NO `Nat.cast` at ℕ/ℕ — a `Nat.cast_id` simp arg is inert. (3) In base-64→base-4 digit splitting the `j % 3 = 2` leg is SHORTER than `j % 3 = 1` (`Nat.mod_mul_right_div_self a 16 4` already ends mod 4). (4) `List.getD_eq_getElem` doesn't exist in core 4.31 — go `List.getD_eq_getElem?_getD` → `List.getElem?_eq_getElem` → `Option.getD_some`. (5) Don't `set M := <expr>` when you'll `rw` inside a `getElem` on `M` — use a `private def` + `:= rfl` unfolding lemma.

**`safe-lake.sh` takes the machine-wide lock BEFORE `resource-guard.sh wait`.** When the guard is LOADED for a non-transient reason (e.g. DISK below `CLAUDE_MIN_DISK_GB`, default 15), every queued build sits idle holding the lock, emits zero Lean output, and starves the machine. An empty build log is NOT evidence about the code — diagnose with `resource-guard.sh check` + `ps aux | grep safe-lake`, and kill a build immediately on learning the machine is loaded (releases the lock). AgentFoundations worktrees run 2-9GB each; a few stale `agent-*` trees can seize the whole disk. Cost ~50 min across two agents on 2026-08-30. Watcher pattern: loop `resource-guard.sh check` WITHOUT invoking safe-lake, and only call safe-lake once the guard passes.

**`have h : PolyFueled _ f := by tac` cannot work — the code metavariable is unassignable.** The ascribed type elaborates to completion BEFORE the tactic block, so the `_` for the `Code` witness is a postponed metavariable nothing will solve (`don't know how to synthesize placeholder for argument c` at the `_`, plus a cascading `unsolved goals` on the enclosing declaration from the truncated block — don't chase the second error). Use term mode: bind composites unascribed (`have hinner := ifzSel_polyFueled.comp …`) and finish `houter.of_eq (fun z => by …)` — `BigDigits.blockSeg`'s discipline (`DigitArith.lean:944`).

**Foundation registers `)[` as a TOKEN** (`FirstOrder/Basic/BinderNotation.lean:159,338`), so `(f x)[n]` is a parse error (`unexpected token ')['`) in any module importing binder notation — and parses fine in modules that don't, which looks non-deterministic. Write `getElem l n h`; a space does not help (getElem is `noWs`).

**Two different `quote_eq_encode`s** (`Bootstrapping/Syntax/Formula/Coding.lean:224,296`): `Semiformula.quote_eq_encode` is for `Semiproposition`, `Sentence.quote_eq_encode` for `Semisentence`. The wrong one gives a bare "simp made no progress". With the right one, `Semiformula.encode_emb` + `encode_inj_sentence` (both simp) finish the emb/encode bookkeeping.

**`Rewriting.emb` does not commute with `Semiformula.all` by `rfl`** — needs `Rew.q_emb`; and `Rewriting.app_all` is stated at `∀⁰`, which simp won't match against `Semiformula.all`. Incantation: `have h := Rewriting.app_all (Rew.emb : Rew ℒₒᵣ Empty 0 ℕ 0) ψ; rw [Rew.q_emb] at h; exact h`. NOTE `simpa using` that term FAILS (simp reduces the hypothesis to `True`).

**`simp` won't reduce `encodeArithmeticFormulaSymbols ⊥`** (`⊥` isn't syntactically the `.falsum` arm): supply `have hbot : … = [10] := rfl`. Same for `⊤`/`.verum`.

**`provableCode_quote_iff` takes the theory as an explicit leading argument** — `.mpr` on the bare name fails (`Unknown constant`), and `(… _).mpr` fills T not φ. Spell both: `(provableCode_quote_iff T' (⊥ : ArithmeticSentence)).mpr`. `rw` hides this by unifying leading args.

**Calibration, first-compile of a ~900-line WIP tranche:** six edits, all proof-local, none touching a statement; the authors' suspicions (a),(b),(d)-(g) were sound as written and only (c) had a defect — an elaboration-order failure, not math. Budget elaboration-order and notation-token failures ahead of mathematical ones.

**Foundation's `≤`, `/`, `%` on a MODEL are scoped instances that are NOT Nat's even at `V := ℕ`** (`LE M := ⟨fun x y => x = y ∨ x < y⟩` PeanoMinus/Basic.lean:163; noncomputable `Div`/`Mod` IOpen/Basic.lean:86,260; `+`,`*`,`<` ARE shared). Inside `open LO.FirstOrder.Arithmetic`, a `≤`/`/` YOU write elaborates to Nat's while one from a Foundation lemma is Foundation's — `exact` fails on instance mismatch. Idioms: (i) state bridging lemmas BEFORE the `open` and reach them with `refine` (a `have` re-elaborates with Nat's instance); (ii) convert with `le_def` + `Nat.le_of_eq`/`le_of_lt`. Worked example: `mem_iff_testBit` in DerivationSize.lean. Cost ~6 build cycles in 9a.

**`nat_pair_eq`'s arguments are SWAPPED vs its conclusion:** `nat_pair_eq m n : ⟪n, m⟫ = Nat.pair n m` — the natural-order bridge is `nat_pair_eq b a`.

**`PrimrecPred`/`PrimrecRel` package `Decidable` existentially** in this Mathlib, so `.to_comp` fails with `Invalid field to_comp: … Exists`; use `PrimrecPred.decide Primrec.nat_le` first.

**`G (1 + x)` will not unify with `G (?N + 1)` — and the failure is a whnf heartbeat timeout,** not a clean error, plus cascading `unsolved goals`. Normalise first: `rw [show 1 + e = e + 1 by omega]`.

**`interval_cases` needs `import Mathlib.Tactic.IntervalCases`** (error otherwise: `unknown tactic` + misleading bullet cascade); `Nat.size`/`Nat.lt_size_self` need `Mathlib.Data.Nat.Size` (not pulled by `Computability.Partrec`).

**`Primrec.comp`/`Primrec₂.comp` unfold the goal's function for HO unification and the error names a constant you never wrote** (`Option.getD` for a `List.getD` goal, `Nat.binaryRec 0` + bogus Primcodable complaint for `Nat.size`, `tvAux` for `tvPacked`). Supply `(f := …)` explicitly or route through a helper with the function as an explicit parameter; `Primrec.list_foldl`'s step must be passed `(h := …)`.

**`private` restricts name resolution, not reducibility:** downstream `rfl` still unfolds a private def (`G (N+1) = Gstep (G N)` proved by `rfl` from another file). Don't de-privatise just to state an unfolding. (`P^[6] y` = six squarings.)

**Mathlib has no `Primrec Nat.size`, no `Nat.log` primrec lemma, and no `Computable.list_map/foldr`** (only `Primrec` versions). Reuse `LogicalInduction.prim_natSize` (from `Nat.size n = Nat.size (n/2) + 1` via `nat_strong_rec`) and `LogicalInduction.computable_boundedSearchValue` (bounded ∃ over a computable binary predicate with computable bound; decidability hypothesis CURRIED `[∀ a d, Decidable (p a d)]` — pair-shaped `DecidablePred` blocks `Nat.decidableExistsLE`).

**Estimate calibration 9a:** predicted 500-800 lines / 4-8 cycles, medium risk at the g-bound. Actual ~1350 lines / ~12 cycles; the g-bound was EASY (2 cycles, junk-branch trick); the expensive pockets were Foundation-vs-Nat scoped instances (~6 cycles, one 12-line lemma) and the ~580-line Primrec grind (worth delegating to a disjoint file). Budget instance-mismatch and unification pathologies ahead of the mathematics.

**The trust-surface page's per-node text has TWO independent sources:** the reading note from `LI_READING` (gen-trust-surface.py) and the "What to check" footer from the row's justification cell (classification). Editing one and regenerating leaves the other stale, and `check_trust_surface.py` still passes — it checks page-vs-inputs, never input-vs-input (the README isn't an input at all). Always edit both for a node.

**Row-cell surgery mechanics:** justification cells are single physical lines thousands of characters long; enumerated residual lists ((i)/(ii)/(iii)) renumber by hand; identical strings can occur in BOTH pac and pazfc rows, so count replacements explicitly (a single-occurrence assert fires, a global replace is what's wanted). Verify one-line survival with `awk -F'|' '/^\| thm:pac /{print NF}'` (expect 6).

**R9 cleared suspicions on the symbol measure — do not re-raise.** (1) The ill-formed catch-alls (`else m + 1`) are provably unreachable under `Bootstrapping.Proof`: `Derivation.Phi` (Proof/Basic.lean:280-291) forces `IsFormulaSet` at every node, pins `d` to a constructor ten ways, and forces `IsTerm` in exsIntro. They exist only so `le_G_dSize` needs no well-formedness hypothesis. (2) Zero-costing (`tSize 0 = 0` etc.) does NOT create infinite fibres — `le_G_dSize` is unconditional, so `{d | dSize d ≤ k} ⊆ {d | d ≤ G k}` is finite; don't re-raise without a counterexample to that lemma. (3) `sSize` charges NO separator per sequent member while `tvSize` charges one per vector entry — deliberate asymmetry; the glossary's "one separator per argument-list entry" is about term vectors only. CAUTION: lens A also "cleared" `idxLen` as a genuine digit count, but codex R9-CX1 is right that `idxLen n = Nat.size n + 1` is digit-count PLUS ONE (`idxLen 1 = 2`) — the convention text must disclose the +1 as a per-index marker token.

**`#print axioms` is a LOGGING command — it never fails a build.** For substrate modules whose declarations carry no `Paper node:` line (DerivationSize, DerivationSizeComputable, BoundedConsistency), the entire axiom accounting is a human reading build logs, and `check_endpoint_coverage.py` checks only the annotated-label direction — a name dropped from a `#print axioms` list is caught by nothing. R9-B1/B2: an AxiomAudit prose block CLAIMED coverage three names didn't have. When a block says "axiom-checked by the footer", verify the footer actually prints every listed name.

**tex:1859's `Con(PA)(Ack)` gloss is off by one against its own definition** (tex:1857: "no proof with ν or fewer symbols" ⇒ "requires MORE than", not "at least"). Recorded in `notes/paper-errata.md`; the Lean follows the definition (inclusive `dSize d ≤ k`). A faithfulness auditor reading the gloss will think the inclusive bound is drift — it is not.

**`check-paper-nodes.sh` scans every backticked `xx:yy` token on ANY line containing `Paper node:`** — including prose in section comments that merely mentions the string. "this module carries no `Paper node:` annotation — the `dd:symbolcount` convention" on one line yields `INVALID LABEL: dd:symbolcount`. Never put a colon-token on the same physical line as the words `Paper node:`; write "paper-node annotation". And check its exit code unpiped (`| tail` masks it).

**The bare `git stash`/`pop` hazard fired in R9:** with a clean tree, `git stash` saves nothing and the following `pop` popped ANOTHER SESSION'S stash (`agent/fol-luv-frontend`), leaving six `UU` conflicts. Recovery: `git reset --hard HEAD` (a failed pop keeps the entry — nothing lost). For baseline comparisons use `git show HEAD~1:<path>` into scratch, never the stash stack. (This is the standing CLAUDE.md rule; restate it in fixer packets.)

**`Theory.Δ₁` is a DEFINABILITY class — Foundation states NO computability fact about a Δ₁ theory's axiom set** (verified absences). Membership becomes decidable only absorbed into `Proof`'s Δ₁-ness; reach for `proofPacked_computable`, never the axiom set.

**Mathlib has NO r.e.-projection lemma** (`REPred p → REPred (∃ w, …)` does not exist — RE.lean verified). Workaround when the matrix is DECIDABLE: `Partrec.rfind` + `Partrec.dom_re` + `.of_eq (by simp [Nat.rfind_dom])`. Spelling trap: carry the matrix as `f : ℕ → ℕ → Bool` with `Computable fun p : ℕ × ℕ => f p.1 p.2`, NOT as a Prop with a paired `DecidablePred` — the latter fails to synthesize `Decidable (Q z w)` inside the rfind.

**Shared-`.lake` hazard with two fixers on one checkout:** a `lake env lean` probe can hit a MID-REBUILD tree ("olean does not exist" beside siblings from two build generations — read the mtimes). `safe-lake.sh`'s lock serializes builds but does not protect a READER from a half-written tree. Probe workaround: import the lowest module with a current olean.

**`omit [inst] in` cannot drop an instance the STATEMENT can reach** — it errors `cannot omit referenced section variable`, and instance search prefers a one-step derivation from a local section instance over two steps from a stronger binder (thm:lp's `theoremDiagonalQuoteCode` needs `𝗥₀ ⪯ T`: one step from local 𝗣𝗔⁻, two from 𝗜𝚺₁). To actually drop a redundant binder, put the `variable` line inside a named `section`/`end` and declare the endpoint BELOW the `end`, recovering the weaker instance in the proof via `haveI := inferInstance`. Also: an `omit … in` on a paper-facing declaration must sit ABOVE the docstring or `check-paper-nodes.sh` reads the endpoint as un-annotated.

**A `#print axioms` footer in a build log is NOT evidence the declaration elaborated** — a failing declaration's footer still prints, and prints *"does not depend on any axioms"*, which reads as clean. Grep for `error:` before believing axiom footers.

**In a shared worktree, a bare `git commit` commits the ENTIRE INDEX — including another agent's staged files.** Explicit `git add <paths>` does not protect you if the index already holds someone else's staging: round 10's orchestrator knowledge commits swept 24 of the concurrent fixer's files (content fine, per-item trail lost). Rule: while a fixer is active in the worktree, the orchestrator commits with `git commit -- <paths>` (pathspec form) or not at all; better, don't commit at all until the fixer lands.

**Naming collision to keep straight:** "token-metered" (the tier) vs "token model / digit model" (a distinct certificate-format contrast, e.g. `RpnEmission.lean:208`). Two notions, adjacent names.

**Stale header, reported not yet fixed (fold into the next code tranche):** `ComputationDP.lean` ~lines 16-18 still says the file works "for a fixed Σ₁-sound `T ⊇ 𝗜𝚺₁`" and that `hworld` is proved from Σ₁-soundness — Σ₁-soundness is gone from the development (0/105); `hworld` follows from consistency.

**Census parsing traps (DEFEC probe, cost ~20 min).** (1) The `#check @name` grep must match DOTTED qualifiers — `(?:[A-Za-z_][\w']*\.)*NAME` — or projection notation (`X.RpnThresholdCodes`, `AffineCombination.PolySequence As`) silently undercounts (22 of 105 missed). (2) The census is incomplete without a STRUCTURE-EXPANSION pass: `AffineCombination.PolySequence.affcoh` shows no data class in its binder list and carries four; the carriers to `#print` are PolySequence/BoundedCombinationSequence/LUVCombination.*/LUVCombinationSyntax/GeneratedRatFeature/PGenerableWeighting/PaperLUVSeq. `DeductiveProcessComputation` is NOT a fuel class (bare code + eval spec = the paper's own c.e.).

**`Properties`/`Construction` do NOT transitively import the machine data classes** — only `LogicalInduction.Framework` does (`Framework.lean:61`); scratch probes need `import LogicalInduction.Framework`. And `BigTokenStream.toMachine` must be applied prefix when its argument comes from `obtain` on a `BigSpliceStream` (destructuring leaves the unfolded ∃-type).

**Estimate anchors for FP work:** `CondStep.lean` = 2,909 lines / ~50 `_mem_FP` lemmas for ONE transducer; the fuel→machine compiler chain = ~19,500 lines. "Just port the combinators to FP" is a multi-thousand-line project; the fuel-side suite to mirror is ~70 lemmas, hardest single one `BigSpliceStream.concatVar` (variable-count flatMap needing `runFold_mem_FP` with per-step length bounds).

**T10 tactic/API traps.** `Entailment.weakening!` is exported only as `Entailment.wk!` (Axiomatized namespace; exact? won't find it from ⊆-goals). `∃ b i (s : T),` does not parse — write `∃ (b i : ℕ) (s : T),`. `evaln_mono` is Option-membership-stated but `= some` coerces silently. The r.e.-projection incantation COMPILES (T10): Bool matrix from `ComputablePred.computable_iff.mp (proofPacked_computable ∅)`, pack ⟨d,w⟩ via `proofPacked_pair_iff`, then `((Partrec.rfind hF.partrec₂).dom_re).of_eq` + `simp [Nat.rfind_dom, key z]`; the Partrec₂ coercion is `Computable₂.partrec₂`. Day-varying `DigitMachineCodes` witness = `dayMachine F n := Code.curry F n` (curry embeds only the DAY as a unary const — Θ(n) tags; NEVER `Code.const v` for a payload, Θ(v) tags; `Code.nest` computes constant 0, useless as computation). Repo source family → Code: `PolyArithmeticSourceSeq` unfolds to `PolySegStream (sourceTokens ∘ s)`, `.primrec` ∘ `tokenListNat_primrec` gives `Primrec (sourceNat ∘ s)`, then `exists_code.mp (Partrec.nat_iff.mp hf.to_comp.partrec)`. `lake env lean` with same-session NEW upstream lemmas cascades `Unknown identifier` + autoImplicit noise — build the upstream module first; genuine errors are the ones NOT mentioning an unknown identifier. `PolySegStream.constList` lives in `StructuredPaperRpn.lean:657` DOWNSTREAM of Framework — constrains module placement (why DayMachine.lean is in Witnesses/). `ifzSel_polyFueled.comp ((A.pair B).pair test)` = if test = 0 then A else B (ZERO branch FIRST). Mathlib has NO Primrec lemma for `Nat.ofDigits` (verified) — reuse `tokenListNat_primrec`; use ℕ-specific `Nat.ofDigits_cons` (rfl), never the Semiring `ofDigits_eq_foldr`. Right-growing constructor runs (`Code.const`): `simp only [replicate_succ, cons_append, nil_append, append_assoc, cons.injEq, true_and]` then `rw [← replicate_succ', replicate_succ]`.

**`git add <directory>` in a harness worktree is unsafe** — swept a concurrent KNOWLEDGE.md edit into a T10 commit; recovery (no --amend): copy aside, `git checkout <base> -- <path>`, pathspec-commit the back-out, restore working-tree content. Per-file pathspecs on every add; `git status --porcelain` immediately before each commit.

**Estimate calibration T10:** predicted 1200-1600 lines / 20-28 cycles with S1 riskiest; actual ~1220 lines / ~8 cycles with S1 CHEAPEST (the input-list redesign deleted the risk; `curry`+`curry_inj` already existed). The real sink was build-lock queueing. When a design carries a "junk guard", first ask whether an explicit witness list makes the guard unnecessary.

**R11 blind audit: the T10 window has TWO cross-family-corroborated leak mechanisms (codex + lens A, independent).** (1) Splice-across-entries: incomplete-source outputs (`tokenListNat [20]`, `tokenListNat [9,9]`) concatenate into a complete refutable source `[15,20,15,9,9,9]`. (2) Prefix truncation: `tokensOfNat` keeps digits below the FIRST 63-sentinel, so non-names decode to legal runs (`8138` = digits `[10,63,1]` decodes like `4042 = (leaf ⊥).sourceNat`). Both make `MachineTheoryInconsistent` true for machines whose `theoryOf` is EMPTY (consistent) — the soundness direction is FALSE as stated, not merely unproved. Endpoint conclusions survive (only the inconsistency→predicate direction is consumed, under `hinc`), but the sentence content is broader than the `dd:machinetheory` convention claims. Repair (R11 fix wave): per-entry gate = exact round-trip name test (`tokenListNat (tokensOfNat v) = v`, kills (2)) AND complete-parse test (parser consumes the whole run, kills (1)), verum-substitute failures; align `theoryOf` semantics with the parser (an output contributes the formula the parser reads off it in full) so window-refutability ⇒ contributed formulas ∈ theory ⇒ theory inconsistent — full extensional agreement; surjectivity survives via `parseStructuredArithmeticFormula_sourceTokens` on genuine names. Also from lens A: `∼claim` polarity/paperPrime handling verified fine; `DigitMachineCodes` is write-out not runtime (don't re-raise); `negSourceFormulaCode`'s junk-to-0 justification ("code 0 never provable") is prose with no lemma — don't cite as established.

**R11 lens-B records (T10 surface).** (1) "Covered transitively by the endpoint" is NEVER true for applied witnesses — they are downstream of a universally-quantified endpoint; only upstream substrate is transitively covered. Verify with a `getUsedConstants` closure walk, not by reading the ledger (probe recipe in the R11 lens-B report; fresh names — `closure`/`contains` collide with Mathlib). (2) LI's reverse node gate is per-LABEL, not per-declaration: a second `Paper node:`-annotated carrier for an inventoried label passes every checker while sitting in no assert block (CF/MA/FFS use the per-declaration path; LI does not — hardening queued). (3) LI has NO blanket sorry/axiom gate: `check_sorry_ledger.py` is Condensation-only; `lake build AxiomAudit` reaches exactly the names in `#assert_axioms_clean`; `#print axioms` footers are non-failing info commands. (4) Verified sound in T10 and not to be re-raised: the truth chain routes compactness → common budget (`evaln_mono`) → splice spec → `provable_neg_listConj_of_not_consistent` with no represented-literal assumption; `negWindowCode_eq_quote` takes the window shape as a HYPOTHESIS so the `getD` default only ever discharges at `verumSourceNat`; `sourceTags_dayMachine`'s closed form is kernel-checked via `curry = comp c (pair (const n) id)` and `id = pair left right` (five-tag frame `[3,4,5,5,6]`).

**Docs-surgery pitfalls (R11 pass).** Python `\U0001d5e3` escapes produce WRONG sans-serif glyphs (`𝗣𝗠` for `𝗣𝗔` etc.) and no checker catches it — harvest glyphs from the target file by regex, never type escapes; `𝗭𝗙𝗖` appears in no docs file (spell plain ZFC). Check G's instantiated sentence compares BOTH numbers (`X at exact or strengthened, Y at qualified`) — moving one node changes both (pattern list at check_endpoint_coverage.py:340-357). Strength rows are 2-8KB single lines: locate with `grep -n '^| label '`, edit by exact-string replace, never `sed -n` a range (blows the output budget); cells must contain no raw `|`; regenerate the page LAST.

**R11 recognizer traps (reuse, don't re-derive).** `parseStructuredNat` is NOT injective on runs (`[1,0]`,`[1,1,0]`,… all decode 0) — the canonical-only `structuredNatRun` (side condition `p.1 ≠ 0` on tag 1) characterizes the encode image exactly. Binder depth cannot ride a `Primrec.nat_strong_rec` index (it GROWS at quantifiers; `Nat.pair` monotone per-argument only) — factor through bottom-up LEVEL functions + one `if p.1 ≤ k` at top. `PrimrecPred p` is an ∃ over the Decidable instance — a `Primrec fun a => decide (p a)` lemma won't `exact`-unify; wrap `⟨inferInstance, h⟩`. Foundation family-abbrev coercions make `Rewriting.emb` rw-lemmas SILENTLY no-op when the RHS is spelled `↑τ` (different family stamps) — spell `(Rewriting.emb τ : …)`; diagnose with `pp.explicit`. `simp [encodeArithmeticFormulaSymbols]` can't unfold under `Rewriting.emb` — push the emb through the constructor first (`coe_rel`/`coe_nrel` exist; and/or/all/exs need local rfl lemmas via `app_all`/`app_exs` + `Rew.q_emb`). `Semiformula.eq_and_iff` etc. take the rewriting ω EXPLICITLY (`(eq_and_iff Rew.emb).mp`); `eq_neg_iff` is for `🡒`, not `∼` (use `map_neg` + `neg_neg`; for `🡘` rewrite `iff_eq` first). `Provable T x → 0 < x` IS four lines (`isFormulaSet` + `IsFormulaSet.singleton` + `IsSemiformula.pos`; `fstIdx` resolves UNQUALIFIED; `_root_.lt_irrefl`); `Provable T x → ∃ σ, x = ⌜σ⌝` was searched for and does NOT exist. `split_ifs at h` auto-closes `none = some` branches (drop the old `· simp at h` bullets); `simp only [Option.bind_some] at h` BEFORE `rcases hq :` (lambda shadowing). Gate non-vacuity was checked by EVALUATION too (accepts ∀-sentences and ⟺; rejects the three audit leak shapes) — a gate rejecting everything would also be 'sound'.

**Worktree Bash-guard trap (cost a subagent ~250 finished lines):** the guard refuses compound commands ('too complex to verify'), aborting the WHOLE command — a heredoc write inside never happens, but a follow-up `lake env lean` on the stale file succeeds and the loss surfaces two steps later as `unknown identifier`. Keep writes single-command (or Write tool) and re-verify file contents after every write.

**Estimate calibration R11:** the honest window fix was not the ~50-line per-entry parser test but a ~1435-line recognizer + ~250 wiring (~60% `nat_strong_rec` boilerplate adapted from LIACompiler:2840-3480). Budget three strong recursions per new fuel-recursive certified decider; the design analysis ruling out lighter options was itself a major fraction and is recorded above.

**R11 docs-mirror records.** The `dd:machinetheory` convention text lives in SIX places that must move together: the glossary bullet (LogicalInduction.lean), ComputationRepresented's §4.10 header + `theoryOf`/`MachineTheoryInconsistent` docstrings, AxiomAudit's thm:incons block, README item 5, the classification's global bullet AND its thm:incons row cell, and `LI_READING['thm:incons']` (page regenerated from the last two). Glyph-harvest refinement: check `git show HEAD:<file> | grep -c <glyph>` (working-copy greps count your own edits — false confirmation); `↔` is absent from gen-trust-surface.py and `↑` from all three docs files — state such facts in words. The scoped-surjectivity phrasing is now everywhere; do NOT restore the old unqualified "surjective onto the r.a. theories". General lesson: a docs mirror of a soundness repair is LONGER than what it replaces — the old text asserted a claim that becomes true only BY the new mechanism, so the mechanism must be named, not just the wording swapped.

**R12 residual looseness, recorded not fixed: `check_endpoint_coverage.declarations()` walks back to the nearest `/--` WITHOUT stopping at `/-! -/` headers or intervening declarations** — an unannotated declaration after a section header inherits an earlier docstring's labels (`size_succ_le`/`unpair_fst_le_sqrt` falsely reported as thm:ob carriers). Checks C/D and `gen-trust-surface.py` consume that map, so a canonical endpoint can pass check D on an INHERITED label. Use `paper_nodes.scan` + `following_declaration` for anything that must be right; fixing `declarations()` is queued.

**AxiomAudit.lean (and EVERY registered library's .lean file) is a hashed trust-surface input** — any inventory or Lean edit reds `check_trust_surface.py` until the generator reruns; a packet forbidding `docs/` while requiring that checker green is self-contradictory whenever it touches Lean. Plan one regeneration after integration; resolve conflicts in the page by rerunning the generator, never by hand.

**AxiomAudit entry-name resolution needs a unique-dotted-suffix leg:** the file is inside `namespace LogicalInduction` and `open`s four namespaces, so ~12 entries are written relative; and `_root_.`-prefixed declarations must have the namespace prefix DISCARDED, not prepended. See `_resolve_entry`.

**Calibration:** "two witnesses slipped through" was the anecdote; the census found 166. Budget the census, not the anecdote (the fix was still cheap: ~7-13s AxiomAudit rebuild, ~1.5s scan).

**Upstream-prep pitfalls.** `git log -S` cannot find removal-by-commenting (occurrence count unchanged) — pickaxe structurally with `-G '^section model$'` without a path filter, then resolve paths per commit. Shadow-olean recipe for building modified Foundation modules without lake: `cp -Rc` the installed build (APFS hardlinks, instant), shadow FIRST on LEAN_PATH, re-emit with `lean --root=<clone> -o <shadow>/<Module>.olean` — and **`rm` each shadow file before re-emitting: they are HARDLINKS to the installed package's oleans and writing through them corrupts the installed build**. `-o` requires `--root=`. Old commented Foundation code may `open LO.Arithmetic` — a dead namespace now (material moved to `LO.FirstOrder.Arithmetic`); strip stale opens when reviving. Porting LI→Foundation is header/doc work, not proof work (same pin): module-system header, drop `#print axioms`/provenance lines, promote useful privates, commit style `<type>(scope): <subject>`, re-run `mk_all` for alphabetical registration.

**Regex-deleting one bullet from an `rcases` case chain is a trap:** non-greedy `(?:.*\n)*?` anchored on the shared bullet prefix matches from the FIRST bullet — locate the target's index, `rindex` back to the bullet start, and re-read the edited proof before building.

**Calibration, ComputationDP tag refactor:** budgeted "own tranche"; actual ~2h across 10 files, ZERO proof repair (surviving branches byte-identical); cost = three sequential full builds under the lake lock. Budget build wall-clock.

**R13 pitfalls (reuse).** Market migration is mechanical IFF the lane is generic-plus-instantiation (13 quotation endpoints, ZERO repairs — swap presentation/market/hworld); budget by the IMPORT DAG, not the proofs — compute upstream/incomparable/downstream splits first. Atom-payload tag numerals are spelled LITERALLY in emitters/parsers in grep-proof forms (`PolyFueled.const 4`, `Nat.pair 7 (Nat.pair w.1.1.2.1 w.2.1)`, …) — the COMPILER is the only oracle (each sits in a definitional `of_eq`); budget 4-6 whack-a-mole cycles, and the renumbering half of a mixed tranche is the LARGER half (6 of 7 cycles in R13). Verified look-alikes NOT to touch: EF serialize tags (Criterion:348), Foundation qq codes (negFormulaCode), DerivationSize rule codes, RPN token opcodes (`t = 1 ∨ t = 7`), theoremDP EVENT tag at ComputationDP:112 vs the PAYLOAD tag ten lines away, `Formula.or`'s constructor tag (ProductDefinition:813). File surgery by line range truncates docstrings SILENTLY (build stays green; only the node checker catches the orphaned `def`) — run the node checker after any split. `quotation_presentation_nonvacuous` still witnesses at `theoremDP` correctly (existential statement, internal witness choice).

**R13 docs-mirror records.** Market unification is NOT a safe sed: two docs sentences became FALSE, not stale — thm:pazfc's "trained on that process and nothing else" (the union adds theoremDP's atoms; honest repair: "trained on Θ's own commitments and on nothing about Θ′") and a README list putting thm:ccee among the shared-market nodes. Only reading the surrounding clause catches falsity. NOT every `paperTheoryDP` in docs is a market claim: the PaperLUV `source_valued` completed-world premises genuinely still run over `paperTheoryDP` (ArithmeticSource.lean:1194/1242/1606) — verified and left alone; blanket renames would introduce errors. `scripts/trust-surface-template.html` carries a HAND-WRITTEN vocabulary legend (~line 386) that is a generator input but not gen-trust-surface.py — a packet scoped to the generator misses it and `check_trust_surface.py` passes on the faithfully-stale render; it carried the last `theoremDP` + a wrong `𝗜𝚺₁` until the orchestrator fixed it post-R13. The 𝗣𝗔⁻/Σ₁-soundness paragraph is copy-pasted into 8 ledger rows AND 7 LI_READING notes with two independent "tag 7" spellings each — a tag rename needs four global replacements and the two files' wordings differ.

**R14 docs pitfalls.** The classification has TWO global sections — `## Global model disclosure` (substrate/dd:fuel/dd:symbolcount) and `## Arithmetic-theory hypotheses` (binders, soundness history) — cross-references must target the second for binder pointers or they dangle. Copy-paste census as of R14: the binder paragraph existed as two shared blocks (×8, ×3) + three one-offs in the ledger, and only FOUR LI_READING notes (not ~7) — count with an asserting script. Glyph trap: `𝚺` (U+1D6BA) vs `𝚪`-family mis-types make exact-match finds silently 0 — harvest from the file, assert counts, exit before writing. Quote style is MIXED (ASCII vs typographic) and load-bearing for exact strings. `docs/trust-surface.html` renders all six papers — Condensation's "pending a ruling" scope note is a standing false positive for LI ruling sweeps.

**FINAL-audit confirmed defects (fix wave in flight).** (1) `LimitCoherence.lean:20-25` duplicates Mathlib's `Prop.instMeasurableSpace`/`instMeasurableSingletonClass` and SHADOWS them repo-wide (declared later) — the rule-2b failure mode at instance level; delete and cite. (2) thm:wubexp endpoints take the support hypothesis the printed node lacks — a VERIFIED paper transposition (errata: support condition belongs on the feedback theorems; the affine twins prove it) — but the docstrings DENY the extra premise; declare the correction instead. (3) `FeedbackTruthComputation` has ONE inhabitant, constant truth ≡ 1: the §4.12 lane's non-vacuity is degenerate and undisclosed at its five endpoints. (4) `lic_self_trust_closed` is the ONE endpoint the write-out migration left at `RpnSentenceCodes` (docstring mislabels it def:ec); the narrowing enters via the quote-code lane + the nonexistent `LUV.BigThresholdCodeSeq`. (5) thm:scon's growing form hides the same class in `CompactConditioningProcessComputation.condition_codes` — structure fields are invisible to binder censuses (the standing structure-expansion lesson, now with a concrete miss). (6) thm:lp's width bundle: inhabited but never discharged in the shown example.

**Two new VERIFIED paper errata (final audit):** the thm:recurringunbiasednessexp/thm:wubexp support-condition transposition (affine twins prove the intended placement; recurringunbiasednessexp's statement references an f it never introduces), and def:seqprand's above/below sign (printed `p − ThmInd` contradicts thm:prand's pairing; counterexample = all-refutable at p=1/2; Lean's `ThmInd − p` is correct). Both in notes/paper-errata.md.

**FW pitfalls (reuse).** Import-induced PARSE breakage: adding a PaperTheoryDP import to a low-level module made an UNMODIFIED file's `xs[k]'h` unparseable (LO notation after a ?-subterm); looks nothing like an import problem and hides behind stale oleans — probe with a two-line import-only file; fix by LAYERING, never by rewriting the victim; "no consumer references a changed name" does NOT make an added import safe (notation, not names). Namespaced-grep false negatives: before recording "structure X has no witness", grep the TYPE NAME in def/instance position across namespaces. The two `#assert_axioms_clean` rules cut in OPPOSITE directions (per-declaration gate forces annotated decls IN; block membership forces unannotated decls OUT) — check annotation status before adding a name. `Entailment.Consistent` needs `open LO` (not just LO.FirstOrder...) — fails only at the third binder and reads like a missing import; copy PaperTheoryDP's full open list. `PCWorld.holds_congr_atomCodes` lives at ProductDefinition.lean:108 (not Framework/) — grep the statement shape; move candidate. Emitter chains generalize over an index-renaming map essentially for FREE (proofs transport the index without casing); tagging = `(PolyFueled.const tag).pair PolyFueled.id`. `PolyFueled` is a Prop — a/degree can't be projected; nonconstant-witness lemmas must be `Nonempty` LEMMAS. Truth-assignment defs: prefer explicit `if ∃ k, f k = n ∧ …` over `Function.invFun` (Classical junk off-image blocks TheoryTruth). Calibration: every FW budget overshot in the CHEAP direction because primitives existed — inventory combinators (`rg 'PolyFueled' | rg 'lemma |def '`) before writing; the unbudgeted cost was INTEGRATION (the parse regression outcost every fix). Errata-vs-docstring drift: when an errata entry postdates a statement's docstring, nothing gates their agreement — sweep the statements when recording an erratum.

**R15 docs-mirror records (final).** `RpnSentenceCodes` binds ZERO canonical endpoints; only token retentions = `LUV.RpnThresholdCodeSeq` on the quotation `_ofRepresentation` layer + thm:scon's `condition_codes`. thm:dus axis moved universal→instantiated on `lic_domination_everyLowerSemicomputable_paperDP` (README instantiated 18→19; the axis is gated only through the README sub-count regexes — flip both numbers in the same commit). The three `_paperDP` dus endpoints are deliberately NOT in the 105-census (parity with LI-CANONICAL + the def:ec class counts computed against it; annotated-but-noncanonical is legal if asserted). Ledger's whole-value structure list drifts silently (three stale entries corrected: IntrospectionIntervalQuote→DigitRatCodes, SelfTrustQuote→BigThresholdCodeSeq, ParadoxResistanceQuote never had the field); metering notes can be stale in the CLASS NAME while reading plausibly — check elaborated signatures. `Rpn ⊊ Big` for sentence codes has NO strictness lemma (README records it) — write "argued, not carried by a lemma". PE2 has TWO halves (wubexp carries the unprinted clause; recurringunbiasednessexp prints it with no f) — docs stating one half are wrong. New names: `indicatorProductLUV_bigThresholdCodeSeq` (renamed+generalized), `LUV.BigThresholdCodeSeq{,.toBig,.reindex}`, `SelfTrustQuote.{product,confidence}_codes` at the Big class.

**DOC pass (consumer surface + README, 2026-09-01).** README rewritten 1010→297 lines around the finished object (What is this / How it is modeled / What differs / How to use / Where the accounting lives / Layout); ALL audit statistics now live ONLY in `scripts/coverage-classification.md`'s `## Headline counts` (check G reads that file; README counts are gone and the checker will NOT catch a reintroduced count — don't). Public wrapper `LogicalInduction.lic_iff_of_recognizableSupportPerturbation` (API.lean) = the supported name for corrected thm:ifp (second carrier; asserted in a topical block, NOT LI-CANONICAL); `RecognizableSupportPerturbation` + atom helpers exported unqualified. `import LogicalInduction.API` brings WriteOut transitively — the old add-this-import advice was wrong (the "import" grep hit was inside a doc fence). APITests is a seven-step client session; `buyOneDaily`'s certificate is fully discharged from the API import alone (`ofSingleTradeBlocksBig` + `BigSentenceCodes.const` + `serialize_const`). Lean traps: docstrings can't precede `export` (use `/-! -/`); never cite paper labels from memory (def:tf not def:ef; def:exploitation; alg:li+def:lia share a line; def:affcomsen) — nothing gates README labels. Two dangling .lean comments into removed README sections left under the freeze (Framework/Computable.lean:1566 — already stale before this pass; QuoteCodeOfMarket.lean:788/796) — fix in the next tranche that rebuilds those files. Errata ledger consolidated to PE1-PE8 (duplicates folded into PE2/PE5, harness narration stripped).
