import LogicalInduction.Construction.Knowledge.Syntax
import LogicalInduction.Framework.Emission.WriteOut
import LogicalInduction.Framework.Theory.QuoteRepresentability
import LogicalInduction.Construction.Statistics.FeedbackEmission
import LogicalInduction.Construction.Quotation.DeferralFibre
import LogicalInduction.Properties.Introspection
import Foundation.FirstOrder.Bootstrapping.FixedPoint

/-!
# Arithmetic quotation and affine-package construction

The reflection apparatus behind `thm:ref` (Introspection), `thm:lp` (Paradox Resistance),
`thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee` and `thm:st` (Self-Trust).  Each of
those theorems prices a sentence that quotes a market quantity; this file supplies the
quoted syntax together with the affine portfolios that trade on it.

**Compact naming.**  The public market language is propositional, while the paper's
quotation mechanism is first-order arithmetic.  `quotationClaimCode`,
`quotationClaimSentence` and `quoteAtom` give every code-indexed Boolean decision one
injective, polynomially emitted propositional atom on payload tag `2`; the allocation table
is at `ComputationClaimKind.godelCode`.

**Fixed universal schemas.**  `universalQuotePos` and `universalQuoteNeg` are the value-`1`
and value-`0` fibers of a single code formula, `valueSchema universalQuoteCode`, with the
decision selector folded into the numeral.  That is what makes their exclusivity provable
inside `T` (`universalQuote_exclusive_prov`), and it is why nothing here takes
Σ₁-soundness (`dd:quote-code`).

**The quotation interfaces.**  `QuotationTheoryPresentation` is the language bridge: it
translates an arithmetic proof of the positive or complementary quote schema into the
corresponding public literal.  `BooleanQuoteCode` — with `BooleanQuoteCode.ofComputable` —
names a decidable decision; `RationalQuoteCode` quotes a rational value over the threshold
family `arithmeticThresholdLUV`; `ParameterizedDiagonalQuoteCode` records an actual FFL
parameterized fixed point.  Each carries a `reflected` lemma pinning completed-theory
worlds to the represented decision.

**The same-day affine layer.**  `numericQuoteAffine` holds target-minus-mesh over the
day-indexed expectation mesh `LUV.expectAffineSeq` (`def:e`); `gatedComplementAffine` and
`gatedAffirmativeAffine` are the exact Boolean gate portfolios.

**The deferred layer** is quotation-free and lives in
`Construction/Quotation/DeferralFibre.lean`, which this module imports: the variable-width affine
combinations, the paired-index emission certificate `PairedWeighting` (`def:ece`), the division-free
first-violator `selectorFeature`, and `DeferralFibre.deferred_block_price_tendsto_zero`, which
delivers deferred coherence for every `def:deferralfunc` with no injectivity or monotonicity
assumption on the schedule.

**Self-reference.**  `parameterizedDiagonalQuoteCodeOfMarket` uses Kleene's second recursion
theorem to build the public selector that prices its own atom, and matches it with the FFL
parameterized fixed point representing the same predicate; no self-reference law is a caller
premise.

**The package constructors** are `introspectionIntervalQuoteOfCode`,
`paradoxResistanceQuoteOfDiagonal`, `expectedFutureExpectationQuoteOfRepresentation`,
`futurePriceQuoteOfRepresentation`, `conditionalExpectationQuoteOfRepresentation` and
`selfTrustQuoteOfRepresentation`.

**Where the results are consumed.**  The eight paper-facing theorems at the end of the file
— `lic_expected_future_expectations_ofRepresentation`,
`lic_no_expected_net_update_ofRepresentation`,
`lic_no_expected_net_update_conditional_ofRepresentation`, `lic_self_trust_ofRepresentation`,
`lic_expectations_of_probabilities_ofCode`, `lic_iterated_expectations_ofCode`,
`lic_introspection_ofCode` and `lic_paradox_resistance_ofDiagonal` — and, downstream,
`Construction/Paper/Market.lean` over the single market `liaHistory (paperDP T)`.

Disclosed choices: `dd:quote-code` for code-indexing, `dd:mesh` for `thm:ccee`'s
slack-carrying product, `dd:fuel` for the emission certificates.
-/

namespace LogicalInduction

open Filter Topology
open LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## Compact public names and the proof bridge -/

/-- Injective atom payload for a dual-schema arithmetic decision at one input.  Tag `2`
keeps quotation names disjoint from the computation-claim roles (tags `0`–`1`); see the
global atom-payload allocation table at `ComputationClaimKind.godelCode`. -/
def quotationClaimCode (positive negative : ArithmeticSemisentence 1) (input : ℕ) : ℕ :=
  Nat.pair 2 (Nat.pair (Encodable.encode positive)
    (Nat.pair (Encodable.encode negative) input))

/-- The public propositional literal naming a dual-schema arithmetic decision at one
input: the atom whose payload is `quotationClaimCode`. -/
def quotationClaimSentence (positive negative : ArithmeticSemisentence 1)
    (input : ℕ) : Sentence :=
  LO.Propositional.Formula.atom (quotationClaimCode positive negative input)

lemma quotationClaimCode_injective :
    Function.Injective (fun p : ArithmeticSemisentence 1 ×
      ArithmeticSemisentence 1 × ℕ => quotationClaimCode p.1 p.2.1 p.2.2) := by
  rintro ⟨p₁, n₁, z₁⟩ ⟨p₂, n₂, z₂⟩ h
  simp only [quotationClaimCode, Nat.pair_eq_pair] at h
  have hp : p₁ = p₂ := Encodable.encode_inj.mp h.2.1
  have hn : n₁ = n₂ := Encodable.encode_inj.mp h.2.2.1
  cases hp
  cases hn
  cases h.2.2.2
  rfl

/-- The public naming is injective in the schema pair and the input, so no two quoted
decisions share an atom. -/
lemma quotationClaimSentence_injective :
    Function.Injective (fun p : ArithmeticSemisentence 1 ×
      ArithmeticSemisentence 1 × ℕ => quotationClaimSentence p.1 p.2.1 p.2.2) := by
  intro a b h
  apply quotationClaimCode_injective
  injection h

lemma quotationClaimSentence_poly
    (positive negative : ArithmeticSemisentence 1)
    {input : ℕ → ℕ} (hinput : PolyNatCodes input) :
    PolySentenceCodes (fun n => quotationClaimSentence positive negative (input n)) := by
  let hpayload := (PolyFueled.const 2).pair
    ((PolyFueled.const (Encodable.encode positive)).pair
      ((PolyFueled.const (Encodable.encode negative)).pair hinput.code_poly))
  refine ⟨_, (((PolyFueled.const 1).pair hpayload).succ_comp).of_eq (fun _ => rfl)⟩

/-! ## Universal computable quotation predicates

Quotation is keyed by a *decidable-decision selector* `code : ℕ`, folded into the numeral
of two **fixed** universal schemas `universalQuotePos`/`universalQuoteNeg` — the same shape
the computation side uses (`Construction/Knowledge/Syntax.lean`).  Two properties of the
interface depend on
the schemas being fixed and complementary rather than arbitrary.

*Non-vacuity.*  An interface quantifying over independent schemas
`positive negative : ArithmeticSemisentence 1` can be instantiated at
`positive = negative = ⊤`, which forces an atom and its negation into a common stage, so
that no world is consistent with the theory.  The positive and negative fibers of one
partial-recursive computation are instead mutually exclusive by determinism
(`quotePos_quoteNeg_exclusive`, with the in-theory counterpart
`universalQuote_exclusive_prov`), so a provability world can believe the positive literal
without ever being forced into a contradiction.

*Computable enumerability of the deductive process.*  There is no uniform enumeration of
the provable instances of arbitrary schemas; for a fixed schema the instances are
enumerable via `provable_instances_re`. -/

/-- The partial-recursive computation named by `code`. -/
noncomputable def decodedComputation (code : ℕ) : ℕ →. ℕ :=
  Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code code)

/-- The positive fiber: computation `code` outputs `1` on `input`. -/
def quotePos (code input : ℕ) : Prop := 1 ∈ decodedComputation code input
/-- The negative fiber: computation `code` outputs `0` on `input`. -/
def quoteNeg (code input : ℕ) : Prop := 0 ∈ decodedComputation code input

/-- Positive and negative fibers of one deterministic computation never coincide. -/
lemma quotePos_quoteNeg_exclusive (code input : ℕ) :
    ¬ (quotePos code input ∧ quoteNeg code input) := by
  rintro ⟨h1, h0⟩
  exact absurd (Part.mem_unique h1 h0) (by decide)

lemma decodedComputation_partrec (code : ℕ) : Nat.Partrec (decodedComputation code) :=
  Nat.Partrec.Code.exists_code.mpr ⟨_, rfl⟩

/-- For a partial-recursive `f`, the value-`v` fiber `{a | v ∈ f a}` is r.e. -/
lemma repred_mem {f : ℕ →. ℕ} (hf : Nat.Partrec f) (v : ℕ) :
    REPred (fun a => v ∈ f a) := by
  have hf' : Partrec f := Partrec.nat_iff.mpr hf
  have hassert : Partrec (fun p : ℕ × ℕ =>
      Part.assert (p.2 = v) fun _ => Part.some ()) := by
    have hce : Primrec (fun p : ℕ × ℕ => decide (p.2 = v)) :=
      (Primrec.eq.comp Primrec.snd (Primrec.const v)).decide
    refine (Partrec.cond hce.to_comp (Computable.const ()) Partrec.none).of_eq (fun p => ?_)
    by_cases h : p.2 = v
    · rw [Part.assert_pos h]; simp [h]
    · rw [Part.assert_neg h]; simp [h]
  have hg : Partrec (fun a => (f a).bind fun r => Part.assert (r = v) fun _ => Part.some ()) :=
    hf'.bind hassert
  refine hg.dom_re.of_eq (fun a => ?_)
  simp [Part.dom_iff_mem, Part.mem_bind_iff, Part.mem_assert_iff, eq_comm]

/-- The positive fiber is r.e.; this is what makes the quotation process enumerable. -/
lemma quotePos_re (code : ℕ) : REPred (quotePos code) :=
  repred_mem (decodedComputation_partrec code) 1

/-- The negative fiber is r.e., by the same argument at value `0`. -/
lemma quoteNeg_re (code : ℕ) : REPred (quoteNeg code) :=
  repred_mem (decodedComputation_partrec code) 0

/-- The universal computation: run computation `z.unpair.1` on input `z.unpair.2`. -/
noncomputable def universalComputation : ℕ →. ℕ :=
  fun z => decodedComputation z.unpair.1 z.unpair.2

lemma universalComputation_partrec : Nat.Partrec universalComputation := by
  refine Partrec.nat_iff.mp ?_
  exact (Nat.Partrec.Code.eval_part.comp
    ((Computable.ofNat Nat.Partrec.Code).comp (Primrec.fst.comp Primrec.unpair).to_comp)
    (Primrec.snd.comp Primrec.unpair).to_comp)

/-- The universal computation as the one-argument *vector* partial function that
Foundation's `Nat.ArithPart₁.exists_code` codes. -/
lemma universalComputation_vector_partrec :
    Partrec (fun v : List.Vector ℕ 1 => universalComputation (v.get 0)) :=
  (Partrec.nat_iff.mpr universalComputation_partrec).comp
    (Primrec.to_comp <| Primrec.vector_get.comp Primrec.id (Primrec.const (0 : Fin 1)))

/-- **One** arithmetic code formula for the whole universal quote evaluation.

The positive and negative quotation schemas are the value-`1` and value-`0` fibers of this
single formula (`valueSchema`), not two independent r.e. schemas.  That is what makes their
exclusivity provable *in the theory* (`universalQuote_exclusive_prov`) rather than merely
true in `ℕ`, and it is why the quotation family carries no Σ₁-soundness hypothesis. -/
noncomputable def universalQuoteCode : Nat.ArithPart₁.Code 1 :=
  (Nat.ArithPart₁.exists_code
    (Nat.ArithPart₁.of_partrec
      (Nat.Partrec'.of_part universalComputation_vector_partrec))).choose

lemma universalQuoteCode_spec :
    universalQuoteCode.eval (fun v : List.Vector ℕ 1 => universalComputation (v.get 0)) :=
  (Nat.ArithPart₁.exists_code
    (Nat.ArithPart₁.of_partrec
      (Nat.Partrec'.of_part universalComputation_vector_partrec))).choose_spec

/-- The fixed positive universal quotation schema — the value-`1` fiber of
`universalQuoteCode`; the selector `code` is folded into the numeral `⟨code, input⟩`. -/
noncomputable def universalQuotePos : ArithmeticSemisentence 1 :=
  valueSchema universalQuoteCode 1
/-- The fixed negative universal quotation schema — the value-`0` fiber of the *same*
code formula. -/
noncomputable def universalQuoteNeg : ArithmeticSemisentence 1 :=
  valueSchema universalQuoteCode 0

/-- Σ₁-completeness supplies the positive literal; `[𝗥₀ ⪯ T]` only. -/
lemma universalQuotePos_prov (T : ArithmeticTheory) [𝗥₀ ⪯ T] {w : ℕ}
    (h : quotePos w.unpair.1 w.unpair.2) :
    T ⊢ (universalQuotePos/[‘↑w’] : ArithmeticSentence) :=
  valueSchema_prov T universalQuoteCode_spec
    (by simpa [universalComputation, quotePos, quoteNeg] using h)

/-- Σ₁-completeness supplies the negative literal too; `[𝗥₀ ⪯ T]` only. -/
lemma universalQuoteNeg_prov (T : ArithmeticTheory) [𝗥₀ ⪯ T] {w : ℕ}
    (h : quoteNeg w.unpair.1 w.unpair.2) :
    T ⊢ (universalQuoteNeg/[‘↑w’] : ArithmeticSentence) :=
  valueSchema_prov T universalQuoteCode_spec
    (by simpa [universalComputation, quotePos, quoteNeg] using h)

/-- **Exclusivity is a theorem of `T`.**  The two quotation schemas are the value fibers of
one code formula, so `𝗣𝗔⁻` already refutes their conjunction — no appeal to the standard
model, and hence no Σ₁-soundness, is needed anywhere downstream. -/
lemma universalQuote_exclusive_prov (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] (w : ℕ) :
    T ⊢ ∼((universalQuotePos/[‘↑w’] : ArithmeticSentence) ⋏ universalQuoteNeg/[‘↑w’]) :=
  valueSchema_exclusive_prov T universalQuoteCode (by decide) w

/-- The public quotation literal for a folded selector/input pair `w = ⟨code, input⟩`. -/
noncomputable def quoteAtom (w : ℕ) : Sentence :=
  quotationClaimSentence universalQuotePos universalQuoteNeg w

/-- A first-order arithmetic background and one generic proof-to-public-language
translation.  It carries no sentence family, LUV, price, affine combination, or
asymptotic field.

The quotation fields are **code-indexed** (`dd:quote-code`): a selector `code : ℕ` naming
a decidable decision, folded into the numeral of the two fixed universal schemas
`universalQuotePos`/`universalQuoteNeg`.  Fixing the schemas is what keeps the interface
non-vacuous and the deductive process computably enumerable.
Paper node: `thm:ref`, `thm:lp`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st` -/
structure QuotationTheoryPresentation
    (DP : DeductiveProcess) (T : ArithmeticTheory)
    extends ComputationTheoryPresentation DP T where
  quote_positive_enters : ∀ (code input : ℕ),
    T ⊢ universalQuotePos/[↑(Nat.pair code input)] →
      ∃ k, quoteAtom (Nat.pair code input) ∈ DP.D k
  quote_negative_refutes : ∀ (code input : ℕ),
    T ⊢ universalQuoteNeg/[↑(Nat.pair code input)] →
      ∃ k, (∼quoteAtom (Nat.pair code input)) ∈ DP.D k

/-! ## Boolean quote families -/

/-- A uniformly named Boolean quote backed by a code-indexed decidable decision.  The
selector `code : ℕ` names a total decider; the two completeness fields translate the
public truth predicate into provability of the folded universal schemas.
Paper node: `thm:ref`, `thm:lp`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st` -/
structure BooleanQuoteCode (T : ArithmeticTheory) (truth : ℕ → Prop) where
  code : ℕ
  pos_complete : ∀ input, truth input →
    T ⊢ universalQuotePos/[↑(Nat.pair code input)]
  neg_complete : ∀ input, ¬ truth input →
    T ⊢ universalQuoteNeg/[↑(Nat.pair code input)]

namespace BooleanQuoteCode

/-- The public literal quoting the decision at input `n`: the quotation atom of the
selector/input pair `⟨code, n⟩`.  This is the sentence a downstream statement names. -/
noncomputable def sentence {T : ArithmeticTheory} {truth : ℕ → Prop}
    (q : BooleanQuoteCode T truth) (n : ℕ) : Sentence :=
  quoteAtom (Nat.pair q.code n)

/-- The quoted literal family has a uniform polynomial sentence-code emitter, which is the
certificate every portfolio built over `sentence` consumes. -/
lemma sentence_poly {T : ArithmeticTheory} {truth : ℕ → Prop}
    (q : BooleanQuoteCode T truth) : PolySentenceCodes q.sentence :=
  quotationClaimSentence_poly _ _ ⟨_, (PolyFueled.const q.code).pair PolyFueled.id⟩

/-- Completed-theory worlds satisfy exactly the represented Boolean decision. -/
lemma reflected
    {DP : DeductiveProcess} {T : ArithmeticTheory} {truth : ℕ → Prop}
    (Q : QuotationTheoryPresentation DP T) (q : BooleanQuoteCode T truth)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    v.Holds (q.sentence n) ↔ truth n := by
  constructor
  · intro hholds
    by_contra hfalse
    obtain ⟨k, hk⟩ := Q.quote_negative_refutes q.code n (q.neg_complete n hfalse)
    have hneg := hv k (∼q.sentence n) hk
    exact (PCWorld.holds_neg v (q.sentence n)).mp hneg hholds
  · intro htrue
    obtain ⟨k, hk⟩ := Q.quote_positive_enters q.code n (q.pos_complete n htrue)
    exact hv k (q.sentence n) hk

/-- Build a Boolean quote code from any decidable predicate: pick a total `{0,1}`-valued
decider, name it by its `Code`, and discharge completeness from FFL weak representation of
the folded universal fibers. -/
noncomputable def ofComputable {T : ArithmeticTheory} [𝗥₀ ⪯ T]
    {truth : ℕ → Prop} (htruth : ComputablePred truth) : BooleanQuoteCode T truth := by
  classical
  -- `.choose` (not `obtain`) since the goal is data: `∃` cannot eliminate into `Type`.
  have hcw := ComputablePred.computable_iff.1 htruth
  set f : ℕ → Bool := hcw.choose with hfdef
  have hf : Computable f := hcw.choose_spec.1
  have htr : truth = fun a => (f a : Prop) := hcw.choose_spec.2
  have hcode := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (hf.cond (Computable.const (1 : ℕ)) (Computable.const (0 : ℕ))))
  set c : Nat.Partrec.Code := hcode.choose with hcdef
  have hc : Nat.Partrec.Code.eval c = fun a => Part.some (cond (f a) 1 0) := hcode.choose_spec
  have hval : ∀ input, decodedComputation (Encodable.encode c) input =
      Part.some (cond (f input) 1 0) := by
    intro input
    simp only [decodedComputation, Denumerable.ofNat_encode, hc]
  have hpos : ∀ input, quotePos (Encodable.encode c) input ↔ truth input := by
    intro input
    simp only [quotePos, hval, Part.mem_some_iff, htr]
    cases f input <;> simp
  have hneg : ∀ input, quoteNeg (Encodable.encode c) input ↔ ¬ truth input := by
    intro input
    simp only [quoteNeg, hval, Part.mem_some_iff, htr]
    cases f input <;> simp
  refine ⟨Encodable.encode c, fun input htrue => ?_, fun input hfalse => ?_⟩
  · refine universalQuotePos_prov T (w := Nat.pair (Encodable.encode c) input) ?_
    simpa [Nat.unpair_pair] using (hpos input).mpr htrue
  · refine universalQuoteNeg_prov T (w := Nat.pair (Encodable.encode c) input) ?_
    simpa [Nat.unpair_pair] using (hneg input).mpr hfalse

end BooleanQuoteCode

/-! ## Rational quote families -/

/-- Decode a threshold payload; malformed encodings harmlessly denote zero. -/
def decodedQuotationRat (z : ℕ) : ℚ :=
  (Encodable.decode (α := ℚ) z).getD 0

@[simp] lemma decodedQuotationRat_encode (r : ℚ) :
    decodedQuotationRat (Encodable.encode r) = r := by
  simp [decodedQuotationRat]

lemma decodedQuotationRat_prim : Primrec decodedQuotationRat := by
  exact Primrec.option_getD.comp Primrec.decode (Primrec.const 0)

/-- Threshold LUV determined by a code selector, with the threshold rational folded into
the universal-schema numeral alongside the code. -/
noncomputable def arithmeticThresholdLUV (code n : ℕ) : LUV where
  gt r := quoteAtom (Nat.pair code (Nat.pair n (Encodable.encode r)))

/-- A rational-valued computation together with a code-indexed decidable threshold decision
and an honest polynomial emitter for the resulting threshold syntax.
Paper node: `thm:ref`, `thm:lp`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st` -/
structure RationalQuoteCode (T : ArithmeticTheory) (value : ℕ → ℚ) where
  code : ℕ
  value_mem : ∀ n, 0 ≤ value n ∧ value n ≤ 1
  pos_complete : ∀ (n : ℕ) (r : ℚ), r < value n →
    T ⊢ universalQuotePos/[↑(Nat.pair code (Nat.pair n (Encodable.encode r)))]
  neg_complete : ∀ (n : ℕ) (r : ℚ), value n < r →
    T ⊢ universalQuoteNeg/[↑(Nat.pair code (Nat.pair n (Encodable.encode r)))]
  threshold_poly : LUV.RpnThresholdCodeSeq (fun n => arithmeticThresholdLUV code n)

namespace RationalQuoteCode

/-- The quoted LUV at index `n`: the threshold family of the selector `code`, whose `> r`
literal is the quotation atom of `⟨code, ⟨n, ⌜r⌝⟩⟩`.  This is the LUV a downstream
statement names. -/
noncomputable def luv {T : ArithmeticTheory} {value : ℕ → ℚ}
    (q : RationalQuoteCode T value) (n : ℕ) : LUV :=
  arithmeticThresholdLUV q.code n

/-- The quoted threshold family has a uniform polynomial threshold-syntax emitter, which is
the certificate every portfolio built over `luv` consumes. -/
lemma poly {T : ArithmeticTheory} {value : ℕ → ℚ}
    (q : RationalQuoteCode T value) : LUV.RpnThresholdCodeSeq q.luv :=
  q.threshold_poly

/-- Every completed-theory world values the threshold family at the represented rational. -/
lemma reflected
    {DP : DeductiveProcess} {T : ArithmeticTheory} {value : ℕ → ℚ}
    (Q : QuotationTheoryPresentation DP T) (q : RationalQuoteCode T value)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    v.ValuesAt (q.luv n) (value n : ℝ) := by
  refine ⟨by exact_mod_cast (q.value_mem n).1,
    by exact_mod_cast (q.value_mem n).2, ?_⟩
  intro r
  constructor
  · intro hr
    have hrQ : r < value n := by exact_mod_cast hr
    obtain ⟨k, hk⟩ := Q.quote_positive_enters q.code
      (Nat.pair n (Encodable.encode r)) (q.pos_complete n r hrQ)
    exact hv k ((q.luv n).gt r) hk
  · intro hr
    have hrQ : value n < r := by exact_mod_cast hr
    obtain ⟨k, hk⟩ := Q.quote_negative_refutes q.code
      (Nat.pair n (Encodable.encode r)) (q.neg_complete n r hrQ)
    have hneg := hv k (∼(q.luv n).gt r) hk
    exact (PCWorld.holds_neg v ((q.luv n).gt r)).mp hneg

end RationalQuoteCode

/-- A closed polynomial feature carrying the represented numeric target. -/
structure NumericQuoteTarget (P : History) (target : ℕ → ℝ) where
  feature : ℕ → EF
  generated : PGenerableWeighting feature
  denote : ∀ n, (feature n).denote P = target n
  mem : ∀ n, 0 ≤ target n ∧ target n ≤ 1

/-- Literal affine syntax for `target - E(Y)`: the target is the affine constant and
the quotation thresholds are held with coefficient `-1/n`. -/
def numericQuoteAffine (H : ℕ → EF) (Y : ℕ → LUV) (n : ℕ) :
    AffineCombination where
  const := H n
  terms := ((Y n).expectAffine (n + 1)).terms.map fun p ↦
    (EF.mul (EF.const (-1)) p.1, p.2)

lemma numericQuoteAffine_value (H : ℕ → EF) (Y : ℕ → LUV)
    (P : History) (w : Valuation) (n : ℕ) :
    (numericQuoteAffine H Y n).value P w =
      (H n).denote P - (Y n).expectApprox w (n + 1) := by
  let l := ((Y n).expectAffine (n + 1)).terms
  have hbase : (l.map (fun p ↦ p.1.denote P * w p.2)).sum =
      (Y n).expectApprox w (n + 1) := by
    have h := (Y n).expectAffine_value P w (n + 1)
    rw [AffineCombination.value] at h
    norm_num [l, LUV.expectAffine] at h ⊢
    exact h
  have hsum :
      ((l.map fun p ↦ (EF.mul (EF.const (-1)) p.1, p.2)).map
          (fun p ↦ p.1.denote P * w p.2)).sum =
        -(l.map (fun p ↦ p.1.denote P * w p.2)).sum := by
    induction l with
    | nil => simp
    | cons p ps ih =>
        simp only [List.map_cons, List.sum_cons, EF.denote_mul,
          EF.denote_const, Pi.mul_apply, Rat.cast_neg, Rat.cast_one]
        rw [ih]
        ring
  rw [AffineCombination.value]
  change (H n).denote P +
      (((l.map fun p ↦ (EF.mul (EF.const (-1)) p.1, p.2)).map
        (fun p ↦ p.1.denote P * w p.2)).sum) = _
  rw [hsum, hbase]
  ring

lemma numericQuoteAffine_price (H : ℕ → EF) (Y : ℕ → LUV)
    (P : History) (n : ℕ) :
    (numericQuoteAffine H Y n).price P n =
      (H n).denote P - (Y n).expect P n := by
  rw [AffineCombination.price, numericQuoteAffine_value]
  rfl

/-- The general-day price: on day `m` the portfolio is worth the target feature minus the
day-`m` prices of the grid-`n+1` mesh. -/
lemma numericQuoteAffine_priceAt (H : ℕ → EF) (Y : ℕ → LUV)
    (P : History) (n m : ℕ) :
    (numericQuoteAffine H Y n).price P m =
      (H n).denote P - (Y n).expectApprox (P m) (n + 1) := by
  rw [AffineCombination.price, numericQuoteAffine_value]

lemma numericQuoteAffine_magnitude (H : ℕ → EF) (Y : ℕ → LUV)
    (P : History) (n : ℕ) :
    (numericQuoteAffine H Y n).magnitude P =
      ((Y n).expectAffine (n + 1)).magnitude P := by
  simp only [numericQuoteAffine, AffineCombination.magnitude, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp

/-- Polynomial emission of the concrete target-minus-threshold mesh. -/
noncomputable def numericQuoteAffine_polySequence
    (H : ℕ → EF) (Y : ℕ → LUV)
    (hH : PGenerableWeighting H) (hY : LUV.RpnThresholdCodeSeq Y) :
    AffineCombination.PolySequence (numericQuoteAffine H Y) := by
  let base := LUV.expectAffineSeq_polySequence Y hY.toBig
  exact {
    termCount := base.termCount
    coefficient := fun z ↦ EF.mul (EF.const (-1)) (base.coefficient z)
    sentence := base.sentence
    termCount_poly := base.termCount_poly
    const_poly := hH.polySeg
    coefficient_poly := BigSpliceStream.serialize_mul
      (BigSpliceStream.serialize_const (-1))
      base.coefficient_poly
    sentence_poly := base.sentence_poly
    terms_eq := by
      intro n
      rw [numericQuoteAffine]
      change (LUV.expectAffineSeq Y n).terms.map _ = _
      rw [base.terms_eq]
      simp [List.map_map, Function.comp_def]
    const_rank := hH.rank_le
    coefficient_rank := by
      intro n j hj
      simp only [EF.rank]
      exact Nat.max_le.mpr ⟨by simp, base.coefficient_rank n j hj⟩
    const_closed := hH.closed
    coefficient_closed := by
      intro z ρ V
      simp only [EF.denoteWith, EF.denote_mul, EF.denote_const,
        Pi.mul_apply]
      rw [base.coefficient_closed z ρ V]
  }

/-- Construct the entire same-day numeric quotation certificate from literal target
features and an arithmetically reflected rational quote. -/
noncomputable def completedNumericQuote
    {P : History} {DP : DeductiveProcess} {T : ArithmeticTheory}
    {value : ℕ → ℚ} (Q : QuotationTheoryPresentation DP T)
    (q : RationalQuoteCode T value)
    (target : NumericQuoteTarget P (fun n ↦ (value n : ℝ)))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    CompletedAffineQuoteApprox P DP
      (fun n ↦ (value n : ℝ) - (q.luv n).expect P n) where
  family := numericQuoteAffine target.feature q.luv
  poly := numericQuoteAffine_polySequence target.feature q.luv
    target.generated q.poly
  scale := 1
  scale_pos := by norm_num
  current_price := by
    intro n
    rw [numericQuoteAffine_price, target.denote]
    norm_num
  bounded := by
    refine ⟨1, zero_le_one, fun n m ↦ ?_⟩
    rw [numericQuoteAffine_priceAt, target.denote, abs_le]
    have hE0 := (q.luv n).expectApprox_nonneg (P m) (n + 1)
      (fun s ↦ (hP m s).1)
    have hE1 := (q.luv n).expectApprox_le_one (P m) (n + 1)
      (fun s ↦ (hP m s).2)
    have hv0 : (0 : ℝ) ≤ value n := by exact_mod_cast (q.value_mem n).1
    have hv1 : (value n : ℝ) ≤ 1 := by exact_mod_cast (q.value_mem n).2
    constructor <;> linarith
  magnitude_le_one := by
    intro n
    rw [numericQuoteAffine_magnitude]
    exact (q.luv n).expectAffine_magnitude_le_one P (n + 1)
  theory_coherent := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine eventually_atTop.2 ⟨N, fun n hn v hv ↦ ?_⟩
    have hnR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hsmall : 1 / ((n : ℝ) + 1) ≤ ε := by
      have hNn : (1 : ℝ) / ε < (n : ℝ) + 1 :=
        hN.trans_le (by have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
                        linarith)
      rw [div_lt_iff₀ hε] at hNn
      rw [div_le_iff₀ hnR]
      nlinarith
    rw [numericQuoteAffine_value, target.denote, abs_sub_comm]
    refine LE.le.trans ?_ hsmall
    simpa using (q.reflected Q n v hv).expectApprox_near (n := n + 1) n.succ_pos

/-! ### The two same-day numeric quotation packages -/

/-- Closed feature carrying the actual current price of a polynomial sentence family. -/
def currentPriceFeature (φ : ℕ → Sentence) (n : ℕ) : EF :=
  EF.price (φ n) n

lemma currentPriceFeature_generated (φ : ℕ → Sentence)
    (hφ : BigSentenceCodes φ) :
    PGenerableWeighting (currentPriceFeature φ) := by
  exact {
    polySeg := (BigSpliceStream.serialize_price (hφ) PolyFueled.id
      PolyFueled.id).of_eq (fun n ↦ by simp [currentPriceFeature])
    rank_le := by intro n; simp [currentPriceFeature]
    closed := by intro n ρ V; simp [currentPriceFeature]
  }

/-- The numeric target carried by the actual current price of a polynomial sentence family:
`hexact` says day `n`'s price of `φ n` is the quoted rational, and `currentPriceFeature`
emits it as a closed polynomial feature. -/
noncomputable def currentPriceNumericTarget
    {P : History} {T : ArithmeticTheory} {value : ℕ → ℚ}
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, P n (φ n) = (value n : ℝ)) :
    NumericQuoteTarget P (fun n ↦ (value n : ℝ)) where
  feature := currentPriceFeature φ
  generated := currentPriceFeature_generated φ hφ
  denote := by intro n; simpa [currentPriceFeature] using hexact n
  mem := by
    intro n
    exact ⟨by exact_mod_cast (q.value_mem n).1,
      by exact_mod_cast (q.value_mem n).2⟩

/-- Construct `CurrentPriceExpectationQuote` from the arithmetic quote of the actual
current rational price and the literal price-feature/threshold affine mesh. -/
noncomputable def currentPriceExpectationQuoteOfCode
    {P : History} {DP : DeductiveProcess} {T : ArithmeticTheory}
    {value : ℕ → ℚ} (Q : QuotationTheoryPresentation DP T)
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, P n (φ n) = (value n : ℝ))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    CurrentPriceExpectationQuote P DP φ q.luv where
  sentence_codes := hφ
  quote_codes := q.poly
  reflected := by
    intro n v hv
    simpa [hexact n] using q.reflected Q n v hv
  affine := by
    simpa [hexact] using completedNumericQuote Q q
      (currentPriceNumericTarget φ hφ q hexact) hP

/-- Feature evaluating the market price of the source LUV's current expectation mesh. -/
def currentExpectationFeature (X : ℕ → LUV) (n : ℕ) : EF :=
  (LUV.expectAffineSeq X n).priceFeature n

lemma currentExpectationFeature_generated (X : ℕ → LUV)
    (hX : LUV.RpnThresholdCodeSeq X) :
    PGenerableWeighting (currentExpectationFeature X) := by
  let hmesh := LUV.expectAffineSeq_polySequence X hX.toBig
  have hdiag : PolyFueled
      (Nat.Partrec.Code.id.pair Nat.Partrec.Code.id)
      (fun n : ℕ ↦ Nat.pair n n) := PolyFueled.id.pair PolyFueled.id
  exact {
    polySeg := BigSpliceStream.of_eq (hmesh.priceFeature_polySeg.comp hdiag)
      (fun n ↦ by simp [currentExpectationFeature])
    rank_le := by
      intro n
      exact AffineCombination.priceFeature_rank (LUV.expectAffineSeq X n)
        (le_refl n) (hmesh.const_rank n) (hmesh.terms_rank n)
    closed := by
      intro n ρ V
      exact hmesh.priceFeature_closed n n ρ V
  }

lemma currentExpectationFeature_denote (X : ℕ → LUV)
    (P : History) (n : ℕ) :
    (currentExpectationFeature X n).denote P = (X n).expect P n := by
  rw [currentExpectationFeature, AffineCombination.priceFeature_denote,
    LUV.expectAffineSeq_price]

/-- The numeric target carried by the current expectation of a source LUV family:
`hexact` says day `n`'s expectation of `X n` is the quoted rational, and
`currentExpectationFeature` emits the price of its own mesh as a closed polynomial
feature. -/
noncomputable def currentExpectationNumericTarget
    {P : History} {T : ArithmeticTheory} {value : ℕ → ℚ}
    (X : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, (X n).expect P n = (value n : ℝ)) :
    NumericQuoteTarget P (fun n ↦ (value n : ℝ)) where
  feature := currentExpectationFeature X
  generated := currentExpectationFeature_generated X hX
  denote := by
    intro n
    rw [currentExpectationFeature_denote, hexact n]
  mem := by
    intro n
    exact ⟨by exact_mod_cast (q.value_mem n).1,
      by exact_mod_cast (q.value_mem n).2⟩

/-- Construct `CurrentExpectationQuote` from the arithmetic quote of the literal source
expectation computation. -/
noncomputable def currentExpectationQuoteOfCode
    {P : History} {DP : DeductiveProcess} {T : ArithmeticTheory}
    {value : ℕ → ℚ} (Q : QuotationTheoryPresentation DP T)
    (X : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, (X n).expect P n = (value n : ℝ))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    CurrentExpectationQuote P DP X q.luv where
  source_codes := hX
  quote_codes := q.poly
  reflected := by
    intro n v hv
    simpa [hexact n] using q.reflected Q n v hv
  affine := by
    simpa [hexact] using completedNumericQuote Q q
      (currentExpectationNumericTarget X hX q hexact) hP

/-! ## Exact Boolean gate portfolios -/

/-- `scale · H · (1 - quote)` as literal one-share affine syntax. -/
def gatedComplementAffine (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (n : ℕ) : AffineCombination where
  const := EF.mul (EF.const scale) (H n)
  terms := [(EF.mul (EF.const (-scale)) (H n), quote n)]

/-- `scale · H · quote` as literal one-share affine syntax. -/
def gatedAffirmativeAffine (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (n : ℕ) : AffineCombination where
  const := EF.const 0
  terms := [(EF.mul (EF.const scale) (H n), quote n)]

@[simp] lemma gatedComplementAffine_price (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (P : History) (n m : ℕ) :
    (gatedComplementAffine scale H quote n).price P m =
      (scale : ℝ) * (H n).denote P * (1 - P m (quote n)) := by
  simp [gatedComplementAffine, AffineCombination.price,
    AffineCombination.value]
  ring

@[simp] lemma gatedComplementAffine_value (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (P : History) (w : Valuation) (n : ℕ) :
    (gatedComplementAffine scale H quote n).value P w =
      (scale : ℝ) * (H n).denote P * (1 - w (quote n)) := by
  simp [gatedComplementAffine, AffineCombination.value]
  ring

@[simp] lemma gatedComplementAffine_magnitude (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (P : History) (n : ℕ) :
    (gatedComplementAffine scale H quote n).magnitude P =
      |(scale : ℝ) * (H n).denote P| := by
  simp [gatedComplementAffine, AffineCombination.magnitude, abs_mul]

@[simp] lemma gatedAffirmativeAffine_price (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (P : History) (n m : ℕ) :
    (gatedAffirmativeAffine scale H quote n).price P m =
      (scale : ℝ) * (H n).denote P * P m (quote n) := by
  simp [gatedAffirmativeAffine, AffineCombination.price,
    AffineCombination.value]

@[simp] lemma gatedAffirmativeAffine_value (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (P : History) (w : Valuation) (n : ℕ) :
    (gatedAffirmativeAffine scale H quote n).value P w =
      (scale : ℝ) * (H n).denote P * w (quote n) := by
  simp [gatedAffirmativeAffine, AffineCombination.value]

@[simp] lemma gatedAffirmativeAffine_magnitude (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (P : History) (n : ℕ) :
    (gatedAffirmativeAffine scale H quote n).magnitude P =
      |(scale : ℝ) * (H n).denote P| := by
  simp [gatedAffirmativeAffine, AffineCombination.magnitude, abs_mul]

/-- The uniform polynomial emitter for `gatedComplementAffine`: one term per day, whose
coefficient stream is `-scale · H` and whose sentence stream is the quote literal.  It
consumes a `PGenerableWeighting` certificate for `H` and a `PolySentenceCodes` certificate
for the quote family. -/
noncomputable def gatedComplementAffine_polySequence
    (scale : ℚ) (H : ℕ → EF) (quote : ℕ → Sentence)
    (hH : PGenerableWeighting H) (hq : PolySentenceCodes quote) :
    AffineCombination.PolySequence (gatedComplementAffine scale H quote) := by
  let cq := Classical.choose hq
  have hcq := Classical.choose_spec hq
  exact {
    termCount := fun _ ↦ 1
    coefficient := fun z ↦ EF.mul (EF.const (-scale)) (H z.unpair.1)
    sentence := fun z ↦ quote z.unpair.1
    termCount_poly := ⟨Nat.Partrec.Code.const 1, PolyFueled.const 1⟩
    const_poly := BigSpliceStream.serialize_mul
      (BigSpliceStream.serialize_const scale) hH.polySeg
    coefficient_poly := BigSpliceStream.serialize_mul
      (BigSpliceStream.serialize_const (-scale))
      (hH.polySeg.comp PolyFueled.left)
    sentence_poly := BigSentenceCodes.ofPolySentenceCodes
      ⟨cq.comp Nat.Partrec.Code.left, hcq.comp PolyFueled.left⟩
    terms_eq := by intro n; simp [gatedComplementAffine]
    const_rank := by
      intro n
      simp only [gatedComplementAffine, EF.rank]
      exact Nat.max_le.mpr ⟨by simp, hH.rank_le n⟩
    coefficient_rank := by
      intro n j hj
      simp only [EF.rank]
      exact Nat.max_le.mpr ⟨by simp,
        by simpa only [Nat.unpair_pair] using hH.rank_le n⟩
    const_closed := by
      intro n ρ V
      simp only [gatedComplementAffine, EF.denoteWith, EF.denote_mul,
        EF.denote_const, Pi.mul_apply]
      rw [hH.closed n ρ V]
    coefficient_closed := by
      intro z ρ V
      simp only [EF.denoteWith, EF.denote_mul, EF.denote_const, Pi.mul_apply]
      rw [hH.closed z.unpair.1 ρ V]
  }

/-- The uniform polynomial emitter for `gatedAffirmativeAffine`: one term per day with
coefficient stream `scale · H` over the quote literal and zero constant.  It consumes the
same two certificates as `gatedComplementAffine_polySequence`. -/
noncomputable def gatedAffirmativeAffine_polySequence
    (scale : ℚ) (H : ℕ → EF) (quote : ℕ → Sentence)
    (hH : PGenerableWeighting H) (hq : PolySentenceCodes quote) :
    AffineCombination.PolySequence (gatedAffirmativeAffine scale H quote) := by
  let cq := Classical.choose hq
  have hcq := Classical.choose_spec hq
  exact {
    termCount := fun _ ↦ 1
    coefficient := fun z ↦ EF.mul (EF.const scale) (H z.unpair.1)
    sentence := fun z ↦ quote z.unpair.1
    termCount_poly := ⟨Nat.Partrec.Code.const 1, PolyFueled.const 1⟩
    const_poly := BigSpliceStream.serialize_const 0
    coefficient_poly := BigSpliceStream.serialize_mul
      (BigSpliceStream.serialize_const scale)
      (hH.polySeg.comp PolyFueled.left)
    sentence_poly := BigSentenceCodes.ofPolySentenceCodes
      ⟨cq.comp Nat.Partrec.Code.left, hcq.comp PolyFueled.left⟩
    terms_eq := by intro n; simp [gatedAffirmativeAffine]
    const_rank := by intro n; simp [gatedAffirmativeAffine]
    coefficient_rank := by
      intro n j hj
      simp only [EF.rank]
      exact Nat.max_le.mpr ⟨by simp,
        by simpa only [Nat.unpair_pair] using hH.rank_le n⟩
    const_closed := by intro n ρ V; simp [gatedAffirmativeAffine]
    coefficient_closed := by
      intro z ρ V
      simp only [EF.denoteWith, EF.denote_mul, EF.denote_const, Pi.mul_apply]
      rw [hH.closed z.unpair.1 ρ V]
  }

/-- Exact completed-theory portfolio when a gate can be nonzero only if the quoted
Boolean decision is true. -/
noncomputable def completedGatedComplementQuote
    {P : History} {DP : DeductiveProcess} {T : ArithmeticTheory}
    {truth : ℕ → Prop} (Q : QuotationTheoryPresentation DP T)
    (q : BooleanQuoteCode T truth) (H : ℕ → EF)
    (hH : PGenerableWeighting H) (scale : ℚ) (hscale : 0 < scale)
    (hHnonneg : ∀ n, 0 ≤ (H n).denote P)
    (hnorm : ∀ n, (scale : ℝ) * (H n).denote P ≤ 1)
    (hzero : ∀ n, ¬truth n → (H n).denote P = 0)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    CompletedAffineQuoteEq P DP
      (fun n ↦ (H n).denote P * (1 - P n (q.sentence n))) where
  family := gatedComplementAffine scale H q.sentence
  poly := gatedComplementAffine_polySequence scale H q.sentence hH q.sentence_poly
  scale := scale
  scale_pos := hscale
  current_price := by intro n; rw [gatedComplementAffine_price]; ring
  bounded := by
    refine ⟨1, zero_le_one, fun n m ↦ ?_⟩
    rw [gatedComplementAffine_price, abs_of_nonneg (mul_nonneg
      (mul_nonneg (by exact_mod_cast hscale.le) (hHnonneg n))
      (sub_nonneg.mpr (hP m _).2))]
    nlinarith [hnorm n, (hP m (q.sentence n)).1, (hP m (q.sentence n)).2]
  magnitude_le_one := by
    intro n
    rw [gatedComplementAffine_magnitude,
      abs_of_nonneg (mul_nonneg (by exact_mod_cast hscale.le) (hHnonneg n))]
    exact hnorm n
  theory_coherent := by
    intro n v hv
    rw [gatedComplementAffine_value]
    by_cases ht : truth n
    · have hholds := (q.reflected Q n v hv).2 ht
      simp [PCWorld.payout, hholds]
    · rw [hzero n ht]
      ring

/-- Exact completed-theory portfolio when a gate can be nonzero only if the quoted
Boolean decision is false. -/
noncomputable def completedGatedAffirmativeQuote
    {P : History} {DP : DeductiveProcess} {T : ArithmeticTheory}
    {truth : ℕ → Prop} (Q : QuotationTheoryPresentation DP T)
    (q : BooleanQuoteCode T truth) (H : ℕ → EF)
    (hH : PGenerableWeighting H) (scale : ℚ) (hscale : 0 < scale)
    (hHnonneg : ∀ n, 0 ≤ (H n).denote P)
    (hnorm : ∀ n, (scale : ℝ) * (H n).denote P ≤ 1)
    (hzero : ∀ n, truth n → (H n).denote P = 0)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    CompletedAffineQuoteEq P DP
      (fun n ↦ (H n).denote P * P n (q.sentence n)) where
  family := gatedAffirmativeAffine scale H q.sentence
  poly := gatedAffirmativeAffine_polySequence scale H q.sentence hH q.sentence_poly
  scale := scale
  scale_pos := hscale
  current_price := by intro n; rw [gatedAffirmativeAffine_price]; ring
  bounded := by
    refine ⟨1, zero_le_one, fun n m ↦ ?_⟩
    rw [gatedAffirmativeAffine_price, abs_of_nonneg (mul_nonneg
      (mul_nonneg (by exact_mod_cast hscale.le) (hHnonneg n)) (hP m _).1)]
    nlinarith [hnorm n, (hP m (q.sentence n)).1, (hP m (q.sentence n)).2]
  magnitude_le_one := by
    intro n
    rw [gatedAffirmativeAffine_magnitude,
      abs_of_nonneg (mul_nonneg (by exact_mod_cast hscale.le) (hHnonneg n))]
    exact hnorm n
  theory_coherent := by
    intro n v hv
    rw [gatedAffirmativeAffine_value]
    by_cases ht : truth n
    · rw [hzero n ht]
      ring
    · have hfalse : ¬v.Holds (q.sentence n) :=
        fun h ↦ ht ((q.reflected Q n v hv).1 h)
      simp [PCWorld.payout, hfalse]

/-! ## Interval quotation package -/

/-- Construct the complete interval-introspection quotation package from the literal
current-price feature, generated rational endpoints, a generated continuous width, and
one arithmetically reflected Boolean interval claim.  Both affine certificates are
concrete one-share portfolios; the outward sum is normalized by `1/2`. -/
noncomputable def introspectionIntervalQuoteOfCode
    {P : History} {DP : DeductiveProcess} {T : ArithmeticTheory}
    (Q : QuotationTheoryPresentation DP T)
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (a b δ : ℕ → ℚ)
    (lowerFeature : ℕ → EF)
    (hlower : GeneratedRatFeature P a lowerFeature)
    (upperFeature : ℕ → EF)
    (hupper : GeneratedRatFeature P b upperFeature)
    (hδinv : DigitRatCodes (fun n ↦ 1 / δ n))
    (hδpos : ∀ n, 0 < δ n)
    (hδzero : Tendsto (fun n ↦ (δ n : ℝ)) atTop (𝓝 0))
    (hab : ∀ n, 0 ≤ a n ∧ a n ≤ 1 ∧ 0 ≤ b n ∧ b n ≤ 1)
    (q : BooleanQuoteCode T (fun n ↦
      (a n : ℝ) < P n (φ n) ∧ P n (φ n) < (b n : ℝ)))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    IntrospectionIntervalQuote P DP φ a b δ := by
  let price : ℕ → EF := currentPriceFeature φ
  let inLower : ℕ → EF := ctsIndFeature δ price lowerFeature
  let inUpper : ℕ → EF := ctsIndFeature δ upperFeature price
  let inside : ℕ → EF := fun n ↦ EF.mul (inLower n) (inUpper n)
  let outLower : ℕ → EF := ctsIndFeature δ lowerFeature price
  let outUpper : ℕ → EF := ctsIndFeature δ price upperFeature
  let outside : ℕ → EF := fun n ↦ EF.add (outLower n) (outUpper n)
  have hprice : PGenerableWeighting price := currentPriceFeature_generated φ hφ
  have hinLower : PGenerableWeighting inLower :=
    ctsIndFeature_generated δ price lowerFeature hδinv hprice hlower.toWeighting
  have hinUpper : PGenerableWeighting inUpper :=
    ctsIndFeature_generated δ upperFeature price hδinv hupper.toWeighting hprice
  have hinside : PGenerableWeighting inside := hinLower.mul hinUpper
  have houtLower : PGenerableWeighting outLower :=
    ctsIndFeature_generated δ lowerFeature price hδinv hlower.toWeighting hprice
  have houtUpper : PGenerableWeighting outUpper :=
    ctsIndFeature_generated δ price upperFeature hδinv hprice hupper.toWeighting
  have houtside : PGenerableWeighting outside := houtLower.add houtUpper
  have hpriceDenote (n : ℕ) : (price n).denote P = P n (φ n) := by
    simp [price, currentPriceFeature]
  have hinLowerDenote (n : ℕ) : (inLower n).denote P =
      ctsInd (δ n) (P n (φ n)) (a n : ℝ) := by
    rw [show inLower n = ctsIndFeature δ price lowerFeature n by rfl,
      ctsIndFeature_denote δ price lowerFeature hδpos P n,
      hpriceDenote n, hlower.denote n]
  have hinUpperDenote (n : ℕ) : (inUpper n).denote P =
      ctsInd (δ n) (b n : ℝ) (P n (φ n)) := by
    rw [show inUpper n = ctsIndFeature δ upperFeature price n by rfl,
      ctsIndFeature_denote δ upperFeature price hδpos P n,
      hupper.denote n, hpriceDenote n]
  have houtLowerDenote (n : ℕ) : (outLower n).denote P =
      ctsInd (δ n) (a n : ℝ) (P n (φ n)) := by
    rw [show outLower n = ctsIndFeature δ lowerFeature price n by rfl,
      ctsIndFeature_denote δ lowerFeature price hδpos P n,
      hlower.denote n, hpriceDenote n]
  have houtUpperDenote (n : ℕ) : (outUpper n).denote P =
      ctsInd (δ n) (P n (φ n)) (b n : ℝ) := by
    rw [show outUpper n = ctsIndFeature δ price upperFeature n by rfl,
      ctsIndFeature_denote δ price upperFeature hδpos P n,
      hpriceDenote n, hupper.denote n]
  have hinsideDenote (n : ℕ) : (inside n).denote P =
      ctsInd (δ n) (P n (φ n)) (a n : ℝ) *
        ctsInd (δ n) (b n : ℝ) (P n (φ n)) := by
    simp only [inside, EF.denote_mul, Pi.mul_apply, hinLowerDenote, hinUpperDenote]
  have houtsideDenote (n : ℕ) : (outside n).denote P =
      ctsInd (δ n) (a n : ℝ) (P n (φ n)) +
        ctsInd (δ n) (P n (φ n)) (b n : ℝ) := by
    simp only [outside, EF.denote_add, Pi.add_apply, houtLowerDenote, houtUpperDenote]
  refine {
    source_codes := hφ
    lower_feature := lowerFeature
    lower_generated := hlower
    upper_feature := upperFeature
    upper_generated := hupper
    inverse_width_codes := hδinv
    width_pos := hδpos
    width_tendsto_zero := hδzero
    probability_bounds := hab
    quote := q.sentence
    quote_codes := BigSentenceCodes.ofPolySentenceCodes q.sentence_poly
    reflected := by
      intro n v hv
      exact q.reflected Q n v hv
    inside_affine := ?_
    outside_affine := ?_
  }
  · simpa only [hinsideDenote] using completedGatedComplementQuote Q q inside
      hinside 1 (by norm_num)
      (fun n ↦ by
        rw [hinsideDenote]
        exact mul_nonneg (ctsInd_mem_Icc _ _ _).1 (ctsInd_mem_Icc _ _ _).1)
      (fun n ↦ by
        rw [hinsideDenote]
        have h₁ := ctsInd_mem_Icc (δ n) (P n (φ n)) (a n : ℝ)
        have h₂ := ctsInd_mem_Icc (δ n) (b n : ℝ) (P n (φ n))
        norm_num
        exact (mul_le_mul_of_nonneg_left h₂.2 h₁.1).trans (by simpa using h₁.2))
      (fun n hn ↦ by
        rw [hinsideDenote]
        by_cases hleft : P n (φ n) ≤ (a n : ℝ)
        · rw [ctsInd_eq_zero_of_le (δ n) _ _ (hδpos n) hleft, zero_mul]
        · have hright : (b n : ℝ) ≤ P n (φ n) := by
            by_contra hnot
            exact hn ⟨lt_of_not_ge hleft, lt_of_not_ge hnot⟩
          rw [ctsInd_eq_zero_of_le (δ n) _ _ (hδpos n) hright, mul_zero])
      hP
  · simpa only [houtsideDenote] using completedGatedAffirmativeQuote Q q outside
      houtside (1 / 2) (by norm_num)
      (fun n ↦ by
        rw [houtsideDenote]
        exact add_nonneg (ctsInd_mem_Icc _ _ _).1 (ctsInd_mem_Icc _ _ _).1)
      (fun n ↦ by
        rw [houtsideDenote]
        rcases ctsInd_mem_Icc (δ n) (a n : ℝ) (P n (φ n)) with ⟨h₁0, h₁1⟩
        rcases ctsInd_mem_Icc (δ n) (P n (φ n)) (b n : ℝ) with ⟨h₂0, h₂1⟩
        norm_num
        linarith)
      (fun n hn ↦ by
        rw [houtsideDenote]
        have hleft : (a n : ℝ) ≤ P n (φ n) := hn.1.le
        have hright : P n (φ n) ≤ (b n : ℝ) := hn.2.le
        rw [ctsInd_eq_zero_of_le (δ n) _ _ (hδpos n) hleft,
          ctsInd_eq_zero_of_le (δ n) _ _ (hδpos n) hright, zero_add])
      hP

/-! ## Genuine parameterized diagonal syntax -/

/-- A Boolean quote family carrying an actual FFL parameterized fixed point `body`.
`represents_fixedpoint` identifies its standard-model predicate with the decision quoted by
the inherited public atom.  The paper-facing constructor
`parameterizedDiagonalQuoteCodeOfMarket` below derives both pieces from the same
self-referential market computation; callers do not supply the semantic diagonal relation.
Paper node: `thm:lp` -/
structure ParameterizedDiagonalQuoteCode
    (T : ArithmeticTheory) (truth : ℕ → Prop)
    extends BooleanQuoteCode T truth where
  body : ArithmeticSemisentence 2
  represents_fixedpoint : ∀ (z : ℕ), (parameterizedFixedpoint body).Evalb ![z] ↔ truth z

/-- The genuine parameterized fixed point carried by a diagonal quote satisfies FFL's
uniform diagonal law inside the ambient arithmetic theory: a genuine self-referential
arithmetic sentence, not a stipulated relation, backs the quoted decision. -/
lemma ParameterizedDiagonalQuoteCode.diagonal_law
    {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] {truth : ℕ → Prop}
    (q : ParameterizedDiagonalQuoteCode T truth) :
    T ⊢ ∀⁰ (parameterizedFixedpoint q.body 🡘
      q.body/[⌜parameterizedFixedpoint q.body⌝, #0]) := by
  simpa using parameterized_diagonal₁ (T := T) q.body

/-! ## A public diagonal atom derived from the computable market -/

/-- Given a candidate selector program `c`, run the market on the public atom selected by
`c` and output `1` exactly when that same-day price is below `p`.  Kleene's second recursion
theorem will choose a selector whose behavior is this very computation at its own code. -/
noncomputable def diagonalPriceDecisionPart
    {P : History} (market : MarketComputation P) (p : ℚ)
    (c : Nat.Partrec.Code) (n : ℕ) : Part ℕ :=
  (market.code.eval
    (Nat.pair n
      (Encodable.encode
        (quoteAtom (Nat.pair (Encodable.encode c) n))))).map fun out =>
          if decodedQuotationRat out < p then 1 else 0

/-- The market-relative diagonal decision is a partial-recursive binary program.
Paper node: `thm:lp` -/
lemma diagonalPriceDecisionPart_partrec
    {P : History} (market : MarketComputation P) (p : ℚ) :
    Partrec₂ (diagonalPriceDecisionPart market p) := by
  let input : Nat.Partrec.Code × ℕ → ℕ := fun z =>
    Nat.pair z.2
      (Encodable.encode
        (quoteAtom (Nat.pair (Encodable.encode z.1) z.2)))
  have hcode : Primrec fun z : Nat.Partrec.Code × ℕ => Encodable.encode z.1 :=
    Primrec.encode.comp Primrec.fst
  have hselector : Primrec fun z : Nat.Partrec.Code × ℕ =>
      Nat.pair (Encodable.encode z.1) z.2 :=
    Primrec₂.natPair.comp hcode Primrec.snd
  have hpayload : Primrec fun z : Nat.Partrec.Code × ℕ =>
      quotationClaimCode universalQuotePos universalQuoteNeg
        (Nat.pair (Encodable.encode z.1) z.2) :=
    Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const (Encodable.encode universalQuotePos))
        (Primrec₂.natPair.comp (Primrec.const (Encodable.encode universalQuoteNeg))
          hselector))
  have hsentence : Primrec fun z : Nat.Partrec.Code × ℕ =>
      Encodable.encode
        (quoteAtom (Nat.pair (Encodable.encode z.1) z.2)) :=
    (Primrec.succ.comp
      (Primrec₂.natPair.comp (Primrec.const 1) hpayload)).of_eq fun _ => rfl
  have hinput : Computable input :=
    (Primrec.snd.pair hsentence).to_comp
  have heval : Partrec fun z : Nat.Partrec.Code × ℕ =>
      market.code.eval (input z) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const market.code) hinput
  have hrat : Primrec fun out : ℕ => decodedQuotationRat out :=
    decodedQuotationRat_prim
  have hlt : PrimrecPred fun out : ℕ => decodedQuotationRat out < p :=
    ((ratLE_prim.comp (Primrec.const p) hrat).not).of_eq fun _ => not_le
  have hdecision : Computable fun out : ℕ =>
      if decodedQuotationRat out < p then 1 else 0 :=
    (Primrec.ite hlt (Primrec.const 1) (Primrec.const 0)).to_comp
  exact (heval.map ((hdecision.comp Computable.snd).to₂)).to₂

/-- The actual program fixed point behind the public paradox-resistance atom. -/
noncomputable def diagonalPriceDecisionCode
    {P : History} (market : MarketComputation P) (p : ℚ) :
    Nat.Partrec.Code :=
  Classical.choose
    (Nat.Partrec.Code.fixed_point₂ (diagonalPriceDecisionPart_partrec market p))

lemma diagonalPriceDecisionCode_spec
    {P : History} (market : MarketComputation P) (p : ℚ) :
    (diagonalPriceDecisionCode market p).eval =
      diagonalPriceDecisionPart market p (diagonalPriceDecisionCode market p) :=
  Classical.choose_spec
    (Nat.Partrec.Code.fixed_point₂ (diagonalPriceDecisionPart_partrec market p))

/-- The semantic predicate decided by the self-referential selector: its own public atom
has same-day market price below `p`. -/
def diagonalPriceTruth
    {P : History} (market : MarketComputation P) (p : ℚ) (n : ℕ) : Prop :=
  market.quote n
    (Encodable.encode
      (quoteAtom
        (Nat.pair (Encodable.encode (diagonalPriceDecisionCode market p)) n))) < p

/-- The Kleene fixed selector computes the threshold decision for its own public atom.
Paper node: `thm:lp` -/
lemma diagonalPriceDecisionCode_eval
    {P : History} (market : MarketComputation P) (p : ℚ) (n : ℕ) :
    (diagonalPriceDecisionCode market p).eval n =
      Part.some (if market.quote n
        (Encodable.encode
          (quoteAtom
            (Nat.pair (Encodable.encode (diagonalPriceDecisionCode market p)) n))) < p
        then 1 else 0) := by
  classical
  rw [diagonalPriceDecisionCode_spec]
  unfold diagonalPriceDecisionPart
  let input := Nat.pair n
    (Encodable.encode
      (quoteAtom
        (Nat.pair (Encodable.encode (diagonalPriceDecisionCode market p)) n)))
  have hmarket := market.code_spec input
  have hmarketEq : market.code.eval input =
      Part.some (Encodable.encode
        (market.quote input.unpair.1 input.unpair.2)) :=
    Part.eq_some_iff.mpr hmarket
  rw [show Nat.pair n
      (Encodable.encode
        (quoteAtom
          (Nat.pair (Encodable.encode (diagonalPriceDecisionCode market p)) n))) =
        input from rfl, hmarketEq]
  simp [input, decodedQuotationRat]

/-- The fixed selector's positive quote is exactly the market-derived diagonal predicate.
Paper node: `thm:lp` -/
lemma diagonalPriceQuotePos_iff
    {P : History} (market : MarketComputation P) (p : ℚ) (n : ℕ) :
    quotePos (Encodable.encode (diagonalPriceDecisionCode market p)) n ↔
      diagonalPriceTruth market p n := by
  classical
  rw [quotePos]
  simp only [decodedComputation, Denumerable.ofNat_encode, diagonalPriceDecisionCode_eval,
    diagonalPriceTruth]
  split <;> simp_all

/-- The fixed selector's negative quote is exactly the complement of its diagonal predicate.
Paper node: `thm:lp` -/
lemma diagonalPriceQuoteNeg_iff
    {P : History} (market : MarketComputation P) (p : ℚ) (n : ℕ) :
    quoteNeg (Encodable.encode (diagonalPriceDecisionCode market p)) n ↔
      ¬diagonalPriceTruth market p n := by
  classical
  rw [quoteNeg]
  simp only [decodedComputation, Denumerable.ofNat_encode, diagonalPriceDecisionCode_eval,
    diagonalPriceTruth]
  split <;> simp_all

lemma diagonalPriceTruth_re
    {P : History} (market : MarketComputation P) (p : ℚ) :
    REPred (diagonalPriceTruth market p) :=
  REPred.of_eq
    (quotePos_re (Encodable.encode (diagonalPriceDecisionCode market p)))
    (diagonalPriceQuotePos_iff market p)

/-- An FFL binary body whose second parameter is precisely the public diagonal predicate.
The first parameter is reserved for parameterized diagonalization. -/
noncomputable def diagonalPriceBody
    {P : History} (market : MarketComputation P) (p : ℚ) :
    ArithmeticSemisentence 2 :=
  (Rew.subst ![#1]) ▹
    codeOfREPred (diagonalPriceTruth market p)

lemma diagonalPriceBody_spec
    {P : History} (market : MarketComputation P) (p : ℚ) (x n : ℕ) :
    (diagonalPriceBody market p).Evalb ![x, n] ↔
      diagonalPriceTruth market p n := by
  simpa [diagonalPriceBody, Semiformula.eval_substs,
    Matrix.constant_eq_singleton] using
      (codeOfREPred_spec (diagonalPriceTruth_re market p) (x := n))

/-- The FFL parameterized fixed point represents the same predicate as the public selector.
Paper node: `thm:lp` -/
lemma diagonalPriceFixedpoint_spec
    {P : History} (market : MarketComputation P) (p : ℚ) (n : ℕ) :
    (parameterizedFixedpoint (diagonalPriceBody market p)).Evalb ![n] ↔
      diagonalPriceTruth market p n := by
  have hall := models_of_provable (M := ℕ) (T := 𝗜𝚺₁) inferInstance
    (parameterized_diagonal₁ (T := 𝗜𝚺₁) (diagonalPriceBody market p))
  have hdiag : ∀ n : ℕ,
      ((parameterizedFixedpoint (diagonalPriceBody market p)).Evalb ![n]) ↔
        ((diagonalPriceBody market p).Evalb
          ![⌜parameterizedFixedpoint (diagonalPriceBody market p)⌝, n]) := by
    simpa [models_iff, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using hall
  exact (hdiag n).trans (diagonalPriceBody_spec market p _ n)

/-- Construct the public Boolean diagonal quote from the market computation itself.
The selector is obtained by Kleene recursion, while `body` is its matching FFL
parameterized fixed point.  No caller-supplied truth relation occurs in this constructor.
Paper node: `thm:lp` -/
noncomputable def parameterizedDiagonalQuoteCodeOfMarket
    {P : History} (market : MarketComputation P) (T : ArithmeticTheory)
    [𝗥₀ ⪯ T] (p : ℚ) :
    ParameterizedDiagonalQuoteCode T (diagonalPriceTruth market p) where
  toBooleanQuoteCode := {
    code := Encodable.encode (diagonalPriceDecisionCode market p)
    pos_complete := fun n hn =>
      universalQuotePos_prov T <| by
        simpa [Nat.unpair_pair] using (diagonalPriceQuotePos_iff market p n).mpr hn
    neg_complete := fun n hn =>
      universalQuoteNeg_prov T <| by
        simpa [Nat.unpair_pair] using (diagonalPriceQuoteNeg_iff market p n).mpr hn
  }
  body := diagonalPriceBody market p
  represents_fixedpoint := diagonalPriceFixedpoint_spec market p

/-- What the `thm:lp` endpoint's sentence actually is: the quotation atom of the diagonal
selector's own code at index `n`.  A client reading
`lic_paradox_resistance_ofDiagonal`'s conclusion needs this unfolding of the otherwise
opaque `toBooleanQuoteCode.sentence` projection. -/
lemma parameterizedDiagonalQuoteCodeOfMarket_sentence
    {P : History} (market : MarketComputation P) (T : ArithmeticTheory)
    [𝗥₀ ⪯ T] (p : ℚ) (n : ℕ) :
    (parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n =
      quoteAtom
        (Nat.pair (Encodable.encode (diagonalPriceDecisionCode market p)) n) :=
  rfl

/-- The diagonal predicate, restated at the inherited public atom and in the real-valued
market price the endpoints use.  This is the primitive fact; the fixed-point form below is
it composed with the representation. -/
lemma parameterizedDiagonalQuoteCodeOfMarket_public_price_iff
    {P : History} (market : MarketComputation P) (T : ArithmeticTheory)
    [𝗥₀ ⪯ T] (p : ℚ) (n : ℕ) :
    diagonalPriceTruth market p n ↔
      P n
        ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n) <
          (p : ℝ) := by
  rw [market.quote_exact]
  change market.quote n
      (Encodable.encode
        ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n)) <
        p ↔
    (market.quote n
      (Encodable.encode
        ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n)) :
          ℝ) < (p : ℝ)
  norm_cast

/-- The constructor's represented arithmetic fixed point is exactly the same-day price
comparison for its inherited public atom.  This is the semantic link between the
arithmetic fixed point and the public atom, derived here rather than assumed.
Paper node: `thm:lp` -/
lemma parameterizedDiagonalQuoteCodeOfMarket_public_fixedpoint
    {P : History} (market : MarketComputation P) (T : ArithmeticTheory)
    [𝗥₀ ⪯ T] (p : ℚ) (n : ℕ) :
    ((parameterizedFixedpoint
          (parameterizedDiagonalQuoteCodeOfMarket market T p).body).Evalb ![n]) ↔
      P n
        ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n) <
          (p : ℝ) := by
  rw [(parameterizedDiagonalQuoteCodeOfMarket market T p).represents_fixedpoint n]
  exact parameterizedDiagonalQuoteCodeOfMarket_public_price_iff market T p n

/-! ## Paradox-resistance quotation package -/

/-- Construct paradox resistance directly from a named computable market.  The public atom,
its decision code, and its FFL fixed point are all built internally, so there is no
caller-supplied self-reference premise. -/
noncomputable def paradoxResistanceQuoteOfDiagonal
    {P : History} {DP : DeductiveProcess} {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T]
    (Q : QuotationTheoryPresentation DP T)
    (market : MarketComputation P)
    (p : ℚ) (width : ℕ → ℚ)
    (hwidthInv : DigitRatCodes (fun n ↦ 1 / width n))
    (hwidthPos : ∀ n, 0 < width n)
    (hwidthZero : Tendsto (fun n ↦ (width n : ℝ)) atTop (𝓝 0)) :
    ParadoxResistanceQuote P DP p := by
  let q := parameterizedDiagonalQuoteCodeOfMarket market T p
  let quote := q.toBooleanQuoteCode
  let price : ℕ → EF := currentPriceFeature quote.sentence
  let pFeature : ℕ → EF := AffineCombination.constantRatFeature p
  let lower : ℕ → EF := ctsIndFeature width pFeature price
  let upper : ℕ → EF := ctsIndFeature width price pFeature
  have hquote : BigSentenceCodes quote.sentence :=
    BigSentenceCodes.ofPolySentenceCodes quote.sentence_poly
  have hprice : PGenerableWeighting price :=
    currentPriceFeature_generated quote.sentence hquote
  have hpFeature : PGenerableWeighting pFeature :=
    (AffineCombination.constantRatFeature_generated P p).toWeighting
  have hlower : PGenerableWeighting lower :=
    ctsIndFeature_generated width pFeature price hwidthInv hpFeature hprice
  have hupper : PGenerableWeighting upper :=
    ctsIndFeature_generated width price pFeature hwidthInv hprice hpFeature
  have hpriceDenote (n : ℕ) : (price n).denote P =
      P n (quote.sentence n) := by
    simp [price, currentPriceFeature]
  have hpDenote (n : ℕ) : (pFeature n).denote P = (p : ℝ) := by
    simp [pFeature, AffineCombination.constantRatFeature]
  have hlowerDenote (n : ℕ) : (lower n).denote P =
      ctsInd (width n) (p : ℝ) (P n (quote.sentence n)) := by
    rw [show lower n = ctsIndFeature width pFeature price n by rfl,
      ctsIndFeature_denote width pFeature price hwidthPos P n,
      hpDenote n, hpriceDenote n]
  have hupperDenote (n : ℕ) : (upper n).denote P =
      ctsInd (width n) (P n (quote.sentence n)) (p : ℝ) := by
    rw [show upper n = ctsIndFeature width price pFeature n by rfl,
      ctsIndFeature_denote width price pFeature hwidthPos P n,
      hpriceDenote n, hpDenote n]
  refine {
    sentence := quote.sentence
    sentence_codes := hquote
    width := width
    width_pos := hwidthPos
    width_tendsto_zero := hwidthZero
    diagonal_reflected := by
      intro n v hv
      exact (quote.reflected Q n v hv).trans
        (parameterizedDiagonalQuoteCodeOfMarket_public_price_iff market T p n)
    lower_affine := ?_
    upper_affine := ?_
  }
  · simpa only [hlowerDenote] using completedGatedComplementQuote Q quote lower
      hlower 1 (by norm_num)
      (fun n ↦ by rw [hlowerDenote]; exact (ctsInd_mem_Icc _ _ _).1)
      (fun n ↦ by rw [hlowerDenote]; norm_num; exact (ctsInd_mem_Icc _ _ _).2)
      (fun n hn ↦ by
        rw [hlowerDenote]
        have hge : (p : ℝ) ≤ P n (quote.sentence n) := by
          exact le_of_not_gt (fun hlt ↦ hn
            ((parameterizedDiagonalQuoteCodeOfMarket_public_price_iff market T p n).2 hlt))
        exact ctsInd_eq_zero_of_le (width n) _ _ (hwidthPos n) hge)
      market.price_mem_Icc
  · simpa only [hupperDenote] using completedGatedAffirmativeQuote Q quote upper
      hupper 1 (by norm_num)
      (fun n ↦ by rw [hupperDenote]; exact (ctsInd_mem_Icc _ _ _).1)
      (fun n ↦ by rw [hupperDenote]; norm_num; exact (ctsInd_mem_Icc _ _ _).2)
      (fun n hn ↦ by
        rw [hupperDenote]
        exact ctsInd_eq_zero_of_le (width n) _ _ (hwidthPos n)
          (le_of_lt
            ((parameterizedDiagonalQuoteCodeOfMarket_public_price_iff market T p n).1 hn)))
      market.price_mem_Icc

/-! ## Completed-theory semantics imply deferred fixed-portfolio coherence -/

/-- Uniformly vanishing completed-theory value is enough to control the price of the
same polynomial affine portfolio on every later deferral day.  This is the missing
bridge between arithmetic quotation and `AffineQuoteEq`: affine coherence first pins
the limiting value to zero, affine persistence pins both future extrema to zero, and
the actual day-`f n` price lies between those extrema. -/
lemma CompletedAffineQuoteApprox.future_price_tendsto_zero
    {P : History} {DP : DeductiveProcess} {gap : ℕ → ℝ}
    (q : CompletedAffineQuoteApprox P DP gap) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) :
    Tendsto (fun n ↦ (q.family n).price P (f n)) atTop (𝓝 0) := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  let As : ℕ → AffineCombination := q.family
  let lv : ℕ → ℝ := fun n ↦ (As n).value P (limitingBelief P)
  have hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C :=
    ⟨1, q.magnitude_le_one⟩
  have hbdd := q.poly.completedAffineValues_bdd P DP q.bounded hmag hP
  have htheoryLow : Tendsto (completedAffineLow As P DP) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hnear := q.theory_coherent (ε / 2) (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hnear
    refine ⟨N, fun n hn ↦ ?_⟩
    have hall := hN n hn
    have hnonempty := completedAffineValues_nonempty DP (As n) P hworld
    have hlo : -(ε / 2) ≤ completedAffineLow As P DP n := by
      apply le_csInf hnonempty
      rintro x ⟨v, hv, rfl⟩
      have hx := hall v hv
      rw [abs_le] at hx
      linarith
    have hhi : completedAffineLow As P DP n ≤ ε / 2 := by
      obtain ⟨x, hx⟩ := hnonempty
      have hinf := csInf_le (hbdd n).1 hx
      rcases hx with ⟨v, hv, rfl⟩
      have hinf' : completedAffineLow As P DP n ≤
          (As n).value P v.payout := by
        exact hinf
      have hvnear := hall v hv
      rw [abs_le] at hvnear
      linarith
    rw [Real.dist_eq, _root_.sub_zero, abs_lt]
    constructor <;> linarith
  have htheoryHigh : Tendsto (completedAffineHigh As P DP) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hnear := q.theory_coherent (ε / 2) (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hnear
    refine ⟨N, fun n hn ↦ ?_⟩
    have hall := hN n hn
    have hnonempty := completedAffineValues_nonempty DP (As n) P hworld
    have hlo : -(ε / 2) ≤ completedAffineHigh As P DP n := by
      obtain ⟨x, hx⟩ := hnonempty
      have hsup := le_csSup (hbdd n).2 hx
      rcases hx with ⟨v, hv, rfl⟩
      have hsup' : (As n).value P v.payout ≤
          completedAffineHigh As P DP n := by
        exact hsup
      have hvnear := hall v hv
      rw [abs_le] at hvnear
      linarith
    have hhi : completedAffineHigh As P DP n ≤ ε / 2 := by
      apply csSup_le hnonempty
      rintro x ⟨v, hv, rfl⟩
      have hx := hall v hv
      rw [abs_le] at hx
      linarith
    rw [Real.dist_eq, _root_.sub_zero, abs_lt]
    constructor <;> linarith
  have hlimBounds :=
    AffineCombination.BoundedAffinePrices.limitingValue_filterBounds
      q.bounded DP hworld
  have hcoh := q.poly.affcoh P DP q.bounded hmag hworld
  have hlv : Tendsto lv atTop (𝓝 0) := by
    apply tendsto_of_le_liminf_of_limsup_le
    · simpa only [lv, As, htheoryLow.liminf_eq] using hcoh.1.1
    · simpa only [lv, As, htheoryHigh.limsup_eq] using hcoh.2.2
    · simpa only [lv, As] using hlimBounds.2
    · simpa only [lv, As] using hlimBounds.1
  have hper := q.poly.peraffkno P DP q.bounded hmag hworld
  obtain ⟨_htdocs, _, hhlo, hhhi, hllo, hlhi⟩ := q.bounded.filterBounds
  have hbetween : ∀ n,
      affineFutureLow As P n ≤ lv n ∧ lv n ≤ affineFutureHigh As P n := by
    intro n
    simpa only [As, lv] using
      AffineCombination.futureLow_le_limitingValue_le_futureHigh
        q.family P DP q.bounded hworld n
  have hfutureHigh : Tendsto (affineFutureHigh As P) atTop (𝓝 0) := by
    apply tendsto_of_le_liminf_of_limsup_le
    · calc
        0 = liminf lv atTop := hlv.liminf_eq.symm
        _ ≤ liminf (affineFutureHigh As P) atTop :=
          liminf_le_liminf (Eventually.of_forall fun n ↦ (hbetween n).2)
            (by simpa only [As, lv] using hlimBounds.1) hhhi.isCobounded_flip
    · simpa only [As, lv, hlv.limsup_eq] using hper.2.le
    · simpa only [As] using hhhi
    · simpa only [As] using hhlo
  have hfutureLow : Tendsto (affineFutureLow As P) atTop (𝓝 0) := by
    apply tendsto_of_le_liminf_of_limsup_le
    · simpa only [As, lv, hlv.liminf_eq] using hper.1.ge
    · calc
        limsup (affineFutureLow As P) atTop ≤ limsup lv atTop :=
          limsup_le_limsup (Eventually.of_forall fun n ↦ (hbetween n).1)
            hllo.isCobounded_flip (by simpa only [As, lv] using hlimBounds.2)
        _ = 0 := hlv.limsup_eq
    · simpa only [As] using hlhi
    · simpa only [As] using hllo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hfutureLow hfutureHigh
  · exact Eventually.of_forall fun n ↦ by
      simpa only [As] using
        AffineCombination.BoundedAffinePrices.futureLow_le_price
          q.bounded (f.lt n).le
  · exact Eventually.of_forall fun n ↦ by
      simpa only [As] using
        AffineCombination.BoundedAffinePrices.price_le_futureHigh
          q.bounded (f.lt n).le

/-! ## Concrete deferred expectation quotation -/

/-- Strict deferral tends to infinity even when it grows too quickly to be polynomial in
its source index. -/
lemma DeferralFunction.tendsto_atTop (f : DeferralFunction) :
    Tendsto f atTop atTop := by
  apply tendsto_atTop_atTop.2
  intro N
  exact ⟨N, fun n hn ↦ hn.trans (f.lt n).le⟩

/-- **The deferral clock.**  `DeferralFunction.fueled` states the polynomial fuel bound in
raw arithmetic form, while every bounded evaluator in the development is clocked by
`PrefixPatchCompile.ecClock`.  This is that bound in the `ecClock` spelling, so no consumer
— here or downstream — re-derives how to open `f.fueled`.  A deferred package that must
name the clock parameters as data opens this with `Classical.choose`, since the goal it
builds lives in `Type`. -/
lemma DeferralFunction.exists_clock (f : DeferralFunction) :
    ∃ a degree, ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k) := by
  obtain ⟨a, degree, h⟩ := f.fueled
  exact ⟨a, degree, fun k ↦ by simpa [PrefixPatchCompile.ecClock] using h k⟩

/-- Construct the complete `thm:cee` quote package.  The additional `source_valued`
premise is the explicit first-order representation fact needed to compare two threshold
mesh precisions; compact syntax alone cannot imply it. -/
noncomputable def expectedFutureExpectationQuoteOfRepresentation
    {P : History} {DP : DeductiveProcess}
    (f : DeferralFunction)
    (X Y : ℕ → LUV)
    (hX : LUV.RpnThresholdCodeSeq X) (hY : LUV.RpnThresholdCodeSeq Y)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X n) x)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Y n) ((X n).expect P (f n)))
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ExpectedFutureExpectationQuote P DP f X Y := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  have hspec := Classical.choose_spec (Classical.choose_spec f.exists_clock)
  have quote_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ y, v.ValuesAt (Y n) y := by
    intro n v hv
    exact ⟨(X n).expect P (f n), reflected n v hv⟩
  have hHmem : ∀ z, 0 ≤ (DeferralFibre.pairedExpectationFeature X z).denote P ∧
      (DeferralFibre.pairedExpectationFeature X z).denote P ≤ 1 := by
    intro z
    obtain ⟨m, k, rfl⟩ : ∃ m k, z = Nat.pair m k := ⟨z.unpair.1, z.unpair.2, by simp⟩
    rw [DeferralFibre.pairedExpectationFeature_denote]
    exact (X k).expect_mem_Icc P m (hP m)
  have hhigh0 : Tendsto (fun n ↦ (X n).expect P (f n) - (Y n).expect P (f n))
      atTop (𝓝 0) := by
    have h := DeferralFibre.numericQuote_deferred_tendsto_zero hworld f hspec
      (DeferralFibre.pairedExpectationFeature X)
      (DeferralFibre.pairedExpectationFeature_paired X hX.toBig) hHmem Y hY
      (fun m k hfk v hv ↦ by
        rw [DeferralFibre.pairedExpectationFeature_denote, ← hfk]
        exact reflected k v hv) hP
    refine Tendsto.congr' (Eventually.of_forall fun n ↦ ?_) h
    rw [DeferralFibre.pairedExpectationFeature_denote]
    rfl
  have hcrossX0 := DeferralFibre.crossPrecision_deferred_tendsto_zero hworld f hspec
    X hX.toBig source_valued hP
  have hcrossY0 := DeferralFibre.crossPrecision_deferred_tendsto_zero hworld f hspec
    Y hY.toBig quote_valued hP
  let raw := LUV.expectDifferenceAffine X Y
  let family : ℕ → AffineCombination := fun n ↦
    (raw n).scale (EF.const (1 / 2))
  let hraw := LUV.expectDifferenceAffine_polySequence X Y hX hY
  let hfamily := hraw.scaleRat (1 / 2)
  refine {
    source_codes := hX
    quote_codes := hY
    reflected := reflected
    affine := {
      family := family
      poly := hfamily
      scale := 1 / 2
      scale_pos := by norm_num
      current_price := by
        intro n
        simp only [family, raw, AffineCombination.scale_price, EF.denote_const,
          LUV.expectDifferenceAffine_priceAt, LUV.expect]
      bounded := by
        refine ⟨1, zero_le_one, fun n m ↦ ?_⟩
        simp only [family, raw, AffineCombination.scale_price, EF.denote_const,
          LUV.expectDifferenceAffine_priceAt]
        have hX0 := (X n).expectApprox_nonneg (P m) (n + 1) (fun s ↦ (hP m s).1)
        have hX1 := (X n).expectApprox_le_one (P m) (n + 1) (fun s ↦ (hP m s).2)
        have hY0 := (Y n).expectApprox_nonneg (P m) (n + 1) (fun s ↦ (hP m s).1)
        have hY1 := (Y n).expectApprox_le_one (P m) (n + 1) (fun s ↦ (hP m s).2)
        rw [abs_le]
        constructor <;> norm_num <;> linarith
      magnitude_le_one := by
        intro n
        simp only [family, AffineCombination.scale_magnitude, EF.denote_const]
        norm_num
        linarith [LUV.expectDifferenceAffine_magnitude_le_two X Y P n]
      future_coherent := by
        have hcombined : Tendsto (fun n ↦ (1 / 2 : ℝ) *
            (((X n).expect P (f n) - (Y n).expect P (f n)) +
              ((X n).expectApprox (P (f n)) (n + 1) -
                (X n).expectApprox (P (f n)) (f n + 1)) -
              ((Y n).expectApprox (P (f n)) (n + 1) -
                (Y n).expectApprox (P (f n)) (f n + 1)))) atTop (𝓝 0) := by
          simpa using ((hhigh0.add hcrossX0).sub hcrossY0).const_mul (1 / 2 : ℝ)
        show Tendsto (fun n ↦ (family n).price P (f n) - 0) atTop (𝓝 0)
        apply Tendsto.congr' _ hcombined
        exact Eventually.of_forall fun n ↦ by
          simp only [family, raw, AffineCombination.scale_price,
            EF.denote_const, LUV.expectDifferenceAffine_priceAt,
            Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, LUV.expect,
            _root_.sub_zero]
          ring
    }
  }

/-- Construct the complete `thm:ceu` future-price quote package. -/
noncomputable def futurePriceQuoteOfRepresentation
    {P : History} {DP : DeductiveProcess}
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (Y : ℕ → LUV)
    (hφ : BigSentenceCodes φ) (hY : LUV.RpnThresholdCodeSeq Y)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Y n) (P (f n) (φ n)))
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    FuturePriceQuote P DP f φ Y := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  have hspec := Classical.choose_spec (Classical.choose_spec f.exists_clock)
  have quote_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ y, v.ValuesAt (Y n) y := by
    intro n v hv
    exact ⟨P (f n) (φ n), reflected n v hv⟩
  have hHmem : ∀ z, 0 ≤ (DeferralFibre.pairedPriceFeature φ z).denote P ∧
      (DeferralFibre.pairedPriceFeature φ z).denote P ≤ 1 := by
    intro z
    obtain ⟨m, k, rfl⟩ : ∃ m k, z = Nat.pair m k := ⟨z.unpair.1, z.unpair.2, by simp⟩
    rw [DeferralFibre.pairedPriceFeature_denote]
    exact hP m (φ k)
  have hhigh0 : Tendsto (fun n ↦ P (f n) (φ n) - (Y n).expect P (f n))
      atTop (𝓝 0) := by
    have h := DeferralFibre.numericQuote_deferred_tendsto_zero hworld f hspec
      (DeferralFibre.pairedPriceFeature φ)
      (DeferralFibre.pairedPriceFeature_paired φ hφ) hHmem Y hY
      (fun m k hfk v hv ↦ by
        rw [DeferralFibre.pairedPriceFeature_denote, ← hfk]
        exact reflected k v hv) hP
    refine Tendsto.congr' (Eventually.of_forall fun n ↦ ?_) h
    rw [DeferralFibre.pairedPriceFeature_denote]
    rfl
  have hcrossY0 := DeferralFibre.crossPrecision_deferred_tendsto_zero hworld f hspec
    Y hY.toBig quote_valued hP
  let sentenceFamily := AffineCombination.sentenceAffine φ
  let quoteFamily := LUV.expectAffineSeq Y
  let raw : ℕ → AffineCombination := fun n ↦
    (sentenceFamily n).add (quoteFamily n).neg
  let hsentence := AffineCombination.sentenceAffine_polySequence φ hφ
  let hquote := LUV.expectAffineSeq_polySequence Y hY.toBig
  let hraw := hsentence.add hquote.neg
  let family : ℕ → AffineCombination := fun n ↦
    (raw n).scale (EF.const (1 / 2))
  let hfamily := hraw.scaleRat (1 / 2)
  refine {
    sentence_codes := hφ
    quote_codes := hY
    reflected := reflected
    affine := {
      family := family
      poly := hfamily
      scale := 1 / 2
      scale_pos := by norm_num
      current_price := by
        intro n
        simp only [family, raw, sentenceFamily, quoteFamily,
          AffineCombination.scale_price, EF.denote_const,
          AffineCombination.add_price, AffineCombination.neg_price,
          AffineCombination.sentenceAffine_price, LUV.expectAffineSeq_price]
        ring
      bounded := by
        refine ⟨1, zero_le_one, fun n m ↦ ?_⟩
        simp only [family, raw, sentenceFamily, quoteFamily,
          AffineCombination.scale_price, EF.denote_const,
          AffineCombination.add_price, AffineCombination.neg_price,
          AffineCombination.sentenceAffine_price, LUV.expectAffineSeq,
          LUV.expectAffine_priceAt]
        have hY0 := (Y n).expectApprox_nonneg (P m) (n + 1) (fun s ↦ (hP m s).1)
        have hY1 := (Y n).expectApprox_le_one (P m) (n + 1) (fun s ↦ (hP m s).2)
        rw [abs_le]
        constructor <;> norm_num <;> linarith [(hP m (φ n)).1, (hP m (φ n)).2]
      magnitude_le_one := by
        intro n
        simp only [family, raw, sentenceFamily, quoteFamily,
          AffineCombination.scale_magnitude, EF.denote_const,
          AffineCombination.add_magnitude, AffineCombination.neg_magnitude,
          AffineCombination.sentenceAffine_magnitude]
        norm_num
        linarith [LUV.expectAffineSeq_magnitude_le_one Y P n]
      future_coherent := by
        have hcombined : Tendsto (fun n ↦ (1 / 2 : ℝ) *
            ((P (f n) (φ n) - (Y n).expect P (f n)) -
              ((Y n).expectApprox (P (f n)) (n + 1) -
                (Y n).expectApprox (P (f n)) (f n + 1)))) atTop (𝓝 0) := by
          simpa using (hhigh0.sub hcrossY0).const_mul (1 / 2 : ℝ)
        show Tendsto (fun n ↦ (family n).price P (f n) - 0) atTop (𝓝 0)
        apply Tendsto.congr' _ hcombined
        exact Eventually.of_forall fun n ↦ by
          simp only [family, raw, sentenceFamily, quoteFamily,
            AffineCombination.scale_price, EF.denote_const,
            AffineCombination.add_price, AffineCombination.neg_price,
            AffineCombination.sentenceAffine_price, LUV.expectAffineSeq,
            LUV.expectAffine_priceAt,
            Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, LUV.expect,
            _root_.sub_zero]
          ring
    }
  }

/-- Construct the complete `thm:ccee` conditional-expectation quote package.  The left
product is reflected only to within the vanishing `slack` (disclosed type-`(c)`; see
`ConditionalExpectationQuote`); `slack = 0` recovers exact reflection. -/
noncomputable def conditionalExpectationQuoteOfRepresentation
    {P : History} {DP : DeductiveProcess}
    (f : DeferralFunction)
    (X Z Z' : ℕ → LUV) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat P w)
    (hX : LUV.RpnThresholdCodeSeq X)
    (hZ : LUV.RpnThresholdCodeSeq Z)
    (hZ' : LUV.RpnThresholdCodeSeq Z')
    (slack : ℕ → ℝ) (slack_tendsto : Tendsto slack atTop (𝓝 0))
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X n) x)
    (left_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ x, v.ValuesAt (X n) x →
        ∃ z, v.ValuesAt (Z n) z ∧ |z - x * w (f n)| ≤ slack n)
    (right_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Z' n) ((X n).expect P (f n) * w (f n)))
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConditionalExpectationQuote P DP f X Z Z' w := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  have hspec := Classical.choose_spec (Classical.choose_spec f.exists_clock)
  let W := Classical.choose weight_generable
  let hWgen := Classical.choose_spec weight_generable
  let hW := hWgen.toWeighting
  have hsemantic : ∀ m k, f k = m → ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∃ x z, v.ValuesAt (X k) x ∧ v.ValuesAt (Z k) z ∧ |z - x * w m| ≤ slack k ∧
        v.ValuesAt (Z' k) ((X k).expect P m * w m) := by
    intro m k hfk v hv
    subst hfk
    obtain ⟨x, hx⟩ := source_valued k v hv
    obtain ⟨z, hz, hzs⟩ := left_reflected k v hv x hx
    exact ⟨x, z, hx, hz, hzs, right_reflected k v hv⟩
  have Zvalued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ z, v.ValuesAt (Z n) z := by
    intro n v hv
    obtain ⟨x, hx⟩ := source_valued n v hv
    obtain ⟨z, hz, -⟩ := left_reflected n v hv x hx
    exact ⟨z, hz⟩
  have Z'valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ z, v.ValuesAt (Z' n) z := by
    intro n v hv
    exact ⟨(X n).expect P (f n) * w (f n), right_reflected n v hv⟩
  have hhigh0 := DeferralFibre.conditional_deferred_tendsto_zero hworld f hspec
    X Z Z' hX hZ hZ' w W hW hWgen.denote weight_mem slack slack_tendsto hsemantic hP
  have hcrossZ0 := DeferralFibre.crossPrecision_deferred_tendsto_zero hworld f hspec
    Z hZ.toBig Zvalued hP
  have hcrossZ'0 := DeferralFibre.crossPrecision_deferred_tendsto_zero hworld f hspec
    Z' hZ'.toBig Z'valued hP
  let raw := LUV.expectDifferenceAffine Z Z'
  let family : ℕ → AffineCombination := fun n ↦
    (raw n).scale (EF.const (1 / 2))
  let hraw := LUV.expectDifferenceAffine_polySequence Z Z' hZ hZ'
  let hfamily := hraw.scaleRat (1 / 2)
  refine {
    weight_mem := weight_mem
    weight_generable := weight_generable
    source_codes := hX
    left_codes := hZ
    right_codes := hZ'
    slack := slack
    slack_tendsto := slack_tendsto
    source_valued := source_valued
    left_reflected := left_reflected
    right_reflected := right_reflected
    affine := {
      family := family
      poly := hfamily
      scale := 1 / 2
      scale_pos := by norm_num
      current_price := by
        intro n
        simp only [family, raw, AffineCombination.scale_price, EF.denote_const,
          LUV.expectDifferenceAffine_priceAt, LUV.expect]
      bounded := by
        refine ⟨1, zero_le_one, fun n m ↦ ?_⟩
        simp only [family, raw, AffineCombination.scale_price, EF.denote_const,
          LUV.expectDifferenceAffine_priceAt]
        have hZ0 := (Z n).expectApprox_nonneg (P m) (n + 1) (fun s ↦ (hP m s).1)
        have hZ1 := (Z n).expectApprox_le_one (P m) (n + 1) (fun s ↦ (hP m s).2)
        have hZ'0 := (Z' n).expectApprox_nonneg (P m) (n + 1) (fun s ↦ (hP m s).1)
        have hZ'1 := (Z' n).expectApprox_le_one (P m) (n + 1) (fun s ↦ (hP m s).2)
        rw [abs_le]
        constructor <;> norm_num <;> linarith
      magnitude_le_one := by
        intro n
        simp only [family, AffineCombination.scale_magnitude, EF.denote_const]
        norm_num
        linarith [LUV.expectDifferenceAffine_magnitude_le_two Z Z' P n]
      future_coherent := by
        have hcombined : Tendsto (fun n ↦ (1 / 2 : ℝ) *
            (((Z n).expect P (f n) - (Z' n).expect P (f n) +
                ((Z n).expectApprox (P (f n)) (n + 1) -
                  (Z n).expectApprox (P (f n)) (f n + 1))) -
              ((Z' n).expectApprox (P (f n)) (n + 1) -
                (Z' n).expectApprox (P (f n)) (f n + 1)))) atTop (𝓝 0) := by
          simpa using ((hhigh0.add hcrossZ0).sub hcrossZ'0).const_mul (1 / 2 : ℝ)
        show Tendsto (fun n ↦ (family n).price P (f n) - 0) atTop (𝓝 0)
        apply Tendsto.congr' _ hcombined
        exact Eventually.of_forall fun n ↦ by
          simp only [family, raw, AffineCombination.scale_price,
            EF.denote_const, LUV.expectDifferenceAffine_priceAt,
            Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, LUV.expect,
            _root_.sub_zero]
          ring
    }
  }

/-! ### Complete deferred self-trust package -/

/-- Construct the complete `thm:st` self-trust package.  The constructor asks of the
deferral function only what `def:deferralfunc` does — `f n > n` plus poly-clocked
emission; no injectivity, no monotonicity.

The confidence threshold enters as a P-generable feature `pFeature` (`def:ece`), so the
trader may scale by a threshold that varies with the market's own prices: the emitted
portfolio carries the *expression* `pFeature n`, never a day-`n` numeral for `p n`.  The
deferred gate is a *paired-index* family: at `z = ⟨m,k⟩` it reads the day-`m` price of
`φ k` against the confidence data at the clamped source index `min k m`, which keeps the
emitted expression legal on day `m` while agreeing with the source index `k` on the
fibre, where `k < f k = m`. -/
noncomputable def selfTrustQuoteOfRepresentation
    {P : History} {DP : DeductiveProcess}
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (δ p : ℕ → ℚ) (A B : ℕ → LUV)
    (delta_pos : ∀ n, 0 < δ n)
    (probability_mem : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hφ : BigSentenceCodes φ)
    (hδinv : DigitRatCodes (fun n ↦ 1 / δ n))
    (pFeature : ℕ → EF) (hp : GeneratedRatFeature P p pFeature)
    (hA : LUV.BigThresholdCodeSeq A)
    (hB : LUV.BigThresholdCodeSeq B)
    (confidence_reflected : ∀ n (v : PCWorld),
      v.ConsistentWithTheory DP →
        v.ValuesAt (B n) (ctsInd (δ n) (P (f n) (φ n)) (p n)))
    (product_reflected : ∀ n (v : PCWorld),
      v.ConsistentWithTheory DP →
        v.ValuesAt (A n)
          (v.payout (φ n) * ctsInd (δ n) (P (f n) (φ n)) (p n)))
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    SelfTrustQuote P DP f φ δ p A B := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  have hspec := Classical.choose_spec (Classical.choose_spec f.exists_clock)
  let δp : ℕ → ℚ := fun z ↦ δ (min z.unpair.2 z.unpair.1)
  have hδpInv : DigitRatCodes (fun z ↦ 1 / δp z) :=
    hδinv.comp (Classical.choose_spec PairedWeighting.clampedSource_polyFueled)
  have hδpPos : ∀ z, 0 < δp z := fun z ↦ delta_pos _
  let pF : ℕ → EF := fun z ↦ pFeature (min z.unpair.2 z.unpair.1)
  have hpF : PairedWeighting pF :=
    PairedWeighting.ofPGenerableClamped hp.toWeighting
  have hpFdenote : ∀ z, (pF z).denote P = (p (min z.unpair.2 z.unpair.1) : ℝ) :=
    fun z ↦ hp.denote _
  have hpFmem : ∀ z, 0 ≤ (pF z).denote P ∧ (pF z).denote P ≤ 1 := by
    intro z
    rw [hpFdenote]
    exact ⟨by exact_mod_cast (probability_mem _).1,
      by exact_mod_cast (probability_mem _).2⟩
  have hpDenote : ∀ m k, k ≤ m → (pF (Nat.pair m k)).denote P = (p k : ℝ) := by
    intro m k hk
    rw [hpFdenote]
    simp [min_eq_left hk]
  let G : ℕ → EF := ctsIndFeature δp (DeferralFibre.pairedPriceFeature φ) pF
  have hG : PairedWeighting G :=
    PairedWeighting.ctsInd hδpInv (DeferralFibre.pairedPriceFeature_paired φ hφ) hpF
  have hGdenote : ∀ m k, k ≤ m → (G (Nat.pair m k)).denote P =
      ctsInd (δ k) (P m (φ k)) (p k) := by
    intro m k hk
    rw [show G (Nat.pair m k) = ctsIndFeature δp (DeferralFibre.pairedPriceFeature φ) pF
        (Nat.pair m k) from rfl,
      ctsIndFeature_denote δp (DeferralFibre.pairedPriceFeature φ) pF hδpPos P (Nat.pair m k),
      DeferralFibre.pairedPriceFeature_denote, hpDenote m k hk]
    simp [δp, min_eq_left hk]
  have hGmem : ∀ z, 0 ≤ (G z).denote P ∧ (G z).denote P ≤ 1 := by
    intro z
    rw [show G z = ctsIndFeature δp (DeferralFibre.pairedPriceFeature φ) pF z from rfl,
      ctsIndFeature_denote δp (DeferralFibre.pairedPriceFeature φ) pF hδpPos P z]
    exact ctsInd_mem_Icc _ _ _
  have hsemantic : ∀ m k, f k = m → ∀ v : PCWorld, v.ConsistentWithTheory DP →
      v.ValuesAt (B k) ((G (Nat.pair m k)).denote P) ∧
        v.ValuesAt (A k) (v.payout (φ k) * (G (Nat.pair m k)).denote P) := by
    intro m k hfk v hv
    have hk : k ≤ m := hfk ▸ (f.lt k).le
    rw [hGdenote m k hk, ← hfk]
    exact ⟨confidence_reflected k v hv, product_reflected k v hv⟩
  have Avalued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (A n) x := fun n v hv ↦
    ⟨_, product_reflected n v hv⟩
  have Bvalued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (B n) x := fun n v hv ↦
    ⟨_, confidence_reflected n v hv⟩
  let highGap : ℕ → ℝ := fun n ↦
    (A n).expect P (f n) - (p n : ℝ) * (B n).expect P (f n) -
      ctsInd (δ n) (P (f n) (φ n)) (p n) * (P (f n) (φ n) - (p n : ℝ))
  let crossAGap : ℕ → ℝ := fun n ↦
    (A n).expectApprox (P (f n)) (n + 1) - (A n).expect P (f n)
  let crossBGap : ℕ → ℝ := fun n ↦
    (B n).expectApprox (P (f n)) (n + 1) - (B n).expect P (f n)
  have hhigh0 : Tendsto highGap atTop (𝓝 0) := by
    have hkey := DeferralFibre.selfTrust_deferred_tendsto_zero
      (P := P) (DP := DP) hworld f hspec φ hφ p probability_mem pF hpF hpFmem
      hpDenote G hG hGmem A B hA hB hsemantic hP
    refine Tendsto.congr' (Eventually.of_forall fun n ↦ ?_) hkey
    rw [hGdenote (f n) n (f.lt n).le]
  have hcrossA0 : Tendsto crossAGap atTop (𝓝 0) := by
    simpa only [crossAGap, LUV.expect] using
      DeferralFibre.crossPrecision_deferred_tendsto_zero hworld f hspec A hA
        Avalued hP
  have hcrossB0 : Tendsto crossBGap atTop (𝓝 0) := by
    simpa only [crossBGap, LUV.expect] using
      DeferralFibre.crossPrecision_deferred_tendsto_zero hworld f hspec B hB
        Bvalued hP
  have hpCrossB0 : Tendsto (fun n ↦ (p n : ℝ) * crossBGap n) atTop (𝓝 0) := by
    apply bdd_le_mul_tendsto_zero (b := (0 : ℝ)) (B := (1 : ℝ))
    · exact Eventually.of_forall fun n ↦ by
        exact_mod_cast (probability_mem n).1
    · exact Eventually.of_forall fun n ↦ by
        exact_mod_cast (probability_mem n).2
    · exact hcrossB0
  let combined : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) *
    (highGap n + crossAGap n - (p n : ℝ) * crossBGap n)
  have hcombined0 : Tendsto combined atTop (𝓝 0) := by
    simpa [combined] using
      ((hhigh0.add hcrossA0).sub hpCrossB0).const_mul (1 / 2 : ℝ)
  let pOrig : ℕ → EF := pFeature
  let hpOrig : PGenerableWeighting pOrig := hp.toWeighting
  let pNeg : ℕ → EF := fun n ↦ EF.mul (EF.const (-1)) (pOrig n)
  have hpNeg : PGenerableWeighting pNeg := {
    polySeg := BigSpliceStream.serialize_mul
      (BigSpliceStream.serialize_const (-1))
      hpOrig.polySeg
    rank_le := by intro n; simp [pNeg, EF.rank, hpOrig.rank_le n]
    closed := by intro n ρ V; simp [pNeg, EF.denoteWith, hpOrig.closed n ρ V]
  }
  let AA := LUV.expectAffineSeq A
  let AB := LUV.expectAffineSeq B
  let raw : ℕ → AffineCombination := fun n ↦ (AA n).add ((AB n).scale (pNeg n))
  let hraw := (LUV.expectAffineSeq_polySequence A hA).add
    ((LUV.expectAffineSeq_polySequence B hB).scaleFeature pNeg hpNeg)
  let family : ℕ → AffineCombination := fun n ↦
    (raw n).scale (EF.const (1 / 2))
  let hfamily := hraw.scaleRat (1 / 2)
  refine {
    delta_pos := delta_pos
    probability_mem := probability_mem
    sentence_codes := hφ
    probability_generable := ⟨pFeature, hp⟩
    product_codes := hA
    confidence_codes := hB
    confidence_reflected := confidence_reflected
    product_reflected := product_reflected
    affine := {
      family := family
      poly := hfamily
      scale := 1 / 2
      scale_pos := by norm_num
      current_price := by
        intro n
        simp only [family, raw, AA, AB, pNeg, pOrig,
          AffineCombination.scale_price, AffineCombination.add_price,
          LUV.expectAffineSeq_price, EF.denote_mul, EF.denote_const,
          hp.denote, Pi.mul_apply]
        push_cast
        ring
      bounded := by
        refine ⟨1, zero_le_one, fun n m ↦ ?_⟩
        simp only [family, raw, AA, AB, pNeg, pOrig,
          AffineCombination.scale_price, AffineCombination.add_price,
          LUV.expectAffineSeq, LUV.expectAffine_priceAt, EF.denote_mul,
          EF.denote_const, hp.denote, Pi.mul_apply]
        push_cast
        have hA0 := (A n).expectApprox_nonneg (P m) (n + 1) (fun s ↦ (hP m s).1)
        have hA1 := (A n).expectApprox_le_one (P m) (n + 1) (fun s ↦ (hP m s).2)
        have hB0 := (B n).expectApprox_nonneg (P m) (n + 1) (fun s ↦ (hP m s).1)
        have hB1 := (B n).expectApprox_le_one (P m) (n + 1) (fun s ↦ (hP m s).2)
        have hp0 : (0 : ℝ) ≤ p n := by exact_mod_cast (probability_mem n).1
        have hp1 : (p n : ℝ) ≤ 1 := by exact_mod_cast (probability_mem n).2
        rw [abs_le]
        constructor <;> nlinarith
      magnitude_le_one := by
        intro n
        simp only [family, raw, AA, AB, pNeg, pOrig,
          AffineCombination.scale_magnitude, AffineCombination.add_magnitude,
          LUV.expectAffineSeq, EF.denote_const, EF.denote_mul,
          hp.denote, Pi.mul_apply, Rat.cast_neg, Rat.cast_one, neg_mul,
          one_mul, abs_neg]
        have hAm := (A n).expectAffine_magnitude_le_one P (n + 1)
        have hBm := (B n).expectAffine_magnitude_le_one P (n + 1)
        have hpabs : |(p n : ℝ)| ≤ 1 := by
          rw [abs_of_nonneg (by exact_mod_cast (probability_mem n).1)]
          exact_mod_cast (probability_mem n).2
        have hpB : |(p n : ℝ)| * ((B n).expectAffine (n + 1)).magnitude P ≤ 1 := by
          exact (mul_le_mul hpabs hBm (((B n).expectAffine (n + 1)).magnitude_nonneg P)
            (by norm_num)).trans_eq (one_mul 1)
        norm_num
        linarith
      future_coherent := by
        intro ε hε
        have hnear := asympEq_iff_eventuallyWithin.1
          (show AsympEq combined (fun _ ↦ 0) by
            simpa only [AsympEq, _root_.sub_zero] using hcombined0)
          ε hε
        filter_upwards [hnear] with n hn
        simp only [_root_.sub_zero] at hn
        have hlower : -ε ≤ combined n := (abs_le.mp hn).1
        have hcorr : 0 ≤ ctsInd (δ n) (P (f n) (φ n)) (p n) *
            (P (f n) (φ n) - (p n : ℝ)) := by
          by_cases hle : P (f n) (φ n) ≤ (p n : ℝ)
          · rw [ctsInd_eq_zero_of_le (δ n) _ _ (delta_pos n) hle]
            simp
          · have hdiff : 0 ≤ P (f n) (φ n) - (p n : ℝ) := by
              linarith [lt_of_not_ge hle]
            exact mul_nonneg (ctsInd_mem_Icc _ _ _).1 hdiff
        have hidentity : (family n).price P (f n) =
            combined n + (1 / 2 : ℝ) *
              (ctsInd (δ n) (P (f n) (φ n)) (p n) *
                (P (f n) (φ n) - (p n : ℝ))) := by
          simp only [family, raw, AA, AB, pNeg, pOrig,
            AffineCombination.scale_price, AffineCombination.add_price,
            LUV.expectAffineSeq, LUV.expectAffine_priceAt, EF.denote_mul,
            EF.denote_const, hp.denote, Pi.mul_apply, combined,
            highGap, crossAGap, crossBGap, LUV.expect]
          push_cast
          ring
        rw [hidentity]
        nlinarith
    }
  }

/-! ## Direct deferred consumers -/

/-- Paper-facing `thm:cee` entry point from completed-world representation data.
Paper node: `thm:cee` -/
theorem lic_expected_future_expectations_ofRepresentation
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (f : DeferralFunction)
    (X Y : ℕ → LUV)
    (hX : LUV.RpnThresholdCodeSeq X) (hY : LUV.RpnThresholdCodeSeq Y)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X n) x)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Y n) ((X n).expect P (f n)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n ↦ (X n).expect P n) ≈ₙ fun n ↦ (Y n).expect P n :=
  lic_expected_future_expectations P DP f X Y hworld
    (expectedFutureExpectationQuoteOfRepresentation f X Y hX hY
      source_valued reflected hworld)

/-- Paper-facing `thm:ceu` entry point from completed-world representation data.
Paper node: `thm:ceu` -/
theorem lic_no_expected_net_update_ofRepresentation
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (Y : ℕ → LUV)
    (hφ : BigSentenceCodes φ) (hY : LUV.RpnThresholdCodeSeq Y)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Y n) (P (f n) (φ n)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n ↦ P n (φ n)) ≈ₙ fun n ↦ (Y n).expect P n :=
  lic_no_expected_net_update P DP f φ Y hworld
    (futurePriceQuoteOfRepresentation f φ Y hφ hY reflected hworld)

/-- Paper-facing `thm:ccee` entry point from completed-world product representations.
The left quoted product need only reflect `x · w (f n)` to within the vanishing `slack`
(disclosed type-`(c)`; see `ConditionalExpectationQuote`).
Paper node: `thm:ccee` -/
theorem lic_no_expected_net_update_conditional_ofRepresentation
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (f : DeferralFunction)
    (X Z Z' : ℕ → LUV) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat P w)
    (hX : LUV.RpnThresholdCodeSeq X)
    (hZ : LUV.RpnThresholdCodeSeq Z)
    (hZ' : LUV.RpnThresholdCodeSeq Z')
    (slack : ℕ → ℝ) (slack_tendsto : Tendsto slack atTop (𝓝 0))
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X n) x)
    (left_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ x, v.ValuesAt (X n) x →
        ∃ z, v.ValuesAt (Z n) z ∧ |z - x * w (f n)| ≤ slack n)
    (right_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Z' n) ((X n).expect P (f n) * w (f n)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n ↦ (Z n).expect P n) ≈ₙ fun n ↦ (Z' n).expect P n :=
  lic_no_expected_net_update_conditional P DP f X Z Z' w hworld
    (conditionalExpectationQuoteOfRepresentation f X Z Z' w
      weight_mem weight_generable hX hZ hZ' slack slack_tendsto
      source_valued left_reflected right_reflected hworld)

/-- Paper-facing `thm:st` entry point from completed-world confidence/product
representations.  The confidence threshold `p` is P-generable (`def:ece`), presented by its
feature expression, exactly as in the paper's `thm:st`.
Paper node: `thm:st` -/
theorem lic_self_trust_ofRepresentation
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (δ p : ℕ → ℚ) (A B : ℕ → LUV)
    (delta_pos : ∀ n, 0 < δ n)
    (probability_mem : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hφ : BigSentenceCodes φ) (hδ : DigitRatCodes δ)
    (pFeature : ℕ → EF) (hp : GeneratedRatFeature P p pFeature)
    (hA : LUV.BigThresholdCodeSeq A)
    (hB : LUV.BigThresholdCodeSeq B)
    (confidence_reflected : ∀ n (v : PCWorld),
      v.ConsistentWithTheory DP →
        v.ValuesAt (B n) (ctsInd (δ n) (P (f n) (φ n)) (p n)))
    (product_reflected : ∀ n (v : PCWorld),
      v.ConsistentWithTheory DP →
        v.ValuesAt (A n)
          (v.payout (φ n) * ctsInd (δ n) (P (f n) (φ n)) (p n)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n ↦ (A n).expect P n) ≳ₙ
      fun n ↦ (p n : ℝ) * (B n).expect P n :=
  lic_self_trust P DP f φ δ p A B hworld
    (selfTrustQuoteOfRepresentation f φ δ p A B delta_pos
      probability_mem hφ (hδ.inv_of_pos delta_pos) pFeature hp hA hB
      confidence_reflected product_reflected hworld)

/-! ## Direct same-day consumers -/

/-- Paper-facing `thm:epr` entry point from concrete arithmetic quotation code.
Paper node: `thm:epr` -/
theorem lic_expectations_of_probabilities_ofCode
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    (Q : QuotationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    {value : ℕ → ℚ} (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, P n (φ n) = (value n : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (φ n)) ≈ₙ fun n => (q.luv n).expect P n :=
  lic_expectations_of_probabilities P DP φ q.luv hworld
    (currentPriceExpectationQuoteOfCode Q φ hφ q hexact
      (fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s))

/-- Paper-facing `thm:er` entry point from concrete arithmetic quotation code.
Paper node: `thm:er` -/
theorem lic_iterated_expectations_ofCode
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    (Q : QuotationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    {value : ℕ → ℚ} (X : ℕ → LUV)
    (hX : LUV.RpnThresholdCodeSeq X)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, (X n).expect P n = (value n : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (X n).expect P n) ≈ₙ fun n => (q.luv n).expect P n :=
  lic_iterated_expectations P DP X q.luv hworld
    (currentExpectationQuoteOfCode Q X hX q hexact
      (fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s))

/-- Paper-facing `thm:ref` entry point from generated endpoint features and the
arithmetically reflected interval decision.
Paper node: `thm:ref` -/
theorem lic_introspection_ofCode
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    (Q : QuotationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (a b δ : ℕ → ℚ)
    (lowerFeature : ℕ → EF)
    (hlower : GeneratedRatFeature P a lowerFeature)
    (upperFeature : ℕ → EF)
    (hupper : GeneratedRatFeature P b upperFeature)
    (hδ : DigitRatCodes δ)
    (hδpos : ∀ n, 0 < δ n)
    (hδzero : Tendsto (fun n ↦ (δ n : ℝ)) atTop (𝓝 0))
    (hab : ∀ n, 0 ≤ a n ∧ a n ≤ 1 ∧ 0 ≤ b n ∧ b n ≤ 1)
    (q : BooleanQuoteCode T (fun n ↦
      (a n : ℝ) < P n (φ n) ∧ P n (φ n) < (b n : ℝ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ ε : ℕ → ℚ,
      (∀ n, 0 < ε n) ∧
      Tendsto (fun n ↦ (ε n : ℝ)) atTop (𝓝 0) ∧
      ∀ n,
        (((a n : ℝ) + δ n < P n (φ n) ∧
            P n (φ n) < (b n : ℝ) - δ n) →
          1 - (ε n : ℝ) < P n (q.sentence n)) ∧
        ((¬ ((a n : ℝ) - δ n < P n (φ n) ∧
              P n (φ n) < (b n : ℝ) + δ n)) →
          P n (q.sentence n) < (ε n : ℝ)) := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  let package := introspectionIntervalQuoteOfCode Q φ hφ a b δ
    lowerFeature hlower upperFeature hupper (hδ.inv_of_pos hδpos) hδpos hδzero hab q hP
  exact lic_introspection P DP φ a b δ package hworld

/-- Paper-facing `thm:lp` entry point.  Its genuine parameterized fixed point and public
diagonal atom are constructed from `market`; no semantic diagonal premise is accepted.
Paper node: `thm:lp` -/
theorem lic_paradox_resistance_ofDiagonal
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [𝗜𝚺₁ ⪯ T]
    (Q : QuotationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    (market : MarketComputation P)
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (width : ℕ → ℚ) (hwidth : DigitRatCodes width)
    (hwidthPos : ∀ n, 0 < width n)
    (hwidthZero : Tendsto (fun n ↦ (width n : ℝ)) atTop (𝓝 0))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n
      ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n)) ≈ₙ
      fun _ => (p : ℝ) := by
  let package := paradoxResistanceQuoteOfDiagonal Q market p width
    (hwidth.inv_of_pos hwidthPos) hwidthPos hwidthZero
  exact lic_paradox_resistance P DP p hp0 hp1 package hworld

/-! ## Positive and complementary quotation paths -/

/-- A concrete FFL-backed Boolean quote whose represented predicate is always true. -/
noncomputable def trueBooleanQuoteCode
    (T : ArithmeticTheory) [𝗥₀ ⪯ T] :
    BooleanQuoteCode T (fun _ ↦ True) :=
  BooleanQuoteCode.ofComputable (ComputablePred.const True)

/-- A concrete FFL-backed Boolean quote whose represented predicate is always false. -/
noncomputable def falseBooleanQuoteCode
    (T : ArithmeticTheory) [𝗥₀ ⪯ T] :
    BooleanQuoteCode T (fun _ ↦ False) :=
  BooleanQuoteCode.ofComputable (ComputablePred.const False)

/-- Non-vacuity: the positive arithmetic quotation schema reaches the public process as a
literal, so the `quote_positive_enters` field of `QuotationTheoryPresentation` is
inhabited by an actual quote rather than vacuously. -/
lemma quotationRepresentation_positive_path
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T]
    (Q : QuotationTheoryPresentation DP T) (n : ℕ) :
    ∃ k, (trueBooleanQuoteCode T).sentence n ∈ DP.D k := by
  let q := trueBooleanQuoteCode T
  exact Q.quote_positive_enters q.code n (q.pos_complete n trivial)

/-- Non-vacuity: the complementary arithmetic schema reaches the public process as a
negated literal, exercising the separate negative quotation path.  Together with
`quotationRepresentation_positive_path` this shows both quotation paths through
`QuotationTheoryPresentation` are inhabited. -/
lemma quotationRepresentation_negative_path
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T]
    (Q : QuotationTheoryPresentation DP T) (n : ℕ) :
    ∃ k, (∼(falseBooleanQuoteCode T).sentence n) ∈ DP.D k := by
  let q := falseBooleanQuoteCode T
  exact Q.quote_negative_refutes q.code n (q.neg_complete n not_false)

end LogicalInduction
