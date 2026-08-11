import LogicalInduction.Construction.Witnesses.ComputationSyntax
import LogicalInduction.Construction.Witnesses.FeedbackEmission
import LogicalInduction.Properties.Introspection
import Foundation.FirstOrder.Bootstrapping.FixedPoint

/-!
# Arithmetic quotation and affine-package construction

The reflection apparatus behind `thm:ref` (Introspection), `thm:lp` (Paradox Resistance),
`thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee` and `thm:st` (Self-Trust).  Each of
those theorems prices a sentence that quotes a market quantity; this file supplies the
quoted syntax together with the affine portfolios that trade on it.

The public market language is propositional, while the paper's quotation mechanism is
first-order arithmetic.  Every quoted Boolean decision is represented by a positive and a
complementary FFL arithmetic schema; the pair has one injective, polynomially emitted
propositional name.  A quoted rational value uses the same dual-schema mechanism at every
rational threshold.  Consequently a world consistent with the completed deductive theory
values the resulting LUV correctly.

`ParameterizedDiagonalQuoteCode` records an actual FFL parameterized fixed point.  For
paradox resistance, `parameterizedDiagonalQuoteCodeOfMarket` uses Kleene's second recursion
theorem to construct the public selector that prices its own atom and then represents that
same predicate with the FFL fixed point; no self-reference law is supplied by the caller.
`QuotationTheoryPresentation` is the remaining language bridge: it translates arithmetic
proofs of positive or complementary quote schemas into the corresponding public literal.
It assumes no affine portfolio, asymptotic coherence, or logical-inductor conclusion.
-/

namespace LogicalInduction

open Filter Topology
open LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## Compact public names and the proof bridge -/

/-- Injective atom payload for a dual-schema arithmetic decision at one input.  Tag `4`
keeps quotation names disjoint from the four computation-claim roles. -/
def quotationClaimCode (positive negative : ArithmeticSemisentence 1) (input : ℕ) : ℕ :=
  Nat.pair 4 (Nat.pair (Encodable.encode positive)
    (Nat.pair (Encodable.encode negative) input))

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
  let hpayload := (PolyFueled.const 4).pair
    ((PolyFueled.const (Encodable.encode positive)).pair
      ((PolyFueled.const (Encodable.encode negative)).pair hinput.code_poly))
  refine ⟨_, (((PolyFueled.const 1).pair hpayload).succ_comp).of_eq (fun _ => rfl)⟩

/-! ## Universal computable quotation predicates

Quotation is keyed by a *decidable-decision selector* `code : ℕ`, folded into the numeral
of two **fixed** universal schemas `universalQuotePos`/`universalQuoteNeg` — the same shape
the computation side uses (`ComputationSyntax`).  Two properties of the interface depend on
the schemas being fixed and complementary rather than arbitrary.

*Non-vacuity.*  An interface quantifying over independent schemas
`positive negative : ArithmeticSemisentence 1` can be instantiated at
`positive = negative = ⊤`, which forces an atom and its negation into a common stage, so
that no world is consistent with the theory.  The positive and negative fibers of one
partial-recursive computation are instead mutually exclusive by determinism, so a
provability world can believe the positive literal without ever being forced into a
contradiction.

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

lemma quotePos_re (code : ℕ) : REPred (quotePos code) :=
  repred_mem (decodedComputation_partrec code) 1
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

/-- The fixed positive universal quotation schema; the selector `code` is folded into the
numeral `⟨code, input⟩`. -/
noncomputable def universalQuotePos : ArithmeticSemisentence 1 :=
  codeOfREPred (fun z => quotePos z.unpair.1 z.unpair.2)
/-- The fixed negative universal quotation schema. -/
noncomputable def universalQuoteNeg : ArithmeticSemisentence 1 :=
  codeOfREPred (fun z => quoteNeg z.unpair.1 z.unpair.2)

lemma universalQuotePos_re : REPred (fun z : ℕ => quotePos z.unpair.1 z.unpair.2) :=
  REPred.of_eq (repred_mem universalComputation_partrec 1) (fun _ => Iff.rfl)
lemma universalQuoteNeg_re : REPred (fun z : ℕ => quoteNeg z.unpair.1 z.unpair.2) :=
  REPred.of_eq (repred_mem universalComputation_partrec 0) (fun _ => Iff.rfl)

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
  theory_sigmaOne : 𝗜𝚺₁ ⪯ T
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

noncomputable def sentence {T : ArithmeticTheory} {truth : ℕ → Prop}
    (q : BooleanQuoteCode T truth) (n : ℕ) : Sentence :=
  quoteAtom (Nat.pair q.code n)

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
noncomputable def ofComputable {T : ArithmeticTheory} [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
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
  · refine (re_complete (T := T) universalQuotePos_re (x := Nat.pair (Encodable.encode c) input)).mp ?_
    simpa [Nat.unpair_pair] using (hpos input).mpr htrue
  · refine (re_complete (T := T) universalQuoteNeg_re (x := Nat.pair (Encodable.encode c) input)).mp ?_
    simpa [Nat.unpair_pair] using (hneg input).mpr hfalse

end BooleanQuoteCode

/-! ## Rational quote families -/

/-- Decode a threshold payload; malformed encodings harmlessly denote zero. -/
def decodedQuotationRat (z : ℕ) : ℚ :=
  (Encodable.decode (α := ℚ) z).getD 0

@[simp] theorem decodedQuotationRat_encode (r : ℚ) :
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

noncomputable def luv {T : ArithmeticTheory} {value : ℕ → ℚ}
    (q : RationalQuoteCode T value) (n : ℕ) : LUV :=
  arithmeticThresholdLUV q.code n

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

/-! ## Concrete affine meshes for varying quotation LUVs -/

namespace LUV

/-- The day-indexed expectation mesh for a varying LUV family: day `n` carries its own
grid `n + 1` (`def:e`). -/
def expectAffineSeq (X : ℕ → LUV) (n : ℕ) : AffineCombination :=
  (X n).expectAffine (n + 1)

lemma expectAffineSeq_price (X : ℕ → LUV) (P : History) (n : ℕ) :
    (expectAffineSeq X n).price P n = (X n).expect P n :=
  (X n).expectAffine_price P n

lemma expectAffineSeq_value (X : ℕ → LUV) (P : History)
    (w : Valuation) (n : ℕ) :
    (expectAffineSeq X n).value P w = (X n).expectApprox w (n + 1) :=
  (X n).expectAffine_value P w (n + 1)

lemma expectAffineSeq_magnitude_le_one (X : ℕ → LUV)
    (P : History) (n : ℕ) :
    (expectAffineSeq X n).magnitude P ≤ 1 :=
  (X n).expectAffine_magnitude_le_one P (n + 1)

/-- A compact varying threshold presentation emits the literal diagonal expectation
mesh uniformly; no opaque serialized affine object is decoded. -/
noncomputable def expectAffineSeq_polySequence (X : ℕ → LUV)
    (hcode : LUV.RpnThresholdCodeSeq X) :
    AffineCombination.PolySequence (expectAffineSeq X) := by
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  have hindex := PolyFueled.left.pair (PolyFueled.left.succ_comp.pair PolyFueled.right)
  have hsentence := hcode.comp hindex
  exact {
    termCount := fun n ↦ n + 1
    coefficient := fun z ↦ .const (1 / ((z.unpair.1 + 1 : ℕ) : ℚ))
    sentence := fun z ↦
      (X z.unpair.1).gt ((z.unpair.2 : ℚ) / ((z.unpair.1 + 1 : ℕ) : ℚ))
    termCount_poly := ⟨_, PolyFueled.id.succ_comp⟩
    const_poly := RpnSpliceStream.serialize_const 0
    coefficient_poly := RpnSpliceStream.serialize_const_comp
      ⟨_, hinv.comp PolyFueled.left.succ_comp⟩
    sentence_poly := hsentence.of_eq (fun z ↦ by simp)
    terms_eq := by intro n; simp [expectAffineSeq, LUV.expectAffine]
    const_rank := by intro n; simp [expectAffineSeq, LUV.expectAffine]
    coefficient_rank := by intro n j hj; simp [EF.rank]
    const_closed := by intro n ρ V; simp [expectAffineSeq, LUV.expectAffine]
    coefficient_closed := by intro z ρ V; simp [EF.denoteWith]
  }

end LUV

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
  let base := LUV.expectAffineSeq_polySequence Y hY
  exact {
    termCount := base.termCount
    coefficient := fun z ↦ EF.mul (EF.const (-1)) (base.coefficient z)
    sentence := base.sentence
    termCount_poly := base.termCount_poly
    const_poly := hH.polySeg
    coefficient_poly := RpnSpliceStream.serialize_mul
      (RpnSpliceStream.serialize_const (-1))
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
    rw [AffineCombination.price, numericQuoteAffine_value, target.denote, abs_le]
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
    (hφ : RpnSentenceCodes φ) :
    PGenerableWeighting (currentPriceFeature φ) := by
  exact {
    polySeg := (RpnSpliceStream.serialize_price hφ PolyFueled.id
      PolyFueled.id).of_eq (fun n ↦ by simp [currentPriceFeature])
    rank_le := by intro n; simp [currentPriceFeature]
    closed := by intro n ρ V; simp [currentPriceFeature]
  }

noncomputable def currentPriceNumericTarget
    {P : History} {T : ArithmeticTheory} {value : ℕ → ℚ}
    (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ)
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
    (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ)
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
  let hmesh := LUV.expectAffineSeq_polySequence X hX
  have hdiag : PolyFueled
      (Nat.Partrec.Code.id.pair Nat.Partrec.Code.id)
      (fun n : ℕ ↦ Nat.pair n n) := PolyFueled.id.pair PolyFueled.id
  exact {
    polySeg := RpnSpliceStream.of_eq (hmesh.priceFeature_polySeg.comp hdiag)
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

@[simp] theorem gatedComplementAffine_price (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (P : History) (n m : ℕ) :
    (gatedComplementAffine scale H quote n).price P m =
      (scale : ℝ) * (H n).denote P * (1 - P m (quote n)) := by
  simp [gatedComplementAffine, AffineCombination.price,
    AffineCombination.value]
  ring

@[simp] theorem gatedComplementAffine_value (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (P : History) (w : Valuation) (n : ℕ) :
    (gatedComplementAffine scale H quote n).value P w =
      (scale : ℝ) * (H n).denote P * (1 - w (quote n)) := by
  simp [gatedComplementAffine, AffineCombination.value]
  ring

@[simp] theorem gatedComplementAffine_magnitude (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (P : History) (n : ℕ) :
    (gatedComplementAffine scale H quote n).magnitude P =
      |(scale : ℝ) * (H n).denote P| := by
  simp [gatedComplementAffine, AffineCombination.magnitude, abs_mul]

@[simp] theorem gatedAffirmativeAffine_price (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (P : History) (n m : ℕ) :
    (gatedAffirmativeAffine scale H quote n).price P m =
      (scale : ℝ) * (H n).denote P * P m (quote n) := by
  simp [gatedAffirmativeAffine, AffineCombination.price,
    AffineCombination.value]

@[simp] theorem gatedAffirmativeAffine_value (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (P : History) (w : Valuation) (n : ℕ) :
    (gatedAffirmativeAffine scale H quote n).value P w =
      (scale : ℝ) * (H n).denote P * w (quote n) := by
  simp [gatedAffirmativeAffine, AffineCombination.value]

@[simp] theorem gatedAffirmativeAffine_magnitude (scale : ℚ) (H : ℕ → EF)
    (quote : ℕ → Sentence) (P : History) (n : ℕ) :
    (gatedAffirmativeAffine scale H quote n).magnitude P =
      |(scale : ℝ) * (H n).denote P| := by
  simp [gatedAffirmativeAffine, AffineCombination.magnitude, abs_mul]

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
    const_poly := RpnSpliceStream.serialize_mul
      (RpnSpliceStream.serialize_const scale) hH.polySeg
    coefficient_poly := RpnSpliceStream.serialize_mul
      (RpnSpliceStream.serialize_const (-scale))
      (hH.polySeg.comp PolyFueled.left)
    sentence_poly := RpnSentenceCodes.ofPolySentenceCodes
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
    const_poly := RpnSpliceStream.serialize_const 0
    coefficient_poly := RpnSpliceStream.serialize_mul
      (RpnSpliceStream.serialize_const scale)
      (hH.polySeg.comp PolyFueled.left)
    sentence_poly := RpnSentenceCodes.ofPolySentenceCodes
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

/-! ## Continuous gate feature compiler -/

namespace PGenerableWeighting

lemma mul {A B : ℕ → EF} (hA : PGenerableWeighting A)
    (hB : PGenerableWeighting B) :
    PGenerableWeighting (fun n ↦ EF.mul (A n) (B n)) where
  polySeg := RpnSpliceStream.serialize_mul hA.polySeg hB.polySeg
  rank_le := by
    intro n
    simp only [EF.rank]
    exact Nat.max_le.mpr ⟨hA.rank_le n, hB.rank_le n⟩
  closed := by
    intro n ρ V
    simp only [EF.denoteWith, EF.denote_mul, Pi.mul_apply]
    rw [hA.closed n ρ V, hB.closed n ρ V]

lemma add {A B : ℕ → EF} (hA : PGenerableWeighting A)
    (hB : PGenerableWeighting B) :
    PGenerableWeighting (fun n ↦ EF.add (A n) (B n)) where
  polySeg := RpnSpliceStream.serialize_add hA.polySeg hB.polySeg
  rank_le := by
    intro n
    simp only [EF.rank]
    exact Nat.max_le.mpr ⟨hA.rank_le n, hB.rank_le n⟩
  closed := by
    intro n ρ V
    simp only [EF.denoteWith, EF.denote_add, Pi.add_apply]
    rw [hA.closed n ρ V, hB.closed n ρ V]

end PGenerableWeighting

lemma GeneratedRatFeature.toWeighting
    {P : History} {q : ℕ → ℚ} {feature : ℕ → EF}
    (h : GeneratedRatFeature P q feature) : PGenerableWeighting feature where
  polySeg := h.polyTok
  rank_le := h.rank_le
  closed := h.closed

/-- A polynomial rational code sequence, viewed as a closed constant feature on each day. -/
def ratCodeFeature (q : ℕ → ℚ) (n : ℕ) : EF :=
  EF.const (q n)

lemma ratCodeFeature_generated (P : History) (q : ℕ → ℚ)
    (hq : PolyRatCodes q) : GeneratedRatFeature P q (ratCodeFeature q) where
  rank_le := by intro n; simp [ratCodeFeature]
  polyTok := RpnSpliceStream.serialize_const_comp hq
  closed := by intro n ρ V; simp [ratCodeFeature]
  denote := by intro n; simp [ratCodeFeature]

/-- Polynomial rational codes remain polynomial after a polynomially fueled reindexing. -/
lemma PolyRatCodes.reindex {q : ℕ → ℚ} (hq : PolyRatCodes q)
    {index : ℕ → ℕ} (hindex : ∃ c, PolyFueled c index) :
    PolyRatCodes (fun n ↦ q (index n)) := by
  obtain ⟨cq, hq⟩ := hq
  obtain ⟨ci, hi⟩ := hindex
  exact ⟨cq.comp ci, hq.comp hi⟩

/-- A generated rational feature remains generated after a polynomially fueled,
non-increasing reindexing: the day-`m` expression is the source expression at day
`index m`, whose rank is already below `index m ≤ m`. -/
lemma GeneratedRatFeature.reindex {P : History} {q : ℕ → ℚ} {feature : ℕ → EF}
    (h : GeneratedRatFeature P q feature)
    {index : ℕ → ℕ} (hindex : ∃ c, PolyFueled c index)
    (hle : ∀ m, index m ≤ m) :
    GeneratedRatFeature P (fun m ↦ q (index m)) (fun m ↦ feature (index m)) where
  rank_le := fun m ↦ (h.rank_le (index m)).trans (hle m)
  polyTok := by
    obtain ⟨ci, hi⟩ := hindex
    exact h.polyTok.comp hi
  closed := fun m ↦ h.closed (index m)
  denote := fun m ↦ h.denote (index m)

/-- Express `ctsInd δ x y` using only the repository's allowed feature operations. -/
def ctsIndFeature (δ : ℕ → ℚ) (x y : ℕ → EF) (n : ℕ) : EF :=
  clip01 (EF.mul
    (EF.add (x n) (EF.mul (EF.const (-1)) (y n)))
    (EF.const (1 / δ n)))

lemma ctsIndFeature_generated (δ : ℕ → ℚ) (x y : ℕ → EF)
    (hδinv : PolyRatCodes (fun n ↦ 1 / δ n))
    (hx : PGenerableWeighting x) (hy : PGenerableWeighting y) :
    PGenerableWeighting (ctsIndFeature δ x y) := by
  have hinv : RpnSpliceStream (fun n ↦ (EF.const (1 / δ n)).serialize) :=
    RpnSpliceStream.serialize_const_comp hδinv
  have hnegY := RpnSpliceStream.serialize_mul
    (RpnSpliceStream.serialize_const (-1)) hy.polySeg
  exact {
    polySeg := RpnSpliceStream.serialize_clip01
      (RpnSpliceStream.serialize_mul (RpnSpliceStream.serialize_add hx.polySeg hnegY) hinv)
    rank_le := by
      intro n
      simp only [ctsIndFeature, clip01_rank, EF.rank]
      exact Nat.max_le.mpr
        ⟨Nat.max_le.mpr ⟨hx.rank_le n,
            Nat.max_le.mpr ⟨by simp, hy.rank_le n⟩⟩, by simp⟩
    closed := by
      intro n ρ V
      simp [ctsIndFeature, clip01, efMin, EF.denoteWith,
        hx.closed n ρ V, hy.closed n ρ V]
  }

lemma ctsIndFeature_denote (δ : ℕ → ℚ) (x y : ℕ → EF)
    (hδ : ∀ n, 0 < δ n) (P : History) (n : ℕ) :
    (ctsIndFeature δ x y n).denote P =
      ctsInd (δ n) ((x n).denote P) ((y n).denote P) := by
  have hδR : (0 : ℝ) < δ n := by exact_mod_cast hδ n
  rw [ctsIndFeature, clip01_denote]
  simp only [EF.denote_mul, EF.denote_add, EF.denote_const, Pi.mul_apply,
    Pi.add_apply, Rat.cast_neg, Rat.cast_one, Rat.cast_div]
  rw [max_min_distrib_left]
  simp only [max_eq_right zero_le_one]
  unfold ctsInd
  congr 2
  field_simp
  ring

lemma ctsInd_eq_zero_of_le (δ : ℚ) (x y : ℝ) (hδ : 0 < δ)
    (hxy : x ≤ y) : ctsInd δ x y = 0 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  have hratio : (x - y) / (δ : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hδR.le
  rw [max_eq_left hratio, min_eq_right zero_le_one]

/-! ## Bounded deferral preimage

A day-indexed affine family that is to be evaluated on the deferral day `f n` may recover
the source day `n` from `f n` by a bounded scan whenever `f` is injective.  That is the
device below, and its only consumers are the `thm:wub`/`thm:wubaff`/`thm:wubexp` feedback
chain (`FeedbackTruth`), where the paper itself asks for a *strictly increasing* deferral
function, so `StrictlyIncreasingDeferral.injective` supplies the hypothesis and nothing is
narrowed.

The `thm:cee`/`thm:ceu`/`thm:ccee`/`thm:st` chain does **not** use it: those endpoints
hold for every `def:deferralfunc` (`f n > n` plus time-computability), through the
deferral-fibre selector of the `DeferralFibre` section — `AffineCombination.blockSum`
(variable-width affine combination), `selectorFeature` (division-free first-violator
selector, with `firstSuccess_sum_le_one` for the budget and `firstSuccess_forces` for the
forcing step) and `DeferralFibre.deferred_block_price_tendsto_zero`, which delivers
`(Bs ⟨f n, n⟩).price P (f n) → 0` with no injectivity.  A plain price-gated sum over the
fibre `f⁻¹(m)` provably cannot do this (the unit magnitude budget spreads across an
unboundedly large fibre while the gap convergence carries no rate, so no
violation-independent weighting forces individual terms); the first-violator selector is
what makes one saturated gate enough. -/

/-- Number of bounded-schedule preimages of day `m` among the only possible source
indices `k < m`. -/
def deferralMatchCount (f : DeferralFunction) (a degree m : ℕ) : ℕ :=
  segPrefix (fun z => FeedbackEmission.scheduledMatch f a degree z) m m

/-- Sum of the matching source indices.  Under injectivity there is at most one match,
so this is the unique preimage on the image of `f` and harmlessly defaults to zero off it. -/
def deferralPreimage (f : DeferralFunction) (a degree m : ℕ) : ℕ :=
  segPrefix (fun z => z.unpair.2 *
    FeedbackEmission.scheduledMatch f a degree z) m m

/-- Boolean-as-natural image flag derived from the bounded match count. -/
def deferralImageFlag (f : DeferralFunction) (a degree m : ℕ) : ℕ :=
  if deferralMatchCount f a degree m = 0 then 0 else 1

lemma deferralMatchCount_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (deferralMatchCount f a degree) := by
  obtain ⟨cmatch, hmatch⟩ := FeedbackEmission.scheduledMatch_polyFueled f a degree
  obtain ⟨cprefix, hprefix⟩ := segPrefix_polyFueled hmatch
  exact ⟨_, (hprefix.comp (PolyFueled.id.pair PolyFueled.id)).of_eq (fun m => by
    simp [deferralMatchCount])⟩

lemma deferralPreimage_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (deferralPreimage f a degree) := by
  obtain ⟨cmatch, hmatch⟩ := FeedbackEmission.scheduledMatch_polyFueled f a degree
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  have hterm := hmul.comp (PolyFueled.right.pair hmatch)
  obtain ⟨cprefix, hprefix⟩ := segPrefix_polyFueled hterm
  exact ⟨_, (hprefix.comp (PolyFueled.id.pair PolyFueled.id)).of_eq (fun m => by
    simp [deferralPreimage])⟩

lemma deferralImageFlag_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (deferralImageFlag f a degree) := by
  obtain ⟨ccount, hcount⟩ := deferralMatchCount_polyFueled f a degree
  exact ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const 0).pair (PolyFueled.const 1)).pair hcount)).of_eq
      (fun m => by simp [deferralImageFlag, ifzSelFn])⟩

lemma deferralImageFlag_zero_or_one (f : DeferralFunction) (a degree m : ℕ) :
    deferralImageFlag f a degree m = 0 ∨ deferralImageFlag f a degree m = 1 := by
  simp only [deferralImageFlag]
  split <;> simp

lemma deferralPreimage_at
    (f : DeferralFunction) (hinj : Function.Injective f.f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k =
      some (f k)) (n : ℕ) :
    deferralPreimage f a degree (f n) = n := by
  let lenFn : ℕ → ℕ := fun z => z.unpair.2 *
    FeedbackEmission.scheduledMatch f a degree z
  have hscan : ∀ k, k ≤ f n →
      segPrefix lenFn (f n) k = if n < k then n else 0 := by
    intro k hk
    induction k with
    | zero => simp [segPrefix]
    | succ k ih =>
        rw [segPrefix_succ, ih (by omega)]
        have hmatch : FeedbackEmission.scheduledMatch f a degree
            (Nat.pair (f n) k) = if k = n then 1 else 0 := by
          by_cases hkn : k = n
          · subst k
            simpa using
              (FeedbackEmission.scheduledMatch_eq_one_iff f hspec (f n) n).2 rfl
          · have hne : f k ≠ f n := fun h => hkn (hinj h)
            simpa [hkn] using
              (FeedbackEmission.scheduledMatch_eq_zero_iff f hspec (f n) k).2 hne
        simp only [lenFn, Nat.unpair_pair, hmatch]
        split_ifs <;> omega
  rw [deferralPreimage, hscan (f n) le_rfl]
  simp [f.lt n]

lemma deferralMatchCount_pos_iff
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    (m : ℕ) :
    0 < deferralMatchCount f a degree m ↔ ∃ k < m, f k = m := by
  let lenFn : ℕ → ℕ := fun z => FeedbackEmission.scheduledMatch f a degree z
  have hscan : ∀ r, 0 < segPrefix lenFn m r ↔
      ∃ k < r, lenFn (Nat.pair m k) = 1 := by
    intro r
    induction r with
    | zero => simp [segPrefix]
    | succ r ih =>
        rw [segPrefix_succ]
        rcases FeedbackEmission.scheduledMatch_zero_or_one f a degree
          (Nat.pair m r) with hr | hr
        · rw [show lenFn (Nat.pair m r) = 0 by exact hr]
          simp only [add_zero, ih]
          constructor
          · rintro ⟨k, hk, hmatch⟩
            exact ⟨k, by omega, hmatch⟩
          · rintro ⟨k, hk, hmatch⟩
            have hkle : k < r ∨ k = r := by omega
            rcases hkle with hlt | rfl
            · exact ⟨k, hlt, hmatch⟩
            · have hr' : lenFn (Nat.pair m k) = 0 := hr
              rw [hr'] at hmatch
              omega
        · rw [show lenFn (Nat.pair m r) = 1 by exact hr]
          constructor
          · intro _
            exact ⟨r, Nat.lt_succ_self r, hr⟩
          · intro _
            omega
  rw [deferralMatchCount, hscan m]
  constructor
  · rintro ⟨k, hk, hmatch⟩
    exact ⟨k, hk,
      (FeedbackEmission.scheduledMatch_eq_one_iff f hspec m k).1 hmatch⟩
  · rintro ⟨k, hk, hfk⟩
    exact ⟨k, hk,
      (FeedbackEmission.scheduledMatch_eq_one_iff f hspec m k).2 hfk⟩

lemma deferralImageFlag_eq_one_iff
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    (m : ℕ) :
    deferralImageFlag f a degree m = 1 ↔ ∃ k < m, f k = m := by
  rw [deferralImageFlag]
  by_cases hzero : deferralMatchCount f a degree m = 0
  · rw [if_pos hzero]
    constructor
    · intro h
      omega
    · intro hex
      have hpos := (deferralMatchCount_pos_iff f hspec m).2 hex
      omega
  · rw [if_neg hzero]
    constructor
    · intro _
      exact (deferralMatchCount_pos_iff f hspec m).1 (Nat.pos_of_ne_zero hzero)
    · intro _
      rfl

/-- Every scheduled day is flagged: `n` itself witnesses membership of `f n` in the
image, so no injectivity of `f` is needed here. -/
lemma deferralImageFlag_at
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k =
      some (f k)) (n : ℕ) :
    deferralImageFlag f a degree (f n) = 1 :=
  (deferralImageFlag_eq_one_iff f hspec (f n)).2 ⟨n, f.lt n, rfl⟩

lemma deferralPreimage_spec
    (f : DeferralFunction) (hinj : Function.Injective f.f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    {m : ℕ} (hm : deferralImageFlag f a degree m = 1) :
    deferralPreimage f a degree m < m ∧
      f (deferralPreimage f a degree m) = m := by
  obtain ⟨k, hk, hfk⟩ := (deferralImageFlag_eq_one_iff f hspec m).1 hm
  have hidx : deferralPreimage f a degree m = k := by
    rw [← hfk]
    exact deferralPreimage_at f hinj hspec k
  rw [hidx]
  exact ⟨hk, hfk⟩

/-! ### Reindexed threshold syntax and cross-precision meshes -/

lemma LUV.RpnThresholdCodeSeq.reindex
    {X : ℕ → LUV} (hX : LUV.RpnThresholdCodeSeq X)
    {index : ℕ → ℕ} (hindex : ∃ c, PolyFueled c index) :
    LUV.RpnThresholdCodeSeq (fun n ↦ X (index n)) := by
  obtain ⟨ci, hi⟩ := hindex
  have hquery : PolyFueled _ (fun z : ℕ ↦
      Nat.pair (index z.unpair.1) z.unpair.2) :=
    (hi.comp PolyFueled.left).pair PolyFueled.right
  exact (hX.comp hquery).of_eq (fun z ↦ by simp)

/-- Pointwise addition of polynomial affine families, with the two term streams joined
by a bounded conditional rather than by decoding either affine object. -/
noncomputable def AffineCombination.PolySequence.add
    {As Bs : ℕ → AffineCombination}
    (hA : AffineCombination.PolySequence As)
    (hB : AffineCombination.PolySequence Bs) :
    AffineCombination.PolySequence (fun n ↦ (As n).add (Bs n)) := by
  let cA := Classical.choose hA.termCount_poly
  have hcA := Classical.choose_spec hA.termCount_poly
  let cB := Classical.choose hB.termCount_poly
  have hcB := Classical.choose_spec hB.termCount_poly
  let cadd := Classical.choose addc_polyFueled
  have hadd := Classical.choose_spec addc_polyFueled
  have hn := PolyFueled.left
  have hj := PolyFueled.right
  have hcountA := hcA.comp hn
  have htest0 := subc_polyFueled.comp (hj.succ_comp.pair hcountA)
  have htest : PolyFueled _ (fun z : ℕ ↦
      (z.unpair.2 + 1) - hA.termCount z.unpair.1) :=
    htest0.of_eq (fun z ↦ by simp)
  have hoffset0 := subc_polyFueled.comp (hj.pair hcountA)
  have hoffset : PolyFueled _ (fun z : ℕ ↦
      z.unpair.2 - hA.termCount z.unpair.1) :=
    hoffset0.of_eq (fun z ↦ by simp)
  have hqueryB : PolyFueled _ (fun z : ℕ ↦
      Nat.pair z.unpair.1 (z.unpair.2 - hA.termCount z.unpair.1)) :=
    hn.pair hoffset
  have hcoeff := RpnSpliceStream.ifZero hA.coefficient_poly
    (hB.coefficient_poly.comp hqueryB) htest
  have hsentence : RpnSentenceCodes (fun z ↦
      if z.unpair.2 < hA.termCount z.unpair.1 then hA.sentence z
      else hB.sentence (Nat.pair z.unpair.1
        (z.unpair.2 - hA.termCount z.unpair.1))) :=
    (RpnSentenceCodes.ifZero hA.sentence_poly
      (hB.sentence_poly.comp hqueryB) htest).of_eq (fun z ↦ by
      by_cases hjlt : z.unpair.2 < hA.termCount z.unpair.1
      · rw [if_pos (by omega : (z.unpair.2 + 1) - hA.termCount z.unpair.1 = 0),
          if_pos hjlt]
      · rw [if_neg (by omega : ¬ ((z.unpair.2 + 1) - hA.termCount z.unpair.1 = 0)),
          if_neg hjlt])
  exact {
    termCount := fun n ↦ hA.termCount n + hB.termCount n
    coefficient := fun z ↦ if z.unpair.2 < hA.termCount z.unpair.1 then
      hA.coefficient z
      else hB.coefficient (Nat.pair z.unpair.1
        (z.unpair.2 - hA.termCount z.unpair.1))
    sentence := fun z ↦ if z.unpair.2 < hA.termCount z.unpair.1 then
      hA.sentence z
      else hB.sentence (Nat.pair z.unpair.1
        (z.unpair.2 - hA.termCount z.unpair.1))
    termCount_poly := ⟨cadd.comp (cA.pair cB),
      (hadd.comp (hcA.pair hcB)).of_eq (fun n ↦ by simp)⟩
    const_poly := RpnSpliceStream.serialize_add hA.const_poly hB.const_poly
    coefficient_poly := RpnSpliceStream.of_eq hcoeff (fun z ↦ by
      by_cases hjlt : z.unpair.2 < hA.termCount z.unpair.1
      · rw [if_pos hjlt, if_pos (by omega)]
      · rw [if_neg hjlt, if_neg (by omega)])
    sentence_poly := hsentence
    terms_eq := by
      intro n
      simp only [AffineCombination.add]
      rw [hA.terms_eq, hB.terms_eq, List.range_add, List.map_append]
      simp only [List.map_map, Function.comp_def]
      apply congrArg₂ (· ++ ·)
      · apply List.map_congr_left
        intro j hjmem
        simp only [List.mem_range] at hjmem
        simp [hjmem]
      · apply List.map_congr_left
        intro j hjmem
        simp
    const_rank := by
      intro n
      simp only [AffineCombination.add, EF.rank]
      exact Nat.max_le.mpr ⟨hA.const_rank n, hB.const_rank n⟩
    coefficient_rank := by
      intro n j hjbound
      simp only [Nat.unpair_pair]
      by_cases hjlt : j < hA.termCount n
      · rw [if_pos hjlt]
        exact hA.coefficient_rank n j hjlt
      · rw [if_neg hjlt]
        exact hB.coefficient_rank n (j - hA.termCount n) (by omega)
    const_closed := by
      intro n ρ V
      simp only [AffineCombination.add, EF.denoteWith, EF.denote_add,
        Pi.add_apply]
      rw [hA.const_closed n ρ V, hB.const_closed n ρ V]
    coefficient_closed := by
      intro z ρ V
      by_cases hjlt : z.unpair.2 < hA.termCount z.unpair.1
      · rw [if_pos hjlt]
        exact hA.coefficient_closed z ρ V
      · rw [if_neg hjlt]
        exact hB.coefficient_closed _ ρ V
  }

/-- Multiply every member of a polynomial affine family by a generated closed feature. -/
noncomputable def AffineCombination.PolySequence.scaleFeature
    {As : ℕ → AffineCombination} (hA : AffineCombination.PolySequence As)
    (W : ℕ → EF) (hW : PGenerableWeighting W) :
    AffineCombination.PolySequence (fun n ↦ (As n).scale (W n)) where
  termCount := hA.termCount
  coefficient := fun z ↦ EF.mul (W z.unpair.1) (hA.coefficient z)
  sentence := hA.sentence
  termCount_poly := hA.termCount_poly
  const_poly := RpnSpliceStream.serialize_mul hW.polySeg hA.const_poly
  coefficient_poly := RpnSpliceStream.serialize_mul
    (hW.polySeg.comp PolyFueled.left) hA.coefficient_poly
  sentence_poly := hA.sentence_poly
  terms_eq := by
    intro n
    rw [AffineCombination.scale, hA.terms_eq]
    simp [List.map_map, Function.comp_def]
  const_rank := by
    intro n
    simp only [AffineCombination.scale, EF.rank]
    exact Nat.max_le.mpr ⟨hW.rank_le n, hA.const_rank n⟩
  coefficient_rank := by
    intro n j hj
    simp only [EF.rank]
    simpa only [Nat.unpair_pair] using
      Nat.max_le.mpr ⟨hW.rank_le n, hA.coefficient_rank n j hj⟩
  const_closed := by
    intro n ρ V
    simp only [AffineCombination.scale, EF.denoteWith, EF.denote_mul, Pi.mul_apply]
    rw [hW.closed n ρ V, hA.const_closed n ρ V]
  coefficient_closed := by
    intro z ρ V
    simp only [EF.denoteWith, EF.denote_mul, Pi.mul_apply]
    rw [hW.closed z.unpair.1 ρ V, hA.coefficient_closed z ρ V]

/-! ## Variable-width affine combinations

The `add`/`scaleFeature` layer combines a *fixed* number of affine families.  The
deferral-fibre gating below needs a day-indexed sum whose width grows with the day: on
day `m`, one term per source day `k < cnt m`, each weighted by a day-`m`-legal feature.
Blocks are padded out to a common width `width m`, which keeps the flat term index a
plain `range` — block `= j / width m`, offset `= j % width m` — and so replaces an
inverse prefix-sum by division and remainder. -/

namespace AffineCombination

/-- Zero-coefficient padding entry. -/
def padEntry (pad : Sentence) : EF × Sentence := (EF.const 0, pad)

private lemma eq_map_range_getD {α : Type*} (t : List α) (d : α) :
    t = (List.range t.length).map (fun o => t.getD o d) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h1]

private lemma padded_map_sum {α : Type*} [AddCommMonoid α]
    {β : Type*} (t : List β) (d : β) (W : ℕ) (hW : t.length ≤ W)
    (F : β → α) (hF : F d = 0) :
    ((List.range W).map (fun o => F (t.getD o d))).sum = (t.map F).sum := by
  obtain ⟨r, hr⟩ : ∃ r, W = t.length + r := ⟨W - t.length, by omega⟩
  subst hr
  rw [List.range_add]
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def]
  have h1 : ((List.range t.length).map (fun o => F (t.getD o d))).sum = (t.map F).sum := by
    conv_rhs => rw [eq_map_range_getD t d]
    simp [Function.comp_def]
  have h2 : ((List.range r).map (fun o => F (t.getD (t.length + o) d))).sum = 0 := by
    have hz : ∀ o, F (t.getD (t.length + o) d) = 0 := by
      intro o
      rw [List.getD_eq_default _ _ (by omega), hF]
    rw [List.map_congr_left (fun o _ => hz o)]
    simp
  rw [h1, h2, add_zero]

private lemma sum_map_flatMap {α β γ : Type*} [AddCommMonoid γ]
    (L : List α) (g : α → List β) (F : β → γ) :
    ((L.flatMap g).map F).sum = (L.map (fun x => ((g x).map F).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

private lemma sum_map_add' {α γ : Type*} [AddCommMonoid γ] (L : List α) (u v : α → γ) :
    (L.map fun x => u x + v x).sum = (L.map u).sum + (L.map v).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; abel

/-- Rectangular flattening: a block/offset double range is the plain range of the product,
read through division and remainder by the block width. -/
private lemma flatMap_range_map_range {α : Type*} (a b : ℕ) (hb : 0 < b) (G : ℕ → ℕ → α) :
    ((List.range a).flatMap fun k => (List.range b).map fun o => G k o)
      = (List.range (a * b)).map fun j => G (j / b) (j % b) := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [List.range_succ, List.flatMap_append, ih]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [show (a + 1) * b = a * b + b by ring, List.range_add, List.map_append]
      congr 1
      · rw [List.map_map]
        refine List.map_congr_left fun o ho => ?_
        simp only [Function.comp_apply, List.mem_range] at ho ⊢
        have hd : (a * b + o) / b = a := by
          rw [Nat.mul_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt ho, Nat.add_zero]
        have hm : (a * b + o) % b = o := by
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ho]
        rw [hd, hm]

/-- `blockSum Bs coeff cnt width pad m = Σ_{k < cnt m} coeff⟨m,k⟩ · Bs⟨m,k⟩`, each block's
term list padded with zero coefficients out to the uniform width `width m`. -/
noncomputable def blockSum (Bs : ℕ → AffineCombination) (coeff : ℕ → EF)
    (cnt width : ℕ → ℕ) (pad : Sentence) (m : ℕ) : AffineCombination where
  const := (List.range (cnt m)).foldr
    (fun k acc => .add (.mul (coeff (Nat.pair m k)) (Bs (Nat.pair m k)).const) acc)
    (.const 0)
  terms := (List.range (cnt m)).flatMap fun k =>
    (List.range (width m)).map fun o =>
      (EF.mul (coeff (Nat.pair m k))
          ((Bs (Nat.pair m k)).terms.getD o (padEntry pad)).1,
        ((Bs (Nat.pair m k)).terms.getD o (padEntry pad)).2)

private lemma foldr_addMul_denote (L : List ℕ) (c v : ℕ → EF) (V : History) :
    ((L.foldr (fun k acc => EF.add (EF.mul (c k) (v k)) acc) (EF.const 0)).denote V)
      = (L.map fun k => (c k).denote V * (v k).denote V).sum := by
  induction L with
  | nil => simp
  | cons k L ih => simp [ih]

lemma blockSum_value (Bs : ℕ → AffineCombination) (coeff : ℕ → EF)
    (cnt width : ℕ → ℕ) (pad : Sentence) (m : ℕ) (V : History) (w : Valuation)
    (hw : ∀ k < cnt m, (Bs (Nat.pair m k)).terms.length ≤ width m) :
    (blockSum Bs coeff cnt width pad m).value V w =
      ((List.range (cnt m)).map fun k =>
        (coeff (Nat.pair m k)).denote V * (Bs (Nat.pair m k)).value V w).sum := by
  rw [value, blockSum]
  rw [foldr_addMul_denote, sum_map_flatMap, ← sum_map_add']
  refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
  simp only [List.mem_range] at hk
  have hblock := padded_map_sum ((Bs (Nat.pair m k)).terms) (padEntry pad) (width m)
    (hw k hk) (fun p : EF × Sentence =>
      (EF.mul (coeff (Nat.pair m k)) p.1).denote V * w p.2) (by simp [padEntry])
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [hblock, value]
  simp only [EF.denote_mul, Pi.mul_apply]
  have hpull : ((Bs (Nat.pair m k)).terms.map fun p =>
      (coeff (Nat.pair m k)).denote V * p.1.denote V * w p.2).sum
      = (coeff (Nat.pair m k)).denote V *
        ((Bs (Nat.pair m k)).terms.map fun p => p.1.denote V * w p.2).sum := by
    induction (Bs (Nat.pair m k)).terms with
    | nil => simp
    | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [hpull]
  ring

lemma blockSum_price (Bs : ℕ → AffineCombination) (coeff : ℕ → EF)
    (cnt width : ℕ → ℕ) (pad : Sentence) (m : ℕ) (V : History) (day : ℕ)
    (hw : ∀ k < cnt m, (Bs (Nat.pair m k)).terms.length ≤ width m) :
    (blockSum Bs coeff cnt width pad m).price V day =
      ((List.range (cnt m)).map fun k =>
        (coeff (Nat.pair m k)).denote V * (Bs (Nat.pair m k)).price V day).sum := by
  simpa only [price] using blockSum_value Bs coeff cnt width pad m V (V day) hw

lemma blockSum_magnitude (Bs : ℕ → AffineCombination) (coeff : ℕ → EF)
    (cnt width : ℕ → ℕ) (pad : Sentence) (m : ℕ) (V : History)
    (hw : ∀ k < cnt m, (Bs (Nat.pair m k)).terms.length ≤ width m) :
    (blockSum Bs coeff cnt width pad m).magnitude V =
      ((List.range (cnt m)).map fun k =>
        |(coeff (Nat.pair m k)).denote V| * (Bs (Nat.pair m k)).magnitude V).sum := by
  rw [magnitude, blockSum]
  rw [sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
  simp only [List.mem_range] at hk
  have hblock := padded_map_sum ((Bs (Nat.pair m k)).terms) (padEntry pad) (width m)
    (hw k hk) (fun p : EF × Sentence =>
      |(EF.mul (coeff (Nat.pair m k)) p.1).denote V|) (by simp [padEntry])
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [hblock, magnitude]
  simp only [EF.denote_mul, Pi.mul_apply, abs_mul]
  induction (Bs (Nat.pair m k)).terms with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma PolySequence.terms_length {As : ℕ → AffineCombination} (h : PolySequence As)
    (n : ℕ) : (As n).terms.length = h.termCount n := by
  rw [h.terms_eq]; simp

lemma getD_map_range_ite {α : Type*} (n : ℕ) (g : ℕ → α) (o : ℕ) (d : α) :
    ((List.range n).map g).getD o d = if o < n then g o else d := by
  by_cases ho : o < n
  · rw [if_pos ho, List.getD_eq_getElem _ _ (by simpa using ho)]
    simp
  · rw [if_neg ho, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ho)]

/-- Serialization of a `Σ uₖ · vₖ` fold: one `coefficient/value/multiply` block per
summand, closed by a run of `add` tags. -/
private lemma foldr_addMul_serialize (L : List ℕ) (u v : ℕ → EF) :
    (L.foldr (fun k acc => EF.add (EF.mul (u k) (v k)) acc) (EF.const 0)).serialize =
      (L.flatMap fun k => (u k).serialize ++ (v k).serialize ++ [3]) ++
        (EF.const 0).serialize ++ List.replicate L.length 2 := by
  induction L with
  | nil => simp
  | cons k L ih =>
      simp only [List.foldr_cons, List.flatMap_cons, List.length_cons]
      rw [show (EF.add (EF.mul (u k) (v k))
            (L.foldr (fun k acc => EF.add (EF.mul (u k) (v k)) acc) (EF.const 0))).serialize =
          ((u k).serialize ++ (v k).serialize ++ [3]) ++
            (L.foldr (fun k acc => EF.add (EF.mul (u k) (v k)) acc)
              (EF.const 0)).serialize ++ [2] by
        simp [EF.serialize, List.append_assoc]]
      rw [ih]
      simp [List.replicate_succ', List.append_assoc]

private lemma foldr_addMul_rank (L : List ℕ) (u v : ℕ → EF) (n : ℕ)
    (hu : ∀ k ∈ L, (u k).rank ≤ n) (hv : ∀ k ∈ L, (v k).rank ≤ n) :
    (L.foldr (fun k acc => EF.add (EF.mul (u k) (v k)) acc) (EF.const 0)).rank ≤ n := by
  induction L with
  | nil => simp
  | cons k L ih =>
      simp only [List.foldr_cons, EF.rank]
      refine Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hu k (by simp), hv k (by simp)⟩,
        ih (fun j hj => hu j (by simp [hj])) (fun j hj => hv j (by simp [hj]))⟩

private lemma foldr_addMul_closed (L : List ℕ) (u v : ℕ → EF) (ρ : List ℝ) (V : History)
    (hu : ∀ k ∈ L, (u k).denoteWith ρ V = (u k).denote V)
    (hv : ∀ k ∈ L, (v k).denoteWith ρ V = (v k).denote V) :
    (L.foldr (fun k acc => EF.add (EF.mul (u k) (v k)) acc) (EF.const 0)).denoteWith ρ V =
      (L.foldr (fun k acc => EF.add (EF.mul (u k) (v k)) acc) (EF.const 0)).denote V := by
  induction L with
  | nil => simp [EF.denote]
  | cons k L ih =>
      simp only [List.foldr_cons, EF.denoteWith, EF.denote_add, EF.denote_mul,
        Pi.add_apply, Pi.mul_apply]
      rw [hu k (by simp), hv k (by simp),
        ih (fun j hj => hu j (by simp [hj])) (fun j hj => hv j (by simp [hj]))]

/-- **Variable-width affine combinator.**  A polynomially emitted *block* family `Bs`
(indexed by `⟨m,k⟩`: evaluation day `m`, source day `k`) and a day-`m`-legal coefficient
family combine into a polynomially emitted affine sequence whose day-`m` member is
`Σ_{k < cnt m} coeff⟨m,k⟩ · Bs⟨m,k⟩`.  Blocks are padded to the common width `width m`, so
the flat term index stays a plain `range` and the block/offset inverse is division and
remainder rather than an inverse prefix-sum. -/
noncomputable def PolySequence.blockSum
    {Bs : ℕ → AffineCombination} (hB : PolySequence Bs)
    {coeff : ℕ → EF} (hcoeff : RpnSpliceStream fun z => (coeff z).serialize)
    (hcoeffClosed : ∀ z ρ V, (coeff z).denoteWith ρ V = (coeff z).denote V)
    (hcoeffRank : ∀ m k, (coeff (Nat.pair m k)).rank ≤ m)
    {cnt width : ℕ → ℕ}
    (hcnt : ∃ c, PolyFueled c cnt) (hwidth : ∃ c, PolyFueled c width)
    (hwidthPos : ∀ m, 0 < width m)
    (hBconstRank : ∀ m k, (Bs (Nat.pair m k)).const.rank ≤ m)
    (hBcoeffRank : ∀ m k o, o < hB.termCount (Nat.pair m k) →
      (hB.coefficient (Nat.pair (Nat.pair m k) o)).rank ≤ m)
    (pad : Sentence) (hpad : RpnSentenceCodes fun _ : ℕ => pad) :
    PolySequence (AffineCombination.blockSum Bs coeff cnt width pad) := by
  have hcntPF := Classical.choose_spec hcnt
  have hwidthPF := Classical.choose_spec hwidth
  have hmulPF := Classical.choose_spec mul_polyFueled
  have hdmPF := Classical.choose_spec divmod1_polyFueled
  have htcPF0 := Classical.choose_spec hB.termCount_poly
  -- block index and offset of a flat term index
  have hdm0 := hdmPF.comp ((subc_polyFueled.comp ((hwidthPF.comp PolyFueled.left).pair
    (PolyFueled.const 1))).pair PolyFueled.right)
  have hdm : PolyFueled _ (fun z : ℕ ↦
      Nat.pair (z.unpair.2 / width z.unpair.1) (z.unpair.2 % width z.unpair.1)) :=
    hdm0.of_eq (fun z ↦ by
      have hw := hwidthPos z.unpair.1
      simp only [Nat.unpair_pair]
      rw [show width z.unpair.1 - 1 + 1 = width z.unpair.1 from by omega])
  have hblk : PolyFueled _ (fun z : ℕ ↦ z.unpair.2 / width z.unpair.1) :=
    (PolyFueled.left.comp hdm).of_eq (fun z ↦ by simp)
  have hoff : PolyFueled _ (fun z : ℕ ↦ z.unpair.2 % width z.unpair.1) :=
    (PolyFueled.right.comp hdm).of_eq (fun z ↦ by simp)
  have hkey : PolyFueled _ (fun z : ℕ ↦ Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1)) :=
    PolyFueled.left.pair hblk
  have hq : PolyFueled _ (fun z : ℕ ↦
      Nat.pair (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
        (z.unpair.2 % width z.unpair.1)) := hkey.pair hoff
  have htest : PolyFueled _ (fun z : ℕ ↦
      (z.unpair.2 % width z.unpair.1 + 1) -
        hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))) :=
    (subc_polyFueled.comp (hoff.succ_comp.pair (htcPF0.comp hkey))).of_eq
      (fun z ↦ by simp)
  have htermCount : ∃ c, PolyFueled c (fun m ↦ cnt m * width m) :=
    ⟨_, (hmulPF.comp (hcntPF.pair hwidthPF)).of_eq (fun m ↦ by simp)⟩
  refine
    { termCount := fun m ↦ cnt m * width m
      coefficient := fun z ↦ EF.mul
        (coeff (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1)))
        (if z.unpair.2 % width z.unpair.1 <
            hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1)) then
          hB.coefficient (Nat.pair (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
            (z.unpair.2 % width z.unpair.1))
        else EF.const 0)
      sentence := fun z ↦
        if z.unpair.2 % width z.unpair.1 <
            hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1)) then
          hB.sentence (Nat.pair (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
            (z.unpair.2 % width z.unpair.1))
        else pad
      termCount_poly := htermCount
      const_poly := ?_
      coefficient_poly := ?_
      sentence_poly := ?_
      terms_eq := ?_
      const_rank := ?_
      coefficient_rank := ?_
      const_closed := ?_
      coefficient_closed := ?_ }
  · refine RpnSpliceStream.of_eq
      ((((hcoeff.append hB.const_poly).append (RpnSpliceStream.tag 3 (by norm_num))).concatVar
        hcntPF).append ((RpnSpliceStream.serialize_const 0).append
          (RpnSpliceStream.repeatTag 2 (by norm_num) hcntPF))) (fun m ↦ ?_)
    rw [AffineCombination.blockSum, foldr_addMul_serialize]
    simp [List.append_assoc]
  · have hif : RpnSpliceStream (fun z ↦
        (if z.unpair.2 % width z.unpair.1 <
            hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1)) then
          hB.coefficient (Nat.pair (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
            (z.unpair.2 % width z.unpair.1))
        else EF.const 0).serialize) := by
      refine RpnSpliceStream.of_eq (RpnSpliceStream.ifZero (hB.coefficient_poly.comp hq)
        (RpnSpliceStream.serialize_const 0) htest) (fun z ↦ ?_)
      by_cases hlt : z.unpair.2 % width z.unpair.1 <
          hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
      · rw [if_pos hlt, if_pos (show _ = 0 from by omega)]
      · rw [if_neg hlt, if_neg (show ¬ _ = 0 from by omega)]
    exact RpnSpliceStream.serialize_mul (hcoeff.comp hkey) hif
  · refine (RpnSentenceCodes.ifZero (hB.sentence_poly.comp hq) hpad htest).of_eq (fun z ↦ ?_)
    by_cases hlt : z.unpair.2 % width z.unpair.1 <
        hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
    · rw [if_pos (show _ = 0 from by omega), if_pos hlt]
    · rw [if_neg (show ¬ _ = 0 from by omega), if_neg hlt]
  · intro m
    rw [AffineCombination.blockSum,
      flatMap_range_map_range (cnt m) (width m) (hwidthPos m)]
    refine List.map_congr_left fun j _ ↦ ?_
    simp only [Nat.unpair_pair]
    rw [hB.terms_eq, getD_map_range_ite]
    by_cases hlt : j % width m < hB.termCount (Nat.pair m (j / width m)) <;>
      simp [hlt, AffineCombination.padEntry]
  · intro m
    rw [AffineCombination.blockSum]
    exact foldr_addMul_rank _ _ _ m (fun k _ ↦ hcoeffRank m k) (fun k _ ↦ hBconstRank m k)
  · intro m j hj
    simp only [Nat.unpair_pair, EF.rank]
    refine Nat.max_le.mpr ⟨hcoeffRank m (j / width m), ?_⟩
    by_cases hlt : j % width m < hB.termCount (Nat.pair m (j / width m))
    · rw [if_pos hlt]
      exact hBcoeffRank m (j / width m) (j % width m) hlt
    · rw [if_neg hlt]
      simp [EF.rank]
  · intro m ρ V
    rw [AffineCombination.blockSum]
    exact foldr_addMul_closed _ _ _ ρ V (fun k _ ↦ hcoeffClosed _ ρ V)
      (fun k _ ↦ hB.const_closed _ ρ V)
  · intro z ρ V
    simp only [EF.denoteWith, EF.denote_mul, Pi.mul_apply]
    rw [hcoeffClosed _ ρ V]
    by_cases hlt : z.unpair.2 % width z.unpair.1 <
        hB.termCount (Nat.pair z.unpair.1 (z.unpair.2 / width z.unpair.1))
    · rw [if_pos hlt, hB.coefficient_closed _ ρ V]
    · rw [if_neg hlt]
      simp [EF.denoteWith]

end AffineCombination

/-! ## First-violator selector: analytic core -/

/-- First-success telescoping: the total weight a first-violator selector spends is
`1 - Π (1 - g j)`, so no normalization (no `safeRecip`, no division) is needed to keep
the day's magnitude budget. -/
lemma firstSuccess_sum (g : ℕ → ℝ) (c : ℕ) :
    ∑ k ∈ Finset.range c, g k * ∏ j ∈ Finset.range k, (1 - g j) =
      1 - ∏ j ∈ Finset.range c, (1 - g j) := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Finset.sum_range_succ, ih, Finset.prod_range_succ]
      ring

lemma firstSuccess_weight_nonneg {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (k : ℕ) :
    0 ≤ g k * ∏ j ∈ Finset.range k, (1 - g j) :=
  mul_nonneg (hg k).1 (Finset.prod_nonneg fun j _ => by have := (hg j).2; linarith)

lemma firstSuccess_sum_le_one {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (c : ℕ) :
    ∑ k ∈ Finset.range c, g k * ∏ j ∈ Finset.range k, (1 - g j) ≤ 1 := by
  rw [firstSuccess_sum]
  have : (0:ℝ) ≤ ∏ j ∈ Finset.range c, (1 - g j) :=
    Finset.prod_nonneg (fun j _ => by have := (hg j).2; linarith)
  linarith

lemma firstSuccess_sum_nonneg {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (c : ℕ) :
    0 ≤ ∑ k ∈ Finset.range c, g k * ∏ j ∈ Finset.range k, (1 - g j) :=
  Finset.sum_nonneg fun k _ => firstSuccess_weight_nonneg hg k

/-- **Forcing.**  Once *some* gate in the window saturates, the selector's total weight is
exactly `1`; since every summand carrying positive weight is at least `δ`, the gated sum
is at least `δ`.  This is the step that makes the terms non-cancelling, and it needs no
minimality of the violator — only the telescoping identity above. -/
lemma firstSuccess_forces {g d : ℕ → ℝ} {δ : ℝ} {c k₀ : ℕ} (hk₀ : k₀ < c)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (hhit : g k₀ = 1)
    (hδ : ∀ k < c, 0 < g k → δ ≤ d k) :
    δ ≤ ∑ k ∈ Finset.range c, (g k * ∏ j ∈ Finset.range k, (1 - g j)) * d k := by
  have hzero : ∏ j ∈ Finset.range c, (1 - g j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.2 hk₀) (by rw [hhit]; ring)
  have htotal : ∑ k ∈ Finset.range c, g k * ∏ j ∈ Finset.range k, (1 - g j) = 1 := by
    rw [firstSuccess_sum, hzero, _root_.sub_zero]
  calc δ = δ * ∑ k ∈ Finset.range c, g k * ∏ j ∈ Finset.range k, (1 - g j) := by
        rw [htotal, mul_one]
    _ = ∑ k ∈ Finset.range c, (g k * ∏ j ∈ Finset.range k, (1 - g j)) * δ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun k hk => ?_
        rcases eq_or_lt_of_le (hg k).1 with hk0 | hk0
        · simp [← hk0]
        · exact mul_le_mul_of_nonneg_left (hδ k (Finset.mem_range.1 hk) hk0)
            (firstSuccess_weight_nonneg hg k)

/-! ## First-violator selector: syntax -/

/-- One factor `1 - g j` of the selector product. -/
private def selectorFactor (g : ℕ → EF) (j : ℕ) : EF :=
  EF.add (EF.const 1) (EF.mul (EF.const (-1)) (g j))

/-- The selector product `Π_{j < k} (1 - g⟨m,j⟩)` for `z = ⟨m,k⟩`. -/
private def selectorProd (g : ℕ → EF) (z : ℕ) : EF :=
  (List.range z.unpair.2).foldr
    (fun j acc ↦ EF.mul (selectorFactor g (Nat.pair z.unpair.1 j)) acc) (EF.const 1)

/-- **First-violator selector weight** `gate⟨m,k⟩ = g⟨m,k⟩ · Π_{j<k} (1 - g⟨m,j⟩)`.  A
division-free device that spreads a *unit* total weight across an unboundedly large
deferral fibre: by `firstSuccess_sum` the weights over a fibre sum to `1 - Π(1-g) ≤ 1`
with no normalization, and by `firstSuccess_forces` a single saturated gate already forces
the whole gated sum. -/
def selectorFeature (g : ℕ → EF) (z : ℕ) : EF :=
  EF.mul (g z) (selectorProd g z)

lemma list_prod_range {M : Type*} [CommMonoid M] (n : ℕ) (F : ℕ → M) :
    ((List.range n).map F).prod = ∏ j ∈ Finset.range n, F j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih,
        Finset.prod_range_succ]
      simp

private lemma foldr_mul_denoteWith (L : List ℕ) (u : ℕ → EF) (ρ : List ℝ) (V : History) :
    (L.foldr (fun j acc ↦ EF.mul (u j) acc) (EF.const 1)).denoteWith ρ V =
      (L.map fun j ↦ (u j).denoteWith ρ V).prod := by
  induction L with
  | nil => simp
  | cons j L ih =>
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, ← ih]
      rfl

private lemma foldr_mul_serialize (L : List ℕ) (u : ℕ → EF) :
    (L.foldr (fun j acc ↦ EF.mul (u j) acc) (EF.const 1)).serialize =
      (L.flatMap fun j ↦ (u j).serialize) ++ (EF.const 1).serialize ++
        List.replicate L.length 3 := by
  induction L with
  | nil => simp
  | cons j L ih =>
      simp only [List.foldr_cons, List.flatMap_cons, List.length_cons]
      rw [show (EF.mul (u j)
            (L.foldr (fun j acc ↦ EF.mul (u j) acc) (EF.const 1))).serialize =
          (u j).serialize ++
            (L.foldr (fun j acc ↦ EF.mul (u j) acc) (EF.const 1)).serialize ++ [3] by
        simp [EF.serialize, List.append_assoc]]
      rw [ih]
      simp [List.replicate_succ', List.append_assoc]

private lemma foldr_mul_rank (L : List ℕ) (u : ℕ → EF) (n : ℕ)
    (hu : ∀ j ∈ L, (u j).rank ≤ n) :
    (L.foldr (fun j acc ↦ EF.mul (u j) acc) (EF.const 1)).rank ≤ n := by
  induction L with
  | nil => simp
  | cons j L ih =>
      simp only [List.foldr_cons, EF.rank]
      exact Nat.max_le.mpr ⟨hu j (by simp), ih fun i hi ↦ hu i (by simp [hi])⟩

@[simp] private lemma selectorFactor_rank (g : ℕ → EF) (j : ℕ) :
    (selectorFactor g j).rank = (g j).rank := by
  simp [selectorFactor, EF.rank]

private lemma selectorFactor_denoteWith (g : ℕ → EF) (j : ℕ) (ρ : List ℝ) (V : History) :
    (selectorFactor g j).denoteWith ρ V = 1 - (g j).denoteWith ρ V := by
  simp only [selectorFactor, EF.denoteWith, Rat.cast_one, Rat.cast_neg, neg_mul, one_mul]
  ring

private lemma selectorFactor_serialize (g : ℕ → EF) (j : ℕ) :
    (selectorFactor g j).serialize =
      (EF.const 1).serialize ++ (EF.const (-1)).serialize ++ (g j).serialize ++ [3, 2] := by
  simp [selectorFactor, EF.serialize, List.append_assoc]

private lemma selectorProd_denoteWith (g : ℕ → EF) (z : ℕ) (ρ : List ℝ) (V : History) :
    (selectorProd g z).denoteWith ρ V =
      ∏ j ∈ Finset.range z.unpair.2, (1 - (g (Nat.pair z.unpair.1 j)).denoteWith ρ V) := by
  rw [selectorProd, foldr_mul_denoteWith, list_prod_range]
  exact Finset.prod_congr rfl fun j _ ↦ selectorFactor_denoteWith _ _ ρ V

lemma selectorFeature_denote (g : ℕ → EF) (m k : ℕ) (V : History) :
    (selectorFeature g (Nat.pair m k)).denote V =
      (g (Nat.pair m k)).denote V *
        ∏ j ∈ Finset.range k, (1 - (g (Nat.pair m j)).denote V) := by
  simp only [selectorFeature, EF.denote, EF.denoteWith]
  rw [show (selectorProd g (Nat.pair m k)).denoteWith [] V =
      ∏ j ∈ Finset.range k, (1 - (g (Nat.pair m j)).denoteWith [] V) by
    simpa using selectorProd_denoteWith g (Nat.pair m k) [] V]

lemma selectorFeature_closed {g : ℕ → EF}
    (hg : ∀ z ρ V, (g z).denoteWith ρ V = (g z).denote V) (z : ℕ) (ρ : List ℝ)
    (V : History) :
    (selectorFeature g z).denoteWith ρ V = (selectorFeature g z).denote V := by
  simp only [selectorFeature, EF.denoteWith, EF.denote_mul, Pi.mul_apply]
  rw [show (g z).denoteWith ρ V = (g z).denote V from hg z ρ V,
    selectorProd_denoteWith g z ρ V,
    show (selectorProd g z).denote V =
      ∏ j ∈ Finset.range z.unpair.2, (1 - (g (Nat.pair z.unpair.1 j)).denote V) from
      selectorProd_denoteWith g z [] V]
  exact congrArg _ (Finset.prod_congr rfl fun j _ ↦ by rw [hg])

lemma selectorFeature_rank {g : ℕ → EF} {m k : ℕ}
    (hg : ∀ j, j ≤ k → (g (Nat.pair m j)).rank ≤ m) :
    (selectorFeature g (Nat.pair m k)).rank ≤ m := by
  simp only [selectorFeature, EF.rank]
  refine Nat.max_le.mpr ⟨hg k le_rfl, ?_⟩
  rw [selectorProd]
  simp only [Nat.unpair_pair]
  exact foldr_mul_rank _ _ _ fun j hj ↦ by
    rw [selectorFactor_rank]
    exact hg j (le_of_lt (List.mem_range.1 hj))

/-- Uniform emission of the selector weights. -/
lemma selectorFeature_polySeg {g : ℕ → EF}
    (hg : RpnSpliceStream fun z ↦ (g z).serialize) :
    RpnSpliceStream fun z ↦ (selectorFeature g z).serialize := by
  have hidx : PolyFueled _ (fun q : ℕ ↦ Nat.pair q.unpair.1.unpair.1 q.unpair.2) :=
    (PolyFueled.left.comp PolyFueled.left).pair PolyFueled.right
  have hfactor : RpnSpliceStream fun q ↦
      (selectorFactor g (Nat.pair q.unpair.1.unpair.1 q.unpair.2)).serialize := by
    refine RpnSpliceStream.of_eq
      ((((RpnSpliceStream.serialize_const 1).append
        (RpnSpliceStream.serialize_const (-1))).append (hg.comp hidx)).append
        ((RpnSpliceStream.tag 3 (by norm_num)).append
          (RpnSpliceStream.tag 2 (by norm_num)))) (fun q ↦ ?_)
    rw [selectorFactor_serialize]
    simp [List.append_assoc]
  have hprod : RpnSpliceStream fun z ↦ (selectorProd g z).serialize := by
    refine RpnSpliceStream.of_eq
      (((hfactor.concatVar PolyFueled.right).append
        ((RpnSpliceStream.serialize_const 1).append
          (RpnSpliceStream.repeatTag 3 (by norm_num) PolyFueled.right)))) (fun z ↦ ?_)
    rw [selectorProd, foldr_mul_serialize]
    simp [List.append_assoc]
  exact RpnSpliceStream.serialize_mul hg hprod

lemma list_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → M) :
    ((List.range n).map F).sum = ∑ j ∈ Finset.range n, F j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

/-! ## Deferral-fibre gating

A day-`m` portfolio that is to settle a *deferred* obligation must carry one term per
source day in the fibre `f⁻¹(m)`, whose size is unbounded when `f` is not injective.  The
day's magnitude budget is one unit, and the gap convergence carries no rate, so no
violation-independent weighting of the fibre can force its individual terms.  The device
that does work is the division-free first-violator selector of `selectorFeature`: gate the
source-`k` block by `ctsInd(δ; |dₖ|, δ)` damped by `Π_{j<k}(1 - …)`, take the whole
package as a `δ`-indexed tower, and read the pointwise conclusion off the union of the
towers' eventual bounds. -/

/-- Emission certificate for a *paired-index* feature family: the member at `z = ⟨m,k⟩` is
legal on the evaluation day `m` — rank `≤ z.unpair.1`, not merely `≤ z` — as well as
polynomially emitted and environment-closed.  The day-indexed `PGenerableWeighting` cannot
state that refinement, and it is exactly what a fibre gate needs in order to be a legal
day-`m` affine coefficient.
Paper node: `def:ece` -/
structure PairedWeighting (A : ℕ → EF) : Prop where
  polySeg : RpnSpliceStream fun z ↦ (A z).serialize
  rank_le : ∀ z, (A z).rank ≤ z.unpair.1
  closed : ∀ z ρ V, (A z).denoteWith ρ V = (A z).denote V

namespace PairedWeighting

lemma ofRatCodes {q : ℕ → ℚ} (hq : PolyRatCodes q) :
    PairedWeighting (fun z ↦ EF.const (q z)) where
  polySeg := RpnSpliceStream.serialize_const_comp hq
  rank_le := by intro z; simp [EF.rank]
  closed := by intro z ρ V; simp [EF.denoteWith]

lemma const (q : ℚ) : PairedWeighting (fun _ ↦ EF.const q) where
  polySeg := RpnSpliceStream.serialize_const q
  rank_le := by intro z; simp [EF.rank]
  closed := by intro z ρ V; simp [EF.denoteWith]

lemma mul {A B : ℕ → EF} (hA : PairedWeighting A) (hB : PairedWeighting B) :
    PairedWeighting (fun z ↦ EF.mul (A z) (B z)) where
  polySeg := RpnSpliceStream.serialize_mul hA.polySeg hB.polySeg
  rank_le := fun z ↦ Nat.max_le.mpr ⟨hA.rank_le z, hB.rank_le z⟩
  closed := by
    intro z ρ V
    simp only [EF.denoteWith, EF.denote_mul, Pi.mul_apply]
    rw [hA.closed z ρ V, hB.closed z ρ V]

lemma add {A B : ℕ → EF} (hA : PairedWeighting A) (hB : PairedWeighting B) :
    PairedWeighting (fun z ↦ EF.add (A z) (B z)) where
  polySeg := RpnSpliceStream.serialize_add hA.polySeg hB.polySeg
  rank_le := fun z ↦ Nat.max_le.mpr ⟨hA.rank_le z, hB.rank_le z⟩
  closed := by
    intro z ρ V
    simp only [EF.denoteWith, EF.denote_add, Pi.add_apply]
    rw [hA.closed z ρ V, hB.closed z ρ V]

lemma max {A B : ℕ → EF} (hA : PairedWeighting A) (hB : PairedWeighting B) :
    PairedWeighting (fun z ↦ EF.max (A z) (B z)) where
  polySeg := RpnSpliceStream.serialize_max hA.polySeg hB.polySeg
  rank_le := fun z ↦ Nat.max_le.mpr ⟨hA.rank_le z, hB.rank_le z⟩
  closed := by
    intro z ρ V
    simp only [EF.denoteWith, EF.denote_max]
    rw [hA.closed z ρ V, hB.closed z ρ V]

lemma clip01 {A : ℕ → EF} (hA : PairedWeighting A) :
    PairedWeighting (fun z ↦ _root_.LogicalInduction.clip01 (A z)) := by
  have h := ((PairedWeighting.const 0).max
    (((PairedWeighting.const (-1)).mul (((PairedWeighting.const (-1)).mul
      (PairedWeighting.const 1)).max ((PairedWeighting.const (-1)).mul hA)))))
  exact h

lemma ctsInd {δ : ℕ → ℚ} (hδinv : PolyRatCodes (fun z ↦ 1 / δ z))
    {x y : ℕ → EF} (hx : PairedWeighting x) (hy : PairedWeighting y) :
    PairedWeighting (ctsIndFeature δ x y) :=
  PairedWeighting.clip01
    ((hx.add ((PairedWeighting.const (-1)).mul hy)).mul (PairedWeighting.ofRatCodes hδinv))

lemma selector {A : ℕ → EF} (hA : PairedWeighting A) :
    PairedWeighting (selectorFeature A) where
  polySeg := selectorFeature_polySeg hA.polySeg
  rank_le := by
    intro z
    have := selectorFeature_rank (g := A) (m := z.unpair.1) (k := z.unpair.2)
      (fun j _ ↦ by simpa using hA.rank_le (Nat.pair z.unpair.1 j))
    simpa using this
  closed := selectorFeature_closed hA.closed

/-- A paired-index emission certificate is in particular a day-indexed one: the paired
rank bound `≤ z.unpair.1` implies the day bound `≤ z`. -/
lemma toPGenerable {A : ℕ → EF} (h : PairedWeighting A) :
    PGenerableWeighting A where
  polySeg := h.polySeg
  rank_le := fun z ↦ (h.rank_le z).trans (Nat.unpair_left_le z)
  closed := h.closed

/-- A day-indexed generated feature, read at the *evaluation day* of a paired index, is a
paired-index feature. -/
lemma ofPGenerableFst {A : ℕ → EF} (h : PGenerableWeighting A) :
    PairedWeighting (fun z ↦ A z.unpair.1) where
  polySeg := h.polySeg.comp PolyFueled.left
  rank_le := fun _ ↦ h.rank_le _
  closed := fun _ ρ V ↦ h.closed _ ρ V

/-- The source index of a paired index, clamped to the evaluation day.  On the fibre the
source is below the day, so the clamp is invisible there; off it, it keeps the emitted
expression legal on day `z.unpair.1`. -/
lemma clampedSource_polyFueled :
    ∃ c, PolyFueled c (fun z : ℕ ↦ min z.unpair.2 z.unpair.1) :=
  ⟨_, (subc_polyFueled.comp (PolyFueled.right.pair
    (subc_polyFueled.comp (PolyFueled.right.pair PolyFueled.left)))).of_eq
      (fun z ↦ by simp; omega)⟩

/-- A day-indexed generated feature read at the *clamped source* index of a paired index.
This is how source-indexed confidence data (a threshold, a probability expression) becomes
a legal day-`z.unpair.1` coefficient. -/
lemma ofPGenerableClamped {A : ℕ → EF} (h : PGenerableWeighting A) :
    PairedWeighting (fun z ↦ A (min z.unpair.2 z.unpair.1)) where
  polySeg := h.polySeg.comp (Classical.choose_spec clampedSource_polyFueled)
  rank_le := fun _ ↦ (h.rank_le _).trans (min_le_right _ _)
  closed := fun _ ρ V ↦ h.closed _ ρ V


end PairedWeighting

namespace DeferralFibre

/-- Day-`m` price feature of the source-`k` block, for `z = ⟨m,k⟩`. -/
def priceFeat (Bs : ℕ → AffineCombination) (z : ℕ) : EF :=
  (Bs z).priceFeature z.unpair.1

/-- Positive part of the block's day-`m` price. -/
def gapPos (Bs : ℕ → AffineCombination) (z : ℕ) : EF :=
  EF.max (priceFeat Bs z) (EF.const 0)

/-- Negative part of the block's day-`m` price. -/
def gapNeg (Bs : ℕ → AffineCombination) (z : ℕ) : EF :=
  EF.max (EF.mul (EF.const (-1)) (priceFeat Bs z)) (EF.const 0)

/-- The `[f k = m]` fibre-membership flag as a closed constant feature. -/
def matchFeat (f : DeferralFunction) (a degree z : ℕ) : EF :=
  EF.const ((FeedbackEmission.scheduledMatch f a degree z : ℕ) : ℚ)

/-- Fibre-gated continuous threshold on one side of the gap. -/
def gateBase (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (d : ℕ → EF) (z : ℕ) : EF :=
  EF.mul (matchFeat f a degree z)
    (ctsIndFeature (fun _ ↦ δ) d (fun _ ↦ EF.const δ) z)

/-- Two-sided first-violator coefficient: the positive-side selector minus the
negative-side selector, normalised by `1/(2C)`. -/
def gateCoeff (f : DeferralFunction) (a degree : ℕ) (δ C : ℚ)
    (Bs : ℕ → AffineCombination) (z : ℕ) : EF :=
  EF.mul (EF.const (1 / (2 * C)))
    (EF.add (selectorFeature (gateBase f a degree δ (gapPos Bs)) z)
      (EF.mul (EF.const (-1))
        (selectorFeature (gateBase f a degree δ (gapNeg Bs)) z)))

variable {Bs : ℕ → AffineCombination}

lemma priceFeat_denote (Bs : ℕ → AffineCombination) (z : ℕ) (V : History) :
    (priceFeat Bs z).denote V = (Bs z).price V z.unpair.1 :=
  AffineCombination.priceFeature_denote _ _ _

lemma priceFeat_paired (hB : AffineCombination.PolySequence Bs)
    (hconstRank : ∀ z, (Bs z).const.rank ≤ z.unpair.1)
    (htermRank : ∀ z, ∀ p ∈ (Bs z).terms, p.1.rank ≤ z.unpair.1) :
    PairedWeighting (priceFeat Bs) where
  polySeg := (hB.priceFeature_polySeg.comp
    (PolyFueled.id.pair PolyFueled.left)).of_eq (fun z ↦ by simp [priceFeat])
  rank_le := fun z ↦ AffineCombination.priceFeature_rank (Bs z) le_rfl
    (hconstRank z) (htermRank z)
  closed := fun z ρ V ↦ hB.priceFeature_closed z z.unpair.1 ρ V

lemma gapPos_denote (Bs : ℕ → AffineCombination) (z : ℕ) (V : History) :
    (gapPos Bs z).denote V = Max.max ((Bs z).price V z.unpair.1) 0 := by
  simp [gapPos, priceFeat_denote]

lemma gapNeg_denote (Bs : ℕ → AffineCombination) (z : ℕ) (V : History) :
    (gapNeg Bs z).denote V = Max.max (-((Bs z).price V z.unpair.1)) 0 := by
  simp [gapNeg, priceFeat_denote]

lemma matchFeat_denote (f : DeferralFunction) (a degree z : ℕ) (V : History) :
    (matchFeat f a degree z).denote V =
      ((FeedbackEmission.scheduledMatch f a degree z : ℕ) : ℝ) := by
  simp [matchFeat]

lemma matchFeat_paired (f : DeferralFunction) (a degree : ℕ) :
    PairedWeighting (matchFeat f a degree) :=
  PairedWeighting.ofRatCodes
    (ratNatCast_codes_of_polyFueled
      (Classical.choose_spec (FeedbackEmission.scheduledMatch_polyFueled f a degree)))

lemma gateBase_denote (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (d : ℕ → EF) (z : ℕ) (V : History) :
    (gateBase f a degree δ d z).denote V =
      ((FeedbackEmission.scheduledMatch f a degree z : ℕ) : ℝ) *
        ctsInd δ ((d z).denote V) (δ : ℝ) := by
  simp only [gateBase, EF.denote_mul, Pi.mul_apply, matchFeat_denote]
  rw [ctsIndFeature_denote (fun _ ↦ δ) d _ (fun _ ↦ hδ) V z]
  simp

lemma gateBase_mem (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (d : ℕ → EF) (z : ℕ) (V : History) :
    0 ≤ (gateBase f a degree δ d z).denote V ∧
      (gateBase f a degree δ d z).denote V ≤ 1 := by
  rw [gateBase_denote f a degree δ hδ d z V]
  have hI := ctsInd_mem_Icc δ ((d z).denote V) (δ : ℝ)
  rcases FeedbackEmission.scheduledMatch_zero_or_one f a degree z with h | h
  · rw [h]; simp
  · rw [h]; simpa using ⟨hI.1, hI.2⟩

lemma gateBase_pos (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (d : ℕ → EF) (z : ℕ) (V : History)
    (h : 0 < (gateBase f a degree δ d z).denote V) :
    (δ : ℝ) < (d z).denote V := by
  rw [gateBase_denote f a degree δ hδ d z V] at h
  by_contra hle
  rw [ctsInd_eq_zero_of_le δ _ _ hδ (not_lt.1 hle), mul_zero] at h
  exact absurd h (lt_irrefl 0)

lemma gateBase_eq_one (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (d : ℕ → EF) (z : ℕ) (V : History)
    (hmatch : FeedbackEmission.scheduledMatch f a degree z = 1)
    (hbig : 2 * (δ : ℝ) ≤ (d z).denote V) :
    (gateBase f a degree δ d z).denote V = 1 := by
  rw [gateBase_denote f a degree δ hδ d z V, hmatch,
    ctsInd_eq_one_of_le_sub δ _ _ hδ (by linarith)]
  simp

lemma gateBase_paired (f : DeferralFunction) (a degree : ℕ) {δ : ℚ}
    (hδinv : PolyRatCodes (fun _ : ℕ ↦ 1 / δ)) {d : ℕ → EF} (hd : PairedWeighting d) :
    PairedWeighting (gateBase f a degree δ d) :=
  (matchFeat_paired f a degree).mul
    (PairedWeighting.ctsInd hδinv hd (PairedWeighting.const δ))

lemma gateCoeff_paired (f : DeferralFunction) (a degree : ℕ) {δ C : ℚ}
    (hδinv : PolyRatCodes (fun _ : ℕ ↦ 1 / δ))
    (hB : AffineCombination.PolySequence Bs)
    (hconstRank : ∀ z, (Bs z).const.rank ≤ z.unpair.1)
    (htermRank : ∀ z, ∀ p ∈ (Bs z).terms, p.1.rank ≤ z.unpair.1) :
    PairedWeighting (gateCoeff f a degree δ C Bs) := by
  have hprice := priceFeat_paired hB hconstRank htermRank
  have hpos : PairedWeighting (gapPos Bs) := hprice.max (PairedWeighting.const 0)
  have hneg : PairedWeighting (gapNeg Bs) :=
    ((PairedWeighting.const (-1)).mul hprice).max (PairedWeighting.const 0)
  exact (PairedWeighting.const (1 / (2 * C))).mul
    (((gateBase_paired f a degree hδinv hpos).selector).add
      ((PairedWeighting.const (-1)).mul
        ((gateBase_paired f a degree hδinv hneg).selector)))

/-- Only finitely many days are scheduled from below `N`, so past the largest of them every
element of every fibre is at or above `N`.  Injectivity-free: the constraint is only that
`f 0, …, f (N-1)` are finitely many days. -/
lemma exists_fibre_floor (f : DeferralFunction) (N : ℕ) :
    ∃ M, ∀ m, M ≤ m → ∀ k, f k = m → N ≤ k := by
  refine ⟨(Finset.range N).sup (fun k ↦ f k) + 1, fun m hm k hk ↦ ?_⟩
  by_contra hnot
  have hlt : k < N := Nat.lt_of_not_ge hnot
  have hle : f k ≤ (Finset.range N).sup (fun j ↦ f j) :=
    Finset.le_sup (f := fun j ↦ f j) (Finset.mem_range.2 hlt)
  omega

/-- **Fibre-gated deferred coherence, one precision.**  For a single gate width `δ` the
first-violator selector packages the whole fibre into one day-`m` portfolio of unit
magnitude, so affine coherence forces the day-`m` price to zero; a saturated gate would
keep that price at `δ/(2C)`, so eventually no fibre element's gap reaches `2δ`. -/
lemma fibre_price_eventually_small
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    {Bs : ℕ → AffineCombination} (hB : AffineCombination.PolySequence Bs)
    (hconstRank : ∀ z, (Bs z).const.rank ≤ z.unpair.1)
    (htermRank : ∀ z, ∀ p ∈ (Bs z).terms, p.1.rank ≤ z.unpair.1)
    {width : ℕ → ℕ} (hwidth : ∃ c, PolyFueled c width) (hwidthPos : ∀ m, 0 < width m)
    (hwide : ∀ m k, k < m → (Bs (Nat.pair m k)).terms.length ≤ width m)
    {C : ℚ} (hC : 0 < C)
    (hmag : ∀ z, (Bs z).magnitude P ≤ (C : ℝ))
    (hbdd : ∀ z day, |(Bs z).price P day| ≤ (C : ℝ))
    (hsmall : ∀ ε > 0, ∃ N, ∀ m k, N ≤ k → k < m → f k = m →
      ∀ v : PCWorld, v.ConsistentWithTheory DP →
        |(Bs (Nat.pair m k)).value P v.payout| ≤ ε)
    {δ : ℚ} (hδ : 0 < δ) :
    ∀ᶠ m in atTop, ∀ k, k < m → f k = m →
      |(Bs (Nat.pair m k)).price P m| < 2 * (δ : ℝ) := by
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδinv : PolyRatCodes (fun _ : ℕ ↦ 1 / δ) :=
    ⟨_, PolyFueled.const (Encodable.encode (1 / δ))⟩
  have hnorm : (0 : ℝ) < ((1 / (2 * C) : ℚ) : ℝ) := by
    have : (0 : ℚ) < 1 / (2 * C) := by positivity
    exact_mod_cast this
  -- the two gate families and the affine coefficient
  set gP : ℕ → EF := gateBase f a degree δ (gapPos Bs) with hgPdef
  set gN : ℕ → EF := gateBase f a degree δ (gapNeg Bs) with hgNdef
  set coeff : ℕ → EF := gateCoeff f a degree δ C Bs with hcoeffdef
  have hcoeffP : PairedWeighting coeff :=
    gateCoeff_paired f a degree hδinv hB hconstRank htermRank
  -- real-valued shorthands
  set pr : ℕ → ℕ → ℝ := fun m k ↦ (Bs (Nat.pair m k)).price P m with hprdef
  set pos : ℕ → ℕ → ℝ := fun m k ↦ Max.max (pr m k) 0 with hposdef
  set neg : ℕ → ℕ → ℝ := fun m k ↦ Max.max (-(pr m k)) 0 with hnegdef
  set bP : ℕ → ℕ → ℝ := fun m k ↦ (gP (Nat.pair m k)).denote P with hbPdef
  set bN : ℕ → ℕ → ℝ := fun m k ↦ (gN (Nat.pair m k)).denote P with hbNdef
  set wP : ℕ → ℕ → ℝ := fun m k ↦ bP m k * ∏ j ∈ Finset.range k, (1 - bP m j) with hwPdef
  set wN : ℕ → ℕ → ℝ := fun m k ↦ bN m k * ∏ j ∈ Finset.range k, (1 - bN m j) with hwNdef
  have hpr : ∀ m k, pr m k = (Bs (Nat.pair m k)).price P m := fun _ _ ↦ rfl
  have hpos : ∀ m k, pos m k = Max.max (pr m k) 0 := fun _ _ ↦ rfl
  have hneg : ∀ m k, neg m k = Max.max (-(pr m k)) 0 := fun _ _ ↦ rfl
  have hgapPos : ∀ m k, (gapPos Bs (Nat.pair m k)).denote P = pos m k := by
    intro m k; rw [gapPos_denote, hpos m k, hpr m k]; simp
  have hgapNeg : ∀ m k, (gapNeg Bs (Nat.pair m k)).denote P = neg m k := by
    intro m k; rw [gapNeg_denote, hneg m k, hpr m k]; simp
  have hbPeq : ∀ m k, bP m k = (gP (Nat.pair m k)).denote P := fun _ _ ↦ rfl
  have hbNeq : ∀ m k, bN m k = (gN (Nat.pair m k)).denote P := fun _ _ ↦ rfl
  have hwP : ∀ m k, wP m k = bP m k * ∏ j ∈ Finset.range k, (1 - bP m j) := fun _ _ ↦ rfl
  have hwN : ∀ m k, wN m k = bN m k * ∏ j ∈ Finset.range k, (1 - bN m j) := fun _ _ ↦ rfl
  have hbPmem : ∀ m k, 0 ≤ bP m k ∧ bP m k ≤ 1 := fun m k ↦
    gateBase_mem f a degree δ hδ _ _ P
  have hbNmem : ∀ m k, 0 ≤ bN m k ∧ bN m k ≤ 1 := fun m k ↦
    gateBase_mem f a degree δ hδ _ _ P
  have hwPnonneg : ∀ m k, 0 ≤ wP m k := fun m k ↦
    firstSuccess_weight_nonneg (hbPmem m) k
  have hwNnonneg : ∀ m k, 0 ≤ wN m k := fun m k ↦
    firstSuccess_weight_nonneg (hbNmem m) k
  have hwPsum : ∀ m, ∑ k ∈ Finset.range m, wP m k ≤ 1 := fun m ↦
    firstSuccess_sum_le_one (hbPmem m) m
  have hwNsum : ∀ m, ∑ k ∈ Finset.range m, wN m k ≤ 1 := fun m ↦
    firstSuccess_sum_le_one (hbNmem m) m
  have hcoeffDen : ∀ m k, (coeff (Nat.pair m k)).denote P =
      ((1 / (2 * C) : ℚ) : ℝ) * (wP m k - wN m k) := by
    intro m k
    rw [hwP m k, hwN m k, hbPeq m k, hbNeq m k, hcoeffdef]
    simp only [gateCoeff, EF.denote_mul, EF.denote_add, EF.denote_const,
      Pi.mul_apply, Pi.add_apply, hgPdef, hgNdef, selectorFeature_denote]
    push_cast
    ring
  -- gates only fire inside the fibre
  have hbP_match : ∀ m k, FeedbackEmission.scheduledMatch f a degree (Nat.pair m k) = 0 →
      bP m k = 0 := by
    intro m k h
    rw [hbPeq m k, hgPdef, gateBase_denote f a degree δ hδ _ _ P, h]
    simp
  have hbN_match : ∀ m k, FeedbackEmission.scheduledMatch f a degree (Nat.pair m k) = 0 →
      bN m k = 0 := by
    intro m k h
    rw [hbNeq m k, hgNdef, gateBase_denote f a degree δ hδ _ _ P, h]
    simp
  have hcoeff_fibre : ∀ m k, (coeff (Nat.pair m k)).denote P ≠ 0 → f k = m := by
    intro m k hne
    rcases FeedbackEmission.scheduledMatch_zero_or_one f a degree (Nat.pair m k) with h | h
    · exfalso
      rw [hcoeffDen m k, hwP m k, hwN m k, hbP_match m k h, hbN_match m k h] at hne
      simp at hne
    · exact (FeedbackEmission.scheduledMatch_eq_one_iff f hspec m k).1 h
  -- gate positivity forces the gap past δ
  have hbP_forces : ∀ m k, 0 < bP m k → (δ : ℝ) ≤ pos m k := by
    intro m k h
    have := gateBase_pos f a degree δ hδ (gapPos Bs) (Nat.pair m k) P h
    rw [hgapPos m k] at this
    exact this.le
  have hbN_forces : ∀ m k, 0 < bN m k → (δ : ℝ) ≤ neg m k := by
    intro m k h
    have := gateBase_pos f a degree δ hδ (gapNeg Bs) (Nat.pair m k) P h
    rw [hgapNeg m k] at this
    exact this.le
  -- signed summand splits into two non-cancelling halves
  have hsplit : ∀ m k, (wP m k - wN m k) * pr m k = wP m k * pos m k + wN m k * neg m k := by
    intro m k
    by_cases hge : 0 ≤ pr m k
    · have e1 : pos m k = pr m k := by rw [hpos m k]; exact max_eq_left hge
      have e2 : neg m k = 0 := by rw [hneg m k]; exact max_eq_right (by linarith)
      have hwN0 : wN m k = 0 := by
        rcases eq_or_lt_of_le (hbNmem m k).1 with h0 | h0
        · rw [hwN m k, ← h0, zero_mul]
        · exact absurd (hbN_forces m k h0) (by rw [e2]; linarith)
      rw [e1, e2, hwN0]; ring
    · have hlt : pr m k < 0 := by linarith [not_le.mp hge]
      have e1 : pos m k = 0 := by rw [hpos m k]; exact max_eq_right hlt.le
      have e2 : neg m k = -(pr m k) := by rw [hneg m k]; exact max_eq_left (by linarith)
      have hwP0 : wP m k = 0 := by
        rcases eq_or_lt_of_le (hbPmem m k).1 with h0 | h0
        · rw [hwP m k, ← h0, zero_mul]
        · exact absurd (hbP_forces m k h0) (by rw [e1]; linarith)
      rw [e1, e2, hwP0]; ring
  -- the day-indexed portfolio
  have hBconstRank : ∀ m k, (Bs (Nat.pair m k)).const.rank ≤ m := fun m k ↦ by
    simpa using hconstRank (Nat.pair m k)
  have hBcoeffRank : ∀ m k o, o < hB.termCount (Nat.pair m k) →
      (hB.coefficient (Nat.pair (Nat.pair m k) o)).rank ≤ m := by
    intro m k o ho
    have hmem : (hB.coefficient (Nat.pair (Nat.pair m k) o),
        hB.sentence (Nat.pair (Nat.pair m k) o)) ∈ (Bs (Nat.pair m k)).terms := by
      rw [hB.terms_eq]
      exact List.mem_map.2 ⟨o, List.mem_range.2 ho, rfl⟩
    simpa using htermRank (Nat.pair m k) _ hmem
  set family : ℕ → AffineCombination :=
    AffineCombination.blockSum Bs coeff (fun m ↦ m) width (hB.sentence 0) with hfamdef
  have hfamilyPoly : AffineCombination.PolySequence family :=
    hB.blockSum hcoeffP.polySeg hcoeffP.closed
      (fun m k ↦ by simpa using hcoeffP.rank_le (Nat.pair m k))
      ⟨_, PolyFueled.id⟩ hwidth hwidthPos hBconstRank hBcoeffRank
      (hB.sentence 0) (hB.sentence_poly.comp (PolyFueled.const 0))
  have hwq : ∀ m, ∀ k < m, (Bs (Nat.pair m k)).terms.length ≤ width m :=
    fun m k hk ↦ hwide m k hk
  have hfamPrice : ∀ m day, (family m).price P day =
      ∑ k ∈ Finset.range m, (coeff (Nat.pair m k)).denote P *
        (Bs (Nat.pair m k)).price P day := by
    intro m day
    rw [hfamdef, AffineCombination.blockSum_price _ _ _ _ _ _ _ _ (hwq m),
      list_sum_range]
  have hfamMag : ∀ m, (family m).magnitude P =
      ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P| *
        (Bs (Nat.pair m k)).magnitude P := by
    intro m
    rw [hfamdef, AffineCombination.blockSum_magnitude _ _ _ _ _ _ _ (hwq m),
      list_sum_range]
  have hfamValue : ∀ m (w : Valuation), (family m).value P w =
      ∑ k ∈ Finset.range m, (coeff (Nat.pair m k)).denote P *
        (Bs (Nat.pair m k)).value P w := by
    intro m w
    rw [hfamdef, AffineCombination.blockSum_value _ _ _ _ _ _ _ _ (hwq m),
      list_sum_range]
  have hcoeffAbs : ∀ m k, |(coeff (Nat.pair m k)).denote P| ≤
      ((1 / (2 * C) : ℚ) : ℝ) * (wP m k + wN m k) := by
    intro m k
    rw [hcoeffDen m k, abs_mul, abs_of_pos hnorm]
    refine mul_le_mul_of_nonneg_left ?_ hnorm.le
    rw [abs_sub_le_iff]
    constructor <;> [linarith [hwNnonneg m k]; linarith [hwPnonneg m k]]
  have hcoeffSum : ∀ m, ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P| ≤
      ((1 / (2 * C) : ℚ) : ℝ) * 2 := by
    intro m
    calc ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P|
        ≤ ∑ k ∈ Finset.range m, ((1 / (2 * C) : ℚ) : ℝ) * (wP m k + wN m k) :=
          Finset.sum_le_sum fun k _ ↦ hcoeffAbs m k
      _ = ((1 / (2 * C) : ℚ) : ℝ) *
            ((∑ k ∈ Finset.range m, wP m k) + ∑ k ∈ Finset.range m, wN m k) := by
          rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ ↦ by ring
      _ ≤ ((1 / (2 * C) : ℚ) : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left (by linarith [hwPsum m, hwNsum m]) hnorm.le
  have hnorm2 : ((1 / (2 * C) : ℚ) : ℝ) * 2 * (C : ℝ) = 1 := by
    have : ((1 / (2 * C) : ℚ) : ℝ) = 1 / (2 * (C : ℝ)) := by push_cast; ring
    rw [this]; field_simp
  have q : CompletedAffineQuoteApprox P DP (fun m ↦ (family m).price P m) :=
    { family := family
      poly := hfamilyPoly
      scale := 1
      scale_pos := by norm_num
      current_price := fun m ↦ by norm_num
      bounded := ⟨1, zero_le_one, fun m day ↦ by
        rw [hfamPrice m day]
        calc |∑ k ∈ Finset.range m, (coeff (Nat.pair m k)).denote P *
                (Bs (Nat.pair m k)).price P day|
            ≤ ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P *
                (Bs (Nat.pair m k)).price P day| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P| * (C : ℝ) := by
              refine Finset.sum_le_sum fun k _ ↦ ?_
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hbdd _ day) (abs_nonneg _)
          _ = (∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P|) * (C : ℝ) := by
              rw [Finset.sum_mul]
          _ ≤ ((1 / (2 * C) : ℚ) : ℝ) * 2 * (C : ℝ) :=
              mul_le_mul_of_nonneg_right (hcoeffSum m) hCR.le
          _ = 1 := hnorm2⟩
      magnitude_le_one := fun m ↦ by
        rw [hfamMag m]
        calc ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P| *
              (Bs (Nat.pair m k)).magnitude P
            ≤ ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P| * (C : ℝ) :=
              Finset.sum_le_sum fun k _ ↦
                mul_le_mul_of_nonneg_left (hmag _) (abs_nonneg _)
          _ = (∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P|) * (C : ℝ) := by
              rw [Finset.sum_mul]
          _ ≤ ((1 / (2 * C) : ℚ) : ℝ) * 2 * (C : ℝ) :=
              mul_le_mul_of_nonneg_right (hcoeffSum m) hCR.le
          _ = 1 := hnorm2
      theory_coherent := by
        intro ε hε
        obtain ⟨N, hN⟩ := hsmall ((C : ℝ) * ε) (by positivity)
        obtain ⟨M, hM⟩ := exists_fibre_floor f N
        refine eventually_atTop.2 ⟨M, fun m hm v hv ↦ ?_⟩
        rw [hfamValue m v.payout]
        calc |∑ k ∈ Finset.range m, (coeff (Nat.pair m k)).denote P *
                (Bs (Nat.pair m k)).value P v.payout|
            ≤ ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P *
                (Bs (Nat.pair m k)).value P v.payout| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range m,
                |(coeff (Nat.pair m k)).denote P| * ((C : ℝ) * ε) := by
              refine Finset.sum_le_sum fun k hk ↦ ?_
              rw [abs_mul]
              by_cases hz : (coeff (Nat.pair m k)).denote P = 0
              · simp [hz]
              · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                have hfk := hcoeff_fibre m k hz
                exact hN m k (hM m hm k hfk) (Finset.mem_range.1 hk) hfk v hv
          _ = (∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P|) *
                ((C : ℝ) * ε) := by rw [Finset.sum_mul]
          _ ≤ ((1 / (2 * C) : ℚ) : ℝ) * 2 * ((C : ℝ) * ε) :=
              mul_le_mul_of_nonneg_right (hcoeffSum m) (by positivity)
          _ = ε := by rw [← mul_assoc, hnorm2, one_mul] }
  -- the gated day-`m` price converges, and a saturated gate would keep it at `δ/(2C)`
  have hgap : Tendsto (fun m ↦ (family m).price P m) atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero] using q.gap_asympEq_zero hworld
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hgap
    (((1 / (2 * C) : ℚ) : ℝ) * (δ : ℝ)) (by positivity)
  refine eventually_atTop.2 ⟨M, fun m hm k hk hfk ↦ ?_⟩
  by_contra hbig
  rw [not_lt] at hbig
  have hmatch : FeedbackEmission.scheduledMatch f a degree (Nat.pair m k) = 1 :=
    (FeedbackEmission.scheduledMatch_eq_one_iff f hspec m k).2 hfk
  have hsum_eq : (family m).price P m =
      ((1 / (2 * C) : ℚ) : ℝ) *
        ((∑ j ∈ Finset.range m, wP m j * pos m j) +
          ∑ j ∈ Finset.range m, wN m j * neg m j) := by
    rw [hfamPrice m m, mul_add, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hcoeffDen m j, show (Bs (Nat.pair m j)).price P m = pr m j from rfl, mul_assoc,
      hsplit m j]
    ring
  have hlarge : ((1 / (2 * C) : ℚ) : ℝ) * (δ : ℝ) ≤ (family m).price P m := by
    rw [hsum_eq]
    refine mul_le_mul_of_nonneg_left ?_ hnorm.le
    have hbig' : 2 * (δ : ℝ) ≤ |pr m k| := hbig
    rcases le_abs.mp hbig' with hup | hdown
    · have hposk : pos m k = pr m k := by
        rw [hpos m k]; exact max_eq_left (by linarith)
      have hhit : bP m k = 1 := by
        rw [hbPeq m k, hgPdef]
        exact gateBase_eq_one f a degree δ hδ _ _ P hmatch
          (by rw [hgapPos m k, hposk]; linarith)
      have h1 : (δ : ℝ) ≤ ∑ j ∈ Finset.range m, wP m j * pos m j :=
        firstSuccess_forces hk (hbPmem m) hhit (fun j _ hj ↦ hbP_forces m j hj)
      have h2 : 0 ≤ ∑ j ∈ Finset.range m, wN m j * neg m j :=
        Finset.sum_nonneg fun j _ ↦ mul_nonneg (hwNnonneg m j) (le_max_right _ _)
      linarith
    · have hnegk : neg m k = -(pr m k) := by
        rw [hneg m k]; exact max_eq_left (by linarith)
      have hhit : bN m k = 1 := by
        rw [hbNeq m k, hgNdef]
        exact gateBase_eq_one f a degree δ hδ _ _ P hmatch
          (by rw [hgapNeg m k, hnegk]; linarith)
      have h1 : (δ : ℝ) ≤ ∑ j ∈ Finset.range m, wN m j * neg m j :=
        firstSuccess_forces hk (hbNmem m) hhit (fun j _ hj ↦ hbN_forces m j hj)
      have h2 : 0 ≤ ∑ j ∈ Finset.range m, wP m j * pos m j :=
        Finset.sum_nonneg fun j _ ↦ mul_nonneg (hwPnonneg m j) (le_max_right _ _)
      linarith
  have hclose := hM m hm
  rw [Real.dist_eq, _root_.sub_zero, abs_lt] at hclose
  linarith [hclose.2]

/-- **Deferred price coherence without injectivity.**  For every deferral function
satisfying only `f n > n` plus poly-clocked emission — no injectivity, no monotonicity —
a uniformly small completed-theory block family has vanishing deferred price along the
diagonal `n ↦ ⟨f n, n⟩`. -/
lemma deferred_block_price_tendsto_zero
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    {Bs : ℕ → AffineCombination} (hB : AffineCombination.PolySequence Bs)
    (hconstRank : ∀ z, (Bs z).const.rank ≤ z.unpair.1)
    (htermRank : ∀ z, ∀ p ∈ (Bs z).terms, p.1.rank ≤ z.unpair.1)
    {width : ℕ → ℕ} (hwidth : ∃ c, PolyFueled c width) (hwidthPos : ∀ m, 0 < width m)
    (hwide : ∀ m k, k < m → (Bs (Nat.pair m k)).terms.length ≤ width m)
    {C : ℚ} (hC : 0 < C)
    (hmag : ∀ z, (Bs z).magnitude P ≤ (C : ℝ))
    (hbdd : ∀ z day, |(Bs z).price P day| ≤ (C : ℝ))
    (hsmall : ∀ ε > 0, ∃ N, ∀ m k, N ≤ k → k < m → f k = m →
      ∀ v : PCWorld, v.ConsistentWithTheory DP →
        |(Bs (Nat.pair m k)).value P v.payout| ≤ ε) :
    Tendsto (fun n ↦ (Bs (Nat.pair (f n) n)).price P (f n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδpos, hδsmall⟩ : ∃ δ : ℚ, 0 < δ ∧ 2 * (δ : ℝ) < ε := by
    obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn (show (0:ℝ) < ε / 3 from by linarith)
    refine ⟨q, by exact_mod_cast hq0, ?_⟩
    have : (q : ℝ) < ε / 3 := hqε
    linarith
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (fibre_price_eventually_small hworld f hspec hB hconstRank htermRank hwidth
      hwidthPos hwide hC hmag hbdd hsmall hδpos)
  refine ⟨M, fun n hn ↦ ?_⟩
  have hfn : M ≤ f n := le_trans hn (f.lt n).le
  have := hM (f n) hfn n (f.lt n) rfl
  rw [Real.dist_eq, _root_.sub_zero]
  linarith

end DeferralFibre

/-- Difference between two threshold meshes of the same represented LUV. -/
def LUV.crossPrecisionAffine (X : ℕ → LUV) (low high : ℕ → ℕ)
    (n : ℕ) : AffineCombination where
  const := EF.const 0
  terms := ((X n).expectAffine (low n)).terms ++
    ((X n).expectAffine (high n)).terms.map fun p ↦
      (EF.mul (EF.const (-1)) p.1, p.2)

noncomputable def LUV.crossPrecisionAffine_polySequence
    (X : ℕ → LUV) (low high : ℕ → ℕ)
    (hX : LUV.RpnThresholdCodeSeq X)
    (hlow : ∃ c, PolyFueled c low) (hhigh : ∃ c, PolyFueled c high) :
    AffineCombination.PolySequence (LUV.crossPrecisionAffine X low high) := by
  let clow := Classical.choose hlow
  have hlow := Classical.choose_spec hlow
  let chigh := Classical.choose hhigh
  have hhigh := Classical.choose_spec hhigh
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  let cadd := Classical.choose addc_polyFueled
  have hadd := Classical.choose_spec addc_polyFueled
  have hn := PolyFueled.left
  have hj := PolyFueled.right
  have hlo := hlow.comp hn
  have hhi := hhigh.comp hn
  have hcount := hadd.comp (hlow.pair hhigh)
  have htest := subc_polyFueled.comp (hj.succ_comp.pair hlo)
  have hcount' : PolyFueled _ (fun n ↦ low n + high n) :=
    hcount.of_eq (fun n ↦ by simp)
  have htest' : PolyFueled _ (fun z : ℕ ↦
      (z.unpair.2 + 1) - low z.unpair.1) :=
    htest.of_eq (fun z ↦ by simp)
  have hoffset := subc_polyFueled.comp (hj.pair hlo)
  have hoffset' : PolyFueled _ (fun z : ℕ ↦
      z.unpair.2 - low z.unpair.1) :=
    hoffset.of_eq (fun z ↦ by simp)
  have hqueryLow : PolyFueled _ (fun z : ℕ ↦
      Nat.pair z.unpair.1 (Nat.pair (low z.unpair.1) z.unpair.2)) :=
    hn.pair (hlo.pair hj)
  have hqueryHigh : PolyFueled _ (fun z : ℕ ↦
      Nat.pair z.unpair.1 (Nat.pair (high z.unpair.1)
        (z.unpair.2 - low z.unpair.1))) :=
    hn.pair (hhi.pair hoffset')
  have hInvLow : RpnSpliceStream (fun z ↦
      (EF.const (1 / (low z.unpair.1 : ℚ))).serialize) :=
    RpnSpliceStream.serialize_const_comp
      ⟨cinv.comp (clow.comp Nat.Partrec.Code.left),
        hinv.comp (hlow.comp PolyFueled.left)⟩
  have hInvHighNeg : RpnSpliceStream (fun z ↦
      (EF.mul (EF.const (-1))
        (EF.const (1 / (high z.unpair.1 : ℚ)))).serialize) := by
    have hinvHigh : RpnSpliceStream (fun z ↦
        (EF.const (1 / (high z.unpair.1 : ℚ))).serialize) :=
      RpnSpliceStream.serialize_const_comp
        ⟨cinv.comp (chigh.comp Nat.Partrec.Code.left),
          hinv.comp (hhigh.comp PolyFueled.left)⟩
    exact RpnSpliceStream.serialize_mul (RpnSpliceStream.serialize_const (-1)) hinvHigh
  have hcoeff : RpnSpliceStream (fun z ↦
      (if z.unpair.2 < low z.unpair.1 then
        EF.const (1 / (low z.unpair.1 : ℚ))
      else EF.mul (EF.const (-1))
        (EF.const (1 / (high z.unpair.1 : ℚ)))).serialize) := by
    refine RpnSpliceStream.of_eq
      (RpnSpliceStream.ifZero hInvLow hInvHighNeg htest') ?_
    intro z
    by_cases hlt : z.unpair.2 < low z.unpair.1
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]
  have hsentence : RpnSentenceCodes (fun z ↦
      if z.unpair.2 < low z.unpair.1 then
        (X z.unpair.1).gt ((z.unpair.2 : ℚ) / (low z.unpair.1 : ℚ))
      else (X z.unpair.1).gt
        (((z.unpair.2 - low z.unpair.1 : ℕ) : ℚ) /
          (high z.unpair.1 : ℚ))) := by
    refine (RpnSentenceCodes.ifZero (hX.comp hqueryLow) (hX.comp hqueryHigh)
      htest').of_eq (fun z ↦ ?_)
    simp only [Nat.unpair_pair]
    by_cases hlt : z.unpair.2 < low z.unpair.1
    · rw [if_pos (show z.unpair.2 + 1 - low z.unpair.1 = 0 from by omega),
        if_pos hlt]
    · rw [if_neg (show ¬ z.unpair.2 + 1 - low z.unpair.1 = 0 from by omega),
        if_neg hlt]
  exact {
    termCount := fun n ↦ low n + high n
    coefficient := fun z ↦ if z.unpair.2 < low z.unpair.1 then
      EF.const (1 / (low z.unpair.1 : ℚ))
      else EF.mul (EF.const (-1))
        (EF.const (1 / (high z.unpair.1 : ℚ)))
    sentence := fun z ↦ if z.unpair.2 < low z.unpair.1 then
      (X z.unpair.1).gt ((z.unpair.2 : ℚ) / (low z.unpair.1 : ℚ))
      else (X z.unpair.1).gt
        (((z.unpair.2 - low z.unpair.1 : ℕ) : ℚ) /
          (high z.unpair.1 : ℚ))
    termCount_poly := ⟨cadd.comp (clow.pair chigh), hcount'⟩
    const_poly := RpnSpliceStream.serialize_const 0
    coefficient_poly := hcoeff
    sentence_poly := hsentence
    terms_eq := by
      intro n
      simp only [LUV.crossPrecisionAffine, LUV.expectAffine, List.range_add,
        List.map_append, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro j hj
        simp only [List.mem_range] at hj
        simp [hj]
      · apply List.map_congr_left
        intro j hj
        simp only [List.mem_range] at hj
        simp
    const_rank := by intro n; simp [LUV.crossPrecisionAffine]
    coefficient_rank := by
      intro n j hj
      by_cases hlt : j < low n <;> simp [hlt, EF.rank]
    const_closed := by intro n ρ V; simp [LUV.crossPrecisionAffine]
    coefficient_closed := by
      intro z ρ V
      by_cases hlt : z.unpair.2 < low z.unpair.1 <;>
        simp [hlt, EF.denoteWith]
  }

lemma LUV.crossPrecisionAffine_value
    (X : ℕ → LUV) (low high : ℕ → ℕ)
    (P : History) (w : Valuation) (n : ℕ) :
    (LUV.crossPrecisionAffine X low high n).value P w =
      (X n).expectApprox w (low n) - (X n).expectApprox w (high n) := by
  have hlo := (X n).expectAffine_value P w (low n)
  have hhi := (X n).expectAffine_value P w (high n)
  rw [AffineCombination.value]
  simp only [LUV.crossPrecisionAffine, EF.denote_const, List.map_append,
    List.sum_append, List.map_map, Function.comp_def, EF.denote_mul,
    Pi.mul_apply, Rat.cast_neg, Rat.cast_one]
  have hneg :
      (((X n).expectAffine (high n)).terms.map fun p ↦
          (-1 : ℝ) * p.1.denote P * w p.2).sum =
        -(((X n).expectAffine (high n)).terms.map fun p ↦
          p.1.denote P * w p.2).sum := by
    induction ((X n).expectAffine (high n)).terms with
    | nil => simp
    | cons p ps ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        ring
  have hlo' :
      (((X n).expectAffine (low n)).terms.map fun p ↦
        p.1.denote P * w p.2).sum = (X n).expectApprox w (low n) := by
    rw [← hlo]
    simp [AffineCombination.value, LUV.expectAffine]
  have hhi' :
      (((X n).expectAffine (high n)).terms.map fun p ↦
        p.1.denote P * w p.2).sum = (X n).expectApprox w (high n) := by
    rw [← hhi]
    simp [AffineCombination.value, LUV.expectAffine]
  norm_num only [Rat.cast_zero, zero_add]
  rw [hneg, hlo', hhi']
  ring

lemma LUV.crossPrecisionAffine_price
    (X : ℕ → LUV) (low high : ℕ → ℕ)
    (P : History) (n m : ℕ) :
    (LUV.crossPrecisionAffine X low high n).price P m =
      (X n).expectApprox (P m) (low n) -
        (X n).expectApprox (P m) (high n) := by
  rw [AffineCombination.price, LUV.crossPrecisionAffine_value]

lemma LUV.crossPrecisionAffine_magnitude_le_two
    (X : ℕ → LUV) (low high : ℕ → ℕ) (P : History) (n : ℕ) :
    (LUV.crossPrecisionAffine X low high n).magnitude P ≤ 2 := by
  have hlo := (X n).expectAffine_magnitude_le_one P (low n)
  have hhi := (X n).expectAffine_magnitude_le_one P (high n)
  simp only [LUV.crossPrecisionAffine, AffineCombination.magnitude,
    List.map_append, List.sum_append, List.map_map, Function.comp_def,
    EF.denote_mul, Pi.mul_apply, EF.denote_const, Rat.cast_neg, Rat.cast_one,
    neg_mul, one_mul, abs_neg]
  change ((X n).expectAffine (low n)).magnitude P +
      ((X n).expectAffine (high n)).magnitude P ≤ 2
  linarith

namespace DeferralFibre

/-- Two-index cross-precision mesh difference: at `z = ⟨m,k⟩`, the day-`m` reading of the
source-`k` LUV's mesh-`(k+1)` expectation minus its mesh-`(m+1)` expectation.  This is the
block family the fibre selector gates. -/
noncomputable def crossPrecisionBlocks (X : ℕ → LUV) : ℕ → AffineCombination :=
  LUV.crossPrecisionAffine (fun z ↦ X z.unpair.2)
    (fun z ↦ z.unpair.2 + 1) (fun z ↦ z.unpair.1 + 1)

private lemma crossPrecisionBlocks_terms_rank (X : ℕ → LUV) (z : ℕ) :
    ∀ p ∈ (crossPrecisionBlocks X z).terms, p.1.rank ≤ z.unpair.1 := by
  intro p hp
  simp only [crossPrecisionBlocks, LUV.crossPrecisionAffine, LUV.expectAffine,
    List.mem_append, List.mem_map, List.mem_range] at hp
  rcases hp with h | ⟨q, hq, rfl⟩
  · obtain ⟨i, _, rfl⟩ := h
    simp [EF.rank]
  · obtain ⟨i, _, rfl⟩ := hq
    simp [EF.rank]

private lemma crossPrecisionBlocks_terms_length (X : ℕ → LUV) (m k : ℕ) :
    (crossPrecisionBlocks X (Nat.pair m k)).terms.length = (k + 1) + (m + 1) := by
  simp [crossPrecisionBlocks, LUV.crossPrecisionAffine, LUV.expectAffine]

private lemma crossPrecisionBlocks_price (X : ℕ → LUV) (P : History) (m k day : ℕ) :
    (crossPrecisionBlocks X (Nat.pair m k)).price P day =
      (X k).expectApprox (P day) (k + 1) - (X k).expectApprox (P day) (m + 1) := by
  simpa [crossPrecisionBlocks] using
    LUV.crossPrecisionAffine_price (fun z ↦ X z.unpair.2)
      (fun z ↦ z.unpair.2 + 1) (fun z ↦ z.unpair.1 + 1) P (Nat.pair m k) day

private lemma crossPrecisionBlocks_value (X : ℕ → LUV) (P : History) (w : Valuation)
    (m k : ℕ) :
    (crossPrecisionBlocks X (Nat.pair m k)).value P w =
      (X k).expectApprox w (k + 1) - (X k).expectApprox w (m + 1) := by
  simpa [crossPrecisionBlocks] using
    LUV.crossPrecisionAffine_value (fun z ↦ X z.unpair.2)
      (fun z ↦ z.unpair.2 + 1) (fun z ↦ z.unpair.1 + 1) P w (Nat.pair m k)

/-- **Cross-precision correction without injectivity.**  The deferred-day reading of
a source LUV's own-day expectation mesh agrees asymptotically with its deferred-day mesh,
for every deferral function satisfying only `f n > n` plus poly-clocked emission. -/
lemma crossPrecision_deferred_tendsto_zero
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    (X : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X)
    (hvalued : ∀ k (v : PCWorld), v.ConsistentWithTheory DP → ∃ x, v.ValuesAt (X k) x)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    Tendsto (fun n ↦ (X n).expectApprox (P (f n)) (n + 1) -
      (X n).expectApprox (P (f n)) (f n + 1)) atTop (𝓝 0) := by
  have hX' : LUV.RpnThresholdCodeSeq (fun z ↦ X z.unpair.2) :=
    hX.reindex ⟨_, PolyFueled.right⟩
  have hB : AffineCombination.PolySequence (crossPrecisionBlocks X) :=
    LUV.crossPrecisionAffine_polySequence (fun z ↦ X z.unpair.2)
      (fun z ↦ z.unpair.2 + 1) (fun z ↦ z.unpair.1 + 1) hX'
      ⟨_, PolyFueled.right.succ_comp⟩ ⟨_, PolyFueled.left.succ_comp⟩
  have hw : ∃ c, PolyFueled c (fun m ↦ m * 2 + 2) := by
    have h2 := Classical.choose_spec (mulc_polyFueled 2)
    obtain ⟨ca, hca⟩ := h2.addConst 2
    exact ⟨ca, hca⟩
  have hkey := deferred_block_price_tendsto_zero (P := P) (DP := DP) hworld f hspec hB
    (hconstRank := fun z ↦ by
      simp [crossPrecisionBlocks, LUV.crossPrecisionAffine])
    (htermRank := crossPrecisionBlocks_terms_rank X)
    (width := fun m ↦ m * 2 + 2) (hwidth := hw)
    (hwidthPos := fun m ↦ by (try dsimp only); omega)
    (hwide := fun m k hk ↦ by
      rw [crossPrecisionBlocks_terms_length]; (try dsimp only); omega)
    (C := 2) (hC := by norm_num)
    (hmag := fun z ↦ by
      exact LUV.crossPrecisionAffine_magnitude_le_two (fun z ↦ X z.unpair.2)
        (fun z ↦ z.unpair.2 + 1) (fun z ↦ z.unpair.1 + 1) P z)
    (hbdd := fun z day ↦ by
      obtain ⟨m, k, rfl⟩ : ∃ m k, z = Nat.pair m k := ⟨z.unpair.1, z.unpair.2, by simp⟩
      rw [crossPrecisionBlocks_price]
      have h1 := (X k).expectApprox_nonneg (P day) (k + 1) (fun s ↦ (hP day s).1)
      have h2 := (X k).expectApprox_le_one (P day) (k + 1) (fun s ↦ (hP day s).2)
      have h3 := (X k).expectApprox_nonneg (P day) (m + 1) (fun s ↦ (hP day s).1)
      have h4 := (X k).expectApprox_le_one (P day) (m + 1) (fun s ↦ (hP day s).2)
      rw [abs_le]
      norm_num
      constructor <;> linarith)
    (hsmall := ?_)
  · refine Tendsto.congr' (Eventually.of_forall fun n ↦ ?_) hkey
    rw [crossPrecisionBlocks_price]
  · intro ε hε
    obtain ⟨N, hNpos, hNsmall⟩ : ∃ N : ℕ, 0 < N ∧ 2 / (N : ℝ) ≤ ε := by
      obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
      have hNR : (0 : ℝ) < N := (div_pos (by norm_num) hε).trans hN
      refine ⟨N, by exact_mod_cast hNR, ?_⟩
      rw [div_le_iff₀ hNR]
      have := (div_lt_iff₀ hε).mp hN
      linarith [this]
    refine ⟨N, fun m k hk hkm _ v hv ↦ ?_⟩
    obtain ⟨x, hx⟩ := hvalued k v hv
    have hlo := hx.expectApprox_near (n := k + 1) k.succ_pos
    have hhi := hx.expectApprox_near (n := m + 1) m.succ_pos
    push_cast at hlo hhi
    rw [crossPrecisionBlocks_value]
    have hcalc : |(X k).expectApprox v.payout (k + 1) - (X k).expectApprox v.payout (m + 1)| ≤
        1 / ((k : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by
      calc |(X k).expectApprox v.payout (k + 1) - (X k).expectApprox v.payout (m + 1)|
          = |((X k).expectApprox v.payout (k + 1) - x) -
              ((X k).expectApprox v.payout (m + 1) - x)| := by ring_nf
        _ ≤ |(X k).expectApprox v.payout (k + 1) - x| +
              |(X k).expectApprox v.payout (m + 1) - x| := abs_sub _ _
        _ ≤ _ := add_le_add hlo hhi
    have hkR : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hmR : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt (lt_of_le_of_lt hk hkm)
    have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
    have b1 : 1 / ((k : ℝ) + 1) ≤ 1 / (N : ℝ) :=
      one_div_le_one_div_of_le hNR (by linarith)
    have b2 : 1 / ((m : ℝ) + 1) ≤ 1 / (N : ℝ) :=
      one_div_le_one_div_of_le hNR (by linarith)
    have : 2 / (N : ℝ) = 1 / (N : ℝ) + 1 / (N : ℝ) := by ring
    linarith [hcalc, hNsmall]

end DeferralFibre

/-! ### Fixed expectation-difference portfolios -/

/-- The literal threshold portfolio for `E(X) - E(Y)` at the day-indexed mesh. -/
def LUV.expectDifferenceAffine (X Y : ℕ → LUV) (n : ℕ) : AffineCombination :=
  (LUV.expectAffineSeq X n).add (LUV.expectAffineSeq Y n).neg

noncomputable def LUV.expectDifferenceAffine_polySequence
    (X Y : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X)
    (hY : LUV.RpnThresholdCodeSeq Y) :
    AffineCombination.PolySequence (LUV.expectDifferenceAffine X Y) :=
  (LUV.expectAffineSeq_polySequence X hX).add
    (LUV.expectAffineSeq_polySequence Y hY).neg

lemma LUV.expectDifferenceAffine_priceAt
    (X Y : ℕ → LUV) (P : History) (n m : ℕ) :
    (LUV.expectDifferenceAffine X Y n).price P m =
      (X n).expectApprox (P m) (n + 1) - (Y n).expectApprox (P m) (n + 1) := by
  rw [LUV.expectDifferenceAffine, AffineCombination.add_price,
    AffineCombination.neg_price]
  simp only [LUV.expectAffineSeq]
  rw [LUV.expectAffine_priceAt,
    LUV.expectAffine_priceAt]
  ring

lemma LUV.expectDifferenceAffine_magnitude_le_two
    (X Y : ℕ → LUV) (P : History) (n : ℕ) :
    (LUV.expectDifferenceAffine X Y n).magnitude P ≤ 2 := by
  rw [LUV.expectDifferenceAffine, AffineCombination.add_magnitude,
    AffineCombination.neg_magnitude]
  linarith [LUV.expectAffineSeq_magnitude_le_one X P n,
    LUV.expectAffineSeq_magnitude_le_one Y P n]

/-- A generated feature used as a pure affine constant. -/
def featureConstantAffine (H : ℕ → EF) (n : ℕ) : AffineCombination :=
  ⟨H n, []⟩

noncomputable def featureConstantAffine_polySequence
    (H : ℕ → EF) (hH : PGenerableWeighting H) :
    AffineCombination.PolySequence (featureConstantAffine H) where
  termCount := fun _ ↦ 0
  coefficient := fun _ ↦ EF.const 0
  sentence := fun _ ↦ ⊥
  termCount_poly := ⟨Nat.Partrec.Code.const 0, PolyFueled.const 0⟩
  const_poly := hH.polySeg
  coefficient_poly := RpnSpliceStream.serialize_const 0
  sentence_poly := RpnSentenceCodes.ofPolySentenceCodes
    ⟨Nat.Partrec.Code.const (Encodable.encode (⊥ : Sentence)), PolyFueled.const _⟩
  terms_eq := by intro n; simp [featureConstantAffine]
  const_rank := hH.rank_le
  coefficient_rank := by intro n j hj; simp at hj
  const_closed := hH.closed
  coefficient_closed := by intro z ρ V; simp [EF.denoteWith]

@[simp] theorem featureConstantAffine_value
    (H : ℕ → EF) (P : History) (v : Valuation) (n : ℕ) :
    (featureConstantAffine H n).value P v = (H n).denote P := by
  simp [featureConstantAffine, AffineCombination.value]

@[simp] theorem featureConstantAffine_price
    (H : ℕ → EF) (P : History) (n m : ℕ) :
    (featureConstantAffine H n).price P m = (H n).denote P := by
  simp [AffineCombination.price]

@[simp] theorem AffineCombination.sentenceAffine_value
    (φ : ℕ → Sentence) (P : History) (v : Valuation) (n : ℕ) :
    (AffineCombination.sentenceAffine φ n).value P v = v (φ n) := by
  simp [AffineCombination.sentenceAffine, AffineCombination.value]

@[simp] theorem featureConstantAffine_magnitude
    (H : ℕ → EF) (P : History) (n : ℕ) :
    (featureConstantAffine H n).magnitude P = 0 := by
  simp [featureConstantAffine, AffineCombination.magnitude]

/-! ### Paired-index block families

The deferral fibre needs its blocks indexed by *both* the evaluation day and the
source index: `z = ⟨m,k⟩` carries the day-`m` reading of source-`k` data, and every
emitted coefficient must be legal on day `m`.  These are the paired analogues of the
day-indexed mesh, expectation feature, price feature and numeric quote. -/

namespace DeferralFibre

/-- Two-index expectation mesh: at `z = ⟨m,k⟩` the source-`k` LUV's precision-`(m+1)`
threshold bundle — the block a day-`m` fibre portfolio may hold. -/
def pairedExpectationBlocks (X : ℕ → LUV) (z : ℕ) : AffineCombination :=
  (X z.unpair.2).expectAffine (z.unpair.1 + 1)

lemma pairedExpectationBlocks_value (X : ℕ → LUV) (P : History) (w : Valuation)
    (m k : ℕ) :
    (pairedExpectationBlocks X (Nat.pair m k)).value P w =
      (X k).expectApprox w (m + 1) := by
  simpa [pairedExpectationBlocks] using
    (X k).expectAffine_value P w (m + 1)

lemma pairedExpectationBlocks_price (X : ℕ → LUV) (P : History) (m k day : ℕ) :
    (pairedExpectationBlocks X (Nat.pair m k)).price P day =
      (X k).expectApprox (P day) (m + 1) := by
  rw [AffineCombination.price, pairedExpectationBlocks_value]

lemma pairedExpectationBlocks_magnitude_le_one (X : ℕ → LUV) (P : History) (z : ℕ) :
    (pairedExpectationBlocks X z).magnitude P ≤ 1 :=
  (X z.unpair.2).expectAffine_magnitude_le_one P (z.unpair.1 + 1)

lemma pairedExpectationBlocks_terms_length (X : ℕ → LUV) (z : ℕ) :
    (pairedExpectationBlocks X z).terms.length = z.unpair.1 + 1 := by
  simp [pairedExpectationBlocks, LUV.expectAffine]

lemma pairedExpectationBlocks_const_rank (X : ℕ → LUV) (z : ℕ) :
    (pairedExpectationBlocks X z).const.rank ≤ z.unpair.1 := by
  simp [pairedExpectationBlocks, LUV.expectAffine]

lemma pairedExpectationBlocks_terms_rank (X : ℕ → LUV) (z : ℕ) :
    ∀ p ∈ (pairedExpectationBlocks X z).terms, p.1.rank ≤ z.unpair.1 := by
  intro p hp
  simp only [pairedExpectationBlocks, LUV.expectAffine, List.mem_map,
    List.mem_range] at hp
  obtain ⟨i, _, rfl⟩ := hp
  simp [EF.rank]

/-- The paired mesh family is emitted uniformly from the varying threshold presentation:
the evaluation day fixes the precision and the source index selects the LUV. -/
noncomputable def pairedExpectationBlocks_polySequence (X : ℕ → LUV)
    (hX : LUV.RpnThresholdCodeSeq X) :
    AffineCombination.PolySequence (pairedExpectationBlocks X) := by
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  have hm := PolyFueled.left.comp PolyFueled.left
  have hk := PolyFueled.right.comp PolyFueled.left
  have hj := PolyFueled.right
  have hquery := hk.pair (hm.succ_comp.pair hj)
  have hsentence := hX.comp hquery
  exact {
    termCount := fun z ↦ z.unpair.1 + 1
    coefficient := fun w ↦ .const (1 / ((w.unpair.1.unpair.1 + 1 : ℕ) : ℚ))
    sentence := fun w ↦
      (X w.unpair.1.unpair.2).gt ((w.unpair.2 : ℚ) /
        ((w.unpair.1.unpair.1 + 1 : ℕ) : ℚ))
    termCount_poly := ⟨_, PolyFueled.left.succ_comp⟩
    const_poly := RpnSpliceStream.serialize_const 0
    coefficient_poly := RpnSpliceStream.serialize_const_comp
      ⟨_, hinv.comp hm.succ_comp⟩
    sentence_poly := hsentence.of_eq (fun w ↦ by simp)
    terms_eq := by intro z; simp [pairedExpectationBlocks, LUV.expectAffine]
    const_rank := by intro z; simp [pairedExpectationBlocks, LUV.expectAffine]
    coefficient_rank := by intro z j hj; simp [EF.rank]
    const_closed := by
      intro z ρ V; simp [pairedExpectationBlocks, LUV.expectAffine]
    coefficient_closed := by intro w ρ V; simp [EF.denoteWith]
  }

/-- Two-index current-expectation feature: at `z = ⟨m,k⟩` the day-`m` market price of the
source-`k` LUV's precision-`(m+1)` mesh, i.e. `𝔼ₘ(X k)`.  Its rank is the evaluation day
`m`, not the source index, which is what a fibre gate requires. -/
noncomputable def pairedExpectationFeature (X : ℕ → LUV) (z : ℕ) : EF :=
  (pairedExpectationBlocks X z).priceFeature z.unpair.1

lemma pairedExpectationFeature_denote (X : ℕ → LUV) (P : History) (m k : ℕ) :
    (pairedExpectationFeature X (Nat.pair m k)).denote P = (X k).expect P m := by
  rw [pairedExpectationFeature, AffineCombination.priceFeature_denote]
  simp [pairedExpectationBlocks_price, LUV.expect]

lemma pairedExpectationFeature_paired (X : ℕ → LUV)
    (hX : LUV.RpnThresholdCodeSeq X) :
    PairedWeighting (pairedExpectationFeature X) := by
  let hmesh := pairedExpectationBlocks_polySequence X hX
  exact {
    polySeg := (hmesh.priceFeature_polySeg.comp
      (PolyFueled.id.pair PolyFueled.left)).of_eq
        (fun z ↦ by simp [pairedExpectationFeature])
    rank_le := fun z ↦ AffineCombination.priceFeature_rank _ le_rfl
      (pairedExpectationBlocks_const_rank X z)
      (pairedExpectationBlocks_terms_rank X z)
    closed := fun z ρ V ↦ hmesh.priceFeature_closed z z.unpair.1 ρ V
  }

/-- Two-index current-price feature: at `z = ⟨m,k⟩` the day-`m` market price of the
source-`k` sentence. -/
def pairedPriceFeature (φ : ℕ → Sentence) (z : ℕ) : EF :=
  EF.price (φ z.unpair.2) z.unpair.1

lemma pairedPriceFeature_denote (φ : ℕ → Sentence) (P : History) (m k : ℕ) :
    (pairedPriceFeature φ (Nat.pair m k)).denote P = P m (φ k) := by
  simp [pairedPriceFeature]

lemma pairedPriceFeature_paired (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ) :
    PairedWeighting (pairedPriceFeature φ) where
  polySeg := (RpnSpliceStream.serialize_price hφ PolyFueled.right
    PolyFueled.left).of_eq (fun z ↦ by simp [pairedPriceFeature])
  rank_le := by intro z; simp [pairedPriceFeature]
  closed := by intro z ρ V; simp [pairedPriceFeature]

/-- Two-index numeric quote block: at `z = ⟨m,k⟩` the quoted target `H z` minus the
source-`k` LUV's precision-`(m+1)` mesh. -/
noncomputable def numericQuoteBlocks (H : ℕ → EF) (Y : ℕ → LUV) (z : ℕ) :
    AffineCombination :=
  (featureConstantAffine H z).add ((pairedExpectationBlocks Y z).neg)

lemma numericQuoteBlocks_value (H : ℕ → EF) (Y : ℕ → LUV) (P : History)
    (w : Valuation) (m k : ℕ) :
    (numericQuoteBlocks H Y (Nat.pair m k)).value P w =
      (H (Nat.pair m k)).denote P - (Y k).expectApprox w (m + 1) := by
  rw [numericQuoteBlocks, AffineCombination.add_value,
    AffineCombination.neg_value, featureConstantAffine_value,
    pairedExpectationBlocks_value]
  ring

lemma numericQuoteBlocks_price (H : ℕ → EF) (Y : ℕ → LUV) (P : History)
    (m k day : ℕ) :
    (numericQuoteBlocks H Y (Nat.pair m k)).price P day =
      (H (Nat.pair m k)).denote P - (Y k).expectApprox (P day) (m + 1) := by
  rw [AffineCombination.price, numericQuoteBlocks_value]

lemma numericQuoteBlocks_magnitude (H : ℕ → EF) (Y : ℕ → LUV) (P : History) (z : ℕ) :
    (numericQuoteBlocks H Y z).magnitude P ≤ 1 := by
  rw [numericQuoteBlocks, AffineCombination.add_magnitude,
    featureConstantAffine_magnitude, AffineCombination.neg_magnitude, zero_add]
  exact pairedExpectationBlocks_magnitude_le_one Y P z

lemma numericQuoteBlocks_terms_length (H : ℕ → EF) (Y : ℕ → LUV) (z : ℕ) :
    (numericQuoteBlocks H Y z).terms.length = z.unpair.1 + 1 := by
  rw [numericQuoteBlocks]
  simp [AffineCombination.add, featureConstantAffine, AffineCombination.neg,
    AffineCombination.scale, pairedExpectationBlocks, LUV.expectAffine]

lemma numericQuoteBlocks_const_rank {H : ℕ → EF} (hH : PairedWeighting H)
    (Y : ℕ → LUV) (z : ℕ) :
    (numericQuoteBlocks H Y z).const.rank ≤ z.unpair.1 := by
  simp only [numericQuoteBlocks, AffineCombination.add, AffineCombination.neg,
    AffineCombination.scale, featureConstantAffine, EF.rank]
  exact Nat.max_le.mpr ⟨hH.rank_le z, by simp [
    pairedExpectationBlocks, LUV.expectAffine]⟩

lemma numericQuoteBlocks_terms_rank (H : ℕ → EF) (Y : ℕ → LUV) (z : ℕ) :
    ∀ p ∈ (numericQuoteBlocks H Y z).terms, p.1.rank ≤ z.unpair.1 := by
  intro p hp
  simp only [numericQuoteBlocks, AffineCombination.add, featureConstantAffine,
    List.nil_append] at hp
  exact AffineCombination.neg_terms_rank_le _
    (pairedExpectationBlocks_terms_rank Y z) p hp

noncomputable def numericQuoteBlocks_polySequence
    (H : ℕ → EF) (hH : PairedWeighting H) (Y : ℕ → LUV)
    (hY : LUV.RpnThresholdCodeSeq Y) :
    AffineCombination.PolySequence (numericQuoteBlocks H Y) :=
  (featureConstantAffine_polySequence H hH.toPGenerable).add
    (pairedExpectationBlocks_polySequence Y hY).neg

/-- **Deferred numeric quote without injectivity.**  If every completed world assigns the
paired target `H ⟨f k, k⟩` to the quote LUV `Y k`, then the deferred market reading of
`Y k` matches that target asymptotically — for every deferral function satisfying only
`f n > n` plus poly-clocked emission. -/
lemma numericQuote_deferred_tendsto_zero
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    (H : ℕ → EF) (hH : PairedWeighting H)
    (hHmem : ∀ z, 0 ≤ (H z).denote P ∧ (H z).denote P ≤ 1)
    (Y : ℕ → LUV) (hY : LUV.RpnThresholdCodeSeq Y)
    (hreflected : ∀ m k, f k = m → ∀ v : PCWorld, v.ConsistentWithTheory DP →
      v.ValuesAt (Y k) ((H (Nat.pair m k)).denote P))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    Tendsto (fun n ↦ (H (Nat.pair (f n) n)).denote P -
      (Y n).expectApprox (P (f n)) (f n + 1)) atTop (𝓝 0) := by
  have hkey := deferred_block_price_tendsto_zero (P := P) (DP := DP) hworld f hspec
    (numericQuoteBlocks_polySequence H hH Y hY)
    (hconstRank := numericQuoteBlocks_const_rank hH Y)
    (htermRank := numericQuoteBlocks_terms_rank H Y)
    (width := fun m ↦ m + 1) (hwidth := ⟨_, PolyFueled.id.succ_comp⟩)
    (hwidthPos := fun m ↦ Nat.succ_pos m)
    (hwide := fun m k hk ↦ by rw [numericQuoteBlocks_terms_length]; simp)
    (C := 1) (hC := by norm_num)
    (hmag := fun z ↦ by simpa using numericQuoteBlocks_magnitude H Y P z)
    (hbdd := fun z day ↦ by
      obtain ⟨m, k, rfl⟩ : ∃ m k, z = Nat.pair m k := ⟨z.unpair.1, z.unpair.2, by simp⟩
      rw [numericQuoteBlocks_price]
      have h1 := (Y k).expectApprox_nonneg (P day) (m + 1) (fun s ↦ (hP day s).1)
      have h2 := (Y k).expectApprox_le_one (P day) (m + 1) (fun s ↦ (hP day s).2)
      have h3 := hHmem (Nat.pair m k)
      rw [abs_le]
      norm_num
      constructor <;> linarith [h3.1, h3.2])
    (hsmall := ?_)
  · refine Tendsto.congr' (Eventually.of_forall fun n ↦ ?_) hkey
    rw [numericQuoteBlocks_price]
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun m k hk hkm hfk v hv ↦ ?_⟩
    have hmR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hsmall : 1 / ((m : ℝ) + 1) ≤ ε := by
      have hNm : (1 : ℝ) / ε < (m : ℝ) + 1 := by
        refine hN.trans_le ?_
        have : (N : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast le_of_lt (lt_of_le_of_lt hk hkm)
        linarith
      rw [div_lt_iff₀ hε] at hNm
      rw [div_le_iff₀ hmR]
      nlinarith
    rw [numericQuoteBlocks_value, abs_sub_comm]
    refine LE.le.trans ?_ hsmall
    simpa using
      (hreflected m k hfk v hv).expectApprox_near (n := m + 1) m.succ_pos

/-- **Deferred conditional-expectation quote without injectivity.**  If on the fibre
`f k = m` every completed world reads `Z k` within the vanishing slack `slack k` of
`w m · X k`, and `Z' k` as the numeral `w m · 𝔼ₘ(X k)`, then the two deferred market
expectations agree asymptotically — for every deferral function satisfying only
`f n > n` plus poly-clocked emission, with no injectivity or monotonicity assumption.

The slack enters the block-price bound additively beside the three `1/(m+1)` grid errors,
so it only has to vanish; it need not be tied to the grid. -/
lemma conditional_deferred_tendsto_zero
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    (X Z Z' : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X)
    (hZ : LUV.RpnThresholdCodeSeq Z) (hZ' : LUV.RpnThresholdCodeSeq Z')
    (w : ℕ → ℚ) (W : ℕ → EF) (hW : PGenerableWeighting W)
    (hWdenote : ∀ m, (W m).denote P = (w m : ℝ))
    (hw : ∀ m, 0 ≤ w m ∧ w m ≤ 1)
    (slack : ℕ → ℝ) (hslack : Tendsto slack atTop (𝓝 0))
    (hsemantic : ∀ m k, f k = m → ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∃ x z, v.ValuesAt (X k) x ∧ v.ValuesAt (Z k) z ∧ |z - x * w m| ≤ slack k ∧
        v.ValuesAt (Z' k) ((X k).expect P m * w m))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    Tendsto (fun n ↦ (Z n).expect P (f n) - (Z' n).expect P (f n)) atTop (𝓝 0) := by
  classical
  have hWnegP : PairedWeighting (fun z ↦ EF.mul (EF.const (-1)) (W z.unpair.1)) :=
    (PairedWeighting.const (-1)).mul (PairedWeighting.ofPGenerableFst hW)
  have htargetP :
      PairedWeighting (fun z ↦ EF.mul (W z.unpair.1) (pairedExpectationFeature X z)) :=
    (PairedWeighting.ofPGenerableFst hW).mul (pairedExpectationFeature_paired X hX)
  set Wneg : ℕ → EF := fun z ↦ EF.mul (EF.const (-1)) (W z.unpair.1) with hWnegDef
  set target : ℕ → EF := fun z ↦ EF.mul (W z.unpair.1) (pairedExpectationFeature X z)
    with htargetDef
  set Bs : ℕ → AffineCombination := fun z ↦
    ((pairedExpectationBlocks Z z).add
      ((pairedExpectationBlocks X z).scale (Wneg z))).add
      (numericQuoteBlocks target Z' z) with hBsDef
  have hB : AffineCombination.PolySequence Bs :=
    ((pairedExpectationBlocks_polySequence Z hZ).add
      ((pairedExpectationBlocks_polySequence X hX).scaleFeature Wneg
        hWnegP.toPGenerable)).add
      (numericQuoteBlocks_polySequence target htargetP Z' hZ')
  -- denotations of the two derived features
  have hWnegDenote : ∀ m k, (Wneg (Nat.pair m k)).denote P = -(w m : ℝ) := by
    intro m k
    simp [hWnegDef, hWdenote]
  have htargetDenote : ∀ m k,
      (target (Nat.pair m k)).denote P = (w m : ℝ) * (X k).expect P m := by
    intro m k
    simp [htargetDef, hWdenote, pairedExpectationFeature_denote]
  -- price of a block
  have hprice : ∀ m k day, (Bs (Nat.pair m k)).price P day =
      (Z k).expectApprox (P day) (m + 1) -
        (w m : ℝ) * (X k).expectApprox (P day) (m + 1) +
        ((w m : ℝ) * (X k).expect P m - (Z' k).expectApprox (P day) (m + 1)) := by
    intro m k day
    rw [hBsDef]
    simp only [AffineCombination.add_price, AffineCombination.scale_price,
      pairedExpectationBlocks_price, numericQuoteBlocks_price,
      hWnegDenote m k, htargetDenote m k]
    ring
  have hvalue : ∀ m k (u : Valuation), (Bs (Nat.pair m k)).value P u =
      (Z k).expectApprox u (m + 1) -
        (w m : ℝ) * (X k).expectApprox u (m + 1) +
        ((w m : ℝ) * (X k).expect P m - (Z' k).expectApprox u (m + 1)) := by
    intro m k u
    rw [hBsDef]
    simp only [AffineCombination.add_value, AffineCombination.scale_value,
      pairedExpectationBlocks_value, numericQuoteBlocks_value,
      hWnegDenote m k, htargetDenote m k]
    ring
  -- width certificate
  have hwidth : ∃ c, PolyFueled c (fun m ↦ m * 3 + 3) := by
    have h3 := Classical.choose_spec (mulc_polyFueled 3)
    obtain ⟨ca, hca⟩ := h3.addConst 3
    exact ⟨ca, hca⟩
  have hkey := deferred_block_price_tendsto_zero (P := P) (DP := DP) hworld f hspec hB
    (hconstRank := by
      intro z
      have h1 : ((pairedExpectationBlocks X z).scale (Wneg z)).const.rank ≤ z.unpair.1 := by
        simp only [AffineCombination.scale, EF.rank, Nat.max_le]
        exact ⟨hWnegP.rank_le z, pairedExpectationBlocks_const_rank X z⟩
      have h2 := pairedExpectationBlocks_const_rank Z z
      have h3 := numericQuoteBlocks_const_rank htargetP Z' z
      simp only [hBsDef, AffineCombination.add, EF.rank, Nat.max_le]
      exact ⟨⟨h2, h1⟩, h3⟩)
    (htermRank := by
      intro z p hp
      simp only [hBsDef, AffineCombination.add, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact pairedExpectationBlocks_terms_rank Z z p hp
      · exact AffineCombination.scale_terms_rank_le _ _ (hWnegP.rank_le z)
          (pairedExpectationBlocks_terms_rank X z) p hp
      · exact numericQuoteBlocks_terms_rank target Z' z p hp)
    (width := fun m ↦ m * 3 + 3) (hwidth := hwidth)
    (hwidthPos := fun m ↦ by (try dsimp only); omega)
    (hwide := fun m k hk ↦ by
      simp only [hBsDef, AffineCombination.add, AffineCombination.scale,
        List.length_append, List.length_map, pairedExpectationBlocks_terms_length,
        numericQuoteBlocks_terms_length, Nat.unpair_pair]
      omega)
    (C := 4) (hC := by norm_num)
    (hmag := by
      intro z
      have h1 := pairedExpectationBlocks_magnitude_le_one Z P z
      have h2 := pairedExpectationBlocks_magnitude_le_one X P z
      have h3 := numericQuoteBlocks_magnitude target Z' P z
      have h4 : |(Wneg z).denote P| ≤ 1 := by
        obtain ⟨m, k, rfl⟩ : ∃ m k, z = Nat.pair m k := ⟨z.unpair.1, z.unpair.2, by simp⟩
        rw [hWnegDenote m k, abs_neg, abs_of_nonneg (by exact_mod_cast (hw m).1)]
        exact_mod_cast (hw m).2
      have hXnonneg := (pairedExpectationBlocks X z).magnitude_nonneg P
      have hscale : ((pairedExpectationBlocks X z).scale (Wneg z)).magnitude P ≤ 1 := by
        rw [AffineCombination.scale_magnitude]
        calc |(Wneg z).denote P| * (pairedExpectationBlocks X z).magnitude P
            ≤ 1 * 1 := mul_le_mul h4 h2 hXnonneg (by norm_num)
          _ = 1 := by norm_num
      simp only [hBsDef, AffineCombination.add_magnitude]
      push_cast
      linarith)
    (hbdd := by
      intro z day
      obtain ⟨m, k, rfl⟩ : ∃ m k, z = Nat.pair m k := ⟨z.unpair.1, z.unpair.2, by simp⟩
      rw [hprice]
      have h1 := (Z k).expectApprox_nonneg (P day) (m + 1) (fun s ↦ (hP day s).1)
      have h2 := (Z k).expectApprox_le_one (P day) (m + 1) (fun s ↦ (hP day s).2)
      have h3 := (Z' k).expectApprox_nonneg (P day) (m + 1) (fun s ↦ (hP day s).1)
      have h4 := (Z' k).expectApprox_le_one (P day) (m + 1) (fun s ↦ (hP day s).2)
      have h5 := (X k).expectApprox_nonneg (P day) (m + 1) (fun s ↦ (hP day s).1)
      have h6 := (X k).expectApprox_le_one (P day) (m + 1) (fun s ↦ (hP day s).2)
      have h7 := ((X k).expect_mem_Icc P m (hP m)).1
      have h8 := ((X k).expect_mem_Icc P m (hP m)).2
      have hw0 : (0 : ℝ) ≤ (w m : ℝ) := by exact_mod_cast (hw m).1
      have hw1 : (w m : ℝ) ≤ 1 := by exact_mod_cast (hw m).2
      rw [abs_le]
      push_cast
      constructor <;> nlinarith)
    (hsmall := ?_)
  · refine Tendsto.congr' (Eventually.of_forall fun n ↦ ?_) hkey
    rw [hprice]
    simp only [LUV.expect]
    ring
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (6 / ε)
    obtain ⟨Ns, hNs⟩ := Metric.tendsto_atTop.mp hslack (ε / 2) (by linarith)
    refine ⟨max N Ns, fun m k hk hkm hfk v hv ↦ ?_⟩
    have hkN : N ≤ k := le_trans (le_max_left _ _) hk
    have hslackk : slack k ≤ ε / 2 := by
      have := hNs k (le_trans (le_max_right _ _) hk)
      rw [Real.dist_eq, _root_.sub_zero] at this
      exact le_of_lt (lt_of_le_of_lt (le_abs_self _) this)
    obtain ⟨x, z, hx, hz, hzslack, hz'⟩ := hsemantic m k hfk v hv
    have hmR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hgrid : ∀ {Y : LUV} {y : ℝ}, v.ValuesAt Y y →
        |Y.expectApprox v.payout (m + 1) - y| ≤ 1 / ((m : ℝ) + 1) := by
      intro Y y hy
      simpa using hy.expectApprox_near (n := m + 1) m.succ_pos
    have hnearX := hgrid hx
    have hnearZ := hgrid hz
    have hnearZ' := hgrid hz'
    have hw0 : (0 : ℝ) ≤ (w m : ℝ) := by exact_mod_cast (hw m).1
    have hw1 : (w m : ℝ) ≤ 1 := by exact_mod_cast (hw m).2
    have hwabs : |(w m : ℝ)| ≤ 1 := by rw [abs_of_nonneg hw0]; exact hw1
    have hmul : |(w m : ℝ)| * |(X k).expectApprox v.payout (m + 1) - x| ≤
        1 / ((m : ℝ) + 1) := by
      calc |(w m : ℝ)| * |(X k).expectApprox v.payout (m + 1) - x|
          ≤ 1 * (1 / ((m : ℝ) + 1)) :=
            mul_le_mul hwabs hnearX (abs_nonneg _) (by positivity)
        _ = 1 / ((m : ℝ) + 1) := one_mul _
    have hsmallε : 3 / ((m : ℝ) + 1) ≤ ε / 2 := by
      have hNm : (6 : ℝ) / ε < (m : ℝ) + 1 := by
        refine hN.trans_le ?_
        have : (N : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast le_of_lt (lt_of_le_of_lt hkN hkm)
        linarith
      rw [div_lt_iff₀ hε] at hNm
      rw [div_le_iff₀ hmR]
      nlinarith
    rw [hvalue]
    set eZ := (Z k).expectApprox v.payout (m + 1) - x * (w m : ℝ) with heZ
    set eX := (X k).expectApprox v.payout (m + 1) - x with heX
    set eZ' := (Z' k).expectApprox v.payout (m + 1) -
      (X k).expect P m * (w m : ℝ) with heZ'
    have hform : (Z k).expectApprox v.payout (m + 1) -
          (w m : ℝ) * (X k).expectApprox v.payout (m + 1) +
          ((w m : ℝ) * (X k).expect P m -
            (Z' k).expectApprox v.payout (m + 1)) =
        eZ - (w m : ℝ) * eX - eZ' := by
      rw [heZ, heX, heZ']; ring
    rw [hform]
    have hnearZslack : |eZ| ≤ 1 / ((m : ℝ) + 1) + slack k := by
      have hsplit : eZ = ((Z k).expectApprox v.payout (m + 1) - z) +
          (z - x * (w m : ℝ)) := by rw [heZ]; ring
      calc |eZ| = |((Z k).expectApprox v.payout (m + 1) - z) + (z - x * (w m : ℝ))| := by
            rw [hsplit]
        _ ≤ |(Z k).expectApprox v.payout (m + 1) - z| + |z - x * (w m : ℝ)| :=
            abs_add_le _ _
        _ ≤ 1 / ((m : ℝ) + 1) + slack k := add_le_add hnearZ hzslack
    have hbound : |eZ - (w m : ℝ) * eX - eZ'| ≤ 3 / ((m : ℝ) + 1) + slack k := by
      calc |eZ - (w m : ℝ) * eX - eZ'|
          ≤ (|eZ| + |(w m : ℝ) * eX|) + |eZ'| :=
            (abs_sub _ _).trans (add_le_add (abs_sub eZ ((w m : ℝ) * eX)) (le_refl _))
        _ = (|eZ| + |(w m : ℝ)| * |eX|) + |eZ'| := by rw [abs_mul]
        _ ≤ ((1 / ((m : ℝ) + 1) + slack k) + 1 / ((m : ℝ) + 1)) + 1 / ((m : ℝ) + 1) :=
            add_le_add (add_le_add hnearZslack hmul) hnearZ'
        _ = 3 / ((m : ℝ) + 1) + slack k := by ring
    linarith

/-- **Deferred self-trust correction without injectivity.**  If every completed world
values the confidence LUV `B k` at the paired gate `G ⟨f k, k⟩` and the product LUV `A k`
at that gate scaled by the payout of `φ k`, then the deferred reading of the self-trust
identity vanishes asymptotically — for every deferral function satisfying only `f n > n`
plus poly-clocked emission.  The block family carries the emitted confidence *expression*
`pF` rather than a numeral, so the day-`f n` portfolio stays inside the rank discipline. -/
lemma selfTrust_deferred_tendsto_zero
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ)
    (p : ℕ → ℚ) (hp : ∀ m, 0 ≤ p m ∧ p m ≤ 1)
    (pF : ℕ → EF) (hpF : PairedWeighting pF)
    (hpFmem : ∀ z, 0 ≤ (pF z).denote P ∧ (pF z).denote P ≤ 1)
    (hpDenote : ∀ m k, k ≤ m → (pF (Nat.pair m k)).denote P = (p k : ℝ))
    (G : ℕ → EF) (hG : PairedWeighting G)
    (hGmem : ∀ z, 0 ≤ (G z).denote P ∧ (G z).denote P ≤ 1)
    (A B : ℕ → LUV) (hA : LUV.RpnThresholdCodeSeq A) (hB : LUV.RpnThresholdCodeSeq B)
    (hsemantic : ∀ m k, f k = m → ∀ v : PCWorld, v.ConsistentWithTheory DP →
      v.ValuesAt (B k) ((G (Nat.pair m k)).denote P) ∧
        v.ValuesAt (A k) (v.payout (φ k) * (G (Nat.pair m k)).denote P))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    Tendsto (fun n ↦ (A n).expect P (f n) - (p n : ℝ) * (B n).expect P (f n) -
      (G (Nat.pair (f n) n)).denote P * (P (f n) (φ n) - (p n : ℝ)))
      atTop (𝓝 0) := by
  classical
  set pNeg : ℕ → EF := fun z ↦ EF.mul (EF.const (-1)) (pF z) with hpNegDef
  set GNeg : ℕ → EF := fun z ↦ EF.mul (EF.const (-1)) (G z) with hGNegDef
  set pG : ℕ → EF := fun z ↦ EF.mul (pF z) (G z) with hpGDef
  have hpNeg : PairedWeighting pNeg := (PairedWeighting.const (-1)).mul hpF
  have hGNeg : PairedWeighting GNeg := (PairedWeighting.const (-1)).mul hG
  have hpG : PairedWeighting pG := hpF.mul hG
  have hφ' : RpnSentenceCodes (fun z ↦ φ z.unpair.2) := hφ.comp PolyFueled.right
  set Bs : ℕ → AffineCombination := fun z ↦
    ((((pairedExpectationBlocks A z).add
        ((pairedExpectationBlocks B z).scale (pNeg z))).add
      ((AffineCombination.sentenceAffine (fun z ↦ φ z.unpair.2) z).scale (GNeg z))).add
      (featureConstantAffine pG z)) with hBsDef
  have hBpoly : AffineCombination.PolySequence Bs :=
    (((pairedExpectationBlocks_polySequence A hA).add
        ((pairedExpectationBlocks_polySequence B hB).scaleFeature pNeg
          hpNeg.toPGenerable)).add
      ((AffineCombination.sentenceAffine_polySequence
          (fun z ↦ φ z.unpair.2) hφ').scaleFeature GNeg hGNeg.toPGenerable)).add
      (featureConstantAffine_polySequence pG hpG.toPGenerable)
  -- pointwise readings of the block family
  have hvalue : ∀ (w : Valuation) (m k : ℕ),
      (Bs (Nat.pair m k)).value P w =
        (A k).expectApprox w (m + 1) +
          (-(pF (Nat.pair m k)).denote P) * (B k).expectApprox w (m + 1) +
          (-(G (Nat.pair m k)).denote P) * w (φ k) +
          (pF (Nat.pair m k)).denote P * (G (Nat.pair m k)).denote P := by
    intro w m k
    simp only [hBsDef, AffineCombination.add_value, AffineCombination.scale_value,
      pairedExpectationBlocks_value, AffineCombination.sentenceAffine_value,
      featureConstantAffine_value, hpNegDef, hGNegDef, hpGDef, EF.denote_mul,
      EF.denote_const, Pi.mul_apply, Nat.unpair_pair, Rat.cast_neg, Rat.cast_one]
    ring
  have hprice : ∀ (day m k : ℕ),
      (Bs (Nat.pair m k)).price P day =
        (A k).expectApprox (P day) (m + 1) +
          (-(pF (Nat.pair m k)).denote P) * (B k).expectApprox (P day) (m + 1) +
          (-(G (Nat.pair m k)).denote P) * P day (φ k) +
          (pF (Nat.pair m k)).denote P * (G (Nat.pair m k)).denote P := by
    intro day m k
    rw [AffineCombination.price, hvalue]
  have hpairs : ∀ z : ℕ, ∃ m k, z = Nat.pair m k :=
    fun z ↦ ⟨z.unpair.1, z.unpair.2, by simp⟩
  have hwidth : ∃ c, PolyFueled c (fun m ↦ m * 2 + 3) := by
    have h2 := Classical.choose_spec (mulc_polyFueled 2)
    obtain ⟨ca, hca⟩ := h2.addConst 3
    exact ⟨ca, hca⟩
  have hkey := deferred_block_price_tendsto_zero (P := P) (DP := DP) hworld f hspec hBpoly
    (hconstRank := ?_) (htermRank := ?_)
    (width := fun m ↦ m * 2 + 3) (hwidth := hwidth)
    (hwidthPos := fun m ↦ by (try dsimp only); omega)
    (hwide := ?_)
    (C := 4) (hC := by norm_num)
    (hmag := ?_) (hbdd := ?_) (hsmall := ?_)
  · refine Tendsto.congr' (Eventually.of_forall fun n ↦ ?_) hkey
    rw [hprice, hpDenote (f n) n (f.lt n).le]
    simp only [LUV.expect]
    ring
  · -- hconstRank
    intro z
    simp only [hBsDef, AffineCombination.add, AffineCombination.scale,
      AffineCombination.sentenceAffine, featureConstantAffine, EF.rank,
      hpNegDef, hGNegDef, hpGDef]
    refine Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.max_le.mpr
      ⟨pairedExpectationBlocks_const_rank A z, ?_⟩, ?_⟩, ?_⟩
    · exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨by simp, hpF.rank_le z⟩,
        pairedExpectationBlocks_const_rank B z⟩
    · exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨by simp, hG.rank_le z⟩, by simp⟩
    · exact Nat.max_le.mpr ⟨hpF.rank_le z, hG.rank_le z⟩
  · -- htermRank
    intro z q hq
    have hstep : ∀ (X Y : AffineCombination),
        (∀ r ∈ X.terms, r.1.rank ≤ z.unpair.1) →
        (∀ r ∈ Y.terms, r.1.rank ≤ z.unpair.1) →
        ∀ r ∈ (X.add Y).terms, r.1.rank ≤ z.unpair.1 := by
      intro X Y hX hY r hr
      simp only [AffineCombination.add, List.mem_append] at hr
      rcases hr with hr | hr
      · exact hX r hr
      · exact hY r hr
    have hpNegRank : (pNeg z).rank ≤ z.unpair.1 := hpNeg.rank_le z
    have hGNegRank : (GNeg z).rank ≤ z.unpair.1 := hGNeg.rank_le z
    have hSent : ∀ r ∈ (AffineCombination.sentenceAffine
        (fun z ↦ φ z.unpair.2) z).terms, r.1.rank ≤ z.unpair.1 := by
      intro r hr
      simp only [AffineCombination.sentenceAffine, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      subst hr
      simp [EF.rank]
    refine hstep _ _ (hstep _ _ (hstep _ _
      (pairedExpectationBlocks_terms_rank A z)
      (AffineCombination.scale_terms_rank_le _ _ hpNegRank
        (pairedExpectationBlocks_terms_rank B z)))
      (AffineCombination.scale_terms_rank_le _ _ hGNegRank hSent))
      ?_ q hq
    intro r hr
    simp [featureConstantAffine] at hr
  · -- hwide
    intro m k hk
    simp only [hBsDef, AffineCombination.add, AffineCombination.scale,
      AffineCombination.sentenceAffine, featureConstantAffine,
      pairedExpectationBlocks, LUV.expectAffine, List.length_append,
      List.length_map, List.length_range, List.length_cons, List.length_nil,
      Nat.unpair_pair]
    omega
  · -- hmag
    intro z
    obtain ⟨m, k, rfl⟩ := hpairs z
    have hpm := hpFmem (Nat.pair m k)
    have hgm := hGmem (Nat.pair m k)
    have hmagEq : (Bs (Nat.pair m k)).magnitude P =
        (pairedExpectationBlocks A (Nat.pair m k)).magnitude P +
          |(pF (Nat.pair m k)).denote P| *
            (pairedExpectationBlocks B (Nat.pair m k)).magnitude P +
          |(G (Nat.pair m k)).denote P| * 1 + 0 := by
      simp only [hBsDef, AffineCombination.add_magnitude,
        AffineCombination.scale_magnitude, featureConstantAffine_magnitude,
        AffineCombination.sentenceAffine_magnitude, hpNegDef, hGNegDef,
        EF.denote_mul, EF.denote_const, Pi.mul_apply, Rat.cast_neg, Rat.cast_one,
        neg_mul, one_mul, abs_neg]
    rw [hmagEq, show ((4:ℚ):ℝ) = 4 by norm_num]
    have h1 := pairedExpectationBlocks_magnitude_le_one A P (Nat.pair m k)
    have h2 := pairedExpectationBlocks_magnitude_le_one B P (Nat.pair m k)
    have h3 := (pairedExpectationBlocks B (Nat.pair m k)).magnitude_nonneg P
    have hpabs : |(pF (Nat.pair m k)).denote P| ≤ 1 := by
      rw [abs_of_nonneg hpm.1]; exact hpm.2
    have hgabs : |(G (Nat.pair m k)).denote P| ≤ 1 := by
      rw [abs_of_nonneg hgm.1]; exact hgm.2
    have h4 : (0:ℝ) ≤ |(pF (Nat.pair m k)).denote P| := abs_nonneg _
    nlinarith
  · -- hbdd
    intro z day
    obtain ⟨m, k, rfl⟩ := hpairs z
    rw [hprice]
    have hpm := hpFmem (Nat.pair m k)
    have hgm := hGmem (Nat.pair m k)
    have hA0 := (A k).expectApprox_nonneg (P day) (m + 1) (fun s ↦ (hP day s).1)
    have hA1 := (A k).expectApprox_le_one (P day) (m + 1) (fun s ↦ (hP day s).2)
    have hB0 := (B k).expectApprox_nonneg (P day) (m + 1) (fun s ↦ (hP day s).1)
    have hB1 := (B k).expectApprox_le_one (P day) (m + 1) (fun s ↦ (hP day s).2)
    have hs0 := (hP day (φ k)).1
    have hs1 := (hP day (φ k)).2
    rw [abs_le]
    constructor <;> [skip; skip] <;> push_cast <;>
      nlinarith [hpm.1, hpm.2, hgm.1, hgm.2]
  · -- hsmall
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
    refine ⟨N, fun m k hk hkm hfk v hv ↦ ?_⟩
    obtain ⟨hBv, hAv⟩ := hsemantic m k hfk v hv
    have hmR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hsmallm : 2 / ((m : ℝ) + 1) ≤ ε := by
      have hNm : (2 : ℝ) / ε < (m : ℝ) + 1 := by
        refine hN.trans_le ?_
        have : (N : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast le_of_lt (lt_of_le_of_lt hk hkm)
        linarith
      rw [div_lt_iff₀ hε] at hNm
      rw [div_le_iff₀ hmR]
      nlinarith
    have hnearA : |(A k).expectApprox v.payout (m + 1) -
        v.payout (φ k) * (G (Nat.pair m k)).denote P| ≤ 1 / ((m : ℝ) + 1) := by
      simpa using hAv.expectApprox_near (n := m + 1) m.succ_pos
    have hnearB : |(B k).expectApprox v.payout (m + 1) -
        (G (Nat.pair m k)).denote P| ≤ 1 / ((m : ℝ) + 1) := by
      simpa using hBv.expectApprox_near (n := m + 1) m.succ_pos
    have hpk : (pF (Nat.pair m k)).denote P = (p k : ℝ) :=
      hpDenote m k (le_of_lt hkm)
    have hpabs : |(p k : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by exact_mod_cast (hp k).1)]
      exact_mod_cast (hp k).2
    rw [hvalue, hpk]
    set eA := (A k).expectApprox v.payout (m + 1) -
      v.payout (φ k) * (G (Nat.pair m k)).denote P with heA
    set eB := (B k).expectApprox v.payout (m + 1) -
      (G (Nat.pair m k)).denote P with heB
    have hform : (A k).expectApprox v.payout (m + 1) +
        (-(p k : ℝ)) * (B k).expectApprox v.payout (m + 1) +
        (-(G (Nat.pair m k)).denote P) * v.payout (φ k) +
        (p k : ℝ) * (G (Nat.pair m k)).denote P = eA - (p k : ℝ) * eB := by
      rw [heA, heB]; ring
    rw [hform]
    have hmulB : |(p k : ℝ)| * |eB| ≤ 1 / ((m : ℝ) + 1) := by
      calc |(p k : ℝ)| * |eB| ≤ 1 * (1 / ((m : ℝ) + 1)) :=
            mul_le_mul hpabs hnearB (abs_nonneg _) (by positivity)
        _ = _ := one_mul _
    calc |eA - (p k : ℝ) * eB| ≤ |eA| + |(p k : ℝ) * eB| := abs_sub _ _
      _ = |eA| + |(p k : ℝ)| * |eB| := by rw [abs_mul]
      _ ≤ 1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1) := add_le_add hnearA hmulB
      _ = 2 / ((m : ℝ) + 1) := by ring
      _ ≤ ε := hsmallm

end DeferralFibre

/-! ## Interval quotation package -/

/-- Construct the complete interval-introspection quotation package from the literal
current-price feature, generated rational endpoints, a generated continuous width, and
one arithmetically reflected Boolean interval claim.  Both affine certificates are
concrete one-share portfolios; the outward sum is normalized by `1/2`. -/
noncomputable def introspectionIntervalQuoteOfCode
    {P : History} {DP : DeductiveProcess} {T : ArithmeticTheory}
    (Q : QuotationTheoryPresentation DP T)
    (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ)
    (a b δ : ℕ → ℚ)
    (lowerFeature : ℕ → EF)
    (hlower : GeneratedRatFeature P a lowerFeature)
    (upperFeature : ℕ → EF)
    (hupper : GeneratedRatFeature P b upperFeature)
    (hδ : PolyRatCodes δ) (hδinv : PolyRatCodes (fun n ↦ 1 / δ n))
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
    width_codes := hδ
    inverse_width_codes := hδinv
    width_pos := hδpos
    width_tendsto_zero := hδzero
    probability_bounds := hab
    quote := q.sentence
    quote_codes := RpnSentenceCodes.ofPolySentenceCodes q.sentence_poly
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
uniform diagonal law inside the presented arithmetic theory: a genuine self-referential
arithmetic sentence, not a stipulated relation, backs the quoted decision. -/
lemma ParameterizedDiagonalQuoteCode.diagonal_law
    {DP : DeductiveProcess} {T : ArithmeticTheory} {truth : ℕ → Prop}
    (Q : QuotationTheoryPresentation DP T)
    (q : ParameterizedDiagonalQuoteCode T truth) :
    T ⊢ ∀⁰ (parameterizedFixedpoint q.body 🡘
      q.body/[⌜parameterizedFixedpoint q.body⌝, #0]) := by
  letI : 𝗜𝚺₁ ⪯ T := Q.theory_sigmaOne
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
    Primrec₂.natPair.comp (Primrec.const 4)
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
  simp only [decodedComputation, Denumerable.ofNat_encode]
  rw [diagonalPriceDecisionCode_eval]
  change
    (1 ∈ Part.some (if market.quote n
      (Encodable.encode
        (quoteAtom
          (Nat.pair (Encodable.encode (diagonalPriceDecisionCode market p)) n))) < p
      then 1 else 0)) ↔
    market.quote n
      (Encodable.encode
        (quoteAtom
          (Nat.pair (Encodable.encode (diagonalPriceDecisionCode market p)) n))) < p
  by_cases h : market.quote n
      (Encodable.encode
        (quoteAtom
          (Nat.pair (Encodable.encode (diagonalPriceDecisionCode market p)) n))) < p <;>
    simp [h]

/-- The fixed selector's negative quote is exactly the complement of its diagonal predicate.
Paper node: `thm:lp` -/
lemma diagonalPriceQuoteNeg_iff
    {P : History} (market : MarketComputation P) (p : ℚ) (n : ℕ) :
    quoteNeg (Encodable.encode (diagonalPriceDecisionCode market p)) n ↔
      ¬diagonalPriceTruth market p n := by
  classical
  rw [quoteNeg]
  simp only [decodedComputation, Denumerable.ofNat_encode]
  rw [diagonalPriceDecisionCode_eval]
  change
    (0 ∈ Part.some (if market.quote n
      (Encodable.encode
        (quoteAtom
          (Nat.pair (Encodable.encode (diagonalPriceDecisionCode market p)) n))) < p
      then 1 else 0)) ↔
    ¬market.quote n
      (Encodable.encode
        (quoteAtom
          (Nat.pair (Encodable.encode (diagonalPriceDecisionCode market p)) n))) < p
  by_cases h : market.quote n
      (Encodable.encode
        (quoteAtom
          (Nat.pair (Encodable.encode (diagonalPriceDecisionCode market p)) n))) < p <;>
    simp [h]

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
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (p : ℚ) :
    ParameterizedDiagonalQuoteCode T (diagonalPriceTruth market p) where
  toBooleanQuoteCode := {
    code := Encodable.encode (diagonalPriceDecisionCode market p)
    pos_complete := fun n hn =>
      (re_complete universalQuotePos_re).mp <| by
        simpa [Nat.unpair_pair] using (diagonalPriceQuotePos_iff market p n).mpr hn
    neg_complete := fun n hn =>
      (re_complete universalQuoteNeg_re).mp <| by
        simpa [Nat.unpair_pair] using (diagonalPriceQuoteNeg_iff market p n).mpr hn
  }
  body := diagonalPriceBody market p
  represents_fixedpoint := diagonalPriceFixedpoint_spec market p

lemma parameterizedDiagonalQuoteCodeOfMarket_sentence
    {P : History} (market : MarketComputation P) (T : ArithmeticTheory)
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (p : ℚ) (n : ℕ) :
    (parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n =
      quoteAtom
        (Nat.pair (Encodable.encode (diagonalPriceDecisionCode market p)) n) :=
  rfl

/-- The constructor's represented arithmetic fixed point is exactly the same-day price
comparison for its inherited public atom.  This is the semantic link between the
arithmetic fixed point and the public atom, derived here rather than assumed.
Paper node: `thm:lp` -/
lemma parameterizedDiagonalQuoteCodeOfMarket_public_fixedpoint
    {P : History} (market : MarketComputation P) (T : ArithmeticTheory)
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (p : ℚ) (n : ℕ) :
    ((parameterizedFixedpoint
          (parameterizedDiagonalQuoteCodeOfMarket market T p).body).Evalb ![n]) ↔
      P n
        ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n) <
          (p : ℝ) := by
  rw [(parameterizedDiagonalQuoteCodeOfMarket market T p).represents_fixedpoint n,
    market.quote_exact]
  change market.quote n
      (Encodable.encode
        ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n)) <
        p ↔
    (market.quote n
      (Encodable.encode
        ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n)) :
          ℝ) < (p : ℝ)
  norm_cast

lemma parameterizedDiagonalQuoteCodeOfMarket_public_price_iff
    {P : History} (market : MarketComputation P) (T : ArithmeticTheory)
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (p : ℚ) (n : ℕ) :
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

/-! ## Paradox-resistance quotation package -/

/-- Construct paradox resistance directly from a named computable market.  The public atom,
its decision code, and its FFL fixed point are all built internally, so there is no
caller-supplied self-reference premise. -/
noncomputable def paradoxResistanceQuoteOfDiagonal
    {P : History} {DP : DeductiveProcess} {T : ArithmeticTheory}
    [T.SoundOnHierarchy 𝚺 1] (Q : QuotationTheoryPresentation DP T)
    (market : MarketComputation P)
    (p : ℚ) (width : ℕ → ℚ)
    (hwidth : PolyRatCodes width)
    (hwidthInv : PolyRatCodes (fun n ↦ 1 / width n))
    (hwidthPos : ∀ n, 0 < width n)
    (hwidthZero : Tendsto (fun n ↦ (width n : ℝ)) atTop (𝓝 0)) :
    ParadoxResistanceQuote P DP p := by
  letI : 𝗜𝚺₁ ⪯ T := Q.theory_sigmaOne
  let q := parameterizedDiagonalQuoteCodeOfMarket market T p
  let quote := q.toBooleanQuoteCode
  let price : ℕ → EF := currentPriceFeature quote.sentence
  let pFeature : ℕ → EF := AffineCombination.constantRatFeature p
  let lower : ℕ → EF := ctsIndFeature width pFeature price
  let upper : ℕ → EF := ctsIndFeature width price pFeature
  have hquote : RpnSentenceCodes quote.sentence :=
    RpnSentenceCodes.ofPolySentenceCodes quote.sentence_poly
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
    width_codes := hwidth
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

/-- Package the preceding theorem in the exact deferred interface consumed by Self-Trust. -/
noncomputable def CompletedAffineQuoteApprox.toAffineQuoteEq
    {P : History} {DP : DeductiveProcess} {gap : ℕ → ℝ}
    (q : CompletedAffineQuoteApprox P DP gap) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) : AffineQuoteEq P f gap where
  toAffineQuotePortfolio := q.toAffineQuotePortfolio
  future_coherent := by
    simpa only [AsympEq, _root_.sub_zero] using
      q.future_price_tendsto_zero hworld f

/-! ## Concrete deferred expectation quotation -/

/-- Strict deferral tends to infinity even when it grows too quickly to be polynomial in
its source index. -/
lemma DeferralFunction.tendsto_atTop (f : DeferralFunction) :
    Tendsto f atTop atTop := by
  apply tendsto_atTop_atTop.2
  intro N
  exact ⟨N, fun n hn ↦ hn.trans (f.lt n).le⟩

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
  let a := Classical.choose f.fueled
  let degree := Classical.choose (Classical.choose_spec f.fueled)
  have hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k) := by
    simpa [a, degree, PrefixPatchCompile.ecClock] using
      Classical.choose_spec (Classical.choose_spec f.fueled)
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
      (DeferralFibre.pairedExpectationFeature_paired X hX) hHmem Y hY
      (fun m k hfk v hv ↦ by
        rw [DeferralFibre.pairedExpectationFeature_denote, ← hfk]
        exact reflected k v hv) hP
    refine Tendsto.congr' (Eventually.of_forall fun n ↦ ?_) h
    rw [DeferralFibre.pairedExpectationFeature_denote]
    rfl
  have hcrossX0 := DeferralFibre.crossPrecision_deferred_tendsto_zero hworld f hspec
    X hX source_valued hP
  have hcrossY0 := DeferralFibre.crossPrecision_deferred_tendsto_zero hworld f hspec
    Y hY quote_valued hP
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
    (hφ : RpnSentenceCodes φ) (hY : LUV.RpnThresholdCodeSeq Y)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Y n) (P (f n) (φ n)))
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    FuturePriceQuote P DP f φ Y := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  let a := Classical.choose f.fueled
  let degree := Classical.choose (Classical.choose_spec f.fueled)
  have hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k) := by
    simpa [a, degree, PrefixPatchCompile.ecClock] using
      Classical.choose_spec (Classical.choose_spec f.fueled)
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
    Y hY quote_valued hP
  let sentenceFamily := AffineCombination.sentenceAffine φ
  let quoteFamily := LUV.expectAffineSeq Y
  let raw : ℕ → AffineCombination := fun n ↦
    (sentenceFamily n).add (quoteFamily n).neg
  let hsentence := AffineCombination.sentenceAffine_polySequence φ hφ
  let hquote := LUV.expectAffineSeq_polySequence Y hY
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
  let a := Classical.choose f.fueled
  let degree := Classical.choose (Classical.choose_spec f.fueled)
  have hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k) := by
    simpa [a, degree, PrefixPatchCompile.ecClock] using
      Classical.choose_spec (Classical.choose_spec f.fueled)
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
    Z hZ Zvalued hP
  have hcrossZ'0 := DeferralFibre.crossPrecision_deferred_tendsto_zero hworld f hspec
    Z' hZ' Z'valued hP
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
    (hφ : RpnSentenceCodes φ) (hδ : PolyRatCodes δ)
    (hδinv : PolyRatCodes (fun n ↦ 1 / δ n))
    (pFeature : ℕ → EF) (hp : GeneratedRatFeature P p pFeature)
    (hA : LUV.RpnThresholdCodeSeq A)
    (hB : LUV.RpnThresholdCodeSeq B)
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
  let a := Classical.choose f.fueled
  let degree := Classical.choose (Classical.choose_spec f.fueled)
  have hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k) := by
    simpa [a, degree, PrefixPatchCompile.ecClock] using
      Classical.choose_spec (Classical.choose_spec f.fueled)
  let δp : ℕ → ℚ := fun z ↦ δ (min z.unpair.2 z.unpair.1)
  have hδpInv : PolyRatCodes (fun z ↦ 1 / δp z) :=
    hδinv.reindex PairedWeighting.clampedSource_polyFueled
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
    polySeg := RpnSpliceStream.serialize_mul
      (RpnSpliceStream.serialize_const (-1))
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
    delta_codes := hδ
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
    (hφ : RpnSentenceCodes φ) (hY : LUV.RpnThresholdCodeSeq Y)
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
    (hφ : RpnSentenceCodes φ) (hδ : PolyRatCodes δ)
    (pFeature : ℕ → EF) (hp : GeneratedRatFeature P p pFeature)
    (hA : LUV.RpnThresholdCodeSeq A)
    (hB : LUV.RpnThresholdCodeSeq B)
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
      probability_mem hφ hδ (hδ.inv_of_pos delta_pos) pFeature hp hA hB
      confidence_reflected product_reflected hworld)

/-! ## Direct same-day consumers -/

/-- Paper-facing `thm:epr` entry point from concrete arithmetic quotation code.
Paper node: `thm:epr` -/
theorem lic_expectations_of_probabilities_ofCode
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    (Q : QuotationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    {value : ℕ → ℚ} (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ)
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
    (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ)
    (a b δ : ℕ → ℚ)
    (lowerFeature : ℕ → EF)
    (hlower : GeneratedRatFeature P a lowerFeature)
    (upperFeature : ℕ → EF)
    (hupper : GeneratedRatFeature P b upperFeature)
    (hδ : PolyRatCodes δ)
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
    lowerFeature hlower upperFeature hupper hδ (hδ.inv_of_pos hδpos) hδpos hδzero hab q hP
  exact lic_introspection P DP φ a b δ package hworld

/-- Paper-facing `thm:lp` entry point.  Its genuine parameterized fixed point and public
diagonal atom are constructed from `market`; no semantic diagonal premise is accepted.
Paper node: `thm:lp` -/
theorem lic_paradox_resistance_ofDiagonal
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : QuotationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    (market : MarketComputation P)
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (width : ℕ → ℚ) (hwidth : PolyRatCodes width)
    (hwidthPos : ∀ n, 0 < width n)
    (hwidthZero : Tendsto (fun n ↦ (width n : ℝ)) atTop (𝓝 0))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n
      ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n)) ≈ₙ
      fun _ => (p : ℝ) := by
  let package := paradoxResistanceQuoteOfDiagonal Q market p width hwidth
    (hwidth.inv_of_pos hwidthPos) hwidthPos hwidthZero
  exact lic_paradox_resistance P DP p hp0 hp1 package hworld

/-! ## Positive and complementary quotation paths -/

/-- A concrete FFL-backed Boolean quote whose represented predicate is always true. -/
noncomputable def trueBooleanQuoteCode
    (T : ArithmeticTheory) [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    BooleanQuoteCode T (fun _ ↦ True) :=
  BooleanQuoteCode.ofComputable (ComputablePred.const True)

/-- A concrete FFL-backed Boolean quote whose represented predicate is always false. -/
noncomputable def falseBooleanQuoteCode
    (T : ArithmeticTheory) [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    BooleanQuoteCode T (fun _ ↦ False) :=
  BooleanQuoteCode.ofComputable (ComputablePred.const False)

/-- `N+`: the positive arithmetic quotation schema reaches the public process. -/
lemma quotationRepresentation_positive_path
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : QuotationTheoryPresentation DP T) (n : ℕ) :
    ∃ k, (trueBooleanQuoteCode T).sentence n ∈ DP.D k := by
  let q := trueBooleanQuoteCode T
  exact Q.quote_positive_enters q.code n (q.pos_complete n trivial)

/-- `N+`: the complementary arithmetic schema reaches the public process as a negated
literal, exercising the separate negative quotation path. -/
lemma quotationRepresentation_negative_path
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : QuotationTheoryPresentation DP T) (n : ℕ) :
    ∃ k, (∼(falseBooleanQuoteCode T).sentence n) ∈ DP.D k := by
  let q := falseBooleanQuoteCode T
  exact Q.quote_negative_refutes q.code n (q.neg_complete n not_false)

#print axioms quotationClaimCode_injective
#print axioms quotationClaimSentence_poly
#print axioms BooleanQuoteCode.reflected
#print axioms RationalQuoteCode.reflected
#print axioms ParameterizedDiagonalQuoteCode.diagonal_law
#print axioms diagonalPriceDecisionPart_partrec
#print axioms diagonalPriceDecisionCode_eval
#print axioms parameterizedDiagonalQuoteCodeOfMarket_public_fixedpoint
#print axioms CompletedAffineQuoteApprox.future_price_tendsto_zero
#print axioms CompletedAffineQuoteApprox.toAffineQuoteEq
#print axioms expectedFutureExpectationQuoteOfRepresentation
#print axioms futurePriceQuoteOfRepresentation
#print axioms conditionalExpectationQuoteOfRepresentation
#print axioms selfTrustQuoteOfRepresentation
#print axioms lic_expected_future_expectations_ofRepresentation
#print axioms lic_no_expected_net_update_ofRepresentation
#print axioms lic_no_expected_net_update_conditional_ofRepresentation
#print axioms lic_self_trust_ofRepresentation
#print axioms introspectionIntervalQuoteOfCode
#print axioms paradoxResistanceQuoteOfDiagonal
#print axioms lic_expectations_of_probabilities_ofCode
#print axioms lic_iterated_expectations_ofCode
#print axioms lic_introspection_ofCode
#print axioms lic_paradox_resistance_ofDiagonal
#print axioms quotationRepresentation_positive_path
#print axioms quotationRepresentation_negative_path

end LogicalInduction
