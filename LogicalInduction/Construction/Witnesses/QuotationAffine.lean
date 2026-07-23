import LogicalInduction.Construction.Witnesses.ComputationSyntax
import LogicalInduction.Construction.Witnesses.FeedbackEmission
import LogicalInduction.Properties.Introspection
import Foundation.FirstOrder.Bootstrapping.FixedPoint

/-!
# Arithmetic quotation and affine-package construction

The public market language is propositional, while the paper's quotation mechanism is
first-order arithmetic.  This file makes that boundary concrete.  Every quoted Boolean
decision is represented by a positive and a complementary FFL arithmetic schema; the pair
has one injective, polynomially emitted propositional name.  A quoted rational value uses
the same dual-schema mechanism at every rational threshold.  Consequently a world
consistent with the completed deductive theory values the resulting LUV correctly.

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

The old quotation fields quantified over two *independent, arbitrary* schemas
`positive negative : ArithmeticSemisentence 1`, keyed only by an `input`.  That freedom is
what made the interface **vacuous** alongside the market non-vacuity hypothesis `hworld`:
taking `positive = negative = ⊤` forces an atom and its negation into a common stage, so no
world is consistent with it.  It also makes the deductive process **non-computable** (there
is no uniform enumeration of provable instances over all schemas).

The redesign folds a *decidable-decision selector* `code : ℕ` into the numeral of two
**fixed** universal schemas, mirroring the computation side (`ComputationSyntax`), whose
fixed complementary schemas are exactly what keep it non-vacuous *and* computably
enumerable.  The positive and negative fibers of one partial-recursive computation are
mutually exclusive by determinism, so the provability world can believe the positive
literal without ever being forced into a contradiction, and the schema is a fixed constant
so its instances are enumerable via `provable_instances_re`. -/

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
translation.  Unlike the old quote packages this object contains no sentence family,
LUV, price, affine combination, or asymptotic field.

The quotation fields are **code-indexed** (`dd:quote-code`): a selector `code : ℕ` naming
a decidable decision, folded into the numeral of the two fixed universal schemas
`universalQuotePos`/`universalQuoteNeg`.  This kills the old `⊤,⊤` vacuity (the schemas are
fixed and complementary) and makes the process computably enumerable.
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
  threshold_poly : LUV.PolyThresholdCodeSeq (fun n => arithmeticThresholdLUV code n)

namespace RationalQuoteCode

noncomputable def luv {T : ArithmeticTheory} {value : ℕ → ℚ}
    (q : RationalQuoteCode T value) (n : ℕ) : LUV :=
  arithmeticThresholdLUV q.code n

lemma poly {T : ArithmeticTheory} {value : ℕ → ℚ}
    (q : RationalQuoteCode T value) : LUV.PolyThresholdCodeSeq q.luv :=
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

/-- The day-indexed expectation mesh for a varying LUV family. -/
def expectAffineSeq (X : ℕ → LUV) (n : ℕ) : AffineCombination :=
  (X n).expectAffine n

lemma expectAffineSeq_price (X : ℕ → LUV) (P : History) (n : ℕ) :
    (expectAffineSeq X n).price P n = (X n).expect P n :=
  (X n).expectAffine_price P n

lemma expectAffineSeq_value (X : ℕ → LUV) (P : History)
    (w : Valuation) (n : ℕ) :
    (expectAffineSeq X n).value P w = (X n).expectApprox w n :=
  (X n).expectAffine_value P w n

lemma expectAffineSeq_magnitude_le_one (X : ℕ → LUV)
    (P : History) (n : ℕ) :
    (expectAffineSeq X n).magnitude P ≤ 1 :=
  (X n).expectAffine_magnitude_le_one P n

/-- A compact varying threshold presentation emits the literal diagonal expectation
mesh uniformly; no opaque serialized affine object is decoded. -/
noncomputable def expectAffineSeq_polySequence (X : ℕ → LUV)
    (hcode : LUV.PolyThresholdCodeSeq X) :
    AffineCombination.PolySequence (expectAffineSeq X) := by
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  let cX := Classical.choose hcode
  have hX := Classical.choose_spec hcode
  have hindex : PolyFueled
      (Nat.Partrec.Code.left.pair
        (Nat.Partrec.Code.left.pair Nat.Partrec.Code.right))
      (fun z : ℕ ↦
      Nat.pair z.unpair.1 (Nat.pair z.unpair.1 z.unpair.2)) :=
    PolyFueled.left.pair (PolyFueled.left.pair PolyFueled.right)
  have hsentence := hX.comp hindex
  exact {
    termCount := fun n ↦ n
    coefficient := fun z ↦ .const (1 / (z.unpair.1 : ℚ))
    sentence := fun z ↦
      (X z.unpair.1).gt ((z.unpair.2 : ℚ) / (z.unpair.1 : ℚ))
    termCount_poly := ⟨Nat.Partrec.Code.id, PolyFueled.id⟩
    const_poly := PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
    coefficient_poly := PolySegStream.ofTokenStream
      (PolyTokenStream.serialize_const_comp
        ⟨cinv.comp Nat.Partrec.Code.left, hinv.comp PolyFueled.left⟩)
    sentence_poly := ⟨cX.comp (Nat.Partrec.Code.left.pair
        (Nat.Partrec.Code.left.pair Nat.Partrec.Code.right)),
      hsentence.of_eq (fun z ↦ by simp)⟩
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
  terms := ((Y n).expectAffine n).terms.map fun p ↦
    (EF.mul (EF.const (-1)) p.1, p.2)

lemma numericQuoteAffine_value (H : ℕ → EF) (Y : ℕ → LUV)
    (P : History) (w : Valuation) (n : ℕ) :
    (numericQuoteAffine H Y n).value P w =
      (H n).denote P - (Y n).expectApprox w n := by
  let l := ((Y n).expectAffine n).terms
  have hbase : (l.map (fun p ↦ p.1.denote P * w p.2)).sum =
      (Y n).expectApprox w n := by
    have h := (Y n).expectAffine_value P w n
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
      (H n).denote P - (Y n).expectApprox (P m) n := by
  rw [AffineCombination.price, numericQuoteAffine_value]

lemma numericQuoteAffine_magnitude (H : ℕ → EF) (Y : ℕ → LUV)
    (P : History) (n : ℕ) :
    (numericQuoteAffine H Y n).magnitude P =
      ((Y n).expectAffine n).magnitude P := by
  simp only [numericQuoteAffine, AffineCombination.magnitude, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp

/-- Polynomial emission of the concrete target-minus-threshold mesh. -/
noncomputable def numericQuoteAffine_polySequence
    (H : ℕ → EF) (Y : ℕ → LUV)
    (hH : PGenerableWeighting H) (hY : LUV.PolyThresholdCodeSeq Y) :
    AffineCombination.PolySequence (numericQuoteAffine H Y) := by
  let base := LUV.expectAffineSeq_polySequence Y hY
  exact {
    termCount := base.termCount
    coefficient := fun z ↦ EF.mul (EF.const (-1)) (base.coefficient z)
    sentence := base.sentence
    termCount_poly := base.termCount_poly
    const_poly := hH.polySeg
    coefficient_poly := PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1)))
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
    have hE0 := (q.luv n).expectApprox_nonneg (P m) n
      (fun s ↦ (hP m s).1)
    have hE1 := (q.luv n).expectApprox_le_one (P m) n
      (fun s ↦ (hP m s).2)
    have hv0 : (0 : ℝ) ≤ value n := by exact_mod_cast (q.value_mem n).1
    have hv1 : (value n : ℝ) ≤ 1 := by exact_mod_cast (q.value_mem n).2
    constructor <;> linarith
  magnitude_le_one := by
    intro n
    rw [numericQuoteAffine_magnitude]
    exact (q.luv n).expectAffine_magnitude_le_one P n
  theory_coherent := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine eventually_atTop.2 ⟨max 1 N, fun n hn v hv ↦ ?_⟩
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hsmall : 1 / (n : ℝ) ≤ ε := by
      have hNn : (1 : ℝ) / ε < n :=
        hN.trans_le (by exact_mod_cast (le_trans (le_max_right 1 N) hn))
      rw [div_lt_iff₀ hε] at hNn
      rw [div_le_iff₀ hnR]
      nlinarith
    rw [numericQuoteAffine_value, target.denote, abs_sub_comm]
    exact ((q.reflected Q n v hv).expectApprox_near hn0).trans hsmall

/-! ### The two same-day numeric quotation packages -/

/-- Closed feature carrying the actual current price of a polynomial sentence family. -/
def currentPriceFeature (φ : ℕ → Sentence) (n : ℕ) : EF :=
  EF.price (φ n) n

lemma currentPriceFeature_generated (φ : ℕ → Sentence)
    (hφ : PolySentenceCodes φ) :
    PGenerableWeighting (currentPriceFeature φ) := by
  obtain ⟨cφ, hcφ⟩ := hφ
  have htok : PolyTokenStream
      (fun n ↦ (currentPriceFeature φ n).serialize) := by
    simpa [currentPriceFeature, EF.serialize, List.append_assoc] using
      ((PolyTokenStream.const 0).append
        ((PolyTokenStream.polyTok hcφ).append
          (PolyTokenStream.polyTok PolyFueled.id)))
  exact {
    polySeg := PolySegStream.ofTokenStream htok
    rank_le := by intro n; simp [currentPriceFeature]
    closed := by intro n ρ V; simp [currentPriceFeature]
  }

noncomputable def currentPriceNumericTarget
    {P : History} {T : ArithmeticTheory} {value : ℕ → ℚ}
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ)
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
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ)
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
    (hX : LUV.PolyThresholdCodeSeq X) :
    PGenerableWeighting (currentExpectationFeature X) := by
  let hmesh := LUV.expectAffineSeq_polySequence X hX
  have hdiag : PolyFueled
      (Nat.Partrec.Code.id.pair Nat.Partrec.Code.id)
      (fun n : ℕ ↦ Nat.pair n n) := PolyFueled.id.pair PolyFueled.id
  exact {
    polySeg := PolySegStream.of_eq (hmesh.priceFeature_polySeg.comp hdiag)
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
    (X : ℕ → LUV) (hX : LUV.PolyThresholdCodeSeq X)
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
    (X : ℕ → LUV) (hX : LUV.PolyThresholdCodeSeq X)
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
    const_poly := PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const scale)) hH.polySeg
    coefficient_poly := PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-scale)))
      (hH.polySeg.comp PolyFueled.left)
    sentence_poly := ⟨cq.comp Nat.Partrec.Code.left, hcq.comp PolyFueled.left⟩
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
    const_poly := PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
    coefficient_poly := PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const scale))
      (hH.polySeg.comp PolyFueled.left)
    sentence_poly := ⟨cq.comp Nat.Partrec.Code.left, hcq.comp PolyFueled.left⟩
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
  polySeg := PolySegStream.serialize_mul hA.polySeg hB.polySeg
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
  polySeg := PolySegStream.serialize_add hA.polySeg hB.polySeg
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
  polySeg := PolySegStream.ofTokenStream h.polyTok
  rank_le := h.rank_le
  closed := h.closed

/-- A polynomial rational code sequence, viewed as a closed constant feature on each day. -/
def ratCodeFeature (q : ℕ → ℚ) (n : ℕ) : EF :=
  EF.const (q n)

lemma ratCodeFeature_generated (P : History) (q : ℕ → ℚ)
    (hq : PolyRatCodes q) : GeneratedRatFeature P q (ratCodeFeature q) where
  rank_le := by intro n; simp [ratCodeFeature]
  polyTok := PolyTokenStream.serialize_const_comp hq
  closed := by intro n ρ V; simp [ratCodeFeature]
  denote := by intro n; simp [ratCodeFeature]

/-- Polynomial rational codes remain polynomial after a polynomially fueled reindexing. -/
lemma PolyRatCodes.reindex {q : ℕ → ℚ} (hq : PolyRatCodes q)
    {index : ℕ → ℕ} (hindex : ∃ c, PolyFueled c index) :
    PolyRatCodes (fun n ↦ q (index n)) := by
  obtain ⟨cq, hq⟩ := hq
  obtain ⟨ci, hi⟩ := hindex
  exact ⟨cq.comp ci, hq.comp hi⟩

/-- Express `ctsInd δ x y` using only the repository's allowed feature operations. -/
def ctsIndFeature (δ : ℕ → ℚ) (x y : ℕ → EF) (n : ℕ) : EF :=
  clip01 (EF.mul
    (EF.add (x n) (EF.mul (EF.const (-1)) (y n)))
    (EF.const (1 / δ n)))

lemma ctsIndFeature_generated (δ : ℕ → ℚ) (x y : ℕ → EF)
    (hδinv : PolyRatCodes (fun n ↦ 1 / δ n))
    (hx : PGenerableWeighting x) (hy : PGenerableWeighting y) :
    PGenerableWeighting (ctsIndFeature δ x y) := by
  have hinv : PolySegStream (fun n ↦ (EF.const (1 / δ n)).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const_comp hδinv)
  have hnegY := PolySegStream.serialize_mul
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) hy.polySeg
  exact {
    polySeg := PolySegStream.serialize_clip01
      (PolySegStream.serialize_mul (PolySegStream.serialize_add hx.polySeg hnegY) hinv)
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

/-! ## Strict deferral reindexing -/

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

lemma deferralMatchCount_at
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k =
      some (f k)) (n : ℕ) :
    deferralMatchCount f a degree (f n) = 1 := by
  let lenFn : ℕ → ℕ := fun z => FeedbackEmission.scheduledMatch f a degree z
  have hscan : ∀ k, k ≤ f n →
      segPrefix lenFn (f n) k = if n < k then 1 else 0 := by
    intro k hk
    induction k with
    | zero => simp [segPrefix]
    | succ k ih =>
        rw [segPrefix_succ, ih (by omega)]
        have hmatch : lenFn (Nat.pair (f n) k) = if k = n then 1 else 0 := by
          rw [show lenFn (Nat.pair (f n) k) =
            FeedbackEmission.scheduledMatch f a degree (Nat.pair (f n) k) by rfl]
          by_cases hkn : k = n
          · subst k
            simpa using
              (FeedbackEmission.scheduledMatch_eq_one_iff f hspec (f n) n).2 rfl
          · have hne : f k ≠ f n := fun h => hkn (hstrict.injective h)
            simpa [hkn] using
              (FeedbackEmission.scheduledMatch_eq_zero_iff f hspec (f n) k).2 hne
        rw [hmatch]
        split_ifs <;> omega
  rw [deferralMatchCount, hscan (f n) le_rfl]
  simp [f.lt n]

lemma deferralPreimage_at
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
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
          · have hne : f k ≠ f n := fun h => hkn (hstrict.injective h)
            simpa [hkn] using
              (FeedbackEmission.scheduledMatch_eq_zero_iff f hspec (f n) k).2 hne
        simp only [lenFn, Nat.unpair_pair, hmatch]
        split_ifs <;> omega
  rw [deferralPreimage, hscan (f n) le_rfl]
  simp [f.lt n]

lemma deferralImageFlag_at
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k =
      some (f k)) (n : ℕ) :
    deferralImageFlag f a degree (f n) = 1 := by
  rw [deferralImageFlag, deferralMatchCount_at f hstrict hspec n]
  simp

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

lemma deferralPreimage_spec
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    {m : ℕ} (hm : deferralImageFlag f a degree m = 1) :
    deferralPreimage f a degree m < m ∧
      f (deferralPreimage f a degree m) = m := by
  obtain ⟨k, hk, hfk⟩ := (deferralImageFlag_eq_one_iff f hspec m).1 hm
  have hidx : deferralPreimage f a degree m = k := by
    rw [← hfk]
    exact deferralPreimage_at f hstrict hspec k
  rw [hidx]
  exact ⟨hk, hfk⟩

/-- The image flag as a closed, polynomially emitted feature. -/
def deferralImageFeature (f : DeferralFunction) (a degree m : ℕ) : EF :=
  EF.const (deferralImageFlag f a degree m : ℚ)

lemma deferralImageFeature_generated (f : DeferralFunction) (a degree : ℕ) :
    PGenerableWeighting (deferralImageFeature f a degree) := by
  obtain ⟨cflag, hflag⟩ := deferralImageFlag_polyFueled f a degree
  have hcodes := ratNatCast_codes_of_polyFueled hflag
  exact {
    polySeg := PolySegStream.ofTokenStream
      (PolyTokenStream.serialize_const_comp hcodes)
    rank_le := by intro n; simp [deferralImageFeature]
    closed := by intro n ρ V; simp [deferralImageFeature]
  }

@[simp] theorem deferralImageFeature_denote
    (f : DeferralFunction) (a degree m : ℕ) (P : History) :
    (deferralImageFeature f a degree m).denote P =
      (deferralImageFlag f a degree m : ℝ) := by
  simp [deferralImageFeature]

/-! ### Reindexed threshold syntax and cross-precision meshes -/

lemma LUV.PolyThresholdCodeSeq.reindex
    {X : ℕ → LUV} (hX : LUV.PolyThresholdCodeSeq X)
    {index : ℕ → ℕ} (hindex : ∃ c, PolyFueled c index) :
    LUV.PolyThresholdCodeSeq (fun n ↦ X (index n)) := by
  obtain ⟨cX, hX⟩ := hX
  obtain ⟨ci, hi⟩ := hindex
  have hquery : PolyFueled _ (fun z : ℕ ↦
      Nat.pair (index z.unpair.1) z.unpair.2) :=
    (hi.comp PolyFueled.left).pair PolyFueled.right
  exact ⟨_, (hX.comp hquery).of_eq (fun z ↦ by simp)⟩

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
  let csA := Classical.choose hA.sentence_poly
  have hsA := Classical.choose_spec hA.sentence_poly
  let csB := Classical.choose hB.sentence_poly
  have hsB := Classical.choose_spec hB.sentence_poly
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
  have hcoeff := PolySegStream.ifZero hA.coefficient_poly
    (hB.coefficient_poly.comp hqueryB) htest
  have hsentence : ∃ c, PolyFueled c (fun z ↦ Encodable.encode
      (if z.unpair.2 < hA.termCount z.unpair.1 then hA.sentence z
      else hB.sentence (Nat.pair z.unpair.1
        (z.unpair.2 - hA.termCount z.unpair.1)))) := by
    let hsel := ifzSel_polyFueled.comp
      (((hsA.pair (hsB.comp hqueryB)).pair htest))
    exact ⟨_, hsel.of_eq (fun z ↦ by
      simp only [Nat.unpair_pair, ifzSelFn]
      by_cases hjlt : z.unpair.2 < hA.termCount z.unpair.1
      · rw [if_pos hjlt, if_pos (by omega)]
      · rw [if_neg hjlt, if_neg (by omega)])⟩
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
    const_poly := PolySegStream.serialize_add hA.const_poly hB.const_poly
    coefficient_poly := PolySegStream.of_eq hcoeff (fun z ↦ by
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
  const_poly := PolySegStream.serialize_mul hW.polySeg hA.const_poly
  coefficient_poly := PolySegStream.serialize_mul
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

/-- Difference between two threshold meshes of the same represented LUV. -/
def LUV.crossPrecisionAffine (X : ℕ → LUV) (low high : ℕ → ℕ)
    (n : ℕ) : AffineCombination where
  const := EF.const 0
  terms := ((X n).expectAffine (low n)).terms ++
    ((X n).expectAffine (high n)).terms.map fun p ↦
      (EF.mul (EF.const (-1)) p.1, p.2)

noncomputable def LUV.crossPrecisionAffine_polySequence
    (X : ℕ → LUV) (low high : ℕ → ℕ)
    (hX : LUV.PolyThresholdCodeSeq X)
    (hlow : ∃ c, PolyFueled c low) (hhigh : ∃ c, PolyFueled c high) :
    AffineCombination.PolySequence (LUV.crossPrecisionAffine X low high) := by
  let cX := Classical.choose hX
  have hX := Classical.choose_spec hX
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
  have hInvLow : PolySegStream (fun z ↦
      (EF.const (1 / (low z.unpair.1 : ℚ))).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const_comp
      ⟨cinv.comp (clow.comp Nat.Partrec.Code.left),
        hinv.comp (hlow.comp PolyFueled.left)⟩)
  have hInvHighNeg : PolySegStream (fun z ↦
      (EF.mul (EF.const (-1))
        (EF.const (1 / (high z.unpair.1 : ℚ)))).serialize) := by
    have hneg : PolySegStream (fun _ : ℕ ↦ (EF.const (-1)).serialize) :=
      PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))
    have hinvHigh : PolySegStream (fun z ↦
        (EF.const (1 / (high z.unpair.1 : ℚ))).serialize) :=
      PolySegStream.ofTokenStream (PolyTokenStream.serialize_const_comp
        ⟨cinv.comp (chigh.comp Nat.Partrec.Code.left),
          hinv.comp (hhigh.comp PolyFueled.left)⟩)
    exact PolySegStream.serialize_mul hneg hinvHigh
  have hcoeff : PolySegStream (fun z ↦
      (if z.unpair.2 < low z.unpair.1 then
        EF.const (1 / (low z.unpair.1 : ℚ))
      else EF.mul (EF.const (-1))
        (EF.const (1 / (high z.unpair.1 : ℚ)))).serialize) := by
    refine PolySegStream.of_eq
      (PolySegStream.ifZero hInvLow hInvHighNeg htest') ?_
    intro z
    by_cases hlt : z.unpair.2 < low z.unpair.1
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]
  have hsentence : ∃ c, PolyFueled c (fun z ↦ Encodable.encode
      (if z.unpair.2 < low z.unpair.1 then
        (X z.unpair.1).gt ((z.unpair.2 : ℚ) / (low z.unpair.1 : ℚ))
      else (X z.unpair.1).gt
        (((z.unpair.2 - low z.unpair.1 : ℕ) : ℚ) /
          (high z.unpair.1 : ℚ)))) := by
    let hsel := ifzSel_polyFueled.comp
      (((hX.comp hqueryLow).pair (hX.comp hqueryHigh)).pair htest)
    exact ⟨_, hsel.of_eq (fun z ↦ by
      simp only [Nat.unpair_pair, ifzSelFn]
      by_cases hlt : z.unpair.2 < low z.unpair.1
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)])⟩
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
    const_poly := PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
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

/-! ### Image-gated cross-precision correction -/

/-- Along the image of a strict deferral, the low mesh selected by the bounded inverse
and the day-indexed high mesh have the same completed-world value.  The image gate makes
the family identically zero elsewhere, so affine provability induction can learn the
cross-precision correction without ever emitting `f n` threshold terms on day `n`. -/
noncomputable def completedImageCrossPrecisionQuote
    {P : History} {DP : DeductiveProcess}
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    (X : ℕ → LUV) (hX : LUV.PolyThresholdCodeSeq X)
    (hvalued : ∀ k (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X k) x)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    CompletedAffineQuoteApprox P DP (fun m ↦
      (deferralImageFlag f a degree m : ℝ) *
        ((X (deferralPreimage f a degree m)).expectApprox (P m)
            (deferralPreimage f a degree m) -
          (X (deferralPreimage f a degree m)).expectApprox (P m) m)) := by
  let index := deferralPreimage f a degree
  let flag := deferralImageFeature f a degree
  let X' : ℕ → LUV := fun m ↦ X (index m)
  let base : ℕ → AffineCombination :=
    LUV.crossPrecisionAffine X' index id
  let gated : ℕ → AffineCombination := fun m ↦ (base m).scale (flag m)
  let family : ℕ → AffineCombination := fun m ↦
    (gated m).scale (EF.const (1 / 2))
  let hindex := deferralPreimage_polyFueled f a degree
  let hX' := hX.reindex hindex
  let hbase := LUV.crossPrecisionAffine_polySequence X' index id hX'
    hindex ⟨Nat.Partrec.Code.id, PolyFueled.id⟩
  let hflag := deferralImageFeature_generated f a degree
  let hgated := hbase.scaleFeature flag hflag
  let hfamily := hgated.scaleRat (1 / 2)
  exact {
    family := family
    poly := hfamily
    scale := 1 / 2
    scale_pos := by norm_num
    current_price := by
      intro m
      simp only [family, gated, base, flag, X', index,
        AffineCombination.scale_price, LUV.crossPrecisionAffine_price,
        deferralImageFeature_denote, EF.denote_const, id_eq]
    bounded := by
      refine ⟨1, zero_le_one, fun m day ↦ ?_⟩
      simp only [family, gated, base, flag, X', index,
        AffineCombination.scale_price, LUV.crossPrecisionAffine_price,
        deferralImageFeature_denote, id_eq]
      rcases deferralImageFlag_zero_or_one f a degree m with hm | hm
      · simp [hm]
      · rw [hm]
        norm_num
        have hlo0 := (X (deferralPreimage f a degree m)).expectApprox_nonneg
          (P day) (deferralPreimage f a degree m) (fun s ↦ (hP day s).1)
        have hlo1 := (X (deferralPreimage f a degree m)).expectApprox_le_one
          (P day) (deferralPreimage f a degree m) (fun s ↦ (hP day s).2)
        have hhi0 := (X (deferralPreimage f a degree m)).expectApprox_nonneg
          (P day) m (fun s ↦ (hP day s).1)
        have hhi1 := (X (deferralPreimage f a degree m)).expectApprox_le_one
          (P day) m (fun s ↦ (hP day s).2)
        have habs :
            |(X (deferralPreimage f a degree m)).expectApprox (P day)
                (deferralPreimage f a degree m) -
              (X (deferralPreimage f a degree m)).expectApprox (P day) m| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        nlinarith
    magnitude_le_one := by
      intro m
      simp only [family, gated, AffineCombination.scale_magnitude,
        EF.denote_const, flag, deferralImageFeature_denote]
      have hbaseMag := LUV.crossPrecisionAffine_magnitude_le_two
        X' index id P m
      rcases deferralImageFlag_zero_or_one f a degree m with hm | hm
      · simp [hm]
      · rw [hm]
        norm_num
        linarith
    theory_coherent := by
      intro ε hε
      obtain ⟨N, hNpos, hNsmall⟩ : ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) ≤ ε / 4 := by
        obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε)
        have hNR : (0 : ℝ) < N := (div_pos (by norm_num) hε).trans hN
        refine ⟨N, by exact_mod_cast hNR, ?_⟩
        have hεN : 4 < ε * (N : ℝ) := by
          simpa only [mul_comm] using (div_lt_iff₀ hε).mp hN
        have hsmall : 1 / (N : ℝ) < ε / 4 := by
          apply (div_lt_div_iff₀ hNR (by norm_num : (0 : ℝ) < 4)).2
          simpa using hεN
        exact hsmall.le
      refine eventually_atTop.2 ⟨f N, fun m hm v hv ↦ ?_⟩
      rcases deferralImageFlag_zero_or_one f a degree m with hflag0 | hflag1
      · simpa [family, gated, flag, hflag0, AffineCombination.scale_value] using hε.le
      · have hspecm := deferralPreimage_spec f hstrict hspec hflag1
        have hindexN : N ≤ deferralPreimage f a degree m := by
          by_contra hnot
          have hlt := hstrict (Nat.lt_of_not_ge hnot)
          rw [hspecm.2] at hlt
          omega
        have hindexPos : 0 < deferralPreimage f a degree m :=
          hNpos.trans_le hindexN
        have hmPos : 0 < m := by omega
        obtain ⟨x, hx⟩ := hvalued (deferralPreimage f a degree m) v hv
        have hlo := hx.expectApprox_near hindexPos
        have hhi := hx.expectApprox_near hmPos
        have hmesh :
            |(X (deferralPreimage f a degree m)).expectApprox v.payout
                (deferralPreimage f a degree m) -
              (X (deferralPreimage f a degree m)).expectApprox v.payout m| ≤
              1 / (deferralPreimage f a degree m : ℝ) + 1 / (m : ℝ) := by
          calc
            |_ - _| = |(_ - x) - (_ - x)| := by ring_nf
            _ ≤ |_ - x| + |_ - x| := abs_sub _ _
            _ ≤ 1 / (deferralPreimage f a degree m : ℝ) + 1 / (m : ℝ) :=
              add_le_add hlo hhi
        have hlowSmall : 1 / (deferralPreimage f a degree m : ℝ) ≤ ε / 4 := by
          exact (one_div_le_one_div_of_le (by exact_mod_cast hNpos) (by exact_mod_cast hindexN)).trans hNsmall
        have hmN : N ≤ m := le_trans hindexN hspecm.1.le
        have hhighSmall : 1 / (m : ℝ) ≤ ε / 4 := by
          exact (one_div_le_one_div_of_le (by exact_mod_cast hNpos) (by exact_mod_cast hmN)).trans hNsmall
        simp only [family, gated, base, flag, X', index,
          AffineCombination.scale_value, LUV.crossPrecisionAffine_value,
          deferralImageFeature_denote, hflag1, Nat.cast_one, one_mul,
          EF.denote_const]
        push_cast
        rw [abs_mul]
        norm_num
        nlinarith
  }

/-- An image-gated numeric quotation mesh.  Only scheduled deferral days need carry
semantic content; off the image the generated feature erases the entire affine object. -/
noncomputable def completedImageNumericQuote
    {P : History} {DP : DeductiveProcess}
    (f : DeferralFunction) {a degree : ℕ}
    (H : ℕ → EF) (hH : PGenerableWeighting H)
    (Y : ℕ → LUV) (hY : LUV.PolyThresholdCodeSeq Y)
    (hreflected : ∀ m, deferralImageFlag f a degree m = 1 →
      ∀ v : PCWorld, v.ConsistentWithTheory DP →
        v.ValuesAt (Y m) ((H m).denote P))
    (hHmem : ∀ m, 0 ≤ (H m).denote P ∧ (H m).denote P ≤ 1)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    CompletedAffineQuoteApprox P DP (fun m ↦
      (deferralImageFlag f a degree m : ℝ) *
        ((H m).denote P - (Y m).expect P m)) := by
  let flag := deferralImageFeature f a degree
  let base := numericQuoteAffine H Y
  let family : ℕ → AffineCombination := fun m ↦ (base m).scale (flag m)
  let hbase := numericQuoteAffine_polySequence H Y hH hY
  let hflag := deferralImageFeature_generated f a degree
  let hfamily := hbase.scaleFeature flag hflag
  exact {
    family := family
    poly := hfamily
    scale := 1
    scale_pos := by norm_num
    current_price := by
      intro m
      simp only [family, base, flag, AffineCombination.scale_price,
        numericQuoteAffine_price, deferralImageFeature_denote]
      norm_num
    bounded := by
      refine ⟨1, zero_le_one, fun m day ↦ ?_⟩
      simp only [family, base, flag, AffineCombination.scale_price,
        deferralImageFeature_denote]
      rcases deferralImageFlag_zero_or_one f a degree m with hm | hm
      · simp [hm]
      · rw [hm]
        norm_num
        rw [AffineCombination.price, numericQuoteAffine_value]
        have hE0 := (Y m).expectApprox_nonneg (P day) m
          (fun s ↦ (hP day s).1)
        have hE1 := (Y m).expectApprox_le_one (P day) m
          (fun s ↦ (hP day s).2)
        rw [abs_le]
        constructor <;> linarith [(hHmem m).1, (hHmem m).2]
    magnitude_le_one := by
      intro m
      simp only [family, base, flag, AffineCombination.scale_magnitude,
        deferralImageFeature_denote]
      rw [numericQuoteAffine_magnitude]
      have hmag := (Y m).expectAffine_magnitude_le_one P m
      rcases deferralImageFlag_zero_or_one f a degree m with hm | hm
      · simp [hm]
      · rw [hm]
        norm_num
        exact hmag
    theory_coherent := by
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine eventually_atTop.2 ⟨max 1 N, fun m hm v hv ↦ ?_⟩
      rcases deferralImageFlag_zero_or_one f a degree m with hflag0 | hflag1
      · simpa [family, base, flag, hflag0, AffineCombination.scale_value] using hε.le
      · have hmPos : 0 < m := by omega
        have hmR : (0 : ℝ) < m := by exact_mod_cast hmPos
        have hsmall : 1 / (m : ℝ) ≤ ε := by
          have hNm : (1 : ℝ) / ε < m :=
            hN.trans_le (by exact_mod_cast (le_trans (le_max_right 1 N) hm))
          rw [div_lt_iff₀ hε] at hNm
          rw [div_le_iff₀ hmR]
          nlinarith
        simp only [family, base, flag, AffineCombination.scale_value,
          deferralImageFeature_denote, hflag1, Nat.cast_one, one_mul,
          numericQuoteAffine_value]
        rw [abs_sub_comm]
        exact (hreflected m hflag1 v hv).expectApprox_near hmPos |>.trans hsmall
  }

/-! ### Fixed expectation-difference portfolios -/

/-- The literal threshold portfolio for `E(X) - E(Y)` at the day-indexed mesh. -/
def LUV.expectDifferenceAffine (X Y : ℕ → LUV) (n : ℕ) : AffineCombination :=
  (LUV.expectAffineSeq X n).add (LUV.expectAffineSeq Y n).neg

noncomputable def LUV.expectDifferenceAffine_polySequence
    (X Y : ℕ → LUV) (hX : LUV.PolyThresholdCodeSeq X)
    (hY : LUV.PolyThresholdCodeSeq Y) :
    AffineCombination.PolySequence (LUV.expectDifferenceAffine X Y) :=
  (LUV.expectAffineSeq_polySequence X hX).add
    (LUV.expectAffineSeq_polySequence Y hY).neg

lemma LUV.expectDifferenceAffine_priceAt
    (X Y : ℕ → LUV) (P : History) (n m : ℕ) :
    (LUV.expectDifferenceAffine X Y n).price P m =
      (X n).expectApprox (P m) n - (Y n).expectApprox (P m) n := by
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
  coefficient_poly := PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
  sentence_poly := ⟨Nat.Partrec.Code.const (Encodable.encode (⊥ : Sentence)),
    PolyFueled.const _⟩
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

/-- Image-gated high-precision certificate for the conditional-expectation identity.
The first summand learns `Z = wX` world by world; the second numerically quotes the
market expectation `w E(X)`. -/
noncomputable def completedImageConditionalQuote
    {P : History} {DP : DeductiveProcess}
    (f : DeferralFunction) {a degree : ℕ}
    (X Z Z' : ℕ → LUV)
    (hX : LUV.PolyThresholdCodeSeq X)
    (hZ : LUV.PolyThresholdCodeSeq Z)
    (hZ' : LUV.PolyThresholdCodeSeq Z')
    (w : ℕ → ℚ)
    (W : ℕ → EF) (hW : PGenerableWeighting W)
    (hWdenote : ∀ m, (W m).denote P = (w m : ℝ))
    (hw : ∀ m, 0 ≤ w m ∧ w m ≤ 1)
    (hsemantic : ∀ m, deferralImageFlag f a degree m = 1 →
      ∀ v : PCWorld, v.ConsistentWithTheory DP →
        ∃ x, v.ValuesAt (X m) x ∧ v.ValuesAt (Z m) (x * w m) ∧
          v.ValuesAt (Z' m) ((X m).expect P m * w m))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    CompletedAffineQuoteApprox P DP (fun m ↦
      (deferralImageFlag f a degree m : ℝ) *
        ((Z m).expect P m - (Z' m).expect P m)) := by
  let EX := currentExpectationFeature X
  let hEX := currentExpectationFeature_generated X hX
  let target : ℕ → EF := fun m ↦ EF.mul (W m) (EX m)
  let htarget := hW.mul hEX
  let Wneg : ℕ → EF := fun m ↦ EF.mul (EF.const (-1)) (W m)
  have hWneg : PGenerableWeighting Wneg := {
    polySeg := PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) hW.polySeg
    rank_le := by intro m; simp [Wneg, EF.rank, hW.rank_le m]
    closed := by
      intro m ρ V
      simp only [Wneg, EF.denoteWith, EF.denote_mul, EF.denote_const,
        Pi.mul_apply]
      rw [hW.closed m ρ V]
  }

  let AX := LUV.expectAffineSeq X
  let AZ := LUV.expectAffineSeq Z
  let relation : ℕ → AffineCombination := fun m ↦
    (AZ m).add ((AX m).scale (Wneg m))
  let numeric := numericQuoteAffine target Z'
  let raw : ℕ → AffineCombination := fun m ↦ (relation m).add (numeric m)
  let flag := deferralImageFeature f a degree
  let gated : ℕ → AffineCombination := fun m ↦ (raw m).scale (flag m)
  let family : ℕ → AffineCombination := fun m ↦
    (gated m).scale (EF.const (1 / 4))
  let hAX := LUV.expectAffineSeq_polySequence X hX
  let hAZ := LUV.expectAffineSeq_polySequence Z hZ
  let hrelation := hAZ.add (hAX.scaleFeature Wneg hWneg)
  let hnumeric := numericQuoteAffine_polySequence target Z' htarget hZ'
  let hraw := hrelation.add hnumeric
  let hflag := deferralImageFeature_generated f a degree
  let hgated := hraw.scaleFeature flag hflag
  let hfamily := hgated.scaleRat (1 / 4)
  exact {
    family := family
    poly := hfamily
    scale := 1 / 4
    scale_pos := by norm_num
    current_price := by
      intro m
      simp only [family, gated, raw, relation, numeric, AX, AZ, flag,
        AffineCombination.scale_price, AffineCombination.add_price,
        LUV.expectAffineSeq_price, numericQuoteAffine_price,
        deferralImageFeature_denote, EF.denote_const, Wneg, EX, target,
        EF.denote_mul, Pi.mul_apply, hWdenote,
        currentExpectationFeature_denote]
      push_cast
      ring
    bounded := by
      refine ⟨1, zero_le_one, fun m day ↦ ?_⟩
      simp only [family, gated, raw, relation, numeric, AX, AZ, flag,
        AffineCombination.scale_price, AffineCombination.add_price,
        LUV.expectAffineSeq, LUV.expectAffine_priceAt,
        numericQuoteAffine_priceAt,
        deferralImageFeature_denote, EF.denote_const, Wneg, EX, target,
        EF.denote_mul, Pi.mul_apply, hWdenote,
        currentExpectationFeature_denote]
      rcases deferralImageFlag_zero_or_one f a degree m with hm | hm
      · simp [hm]
      · rw [hm]
        norm_num
        have hZ0 := (Z m).expectApprox_nonneg (P day) m (fun s ↦ (hP day s).1)
        have hZ1 := (Z m).expectApprox_le_one (P day) m (fun s ↦ (hP day s).2)
        have hZ'0 := (Z' m).expectApprox_nonneg (P day) m (fun s ↦ (hP day s).1)
        have hZ'1 := (Z' m).expectApprox_le_one (P day) m (fun s ↦ (hP day s).2)
        have hX0 := (X m).expectApprox_nonneg (P day) m (fun s ↦ (hP day s).1)
        have hX1 := (X m).expectApprox_le_one (P day) m (fun s ↦ (hP day s).2)
        have hEX0 := (X m).expect_mem_Icc P m (hP m) |>.1
        have hEX1 := (X m).expect_mem_Icc P m (hP m) |>.2
        have hw0 : (0 : ℝ) ≤ w m := by exact_mod_cast (hw m).1
        have hw1 : (w m : ℝ) ≤ 1 := by exact_mod_cast (hw m).2
        have habs :
            |(Z m).expectApprox (P day) m - (w m : ℝ) *
                (X m).expectApprox (P day) m +
              ((w m : ℝ) * (X m).expect P m -
                (Z' m).expectApprox (P day) m)| ≤ 4 := by
          rw [abs_le]
          constructor <;> nlinarith
        have habs' :
            |(Z m).expectApprox (P day) m +
                (-((w m : ℝ) * (X m).expectApprox (P day) m)) +
              ((w m : ℝ) * (X m).expect P m -
                (Z' m).expectApprox (P day) m)| ≤ 4 := by
          simpa only [sub_eq_add_neg] using habs
        nlinarith
    magnitude_le_one := by
      intro m
      simp only [family, gated, raw, relation, numeric, AX, AZ, flag,
        AffineCombination.scale_magnitude, AffineCombination.add_magnitude,
        deferralImageFeature_denote, EF.denote_const,
        numericQuoteAffine_magnitude, Wneg, EF.denote_mul, Pi.mul_apply,
        hWdenote, Rat.cast_neg, Rat.cast_one, neg_mul, one_mul, abs_neg]
      have hXm := LUV.expectAffineSeq_magnitude_le_one X P m
      have hZm := LUV.expectAffineSeq_magnitude_le_one Z P m
      have hZ'm := LUV.expectAffineSeq_magnitude_le_one Z' P m
      have hwR : |(w m : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (by exact_mod_cast (hw m).1)]
        exact_mod_cast (hw m).2
      rcases deferralImageFlag_zero_or_one f a degree m with hm | hm
      · simp [hm]
      · rw [hm]
        norm_num
        have hXnonneg := (LUV.expectAffineSeq X m).magnitude_nonneg P
        have hwmag : |(w m : ℝ)| *
            (LUV.expectAffineSeq X m).magnitude P ≤ 1 := by
          calc
            |_| * _ ≤ 1 * 1 := mul_le_mul hwR hXm hXnonneg (by norm_num)
            _ = 1 := by norm_num
        have hZ'm' : ((Z' m).expectAffine m).magnitude P ≤ 1 := by
          simpa only [LUV.expectAffineSeq] using hZ'm
        linarith
    theory_coherent := by
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine eventually_atTop.2 ⟨max 1 N, fun m hm v hv ↦ ?_⟩
      rcases deferralImageFlag_zero_or_one f a degree m with hflag0 | hflag1
      · simpa [family, gated, flag, hflag0, AffineCombination.scale_value] using hε.le
      · have hmPos : 0 < m := by omega
        have hmR : (0 : ℝ) < m := by exact_mod_cast hmPos
        have hsmall : 1 / (m : ℝ) ≤ ε := by
          have hNm : (1 : ℝ) / ε < m :=
            hN.trans_le (by exact_mod_cast (le_trans (le_max_right 1 N) hm))
          rw [div_lt_iff₀ hε] at hNm
          rw [div_le_iff₀ hmR]
          nlinarith
        obtain ⟨x, hx, hz, hz'⟩ := hsemantic m hflag1 v hv
        have hnearX := hx.expectApprox_near hmPos
        have hnearZ := hz.expectApprox_near hmPos
        have hnearZ' := hz'.expectApprox_near hmPos
        have hw0 : (0 : ℝ) ≤ w m := by exact_mod_cast (hw m).1
        have hw1 : (w m : ℝ) ≤ 1 := by exact_mod_cast (hw m).2
        have hwabs : |(w m : ℝ)| ≤ 1 := by simpa [abs_of_nonneg hw0] using hw1
        have hmul : |(w m : ℝ)| *
            |(X m).expectApprox v.payout m - x| ≤ 1 / (m : ℝ) := by
          calc
            |_| * |_| ≤ 1 * (1 / (m : ℝ)) :=
              mul_le_mul hwabs hnearX (abs_nonneg _) (by positivity)
            _ = 1 / (m : ℝ) := one_mul _
        simp only [family, gated, raw, relation, numeric, AX, AZ, flag,
          AffineCombination.scale_value, AffineCombination.add_value,
          LUV.expectAffineSeq_value, numericQuoteAffine_value,
          deferralImageFeature_denote, hflag1, Nat.cast_one, one_mul,
          EF.denote_const, Wneg, EX, target, EF.denote_mul, Pi.mul_apply,
          hWdenote, currentExpectationFeature_denote]
        push_cast
        let eZ := (Z m).expectApprox v.payout m - x * (w m : ℝ)
        let eX := (X m).expectApprox v.payout m - x
        let eZ' := (Z' m).expectApprox v.payout m -
          (X m).expect P m * (w m : ℝ)
        have hbound :
            |eZ - (w m : ℝ) * eX - eZ'| ≤ 3 / (m : ℝ) := by
          calc
            |eZ - (w m : ℝ) * eX - eZ'|
                ≤ (|eZ| + |(w m : ℝ) * eX|) + |eZ'| := by
              exact (abs_sub _ _).trans
                (add_le_add (abs_sub eZ ((w m : ℝ) * eX)) (le_refl _))
            _ = (|eZ| + |(w m : ℝ)| * |eX|) + |eZ'| := by rw [abs_mul]
            _ ≤ (1 / (m : ℝ) + 1 / (m : ℝ)) + 1 / (m : ℝ) := by
              exact add_le_add (add_le_add hnearZ hmul) hnearZ'
            _ = 3 / (m : ℝ) := by ring
        have hform : (1 / 4 : ℝ) *
              ((Z m).expectApprox v.payout m + (-1) * (w m : ℝ) *
                  (X m).expectApprox v.payout m +
                ((w m : ℝ) * (X m).expect P m -
                  (Z' m).expectApprox v.payout m)) =
            (1 / 4 : ℝ) * (eZ - (w m : ℝ) * eX - eZ') := by
          dsimp only [eZ, eX, eZ']
          ring
        rw [hform]
        rw [abs_mul]
        norm_num
        calc
          1 / 4 * |eZ - (w m : ℝ) * eX - eZ'|
              ≤ 1 / 4 * (3 / (m : ℝ)) :=
            mul_le_mul_of_nonneg_left hbound (by norm_num)
          _ ≤ 1 / (m : ℝ) := by
            have hinv : 0 ≤ 1 / (m : ℝ) := (one_div_nonneg.mpr hmR.le)
            calc
              1 / 4 * (3 / (m : ℝ)) = (3 / 4) * (1 / (m : ℝ)) := by ring
              _ ≤ 1 * (1 / (m : ℝ)) :=
                mul_le_mul_of_nonneg_right (by norm_num) hinv
              _ = 1 / (m : ℝ) := one_mul _
          _ ≤ ε := hsmall
  }

/-! ### Image-gated self-trust correction -/

/-- The high-precision affine identity behind self-trust.  Its completed-world value is
only the two mesh errors for `A` and `B`; the literal gate/sentence correction cancels
the represented product exactly. -/
noncomputable def completedImageSelfTrustQuote
    {P : History} {DP : DeductiveProcess}
    (f : DeferralFunction) {a degree : ℕ}
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ)
    (p : ℕ → ℚ) (pF : ℕ → EF) (hpF : PGenerableWeighting pF)
    (hpDenote : ∀ m, (pF m).denote P = (p m : ℝ))
    (hp : ∀ m, 0 ≤ p m ∧ p m ≤ 1)
    (G : ℕ → EF) (hG : PGenerableWeighting G)
    (hGmem : ∀ m, 0 ≤ (G m).denote P ∧ (G m).denote P ≤ 1)
    (A B : ℕ → LUV) (hA : LUV.PolyThresholdCodeSeq A)
    (hB : LUV.PolyThresholdCodeSeq B)
    (hsemantic : ∀ m, deferralImageFlag f a degree m = 1 →
      ∀ v : PCWorld, v.ConsistentWithTheory DP →
        v.ValuesAt (B m) ((G m).denote P) ∧
          v.ValuesAt (A m) (v.payout (φ m) * (G m).denote P))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1) :
    CompletedAffineQuoteApprox P DP (fun m ↦
      (deferralImageFlag f a degree m : ℝ) *
        ((A m).expect P m - (p m : ℝ) * (B m).expect P m -
          (G m).denote P * (P m (φ m) - (p m : ℝ)))) := by
  let pNeg : ℕ → EF := fun m ↦ EF.mul (EF.const (-1)) (pF m)
  let GNeg : ℕ → EF := fun m ↦ EF.mul (EF.const (-1)) (G m)
  let pG : ℕ → EF := fun m ↦ EF.mul (pF m) (G m)
  have hpNeg : PGenerableWeighting pNeg := {
    polySeg := PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) hpF.polySeg
    rank_le := by intro m; simp [pNeg, EF.rank, hpF.rank_le m]
    closed := by intro m ρ V; simp [pNeg, EF.denoteWith, hpF.closed m ρ V]
  }
  have hGNeg : PGenerableWeighting GNeg := {
    polySeg := PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) hG.polySeg
    rank_le := by intro m; simp [GNeg, EF.rank, hG.rank_le m]
    closed := by intro m ρ V; simp [GNeg, EF.denoteWith, hG.closed m ρ V]
  }
  let hpG := hpF.mul hG
  let AA := LUV.expectAffineSeq A
  let AB := LUV.expectAffineSeq B
  let S := AffineCombination.sentenceAffine φ
  let C := featureConstantAffine pG
  let raw : ℕ → AffineCombination := fun m ↦
    (((AA m).add ((AB m).scale (pNeg m))).add
      ((S m).scale (GNeg m))).add (C m)
  let flag := deferralImageFeature f a degree
  let family : ℕ → AffineCombination := fun m ↦
    ((raw m).scale (flag m)).scale (EF.const (1 / 4))
  let hraw := (((LUV.expectAffineSeq_polySequence A hA).add
      ((LUV.expectAffineSeq_polySequence B hB).scaleFeature pNeg hpNeg)).add
      ((AffineCombination.sentenceAffine_polySequence φ hφ).scaleFeature GNeg hGNeg)).add
      (featureConstantAffine_polySequence pG hpG)
  let hfamily := (hraw.scaleFeature flag
    (deferralImageFeature_generated f a degree)).scaleRat (1 / 4)
  exact {
    family := family
    poly := hfamily
    scale := 1 / 4
    scale_pos := by norm_num
    current_price := by
      intro m
      simp only [family, raw, AA, AB, S, C, flag,
        AffineCombination.scale_price, AffineCombination.add_price,
        LUV.expectAffineSeq_price, AffineCombination.sentenceAffine_price,
        featureConstantAffine_price, deferralImageFeature_denote,
        EF.denote_const, pNeg, GNeg, pG, EF.denote_mul, Pi.mul_apply,
        hpDenote]
      push_cast
      ring_nf
    bounded := by
      refine ⟨1, zero_le_one, fun m day ↦ ?_⟩
      simp only [family, raw, AA, AB, S, C, flag,
        AffineCombination.scale_price, AffineCombination.add_price,
        LUV.expectAffineSeq, LUV.expectAffine_priceAt,
        AffineCombination.sentenceAffine_price, featureConstantAffine_price,
        deferralImageFeature_denote, EF.denote_const, pNeg, GNeg, pG,
        EF.denote_mul, Pi.mul_apply, hpDenote]
      rcases deferralImageFlag_zero_or_one f a degree m with hm | hm
      · simp [hm]
      · rw [hm]
        norm_num
        have hA0 := (A m).expectApprox_nonneg (P day) m (fun s ↦ (hP day s).1)
        have hA1 := (A m).expectApprox_le_one (P day) m (fun s ↦ (hP day s).2)
        have hB0 := (B m).expectApprox_nonneg (P day) m (fun s ↦ (hP day s).1)
        have hB1 := (B m).expectApprox_le_one (P day) m (fun s ↦ (hP day s).2)
        have hp0 : (0 : ℝ) ≤ p m := by exact_mod_cast (hp m).1
        have hp1 : (p m : ℝ) ≤ 1 := by exact_mod_cast (hp m).2
        have habs :
            |(A m).expectApprox (P day) m - (p m : ℝ) *
                (B m).expectApprox (P day) m -
              (G m).denote P * P day (φ m) +
              (p m : ℝ) * (G m).denote P| ≤ 4 := by
          rw [abs_le]
          constructor <;> nlinarith [(hGmem m).1, (hGmem m).2,
            (hP day (φ m)).1, (hP day (φ m)).2]
        have habs' :
            |(A m).expectApprox (P day) m +
                (-(p m : ℝ) * (B m).expectApprox (P day) m) +
              (-(G m).denote P * P day (φ m)) +
              (p m : ℝ) * (G m).denote P| ≤ 4 := by
          convert habs using 1
          all_goals ring_nf
        have hscaled := mul_le_mul_of_nonneg_left habs'
          (show (0 : ℝ) ≤ 1 / 4 by norm_num)
        norm_num at hscaled ⊢
        exact hscaled
    magnitude_le_one := by
      intro m
      simp only [family, raw, AA, AB, S, C, flag,
        AffineCombination.scale_magnitude, AffineCombination.add_magnitude,
        LUV.expectAffineSeq, AffineCombination.sentenceAffine_magnitude,
        featureConstantAffine_magnitude, deferralImageFeature_denote,
        EF.denote_const, pNeg, GNeg, EF.denote_mul, Pi.mul_apply,
        hpDenote, Rat.cast_neg, Rat.cast_one, neg_mul, one_mul, abs_neg,
        add_zero]
      have hAm := (A m).expectAffine_magnitude_le_one P m
      have hBm := (B m).expectAffine_magnitude_le_one P m
      have hpR : |(p m : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (by exact_mod_cast (hp m).1)]
        exact_mod_cast (hp m).2
      rcases deferralImageFlag_zero_or_one f a degree m with hm | hm
      · simp [hm]
      · rw [hm]
        norm_num
        have hpB : |(p m : ℝ)| * ((B m).expectAffine m).magnitude P ≤ 1 := by
          exact (mul_le_mul hpR hBm (((B m).expectAffine m).magnitude_nonneg P)
            (by norm_num)).trans_eq (one_mul 1)
        have hGabs : |(G m).denote P| ≤ 1 := by
          simpa [abs_of_nonneg (hGmem m).1] using (hGmem m).2
        linarith
    theory_coherent := by
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine eventually_atTop.2 ⟨max 1 N, fun m hm v hv ↦ ?_⟩
      rcases deferralImageFlag_zero_or_one f a degree m with hflag0 | hflag1
      · simpa [family, flag, hflag0, AffineCombination.scale_value] using hε.le
      · have hmPos : 0 < m := by omega
        have hmR : (0 : ℝ) < m := by exact_mod_cast hmPos
        have hsmall : 1 / (m : ℝ) ≤ ε := by
          have hNm : (1 : ℝ) / ε < m :=
            hN.trans_le (by exact_mod_cast (le_trans (le_max_right 1 N) hm))
          rw [div_lt_iff₀ hε] at hNm
          rw [div_le_iff₀ hmR]
          nlinarith
        obtain ⟨hBv, hAv⟩ := hsemantic m hflag1 v hv
        have hnearA := hAv.expectApprox_near hmPos
        have hnearB := hBv.expectApprox_near hmPos
        have hp0 : (0 : ℝ) ≤ p m := by exact_mod_cast (hp m).1
        have hp1 : (p m : ℝ) ≤ 1 := by exact_mod_cast (hp m).2
        simp only [family, raw, AA, AB, S, C, flag,
          AffineCombination.scale_value, AffineCombination.add_value,
          LUV.expectAffineSeq_value, AffineCombination.sentenceAffine_value,
          featureConstantAffine_value, deferralImageFeature_denote, hflag1,
          Nat.cast_one, one_mul, EF.denote_const, pNeg, GNeg, pG,
          EF.denote_mul, Pi.mul_apply, hpDenote]
        push_cast
        have hpabs : |(p m : ℝ)| ≤ 1 := by
          simpa [abs_of_nonneg hp0] using hp1
        have hpnear : |(p m : ℝ)| *
            |(B m).expectApprox v.payout m - (G m).denote P| ≤
              1 / (m : ℝ) := by
          calc
            |_| * |_| ≤ 1 * (1 / (m : ℝ)) :=
              mul_le_mul hpabs hnearB (abs_nonneg _) (by positivity)
            _ = _ := one_mul _
        let eA := (A m).expectApprox v.payout m -
          v.payout (φ m) * (G m).denote P
        let eB := (B m).expectApprox v.payout m - (G m).denote P
        have herr : |eA - (p m : ℝ) * eB| ≤ 2 / (m : ℝ) := by
          calc
            |eA - (p m : ℝ) * eB| ≤ |eA| + |(p m : ℝ) * eB| := abs_sub _ _
            _ = |_| + |(p m : ℝ)| * |_| := by rw [abs_mul]
            _ ≤ 1 / (m : ℝ) + 1 / (m : ℝ) := add_le_add hnearA hpnear
            _ = 2 / (m : ℝ) := by ring
        have hform : (1 / 4 : ℝ) *
            ((A m).expectApprox v.payout m + (-1) * (p m : ℝ) *
                (B m).expectApprox v.payout m +
              (-1) * (G m).denote P * v.payout (φ m) +
              (p m : ℝ) * (G m).denote P) =
            (1 / 4 : ℝ) * (eA - (p m : ℝ) * eB) := by
          dsimp only [eA, eB]
          ring
        rw [hform, abs_mul]
        norm_num
        calc
          1 / 4 * |eA - (p m : ℝ) * eB|
              ≤ 1 / 4 * (2 / (m : ℝ)) :=
            mul_le_mul_of_nonneg_left herr (by norm_num)
          _ ≤ 1 / (m : ℝ) := by
            have hi : 0 ≤ 1 / (m : ℝ) := one_div_nonneg.mpr hmR.le
            calc
              1 / 4 * (2 / (m : ℝ)) = (1 / 2) * (1 / (m : ℝ)) := by ring
              _ ≤ 1 * (1 / (m : ℝ)) :=
                mul_le_mul_of_nonneg_right (by norm_num) hi
              _ = _ := one_mul _
          _ ≤ ε := hsmall
  }

/-! ## Interval quotation package -/

/-- Construct the complete interval-introspection quotation package from the literal
current-price feature, generated rational endpoints, a generated continuous width, and
one arithmetically reflected Boolean interval claim.  Both affine certificates are
concrete one-share portfolios; the outward sum is normalized by `1/2`. -/
noncomputable def introspectionIntervalQuoteOfCode
    {P : History} {DP : DeductiveProcess} {T : ArithmeticTheory}
    (Q : QuotationTheoryPresentation DP T)
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ)
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
    quote_codes := q.sentence_poly
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
  represents_fixedpoint : ∀ (z : ℕ), (ℕ ⊧ₘ (parameterizedFixedpoint body)/[↑z]) ↔ truth z

/-- The genuine parameterized fixed point carried by a diagonal quote satisfies FFL's
uniform diagonal law inside the presented arithmetic theory — a standalone honesty
artifact that a real self-referential arithmetic sentence backs the quoted decision. -/
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
    (ℕ ⊧ₘ (diagonalPriceBody market p)/[↑x, ↑n]) ↔
      diagonalPriceTruth market p n := by
  simpa [diagonalPriceBody, models_iff, Semiformula.eval_substs,
    Matrix.constant_eq_singleton] using
      (codeOfREPred_spec (diagonalPriceTruth_re market p) (x := n))

/-- The FFL parameterized fixed point represents the same predicate as the public selector.
Paper node: `thm:lp` -/
lemma diagonalPriceFixedpoint_spec
    {P : History} (market : MarketComputation P) (p : ℚ) (n : ℕ) :
    (ℕ ⊧ₘ (parameterizedFixedpoint (diagonalPriceBody market p))/[↑n]) ↔
      diagonalPriceTruth market p n := by
  have hall : ℕ ⊧ₘ ∀⁰
      (parameterizedFixedpoint (diagonalPriceBody market p) 🡘
        (diagonalPriceBody market p)/[
          ⌜parameterizedFixedpoint (diagonalPriceBody market p)⌝, #0]) :=
    models_of_provable (T := 𝗜𝚺₁) inferInstance
      (parameterized_diagonal₁ (T := 𝗜𝚺₁) (diagonalPriceBody market p))
  have hdiag : ∀ n : ℕ,
      (ℕ ⊧ₘ (parameterizedFixedpoint (diagonalPriceBody market p))/[↑n]) ↔
        (ℕ ⊧ₘ (diagonalPriceBody market p)/[
          ⌜parameterizedFixedpoint (diagonalPriceBody market p)⌝, ↑n]) := by
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
comparison for its inherited public atom.  This is the semantic edge formerly supplied as
an external premise.
Paper node: `thm:lp` -/
lemma parameterizedDiagonalQuoteCodeOfMarket_public_fixedpoint
    {P : History} (market : MarketComputation P) (T : ArithmeticTheory)
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (p : ℚ) (n : ℕ) :
    (ℕ ⊧ₘ
        (parameterizedFixedpoint
          (parameterizedDiagonalQuoteCodeOfMarket market T p).body)/[↑n]) ↔
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
  have hquote : PolySentenceCodes quote.sentence := quote.sentence_poly
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
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) :
    Tendsto (fun n ↦ (q.family n).price P (f n)) atTop (𝓝 0) := by
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
        simpa only [As] using hinf
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
        simpa only [As] using hsup
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
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) : AffineQuoteEq P f gap where
  toAffineQuotePortfolio := q.toAffineQuotePortfolio
  future_coherent := by
    simpa only [AsympEq, _root_.sub_zero] using
      q.future_price_tendsto_zero hP hworld f

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
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (X Y : ℕ → LUV)
    (hX : LUV.PolyThresholdCodeSeq X) (hY : LUV.PolyThresholdCodeSeq Y)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X n) x)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Y n) ((X n).expect P (f n)))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ExpectedFutureExpectationQuote P DP f X Y := by
  let a := Classical.choose f.fueled
  let degree := Classical.choose (Classical.choose_spec f.fueled)
  have hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k) := by
    simpa [a, degree, PrefixPatchCompile.ecClock] using
      Classical.choose_spec (Classical.choose_spec f.fueled)
  let index := deferralPreimage f a degree
  let flagN := deferralImageFlag f a degree
  let X' : ℕ → LUV := fun m ↦ X (index m)
  let Y' : ℕ → LUV := fun m ↦ Y (index m)
  let hindex := deferralPreimage_polyFueled f a degree
  let hX' := hX.reindex hindex
  let hY' := hY.reindex hindex
  let H := currentExpectationFeature X'
  let hH := currentExpectationFeature_generated X' hX'
  have hHmem : ∀ m, 0 ≤ (H m).denote P ∧ (H m).denote P ≤ 1 := by
    intro m
    rw [show (H m).denote P = (X' m).expect P m by
      exact currentExpectationFeature_denote X' P m]
    exact (X' m).expect_mem_Icc P m (hP m)
  have hreflectedImage : ∀ m, flagN m = 1 →
      ∀ v : PCWorld, v.ConsistentWithTheory DP →
        v.ValuesAt (Y' m) ((H m).denote P) := by
    intro m hm v hv
    have hmSpec := deferralPreimage_spec f hstrict hspec hm
    rw [show (H m).denote P = (X' m).expect P m by
      exact currentExpectationFeature_denote X' P m]
    simpa only [X', Y', index, hmSpec.2] using reflected (index m) v hv
  let high := completedImageNumericQuote f H hH Y' hY'
    hreflectedImage hHmem hP
  let crossX := completedImageCrossPrecisionQuote f hstrict hspec X hX
    source_valued hP
  have quote_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ y, v.ValuesAt (Y n) y := by
    intro n v hv
    exact ⟨(X n).expect P (f n), reflected n v hv⟩
  let crossY := completedImageCrossPrecisionQuote f hstrict hspec Y hY
    quote_valued hP
  let highGap : ℕ → ℝ := fun m ↦ (flagN m : ℝ) *
    ((X (index m)).expect P m - (Y (index m)).expect P m)
  let crossXGap : ℕ → ℝ := fun m ↦ (flagN m : ℝ) *
    ((X (index m)).expectApprox (P m) (index m) -
      (X (index m)).expect P m)
  let crossYGap : ℕ → ℝ := fun m ↦ (flagN m : ℝ) *
    ((Y (index m)).expectApprox (P m) (index m) -
      (Y (index m)).expect P m)
  have hhigh0 : Tendsto highGap atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero, high, highGap, flagN, X', Y', H,
      index, currentExpectationFeature_denote] using
      high.gap_asympEq_zero hworld
  have hcrossX0 : Tendsto crossXGap atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero, crossX, crossXGap, flagN, index,
      LUV.expect] using crossX.gap_asympEq_zero hworld
  have hcrossY0 : Tendsto crossYGap atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero, crossY, crossYGap, flagN, index,
      LUV.expect] using crossY.gap_asympEq_zero hworld
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
        have hX0 := (X n).expectApprox_nonneg (P m) n (fun s ↦ (hP m s).1)
        have hX1 := (X n).expectApprox_le_one (P m) n (fun s ↦ (hP m s).2)
        have hY0 := (Y n).expectApprox_nonneg (P m) n (fun s ↦ (hP m s).1)
        have hY1 := (Y n).expectApprox_le_one (P m) n (fun s ↦ (hP m s).2)
        rw [abs_le]
        constructor <;> norm_num <;> linarith
      magnitude_le_one := by
        intro n
        simp only [family, AffineCombination.scale_magnitude, EF.denote_const]
        norm_num
        linarith [LUV.expectDifferenceAffine_magnitude_le_two X Y P n]
      future_coherent := by
        have hcombined : Tendsto (fun m ↦ (1 / 2 : ℝ) *
            (highGap m + crossXGap m - crossYGap m)) atTop (𝓝 0) := by
          simpa using ((hhigh0.add hcrossX0).sub hcrossY0).const_mul (1 / 2 : ℝ)
        have hdeferred := hcombined.comp f.tendsto_atTop
        have hdeferred' : Tendsto (fun n ↦ (1 / 2 : ℝ) *
            (highGap (f n) + crossXGap (f n) - crossYGap (f n)))
            atTop (𝓝 0) := by
          simpa only [Function.comp_apply] using hdeferred
        show Tendsto (fun n ↦ (family n).price P (f n) - 0) atTop (𝓝 0)
        apply Tendsto.congr' _ hdeferred'
        exact Eventually.of_forall fun n ↦ by
          simp only [family, raw, AffineCombination.scale_price,
            EF.denote_const, LUV.expectDifferenceAffine_priceAt, highGap,
            crossXGap, crossYGap, flagN, index,
            deferralImageFlag_at f hstrict hspec n,
            deferralPreimage_at f hstrict hspec n, Nat.cast_one, one_mul,
            Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, LUV.expect,
            _root_.sub_zero]
          ring
    }
  }

/-- Construct the complete `thm:ceu` future-price quote package. -/
noncomputable def futurePriceQuoteOfRepresentation
    {P : History} {DP : DeductiveProcess}
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (φ : ℕ → Sentence) (Y : ℕ → LUV)
    (hφ : PolySentenceCodes φ) (hY : LUV.PolyThresholdCodeSeq Y)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Y n) (P (f n) (φ n)))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    FuturePriceQuote P DP f φ Y := by
  let a := Classical.choose f.fueled
  let degree := Classical.choose (Classical.choose_spec f.fueled)
  have hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k) := by
    simpa [a, degree, PrefixPatchCompile.ecClock] using
      Classical.choose_spec (Classical.choose_spec f.fueled)
  let index := deferralPreimage f a degree
  let flagN := deferralImageFlag f a degree
  let φ' : ℕ → Sentence := fun m ↦ φ (index m)
  let Y' : ℕ → LUV := fun m ↦ Y (index m)
  let hindex := deferralPreimage_polyFueled f a degree
  have hφ' : PolySentenceCodes φ' := by
    obtain ⟨cφ, hcφ⟩ := hφ
    let cindex := Classical.choose hindex
    have hcindex := Classical.choose_spec hindex
    exact ⟨_, (hcφ.comp hcindex).of_eq (fun m ↦ by simp [φ', index])⟩
  let hY' := hY.reindex hindex
  let H := currentPriceFeature φ'
  let hH := currentPriceFeature_generated φ' hφ'
  have hHmem : ∀ m, 0 ≤ (H m).denote P ∧ (H m).denote P ≤ 1 := by
    intro m
    simpa [H, currentPriceFeature, φ'] using hP m (φ (index m))
  have hreflectedImage : ∀ m, flagN m = 1 →
      ∀ v : PCWorld, v.ConsistentWithTheory DP →
        v.ValuesAt (Y' m) ((H m).denote P) := by
    intro m hm v hv
    have hmSpec := deferralPreimage_spec f hstrict hspec hm
    simpa only [Y', H, currentPriceFeature, φ', index, hmSpec.2] using
      reflected (index m) v hv
  let high := completedImageNumericQuote f H hH Y' hY'
    hreflectedImage hHmem hP
  have quote_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ y, v.ValuesAt (Y n) y := by
    intro n v hv
    exact ⟨P (f n) (φ n), reflected n v hv⟩
  let crossY := completedImageCrossPrecisionQuote f hstrict hspec Y hY
    quote_valued hP
  let highGap : ℕ → ℝ := fun m ↦ (flagN m : ℝ) *
    (P m (φ (index m)) - (Y (index m)).expect P m)
  let crossYGap : ℕ → ℝ := fun m ↦ (flagN m : ℝ) *
    ((Y (index m)).expectApprox (P m) (index m) -
      (Y (index m)).expect P m)
  have hhigh0 : Tendsto highGap atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero, high, highGap, flagN, Y', H,
      φ', index, currentPriceFeature] using high.gap_asympEq_zero hworld
  have hcrossY0 : Tendsto crossYGap atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero, crossY, crossYGap, flagN, index,
      LUV.expect] using crossY.gap_asympEq_zero hworld
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
        have hY0 := (Y n).expectApprox_nonneg (P m) n (fun s ↦ (hP m s).1)
        have hY1 := (Y n).expectApprox_le_one (P m) n (fun s ↦ (hP m s).2)
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
        have hcombined : Tendsto (fun m ↦ (1 / 2 : ℝ) *
            (highGap m - crossYGap m)) atTop (𝓝 0) := by
          simpa using (hhigh0.sub hcrossY0).const_mul (1 / 2 : ℝ)
        have hdeferred := hcombined.comp f.tendsto_atTop
        have hdeferred' : Tendsto (fun n ↦ (1 / 2 : ℝ) *
            (highGap (f n) - crossYGap (f n))) atTop (𝓝 0) := by
          simpa only [Function.comp_apply] using hdeferred
        show Tendsto (fun n ↦ (family n).price P (f n) - 0) atTop (𝓝 0)
        apply Tendsto.congr' _ hdeferred'
        exact Eventually.of_forall fun n ↦ by
          simp only [family, raw, sentenceFamily, quoteFamily,
            AffineCombination.scale_price, EF.denote_const,
            AffineCombination.add_price, AffineCombination.neg_price,
            AffineCombination.sentenceAffine_price, LUV.expectAffineSeq,
            LUV.expectAffine_priceAt, highGap, crossYGap, flagN, index,
            deferralImageFlag_at f hstrict hspec n,
            deferralPreimage_at f hstrict hspec n, Nat.cast_one, one_mul,
            Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, LUV.expect,
            _root_.sub_zero]
          ring
    }
  }

/-- Construct the complete `thm:ccee` conditional-expectation quote package. -/
noncomputable def conditionalExpectationQuoteOfRepresentation
    {P : History} {DP : DeductiveProcess}
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (X Z Z' : ℕ → LUV) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat P w)
    (hX : LUV.PolyThresholdCodeSeq X)
    (hZ : LUV.PolyThresholdCodeSeq Z)
    (hZ' : LUV.PolyThresholdCodeSeq Z')
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X n) x)
    (left_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ x, v.ValuesAt (X n) x → v.ValuesAt (Z n) (x * w (f n)))
    (right_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Z' n) ((X n).expect P (f n) * w (f n)))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConditionalExpectationQuote P DP f X Z Z' w := by
  let a := Classical.choose f.fueled
  let degree := Classical.choose (Classical.choose_spec f.fueled)
  have hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k) := by
    simpa [a, degree, PrefixPatchCompile.ecClock] using
      Classical.choose_spec (Classical.choose_spec f.fueled)
  let index := deferralPreimage f a degree
  let flagN := deferralImageFlag f a degree
  let Xr : ℕ → LUV := fun m ↦ X (index m)
  let Zr : ℕ → LUV := fun m ↦ Z (index m)
  let Zr' : ℕ → LUV := fun m ↦ Z' (index m)
  let hindex := deferralPreimage_polyFueled f a degree
  let hXr := hX.reindex hindex
  let hZr := hZ.reindex hindex
  let hZr' := hZ'.reindex hindex
  let W := Classical.choose weight_generable
  let hWgen := Classical.choose_spec weight_generable
  let hW := hWgen.toWeighting
  have hsemantic : ∀ m, flagN m = 1 →
      ∀ v : PCWorld, v.ConsistentWithTheory DP →
        ∃ x, v.ValuesAt (Xr m) x ∧ v.ValuesAt (Zr m) (x * w m) ∧
          v.ValuesAt (Zr' m) ((Xr m).expect P m * w m) := by
    intro m hm v hv
    have hmSpec := deferralPreimage_spec f hstrict hspec hm
    obtain ⟨x, hx⟩ := source_valued (index m) v hv
    refine ⟨x, hx, ?_, ?_⟩
    · simpa only [Zr, Xr, index, hmSpec.2] using
        left_reflected (index m) v hv x hx
    · simpa only [Zr', Xr, index, hmSpec.2] using
        right_reflected (index m) v hv
  let high := completedImageConditionalQuote f Xr Zr Zr' hXr hZr hZr'
    w W hW hWgen.denote weight_mem hsemantic hP
  have Zvalued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ z, v.ValuesAt (Z n) z := by
    intro n v hv
    obtain ⟨x, hx⟩ := source_valued n v hv
    exact ⟨x * w (f n), left_reflected n v hv x hx⟩
  have Z'valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ z, v.ValuesAt (Z' n) z := by
    intro n v hv
    exact ⟨(X n).expect P (f n) * w (f n), right_reflected n v hv⟩
  let crossZ := completedImageCrossPrecisionQuote f hstrict hspec Z hZ Zvalued hP
  let crossZ' := completedImageCrossPrecisionQuote f hstrict hspec Z' hZ' Z'valued hP
  let highGap : ℕ → ℝ := fun m ↦ (flagN m : ℝ) *
    ((Z (index m)).expect P m - (Z' (index m)).expect P m)
  let crossZGap : ℕ → ℝ := fun m ↦ (flagN m : ℝ) *
    ((Z (index m)).expectApprox (P m) (index m) -
      (Z (index m)).expect P m)
  let crossZ'Gap : ℕ → ℝ := fun m ↦ (flagN m : ℝ) *
    ((Z' (index m)).expectApprox (P m) (index m) -
      (Z' (index m)).expect P m)
  have hhigh0 : Tendsto highGap atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero, high, highGap, flagN, Xr, Zr,
      Zr', index] using high.gap_asympEq_zero hworld
  have hcrossZ0 : Tendsto crossZGap atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero, crossZ, crossZGap, flagN, index,
      LUV.expect] using crossZ.gap_asympEq_zero hworld
  have hcrossZ'0 : Tendsto crossZ'Gap atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero, crossZ', crossZ'Gap, flagN, index,
      LUV.expect] using crossZ'.gap_asympEq_zero hworld
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
        have hZ0 := (Z n).expectApprox_nonneg (P m) n (fun s ↦ (hP m s).1)
        have hZ1 := (Z n).expectApprox_le_one (P m) n (fun s ↦ (hP m s).2)
        have hZ'0 := (Z' n).expectApprox_nonneg (P m) n (fun s ↦ (hP m s).1)
        have hZ'1 := (Z' n).expectApprox_le_one (P m) n (fun s ↦ (hP m s).2)
        rw [abs_le]
        constructor <;> norm_num <;> linarith
      magnitude_le_one := by
        intro n
        simp only [family, AffineCombination.scale_magnitude, EF.denote_const]
        norm_num
        linarith [LUV.expectDifferenceAffine_magnitude_le_two Z Z' P n]
      future_coherent := by
        have hcombined : Tendsto (fun m ↦ (1 / 2 : ℝ) *
            (highGap m + crossZGap m - crossZ'Gap m)) atTop (𝓝 0) := by
          simpa using ((hhigh0.add hcrossZ0).sub hcrossZ'0).const_mul (1 / 2 : ℝ)
        have hdeferred := hcombined.comp f.tendsto_atTop
        have hdeferred' : Tendsto (fun n ↦ (1 / 2 : ℝ) *
            (highGap (f n) + crossZGap (f n) - crossZ'Gap (f n)))
            atTop (𝓝 0) := by
          simpa only [Function.comp_apply] using hdeferred
        show Tendsto (fun n ↦ (family n).price P (f n) - 0) atTop (𝓝 0)
        apply Tendsto.congr' _ hdeferred'
        exact Eventually.of_forall fun n ↦ by
          simp only [family, raw, AffineCombination.scale_price,
            EF.denote_const, LUV.expectDifferenceAffine_priceAt, highGap,
            crossZGap, crossZ'Gap, flagN, index,
            deferralImageFlag_at f hstrict hspec n,
            deferralPreimage_at f hstrict hspec n, Nat.cast_one, one_mul,
            Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, LUV.expect,
            _root_.sub_zero]
          ring
    }
  }

/-! ### Complete deferred self-trust package -/

/-- Construct the complete `thm:st` self-trust package.  Strictness is needed only by
this concrete constructor, where it makes the bounded image inverse unambiguous; the
abstract `SelfTrustQuote` and its consumer remain stated for every deferral function. -/
noncomputable def selfTrustQuoteOfRepresentation
    {P : History} {DP : DeductiveProcess}
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (φ : ℕ → Sentence) (δ p : ℕ → ℚ) (A B : ℕ → LUV)
    (delta_pos : ∀ n, 0 < δ n)
    (probability_mem : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hφ : PolySentenceCodes φ) (hδ : PolyRatCodes δ)
    (hδinv : PolyRatCodes (fun n ↦ 1 / δ n))
    (hp : PolyRatCodes p)
    (hA : LUV.PolyThresholdCodeSeq A)
    (hB : LUV.PolyThresholdCodeSeq B)
    (confidence_reflected : ∀ n (v : PCWorld),
      v.ConsistentWithTheory DP →
        v.ValuesAt (B n) (ctsInd (δ n) (P (f n) (φ n)) (p n)))
    (product_reflected : ∀ n (v : PCWorld),
      v.ConsistentWithTheory DP →
        v.ValuesAt (A n)
          (v.payout (φ n) * ctsInd (δ n) (P (f n) (φ n)) (p n)))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    SelfTrustQuote P DP f φ δ p A B := by
  let a := Classical.choose f.fueled
  let degree := Classical.choose (Classical.choose_spec f.fueled)
  have hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k) := by
    simpa [a, degree, PrefixPatchCompile.ecClock] using
      Classical.choose_spec (Classical.choose_spec f.fueled)
  let index := deferralPreimage f a degree
  let flagN := deferralImageFlag f a degree
  let φr : ℕ → Sentence := fun m ↦ φ (index m)
  let δr : ℕ → ℚ := fun m ↦ δ (index m)
  let pr : ℕ → ℚ := fun m ↦ p (index m)
  let Ar : ℕ → LUV := fun m ↦ A (index m)
  let Br : ℕ → LUV := fun m ↦ B (index m)
  let hindex := deferralPreimage_polyFueled f a degree
  have hφr : PolySentenceCodes φr := by
    obtain ⟨cφ, hcφ⟩ := hφ
    obtain ⟨ci, hi⟩ := hindex
    exact ⟨cφ.comp ci, (hcφ.comp hi).of_eq (fun m ↦ by simp [φr, index])⟩
  let hAr := hA.reindex hindex
  let hBr := hB.reindex hindex
  let hδrInv := hδinv.reindex hindex
  let hpr := hp.reindex hindex
  let pF : ℕ → EF := ratCodeFeature pr
  let hpFgen := ratCodeFeature_generated P pr hpr
  let hpF := hpFgen.toWeighting
  let priceF : ℕ → EF := currentPriceFeature φr
  let hpriceF := currentPriceFeature_generated φr hφr
  let G : ℕ → EF := ctsIndFeature δr priceF pF
  have hδrPos : ∀ m, 0 < δr m := by
    intro m
    exact delta_pos (index m)
  let hG := ctsIndFeature_generated δr priceF pF hδrInv hpriceF hpF
  have hpFDenote : ∀ m, (pF m).denote P = (pr m : ℝ) := by
    exact hpFgen.denote
  have hGDenote : ∀ m, (G m).denote P =
      ctsInd (δr m) (P m (φr m)) (pr m : ℝ) := by
    intro m
    rw [show G m = ctsIndFeature δr priceF pF m by rfl,
      ctsIndFeature_denote δr priceF pF hδrPos P m]
    simp [priceF, currentPriceFeature, hpFDenote]
  have hGmem : ∀ m, 0 ≤ (G m).denote P ∧ (G m).denote P ≤ 1 := by
    intro m
    rw [hGDenote]
    exact ctsInd_mem_Icc _ _ _
  have hsemantic : ∀ m, flagN m = 1 →
      ∀ v : PCWorld, v.ConsistentWithTheory DP →
        v.ValuesAt (Br m) ((G m).denote P) ∧
          v.ValuesAt (Ar m) (v.payout (φr m) * (G m).denote P) := by
    intro m hm v hv
    have hmSpec := deferralPreimage_spec f hstrict hspec hm
    constructor
    · rw [hGDenote]
      simpa only [Br, δr, pr, φr, index, hmSpec.2] using
        confidence_reflected (index m) v hv
    · rw [hGDenote]
      simpa only [Ar, δr, pr, φr, index, hmSpec.2] using
        product_reflected (index m) v hv
  let high := completedImageSelfTrustQuote (a := a) (degree := degree)
    f φr hφr pr pF hpF hpFDenote
      (fun m ↦ probability_mem (index m)) G hG hGmem Ar Br hAr hBr
      hsemantic hP
  have Avalued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (A n) x := by
    intro n v hv
    exact ⟨v.payout (φ n) * ctsInd (δ n) (P (f n) (φ n)) (p n),
      product_reflected n v hv⟩
  have Bvalued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (B n) x := by
    intro n v hv
    exact ⟨ctsInd (δ n) (P (f n) (φ n)) (p n),
      confidence_reflected n v hv⟩
  let crossA := completedImageCrossPrecisionQuote f hstrict hspec A hA Avalued hP
  let crossB := completedImageCrossPrecisionQuote f hstrict hspec B hB Bvalued hP
  let highGap : ℕ → ℝ := fun m ↦ (flagN m : ℝ) *
    ((A (index m)).expect P m - (p (index m) : ℝ) *
        (B (index m)).expect P m -
      (G m).denote P * (P m (φ (index m)) - (p (index m) : ℝ)))
  let crossAGap : ℕ → ℝ := fun m ↦ (flagN m : ℝ) *
    ((A (index m)).expectApprox (P m) (index m) -
      (A (index m)).expect P m)
  let crossBGap : ℕ → ℝ := fun m ↦ (flagN m : ℝ) *
    ((B (index m)).expectApprox (P m) (index m) -
      (B (index m)).expect P m)
  have hhigh0 : Tendsto highGap atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero, high, highGap, flagN, Ar, Br,
      φr, pr, index] using high.gap_asympEq_zero hworld
  have hcrossA0 : Tendsto crossAGap atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero, crossA, crossAGap, flagN, index,
      LUV.expect] using crossA.gap_asympEq_zero hworld
  have hcrossB0 : Tendsto crossBGap atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero, crossB, crossBGap, flagN, index,
      LUV.expect] using crossB.gap_asympEq_zero hworld
  have hpCrossB0 : Tendsto (fun m ↦ (p (index m) : ℝ) * crossBGap m)
      atTop (𝓝 0) := by
    apply bdd_le_mul_tendsto_zero
      (b := (0 : ℝ)) (B := (1 : ℝ))
    · exact Eventually.of_forall fun m ↦ by
        exact_mod_cast (probability_mem (index m)).1
    · exact Eventually.of_forall fun m ↦ by
        exact_mod_cast (probability_mem (index m)).2
    · exact hcrossB0
  let combined : ℕ → ℝ := fun m ↦ (1 / 2 : ℝ) *
    (highGap m + crossAGap m - (p (index m) : ℝ) * crossBGap m)
  have hcombined0 : Tendsto combined atTop (𝓝 0) := by
    simpa [combined] using
      ((hhigh0.add hcrossA0).sub hpCrossB0).const_mul (1 / 2 : ℝ)
  have hdeferred0 : Tendsto (fun n ↦ combined (f n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using hcombined0.comp f.tendsto_atTop
  let pOrig : ℕ → EF := ratCodeFeature p
  let hpOrig : PGenerableWeighting pOrig :=
    (ratCodeFeature_generated P p hp).toWeighting
  let pNeg : ℕ → EF := fun n ↦ EF.mul (EF.const (-1)) (pOrig n)
  have hpNeg : PGenerableWeighting pNeg := {
    polySeg := PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1)))
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
    probability_codes := hp
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
          ratCodeFeature, Pi.mul_apply]
        push_cast
        ring
      bounded := by
        refine ⟨1, zero_le_one, fun n m ↦ ?_⟩
        simp only [family, raw, AA, AB, pNeg, pOrig,
          AffineCombination.scale_price, AffineCombination.add_price,
          LUV.expectAffineSeq, LUV.expectAffine_priceAt, EF.denote_mul,
          EF.denote_const, ratCodeFeature, Pi.mul_apply]
        push_cast
        have hA0 := (A n).expectApprox_nonneg (P m) n (fun s ↦ (hP m s).1)
        have hA1 := (A n).expectApprox_le_one (P m) n (fun s ↦ (hP m s).2)
        have hB0 := (B n).expectApprox_nonneg (P m) n (fun s ↦ (hP m s).1)
        have hB1 := (B n).expectApprox_le_one (P m) n (fun s ↦ (hP m s).2)
        have hp0 : (0 : ℝ) ≤ p n := by exact_mod_cast (probability_mem n).1
        have hp1 : (p n : ℝ) ≤ 1 := by exact_mod_cast (probability_mem n).2
        rw [abs_le]
        constructor <;> nlinarith
      magnitude_le_one := by
        intro n
        simp only [family, raw, AA, AB, pNeg, pOrig,
          AffineCombination.scale_magnitude, AffineCombination.add_magnitude,
          LUV.expectAffineSeq, EF.denote_const, EF.denote_mul,
          ratCodeFeature, Pi.mul_apply, Rat.cast_neg, Rat.cast_one, neg_mul,
          one_mul, abs_neg]
        have hAm := (A n).expectAffine_magnitude_le_one P n
        have hBm := (B n).expectAffine_magnitude_le_one P n
        have hpabs : |(p n : ℝ)| ≤ 1 := by
          rw [abs_of_nonneg (by exact_mod_cast (probability_mem n).1)]
          exact_mod_cast (probability_mem n).2
        have hpB : |(p n : ℝ)| * ((B n).expectAffine n).magnitude P ≤ 1 := by
          exact (mul_le_mul hpabs hBm (((B n).expectAffine n).magnitude_nonneg P)
            (by norm_num)).trans_eq (one_mul 1)
        norm_num
        linarith
      future_coherent := by
        intro ε hε
        have hnear := asympEq_iff_eventuallyWithin.1
          (show AsympEq (fun n ↦ combined (f n)) (fun _ ↦ 0) by
            simpa only [AsympEq, _root_.sub_zero] using hdeferred0)
          ε hε
        filter_upwards [hnear] with n hn
        simp only [_root_.sub_zero] at hn
        have hlower : -ε ≤ combined (f n) := (abs_le.mp hn).1
        have hcorr : 0 ≤ ctsInd (δ n) (P (f n) (φ n)) (p n) *
            (P (f n) (φ n) - (p n : ℝ)) := by
          by_cases hle : P (f n) (φ n) ≤ (p n : ℝ)
          · rw [ctsInd_eq_zero_of_le (δ n) _ _ (delta_pos n) hle]
            simp
          · have hdiff : 0 ≤ P (f n) (φ n) - (p n : ℝ) := by
              linarith [lt_of_not_ge hle]
            exact mul_nonneg (ctsInd_mem_Icc _ _ _).1 hdiff
        have hidentity : (family n).price P (f n) =
            combined (f n) + (1 / 2 : ℝ) *
              (ctsInd (δ n) (P (f n) (φ n)) (p n) *
                (P (f n) (φ n) - (p n : ℝ))) := by
          simp only [family, raw, AA, AB, pNeg, pOrig,
            AffineCombination.scale_price, AffineCombination.add_price,
            LUV.expectAffineSeq, LUV.expectAffine_priceAt, EF.denote_mul,
            EF.denote_const, ratCodeFeature, Pi.mul_apply, combined,
            highGap, crossAGap, crossBGap, flagN, index, δr, pr, φr,
            deferralImageFlag_at f hstrict hspec n,
            deferralPreimage_at f hstrict hspec n, Nat.cast_one, one_mul,
            hGDenote, Rat.cast_neg, Rat.cast_one, Rat.cast_div,
            Rat.cast_ofNat, neg_mul]
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
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (X Y : ℕ → LUV)
    (hX : LUV.PolyThresholdCodeSeq X) (hY : LUV.PolyThresholdCodeSeq Y)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X n) x)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Y n) ((X n).expect P (f n)))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n ↦ (X n).expect P n) ≈ₙ fun n ↦ (Y n).expect P n :=
  lic_expected_future_expectations P DP f X Y hP hworld
    (expectedFutureExpectationQuoteOfRepresentation f hstrict X Y hX hY
      source_valued reflected hP hworld)

/-- Paper-facing `thm:ceu` entry point from completed-world representation data.
Paper node: `thm:ceu` -/
theorem lic_no_expected_net_update_ofRepresentation
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (φ : ℕ → Sentence) (Y : ℕ → LUV)
    (hφ : PolySentenceCodes φ) (hY : LUV.PolyThresholdCodeSeq Y)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Y n) (P (f n) (φ n)))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n ↦ P n (φ n)) ≈ₙ fun n ↦ (Y n).expect P n :=
  lic_no_expected_net_update P DP f φ Y hP hworld
    (futurePriceQuoteOfRepresentation f hstrict φ Y hφ hY reflected hP hworld)

/-- Paper-facing `thm:ccee` entry point from completed-world product representations.
Paper node: `thm:ccee` -/
theorem lic_no_expected_net_update_conditional_ofRepresentation
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (X Z Z' : ℕ → LUV) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat P w)
    (hX : LUV.PolyThresholdCodeSeq X)
    (hZ : LUV.PolyThresholdCodeSeq Z)
    (hZ' : LUV.PolyThresholdCodeSeq Z')
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (X n) x)
    (left_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ x, v.ValuesAt (X n) x → v.ValuesAt (Z n) (x * w (f n)))
    (right_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Z' n) ((X n).expect P (f n) * w (f n)))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n ↦ (Z n).expect P n) ≈ₙ fun n ↦ (Z' n).expect P n :=
  lic_no_expected_net_update_conditional P DP f X Z Z' w hP hworld
    (conditionalExpectationQuoteOfRepresentation f hstrict X Z Z' w
      weight_mem weight_generable hX hZ hZ' source_valued left_reflected
      right_reflected hP hworld)

/-- Paper-facing `thm:st` entry point from completed-world confidence/product
representations.
Paper node: `thm:st` -/
theorem lic_self_trust_ofRepresentation
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (φ : ℕ → Sentence) (δ p : ℕ → ℚ) (A B : ℕ → LUV)
    (delta_pos : ∀ n, 0 < δ n)
    (probability_mem : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hφ : PolySentenceCodes φ) (hδ : PolyRatCodes δ)
    (hδinv : PolyRatCodes (fun n ↦ 1 / δ n))
    (hp : PolyRatCodes p)
    (hA : LUV.PolyThresholdCodeSeq A)
    (hB : LUV.PolyThresholdCodeSeq B)
    (confidence_reflected : ∀ n (v : PCWorld),
      v.ConsistentWithTheory DP →
        v.ValuesAt (B n) (ctsInd (δ n) (P (f n) (φ n)) (p n)))
    (product_reflected : ∀ n (v : PCWorld),
      v.ConsistentWithTheory DP →
        v.ValuesAt (A n)
          (v.payout (φ n) * ctsInd (δ n) (P (f n) (φ n)) (p n)))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n ↦ (A n).expect P n) ≳ₙ
      fun n ↦ (p n : ℝ) * (B n).expect P n :=
  lic_self_trust P DP f φ δ p A B hP hworld
    (selfTrustQuoteOfRepresentation f hstrict φ δ p A B delta_pos
      probability_mem hφ hδ hδinv hp hA hB confidence_reflected
      product_reflected hP hworld)

/-! ## Direct same-day consumers -/

/-- Paper-facing `thm:epr` entry point from concrete arithmetic quotation code.
Paper node: `thm:epr` -/
theorem lic_expectations_of_probabilities_ofCode
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    (Q : QuotationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    {value : ℕ → ℚ} (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, P n (φ n) = (value n : ℝ))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (φ n)) ≈ₙ fun n => (q.luv n).expect P n :=
  lic_expectations_of_probabilities P DP φ q.luv hworld
    (currentPriceExpectationQuoteOfCode Q φ hφ q hexact hP)

/-- Paper-facing `thm:er` entry point from concrete arithmetic quotation code.
Paper node: `thm:er` -/
theorem lic_iterated_expectations_ofCode
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    (Q : QuotationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    {value : ℕ → ℚ} (X : ℕ → LUV)
    (hX : LUV.PolyThresholdCodeSeq X)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, (X n).expect P n = (value n : ℝ))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (X n).expect P n) ≈ₙ fun n => (q.luv n).expect P n :=
  lic_iterated_expectations P DP X q.luv hworld
    (currentExpectationQuoteOfCode Q X hX q hexact hP)

/-- Paper-facing `thm:ref` entry point from generated endpoint features and the
arithmetically reflected interval decision.
Paper node: `thm:ref` -/
theorem lic_introspection_ofCode
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    (Q : QuotationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ)
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
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
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
  let package := introspectionIntervalQuoteOfCode Q φ hφ a b δ
    lowerFeature hlower upperFeature hupper hδ hδinv hδpos hδzero hab q hP
  simpa only using lic_introspection P DP φ a b δ package hP hworld

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
    (hwidthInv : PolyRatCodes (fun n ↦ 1 / width n))
    (hwidthPos : ∀ n, 0 < width n)
    (hwidthZero : Tendsto (fun n ↦ (width n : ℝ)) atTop (𝓝 0))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n
      ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n)) ≈ₙ
      fun _ => (p : ℝ) := by
  let package := paradoxResistanceQuoteOfDiagonal Q market p width hwidth hwidthInv
    hwidthPos hwidthZero
  simpa only using
    lic_paradox_resistance P DP p hp0 hp1 package market.price_mem_Icc hworld

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
