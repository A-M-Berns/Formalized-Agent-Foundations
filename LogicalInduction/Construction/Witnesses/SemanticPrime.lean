import LogicalInduction.Construction.Witnesses.QuotationAffine

/-!
# Compact semantic-prime names

The paper's public language is propositional over *prime* sentences.  This module records
the corresponding compact-name layer for a future fixed first-order semantic interpreter:
the public atom is only a handle, while its denotation belongs to the deductive process.

This is deliberately upstream of the product construction.  In particular, no source LUV,
market, or value is inspected while emitting a semantic-prime atom.
-/

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Reserved tag for compact handles whose denotation is supplied by a fixed semantic
theorem process. -/
def semanticPrimeTag : ℕ := 6

/-- The public handle consists of a schema selector and its unevaluated input. -/
def semanticPrimeCode (schema input : ℕ) : ℕ :=
  Nat.pair semanticPrimeTag (Nat.pair schema input)

/-- The semantic handle as an ordinary existing propositional atom. -/
def semanticPrimeSentence (schema input : ℕ) : Sentence :=
  Formula.atom (semanticPrimeCode schema input)

/-- Leaf schema names occupy the tag-`0` branch of the self-describing schema language. -/
def semanticSourceSchema (base : ℕ) : ℕ := Nat.pair 0 base

/-- Distinct schema/input pairs have distinct public names. -/
lemma semanticPrimeCode_injective :
    Function.Injective (fun p : ℕ × ℕ => semanticPrimeCode p.1 p.2) := by
  rintro ⟨s₁, i₁⟩ ⟨s₂, i₂⟩ h
  simp only [semanticPrimeCode, Nat.pair_eq_pair] at h
  exact Prod.ext h.2.1 h.2.2

/-- A semantic handle has a whole-value emission certificate whenever its input does.
Unlike a first-order numeral, the schema itself is a fixed token and the varying input is
not expanded into the public formula. -/
lemma semanticPrimeSentence_poly (schema : ℕ) {input : ℕ → ℕ}
    (hinput : PolyNatCodes input) :
    PolySentenceCodes (fun n => semanticPrimeSentence schema (input n)) := by
  let hpayload := (PolyFueled.const semanticPrimeTag).pair
    ((PolyFueled.const schema).pair hinput.code_poly)
  refine ⟨_, (((PolyFueled.const 1).pair hpayload).succ_comp).of_eq (fun _ => rfl)⟩

/-- Hence semantic handles are efficient sentence sequences in the symbol-metered API. -/
lemma semanticPrimeSentence_rpn (schema : ℕ) {input : ℕ → ℕ}
    (hinput : PolyNatCodes input) :
    RpnSentenceCodes (fun n => semanticPrimeSentence schema (input n)) :=
  RpnSentenceCodes.ofPolySentenceCodes (semanticPrimeSentence_poly schema hinput)

/-- A paper-facing LUV source has a syntax-bearing threshold schema, not merely an erased
family of propositional thresholds. -/
structure PresentedLUVSeq where
  thresholdSchema : ℕ
  source_schema : thresholdSchema.unpair.1 = 0
  toLUV : ℕ → LUV
  threshold_codes : LUV.RpnThresholdCodeSeq toLUV
  threshold_named : ∀ n r,
    (toLUV n).gt r = semanticPrimeSentence thresholdSchema
      (Nat.pair n (Encodable.encode r))

namespace PresentedLUVSeq

@[simp] lemma gt_eq (X : PresentedLUVSeq) (n : ℕ) (r : ℚ) :
    (X.toLUV n).gt r = semanticPrimeSentence X.thresholdSchema
      (Nat.pair n (Encodable.encode r)) :=
  X.threshold_named n r

end PresentedLUVSeq

/-! ## A fixed-process smoke test

The following deliberately tiny schema is not a product construction.  It verifies the
two properties the eventual semantic layer must have before it is connected to `LIA`: its
public names are semantic-prime handles, and one *fixed*, computable process makes both a
positive and a negative handle reflect in every completed world.
-/

/-- The one fixed schema used by the smoke test. -/
def semanticToySchema : ℕ := 0

/-- The arithmetic denotation of the toy schema: the unary formula `x = 0`.  The public
handle below does not serialize this formula; it only carries `semanticToySchema`. -/
noncomputable def semanticToyArithmeticFormula : ArithmeticSemisentence 1 := “x. x = 0”

@[simp] lemma semanticToyArithmeticFormula_eval (n : ℕ) :
    semanticToyArithmeticFormula.Evalb (![n]) ↔ n = 0 := by
  simp [semanticToyArithmeticFormula]

/-- The fixed process reveals one positive and one negative semantic fact at every stage. -/
def semanticToyDP : DeductiveProcess where
  D _ := {semanticPrimeSentence semanticToySchema 0,
    ∼semanticPrimeSentence semanticToySchema 1}
  mono _ _ h := h

/-- The fixed semantic process is computable by a literal constant program. -/
def semanticToyDPComputation : DeductiveProcessComputation semanticToyDP where
  code := Nat.Partrec.Code.const (Encodable.encode
    ({semanticPrimeSentence semanticToySchema 0,
      ∼semanticPrimeSentence semanticToySchema 1} : Finset Sentence))
  code_spec := fun _ => by simp [semanticToyDP]

/-- The canonical completed world for the toy schema. -/
def semanticToyWorld : PCWorld := fun a => a = semanticPrimeCode semanticToySchema 0

@[simp] lemma semanticToyWorld_holds_pos :
    semanticToyWorld.Holds (semanticPrimeSentence semanticToySchema 0) := by
  change semanticPrimeCode semanticToySchema 0 = semanticPrimeCode semanticToySchema 0
  rfl

@[simp] lemma semanticToyWorld_holds_neg :
    semanticToyWorld.Holds (∼semanticPrimeSentence semanticToySchema 1) := by
  change ¬ semanticPrimeCode semanticToySchema 1 = semanticPrimeCode semanticToySchema 0
  simp [semanticPrimeCode, Nat.pair_eq_pair]

/-- Non-vacuity of the fixed semantic process. -/
lemma semanticToyDP_hworld :
    semanticToyWorld.ConsistentWithTheory semanticToyDP := by
  intro n φ hφ
  simp only [semanticToyDP, Finset.mem_insert, Finset.mem_singleton] at hφ
  rcases hφ with rfl | rfl
  · exact semanticToyWorld_holds_pos
  · exact semanticToyWorld_holds_neg

/-- The exact bridge required of the fixed semantic theorem process.  `positive` and
`negative` are the external readings of a schema instance; the future arithmetic layer
must prove that they are supplied by one fixed interpreter, rather than add a process that
depends on a particular LUV source. -/
structure SemanticPrimePresentation (DP : DeductiveProcess) where
  positive : ℕ → ℕ → Prop
  negative : ℕ → ℕ → Prop
  positive_enters : ∀ schema input, positive schema input →
    ∃ k, semanticPrimeSentence schema input ∈ DP.D k
  negative_refutes : ∀ schema input, negative schema input →
    ∃ k, (∼semanticPrimeSentence schema input) ∈ DP.D k

namespace SemanticPrimePresentation

/-- Completed-process worlds reflect every semantic handle for which the two semantic
directions have been established. -/
lemma reflected {DP : DeductiveProcess} (S : SemanticPrimePresentation DP)
    {schema input : ℕ} {v : PCWorld} (hv : v.ConsistentWithTheory DP)
    (hpos : S.positive schema input) :
    v.Holds (semanticPrimeSentence schema input) := by
  obtain ⟨k, hk⟩ := S.positive_enters schema input hpos
  exact hv k _ hk

lemma not_reflected {DP : DeductiveProcess} (S : SemanticPrimePresentation DP)
    {schema input : ℕ} {v : PCWorld} (hv : v.ConsistentWithTheory DP)
    (hneg : S.negative schema input) :
    ¬ v.Holds (semanticPrimeSentence schema input) := by
  obtain ⟨k, hk⟩ := S.negative_refutes schema input hneg
  exact fun h => (PCWorld.holds_neg v _).mp (hv k _ hk) h

end SemanticPrimePresentation

/-- The toy process instantiates the generic bridge without depending on any source LUV
or on a market constructed from it. -/
def semanticToyPresentation : SemanticPrimePresentation semanticToyDP where
  positive schema input := schema = semanticToySchema ∧ input = 0
  negative schema input := schema = semanticToySchema ∧ input = 1
  positive_enters := by
    rintro schema input ⟨rfl, rfl⟩
    exact ⟨0, by simp [semanticToyDP]⟩
  negative_refutes := by
    rintro schema input ⟨rfl, rfl⟩
    exact ⟨0, by simp [semanticToyDP]⟩

/-- Positive semantic reflection in every world completed against the fixed process. -/
lemma semanticToy_positive_reflected {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticToyDP) :
    v.Holds (semanticPrimeSentence semanticToySchema 0) :=
  SemanticPrimePresentation.reflected semanticToyPresentation hv ⟨rfl, rfl⟩

/-- Negative semantic reflection in every world completed against the fixed process. -/
lemma semanticToy_negative_reflected {v : PCWorld}
    (hv : v.ConsistentWithTheory semanticToyDP) :
    ¬ v.Holds (semanticPrimeSentence semanticToySchema 1) :=
  SemanticPrimePresentation.not_reflected semanticToyPresentation hv ⟨rfl, rfl⟩

end LogicalInduction
