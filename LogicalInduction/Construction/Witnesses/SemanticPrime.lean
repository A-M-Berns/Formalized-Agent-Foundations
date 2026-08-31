import LogicalInduction.Construction.Witnesses.QuoteCodeOfMarket
import LogicalInduction.Framework.WriteOut

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

/-- Generic emitted-source programs and quotation aliases have disjoint schema tags.
This prevents two fixed interpreters from assigning different meanings to the same
semantic-prime handle.  Tag `1` remains the product constructor. -/
def semanticEmitterSchema (code : ℕ) : ℕ :=
  semanticSourceSchema code

def semanticQuoteSchema (code : ℕ) : ℕ :=
  Nat.pair 2 code

/-- The ordinary `LUV` family named by one compact semantic schema. -/
def semanticHandleLUVSeq (schema n : ℕ) : LUV where
  gt r := semanticPrimeSentence schema (Nat.pair n (Encodable.encode r))

@[simp] lemma semanticHandleLUVSeq_gt (schema n : ℕ) (r : ℚ) :
    (semanticHandleLUVSeq schema n).gt r =
      semanticPrimeSentence schema (Nat.pair n (Encodable.encode r)) := rfl

/-- Compact handles preserve the repository's token-metered threshold interface. -/
lemma semanticHandleLUVSeq_rpnThresholdCodeSeq (schema : ℕ) :
    LUV.RpnThresholdCodeSeq (semanticHandleLUVSeq schema) := by
  obtain ⟨cg, hgcd⟩ := gcdc_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hn := PolyFueled.left
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  have gPF := hgcd.comp (hi.pair hk)
  have pgPF := predc_polyFueled.comp gPF
  have numPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hi))
  have denPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hk))
  have h2num := had.comp (numPF.pair numPF)
  have meshPF := ifzSel_polyFueled.comp
    (((PolyFueled.const (Nat.pair 0 1)).pair (h2num.pair denPF)).pair hk)
  have fullPF := ((PolyFueled.const 1).pair
    ((PolyFueled.const semanticPrimeTag).pair
      ((PolyFueled.const schema).pair (hn.pair meshPF)))).succ_comp
  apply LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq
  refine ⟨_, fullPF.of_eq (fun m => ?_)⟩
  rw [semanticHandleLUVSeq_gt, semanticPrimeSentence, semanticPrimeCode, encode_atom]
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · rw [if_pos hk0, hk0]
    norm_num
    rfl
  · rw [if_neg hk0]
    have hg : 0 < Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk0)
    have hg1 : (Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1).pred + 1 =
        Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.succ_pred_eq_of_pos hg
    rw [hg1, encode_rat_natCast_div hk0, two_mul]

@[simp] lemma semanticEmitterSchema_source (code : ℕ) :
    (semanticEmitterSchema code).unpair.1 = 0 := by
  simp [semanticEmitterSchema, semanticSourceSchema]

@[simp] lemma semanticQuoteSchema_source (code : ℕ) :
    (semanticQuoteSchema code).unpair.1 = 2 := by
  simp [semanticQuoteSchema]

lemma semanticEmitterSchema_ne_quote (emitter quote : ℕ) :
    semanticEmitterSchema emitter ≠ semanticQuoteSchema quote := by
  intro h
  simp [semanticEmitterSchema, semanticQuoteSchema, semanticSourceSchema,
    Nat.pair_eq_pair] at h

lemma semanticEmitterSchema_prim : Primrec semanticEmitterSchema :=
  (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id).of_eq (fun _ => rfl)

lemma semanticQuoteSchema_prim : Primrec semanticQuoteSchema :=
  (Primrec₂.natPair.comp (Primrec.const 2) Primrec.id).of_eq (fun _ => rfl)

lemma semanticPrimeSentence_encode_prim : Primrec fun p : ℕ × ℕ =>
    Encodable.encode (semanticPrimeSentence p.1 p.2) :=
  (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1)
    (Primrec₂.natPair.comp (Primrec.const semanticPrimeTag)
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)))).of_eq (fun _ => rfl)

/-- Distinct schema/input pairs have distinct public names. -/
lemma semanticPrimeCode_injective :
    Function.Injective (fun p : ℕ × ℕ => semanticPrimeCode p.1 p.2) := by
  rintro ⟨s₁, i₁⟩ ⟨s₂, i₂⟩ h
  simp only [semanticPrimeCode, Nat.pair_eq_pair] at h
  exact Prod.ext h.2.1 h.2.2

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
