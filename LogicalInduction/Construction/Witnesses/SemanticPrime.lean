import LogicalInduction.Construction.Witnesses.QuoteCodeOfMarket
import LogicalInduction.Framework.WriteOut

/-!
# Compact semantic-prime names

The compact-name layer for the semantic extension of the market language.  This is not a
paper node of its own: it supplies the atom namespace that the `Semantic*` witness modules
price against, and it feeds `thm:ccee`'s exact-product lane.

The paper's public language is propositional over *prime* sentences, so a semantic fact can
enter the language only as an atom.  A semantic-prime atom is a **handle**: the public name
carries a schema selector and an unevaluated input, while the denotation belongs to a fixed
deductive process.  No source LUV, market or value is inspected while emitting one.

## The allocation

`semanticPrimeTag = 4` in the global atom-payload allocation table at
`ComputationClaimKind.godelCode` (`ComputationSyntax.lean`).  A handle is
`Nat.pair 4 (Nat.pair schema input)` and is an ordinary propositional atom, so nothing about
`Sentence` changes.

## The schema language

The selector is itself paired, into three disjoint branches:

* tag `0` — `semanticSourceSchema` / `semanticEmitterSchema`, emitted-source programs;
* tag `1` — `semanticProductSchema` (`SemanticProduct.lean`), the product constructor;
* tag `2` — `semanticQuoteSchema` (`SemanticQuote.lean`), quotation aliases.

The tags are disjoint by construction (`semanticEmitterSchema_ne_quote`), which is what stops
two fixed interpreters assigning one handle two meanings.

## Objects and results

`semanticPrimeTag`, `semanticPrimeCode`, `semanticPrimeSentence`, the three schema
constructors, and `semanticHandleLUVSeq` — the `LUV` family named by one schema.  The main
result is `semanticHandleLUVSeq_rpnThresholdCodeSeq`: a compact handle satisfies `def:ec`'s
token-metered threshold interface (`LUV.RpnThresholdCodeSeq`), so the extension costs nothing
at the emission surface.

`PresentedLUVSeq` is the module's principal export — a LUV sequence carrying its threshold
*schema* rather than an erased family of propositional thresholds.  `SemanticSource`,
`SemanticProduct`, `SemanticJoint`, `CertifiedSource` and `SemanticCertifiedProduct` all build
on it.  Carrying the schema is forced, not stylistic: `SemanticSource.lean`'s diagonal shows
that no fixed process wraps every erased threshold family.

Design choices: `dd:quote-code` — a handle names a code rather than quantifying over an
abstract schema; and the threshold certificate is the token-metered `RpnThresholdCodeSeq`.
-/

namespace LogicalInduction

open LO LO.Propositional LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## The compact handle -/

/-- Reserved tag for compact handles whose denotation is supplied by a fixed semantic
theorem process.  See the global atom-payload allocation table at
`ComputationClaimKind.godelCode`. -/
def semanticPrimeTag : ℕ := 4

/-- The public handle consists of a schema selector and its unevaluated input. -/
def semanticPrimeCode (schema input : ℕ) : ℕ :=
  Nat.pair semanticPrimeTag (Nat.pair schema input)

/-- The semantic handle as an ordinary existing propositional atom. -/
def semanticPrimeSentence (schema input : ℕ) : Sentence :=
  Formula.atom (semanticPrimeCode schema input)

/-- Distinct schema/input pairs have distinct public names. -/
lemma semanticPrimeCode_injective :
    Function.Injective (fun p : ℕ × ℕ => semanticPrimeCode p.1 p.2) := by
  rintro ⟨s₁, i₁⟩ ⟨s₂, i₂⟩ h
  simp only [semanticPrimeCode, Nat.pair_eq_pair] at h
  exact Prod.ext h.2.1 h.2.2

/-- Naming a handle is primitive recursive in its schema and input, which is what lets a
fixed process enumerate handle sentences (`SemanticSourceDP.lean`). -/
lemma semanticPrimeSentence_encode_prim : Primrec fun p : ℕ × ℕ =>
    Encodable.encode (semanticPrimeSentence p.1 p.2) :=
  (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1)
    (Primrec₂.natPair.comp (Primrec.const semanticPrimeTag)
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)))).of_eq (fun _ => rfl)

/-! ## The schema language -/

/-- Leaf schema names occupy the tag-`0` branch of the self-describing schema language. -/
def semanticSourceSchema (base : ℕ) : ℕ := Nat.pair 0 base

/-- Generic emitted-source programs share the tag-`0` leaf branch: `semanticEmitterSchema code`
names the emitted-source program `code`.  Tag `1` is the product constructor and tag `2` the
quotation aliases, so no handle gets two meanings (`semanticEmitterSchema_ne_quote`). -/
def semanticEmitterSchema (code : ℕ) : ℕ :=
  semanticSourceSchema code

/-- Quotation aliases occupy the tag-`2` branch of the schema language:
`semanticQuoteSchema code` names the universal quotation selector `code`
(`SemanticQuote.semanticQuoteLeaf`).  Disjoint from `semanticSourceSchema`'s tag `0` and
`semanticProductSchema`'s tag `1`. -/
def semanticQuoteSchema (code : ℕ) : ℕ :=
  Nat.pair 2 code

@[simp] lemma semanticEmitterSchema_source (code : ℕ) :
    (semanticEmitterSchema code).unpair.1 = 0 := by
  simp [semanticEmitterSchema, semanticSourceSchema]

@[simp] lemma semanticQuoteSchema_source (code : ℕ) :
    (semanticQuoteSchema code).unpair.1 = 2 := by
  simp [semanticQuoteSchema]

/-- Emitted-source programs and quotation aliases never share a schema selector: this is the
disjointness the schema language rests on. -/
lemma semanticEmitterSchema_ne_quote (emitter quote : ℕ) :
    semanticEmitterSchema emitter ≠ semanticQuoteSchema quote := by
  intro h
  simp [semanticEmitterSchema, semanticQuoteSchema, semanticSourceSchema,
    Nat.pair_eq_pair] at h

/-! ## Handle-named LUV families -/

/-- The ordinary `LUV` family named by one compact semantic schema. -/
def semanticHandleLUVSeq (schema n : ℕ) : LUV where
  gt r := semanticPrimeSentence schema (Nat.pair n (Encodable.encode r))

@[simp] lemma semanticHandleLUVSeq_gt (schema n : ℕ) (r : ℚ) :
    (semanticHandleLUVSeq schema n).gt r =
      semanticPrimeSentence schema (Nat.pair n (Encodable.encode r)) := rfl

/-- Compact handles preserve the repository's token-metered threshold interface.

The emitter reduces the mesh rational `⌜i/k⌝` at runtime under a fixed atom shell; that
reduction is the generic `Dovetail.encode_natDiv_polyFueled`, which four other threshold
emitters (`SemanticSource`, `SemanticProduct`, `ProductDefinition`, `QuoteCodeOfMarket`)
spell out again in the same form. -/
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

/-! ## Presented LUV sequences -/

/-- A paper-facing LUV source has a syntax-bearing threshold schema, not merely an erased
family of propositional thresholds.  The schema is what a fixed process needs in order to
know which handles the family will ever name; `SemanticSource.lean`'s diagonal shows that an
erased family admits no such process. -/
structure PresentedLUVSeq where
  /-- The schema selector every threshold of the family is named under. -/
  thresholdSchema : ℕ
  /-- The selector lies in the tag-`0` leaf branch, so it cannot collide with the product
  constructor or a quotation alias. -/
  source_schema : thresholdSchema.unpair.1 = 0
  /-- The underlying family of logically uncertain variables. -/
  toLUV : ℕ → LUV
  /-- `def:ec`'s token-metered threshold certificate for that family. -/
  threshold_codes : LUV.RpnThresholdCodeSeq toLUV
  /-- The naming identity: the `n`-th threshold at `r` *is* the handle
  `semanticPrimeSentence thresholdSchema ⟨n, ⌜r⌝⟩`. -/
  threshold_named : ∀ n r,
    (toLUV n).gt r = semanticPrimeSentence thresholdSchema
      (Nat.pair n (Encodable.encode r))

namespace PresentedLUVSeq

@[simp] lemma gt_eq (X : PresentedLUVSeq) (n : ℕ) (r : ℚ) :
    (X.toLUV n).gt r = semanticPrimeSentence X.thresholdSchema
      (Nat.pair n (Encodable.encode r)) :=
  X.threshold_named n r

end PresentedLUVSeq

end LogicalInduction
