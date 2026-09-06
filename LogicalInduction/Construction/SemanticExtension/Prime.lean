import LogicalInduction.Construction.Quotation.MarketQuoteCodes
import LogicalInduction.Framework.Emission.WriteOut
import LogicalInduction.Construction.Quotation.ProductDefinition

/-!
# Compact semantic-prime names, and the unrestricted-source obstruction

The compact-name layer for the semantic extension of the market language, together with the
representation-boundary result that fixes what a name may be allowed to mean.  Neither is a
paper node: this module supplies the atom namespace that the rest of the lane prices against,
and it feeds `thm:ccee`'s exact-product route.

The paper's public language is propositional over *prime* sentences, so a semantic fact can
enter the language only as an atom.  A semantic-prime atom is a **handle**: the public name
carries a schema selector and an unevaluated input, while the denotation belongs to a fixed
deductive process.  No source LUV, market or value is inspected while emitting one.

## The allocation

`semanticPrimeTag = 4` in the global atom-payload allocation table at
`ComputationClaimKind.godelCode` (`Construction/Knowledge/Syntax.lean`).  A handle is
`Nat.pair 4 (Nat.pair schema input)` and is an ordinary propositional atom, so nothing about
`Sentence` changes.  The selector is itself paired, into disjoint branches: tag `0` for
proof-carrying source/cut presentations, tag `1` for products, tag `2` for quotation aliases.

## The unrestricted-source obstruction

`LUV.RpnThresholdCodeSeq` controls how efficiently threshold sentences are emitted but not
which propositional atoms they contain, so an efficient source can diagonalize against every
tag-`0` semantic-source schema.  No non-vacuous fixed process can wrap every such source in a
`PresentedLUVSeq` while identifying the wrapper's thresholds with the original thresholds in
all completed worlds.

The two objects of proof are `semanticDiagonalLUVSeq` — thresholds are the *negations* of the
schema-`n` leaf at index `n` — and `semanticValuedDiagonalLUVSeq`, a genuine indicator-style
`[0,1]` LUV with value `1` when the distinguished proposition is false.  Both are certified
`LUV.RpnThresholdCodeSeq`, so neither is excluded by the paper-facing premise.  The
obstruction is `no_nonvacuous_universal_presented_of_rpn`: an unrestricted fixed-process
`presented_of_rpn` plus stage-wise non-vacuity is inconsistent, the contradiction occurring at
the presentation's own schema index `Xhat.thresholdSchema.unpair.2`.

That is why every downstream admission gate in this directory is proof-carrying or
entailment-checked rather than universal.  `no_nonvacuous_worldValued_presented_of_rpn` is the
strengthened form: it rules out even a world-valued wrapper.

## What this module puts on the consumer surface

Unlike the rest of the lane, this module is interface.  `LogicalInduction/API.lean` advertises
five of its declarations as the §4.8 presented-LUV vocabulary a client states a threshold-only
source in — `PresentedLUVSeq` with its `gt_eq` simp lemma, the handle-named family
`semanticHandleLUVSeq` with its `def:ec` certificate
`semanticHandleLUVSeq_rpnThresholdCodeSeq`, and the obstruction
`no_nonvacuous_worldValued_presented_of_rpn` — and `APITests/LogicalInduction.lean` exercises
all five.

**Cross-lane edge.**  `Construction/Paper/FirstOrder.lean` imports this module, for
`semanticPrimeTag` and `SemanticPrimeFreshSentence` alone, so the `Paper/` lane — and with it
`paperDP` and every endpoint priced over it — sits downstream of this one in the import graph,
even though every `SemanticExtension/` endpoint is stated over `Paper/`'s objects.  That
module's header records the same edge.
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
fixed process enumerate handle sentences (`Construction/SemanticExtension/Source.lean`). -/
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

The emitter reduces the mesh rational `⌜i/k⌝` at runtime under a fixed atom shell.  The
reduction step is `encode_rat_natCast_div` (`Framework/Emission/Computable.lean`), whose
whole-emitter form is `encode_natDiv_polyFueled` there; four other threshold emitters — the
second one below, and those in `Construction/SemanticExtension/Source.lean`,
`Construction/SemanticExtension/Product.lean` and
`Construction/Quotation/ProductDefinition.lean` — spell the same `gcd` reduction out inline
under their own atom shells.

This is the whole-value form; `semanticHandleLUVSeq_rpnThresholdCodeSeq` below is its
token-metered weakening, which is the one the presented-source interface stores. -/
lemma semanticHandleLUVSeq_polyThresholdCodeSeq (schema : ℕ) :
    LUV.PolyThresholdCodeSeq (semanticHandleLUVSeq schema) := by
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

/-- Compact handles preserve `def:ec`'s token-metered threshold interface: the weakening of
the whole-value certificate above, and the form `PresentedLUVSeq.threshold_codes` stores. -/
lemma semanticHandleLUVSeq_rpnThresholdCodeSeq (schema : ℕ) :
    LUV.RpnThresholdCodeSeq (semanticHandleLUVSeq schema) :=
  LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq
    (semanticHandleLUVSeq_polyThresholdCodeSeq schema)

/-! ## Presented LUV sequences -/

/-- A paper-facing LUV source has a syntax-bearing threshold schema, not merely an erased
family of propositional thresholds.  The schema is what a fixed process needs in order to
know which handles the family will ever name; the diagonal below shows that an erased
family admits no such process. -/
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

namespace LogicalInduction

open LO LO.Propositional

private lemma natPair_zero_zero : Nat.pair 0 0 = 0 := by rfl

private lemma encodeRat_zero : Encodable.encode (0 : ℚ) = Nat.pair 0 1 := by rfl

attribute [local irreducible] Nat.sqrt

/-! ## The canonical naming program -/

/-- A canonical total naming program can be selected directly from the existing
`RpnThresholdCodeSeq` certificate.  No extra named-code premise is needed. -/
noncomputable def rpnThresholdSourceCode {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) : Nat.Partrec.Code :=
  Classical.choose hX.exists_code

/-- Exact specification of the selected naming program on the certificate's packed
`⟨n,⟨k,i⟩⟩` inputs. -/
lemma rpnThresholdSourceCode_spec {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) (m : ℕ) :
    Encodable.encode ((X m.unpair.1).gt
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))) ∈
      (rpnThresholdSourceCode hX).eval m :=
  Classical.choose_spec hX.exists_code m

/-! ## The source-language separation invariant -/

/-- A sentence belongs to the pre-extension source vocabulary when none of its atoms use
the semantic-prime tag reserved for the extension. -/
def SemanticPrimeFreshSentence (φ : Sentence) : Prop :=
  ∀ a ∈ sentenceAtomCodes φ, a.unpair.1 ≠ semanticPrimeTag

/-- Pointwise source-language separation for a sequence of LUV threshold families. -/
def SemanticPrimeFreshLUVSeq (X : ℕ → LUV) : Prop :=
  ∀ n r, SemanticPrimeFreshSentence ((X n).gt r)

/-! ## The threshold diagonal -/

/-- At index `n`, negate the semantic leaf belonging to the `n`th source schema.  Whichever
tag-`0` schema a proposed presentation chooses, the source attacks it at one index. -/
def semanticDiagonalLUVSeq (n : ℕ) : LUV where
  gt r := ∼semanticPrimeSentence (semanticSourceSchema n)
    (Nat.pair n (Encodable.encode r))

@[simp] lemma semanticDiagonalLUVSeq_gt (n : ℕ) (r : ℚ) :
    (semanticDiagonalLUVSeq n).gt r =
      ∼semanticPrimeSentence (semanticSourceSchema n)
        (Nat.pair n (Encodable.encode r)) := rfl

/-- The diagonal family is already efficiently codeable in the stronger whole-value
interface.  Thus it is not excluded by the paper-facing `RpnThresholdCodeSeq` premise. -/
lemma semanticDiagonalLUVSeq_polyThresholdCodeSeq :
    LUV.PolyThresholdCodeSeq semanticDiagonalLUVSeq := by
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
  have schemaPF := (PolyFueled.const 0).pair hn
  have atomPF := ((PolyFueled.const 1).pair
    ((PolyFueled.const semanticPrimeTag).pair
      (schemaPF.pair (hn.pair meshPF)))).succ_comp
  have negPF := ((PolyFueled.const 2).pair
    (atomPF.pair (PolyFueled.const 1))).succ_comp
  refine ⟨_, negPF.of_eq (fun m => ?_)⟩
  rw [semanticDiagonalLUVSeq_gt, semanticPrimeSentence, semanticPrimeCode,
    semanticSourceSchema, encode_negAtom]
  simp only [Nat.unpair_pair, ifzSelFn]
  have hpair00 : Nat.pair 0 0 = 0 := natPair_zero_zero
  rw [hpair00]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · rw [if_pos hk0, hk0]
    have hrat0 : Encodable.encode (0 : ℚ) = Nat.pair 0 1 := encodeRat_zero
    simp [hrat0]
  · rw [if_neg hk0]
    have hg : 0 < Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk0)
    have hg1 : (Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1).pred + 1 =
        Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.succ_pred_eq_of_pos hg
    rw [hg1, encode_rat_natCast_div hk0, two_mul]

/-- The same diagonal family satisfies the exact source premise proposed for
`presented_of_rpn`. -/
lemma semanticDiagonalLUVSeq_rpnThresholdCodeSeq :
    LUV.RpnThresholdCodeSeq semanticDiagonalLUVSeq :=
  LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq
    semanticDiagonalLUVSeq_polyThresholdCodeSeq

/-- **The diagonal argument.**  A source whose threshold at `0` negates the schema-`n` leaf
at index `n` cannot be reflected by any `PresentedLUVSeq` in a completed world: the
presentation's own schema index `Xhat.thresholdSchema.unpair.2` is where the two disagree. -/
lemma not_reflected_of_negates_own_schema (DP : DeductiveProcess) (Xhat : PresentedLUVSeq)
    {Y : ℕ → LUV}
    (hY : ∀ n, (Y n).gt 0 = ∼semanticPrimeSentence (semanticSourceSchema n)
      (Nat.pair n (Encodable.encode (0 : ℚ)))) :
    ¬ (∃ v : PCWorld, v.ConsistentWithTheory DP ∧
      ∀ n r, v.Holds ((Xhat.toLUV n).gt r) ↔ v.Holds ((Y n).gt r)) := by
  rintro ⟨v, hv, hreflect⟩
  let n := Xhat.thresholdSchema.unpair.2
  have hschema : semanticSourceSchema n = Xhat.thresholdSchema := by
    rw [semanticSourceSchema]
    exact (congrArg (fun k => Nat.pair k Xhat.thresholdSchema.unpair.2)
      Xhat.source_schema).symm.trans (Nat.pair_unpair Xhat.thresholdSchema)
  have h := hreflect n 0
  rw [PresentedLUVSeq.gt_eq, hY n, hschema, PCWorld.holds_neg] at h
  by_cases hp : v.Holds
      (semanticPrimeSentence Xhat.thresholdSchema
        (Nat.pair n (Encodable.encode (0 : ℚ))))
  · exact (h.mp hp) hp
  · exact hp (h.mpr hp)

/-- No completed world can validate threshold reflection between the diagonal source and
any `PresentedLUVSeq`.  The contradiction occurs at the presentation's own schema index. -/
lemma semanticDiagonal_not_reflected (DP : DeductiveProcess) (Xhat : PresentedLUVSeq) :
    ¬ (∃ v : PCWorld, v.ConsistentWithTheory DP ∧
      ∀ n r,
        (v.Holds ((Xhat.toLUV n).gt r) ↔
          v.Holds ((semanticDiagonalLUVSeq n).gt r))) :=
  not_reflected_of_negates_own_schema DP Xhat (fun _ => rfl)

/-- Therefore an unrestricted, fixed-process `presented_of_rpn` theorem plus non-vacuity
is inconsistent.  Any successful bridge must restore the paper's language-separation fact
(for example as a type-level source-language invariant); parser computability alone cannot
prove it from `RpnThresholdCodeSeq`. -/
lemma no_nonvacuous_universal_presented_of_rpn (DP : DeductiveProcess)
    (presented_of_rpn : ∀ (X : ℕ → LUV), LUV.RpnThresholdCodeSeq X →
      ∃ Xhat : PresentedLUVSeq,
        ∀ n r (v : PCWorld), v.ConsistentWithTheory DP →
          (v.Holds ((Xhat.toLUV n).gt r) ↔ v.Holds ((X n).gt r))) :
    ¬ ∃ v : PCWorld, v.ConsistentWithTheory DP := by
  rintro ⟨v, hv⟩
  obtain ⟨Xhat, hreflect⟩ := presented_of_rpn semanticDiagonalLUVSeq
    semanticDiagonalLUVSeq_rpnThresholdCodeSeq
  exact semanticDiagonal_not_reflected DP Xhat
    ⟨v, hv, fun n r => hreflect n r v hv⟩

/-! ## The world-valued diagonal -/

/-- The distinguished proposition attacked by the valued diagonal at index `n`. -/
def semanticValuedDiagonalProp (n : ℕ) : Sentence :=
  semanticPrimeSentence (semanticSourceSchema n)
    (Nat.pair n (Encodable.encode (0 : ℚ)))

/-- A genuine indicator-style `[0,1]` LUV: it has value `1` when the distinguished
semantic proposition is false and value `0` when it is true. -/
def semanticValuedDiagonalLUVSeq (n : ℕ) : LUV where
  gt r := if r < 0 then ⊤ else if r < 1 then ∼semanticValuedDiagonalProp n else ⊥

@[simp] lemma semanticValuedDiagonalLUVSeq_gt (n : ℕ) (r : ℚ) :
    (semanticValuedDiagonalLUVSeq n).gt r =
      (if r < 0 then ⊤ else if r < 1 then ∼semanticValuedDiagonalProp n else ⊥) := rfl

/-- The valued diagonal is an indicator in every deductive process, without using
consistency: its threshold cut is definitionally coherent. -/
lemma semanticValuedDiagonalLUVSeq_isIndicator (DP : DeductiveProcess) (n : ℕ) :
    (semanticValuedDiagonalLUVSeq n).IsIndicator
      (∼semanticValuedDiagonalProp n) DP := by
  intro v hv r
  have hr0 : ((r : ℝ) < 0) ↔ r < 0 := by exact_mod_cast Iff.rfl
  have hr1 : ((r : ℝ) < 1) ↔ r < 1 := by exact_mod_cast Iff.rfl
  refine ⟨fun h => ?_, fun hlo hhi => ?_, fun h => ?_⟩
  · rw [semanticValuedDiagonalLUVSeq_gt, if_pos (hr0.mp h)]
    exact PCWorld.holds_top v
  · have hn0 : ¬ r < 0 := fun h => (not_lt.mpr hlo) (hr0.mpr h)
    rw [semanticValuedDiagonalLUVSeq_gt, if_neg hn0, if_pos (hr1.mp hhi)]
  · have hn1 : ¬ r < 1 := fun h' => (not_lt.mpr h) (hr1.mpr h')
    have hn0 : ¬ r < 0 := fun h' => hn1 (h'.trans (by norm_num))
    simp [semanticValuedDiagonalLUVSeq_gt, hn0, hn1, PCWorld.Holds,
      LO.Propositional.Formula.Boolean.val]

/-- Hence the valued diagonal satisfies the closed CCEE `source_valued` premise for every
process, at the Boolean value of its defining indicator proposition. -/
lemma semanticValuedDiagonalLUVSeq_valuesAt (DP : DeductiveProcess) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    v.ValuesAt (semanticValuedDiagonalLUVSeq n)
      (v.payout (∼semanticValuedDiagonalProp n)) :=
  (semanticValuedDiagonalLUVSeq_isIndicator DP n).valuesAt hv

lemma semanticValuedDiagonalLUVSeq_source_valued (DP : DeductiveProcess) :
    ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (semanticValuedDiagonalLUVSeq n) x := by
  intro n v hv
  exact ⟨v.payout (∼semanticValuedDiagonalProp n),
    semanticValuedDiagonalLUVSeq_valuesAt DP n v hv⟩

private lemma semanticValuedDiagonalProp_neg_rpn :
    RpnSentenceCodes (fun m => ∼semanticValuedDiagonalProp m.unpair.1) := by
  have hn := PolyFueled.left
  have hschema := (PolyFueled.const 0).pair hn
  have hinput := hn.pair (PolyFueled.const (Encodable.encode (0 : ℚ)))
  have hatom := ((PolyFueled.const 1).pair
    ((PolyFueled.const semanticPrimeTag).pair (hschema.pair hinput))).succ_comp
  have hneg := ((PolyFueled.const 2).pair
    (hatom.pair (PolyFueled.const 1))).succ_comp
  refine RpnSentenceCodes.ofPolySentenceCodes ⟨_, hneg.of_eq (fun m => ?_)⟩
  simp only [semanticValuedDiagonalProp, semanticPrimeSentence, semanticPrimeCode,
    semanticSourceSchema, encode_negAtom]
  have hpair00 : Nat.pair 0 0 = 0 := natPair_zero_zero
  simp [hpair00]

/-- On a mesh query `⟨n,⟨k,i⟩⟩`, this selector is zero exactly when `i/k < 1`, including
the repository's `k = 0` convention where the rational quotient is zero. -/
def semanticValuedDiagonalMeshSelector (m : ℕ) : ℕ :=
  ifzSelFn (Nat.pair 0 (m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1))
    m.unpair.2.unpair.1

lemma semanticValuedDiagonalMeshSelector_polyFueled :
    ∃ c, PolyFueled c semanticValuedDiagonalMeshSelector := by
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  have htest := subc_polyFueled.comp (hi.succ_comp.pair hk)
  refine ⟨_, (ifzSel_polyFueled.comp (((PolyFueled.const 0).pair htest).pair hk)).of_eq
    (fun m => by simp only [semanticValuedDiagonalMeshSelector, Nat.unpair_pair])⟩

/-- The world-valued diagonal remains efficiently codeable. -/
lemma semanticValuedDiagonalLUVSeq_rpnThresholdCodeSeq :
    LUV.RpnThresholdCodeSeq semanticValuedDiagonalLUVSeq := by
  obtain ⟨c, hc⟩ := semanticValuedDiagonalMeshSelector_polyFueled
  have h := RpnSentenceCodes.ifZero semanticValuedDiagonalProp_neg_rpn
    (RpnSentenceCodes.const (⊥ : Sentence)) hc
  refine h.of_eq (fun m => ?_)
  rw [semanticValuedDiagonalLUVSeq_gt]
  have hnonneg : ¬ ((m.unpair.2.unpair.2 : ℚ) /
      (m.unpair.2.unpair.1 : ℚ)) < 0 :=
    not_lt.mpr (div_nonneg (by positivity) (by positivity))
  rw [if_neg hnonneg]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · simp [semanticValuedDiagonalMeshSelector, hk0, ifzSelFn]
  · by_cases hi : m.unpair.2.unpair.2 < m.unpair.2.unpair.1
    · have hsub : m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1 = 0 := by omega
      have hrat : (m.unpair.2.unpair.2 : ℚ) /
          (m.unpair.2.unpair.1 : ℚ) < 1 := by
        rw [div_lt_one (by exact_mod_cast Nat.pos_of_ne_zero hk0)]
        exact_mod_cast hi
      simp [semanticValuedDiagonalMeshSelector, hk0, hsub, hrat, ifzSelFn]
    · have hsub : 0 < m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1 := by omega
      have hrat : ¬ (m.unpair.2.unpair.2 : ℚ) /
          (m.unpair.2.unpair.1 : ℚ) < 1 := by
        rw [not_lt, one_le_div (by exact_mod_cast Nat.pos_of_ne_zero hk0)]
        exact_mod_cast (Nat.le_of_not_gt hi)
      simp [semanticValuedDiagonalMeshSelector, hk0, hsub.ne', hrat, ifzSelFn]

/-- Even inside the actual world-valued e.c. source class used by closed CCEE, no
presentation can reflect this source in a completed world. -/
lemma semanticValuedDiagonal_not_reflected (DP : DeductiveProcess)
    (Xhat : PresentedLUVSeq) :
    ¬ (∃ v : PCWorld, v.ConsistentWithTheory DP ∧
      ∀ n r, v.Holds ((Xhat.toLUV n).gt r) ↔
        v.Holds ((semanticValuedDiagonalLUVSeq n).gt r)) :=
  not_reflected_of_negates_own_schema DP Xhat (fun n => by
    rw [semanticValuedDiagonalLUVSeq_gt, if_neg (by norm_num), if_pos (by norm_num),
      semanticValuedDiagonalProp])

/-- Strengthened obstruction: even restricting the universal bridge to source families
that satisfy the exact completed-world valuedness premise of closed CCEE is incompatible
with a non-vacuous fixed process. -/
lemma no_nonvacuous_worldValued_presented_of_rpn (DP : DeductiveProcess)
    (presented_of_rpn : ∀ (X : ℕ → LUV), LUV.RpnThresholdCodeSeq X →
      (∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∃ x, v.ValuesAt (X n) x) →
      ∃ Xhat : PresentedLUVSeq,
        ∀ n r (v : PCWorld), v.ConsistentWithTheory DP →
          (v.Holds ((Xhat.toLUV n).gt r) ↔ v.Holds ((X n).gt r))) :
    ¬ ∃ v : PCWorld, v.ConsistentWithTheory DP := by
  rintro ⟨v, hv⟩
  obtain ⟨Xhat, hreflect⟩ := presented_of_rpn semanticValuedDiagonalLUVSeq
    semanticValuedDiagonalLUVSeq_rpnThresholdCodeSeq
    (semanticValuedDiagonalLUVSeq_source_valued DP)
  exact semanticValuedDiagonal_not_reflected DP Xhat
    ⟨v, hv, fun n r => hreflect n r v hv⟩

end LogicalInduction
