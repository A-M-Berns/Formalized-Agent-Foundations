import LogicalInduction.Construction.Knowledge.Syntax
import LogicalInduction.Construction.Statistics.SettlementCompiler
import LogicalInduction.Construction.Quotation.Packages
import LogicalInduction.Construction.LIACompiler
import Foundation.FirstOrder.Incompleteness.Halting
-- for `ISigma1_delta1Definable`; not reachable through `Incompleteness.Halting`
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
import LogicalInduction.Framework.Emission.WriteOut

/-!
# The computation/quotation literal stream

For a fixed `Δ₁` theory `T` interpreting `𝗣𝗔⁻`, this file constructs a computable
deductive process `theoremDP` whose stages are the `T`-provable instances of the fixed
universal computation and quotation schemas.

It discharges the hypotheses the `_ofComputation` and `_ofCode` endpoints take over such a
process: `ComputationTheoryPresentation` (`theoremPresentation`) and
`QuotationTheoryPresentation` (`quotationPresentation`), together with the market
non-vacuity hypothesis `hworld` (`theoremDP_hworld`).  `hworld` is *proved* from
consistency of `T`: every refutation tag fires on the literal negation of the sentence its
positive partner fires on, and the two quotation fibers are refuted jointly inside `T`
(`universalQuote_exclusive_prov`), so no semantic hypothesis on `T` is needed.

An *event* is a code `e = ⟨tag, z⟩` with `tag ∈ {0,…,5}` selecting one of six
enters/refutes obligations — four computation tags and two quotation tags — and `z` its
input.  One r.e. predicate `eventFires` and one atom map `eventAtom` carry all six, and a
stage is the fuel-`k` dovetail of the events `e ≤ k`.  Because quotation folds a
decidable-decision selector into the numeral of the *fixed* schemas
`universalQuotePos`/`universalQuoteNeg`, its instances are enumerable by the same
`provable_instances_re` as the computation tags.  (Those are *event* tags; the quotation
atoms' payload tag is `2` — see the allocation table at `ComputationClaimKind.godelCode`.)

The two mechanical obligations behind the construction are discharged here: provability of
schema instances is recursively enumerable (`provable_instances_re`), and the fuel-clocked
stage enumerator is primitive recursive (`eventAtom_prim`, `theoremStage_encode_prim`,
`theoremDP_computable`).

`theoremDP` is a *component*, not a market of record.  The paper fixes one deductive
process, and every paper-facing endpoint is priced over `paperDP`
(`Construction/Paper/TheoremDP.lean`), which unions this literal stream with the `Θ`-complete
first-order theorem stream and whose `paperQuotationPresentation` and `paperDP_hworld` are lifted
from the presentation and non-vacuity proved here.  The self-reference family (`thm:ref`, `thm:lp`,
`thm:st`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`) is assembled in
`Construction/Paper/Market.lean`, the meta-learning family (`thm:halts`, `thm:loops`,
`thm:dontwait`, `thm:pac`, `thm:pazfc`, `thm:incons`) in `Construction/Knowledge/Endpoints.lean`.

`liaMarketComputation` is the `LIA`'s exact market program over an arbitrary computable
deductive process (`thm:lia`); `theoremMarketComputation` instantiates it at this stream.
Its one consumer is `theoremDeferredWeightQuoteCode`
(`Construction/Quotation/MarketQuoteCodes.lean`), which feeds
`lic_no_expected_net_update_conditional_exact_productExtension`
(`Construction/Quotation/ProductDefinition.lean`) — the definitional-extension *diagnosis*
of the `thm:ccee` mesh slack, which keeps this stream as its base process by ruling and
which that module's own header is explicit is not a rendering of the node.  The one
canonical endpoint priced outside `paperDP` is a different one:
`lic_no_expected_net_update_conditional_exact_canonical` over `liaHistory (canonicalCCEEDP T)`
(`Construction/SemanticExtension/Endpoints.lean`; see `Construction/Paper/Market.lean`).

This module reaches the `Construction/Statistics/` lane for one lemma: `encode_toFinset_eq`
(`Construction/Statistics/SettlementCompiler.lean`), the shared normal form every stage
encoder in the `Construction/` lanes reduces to, which is why the import list names that
module.

Hypotheses: `[T.Δ₁]` for the enumeration, `[𝗣𝗔⁻ ⪯ T]` and `[Entailment.Consistent T]` for
non-vacuity; that is the whole premise set.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional
open Filter Topology

/-! ## Provability of schema instances is recursively enumerable -/

open Classical in
/-- For a fixed schema `φ` and a `Δ₁` theory `T`, provability of `φ`'s numerical instances
is recursively enumerable: the predicate is `𝚺₁` by `definability` and internalisation, and
`re_iff_sigma1` converts it.  Mirrors the positive-path assembly inside FFL's
`incomplete_of_REPred_not_ComputablePred_Nat'`. -/
lemma provable_instances_re (T : ArithmeticTheory) [T.Δ₁]
    (φ : ArithmeticSemisentence 1) :
    REPred (fun z : ℕ => T ⊢ φ/[↑z]) := by
  have hsig : 𝚺₁-Predicate fun b : ℕ ↦
      Bootstrapping.Provable T
        (Bootstrapping.subst ℒₒᵣ ?[Bootstrapping.Arithmetic.numeral b] ⌜φ⌝) := by
    definability
  apply REPred.of_eq (re_iff_sigma1.mpr hsig)
  intro a
  constructor
  · rintro hP
    apply Bootstrapping.Provable.sound
    simpa [Sentence.quote_def, Semiformula.quote_def,
      Rewriting.emb_subst_eq_subst_coe₁] using hP
  · rintro hφ
    simpa [Sentence.quote_def, Semiformula.quote_def,
      Rewriting.emb_subst_eq_subst_coe₁] using
      Bootstrapping.internalize_provability (V := ℕ) hφ

/-! ## The combined event stream

An *event* is a code `e = ⟨tag, z⟩` with `tag ∈ {0,…,5}` selecting one of the six
enters/refutes obligations (four computation tags 0–3, two quotation tags 4–5) and `z` its
input (for quotation, `z = ⟨code, input⟩`).  A single r.e. predicate `Fires` and a single
atom map `atom` capture all six; the deductive process enumerates the fired atoms. -/

variable (T : ArithmeticTheory)

/-- The public literal an event contributes to the deductive process. -/
noncomputable def eventAtom (e : ℕ) : Sentence :=
  match e.unpair.1 with
  | 0 => haltingClaimSentence e.unpair.2
  | 1 => ∼haltingClaimSentence e.unpair.2
  | 2 => boundedHaltingClaimSentence e.unpair.2
  | 3 => ∼boundedHaltingClaimSentence e.unpair.2
  | 4 => quoteAtom e.unpair.2
  | 5 => ∼quoteAtom e.unpair.2
  | _ => ⊤

/-- The provability obligation an event fires on. -/
def eventFires (e : ℕ) : Prop :=
  match e.unpair.1 with
  | 0 => T ⊢ universalHaltingSchema/[↑e.unpair.2]
  | 1 => T ⊢ ∼(universalHaltingSchema/[↑e.unpair.2])
  | 2 => T ⊢ universalBoundedHaltingSchema/[↑e.unpair.2]
  | 3 => T ⊢ ∼(universalBoundedHaltingSchema/[↑e.unpair.2])
  | 4 => T ⊢ universalQuotePos/[↑e.unpair.2]
  | 5 => T ⊢ universalQuoteNeg/[↑e.unpair.2]
  | _ => False

/-- `eventFires` is a six-way disjunction of a primitive-recursive tag test with
provability of a fixed schema instance; substitution commutes with negation, so the two
refutation tags are schema instances too, and the whole predicate is r.e. -/
lemma eventFires_re [T.Δ₁] :
    REPred (eventFires T) := by
  have key : eventFires T = fun e =>
      (e.unpair.1 = 0 ∧ T ⊢ universalHaltingSchema/[↑e.unpair.2]) ∨
      (e.unpair.1 = 1 ∧ T ⊢ ∼(universalHaltingSchema/[↑e.unpair.2])) ∨
      (e.unpair.1 = 2 ∧ T ⊢ universalBoundedHaltingSchema/[↑e.unpair.2]) ∨
      (e.unpair.1 = 3 ∧ T ⊢ ∼(universalBoundedHaltingSchema/[↑e.unpair.2])) ∨
      (e.unpair.1 = 4 ∧ T ⊢ universalQuotePos/[↑e.unpair.2]) ∨
      (e.unpair.1 = 5 ∧ T ⊢ universalQuoteNeg/[↑e.unpair.2]) := by
    funext e
    rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | n <;>
      simp [eventFires, h]
  rw [key]
  -- Each conjunct is (computable tag-equality) ∧ (r.e. provability of a schema instance).
  have htag : ∀ k : ℕ, REPred (fun e : ℕ => e.unpair.1 = k) := by
    intro k
    have hp : PrimrecPred (fun e : ℕ => e.unpair.1 = k) :=
      Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const k)
    exact ComputablePred.to_re hp.computablePred
  have hsub : ∀ (φ : ArithmeticSemisentence 1),
      REPred (fun e : ℕ => T ⊢ φ/[↑e.unpair.2]) := fun φ =>
    REPred.comp (Primrec.snd.comp Primrec.unpair).to_comp (provable_instances_re T φ)
  have hnegsub :
      REPred (fun e : ℕ => T ⊢ ∼(universalHaltingSchema/[↑e.unpair.2])) := by
    have h := hsub (∼universalHaltingSchema)
    simp only [LogicalConnective.HomClass.map_neg] at h
    exact h
  have hnegbounded :
      REPred (fun e : ℕ => T ⊢ ∼(universalBoundedHaltingSchema/[↑e.unpair.2])) := by
    have h := hsub (∼universalBoundedHaltingSchema)
    simp only [LogicalConnective.HomClass.map_neg] at h
    exact h
  refine ((htag 0).and (hsub _)).or (((htag 1).and hnegsub).or
    (((htag 2).and (hsub _)).or (((htag 3).and hnegbounded).or
      (((htag 4).and (hsub _)).or ((htag 5).and (hsub _))))))

/-- A partial-recursive semi-decider for `eventFires`: `code.eval e` halts iff `e` fires. -/
lemma exists_eventCode [T.Δ₁] :
    ∃ code : Nat.Partrec.Code, ∀ e, (code.eval e).Dom ↔ eventFires T e := by
  obtain ⟨f, hf, hfP⟩ := REPred.iff'.mp (eventFires_re T)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (hf.map (Computable.const (0 : ℕ)).to₂))
  refine ⟨code, fun e => ?_⟩
  rw [hcode]
  exact (hfP e).symm

/-! ## The deductive process -/

open Classical in
/-- Fuel-`k` dovetailer: the atoms of every event `e ≤ k` whose semi-decider halts within `k`
interpreter steps.  Monotone in `k` by `evaln`-monotonicity. -/
noncomputable def theoremStage (code : Nat.Partrec.Code) (k : ℕ) : Finset Sentence :=
  ((Finset.range (k + 1)).filter (fun e => (Nat.Partrec.Code.evaln k code e).isSome = true)).image
    eventAtom

lemma theoremStage_mono (code : Nat.Partrec.Code) (k : ℕ) :
    theoremStage code k ⊆ theoremStage code (k + 1) := by
  classical
  intro φ hφ
  simp only [theoremStage, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hφ ⊢
  obtain ⟨e, ⟨he, hsome⟩, rfl⟩ := hφ
  exact ⟨e, ⟨by omega, evaln_isSome_mono (Nat.le_succ k) hsome⟩, rfl⟩

/-- The constructed deductive process enumerating the `T`-provable computation literals. -/
noncomputable def theoremDP [T.Δ₁] : DeductiveProcess where
  D := theoremStage (exists_eventCode T).choose
  mono := theoremStage_mono _

/-- Coverage: every fired event's atom eventually appears in a stage. -/
lemma theoremDP_covers [T.Δ₁]
    {e : ℕ} (he : eventFires T e) :
    ∃ k, eventAtom e ∈ (theoremDP T).D k := by
  classical
  have hspec := (exists_eventCode T).choose_spec
  set code := (exists_eventCode T).choose with hc
  have hdom : (code.eval e).Dom := (hspec e).mpr he
  obtain ⟨out, hout⟩ := Part.dom_iff_mem.mp hdom
  obtain ⟨fuel, hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hout
  refine ⟨max e fuel, ?_⟩
  simp only [theoremDP, theoremStage, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  refine ⟨e, ⟨by omega, ?_⟩, rfl⟩
  exact evaln_isSome_mono (le_max_right e fuel)
    (Option.isSome_iff_exists.mpr ⟨out, hfuel⟩)

/-! ## Non-vacuity: a consistent world for every stage

The world reads each atom's `kind` code off its Gödel name and believes it iff the
corresponding schema instance is `T`-provable (consistency atoms are disbelieved).  Every
refutation tag fires on the *literal negation* of the sentence its positive partner fires
on, so **consistency of `T` alone** keeps this fixed world consistent with every stage; no
semantic hypothesis on `T` appears. -/

/-- The provability world: an atom is believed iff its claim kind is a "positive" kind and
the associated halting schema instance is `T`-provable. -/
noncomputable def provabilityWorld : PCWorld := fun m =>
  if m.unpair.1 = ComputationClaimKind.halting.godelCode then
    T ⊢ universalHaltingSchema/[↑m.unpair.2.unpair.2]
  else if m.unpair.1 = ComputationClaimKind.boundedHalting.godelCode then
    T ⊢ universalBoundedHaltingSchema/[↑m.unpair.2.unpair.2]
  else if m.unpair.1 = 2 then
    -- Atom payload tag `2` is the quotation claims (allocation table at
    -- `ComputationClaimKind.godelCode`); believe one iff the positive folded universal
    -- schema is provable.
    T ⊢ universalQuotePos/[↑m.unpair.2.unpair.2.unpair.2]
  else False

-- Atom and negation normalisation is wanted throughout the deductive-process lane; the
-- laws themselves are `Framework/Criterion.lean`'s.
attribute [simp] PCWorld.holds_atom PCWorld.holds_neg

@[simp] lemma provabilityWorld_halting (z : ℕ) :
    (provabilityWorld T) ((haltingClaim z).godelCode) ↔ T ⊢ universalHaltingSchema/[↑z] := by
  simp [provabilityWorld, haltingClaim, ComputationClaim.godelCode,
    ComputationClaimKind.godelCode, Nat.unpair_pair]

@[simp] lemma provabilityWorld_boundedHalting (z : ℕ) :
    (provabilityWorld T) ((boundedHaltingClaim z).godelCode) ↔
      T ⊢ universalBoundedHaltingSchema/[↑z] := by
  simp [provabilityWorld, boundedHaltingClaim, ComputationClaim.godelCode,
    ComputationClaimKind.godelCode, Nat.unpair_pair]

@[simp] lemma provabilityWorld_quote (w : ℕ) :
    (provabilityWorld T) (quotationClaimCode universalQuotePos universalQuoteNeg w) ↔
      T ⊢ universalQuotePos/[↑w] := by
  simp [provabilityWorld, quotationClaimCode, ComputationClaimKind.godelCode, Nat.unpair_pair]

/-- **Non-vacuity (`hworld`).** The provability world is consistent with every stage. -/
lemma theoremDP_hworld [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] (n : ℕ) :
    (provabilityWorld T).ConsistentWith ((theoremDP T).D n) := by
  classical
  intro φ hφ
  simp only [theoremDP, theoremStage, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range] at hφ
  obtain ⟨e, ⟨-, hsome⟩, rfl⟩ := hφ
  have hfires : eventFires T e := by
    obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hsome
    exact ((exists_eventCode T).choose_spec e).mp
      (Part.dom_iff_mem.mpr ⟨out, Nat.Partrec.Code.evaln_sound hout⟩)
  -- Case on the event tag.
  rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | m
  · -- tag 0: positive halting
    simp only [eventFires, h] at hfires
    simpa only [eventAtom, h, haltingClaimSentence, computationClaimSentence, PCWorld.holds_atom,
      provabilityWorld_halting] using hfires
  · -- tag 1: ∼halting, ruled out by consistency of `T`
    simp only [eventFires, h] at hfires
    simp only [eventAtom, h, haltingClaimSentence, computationClaimSentence, PCWorld.holds_neg,
      PCWorld.holds_atom, provabilityWorld_halting]
    intro hpos
    exact (Entailment.Consistent.not_bot (𝓢 := T) inferInstance) (by cl_prover [hpos, hfires])
  · -- tag 2: positive bounded halting
    simp only [eventFires, h] at hfires
    simpa only [eventAtom, h, boundedHaltingClaimSentence, computationClaimSentence, PCWorld.holds_atom,
      provabilityWorld_boundedHalting] using hfires
  · -- tag 3: ∼bounded halting, ruled out by consistency of `T`
    simp only [eventFires, h] at hfires
    simp only [eventAtom, h, boundedHaltingClaimSentence, computationClaimSentence, PCWorld.holds_neg,
      PCWorld.holds_atom, provabilityWorld_boundedHalting]
    intro hbh
    exact (Entailment.Consistent.not_bot (𝓢 := T) inferInstance) (by cl_prover [hbh, hfires])
  · -- tag 4: positive quotation
    simp only [eventFires, h] at hfires
    simpa only [eventAtom, h, quoteAtom, quotationClaimSentence, PCWorld.holds_atom,
      provabilityWorld_quote] using hfires
  · -- tag 5: ∼quotation, ruled out by consistency — the positive and negative quotation
    -- schemas are the value-`1` and value-`0` fibers of ONE code formula, and `T` itself
    -- refutes their conjunction (`universalQuote_exclusive_prov`); no soundness is used.
    simp only [eventFires, h] at hfires
    simp only [eventAtom, h, quoteAtom, quotationClaimSentence, PCWorld.holds_neg,
      PCWorld.holds_atom, provabilityWorld_quote]
    intro hpos
    have hexc := universalQuote_exclusive_prov T e.unpair.2
    exact (Entailment.Consistent.not_bot (𝓢 := T) inferInstance)
      (by cl_prover [hpos, hfires, hexc])
  · -- default tag: atom is ⊤, always held
    simp only [eventAtom, h]
    show LO.Propositional.Formula.Boolean.val (provabilityWorld T) ⊤
    simp [LO.Propositional.Formula.Boolean.val]

/-! ## Computability of the stage enumerator

The stage function is a total fuel-clocked computation; its encoding is primitive recursive
in the stage index.  Isolating this mechanical obligation keeps the epistemic content above
fully proved. -/

/-! ### The atom encoder is primitive recursive -/

lemma encode_atom (m : ℕ) :
    Encodable.encode (Formula.atom m : Sentence) = Nat.pair 1 m + 1 := rfl

lemma encode_negAtom (m : ℕ) :
    Encodable.encode (∼(Formula.atom m) : Sentence) =
      Nat.pair 2 (Nat.pair (Nat.pair 1 m + 1) (Nat.pair 0 0 + 1)) + 1 := rfl

lemma encode_top :
    Encodable.encode (⊤ : Sentence) =
      Nat.pair 2 (Nat.pair (Nat.pair 0 0 + 1) (Nat.pair 0 0 + 1)) + 1 := rfl

/-- `eventAtom` is primitive recursive (its Gödel code is a bounded case split over the tag
into fixed pairings of the fixed schema constants). -/
lemma eventAtom_prim : Primrec (fun e : ℕ => eventAtom e) := by
  apply Primrec.encode_iff.mp
  have hz : Primrec (fun e : ℕ => e.unpair.2) := Primrec.snd.comp Primrec.unpair
  have htag : Primrec (fun e : ℕ => e.unpair.1) := Primrec.fst.comp Primrec.unpair
  set KH := Encodable.encode universalHaltingSchema with hKH
  set KBH := Encodable.encode universalBoundedHaltingSchema with hKBH
  set KnH := Encodable.encode (∼universalHaltingSchema : ArithmeticSemisentence 1) with hKnH
  set KQP := Encodable.encode universalQuotePos with hKQP
  set KQN := Encodable.encode universalQuoteNeg with hKQN
  -- Gödel-code builders `Nat.pair kind (Nat.pair schema z)`.
  have gc : ∀ k S : ℕ, Primrec (fun e : ℕ => Nat.pair k (Nat.pair S e.unpair.2)) := fun k S =>
    Primrec₂.natPair.comp (Primrec.const k) (Primrec₂.natPair.comp (Primrec.const S) hz)
  -- Quotation Gödel-code builder `Nat.pair 2 (Nat.pair Kpos (Nat.pair Kneg z))`
  -- (payload tag `2`; the `tagEq 4`/`tagEq 5` below are *event* tags).
  have gcQuote : Primrec (fun e : ℕ => Nat.pair 2 (Nat.pair KQP (Nat.pair KQN e.unpair.2))) :=
    Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const KQP)
        (Primrec₂.natPair.comp (Primrec.const KQN) hz))
  -- Positive/negated atom encoders from a Gödel-code function.
  have encA : ∀ {g : ℕ → ℕ}, Primrec g → Primrec (fun e => Nat.pair 1 (g e) + 1) :=
    fun hg => Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) hg)
  have encN : ∀ {g : ℕ → ℕ}, Primrec g →
      Primrec (fun e => Nat.pair 2 (Nat.pair (Nat.pair 1 (g e) + 1) (Nat.pair 0 0 + 1)) + 1) :=
    fun hg => Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) hg))
        (Primrec.const (Nat.pair 0 0 + 1))))
  have tagEq : ∀ k : ℕ, PrimrecPred (fun e : ℕ => e.unpair.1 = k) := fun k =>
    Primrec.eq.comp htag (Primrec.const k)
  refine (Primrec.ite (tagEq 0) (encA (gc 0 KH))
    (Primrec.ite (tagEq 1) (encN (gc 0 KH))
    (Primrec.ite (tagEq 2) (encA (gc 1 KBH))
    (Primrec.ite (tagEq 3) (encN (gc 1 KBH))
    (Primrec.ite (tagEq 4) (encA gcQuote)
    (Primrec.ite (tagEq 5) (encN gcQuote)
    (Primrec.const
      (Nat.pair 2 (Nat.pair (Nat.pair 0 0 + 1) (Nat.pair 0 0 + 1)) + 1)))))))).of_eq ?_
  intro e
  rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | m
  · simp [h, eventAtom, haltingClaimSentence, computationClaimSentence, haltingClaim,
      ComputationClaim.godelCode, ComputationClaimKind.godelCode, encode_atom, hKH]
  · simp [h, eventAtom, haltingClaimSentence, computationClaimSentence, haltingClaim,
      ComputationClaim.godelCode, ComputationClaimKind.godelCode, encode_negAtom, hKH]
  · simp [h, eventAtom, boundedHaltingClaimSentence, computationClaimSentence,
      boundedHaltingClaim, ComputationClaim.godelCode, ComputationClaimKind.godelCode,
      encode_atom, hKBH]
  · simp [h, eventAtom, boundedHaltingClaimSentence, computationClaimSentence,
      boundedHaltingClaim, ComputationClaim.godelCode, ComputationClaimKind.godelCode,
      encode_negAtom, hKBH]
  · simp [h, eventAtom, quoteAtom, quotationClaimSentence, quotationClaimCode,
      encode_atom, hKQP, hKQN]
  · simp [h, eventAtom, quoteAtom, quotationClaimSentence, quotationClaimCode,
      encode_negAtom, hKQP, hKQN]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
    simp [eventAtom, h, encode_top]

/-! ### Assembling the computation -/

lemma theoremStage_eq_toFinset (c : Nat.Partrec.Code) (n : ℕ) :
    theoremStage c n =
      ((List.range (n + 1)).filterMap
        (fun e => if (Nat.Partrec.Code.evaln n c e).isSome = true then some (eventAtom e)
          else none)).toFinset := by
  classical
  ext φ
  simp only [theoremStage, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
    List.mem_toFinset, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨e, ⟨he, hsome⟩, rfl⟩
    exact ⟨e, he, by rw [if_pos hsome]⟩
  · rintro ⟨e, he, hcond⟩
    by_cases hs : (Nat.Partrec.Code.evaln n c e).isSome = true
    · rw [if_pos hs] at hcond
      exact ⟨e, ⟨he, hs⟩, Option.some_inj.mp hcond⟩
    · rw [if_neg hs] at hcond; exact absurd hcond (by simp)

lemma theoremStage_encode_prim (c : Nat.Partrec.Code) :
    Primrec (fun n => Encodable.encode (theoremStage c n)) := by
  -- The fuel-clocked dovetail list is primrec.
  have hevaln : Primrec (fun p : ℕ × ℕ =>
      (Nat.Partrec.Code.evaln p.1 c p.2).isSome) :=
    Primrec.option_isSome.comp
      (Nat.Partrec.Code.primrec_evaln.comp
        ((Primrec.fst.pair (Primrec.const c)).pair Primrec.snd))
  have hguncur : Primrec (fun p : ℕ × ℕ =>
      if (Nat.Partrec.Code.evaln p.1 c p.2).isSome = true then some (eventAtom p.2)
        else (none : Option Sentence)) := by
    have hb : Primrec (fun p : ℕ × ℕ =>
        bif (Nat.Partrec.Code.evaln p.1 c p.2).isSome then some (eventAtom p.2)
          else (none : Option Sentence)) :=
      Primrec.cond hevaln (Primrec.option_some.comp (eventAtom_prim.comp Primrec.snd))
        (Primrec.const (none : Option Sentence))
    exact hb.of_eq (fun p => by
      cases (Nat.Partrec.Code.evaln p.1 c p.2).isSome <;> simp)
  have hlist : Primrec (fun n : ℕ => (List.range (n + 1)).filterMap
      (fun e => if (Nat.Partrec.Code.evaln n c e).isSome = true then some (eventAtom e)
        else none)) :=
    Primrec.listFilterMap (Primrec.list_range.comp Primrec.succ) hguncur.to₂
  have hkey : (fun n => Encodable.encode (theoremStage c n)) =
      (fun n => Encodable.encode
        ((sentenceDedup ((List.range (n + 1)).filterMap
          (fun e => if (Nat.Partrec.Code.evaln n c e).isSome = true then some (eventAtom e)
            else none))).insertionSort sentenceCodeLE)) := by
    funext n; rw [theoremStage_eq_toFinset, encode_toFinset_eq]
  rw [hkey]
  exact Primrec.encode.comp (sentenceInsertionSort_prim.comp (sentenceDedup_prim.comp hlist))

/-- The provability deductive process is computable: one fixed partial-recursive program
emits the encoded stage `D n` on input `n`. -/
lemma theoremDP_computable [T.Δ₁] :
    ComputableDeductiveProcess (theoremDP T) := by
  let eventCode := (exists_eventCode T).choose
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp (theoremStage_encode_prim eventCode)))
  refine ⟨code, fun n => ?_⟩
  rw [hcode]
  exact Part.mem_some _

/-! ## The presentations -/

/-- **The constructed computation presentation.**  All four enters/refutes obligations are
discharged by coverage of the provability enumeration. -/
noncomputable def theoremPresentation [T.Δ₁] :
    ComputationTheoryPresentation (theoremDP T) T where
  theory_deltaOne := inferInstance
  process := (theoremDP_computable T).nonemptyComputation.some
  halting_enters z hz := by
    have : eventFires T (Nat.pair 0 z) := by simp only [eventFires, Nat.unpair_pair]; exact hz
    obtain ⟨k, hk⟩ := theoremDP_covers T this
    exact ⟨k, by simpa only [eventAtom, Nat.unpair_pair] using hk⟩
  halting_refutes z hz := by
    have : eventFires T (Nat.pair 1 z) := by simp only [eventFires, Nat.unpair_pair]; exact hz
    obtain ⟨k, hk⟩ := theoremDP_covers T this
    exact ⟨k, by simpa only [eventAtom, Nat.unpair_pair] using hk⟩
  boundedHalting_enters z hz := by
    have : eventFires T (Nat.pair 2 z) := by simp only [eventFires, Nat.unpair_pair]; exact hz
    obtain ⟨k, hk⟩ := theoremDP_covers T this
    exact ⟨k, by simpa only [eventAtom, Nat.unpair_pair] using hk⟩
  boundedFailure_refutes z hz := by
    have : eventFires T (Nat.pair 3 z) := by simp only [eventFires, Nat.unpair_pair]; exact hz
    obtain ⟨k, hk⟩ := theoremDP_covers T this
    exact ⟨k, by simpa only [eventAtom, Nat.unpair_pair] using hk⟩

/-- The constructed quotation presentation.  The same computable provability process
`theoremDP`, whose stages also enumerate the code-indexed quotation atoms on tags 4/5,
inhabits `QuotationTheoryPresentation`.  Together with the proved `theoremDP_hworld` this
supplies the two hypotheses shared by the introspection, self-trust, expectation, and
paradox-resistance endpoints.
Paper node: `thm:ref` -/
noncomputable def quotationPresentation [T.Δ₁] :
    QuotationTheoryPresentation (theoremDP T) T where
  toComputationTheoryPresentation := theoremPresentation T
  quote_positive_enters code input h := by
    have : eventFires T (Nat.pair 4 (Nat.pair code input)) := by
      simp only [eventFires, Nat.unpair_pair]; exact h
    obtain ⟨k, hk⟩ := theoremDP_covers T this
    exact ⟨k, by simpa only [eventAtom, Nat.unpair_pair] using hk⟩
  quote_negative_refutes code input h := by
    have : eventFires T (Nat.pair 5 (Nat.pair code input)) := by
      simp only [eventFires, Nat.unpair_pair]; exact h
    obtain ⟨k, hk⟩ := theoremDP_covers T this
    exact ⟨k, by simpa only [eventAtom, Nat.unpair_pair] using hk⟩

/-- Quotation non-vacuity certificate.  For a consistent `Δ₁` theory `T` interpreting
`𝗣𝗔⁻` there is a deductive process carrying both a `QuotationTheoryPresentation` and the
market non-vacuity hypothesis `hworld`, so the conjunction consumed by every
`_ofCode`/`_ofDiagonal`/`_ofRepresentation` introspection, self-trust, expectation, and
paradox-resistance endpoint is satisfiable.
Code-indexing is what makes such a witness possible: the quotation schemas are fixed
(`universalQuotePos`/`universalQuoteNeg`) with the decision selector folded into the
numeral, so their positive and negative fibers are mutually exclusive and no stage is
forced to contain a literal together with its negation.
Paper node: `thm:ref` -/
theorem quotation_presentation_nonvacuous
    (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] :
    ∃ (DP : DeductiveProcess) (_ : QuotationTheoryPresentation DP T),
      ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) :=
  ⟨theoremDP T, quotationPresentation T,
    fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩⟩

/-! ## The market program of the `LIA` over a computable process

`liaMarketComputation` is the `LIA`'s exact market program over an arbitrary computable
deductive process; the single market's own program, `paperMarketComputation`, is one of its
instances.  `theoremMarketComputation` is the instance at this literal stream, consumed by
`theoremDeferredWeightQuoteCode` (`Construction/Quotation/MarketQuoteCodes.lean`) for the
definitional-extension diagnosis of the `thm:ccee` mesh slack, which keeps this stream as
its base process by ruling. -/

section PeanoMinus
variable [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- A named exact market program for the `LIA` over **any** computable deductive process.
`thm:lia` makes the constructed market a logical inductor over `DP`, and a logical
inductor's market is computable, so the program exists uniformly in `DP`.
Paper node: `thm:lia` -/
noncomputable def liaMarketComputation (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) : MarketComputation (liaHistory DP) :=
  (LIA_is_logical_inductor DP hDP).marketComputable.nonemptyComputation.some

/-- A named exact market program for the `LIA` over the literal stream.  It is the market of
the definitional-extension diagnosis of the `thm:ccee` mesh slack, which keeps that stream
as its base process; the single market's program is `paperMarketComputation`.
Paper node: `thm:lia` -/
noncomputable def theoremMarketComputation :
    MarketComputation (liaHistory (theoremDP T)) :=
  liaMarketComputation (theoremDP T) (theoremDP_computable T)

end PeanoMinus

end LogicalInduction
