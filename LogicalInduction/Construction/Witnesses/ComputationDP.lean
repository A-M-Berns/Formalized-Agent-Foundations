import LogicalInduction.Construction.Witnesses.ComputationSyntax
import LogicalInduction.Construction.Witnesses.ConditioningPresentation
import LogicalInduction.Construction.Witnesses.QuotationAffine
import LogicalInduction.Construction.LIACompiler
import Foundation.FirstOrder.Incompleteness.Halting
-- for `ISigma1_delta1Definable`; not reachable through `Incompleteness.Halting`
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
import LogicalInduction.Framework.WriteOut

/-!
# The provability deductive process and the unconditional `LIA` endpoints

The `_ofComputation` endpoints of `ComputationSyntax.lean` are conditional on a
`ComputationTheoryPresentation DP T`: a computable deductive process whose stages track the
`T`-provable instances of the fixed universal computation schemas.  This file constructs
such a process for a fixed Σ₁-sound `T ⊇ 𝗜𝚺₁`, discharging both the presentation and the
market non-vacuity hypothesis `hworld`, which is *proved* from consistency and Σ₁-soundness
of `T` rather than assumed.  Instantiated at the constructed `LIA` inductor, this leaves the
computational-knowledge endpoints (`thm:halts`, `thm:pac`, `thm:pazfc`, `thm:incons`,
`thm:loops`, `thm:dontwait`) with no market, inductor, presentation, or `hworld` hypothesis.

The same computable process also inhabits the code-indexed `QuotationTheoryPresentation`
(event tags 6/7 enumerate the quotation atoms), so `quotationPresentation` together with
`theoremDP_hworld` exhibit a presentation and a plausible-world family that hold
simultaneously (`quotation_presentation_nonvacuous`).  Because quotation folds a
decidable-decision selector into the numeral of *fixed* universal schemas
(`universalQuotePos`/`universalQuoteNeg`), its instances are enumerable by the same
`provable_instances_re`; the positive and negative fibers are the value-1 and value-0
fibers of one deterministic computation, hence mutually exclusive, which is what keeps
`hworld` consistent on tags 6/7.  The self-reference endpoints (`thm:ref`, `thm:lp`,
`thm:st`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee`) then instantiate over the
same constructed inductor.

The two mechanical obligations behind all of this are discharged here: provability of
schema instances is recursively enumerable, and the fuel-clocked stage enumerator is
primitive recursive.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional
open Filter Topology

/-! ## Provability of schema instances is recursively enumerable -/

open Classical in
/-- For a fixed schema `φ`, provability of its numerical instances in a Δ₁, Σ₁-sound theory
extending `𝗜𝚺₁` is recursively enumerable.  Mirrors the positive-path assembly inside FFL's
`incomplete_of_REPred_not_ComputablePred_Nat'`. -/
lemma provable_instances_re (T : ArithmeticTheory) [T.Δ₁]
    (φ : ArithmeticSemisentence 1) :
    REPred (fun z : ℕ => T ⊢ φ/[↑z]) := by
  have hsig : 𝚺₁-Predicate fun b : ℕ ↦
      Bootstrapping.Provable T (Bootstrapping.subst ℒₒᵣ ?[Bootstrapping.Arithmetic.numeral b] ⌜φ⌝) := by
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

An *event* is a code `e = ⟨tag, z⟩` with `tag ∈ {0,…,7}` selecting one of the eight
enters/refutes obligations (six computation tags 0–5, two quotation tags 6–7) and `z` its
input (for quotation, `z = ⟨code, input⟩`).  A single r.e. predicate `Fires` and a single
atom map `atom` capture all eight; the deductive process enumerates the fired atoms. -/

variable (T : ArithmeticTheory)

/-- The public literal an event contributes to the deductive process. -/
noncomputable def eventAtom (e : ℕ) : Sentence :=
  match e.unpair.1 with
  | 0 => haltingClaimSentence e.unpair.2
  | 1 => ∼haltingClaimSentence e.unpair.2
  | 2 => boundedHaltingClaimSentence e.unpair.2
  | 3 => ∼boundedHaltingClaimSentence e.unpair.2
  | 4 => inconsistencyClaimSentence e.unpair.2
  | 5 => ∼consistencyClaimSentence e.unpair.2
  | 6 => quoteAtom e.unpair.2
  | 7 => ∼quoteAtom e.unpair.2
  | _ => ⊤

/-- The provability obligation an event fires on. -/
def eventFires (e : ℕ) : Prop :=
  match e.unpair.1 with
  | 0 => T ⊢ universalHaltingSchema/[↑e.unpair.2]
  | 1 => T ⊢ ∼(universalHaltingSchema/[↑e.unpair.2])
  | 2 => T ⊢ universalBoundedHaltingSchema/[↑e.unpair.2]
  | 3 => T ⊢ ∼(universalBoundedHaltingSchema/[↑e.unpair.2])
  | 4 => T ⊢ universalHaltingSchema/[↑e.unpair.2]
  | 5 => T ⊢ universalHaltingSchema/[↑e.unpair.2]
  | 6 => T ⊢ universalQuotePos/[↑e.unpair.2]
  | 7 => T ⊢ universalQuoteNeg/[↑e.unpair.2]
  | _ => False

/-- Substitution commutes with negation, so the tag-1 obligation is provability of a schema
instance and hence r.e. -/
lemma eventFires_re [T.Δ₁] :
    REPred (eventFires T) := by
  have key : eventFires T = fun e =>
      (e.unpair.1 = 0 ∧ T ⊢ universalHaltingSchema/[↑e.unpair.2]) ∨
      (e.unpair.1 = 1 ∧ T ⊢ ∼(universalHaltingSchema/[↑e.unpair.2])) ∨
      (e.unpair.1 = 2 ∧ T ⊢ universalBoundedHaltingSchema/[↑e.unpair.2]) ∨
      (e.unpair.1 = 3 ∧ T ⊢ ∼(universalBoundedHaltingSchema/[↑e.unpair.2])) ∨
      (e.unpair.1 = 4 ∧ T ⊢ universalHaltingSchema/[↑e.unpair.2]) ∨
      (e.unpair.1 = 5 ∧ T ⊢ universalHaltingSchema/[↑e.unpair.2]) ∨
      (e.unpair.1 = 6 ∧ T ⊢ universalQuotePos/[↑e.unpair.2]) ∨
      (e.unpair.1 = 7 ∧ T ⊢ universalQuoteNeg/[↑e.unpair.2]) := by
    funext e
    rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | _ | _ | n <;>
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
      (((htag 4).and (hsub _)).or (((htag 5).and (hsub _)).or
        (((htag 6).and (hsub _)).or ((htag 7).and (hsub _))))))))

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

/-- Monotonicity of the fuel-clocked semi-decider, in `isSome` form. -/
lemma evaln_isSome_mono {k k' : ℕ} {c : Nat.Partrec.Code} {e : ℕ} (h : k ≤ k')
    (hs : (Nat.Partrec.Code.evaln k c e).isSome) :
    (Nat.Partrec.Code.evaln k' c e).isSome := by
  obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hs
  exact Option.isSome_iff_exists.mpr
    ⟨out, Nat.Partrec.Code.evaln_mono h (Option.mem_def.mpr hout)⟩

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
  else if m.unpair.1 = ComputationClaimKind.inconsistency.godelCode then
    T ⊢ universalHaltingSchema/[↑m.unpair.2.unpair.2]
  else if m.unpair.1 = 4 then
    -- quotation atoms (tag 4): believe iff the positive folded universal schema is provable
    T ⊢ universalQuotePos/[↑m.unpair.2.unpair.2.unpair.2]
  else False

@[simp] lemma holds_atom (v : PCWorld) (m : ℕ) :
    v.Holds (Formula.atom m) ↔ v m := Iff.rfl

@[simp] lemma holds_not (v : PCWorld) (φ : Sentence) :
    v.Holds (∼φ) ↔ ¬ v.Holds φ := by
  show LO.Propositional.Formula.Boolean.val v (∼φ) ↔ ¬ LO.Propositional.Formula.Boolean.val v φ
  exact Semantics.Not.models_not (M := LO.Propositional.Boolean.Valuation ℕ)

@[simp] lemma provabilityWorld_halting (z : ℕ) :
    (provabilityWorld T) ((haltingClaim z).godelCode) ↔ T ⊢ universalHaltingSchema/[↑z] := by
  simp [provabilityWorld, haltingClaim, ComputationClaim.godelCode,
    ComputationClaimKind.godelCode, Nat.unpair_pair]

@[simp] lemma provabilityWorld_boundedHalting (z : ℕ) :
    (provabilityWorld T) ((boundedHaltingClaim z).godelCode) ↔
      T ⊢ universalBoundedHaltingSchema/[↑z] := by
  simp [provabilityWorld, boundedHaltingClaim, ComputationClaim.godelCode,
    ComputationClaimKind.godelCode, Nat.unpair_pair]

@[simp] lemma provabilityWorld_inconsistency (z : ℕ) :
    (provabilityWorld T) ((inconsistencyClaim z).godelCode) ↔
      T ⊢ universalHaltingSchema/[↑z] := by
  simp [provabilityWorld, inconsistencyClaim, ComputationClaim.godelCode,
    ComputationClaimKind.godelCode, Nat.unpair_pair]

@[simp] lemma provabilityWorld_consistency (z : ℕ) :
    (provabilityWorld T) ((consistencyClaim z).godelCode) ↔ False := by
  simp [provabilityWorld, consistencyClaim, ComputationClaim.godelCode,
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
  rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | _ | _ | m
  · -- tag 0: positive halting
    simp only [eventFires, h] at hfires
    simpa only [eventAtom, h, haltingClaimSentence, computationClaimSentence, holds_atom,
      provabilityWorld_halting] using hfires
  · -- tag 1: ∼halting, ruled out by consistency of `T`
    simp only [eventFires, h] at hfires
    simp only [eventAtom, h, haltingClaimSentence, computationClaimSentence, holds_not,
      holds_atom, provabilityWorld_halting]
    intro hpos
    exact (Entailment.Consistent.not_bot (𝓢 := T) inferInstance) (by cl_prover [hpos, hfires])
  · -- tag 2: positive bounded halting
    simp only [eventFires, h] at hfires
    simpa only [eventAtom, h, boundedHaltingClaimSentence, computationClaimSentence, holds_atom,
      provabilityWorld_boundedHalting] using hfires
  · -- tag 3: ∼bounded halting, ruled out by consistency of `T`
    simp only [eventFires, h] at hfires
    simp only [eventAtom, h, boundedHaltingClaimSentence, computationClaimSentence, holds_not,
      holds_atom, provabilityWorld_boundedHalting]
    intro hbh
    exact (Entailment.Consistent.not_bot (𝓢 := T) inferInstance) (by cl_prover [hbh, hfires])
  · -- tag 4: positive inconsistency
    simp only [eventFires, h] at hfires
    simpa only [eventAtom, h, inconsistencyClaimSentence, computationClaimSentence, holds_atom,
      provabilityWorld_inconsistency] using hfires
  · -- tag 5: ∼consistency, always disbelieved
    simp [eventAtom, h, consistencyClaimSentence, computationClaimSentence]
  · -- tag 6: positive quotation
    simp only [eventFires, h] at hfires
    simpa only [eventAtom, h, quoteAtom, quotationClaimSentence, holds_atom,
      provabilityWorld_quote] using hfires
  · -- tag 7: ∼quotation, ruled out by consistency — the positive and negative quotation
    -- schemas are the value-`1` and value-`0` fibers of ONE code formula, and `T` itself
    -- refutes their conjunction (`universalQuote_exclusive_prov`); no soundness is used.
    simp only [eventFires, h] at hfires
    simp only [eventAtom, h, quoteAtom, quotationClaimSentence, holds_not,
      holds_atom, provabilityWorld_quote]
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

/-- A finite sentence set given as a list's `toFinset` has the code of the canonical
sorted, duplicate-free list — the reusable core of `sentenceFinsetUnionNorm_spec`. -/
lemma encode_toFinset_eq (l : List Sentence) :
    Encodable.encode l.toFinset =
      Encodable.encode ((sentenceDedup l).insertionSort sentenceCodeLE) := by
  classical
  let canonical := (sentenceDedup l).insertionSort sentenceCodeLE
  have hnodup : canonical.Nodup :=
    (List.perm_insertionSort sentenceCodeLE _).nodup_iff.mpr (sentenceDedup_nodup l)
  have hsorted : canonical.Pairwise sentenceCodeLE :=
    List.pairwise_insertionSort sentenceCodeLE _
  have htoFinset : canonical.toFinset = l.toFinset := by
    ext φ; simp [canonical, mem_sentenceDedup]
  have hsort : l.toFinset.sort sentenceCodeLE = canonical := by
    rw [← htoFinset]
    exact (List.toFinset_sort (r := sentenceCodeLE) hnodup).mpr hsorted
  rw [encode_eq_encode_stageSort l.toFinset]
  exact congrArg Encodable.encode hsort

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
  -- Quotation Gödel-code builder `Nat.pair 4 (Nat.pair Kpos (Nat.pair Kneg z))`.
  have gcQuote : Primrec (fun e : ℕ => Nat.pair 4 (Nat.pair KQP (Nat.pair KQN e.unpair.2))) :=
    Primrec₂.natPair.comp (Primrec.const 4)
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
    (Primrec.ite (tagEq 4) (encA (gc 2 KH))
    (Primrec.ite (tagEq 5) (encN (gc 3 KnH))
    (Primrec.ite (tagEq 6) (encA gcQuote)
    (Primrec.ite (tagEq 7) (encN gcQuote)
    (Primrec.const
      (Nat.pair 2 (Nat.pair (Nat.pair 0 0 + 1) (Nat.pair 0 0 + 1)) + 1)))))))))).of_eq ?_
  intro e
  rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | _ | _ | m
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
  · simp [h, eventAtom, inconsistencyClaimSentence, computationClaimSentence, inconsistencyClaim,
      ComputationClaim.godelCode, ComputationClaimKind.godelCode, encode_atom, hKH]
  · simp [h, eventAtom, consistencyClaimSentence, computationClaimSentence, consistencyClaim,
      ComputationClaim.godelCode, ComputationClaimKind.godelCode, encode_negAtom, hKnH]
  · simp [h, eventAtom, quoteAtom, quotationClaimSentence, quotationClaimCode,
      encode_atom, hKQP, hKQN]
  · simp [h, eventAtom, quoteAtom, quotationClaimSentence, quotationClaimCode,
      encode_negAtom, hKQP, hKQN]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
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
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp (theoremStage_encode_prim (exists_eventCode T).choose)))
  refine ⟨code, fun n => ?_⟩
  rw [hcode]
  exact Part.mem_some _

/-! ## The presentation and the unconditional LIA endpoint -/

/-- **The constructed computation presentation.**  All six enters/refutes obligations are
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
  inconsistency_enters z hz := by
    have : eventFires T (Nat.pair 4 z) := by simp only [eventFires, Nat.unpair_pair]; exact hz
    obtain ⟨k, hk⟩ := theoremDP_covers T this
    exact ⟨k, by simpa only [eventAtom, Nat.unpair_pair] using hk⟩
  inconsistency_refutesConsistency z hz := by
    have : eventFires T (Nat.pair 5 z) := by simp only [eventFires, Nat.unpair_pair]; exact hz
    obtain ⟨k, hk⟩ := theoremDP_covers T this
    exact ⟨k, by simpa only [eventAtom, Nat.unpair_pair] using hk⟩

/-- The constructed quotation presentation.  The same computable provability process
`theoremDP`, whose stages also enumerate the code-indexed quotation atoms on tags 6/7,
inhabits `QuotationTheoryPresentation`.  Together with the proved `theoremDP_hworld` this
supplies the two hypotheses shared by the introspection, self-trust, expectation, and
paradox-resistance endpoints.
Paper node: `thm:ref` -/
noncomputable def quotationPresentation [T.Δ₁] :
    QuotationTheoryPresentation (theoremDP T) T where
  toComputationTheoryPresentation := theoremPresentation T
  quote_positive_enters code input h := by
    have : eventFires T (Nat.pair 6 (Nat.pair code input)) := by
      simp only [eventFires, Nat.unpair_pair]; exact h
    obtain ⟨k, hk⟩ := theoremDP_covers T this
    exact ⟨k, by simpa only [eventAtom, Nat.unpair_pair] using hk⟩
  quote_negative_refutes code input h := by
    have : eventFires T (Nat.pair 7 (Nat.pair code input)) := by
      simp only [eventFires, Nat.unpair_pair]; exact h
    obtain ⟨k, hk⟩ := theoremDP_covers T this
    exact ⟨k, by simpa only [eventAtom, Nat.unpair_pair] using hk⟩

/-- Quotation non-vacuity certificate (`N+`).  For a Σ₁-sound `T ⊇ 𝗜𝚺₁` there is a deductive
process carrying both a `QuotationTheoryPresentation` and the market non-vacuity hypothesis
`hworld`, so the conjunction consumed by every `_ofCode`/`_ofDiagonal`/`_ofRepresentation`
introspection, self-trust, expectation, and paradox-resistance endpoint is satisfiable.
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

/-! ## Unconditional self-reference and quotation endpoints over the constructed `LIA`

Because `quotationPresentation` inhabits `QuotationTheoryPresentation` over the constructed
computable `theoremDP`, and `theoremDP_hworld` discharges the market non-vacuity, every
`_ofCode`/`_ofDiagonal`/`_ofRepresentation` self-reference endpoint instantiates over
`liaHistory (theoremDP T)` with no market, inductor, presentation, or `hworld` hypothesis
remaining — only the caller's own quoted decision and its reflection data. -/

section PeanoMinus
variable [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- The constructed inductor instance for the provability process, reused (inlined) by every
unconditional quotation endpoint below. -/
private noncomputable abbrev theoremLIA : IsLogicalInductor (liaHistory (theoremDP T)) (theoremDP T) :=
  LIA_is_logical_inductor (theoremDP T) (theoremDP_computable T)

/-- A named exact market program for the `LIA` over **any** computable deductive process.
`thm:lia` makes the constructed market a logical inductor over `DP`, and a logical
inductor's market is computable, so the program exists uniformly in `DP`.
Paper node: `thm:lia` -/
noncomputable def liaMarketComputation (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) : MarketComputation (liaHistory DP) :=
  (LIA_is_logical_inductor DP hDP).marketComputable.nonemptyComputation.some

/-- A named exact market program for the constructed `LIA`, used to derive its canonical
paradox-resistance diagonal without any caller-supplied semantic relation.
Paper node: `thm:lp` -/
noncomputable def theoremMarketComputation :
    MarketComputation (liaHistory (theoremDP T)) :=
  liaMarketComputation (theoremDP T) (theoremDP_computable T)

/-- The canonical public diagonal quote for the constructed `LIA` at threshold `p`.
Paper node: `thm:lp` -/
noncomputable def theoremDiagonalQuoteCode (p : ℚ) :
    ParameterizedDiagonalQuoteCode T
      (diagonalPriceTruth (theoremMarketComputation T) p) :=
  parameterizedDiagonalQuoteCodeOfMarket (theoremMarketComputation T) T p

/-- `thm:epr`, unconditional over `LIA`.
Paper node: `thm:epr` -/
theorem lic_expectations_of_probabilities_ofCode_unconditional
    {value : ℕ → ℚ} (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, liaHistory (theoremDP T) n (φ n) = (value n : ℝ)) :
    (fun n => liaHistory (theoremDP T) n (φ n)) ≈ₙ
      fun n => (q.luv n).expect (liaHistory (theoremDP T)) n :=
  haveI := theoremLIA T
  lic_expectations_of_probabilities_ofCode (quotationPresentation T)
    (liaHistory (theoremDP T)) φ hφ q hexact
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:er`, unconditional over `LIA`.
Paper node: `thm:er` -/
theorem lic_iterated_expectations_ofCode_unconditional
    {value : ℕ → ℚ} (X : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, (X n).expect (liaHistory (theoremDP T)) n = (value n : ℝ)) :
    (fun n => (X n).expect (liaHistory (theoremDP T)) n) ≈ₙ
      fun n => (q.luv n).expect (liaHistory (theoremDP T)) n :=
  haveI := theoremLIA T
  lic_iterated_expectations_ofCode (quotationPresentation T)
    (liaHistory (theoremDP T)) X hX q hexact
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:ref` (introspection), unconditional over `LIA`.
Paper node: `thm:ref` -/
theorem lic_introspection_ofCode_unconditional
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) (a b δ : ℕ → ℚ)
    (lowerFeature : ℕ → EF)
    (hlower : GeneratedRatFeature (liaHistory (theoremDP T)) a lowerFeature)
    (upperFeature : ℕ → EF)
    (hupper : GeneratedRatFeature (liaHistory (theoremDP T)) b upperFeature)
    (hδ : DigitRatCodes δ)
    (hδpos : ∀ n, 0 < δ n)
    (hδzero : Tendsto (fun n ↦ (δ n : ℝ)) atTop (𝓝 0))
    (hab : ∀ n, 0 ≤ a n ∧ a n ≤ 1 ∧ 0 ≤ b n ∧ b n ≤ 1)
    (q : BooleanQuoteCode T (fun n ↦
      (a n : ℝ) < liaHistory (theoremDP T) n (φ n) ∧
        liaHistory (theoremDP T) n (φ n) < (b n : ℝ))) :
    ∃ ε : ℕ → ℚ, (∀ n, 0 < ε n) ∧ Tendsto (fun n ↦ (ε n : ℝ)) atTop (𝓝 0) ∧
      ∀ n,
        (((a n : ℝ) + δ n < liaHistory (theoremDP T) n (φ n) ∧
            liaHistory (theoremDP T) n (φ n) < (b n : ℝ) - δ n) →
          1 - (ε n : ℝ) < liaHistory (theoremDP T) n (q.sentence n)) ∧
        ((¬ ((a n : ℝ) - δ n < liaHistory (theoremDP T) n (φ n) ∧
              liaHistory (theoremDP T) n (φ n) < (b n : ℝ) + δ n)) →
          liaHistory (theoremDP T) n (q.sentence n) < (ε n : ℝ)) :=
  haveI := theoremLIA T
  lic_introspection_ofCode (quotationPresentation T) (liaHistory (theoremDP T))
    φ hφ a b δ lowerFeature hlower upperFeature hupper hδ hδpos hδzero hab q
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:cee` (expected future expectations), unconditional over `LIA`.
Paper node: `thm:cee` -/
theorem lic_expected_future_expectations_ofRepresentation_unconditional
    (f : DeferralFunction)
    (X Y : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X) (hY : LUV.RpnThresholdCodeSeq Y)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      ∃ x, v.ValuesAt (X n) x)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      v.ValuesAt (Y n) ((X n).expect (liaHistory (theoremDP T)) (f n))) :
    (fun n ↦ (X n).expect (liaHistory (theoremDP T)) n) ≈ₙ
      fun n ↦ (Y n).expect (liaHistory (theoremDP T)) n :=
  haveI := theoremLIA T
  lic_expected_future_expectations_ofRepresentation (P := liaHistory (theoremDP T))
    (DP := theoremDP T) f X Y hX hY source_valued reflected
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:ceu` (no expected net update), unconditional over `LIA`.
Paper node: `thm:ceu` -/
theorem lic_no_expected_net_update_ofRepresentation_unconditional
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (Y : ℕ → LUV)
    (hφ : BigSentenceCodes φ) (hY : LUV.RpnThresholdCodeSeq Y)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      v.ValuesAt (Y n) (liaHistory (theoremDP T) (f n) (φ n))) :
    (fun n ↦ liaHistory (theoremDP T) n (φ n)) ≈ₙ
      fun n ↦ (Y n).expect (liaHistory (theoremDP T)) n :=
  haveI := theoremLIA T
  lic_no_expected_net_update_ofRepresentation (P := liaHistory (theoremDP T))
    (DP := theoremDP T) f φ Y hφ hY reflected
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:ccee` (conditional no expected net update), unconditional over `LIA`.
Paper node: `thm:ccee` -/
theorem lic_no_expected_net_update_conditional_ofRepresentation_unconditional
    (f : DeferralFunction)
    (X Z Z' : ℕ → LUV) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat (liaHistory (theoremDP T)) w)
    (hX : LUV.RpnThresholdCodeSeq X) (hZ : LUV.RpnThresholdCodeSeq Z)
    (hZ' : LUV.RpnThresholdCodeSeq Z')
    (slack : ℕ → ℝ) (slack_tendsto : Tendsto slack atTop (𝓝 0))
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      ∃ x, v.ValuesAt (X n) x)
    (left_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      ∀ x, v.ValuesAt (X n) x →
        ∃ z, v.ValuesAt (Z n) z ∧ |z - x * w (f n)| ≤ slack n)
    (right_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      v.ValuesAt (Z' n) ((X n).expect (liaHistory (theoremDP T)) (f n) * w (f n))) :
    (fun n ↦ (Z n).expect (liaHistory (theoremDP T)) n) ≈ₙ
      fun n ↦ (Z' n).expect (liaHistory (theoremDP T)) n :=
  haveI := theoremLIA T
  lic_no_expected_net_update_conditional_ofRepresentation (P := liaHistory (theoremDP T))
    (DP := theoremDP T) f X Z Z' w weight_mem weight_generable hX hZ hZ'
    slack slack_tendsto source_valued left_reflected right_reflected
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:st` (self-trust), unconditional over `LIA`.  The confidence threshold `p` is
P-generable (`def:ece`) against the constructed market, presented by its feature
expression.
Paper node: `thm:st` -/
theorem lic_self_trust_ofRepresentation_unconditional
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (δ p : ℕ → ℚ) (A B : ℕ → LUV)
    (delta_pos : ∀ n, 0 < δ n) (probability_mem : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hφ : BigSentenceCodes φ) (hδ : DigitRatCodes δ)
    (pFeature : ℕ → EF)
    (hp : GeneratedRatFeature (liaHistory (theoremDP T)) p pFeature)
    (hA : LUV.RpnThresholdCodeSeq A) (hB : LUV.RpnThresholdCodeSeq B)
    (confidence_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      v.ValuesAt (B n) (ctsInd (δ n) (liaHistory (theoremDP T) (f n) (φ n)) (p n)))
    (product_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      v.ValuesAt (A n)
        (v.payout (φ n) * ctsInd (δ n) (liaHistory (theoremDP T) (f n) (φ n)) (p n))) :
    (fun n ↦ (A n).expect (liaHistory (theoremDP T)) n) ≳ₙ
      fun n ↦ (p n : ℝ) * (B n).expect (liaHistory (theoremDP T)) n :=
  haveI := theoremLIA T
  lic_self_trust_ofRepresentation (P := liaHistory (theoremDP T)) (DP := theoremDP T)
    f φ δ p A B delta_pos probability_mem hφ hδ pFeature hp hA hB
    confidence_reflected product_reflected
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

end PeanoMinus

/-! ## `thm:lp` sits below `𝗣𝗔⁻`

The paradox-resistance endpoint is the one place on this lane where the diagonal is built,
and Foundation's `parameterized_diagonal₁` is stated over `𝗜𝚺₁`.  Since `𝗜𝚺₁ ⪯ T` implies
`𝗣𝗔⁻ ⪯ T` by instance (`Arithmetic/Schemata.lean`), carrying both would put a redundant pair
in the elaborated signature, so the declaration sits outside the `𝗣𝗔⁻` section above and
recovers the weaker instance in its proof term, where `theoremLIA`/`theoremDP_hworld` need
it.  `omit` cannot do this job: instance search reaches a section variable that is still in
the local context, so the binder has to be out of scope rather than merely unlisted. -/

variable [T.Δ₁] [Entailment.Consistent T]

/-- `thm:lp` (paradox resistance), unconditional over `LIA`.  The named market program,
its self-referential public atom, and the matching FFL parameterized fixed point are all
constructed internally.
`𝗜𝚺₁ ⪯ T` is the one genuinely load-bearing arithmetic strengthening left on this lane: the
diagonal reaches Foundation's `parameterized_diagonal₁`, which is stated over `𝗜𝚺₁`.  It is
carried *in place of* the `[𝗣𝗔⁻ ⪯ T]` of the section above, not beside it — see the section
note.  The elaborated signature therefore carries no redundant pair.
Paper node: `thm:lp` -/
theorem lic_paradox_resistance_ofDiagonal_unconditional [𝗜𝚺₁ ⪯ T]
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (width : ℕ → ℚ) (hwidth : DigitRatCodes width)
    (hwidthPos : ∀ n, 0 < width n)
    (hwidthZero : Tendsto (fun n ↦ (width n : ℝ)) atTop (𝓝 0)) :
    (fun n => liaHistory (theoremDP T) n
      ((theoremDiagonalQuoteCode T p).toBooleanQuoteCode.sentence n)) ≈ₙ
      fun _ => (p : ℝ) :=
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := theoremLIA T
  lic_paradox_resistance_ofDiagonal (quotationPresentation T) (liaHistory (theoremDP T))
    (theoremMarketComputation T) p hp0 hp1 width hwidth hwidthPos hwidthZero
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-! ## The meta-learning lane lives over the paper's own theorem process

Every §4.9–4.10 meta-learning endpoint — `thm:pac`, `thm:pazfc`, `thm:halts`, `thm:loops`,
`thm:dontwait` and `thm:incons` — is stated over `paperTheoryDP` in
`ComputationRepresented.lean`, together with the `loopsTheory` witness for `thm:loops`'s
refutation premise and the `𝗜𝚺₁ ∪ {⊥}` deduction-family witness for `thm:incons`.  Nothing of
that lane remains here. -/

#print axioms provable_instances_re
#print axioms theoremDP_covers
#print axioms theoremDP_hworld
#print axioms theoremPresentation
#print axioms quotationPresentation
#print axioms quotation_presentation_nonvacuous
#print axioms lic_introspection_ofCode_unconditional
#print axioms lic_paradox_resistance_ofDiagonal_unconditional
#print axioms lic_self_trust_ofRepresentation_unconditional
#print axioms lic_expectations_of_probabilities_ofCode_unconditional

end LogicalInduction
