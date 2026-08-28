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
lemma provable_instances_re (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
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
  | 3 => T ⊢ universalBoundedFailureSchema/[↑e.unpair.2]
  | 4 => T ⊢ universalHaltingSchema/[↑e.unpair.2]
  | 5 => T ⊢ universalHaltingSchema/[↑e.unpair.2]
  | 6 => T ⊢ universalQuotePos/[↑e.unpair.2]
  | 7 => T ⊢ universalQuoteNeg/[↑e.unpair.2]
  | _ => False

/-- Substitution commutes with negation, so the tag-1 obligation is provability of a schema
instance and hence r.e. -/
lemma eventFires_re [T.Δ₁] [𝗜𝚺₁ ⪯ T] :
    REPred (eventFires T) := by
  have key : eventFires T = fun e =>
      (e.unpair.1 = 0 ∧ T ⊢ universalHaltingSchema/[↑e.unpair.2]) ∨
      (e.unpair.1 = 1 ∧ T ⊢ ∼(universalHaltingSchema/[↑e.unpair.2])) ∨
      (e.unpair.1 = 2 ∧ T ⊢ universalBoundedHaltingSchema/[↑e.unpair.2]) ∨
      (e.unpair.1 = 3 ∧ T ⊢ universalBoundedFailureSchema/[↑e.unpair.2]) ∨
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
  refine ((htag 0).and (hsub _)).or (((htag 1).and hnegsub).or
    (((htag 2).and (hsub _)).or (((htag 3).and (hsub _)).or
      (((htag 4).and (hsub _)).or (((htag 5).and (hsub _)).or
        (((htag 6).and (hsub _)).or ((htag 7).and (hsub _))))))))

/-- A partial-recursive semi-decider for `eventFires`: `code.eval e` halts iff `e` fires. -/
lemma exists_eventCode [T.Δ₁] [𝗜𝚺₁ ⪯ T] :
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
noncomputable def theoremDP [T.Δ₁] [𝗜𝚺₁ ⪯ T] : DeductiveProcess where
  D := theoremStage (exists_eventCode T).choose
  mono := theoremStage_mono _

/-- Coverage: every fired event's atom eventually appears in a stage. -/
lemma theoremDP_covers [T.Δ₁] [𝗜𝚺₁ ⪯ T]
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
corresponding schema instance is `T`-provable (consistency atoms are disbelieved).  Because
`T` is consistent and Σ₁-sound, no stage ever contains both a literal and its negation, so
this fixed world is consistent with every stage. -/

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
lemma theoremDP_hworld [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (n : ℕ) :
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
  · -- tag 3: ∼bounded halting, via Σ₁-soundness and determinism of the horizon term
    simp only [eventFires, h] at hfires
    simp only [eventAtom, h, boundedHaltingClaimSentence, computationClaimSentence, holds_not,
      holds_atom, provabilityWorld_boundedHalting]
    intro hbh
    exact universalBoundedClaims_exclusive e.unpair.2
      ⟨(re_complete (T := T) universalBoundedHalts_re).mpr hbh,
        (re_complete (T := T) universalBoundedFailure_re).mpr hfires⟩
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
  · -- tag 7: ∼quotation, ruled out by determinism (positive/negative fibers are exclusive)
    simp only [eventFires, h] at hfires
    simp only [eventAtom, h, quoteAtom, quotationClaimSentence, holds_not,
      holds_atom, provabilityWorld_quote]
    intro hpos
    have hp : quotePos e.unpair.2.unpair.1 e.unpair.2.unpair.2 :=
      (re_complete (T := T) universalQuotePos_re (x := e.unpair.2)).mpr hpos
    have hn : quoteNeg e.unpair.2.unpair.1 e.unpair.2.unpair.2 :=
      (re_complete (T := T) universalQuoteNeg_re (x := e.unpair.2)).mpr hfires
    exact quotePos_quoteNeg_exclusive _ _ ⟨hp, hn⟩
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
lemma theoremDP_computable [T.Δ₁] [𝗜𝚺₁ ⪯ T] :
    ComputableDeductiveProcess (theoremDP T) := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp (theoremStage_encode_prim (exists_eventCode T).choose)))
  refine ⟨code, fun n => ?_⟩
  rw [hcode]
  exact Part.mem_some _

/-! ## The presentation and the unconditional LIA endpoint -/

/-- **The constructed computation presentation.**  All six enters/refutes obligations are
discharged by coverage of the provability enumeration. -/
noncomputable def theoremPresentation [T.Δ₁] [𝗜𝚺₁ ⪯ T] :
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
noncomputable def quotationPresentation [T.Δ₁] [𝗜𝚺₁ ⪯ T] :
    QuotationTheoryPresentation (theoremDP T) T where
  toComputationTheoryPresentation := theoremPresentation T
  theory_sigmaOne := inferInstance
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
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ (DP : DeductiveProcess) (_ : QuotationTheoryPresentation DP T),
      ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) :=
  ⟨theoremDP T, quotationPresentation T,
    fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩⟩

/-- For a Σ₁-sound theory `T ⊇ 𝗜𝚺₁`, the constructed `LIA` inductor over the constructed
provability deductive process learns every halting pattern.  The deductive process is
constructed and proved computable and the market non-vacuity `hworld` is proved, so no
hypothesis remains beyond the theory instances and the (true) hypothesis that the machines
halt.

`hm` and `hi` are the paper's own e.c. classes, metered by *write-out*: tex:1931-1933 asks
that the source of `mₙ` be writable in time polynomial in `n`, and a poly-time writer emits
polynomially many symbols, so an `n`-digit description with an exponential Gödel code is
admissible and `⟨x⟩` is a sequence of bitstrings.  Strictly wider than the whole-value pair
this once took — see `digitMachineCodes_nest_not_polyMachineCodes` and
`bigDigits_two_pow_not_polyNatCodes`.
Paper node: `thm:halts` -/
theorem lia_learns_halting_patterns_unconditional
    (T : ArithmeticTheory) [𝗥₀ ⪯ T] [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hhalts : ∀ n, CodeHalts (machines n) (inputs n)) :
    (fun n => liaHistory (theoremDP T) n
      ((representedHaltingClaims (theoremPresentation T) machines inputs hm hi).sentence n))
        ≈ₙ fun _ => 1 :=
  haveI : IsLogicalInductor (liaHistory (theoremDP T)) (theoremDP T) :=
    LIA_is_logical_inductor (theoremDP T) (theoremDP_computable T)
  lic_learns_halting_patterns_ofComputation (theoremPresentation T) (liaHistory (theoremDP T))
    machines inputs hm hi hhalts
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-! ## Unconditional self-reference and quotation endpoints over the constructed `LIA`

Because `quotationPresentation` inhabits `QuotationTheoryPresentation` over the constructed
computable `theoremDP`, and `theoremDP_hworld` discharges the market non-vacuity, every
`_ofCode`/`_ofDiagonal`/`_ofRepresentation` self-reference endpoint instantiates over
`liaHistory (theoremDP T)` with no market, inductor, presentation, or `hworld` hypothesis
remaining — only the caller's own quoted decision and its reflection data. -/

variable [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

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

/-- `thm:lp` (paradox resistance), unconditional over `LIA`.  The named market program,
its self-referential public atom, and the matching FFL parameterized fixed point are all
constructed internally.
Paper node: `thm:lp` -/
theorem lic_paradox_resistance_ofDiagonal_unconditional
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (width : ℕ → ℚ) (hwidth : DigitRatCodes width)
    (hwidthPos : ∀ n, 0 < width n)
    (hwidthZero : Tendsto (fun n ↦ (width n : ℝ)) atTop (𝓝 0)) :
    (fun n => liaHistory (theoremDP T) n
      ((theoremDiagonalQuoteCode T p).toBooleanQuoteCode.sentence n)) ≈ₙ
      fun _ => (p : ℝ) :=
  haveI := theoremLIA T
  lic_paradox_resistance_ofDiagonal (quotationPresentation T) (liaHistory (theoremDP T))
    (theoremMarketComputation T) p hp0 hp1 width hwidth hwidthPos hwidthZero
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

/-! ## Unconditional meta-learning siblings over the constructed `LIA`

The other five `_ofComputation` meta-learning endpoints instantiate over `liaHistory
(theoremDP T)` exactly like `lia_learns_halting_patterns_unconditional`, reusing
`theoremPresentation` + `theoremDP_hworld`. Only the caller's concrete computation and the
(true) hypothesis about it remain. -/

/-- `thm:pac`, unconditional over `LIA`, at the paper's horizon class: `C`'s step budget is
any computable `f`, named by its program and evaluated by the arithmetic schema rather than
by the sentence emitter.
Paper node: `thm:pac` -/
theorem lic_belief_finitistic_consistency_unconditional [𝗥₀ ⪯ T]
    (consistentWithin : ℕ → Prop) (C : BoundedComputation consistentWithin)
    (hconsistent : ∀ n, consistentWithin n) :
    (fun n => liaHistory (theoremDP T) n
      ((representedDecidableClaimsOfComputation (theoremPresentation T) C).sentence n))
        ≈ₙ fun _ => 1 :=
  haveI := theoremLIA T
  lic_belief_finitistic_consistency_ofComputation (theoremPresentation T)
    (liaHistory (theoremDP T)) consistentWithin C hconsistent
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:pazfc`, unconditional over `LIA`, at the same arbitrary-computable-horizon class
as `thm:pac`.
Paper node: `thm:pazfc` -/
theorem lic_belief_stronger_theory_consistency_unconditional [𝗥₀ ⪯ T]
    (strongerConsistentWithin : ℕ → Prop)
    (C : BoundedComputation strongerConsistentWithin)
    (hconsistent : ∀ n, strongerConsistentWithin n) :
    (fun n => liaHistory (theoremDP T) n
      ((representedDecidableClaimsOfComputation (theoremPresentation T) C).sentence n))
        ≈ₙ fun _ => 1 :=
  haveI := theoremLIA T
  lic_belief_stronger_theory_consistency_ofComputation (theoremPresentation T)
    (liaHistory (theoremDP T)) strongerConsistentWithin C hconsistent
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:incons`, unconditional over `LIA`.
Paper node: `thm:incons` -/
theorem lic_disbelief_inconsistent_theories_unconditional [𝗥₀ ⪯ T]
    (inconsistent : ℕ → Prop) (C : SemidecidableComputation inconsistent)
    (hall : ∀ n, inconsistent n) :
    ((fun n => liaHistory (theoremDP T) n
        ((inconsistentTheoryClaimsOfComputation (theoremPresentation T) C).inconsistencySentence n))
          ≈ₙ fun _ => 1) ∧
      ((fun n => liaHistory (theoremDP T) n
        ((inconsistentTheoryClaimsOfComputation (theoremPresentation T) C).consistencySentence n))
          ≈ₙ fun _ => 0) :=
  haveI := theoremLIA T
  lic_disbelief_inconsistent_theories_ofComputation (theoremPresentation T)
    (liaHistory (theoremDP T)) inconsistent C hall
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:loops`, unconditional over `LIA`.  `hm` and `hi` are the write-out metered classes
shared with `thm:halts`, strictly wider than the whole-value pair they replaced.
Paper node: `thm:loops` -/
theorem lic_learns_provable_nonhalting_patterns_unconditional [𝗥₀ ⪯ T]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hloops : ∀ n, T ⊢ ∼(universalHaltingSchema/[
      ↑(haltingClaimInput (machines n) (inputs n))])) :
    (fun n => liaHistory (theoremDP T) n
      ((representedHaltingClaims (theoremPresentation T) machines inputs hm hi).sentence n))
        ≈ₙ fun _ => 0 :=
  haveI := theoremLIA T
  lic_learns_provable_nonhalting_patterns_ofComputation (theoremPresentation T)
    (liaHistory (theoremDP T)) machines inputs hm hi hloops
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:dontwait`, unconditional over `LIA`.  `hh` supplies the horizon program for an
arbitrary computable `f` — no growth bound — which is the paper's own quantifier, and `hm`
and `hi` are the write-out metered machine/input classes, which is the paper's e.c. sequence
of bitstrings `⟨y⟩` (tex:1946-1952).  The three are independent hypotheses of one signature.
Paper node: `thm:dontwait` -/
theorem lic_does_not_anticipate_halting_unconditional [𝗥₀ ⪯ T]
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hh : ComputableHorizon horizons)
    (hnever : ∀ n, ¬CodeHalts (machines n) (inputs n)) :
    (fun n => liaHistory (theoremDP T) n
      ((representedBoundedHaltingClaims (theoremPresentation T) machines inputs horizons hm hi hh).sentence n))
        ≈ₙ fun _ => 0 :=
  haveI := theoremLIA T
  lic_does_not_anticipate_halting_ofComputation (theoremPresentation T)
    (liaHistory (theoremDP T)) machines inputs horizons hm hi hh hnever
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-! ## Client applications of the three halting endpoints

`thm:halts`, `thm:loops` and `thm:dontwait` are stated over a *sequence* of machines, and the
point of the write-out classes is that the sequence may genuinely grow.  The three `example`s
below apply each endpoint the way a downstream caller would: at concrete data, at a family
with growing source, with every class hypothesis actually discharged.  They are not
restatements.

Two of the three leave nothing to the caller.  The `thm:loops` example is the exception: it
still takes `hloops`, the object-level refutation premise, because that premise cannot be
discharged for an *arbitrary* `T`.  Its fully discharged form is
`thm_loops_applied_at_loopsTheory` below, stated at the concrete witness theory
`loopsTheory`; read the disclosure at `loopsTheory` for what that witness does and does not
establish. -/

/-- **`thm:halts`, applied.**  The machine family is `Nat.Partrec.Code.nest`, whose source
grows linearly in the day and whose source *number* is exponential (so the whole-value class
excludes it, `digitMachineCodes_nest_not_polyMachineCodes`), and whose halting hypothesis is
*proved* rather than assumed (`codeHalts_nest`).  The inputs are the paper's own `⟨x⟩` shape,
the `n`-bit string `2 ^ n`.  Nothing is left for the caller. -/
example [𝗥₀ ⪯ T] :
    (fun n => liaHistory (theoremDP T) n
      ((representedHaltingClaims (theoremPresentation T)
          Nat.Partrec.Code.nest (fun n => 2 ^ n)
          Nat.Partrec.Code.bigDigits_sourceNat_nest bigDigits_two_pow).sentence n))
        ≈ₙ fun _ => 1 :=
  lia_learns_halting_patterns_unconditional T
    Nat.Partrec.Code.nest (fun n => 2 ^ n)
    Nat.Partrec.Code.bigDigits_sourceNat_nest bigDigits_two_pow
    (fun n => codeHalts_nest n (2 ^ n))

/-- **`thm:dontwait`, applied.**  A machine that provably halts on nothing
(`neverHaltMachine`), the paper's `⟨y⟩` bitstring inputs `2 ^ n`, and the identity horizon
supplied through `ComputableHorizon.of`.  The non-halting hypothesis is proved, not assumed. -/
example [𝗥₀ ⪯ T] :
    (fun n => liaHistory (theoremDP T) n
      ((representedBoundedHaltingClaims (theoremPresentation T)
          (fun _ => neverHaltMachine) (fun n => 2 ^ n) (fun n => n)
          (digitMachineCodes_const neverHaltMachine) bigDigits_two_pow
          (ComputableHorizon.of Computable.id)).sentence n))
        ≈ₙ fun _ => 0 :=
  lic_does_not_anticipate_halting_unconditional T
    (fun _ => neverHaltMachine) (fun n => 2 ^ n) (fun n => n)
    (digitMachineCodes_const neverHaltMachine) bigDigits_two_pow
    (ComputableHorizon.of Computable.id)
    (fun n => not_codeHalts_neverHaltMachine (2 ^ n))

/-- **`thm:loops`, applied.**  Same growing machine family as `thm:halts`, same inputs, both
class hypotheses discharged — but `hloops` remains a hypothesis of the `example`, because it
is object-level `T`-refutability of a Π₁ fact and, *with the installed substrate*, there is
no route to it for an arbitrary `T`.  The obstruction is representational: the only bridges
FFL gives to `T ⊢ …` for a `codeOfREPred` schema are positive (`re_complete`,
`re_complete_mp`), and the schema itself is picked by `Classical.epsilon`, so its shape is
unreachable and no `T` can be *shown* to refute a particular false instance.  What the
example establishes is that everything else in the signature is inhabitable at a genuinely
varying family.  `hloops` itself is separately shown inhabitable — at a specific, true, `Δ₁`
theory — by `loopsTheory_refutes` and `thm_loops_applied_at_loopsTheory` below; read the
disclosure at `loopsTheory` for what that witness does and does not establish. -/
example [𝗥₀ ⪯ T]
    (hloops : ∀ n, T ⊢ ∼(universalHaltingSchema/[
      ↑(haltingClaimInput (Nat.Partrec.Code.nest n) (2 ^ n))])) :
    (fun n => liaHistory (theoremDP T) n
      ((representedHaltingClaims (theoremPresentation T)
          Nat.Partrec.Code.nest (fun n => 2 ^ n)
          Nat.Partrec.Code.bigDigits_sourceNat_nest bigDigits_two_pow).sentence n))
        ≈ₙ fun _ => 0 :=
  lic_learns_provable_nonhalting_patterns_unconditional T
    Nat.Partrec.Code.nest (fun n => 2 ^ n)
    Nat.Partrec.Code.bigDigits_sourceNat_nest bigDigits_two_pow hloops

/-! ## N+ for `thm:loops`'s refutation premise

`lic_learns_provable_nonhalting_patterns_unconditional` carries the premise

  `hloops : ∀ n, T ⊢ ∼(universalHaltingSchema/[↑(haltingClaimInput (machines n) (inputs n))])`

— object-level `T`-**refutability** of the halting schema.  Every other premise of that
endpoint is discharged at concrete data in the client section above; this one is not, and
this section supplies its witness.

The witness is a theory, not a derivation, and that is forced **by the installed substrate**,
not by mathematics.  Two arguments that look like they force it do not, and are recorded here
so nobody re-derives them:

* Σ₁-soundness does *not* forbid `T ⊢ ∼σ` for a false Σ₁ instance `σ`.  Refuting a false Σ₁
  sentence is proving a true Π₁ sentence, which `𝗜𝚺₁` and `𝗣𝗔` do routinely.
* FFL's `incomplete_of_REPred_not_ComputablePred_Nat'` refutes only the *uniform* negative
  representation principle — that some `T` refutes *every* false instance.  It says nothing
  about any single instance, and a natural arithmetization of "`rfind' succ` diverges" is
  refutable in `𝗜𝚺₁` by a one-line induction.

What actually blocks a natural `T` here is *opacity of the schema*.
`universalHaltingSchema := codeOfREPred UniversalCodeHalts` is chosen by `Classical.epsilon`
(`R0/Representation.lean:232-247`), so nothing about the chosen formula is provable beyond
its defining spec `codeOfREPred_spec`, which is a statement about standard-model truth.  The
only lemmas taking that spec to `T ⊢ …` are positive (`re_complete`, `re_complete_mp`), so
there is no handle by which any `T` could be *shown* to refute a particular false instance.
Hence no natural theory (`𝗜𝚺₁`, `𝗣𝗔`, `𝗭𝗙𝗖`) can be exhibited here *with this substrate*,
and the honest witness puts the Π₁ sentence into the theory as an axiom — the same device
FFL uses for `T.Con` and `T.Incon`. -/

/-- Truth of a halting-schema instance in the standard model.  The `re_complete` route runs
`ℕ ⊧ σ/[↑z] → T ⊢ σ/[↑z]` through Σ₁-completeness; this is the semantic half alone, which is
what an axiom witness needs (and it is an `Iff`, so it also gives *falsity* of an instance
naming a non-halting run). -/
lemma models_haltingSchema_iff (z : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧ (universalHaltingSchema/[↑z] : ArithmeticSentence) ↔ UniversalCodeHalts z := by
  simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton]
    using (universalHaltingSchema_spec z)

/-- The one Π₁ sentence the witness theory adds: `neverHaltMachine` does not halt on `0`,
spelled as a refutation of the halting schema at that claim's input. -/
noncomputable def loopsWitnessSentence : ArithmeticSentence :=
  ∼(universalHaltingSchema/[↑(haltingClaimInput neverHaltMachine 0)])

/-- The added axiom is **true**, not merely consistent: `neverHaltMachine` provably halts on
nothing (`not_codeHalts_neverHaltMachine`). -/
lemma models_loopsWitnessSentence : ℕ↓[ℒₒᵣ] ⊧ loopsWitnessSentence := by
  rw [loopsWitnessSentence, Semantics.Not.models_not, models_haltingSchema_iff,
    universalCodeHalts_claimInput]
  exact not_codeHalts_neverHaltMachine 0

/-- **The witness theory for `thm:loops`'s refutation premise.**  `𝗜𝚺₁` together with one
true Π₁ axiom: "`neverHaltMachine` does not halt on `0`".

*What this establishes.*  The premise set of
`lic_learns_provable_nonhalting_patterns_unconditional` is inhabited by a theory that is
`Δ₁`-axiomatized, extends `𝗜𝚺₁` (hence `𝗥₀`), is Σ₁-sound, and is consistent — all four
instance arguments of the endpoint are *discharged*, not assumed — and by a machine family
whose non-halting is *proved* (`not_codeHalts_neverHaltMachine`), so the endpoint's
`≈ₙ fun _ => 0` conclusion is semantically correct rather than vacuously satisfied.  Since
every axiom is true in `ℕ`, Σ₁-soundness and consistency come from `ℕ↓[ℒₒᵣ] ⊧* loopsTheory`
rather than from an unproved assumption.

*Disclosed weakness.*  `T ⊢ ∼σ` holds here **by axiom fiat**: `loopsTheory_refutes` is
`Entailment.by_axm`, not arithmetic reasoning.  This is the strongest witness available
*with the installed substrate*, and the obstruction is representational, not mathematical.
It is emphatically **not** that refuting `σ` is impossible for a natural theory: `∼σ` is a
true Π₁ sentence, Σ₁-soundness does not forbid proving one, and `𝗜𝚺₁` would refute a natural
arithmetization of this particular non-halting fact by induction.  The obstruction is that
`universalHaltingSchema` is `codeOfREPred UniversalCodeHalts`, whose formula FFL picks by
`Classical.epsilon`: its shape is unreachable from the API, the only property of it that can
be cited is `codeOfREPred_spec` (standard-model truth), and the only lemmas carrying that to
`T ⊢ …` are the positive ones.  So there is no handle by which *any* concrete `T` could be
shown to refute this instance, and the witness cannot be strengthened to a natural theory
without changing the substrate.

*The honest strengthenings,* if this premise is ever to be discharged for a natural `T`, are:
(i) a `halting_fails` field on `ComputationTheoryPresentation`, the exact analogue of its
existing `boundedFailure_refutes` — available there only because *bounded* failure is itself
r.e., and unavailable here because unbounded failure is not; (ii) a Π₁-reflection hypothesis
on `T`, which is a genuine strengthening of the endpoint's hypotheses and would have to be
stated as such; or (iii) replacing `codeOfREPred` for this schema by a hand-rolled Δ₀/Σ₁
halting formula carrying its own representability lemma, which restores the shape of the
formula to the API and would also address the other places in this development where
`Classical.epsilon`-chosen schemas are opaque.

Kind `N+`, provenance: (a) the `Δ₁`, `⪯`, soundness, consistency and non-halting facts are
derived in-project; (b) `𝗜𝚺₁.Δ₁`, `Theory.Δ₁.insert`, `WeakerThan.ofSubset` and the
`ℕ ⊧* T → T.SoundOn F` instance are FFL citations; (c) **the refutation premise itself** —
the sentence is an axiom of the witness theory rather than a consequence of arithmetic.
Paper node: `thm:loops` -/
noncomputable def loopsTheory : ArithmeticTheory := insert loopsWitnessSentence 𝗜𝚺₁

/-- Every axiom of `loopsTheory` is true in the standard model.  Σ₁-soundness and
consistency both follow from this, so neither is assumed. -/
instance models_loopsTheory : ℕ↓[ℒₒᵣ] ⊧* loopsTheory :=
  Semantics.ModelsSet.insert_iff.mpr ⟨models_loopsWitnessSentence, inferInstance⟩

noncomputable instance loopsTheory_delta1 : loopsTheory.Δ₁ :=
  inferInstanceAs (LO.FirstOrder.Theory.Δ₁ (insert loopsWitnessSentence 𝗜𝚺₁))

instance loopsTheory_isigma1 : (𝗜𝚺₁ : ArithmeticTheory) ⪯ loopsTheory :=
  Entailment.WeakerThan.ofSubset (Set.subset_insert _ _)

instance loopsTheory_r0 : (𝗥₀ : ArithmeticTheory) ⪯ loopsTheory :=
  Entailment.WeakerThan.trans (𝓢 := (𝗥₀ : ArithmeticTheory)) (𝓣 := (𝗜𝚺₁ : ArithmeticTheory))
    inferInstance loopsTheory_isigma1

/-- The witness theory is Σ₁-sound — from truth in `ℕ`, not by assumption. -/
lemma loopsTheory_soundOnSigma1 : loopsTheory.SoundOnHierarchy 𝚺 1 := inferInstance

/-- The witness theory is **consistent**, so the premise set is not inhabited by a theory
that proves everything. -/
lemma loopsTheory_consistent : Entailment.Consistent loopsTheory := inferInstance

/-- `loopsTheory` provably does not halt on the constant family — the endpoint's
`≈ₙ fun _ => 0` conclusion is therefore the semantically correct one. -/
lemma loopsWitness_never_halts (n : ℕ) :
    ¬ CodeHalts ((fun _ => neverHaltMachine) n) ((fun _ => 0) n) :=
  not_codeHalts_neverHaltMachine 0

/-- **The refutation premise, discharged.**  By axiom membership — see the disclosure at
`loopsTheory`. -/
lemma loopsTheory_refutes (n : ℕ) :
    loopsTheory ⊢ ∼(universalHaltingSchema/[
      ↑(haltingClaimInput ((fun _ => neverHaltMachine) n) ((fun _ => 0) n))]) :=
  Entailment.by_axm (Set.mem_insert _ _)

/-- **`thm:loops`, applied with nothing left to the caller.**  Every hypothesis and every
instance argument of `lic_learns_provable_nonhalting_patterns_unconditional` is discharged:
the write-out classes at the constant family, and the refutation premise at `loopsTheory`.
The machine family is constant here — the growth of the machine/input sequence is exercised
separately by the `thm:halts` and `thm:dontwait` clients above — because a varying family
would require a `Δ₁` definability proof for an infinite axiom set, whereas what this witness
exists to show is that the refutation premise is inhabitable at all.
Paper node: `thm:loops` -/
lemma thm_loops_applied_at_loopsTheory :
    (fun n => liaHistory (theoremDP loopsTheory) n
      ((representedHaltingClaims (theoremPresentation loopsTheory)
          (fun _ => neverHaltMachine) (fun _ => 0)
          (digitMachineCodes_const neverHaltMachine) (BigDigits.const 0)).sentence n))
        ≈ₙ fun _ => 0 :=
  lic_learns_provable_nonhalting_patterns_unconditional loopsTheory
    (fun _ => neverHaltMachine) (fun _ => 0)
    (digitMachineCodes_const neverHaltMachine) (BigDigits.const 0) loopsTheory_refutes

#print axioms provable_instances_re
#print axioms theoremDP_covers
#print axioms theoremDP_hworld
#print axioms theoremPresentation
#print axioms quotationPresentation
#print axioms quotation_presentation_nonvacuous
#print axioms lia_learns_halting_patterns_unconditional
#print axioms lic_introspection_ofCode_unconditional
#print axioms lic_paradox_resistance_ofDiagonal_unconditional
#print axioms lic_self_trust_ofRepresentation_unconditional
#print axioms lic_expectations_of_probabilities_ofCode_unconditional
#print axioms models_haltingSchema_iff
#print axioms models_loopsWitnessSentence
#print axioms loopsTheory
#print axioms loopsTheory_soundOnSigma1
#print axioms loopsTheory_consistent
#print axioms loopsWitness_never_halts
#print axioms loopsTheory_refutes
#print axioms thm_loops_applied_at_loopsTheory

end LogicalInduction
