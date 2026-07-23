import LogicalInduction.Construction.Witnesses.ComputationSyntax
import LogicalInduction.Construction.Witnesses.ConditioningPresentation
import LogicalInduction.Construction.Witnesses.QuotationAffine
import LogicalInduction.Construction.LIACompiler
import Foundation.FirstOrder.Incompleteness.Halting

/-!
# M7-QUOTE-DP meta-learning MVP — computation side

The `_ofComputation` meta-learning endpoints of `ComputationSyntax.lean` are conditional on
a `ComputationTheoryPresentation DP T`: a computable deductive process whose stages track the
`T`-provable instances of the fixed universal computation schemas.  This file **constructs**
such a process for a fixed Σ₁-sound `T ⊇ 𝗜𝚺₁`, discharging the presentation and — crucially —
the market non-vacuity hypothesis `hworld`, which is *proved* here from `T`-consistency rather
than assumed.  Feeding it to the constructed `LIA` inductor yields the project's first
**unconditional** epistemic theorem over `LIA` (`lia_learns_halting_patterns_unconditional`).

The **same** computable process also inhabits the redesigned code-indexed
`QuotationTheoryPresentation` (event tags 6/7 enumerate the quotation atoms), so
`quotationPresentation` + `theoremDP_hworld` jointly certify that `Q ∧ hworld` is
satisfiable (`quotation_presentation_nonvacuous`) — the fix for the old free-schema
quotation vacuity.  Because quotation folds a decidable-decision selector into the numeral
of *fixed* universal schemas (`universalQuotePos`/`universalQuoteNeg`), its instances are
enumerable by the very same `provable_instances_re`; the positive/negative fibers are the
value-1/value-0 fibers of one deterministic computation, hence mutually exclusive, which is
what keeps `hworld` consistent (tags 6/7).

The result is unconditional and strictly axiom-clean: tall pole A (provability of schema
instances is r.e.), the representation coverage, the non-vacuity world `hworld`, and tall
pole B (the fuel-clocked enumerator is primitive recursive) are all discharged.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional
open Filter Topology

/-! ## Tall pole A — provability of schema instances is r.e. -/

open Classical in
/-- For a fixed schema `φ`, provability of its numerical instances in a Δ₁, Σ₁-sound theory
extending `𝗜𝚺₁` is recursively enumerable.  Mirrors the positive-path assembly inside FFL's
`incomplete_of_REPred_not_ComputablePred_Nat'`. -/
lemma provable_instances_re (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (φ : ArithmeticSemisentence 1) :
    REPred (fun z : ℕ => T ⊢ φ/[↑z]) := by
  have hsig : 𝚺₁-Predicate fun b : ℕ ↦
      T.Provable (Bootstrapping.subst ℒₒᵣ ?[Bootstrapping.Arithmetic.numeral b] ⌜φ⌝) := by
    definability
  apply REPred.of_eq (re_iff_sigma1.mpr hsig)
  intro a
  constructor
  · rintro hP
    apply Theory.Provable.sound
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
lemma eventFires_re [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
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
lemma exists_eventCode [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
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
noncomputable def theoremDP [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : DeductiveProcess where
  D := theoremStage (exists_eventCode T).choose
  mono := theoremStage_mono _

/-- Coverage: every fired event's atom eventually appears in a stage. -/
lemma theoremDP_covers [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
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
  · -- tag 3: ∼bounded halting, via Σ₁-soundness
    simp only [eventFires, h] at hfires
    simp only [eventAtom, h, boundedHaltingClaimSentence, computationClaimSentence, holds_not,
      holds_atom, provabilityWorld_boundedHalting]
    intro hbh
    have h1 : ¬ UniversalCodeHaltsWithin e.unpair.2 :=
      (re_complete (T := T) universalCodeHaltsWithinFailure_re).mpr (by simpa using hfires)
    have h2 : UniversalCodeHaltsWithin e.unpair.2 :=
      (re_complete (T := T) universalCodeHaltsWithin_re).mpr (by simpa using hbh)
    exact h1 h2
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
      (re_complete (T := T) universalQuotePos_re (x := e.unpair.2)).mpr (by simpa using hpos)
    have hn : quoteNeg e.unpair.2.unpair.1 e.unpair.2.unpair.2 :=
      (re_complete (T := T) universalQuoteNeg_re (x := e.unpair.2)).mpr (by simpa using hfires)
    exact quotePos_quoteNeg_exclusive _ _ ⟨hp, hn⟩
  · -- default tag: atom is ⊤, always held
    simp only [eventAtom, h]
    show LO.Propositional.Formula.Boolean.val (provabilityWorld T) ⊤
    simp [LO.Propositional.Formula.Boolean.val]

/-! ## Computability of the stage enumerator (tall pole B)

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
      cases hbb : (Nat.Partrec.Code.evaln p.1 c p.2).isSome <;> simp [hbb])
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

/-- **Tall pole B discharged.**  The provability deductive process is computable: one fixed
partial-recursive program emits the encoded stage `D n` on input `n`. -/
lemma theoremDP_computable [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ComputableDeductiveProcess (theoremDP T) := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp (theoremStage_encode_prim (exists_eventCode T).choose)))
  refine ⟨code, fun n => ?_⟩
  rw [hcode]
  exact Part.mem_some _

/-! ## The presentation and the unconditional LIA endpoint -/

/-- **The constructed computation presentation.**  All six enters/refutes obligations are
discharged by coverage of the provability enumeration. -/
noncomputable def theoremPresentation [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
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

/-- **The constructed quotation presentation — certifies the vacuity fix.**  The very same
computable provability process `theoremDP` (whose stages also enumerate the code-indexed
quotation atoms, tags 6/7) inhabits `QuotationTheoryPresentation`.  Its existence, together
with the *proved* `theoremDP_hworld`, demonstrates that `Q ∧ hworld` is satisfiable — so the
introspection / self-trust / expectation / paradox-resistance endpoints keyed on
`QuotationTheoryPresentation` are **no longer vacuous**.
Paper node: `thm:ref` -/
noncomputable def quotationPresentation [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
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

/-- **Quotation non-vacuity certificate (`N+`).**  For a Σ₁-sound `T ⊇ 𝗜𝚺₁` there is a
deductive process carrying *both* a `QuotationTheoryPresentation` *and* the market
non-vacuity hypothesis `hworld`.  So the conjunction `Q ∧ hworld` that every introspection /
self-trust / expectation / paradox-resistance `_ofCode`/`_ofDiagonal`/`_ofRepresentation`
endpoint consumes is **satisfiable** — those endpoints are no longer vacuously true, which
the old free-schema `QuotationTheoryPresentation` made impossible (`positive = negative = ⊤`
forced an inconsistent stage).  The code-indexed redesign (fixed universal schemas, selector
folded into the numeral) is what makes this witness exist.
Paper node: `thm:ref` -/
theorem quotation_presentation_nonvacuous
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ (DP : DeductiveProcess) (_ : QuotationTheoryPresentation DP T),
      ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) :=
  ⟨theoremDP T, quotationPresentation T,
    fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩⟩

/-- **The MVP.** For a Σ₁-sound theory `T ⊇ 𝗜𝚺₁`, the constructed `LIA` inductor over the
constructed provability deductive process learns every provably-halting pattern —
**unconditionally**: the deductive process is constructed and proved computable, and the
market non-vacuity `hworld` is proved, not assumed.  No hypotheses remain beyond the theory
instances and the (true) hypothesis that the machines provably halt.
Paper node: `thm:halts` -/
theorem lia_learns_halting_patterns_unconditional
    (T : ArithmeticTheory) [𝗥₀ ⪯ T] [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs)
    (hhalts : ∀ n, CodeHalts (machines n) (inputs n)) :
    (fun n => liaHistory (theoremDP T) n
      ((representedHaltingClaims (theoremPresentation T) machines inputs hm hi).sentence n))
        ≈ₙ fun _ => 1 :=
  haveI : IsLogicalInductor (liaHistory (theoremDP T)) (theoremDP T) :=
    LIA_is_logical_inductor (theoremDP T) (theoremDP_computable T)
  lic_learns_halting_patterns_ofComputation (theoremPresentation T) (liaHistory (theoremDP T))
    machines inputs hm hi hhalts
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-! ## Unconditional self-reference / quotation endpoints over the constructed `LIA`

Step 3 of the quotation rescue.  Because `quotationPresentation` inhabits the redesigned
`QuotationTheoryPresentation` over the constructed computable `theoremDP`, and
`theoremDP_hworld` discharges the market non-vacuity, every `_ofCode`/`_ofDiagonal`/
`_ofRepresentation` self-reference endpoint instantiates over `liaHistory (theoremDP T)` with
**no** market / inductor / `Q` / `hworld` hypotheses remaining — only the caller's own quoted
decision and its reflection data.  This turns the introspection / expectation / self-trust /
paradox-resistance family from *conditional on an assumed presentation* into *unconditional
over a concrete constructed inductor*, the same status the meta-learning MVP reached. -/

variable [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- The constructed inductor instance for the provability process, reused (inlined) by every
unconditional quotation endpoint below. -/
private noncomputable abbrev theoremLIA : IsLogicalInductor (liaHistory (theoremDP T)) (theoremDP T) :=
  LIA_is_logical_inductor (theoremDP T) (theoremDP_computable T)

/-- A named exact market program for the constructed `LIA`, used to derive its canonical
paradox-resistance diagonal without any caller-supplied semantic relation.
Paper node: `thm:lp` -/
noncomputable def theoremMarketComputation :
    MarketComputation (liaHistory (theoremDP T)) :=
  (theoremLIA T).marketComputable.nonemptyComputation.some

/-- The canonical public diagonal quote for the constructed `LIA` at threshold `p`.
Paper node: `thm:lp` -/
noncomputable def theoremDiagonalQuoteCode (p : ℚ) :
    ParameterizedDiagonalQuoteCode T
      (diagonalPriceTruth (theoremMarketComputation T) p) :=
  parameterizedDiagonalQuoteCodeOfMarket (theoremMarketComputation T) T p

/-- `thm:epr`, unconditional over `LIA`. -/
theorem lic_expectations_of_probabilities_ofCode_unconditional
    {value : ℕ → ℚ} (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, liaHistory (theoremDP T) n (φ n) = (value n : ℝ)) :
    (fun n => liaHistory (theoremDP T) n (φ n)) ≈ₙ
      fun n => (q.luv n).expect (liaHistory (theoremDP T)) n :=
  haveI := theoremLIA T
  lic_expectations_of_probabilities_ofCode (quotationPresentation T)
    (liaHistory (theoremDP T)) φ hφ q hexact
    (fun n s => liaHistory_range (theoremDP T) n s)
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:er`, unconditional over `LIA`. -/
theorem lic_iterated_expectations_ofCode_unconditional
    {value : ℕ → ℚ} (X : ℕ → LUV) (hX : LUV.PolyThresholdCodeSeq X)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, (X n).expect (liaHistory (theoremDP T)) n = (value n : ℝ)) :
    (fun n => (X n).expect (liaHistory (theoremDP T)) n) ≈ₙ
      fun n => (q.luv n).expect (liaHistory (theoremDP T)) n :=
  haveI := theoremLIA T
  lic_iterated_expectations_ofCode (quotationPresentation T)
    (liaHistory (theoremDP T)) X hX q hexact
    (fun n s => liaHistory_range (theoremDP T) n s)
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:ref` (introspection), unconditional over `LIA`. -/
theorem lic_introspection_ofCode_unconditional
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ) (a b δ : ℕ → ℚ)
    (lowerFeature : ℕ → EF)
    (hlower : GeneratedRatFeature (liaHistory (theoremDP T)) a lowerFeature)
    (upperFeature : ℕ → EF)
    (hupper : GeneratedRatFeature (liaHistory (theoremDP T)) b upperFeature)
    (hδ : PolyRatCodes δ) (hδinv : PolyRatCodes (fun n ↦ 1 / δ n))
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
    φ hφ a b δ lowerFeature hlower upperFeature hupper hδ hδinv hδpos hδzero hab q
    (fun n s => liaHistory_range (theoremDP T) n s)
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:lp` (paradox resistance), unconditional over `LIA`.  The named market program,
its self-referential public atom, and the matching FFL parameterized fixed point are all
constructed internally.
Paper node: `thm:lp` -/
theorem lic_paradox_resistance_ofDiagonal_unconditional
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (width : ℕ → ℚ) (hwidth : PolyRatCodes width)
    (hwidthInv : PolyRatCodes (fun n ↦ 1 / width n))
    (hwidthPos : ∀ n, 0 < width n)
    (hwidthZero : Tendsto (fun n ↦ (width n : ℝ)) atTop (𝓝 0)) :
    (fun n => liaHistory (theoremDP T) n
      ((theoremDiagonalQuoteCode T p).toBooleanQuoteCode.sentence n)) ≈ₙ
      fun _ => (p : ℝ) :=
  haveI := theoremLIA T
  lic_paradox_resistance_ofDiagonal (quotationPresentation T) (liaHistory (theoremDP T))
    (theoremMarketComputation T) p hp0 hp1 width hwidth hwidthInv hwidthPos hwidthZero
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:cee` (expected future expectations), unconditional over `LIA`. -/
theorem lic_expected_future_expectations_ofRepresentation_unconditional
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (X Y : ℕ → LUV) (hX : LUV.PolyThresholdCodeSeq X) (hY : LUV.PolyThresholdCodeSeq Y)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      ∃ x, v.ValuesAt (X n) x)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      v.ValuesAt (Y n) ((X n).expect (liaHistory (theoremDP T)) (f n))) :
    (fun n ↦ (X n).expect (liaHistory (theoremDP T)) n) ≈ₙ
      fun n ↦ (Y n).expect (liaHistory (theoremDP T)) n :=
  haveI := theoremLIA T
  lic_expected_future_expectations_ofRepresentation (P := liaHistory (theoremDP T))
    (DP := theoremDP T) f hstrict X Y hX hY source_valued reflected
    (fun n s => liaHistory_range (theoremDP T) n s)
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:ceu` (no expected net update), unconditional over `LIA`. -/
theorem lic_no_expected_net_update_ofRepresentation_unconditional
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (φ : ℕ → Sentence) (Y : ℕ → LUV)
    (hφ : PolySentenceCodes φ) (hY : LUV.PolyThresholdCodeSeq Y)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      v.ValuesAt (Y n) (liaHistory (theoremDP T) (f n) (φ n))) :
    (fun n ↦ liaHistory (theoremDP T) n (φ n)) ≈ₙ
      fun n ↦ (Y n).expect (liaHistory (theoremDP T)) n :=
  haveI := theoremLIA T
  lic_no_expected_net_update_ofRepresentation (P := liaHistory (theoremDP T))
    (DP := theoremDP T) f hstrict φ Y hφ hY reflected
    (fun n s => liaHistory_range (theoremDP T) n s)
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:ccee` (conditional no expected net update), unconditional over `LIA`. -/
theorem lic_no_expected_net_update_conditional_ofRepresentation_unconditional
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (X Z Z' : ℕ → LUV) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat (liaHistory (theoremDP T)) w)
    (hX : LUV.PolyThresholdCodeSeq X) (hZ : LUV.PolyThresholdCodeSeq Z)
    (hZ' : LUV.PolyThresholdCodeSeq Z')
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      ∃ x, v.ValuesAt (X n) x)
    (left_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      ∀ x, v.ValuesAt (X n) x → v.ValuesAt (Z n) (x * w (f n)))
    (right_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      v.ValuesAt (Z' n) ((X n).expect (liaHistory (theoremDP T)) (f n) * w (f n))) :
    (fun n ↦ (Z n).expect (liaHistory (theoremDP T)) n) ≈ₙ
      fun n ↦ (Z' n).expect (liaHistory (theoremDP T)) n :=
  haveI := theoremLIA T
  lic_no_expected_net_update_conditional_ofRepresentation (P := liaHistory (theoremDP T))
    (DP := theoremDP T) f hstrict X Z Z' w weight_mem weight_generable hX hZ hZ'
    source_valued left_reflected right_reflected
    (fun n s => liaHistory_range (theoremDP T) n s)
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:st` (self-trust), unconditional over `LIA`. -/
theorem lic_self_trust_ofRepresentation_unconditional
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (φ : ℕ → Sentence) (δ p : ℕ → ℚ) (A B : ℕ → LUV)
    (delta_pos : ∀ n, 0 < δ n) (probability_mem : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hφ : PolySentenceCodes φ) (hδ : PolyRatCodes δ)
    (hδinv : PolyRatCodes (fun n ↦ 1 / δ n)) (hp : PolyRatCodes p)
    (hA : LUV.PolyThresholdCodeSeq A) (hB : LUV.PolyThresholdCodeSeq B)
    (confidence_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      v.ValuesAt (B n) (ctsInd (δ n) (liaHistory (theoremDP T) (f n) (φ n)) (p n)))
    (product_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      v.ValuesAt (A n)
        (v.payout (φ n) * ctsInd (δ n) (liaHistory (theoremDP T) (f n) (φ n)) (p n))) :
    (fun n ↦ (A n).expect (liaHistory (theoremDP T)) n) ≳ₙ
      fun n ↦ (p n : ℝ) * (B n).expect (liaHistory (theoremDP T)) n :=
  haveI := theoremLIA T
  lic_self_trust_ofRepresentation (P := liaHistory (theoremDP T)) (DP := theoremDP T)
    f hstrict φ δ p A B delta_pos probability_mem hφ hδ hδinv hp hA hB
    confidence_reflected product_reflected
    (fun n s => liaHistory_range (theoremDP T) n s)
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-! ## Unconditional meta-learning siblings over the constructed `LIA`

The other five `_ofComputation` meta-learning endpoints instantiate over `liaHistory
(theoremDP T)` exactly like `lia_learns_halting_patterns_unconditional`, reusing
`theoremPresentation` + `theoremDP_hworld`. Only the caller's concrete computation and the
(true) hypothesis about it remain. -/

/-- `thm:pac`, unconditional over `LIA`. -/
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

/-- `thm:pazfc`, unconditional over `LIA`. -/
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

/-- `thm:incons`, unconditional over `LIA`. -/
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

/-- `thm:loops`, unconditional over `LIA`. -/
theorem lic_learns_provable_nonhalting_patterns_unconditional [𝗥₀ ⪯ T]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs)
    (hloops : ∀ n, T ⊢ ∼(universalHaltingSchema/[
      ↑(haltingClaimInput (machines n) (inputs n))])) :
    (fun n => liaHistory (theoremDP T) n
      ((representedHaltingClaims (theoremPresentation T) machines inputs hm hi).sentence n))
        ≈ₙ fun _ => 0 :=
  haveI := theoremLIA T
  lic_learns_provable_nonhalting_patterns_ofComputation (theoremPresentation T)
    (liaHistory (theoremDP T)) machines inputs hm hi hloops
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

/-- `thm:dontwait`, unconditional over `LIA`. -/
theorem lic_does_not_anticipate_halting_unconditional [𝗥₀ ⪯ T]
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs)
    (hh : PolyNatCodes horizons)
    (hnever : ∀ n, ¬CodeHalts (machines n) (inputs n)) :
    (fun n => liaHistory (theoremDP T) n
      ((representedBoundedHaltingClaims (theoremPresentation T) machines inputs horizons hm hi hh).sentence n))
        ≈ₙ fun _ => 0 :=
  haveI := theoremLIA T
  lic_does_not_anticipate_halting_ofComputation (theoremPresentation T)
    (liaHistory (theoremDP T)) machines inputs horizons hm hi hh hnever
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

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

end LogicalInduction
