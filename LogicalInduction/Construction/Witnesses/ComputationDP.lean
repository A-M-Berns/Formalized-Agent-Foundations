import LogicalInduction.Construction.Witnesses.ComputationSyntax
import LogicalInduction.Construction.Witnesses.ConditioningPresentation
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

Scope: the *computation* side only (`ComputationTheoryPresentation`), which is consistently
inhabitable.  The *quotation* side is separately blocked by a vacuity obstruction and is not
attempted here (see `notes/next-session.md`).

The result is unconditional and strictly axiom-clean: tall pole A (provability of schema
instances is r.e.), the representation coverage, the non-vacuity world `hworld`, and tall
pole B (the fuel-clocked enumerator is primitive recursive) are all discharged.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional

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

An *event* is a code `e = ⟨tag, z⟩` with `tag ∈ {0,…,5}` selecting one of the six
enters/refutes obligations and `z` its input.  A single r.e. predicate `Fires` and a single
atom map `atom` capture all six; the deductive process enumerates the fired atoms. -/

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
      (e.unpair.1 = 5 ∧ T ⊢ universalHaltingSchema/[↑e.unpair.2]) := by
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
  refine ((htag 0).and (hsub _)).or (((htag 1).and hnegsub).or
    (((htag 2).and (hsub _)).or (((htag 3).and (hsub _)).or
      (((htag 4).and (hsub _)).or ((htag 5).and (hsub _))))))

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
  rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | m
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
  -- Gödel-code builders `Nat.pair kind (Nat.pair schema z)`.
  have gc : ∀ k S : ℕ, Primrec (fun e : ℕ => Nat.pair k (Nat.pair S e.unpair.2)) := fun k S =>
    Primrec₂.natPair.comp (Primrec.const k) (Primrec₂.natPair.comp (Primrec.const S) hz)
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
  · simp [h, eventAtom, inconsistencyClaimSentence, computationClaimSentence, inconsistencyClaim,
      ComputationClaim.godelCode, ComputationClaimKind.godelCode, encode_atom, hKH]
  · simp [h, eventAtom, consistencyClaimSentence, computationClaimSentence, consistencyClaim,
      ComputationClaim.godelCode, ComputationClaimKind.godelCode, encode_negAtom, hKnH]
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
    machines inputs hm hi hhalts (fun n χ => liaHistory_range (theoremDP T) n χ)
    (fun n => ⟨provabilityWorld T, theoremDP_hworld T n⟩)

#print axioms provable_instances_re
#print axioms theoremDP_covers
#print axioms theoremDP_hworld
#print axioms theoremPresentation
#print axioms lia_learns_halting_patterns_unconditional

end LogicalInduction
