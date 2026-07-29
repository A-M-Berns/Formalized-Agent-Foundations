import LogicalInduction.Construction.Witnesses.M7Witnesses
import LogicalInduction.Properties.MetaLearning
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Bootstrapping.Syntax.Theory

/-!
# Concrete computation syntax and arithmetic-theory representation

Syntax layer for the paper's computational-knowledge theorems (`thm:pac`, `thm:pazfc`,
`thm:incons`, `thm:halts`, `thm:loops`, `thm:dontwait`).

The public logical-induction language is propositional, while the computation
representation theorem is first-order arithmetic.  This file supplies the translation
between the two: claims carry an actual FFL arithmetic schema and a compact input, and
their Gödel names are propositional atoms.  `ComputationTheoryPresentation` is the
remaining background-theory premise: it translates proofs of the fixed universal
computation schemas into stages of a computable deductive process.  It contains no
sentence sequences, prices, markets, or asymptotic conclusions.

FFL's `re_complete` gives weak (positive) representation of every r.e. predicate.  A false
decidable claim is not in general refutable merely from weak representation, so bounded
failure is represented by its own complementary r.e. schema.  The presentation translates
a proof of that schema into the negated market literal.  This is the precise residual
translation required by the propositional public language.
-/

namespace LogicalInduction

open LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## Universal arithmetic computation predicates -/

/-- Decode the left component as a repository program and run it on the right component. -/
def UniversalCodeHalts (z : ℕ) : Prop :=
  ((Denumerable.ofNat Nat.Partrec.Code z.unpair.1).eval z.unpair.2).Dom

/-- The universal unbounded halting predicate is recursively enumerable. -/
lemma universalCodeHalts_re : REPred UniversalCodeHalts := by
  apply Partrec.dom_re
  exact Nat.Partrec.Code.eval_part.comp
    ((Computable.ofNat Nat.Partrec.Code).comp
      (Primrec.fst.comp Primrec.unpair).to_comp)
    (Primrec.snd.comp Primrec.unpair).to_comp

/-- Decode `z = ⟨machine, ⟨input, steps⟩⟩` and run the clocked interpreter. -/
def UniversalCodeHaltsWithin (z : ℕ) : Prop :=
  (Nat.Partrec.Code.evaln z.unpair.2.unpair.2
    (Denumerable.ofNat Nat.Partrec.Code z.unpair.1)
    z.unpair.2.unpair.1).isSome = true

/-- Bounded universal halting is a computable predicate. -/
lemma universalCodeHaltsWithin_computable : ComputablePred UniversalCodeHaltsWithin := by
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun z => (Nat.Partrec.Code.evaln z.unpair.2.unpair.2
    (Denumerable.ofNat Nat.Partrec.Code z.unpair.1)
    z.unpair.2.unpair.1).isSome, ?_, by rfl⟩
  apply Primrec.to_comp
  apply Primrec.option_isSome.comp
  let hsteps : Primrec fun z : ℕ => z.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  let hcode : Primrec fun z : ℕ => Denumerable.ofNat Nat.Partrec.Code z.unpair.1 :=
    (Primrec.ofNat Nat.Partrec.Code).comp (Primrec.fst.comp Primrec.unpair)
  let hinput : Primrec fun z : ℕ => z.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact Nat.Partrec.Code.primrec_evaln.comp ((hsteps.pair hcode).pair hinput)

lemma universalCodeHaltsWithin_re : REPred UniversalCodeHaltsWithin :=
  universalCodeHaltsWithin_computable.to_re

lemma universalCodeHaltsWithinFailure_re :
    REPred (fun z => ¬UniversalCodeHaltsWithin z) :=
  universalCodeHaltsWithin_computable.not.to_re

/-- FFL's quoted arithmetic schema for universal unbounded halting. -/
noncomputable def universalHaltingSchema : ArithmeticSemisentence 1 :=
  codeOfREPred UniversalCodeHalts

/-- FFL's quoted arithmetic schema for bounded halting. -/
noncomputable def universalBoundedHaltingSchema : ArithmeticSemisentence 1 :=
  codeOfREPred UniversalCodeHaltsWithin

/-- The complementary FFL schema certifying failure of a bounded run. -/
noncomputable def universalBoundedFailureSchema : ArithmeticSemisentence 1 :=
  codeOfREPred (fun z => ¬UniversalCodeHaltsWithin z)

/-- The unbounded schema has exactly the intended standard-model meaning. -/
lemma universalHaltingSchema_spec (z : ℕ) :
    ℕ ⊧ₘ universalHaltingSchema/[↑z] ↔ UniversalCodeHalts z := by
  simpa [universalHaltingSchema, models_iff, Semiformula.eval_substs,
    Matrix.constant_eq_singleton] using
      (codeOfREPred_spec universalCodeHalts_re (x := z))

/-- The bounded schema has exactly the intended standard-model meaning. -/
lemma universalBoundedHaltingSchema_spec (z : ℕ) :
    ℕ ⊧ₘ universalBoundedHaltingSchema/[↑z] ↔ UniversalCodeHaltsWithin z := by
  simpa [universalBoundedHaltingSchema, models_iff, Semiformula.eval_substs,
    Matrix.constant_eq_singleton] using
      (codeOfREPred_spec universalCodeHaltsWithin_re (x := z))

/-- The failure schema is the exact standard-model complement of bounded halting. -/
lemma universalBoundedFailureSchema_spec (z : ℕ) :
    ℕ ⊧ₘ universalBoundedFailureSchema/[↑z] ↔ ¬UniversalCodeHaltsWithin z := by
  simpa [universalBoundedFailureSchema, models_iff, Semiformula.eval_substs,
    Matrix.constant_eq_singleton] using
      (codeOfREPred_spec universalCodeHaltsWithinFailure_re (x := z))

lemma universalBoundedSchemas_complementary (z : ℕ) :
    (ℕ ⊧ₘ universalBoundedHaltingSchema/[↑z]) ↔
      ¬(ℕ ⊧ₘ universalBoundedFailureSchema/[↑z]) := by
  rw [universalBoundedHaltingSchema_spec, universalBoundedFailureSchema_spec]
  simp

/-! ## Concrete compact Gödel names -/

/-- The role played by an arithmetic schema in a public computation claim. -/
inductive ComputationClaimKind
  | halting
  | boundedHalting
  | inconsistency
  | consistency
  deriving DecidableEq

/-- A concrete quoted first-order claim: its role, arithmetic schema, and compact input. -/
structure ComputationClaim where
  kind : ComputationClaimKind
  schema : ArithmeticSemisentence 1
  input : ℕ

def ComputationClaimKind.godelCode : ComputationClaimKind → ℕ
  | .halting => 0
  | .boundedHalting => 1
  | .inconsistency => 2
  | .consistency => 3

lemma ComputationClaimKind.godelCode_injective :
    Function.Injective ComputationClaimKind.godelCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [ComputationClaimKind.godelCode]

/-- An injective compact Gödel name for a computation claim. -/
def ComputationClaim.godelCode (claim : ComputationClaim) : ℕ :=
  Nat.pair claim.kind.godelCode
    (Nat.pair (Encodable.encode claim.schema) claim.input)

lemma ComputationClaim.godelCode_injective :
    Function.Injective ComputationClaim.godelCode := by
  rintro ⟨ka, sa, ia⟩ ⟨kb, sb, ib⟩ h
  simp only [ComputationClaim.godelCode, Nat.pair_eq_pair] at h
  have hk : ka = kb := ComputationClaimKind.godelCode_injective h.1
  have hs : sa = sb := Encodable.encode_inj.mp h.2.1
  cases hk
  cases hs
  cases h.2.2
  rfl

/-- The public propositional sentence naming a quoted arithmetic computation claim. -/
def computationClaimSentence (claim : ComputationClaim) : Sentence :=
  LO.Propositional.Formula.atom claim.godelCode

lemma computationClaimSentence_injective :
    Function.Injective computationClaimSentence := by
  intro a b h
  apply ComputationClaim.godelCode_injective
  injection h

noncomputable def haltingClaim (z : ℕ) : ComputationClaim :=
  ⟨.halting, universalHaltingSchema, z⟩

noncomputable def boundedHaltingClaim (z : ℕ) : ComputationClaim :=
  ⟨.boundedHalting, universalBoundedHaltingSchema, z⟩

noncomputable def inconsistencyClaim (z : ℕ) : ComputationClaim :=
  ⟨.inconsistency, universalHaltingSchema, z⟩

/-- Consistency is named by the negation of the same halting/search schema. -/
noncomputable def consistencyClaim (z : ℕ) : ComputationClaim :=
  ⟨.consistency, ∼universalHaltingSchema, z⟩

noncomputable def haltingClaimSentence (z : ℕ) : Sentence :=
  computationClaimSentence (haltingClaim z)

noncomputable def boundedHaltingClaimSentence (z : ℕ) : Sentence :=
  computationClaimSentence (boundedHaltingClaim z)

noncomputable def inconsistencyClaimSentence (z : ℕ) : Sentence :=
  computationClaimSentence (inconsistencyClaim z)

noncomputable def consistencyClaimSentence (z : ℕ) : Sentence :=
  computationClaimSentence (consistencyClaim z)

/-- Pair a repository machine code and input without running the machine. -/
def haltingClaimInput (machine : Nat.Partrec.Code) (input : ℕ) : ℕ :=
  Nat.pair (Encodable.encode machine) input

/-- Pair a repository machine code, input, and clock without running the machine. -/
def boundedHaltingClaimInput (machine : Nat.Partrec.Code) (input steps : ℕ) : ℕ :=
  Nat.pair (Encodable.encode machine) (Nat.pair input steps)

@[simp] theorem universalCodeHalts_claimInput (machine : Nat.Partrec.Code) (input : ℕ) :
    UniversalCodeHalts (haltingClaimInput machine input) ↔ CodeHalts machine input := by
  simp [UniversalCodeHalts, haltingClaimInput, CodeHalts]

@[simp] theorem universalCodeHaltsWithin_claimInput
    (machine : Nat.Partrec.Code) (input steps : ℕ) :
    UniversalCodeHaltsWithin (boundedHaltingClaimInput machine input steps) ↔
      CodeHaltsWithin machine input steps := by
  simp [UniversalCodeHaltsWithin, boundedHaltingClaimInput, CodeHaltsWithin]

/-! ## Honest polynomial naming -/

/-- Polynomial code for a sequence of repository machines.
Paper node: `def:ec` -/
structure PolyMachineCodes (machines : ℕ → Nat.Partrec.Code) where
  code : Nat.Partrec.Code
  code_poly : PolyFueled code (fun n => Encodable.encode (machines n))

/-- Polynomial code for a natural-number sequence.
Paper node: `def:ec` -/
structure PolyNatCodes (values : ℕ → ℕ) where
  code : Nat.Partrec.Code
  code_poly : PolyFueled code values

lemma computationClaimSentence_poly
    (kind : ComputationClaimKind) (schema : ArithmeticSemisentence 1)
    {input : ℕ → ℕ} (hinput : PolyNatCodes input) :
    PolySentenceCodes (fun n => computationClaimSentence ⟨kind, schema, input n⟩) := by
  let hclaim := (PolyFueled.const kind.godelCode).pair
    ((PolyFueled.const (Encodable.encode schema)).pair hinput.code_poly)
  refine ⟨_, (((PolyFueled.const 1).pair hclaim).succ_comp).of_eq (fun n => ?_)⟩
  rfl

def haltingClaimInput_poly {machines : ℕ → Nat.Partrec.Code} {inputs : ℕ → ℕ}
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs) :
    PolyNatCodes (fun n => haltingClaimInput (machines n) (inputs n)) :=
  ⟨_, (hm.code_poly.pair hi.code_poly).of_eq (fun _ => rfl)⟩

def boundedHaltingClaimInput_poly
    {machines : ℕ → Nat.Partrec.Code} {inputs steps : ℕ → ℕ}
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs)
    (hs : PolyNatCodes steps) :
    PolyNatCodes (fun n => boundedHaltingClaimInput (machines n) (inputs n) (steps n)) :=
  ⟨_, (hm.code_poly.pair (hi.code_poly.pair hs.code_poly)).of_eq (fun _ => rfl)⟩

lemma haltingClaimSentence_poly {input : ℕ → ℕ} (hinput : PolyNatCodes input) :
    PolySentenceCodes (fun n => haltingClaimSentence (input n)) :=
  computationClaimSentence_poly .halting universalHaltingSchema hinput

lemma boundedHaltingClaimSentence_poly {input : ℕ → ℕ} (hinput : PolyNatCodes input) :
    PolySentenceCodes (fun n => boundedHaltingClaimSentence (input n)) :=
  computationClaimSentence_poly .boundedHalting universalBoundedHaltingSchema hinput

lemma inconsistencyClaimSentence_poly {input : ℕ → ℕ} (hinput : PolyNatCodes input) :
    PolySentenceCodes (fun n => inconsistencyClaimSentence (input n)) :=
  computationClaimSentence_poly .inconsistency universalHaltingSchema hinput

lemma consistencyClaimSentence_poly {input : ℕ → ℕ} (hinput : PolyNatCodes input) :
    PolySentenceCodes (fun n => consistencyClaimSentence (input n)) :=
  computationClaimSentence_poly .consistency (∼universalHaltingSchema) hinput

/-! ## The narrow background-theory translation premise -/

/-- A recursively presented arithmetic theory whose proofs of the fixed universal
computation schemas are translated into the corresponding public propositional literals.

The separate bounded-failure field is necessary because FFL supplies weak positive
representation of r.e. predicates, not strong refutation of false r.e. formulas.
Paper node: `thm:pac`, `thm:pazfc`, `thm:incons`, `thm:halts`, `thm:loops`, `thm:dontwait` -/
structure ComputationTheoryPresentation
    (DP : DeductiveProcess) (T : ArithmeticTheory) where
  theory_deltaOne : LO.FirstOrder.Theory.Δ₁ T
  process : DeductiveProcessComputation DP
  halting_enters : ∀ z : ℕ,
    T ⊢ universalHaltingSchema/[↑z] →
      ∃ k, haltingClaimSentence z ∈ DP.D k
  halting_refutes : ∀ z : ℕ,
    T ⊢ ∼(universalHaltingSchema/[↑z]) →
      ∃ k, (∼haltingClaimSentence z) ∈ DP.D k
  boundedHalting_enters : ∀ z : ℕ,
    T ⊢ universalBoundedHaltingSchema/[↑z] →
      ∃ k, boundedHaltingClaimSentence z ∈ DP.D k
  boundedFailure_refutes : ∀ z : ℕ,
    T ⊢ universalBoundedFailureSchema/[↑z] →
      ∃ k, (∼boundedHaltingClaimSentence z) ∈ DP.D k
  inconsistency_enters : ∀ z : ℕ,
    T ⊢ universalHaltingSchema/[↑z] →
      ∃ k, inconsistencyClaimSentence z ∈ DP.D k
  inconsistency_refutesConsistency : ∀ z : ℕ,
    T ⊢ universalHaltingSchema/[↑z] →
      ∃ k, (∼consistencyClaimSentence z) ∈ DP.D k

/-! ## Operational predicate presentations -/

/-- A semidecidable predicate reduced to one fixed repository machine on polynomially
named inputs.
Paper node: `thm:pac`, `thm:pazfc`, `thm:incons`, `thm:halts`, `thm:loops`, `thm:dontwait` -/
structure SemidecidableComputation (truth : ℕ → Prop) where
  machine : Nat.Partrec.Code
  input : ℕ → ℕ
  input_poly : PolyNatCodes input
  truth_iff : ∀ n, truth n ↔ CodeHalts machine (input n)

/-- A decidable predicate reduced to a bounded run of one fixed repository machine.
Paper node: `thm:pac`, `thm:pazfc`, `thm:incons`, `thm:halts`, `thm:loops`, `thm:dontwait` -/
structure BoundedComputation (truth : ℕ → Prop) where
  machine : Nat.Partrec.Code
  input : ℕ → ℕ
  steps : ℕ → ℕ
  input_poly : PolyNatCodes input
  steps_poly : PolyNatCodes steps
  truth_iff : ∀ n, truth n ↔ CodeHaltsWithin machine (input n) (steps n)

/-! ## Constructors for the three MetaLearning boundaries -/

/-- Constructor for the semidecidable-claims boundary from a concrete computation.
Paper node: `thm:pac` -/
noncomputable def representedSemidecidableClaimsOfComputation
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    {truth : ℕ → Prop} (Q : ComputationTheoryPresentation DP T)
    (C : SemidecidableComputation truth) :
    RepresentedSemidecidableClaims DP truth where
  sentence n := haltingClaimSentence (haltingClaimInput C.machine (C.input n))
  sentence_poly := RpnSentenceCodes.ofPolySentenceCodes <| haltingClaimSentence_poly <|
    haltingClaimInput_poly
      ⟨_, PolyFueled.const (Encodable.encode C.machine)⟩ C.input_poly
  provable_of_true n hn := by
    apply Q.halting_enters
    apply (re_complete (T := T) universalCodeHalts_re).mp
    simpa using (C.truth_iff n).mp hn

/-- Constructor for the decidable-claims boundary from a concrete computation.
Paper node: `thm:pac` -/
noncomputable def representedDecidableClaimsOfComputation
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    {truth : ℕ → Prop} (Q : ComputationTheoryPresentation DP T)
    (C : BoundedComputation truth) :
    RepresentedDecidableClaims DP truth where
  sentence n := boundedHaltingClaimSentence
    (boundedHaltingClaimInput C.machine (C.input n) (C.steps n))
  sentence_poly := RpnSentenceCodes.ofPolySentenceCodes <| boundedHaltingClaimSentence_poly <|
    boundedHaltingClaimInput_poly
      ⟨_, PolyFueled.const (Encodable.encode C.machine)⟩ C.input_poly C.steps_poly
  provable_of_true n hn := by
    apply Q.boundedHalting_enters
    apply (re_complete (T := T) universalCodeHaltsWithin_re).mp
    simpa using (C.truth_iff n).mp hn
  disprovable_of_false n hn := by
    apply Q.boundedFailure_refutes
    apply (re_complete (T := T) universalCodeHaltsWithinFailure_re).mp
    intro hb
    apply hn
    apply (C.truth_iff n).mpr
    exact (universalCodeHaltsWithin_claimInput C.machine (C.input n) (C.steps n)).mp hb

/-- Constructor for the inconsistent-theory-claims boundary from a concrete computation.
Paper node: `thm:incons` -/
noncomputable def inconsistentTheoryClaimsOfComputation
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    {inconsistent : ℕ → Prop} (Q : ComputationTheoryPresentation DP T)
    (C : SemidecidableComputation inconsistent) :
    InconsistentTheoryClaims DP inconsistent where
  inconsistencySentence n := inconsistencyClaimSentence
    (haltingClaimInput C.machine (C.input n))
  consistencySentence n := consistencyClaimSentence
    (haltingClaimInput C.machine (C.input n))
  inconsistency_poly := RpnSentenceCodes.ofPolySentenceCodes <| inconsistencyClaimSentence_poly <|
    haltingClaimInput_poly
      ⟨_, PolyFueled.const (Encodable.encode C.machine)⟩ C.input_poly
  consistency_poly := RpnSentenceCodes.ofPolySentenceCodes <| consistencyClaimSentence_poly <|
    haltingClaimInput_poly
      ⟨_, PolyFueled.const (Encodable.encode C.machine)⟩ C.input_poly
  inconsistency_provable n hn := by
    apply Q.inconsistency_enters
    apply (re_complete (T := T) universalCodeHalts_re).mp
    simpa using (C.truth_iff n).mp hn
  consistency_disprovable n hn := by
    apply Q.inconsistency_refutesConsistency
    apply (re_complete (T := T) universalCodeHalts_re).mp
    simpa using (C.truth_iff n).mp hn

/-! ## Sequence-specialized constructors -/

noncomputable def representedHaltingClaims
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T)
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs) :
    RepresentedSemidecidableClaims DP
      (fun n => CodeHalts (machines n) (inputs n)) where
  sentence n := haltingClaimSentence (haltingClaimInput (machines n) (inputs n))
  sentence_poly := RpnSentenceCodes.ofPolySentenceCodes <| haltingClaimSentence_poly (haltingClaimInput_poly hm hi)
  provable_of_true n hn := by
    apply Q.halting_enters
    apply (re_complete (T := T) universalCodeHalts_re).mp
    simpa using hn

noncomputable def representedBoundedHaltingClaims
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T)
    (machines : ℕ → Nat.Partrec.Code) (inputs steps : ℕ → ℕ)
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs)
    (hs : PolyNatCodes steps) :
    RepresentedDecidableClaims DP
      (fun n => CodeHaltsWithin (machines n) (inputs n) (steps n)) where
  sentence n := boundedHaltingClaimSentence
    (boundedHaltingClaimInput (machines n) (inputs n) (steps n))
  sentence_poly := RpnSentenceCodes.ofPolySentenceCodes <| boundedHaltingClaimSentence_poly
    (boundedHaltingClaimInput_poly hm hi hs)
  provable_of_true n hn := by
    apply Q.boundedHalting_enters
    apply (re_complete (T := T) universalCodeHaltsWithin_re).mp
    simpa using hn
  disprovable_of_false n hn := by
    apply Q.boundedFailure_refutes
    apply (re_complete (T := T) universalCodeHaltsWithinFailure_re).mp
    simpa using hn

/-! ## Direct paper-facing consumers -/

/-- Finitistic-consistency belief, with the representation boundary discharged by a
concrete computation.
Paper node: `thm:pac` -/
theorem lic_belief_finitistic_consistency_ofComputation
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    (consistentWithin : ℕ → Prop) (C : BoundedComputation consistentWithin)
    (hconsistent : ∀ n, consistentWithin n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n ((representedDecidableClaimsOfComputation Q C).sentence n)) ≈ₙ
      fun _ => 1 :=
  lic_belief_finitistic_consistency P DP consistentWithin
    (representedDecidableClaimsOfComputation Q C) hconsistent hworld

/--
Paper node: `thm:pazfc` -/
theorem lic_belief_stronger_theory_consistency_ofComputation
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    (strongerConsistentWithin : ℕ → Prop)
    (C : BoundedComputation strongerConsistentWithin)
    (hconsistent : ∀ n, strongerConsistentWithin n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n ((representedDecidableClaimsOfComputation Q C).sentence n)) ≈ₙ
      fun _ => 1 :=
  lic_belief_stronger_theory_consistency P DP strongerConsistentWithin
    (representedDecidableClaimsOfComputation Q C) hconsistent hworld

/--
Paper node: `thm:incons` -/
theorem lic_disbelief_inconsistent_theories_ofComputation
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    (inconsistent : ℕ → Prop) (C : SemidecidableComputation inconsistent)
    (hall : ∀ n, inconsistent n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ((fun n => P n ((inconsistentTheoryClaimsOfComputation Q C).inconsistencySentence n))
        ≈ₙ fun _ => 1) ∧
      ((fun n => P n ((inconsistentTheoryClaimsOfComputation Q C).consistencySentence n))
        ≈ₙ fun _ => 0) :=
  lic_disbelief_inconsistent_theories P DP inconsistent
    (inconsistentTheoryClaimsOfComputation Q C) hall hworld

/--
Paper node: `thm:halts` -/
theorem lic_learns_halting_patterns_ofComputation
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs)
    (hhalts : ∀ n, CodeHalts (machines n) (inputs n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n ((representedHaltingClaims Q machines inputs hm hi).sentence n)) ≈ₙ
      fun _ => 1 :=
  lic_learns_halting_patterns P DP machines inputs
    (representedHaltingClaims Q machines inputs hm hi) hhalts hworld

/--
Paper node: `thm:loops` -/
theorem lic_learns_provable_nonhalting_patterns_ofComputation
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs)
    (hloops : ∀ n, T ⊢ ∼(universalHaltingSchema/[
      ↑(haltingClaimInput (machines n) (inputs n))]))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n ((representedHaltingClaims Q machines inputs hm hi).sentence n)) ≈ₙ
      fun _ => 0 :=
  lic_learns_provable_nonhalting_patterns P DP machines inputs
    (representedHaltingClaims Q machines inputs hm hi)
    (fun n => Q.halting_refutes _ (hloops n)) hworld

/--
Paper node: `thm:dontwait` -/
theorem lic_does_not_anticipate_halting_ofComputation
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs)
    (hh : PolyNatCodes horizons)
    (hnever : ∀ n, ¬CodeHalts (machines n) (inputs n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n
      ((representedBoundedHaltingClaims Q machines inputs horizons hm hi hh).sentence n))
        ≈ₙ fun _ => 0 :=
  lic_does_not_anticipate_halting P DP machines inputs horizons
    (representedBoundedHaltingClaims Q machines inputs horizons hm hi hh)
    hnever hworld

/-! ## Positive and negative path witnesses -/

/-- `N+`: the positive path fires for the repository's everywhere-zero program. -/
lemma computationRepresentation_positive_path
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T) :
    ∃ k, haltingClaimSentence (haltingClaimInput Nat.Partrec.Code.zero 0) ∈ DP.D k := by
  apply Q.halting_enters
  apply (re_complete (T := T) universalCodeHalts_re).mp
  rw [universalCodeHalts_claimInput]
  rw [CodeHalts]
  rw [Part.dom_iff_mem]
  refine ⟨0, Nat.Partrec.Code.evaln_sound (k := 1) ?_⟩
  simp [Nat.Partrec.Code.evaln]

/-- `N+`: zero interpreter fuel supplies a concrete false bounded claim and exercises the
separate complementary-schema/refutation path. -/
lemma computationRepresentation_negative_path
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T) :
    ∃ k, (∼boundedHaltingClaimSentence
      (boundedHaltingClaimInput Nat.Partrec.Code.zero 0 0)) ∈ DP.D k := by
  apply Q.boundedFailure_refutes
  apply (re_complete (T := T) universalCodeHaltsWithinFailure_re).mp
  rw [universalCodeHaltsWithin_claimInput]
  simp [CodeHaltsWithin, Nat.Partrec.Code.evaln]

#print axioms universalCodeHalts_re
#print axioms universalCodeHaltsWithin_computable
#print axioms universalHaltingSchema_spec
#print axioms universalBoundedSchemas_complementary
#print axioms ComputationClaim.godelCode_injective
#print axioms computationClaimSentence_poly
#print axioms representedSemidecidableClaimsOfComputation
#print axioms representedDecidableClaimsOfComputation
#print axioms inconsistentTheoryClaimsOfComputation
#print axioms representedHaltingClaims
#print axioms representedBoundedHaltingClaims
#print axioms lic_belief_finitistic_consistency_ofComputation
#print axioms lic_belief_stronger_theory_consistency_ofComputation
#print axioms lic_disbelief_inconsistent_theories_ofComputation
#print axioms lic_learns_halting_patterns_ofComputation
#print axioms lic_learns_provable_nonhalting_patterns_ofComputation
#print axioms lic_does_not_anticipate_halting_ofComputation
#print axioms computationRepresentation_positive_path
#print axioms computationRepresentation_negative_path

end LogicalInduction
