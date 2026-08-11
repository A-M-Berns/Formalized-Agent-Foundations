import LogicalInduction.Construction.Witnesses.BoundedEvaluation
import LogicalInduction.Properties.MetaLearning
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.Syntax.Predicate.Rew
import Foundation.FirstOrder.Bootstrapping.Syntax.Theory
import Mathlib.Computability.Ackermann

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

/-! ### Bounded halting with a deferred horizon

`thm:pac`, `thm:pazfc` and `thm:dontwait` quantify over *any* computable horizon function
`f`, and the paper's claim names the **term** `⌜f⌝(⌜n⌝)`, leaving the arithmetic schema to
evaluate it.  A bounded claim therefore carries `⌜f⌝` — a constant — paired with the day
`n` unevaluated, so the claim's Gödel name is polynomial in `n` for *every* computable `f`,
not only the polynomial-time ones.

The price is that the positive and negative schemas are no longer exhaustive: if the
horizon program diverges on `n`, neither fires.  They remain mutually exclusive
(`universalBoundedClaims_exclusive`), which is what the deductive-process construction
needs, and for a total `f` — the paper's setting — exactly one of them fires. -/

/-- Decode `z = ⟨⟨machine, input⟩, ⟨horizon program, day⟩⟩` into its machine. -/
def boundedClaimMachine (z : ℕ) : Nat.Partrec.Code :=
  Denumerable.ofNat Nat.Partrec.Code z.unpair.1.unpair.1

/-- Decode `z = ⟨⟨machine, input⟩, ⟨horizon program, day⟩⟩` into its machine input. -/
def boundedClaimInput (z : ℕ) : ℕ := z.unpair.1.unpair.2

/-- Decode `z = ⟨⟨machine, input⟩, ⟨horizon program, day⟩⟩` into its horizon program `⌜f⌝`. -/
def boundedClaimHorizon (z : ℕ) : Nat.Partrec.Code :=
  Denumerable.ofNat Nat.Partrec.Code z.unpair.2.unpair.1

/-- Decode `z = ⟨⟨machine, input⟩, ⟨horizon program, day⟩⟩` into the day the horizon
program is applied to.  It is *not* evaluated in the name. -/
def boundedClaimDay (z : ℕ) : ℕ := z.unpair.2.unpair.2

/-- `⌜machine⌝` halts on `⌜input⌝` within `⌜f⌝(⌜day⌝)` steps: run the horizon program on
the day to obtain the step budget, then run the clocked interpreter under it. -/
def UniversalBoundedHalts (z : ℕ) : Prop :=
  ∃ m ∈ (boundedClaimHorizon z).eval (boundedClaimDay z),
    CodeHaltsWithin (boundedClaimMachine z) (boundedClaimInput z) m

/-- The complementary claim: the horizon term converges and the bounded run fails. -/
def UniversalBoundedFailure (z : ℕ) : Prop :=
  ∃ m ∈ (boundedClaimHorizon z).eval (boundedClaimDay z),
    ¬CodeHaltsWithin (boundedClaimMachine z) (boundedClaimInput z) m

/-- Both deferred-horizon claims are recursively enumerable: semi-decide by running the
horizon program to convergence and then testing the (decidable) clocked run against `b`.
Unlike the evaluated-horizon schema neither is *computable*, because the horizon term may
diverge — but r.e. is all that FFL's `re_complete` consumes. -/
private lemma universalBoundedRun_re (b : Bool) :
    REPred (fun z : ℕ => ∃ m ∈ (boundedClaimHorizon z).eval (boundedClaimDay z),
      (Nat.Partrec.Code.evaln m (boundedClaimMachine z) (boundedClaimInput z)).isSome = b) := by
  have hmachP : Primrec boundedClaimMachine :=
    (Primrec.ofNat Nat.Partrec.Code).comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
  have hinputP : Primrec boundedClaimInput :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hhorP : Primrec boundedClaimHorizon :=
    (Primrec.ofNat Nat.Partrec.Code).comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hdayP : Primrec boundedClaimDay :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have heval : Partrec fun z : ℕ => (boundedClaimHorizon z).eval (boundedClaimDay z) :=
    Nat.Partrec.Code.eval_part.comp hhorP.to_comp hdayP.to_comp
  have hisSome : Primrec fun p : ℕ × ℕ =>
      (Nat.Partrec.Code.evaln p.2 (boundedClaimMachine p.1) (boundedClaimInput p.1)).isSome :=
    Primrec.option_isSome.comp
      (Nat.Partrec.Code.primrec_evaln.comp
        ((Primrec.snd.pair (hmachP.comp Primrec.fst)).pair (hinputP.comp Primrec.fst)))
  have htest : Computable fun p : ℕ × ℕ =>
      (if (Nat.Partrec.Code.evaln p.2 (boundedClaimMachine p.1)
            (boundedClaimInput p.1)).isSome = b then some 0 else none : Option ℕ) :=
    (Primrec.ite (Primrec.eq.comp hisSome (Primrec.const b))
      (Primrec.const (some 0)) (Primrec.const none)).to_comp
  refine (Partrec.dom_re (heval.bind (Computable.ofOption htest).to₂)).of_eq fun z => ?_
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨m, hm, ha⟩ := Part.mem_bind_iff.mp ha
    refine ⟨m, hm, ?_⟩
    by_contra hb
    rw [if_neg hb] at ha
    simp at ha
  · rintro ⟨m, hm, hb⟩
    exact ⟨0, Part.mem_bind_iff.mpr ⟨m, hm, by rw [if_pos hb]; simp⟩⟩

lemma universalBoundedHalts_re : REPred UniversalBoundedHalts :=
  (universalBoundedRun_re true).of_eq fun _ => Iff.rfl

lemma universalBoundedFailure_re : REPred UniversalBoundedFailure :=
  (universalBoundedRun_re false).of_eq fun _ => by
    simp only [UniversalBoundedFailure, CodeHaltsWithin, Bool.not_eq_true]

/-- Determinism of the horizon program makes the two deferred claims mutually exclusive. -/
lemma universalBoundedClaims_exclusive (z : ℕ) :
    ¬(UniversalBoundedHalts z ∧ UniversalBoundedFailure z) := by
  rintro ⟨⟨m, hm, hpos⟩, ⟨m', hm', hneg⟩⟩
  cases Part.mem_unique hm hm'
  exact hneg hpos

/-- FFL's quoted arithmetic schema for universal unbounded halting. -/
noncomputable def universalHaltingSchema : ArithmeticSemisentence 1 :=
  codeOfREPred UniversalCodeHalts

/-- FFL's quoted arithmetic schema for bounded halting at a deferred horizon. -/
noncomputable def universalBoundedHaltingSchema : ArithmeticSemisentence 1 :=
  codeOfREPred UniversalBoundedHalts

/-- The complementary FFL schema certifying failure of a bounded run. -/
noncomputable def universalBoundedFailureSchema : ArithmeticSemisentence 1 :=
  codeOfREPred UniversalBoundedFailure

/-- The unbounded schema has exactly the intended standard-model meaning. -/
lemma universalHaltingSchema_spec (z : ℕ) :
    universalHaltingSchema.Evalb ![z] ↔ UniversalCodeHalts z :=
  codeOfREPred_spec universalCodeHalts_re (x := z)

/-- The bounded schema has exactly the intended standard-model meaning. -/
lemma universalBoundedHaltingSchema_spec (z : ℕ) :
    universalBoundedHaltingSchema.Evalb ![z] ↔ UniversalBoundedHalts z :=
  codeOfREPred_spec universalBoundedHalts_re (x := z)

/-- The failure schema has exactly the intended standard-model meaning. -/
lemma universalBoundedFailureSchema_spec (z : ℕ) :
    universalBoundedFailureSchema.Evalb ![z] ↔ UniversalBoundedFailure z :=
  codeOfREPred_spec universalBoundedFailure_re (x := z)

/-- The two bounded schemas never both hold: the horizon term has at most one value. -/
lemma universalBoundedSchemas_exclusive (z : ℕ) :
    ¬(universalBoundedHaltingSchema.Evalb ![z] ∧
      universalBoundedFailureSchema.Evalb ![z]) := by
  rw [universalBoundedHaltingSchema_spec, universalBoundedFailureSchema_spec]
  exact universalBoundedClaims_exclusive z

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

/-- Pair a repository machine code, an input, and the **unevaluated** horizon term
`⌜f⌝(⌜day⌝)`.  Nothing is run: `horizon` is the program `⌜f⌝` and `day` is the numeral. -/
def boundedHaltingClaimInput (machine : Nat.Partrec.Code) (input : ℕ)
    (horizon : Nat.Partrec.Code) (day : ℕ) : ℕ :=
  Nat.pair (Nat.pair (Encodable.encode machine) input)
    (Nat.pair (Encodable.encode horizon) day)

@[simp] theorem universalCodeHalts_claimInput (machine : Nat.Partrec.Code) (input : ℕ) :
    UniversalCodeHalts (haltingClaimInput machine input) ↔ CodeHalts machine input := by
  simp [UniversalCodeHalts, haltingClaimInput, CodeHalts]

/-- The four projections invert the packing. -/
lemma boundedClaimInput_decode (machine : Nat.Partrec.Code) (input : ℕ)
    (horizon : Nat.Partrec.Code) (day : ℕ) :
    boundedClaimMachine (boundedHaltingClaimInput machine input horizon day) = machine ∧
      boundedClaimInput (boundedHaltingClaimInput machine input horizon day) = input ∧
      boundedClaimHorizon (boundedHaltingClaimInput machine input horizon day) = horizon ∧
      boundedClaimDay (boundedHaltingClaimInput machine input horizon day) = day := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [boundedClaimMachine, boundedClaimInput, boundedClaimHorizon, boundedClaimDay,
      boundedHaltingClaimInput]

/-- The deferred claim is true exactly when the machine halts within the horizon
program's *actual* value on the day. -/
lemma universalBoundedHalts_claimInput (machine : Nat.Partrec.Code) (input : ℕ)
    (horizon : Nat.Partrec.Code) (day steps : ℕ) (hsteps : steps ∈ horizon.eval day) :
    UniversalBoundedHalts (boundedHaltingClaimInput machine input horizon day) ↔
      CodeHaltsWithin machine input steps := by
  obtain ⟨hm, hi, hh, hd⟩ := boundedClaimInput_decode machine input horizon day
  simp only [UniversalBoundedHalts, hm, hi, hh, hd]
  constructor
  · rintro ⟨m, hmem, hrun⟩
    rwa [Part.mem_unique hmem hsteps] at hrun
  · exact fun h => ⟨steps, hsteps, h⟩

/-- The complementary reading of the same claim input. -/
lemma universalBoundedFailure_claimInput (machine : Nat.Partrec.Code) (input : ℕ)
    (horizon : Nat.Partrec.Code) (day steps : ℕ) (hsteps : steps ∈ horizon.eval day) :
    UniversalBoundedFailure (boundedHaltingClaimInput machine input horizon day) ↔
      ¬CodeHaltsWithin machine input steps := by
  obtain ⟨hm, hi, hh, hd⟩ := boundedClaimInput_decode machine input horizon day
  simp only [UniversalBoundedFailure, hm, hi, hh, hd]
  constructor
  · rintro ⟨m, hmem, hrun⟩
    rwa [Part.mem_unique hmem hsteps] at hrun
  · exact fun h => ⟨steps, hsteps, h⟩

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

/-- The deferred-horizon claim name is polynomial in the day for **every** computable
horizon: `⌜f⌝` enters as a constant and the day enters unevaluated.  No hypothesis on `f`
appears — this is the whole point of the deferred schema. -/
def boundedHaltingClaimInput_poly
    {machines : ℕ → Nat.Partrec.Code} {inputs : ℕ → ℕ}
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs)
    (horizon : Nat.Partrec.Code) :
    PolyNatCodes (fun n => boundedHaltingClaimInput (machines n) (inputs n) horizon n) :=
  ⟨_, ((hm.code_poly.pair hi.code_poly).pair
    ((PolyFueled.const (Encodable.encode horizon)).pair PolyFueled.id)).of_eq (fun _ => rfl)⟩

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

/-- The paper's `f` — an arbitrary computable step budget, presented by the program `⌜f⌝`
that computes it.  The program is a *constant* in the day-indexed claim name, so no
efficiency hypothesis on `f` is needed anywhere; `ComputableHorizon.of` shows every
computable `f` has one.
Paper node: `thm:pac`, `thm:pazfc`, `thm:dontwait` -/
structure ComputableHorizon (steps : ℕ → ℕ) where
  program : Nat.Partrec.Code
  program_spec : ∀ n, steps n ∈ program.eval n

/-- **Every** computable step budget is admissible — the paper's "let `f` be any computable
function", with no polynomial restriction.  `N+` for `ComputableHorizon`. -/
noncomputable def ComputableHorizon.of {steps : ℕ → ℕ} (h : Computable steps) :
    ComputableHorizon steps :=
  have hc : ∃ c : Nat.Partrec.Code, c.eval = (steps : ℕ →. ℕ) :=
    Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp h)
  ⟨hc.choose, fun n => by rw [hc.choose_spec]; exact Part.mem_some _⟩

/-- A concrete `N+` witnessing that the deferred horizon is a *strict* strengthening: the
diagonal Ackermann function is a legitimate `f`, and it is not even primitive recursive,
so `PolyNatCodes` provably rejects it (`not_polyNatCodes_ack`). -/
noncomputable def ComputableHorizon.ackermann : ComputableHorizon (fun n => _root_.ack n n) :=
  .of (_root_.computable₂_ack.comp Computable.id Computable.id)

/-- The evaluated-horizon schema could only ever name a `PolyNatCodes` step budget, and that
class does not contain the diagonal Ackermann function — which `ComputableHorizon.ackermann`
does.  This is the exact content of restoring the paper's "any computable `f`". -/
lemma not_polyNatCodes_ack : ¬Nonempty (PolyNatCodes (fun n => _root_.ack n n)) := by
  rintro ⟨⟨_, hpoly⟩⟩
  exact _root_.not_primrec_ack_self hpoly.primrec

/-- A decidable predicate reduced to a bounded run of one fixed repository machine, the
step budget being an arbitrary computable `f` named by its program.
Paper node: `thm:pac`, `thm:pazfc`, `thm:incons`, `thm:halts`, `thm:loops`, `thm:dontwait` -/
structure BoundedComputation (truth : ℕ → Prop) where
  machine : Nat.Partrec.Code
  input : ℕ → ℕ
  input_poly : PolyNatCodes input
  steps : ℕ → ℕ
  horizon : ComputableHorizon steps
  truth_iff : ∀ n, truth n ↔ CodeHaltsWithin machine (input n) (steps n)

/-! ## Non-vacuity witnesses for the operational presentations -/

/-- Halting on exactly the positive inputs, as a partial function. -/
private def positiveHaltPartial : ℕ →. ℕ := fun n => Part.assert (0 < n) fun _ => Part.some 0

private lemma positiveHaltPartial_partrec : Nat.Partrec positiveHaltPartial := by
  rw [← Partrec.nat_iff]
  have hdec : PrimrecPred fun n : ℕ => 0 < n :=
    Primrec.nat_lt.comp (Primrec.const 0) Primrec.id
  obtain ⟨_, hp⟩ := hdec
  have hre : REPred fun n : ℕ => 0 < n :=
    ComputablePred.to_re (ComputablePred.computable_iff.mpr ⟨_, hp.to_comp, by funext n; simp⟩)
  refine (hre.map (Computable.const (0 : ℕ)).to₂).of_eq (fun n => Part.ext fun x => ?_)
  simp [positiveHaltPartial, Part.mem_assert_iff, eq_comm]

/-- A repository machine halting on exactly the positive inputs.  Existence of a code for a
partial recursive function is `Nat.Partrec.Code.exists_code`; the machine itself is not a
closed term, which is why the definition is `noncomputable`. -/
noncomputable def positiveHaltMachine : Nat.Partrec.Code :=
  (Nat.Partrec.Code.exists_code.mp positiveHaltPartial_partrec).choose

lemma positiveHaltMachine_halts_iff (n : ℕ) : CodeHalts positiveHaltMachine n ↔ 0 < n := by
  have hspec : positiveHaltMachine.eval = positiveHaltPartial :=
    (Nat.Partrec.Code.exists_code.mp positiveHaltPartial_partrec).choose_spec
  simp [CodeHalts, hspec, positiveHaltPartial, Part.assert]

/-- **N+.** The semidecidable-computation premise is inhabited, with a genuinely
index-varying truth predicate: the machine halts on input `n` exactly when `n` is
positive, so `truth` is neither identically true nor identically false.  Kind `N+`,
provenance (a): every field is discharged in-project, with no operational hypothesis.
Paper node: `thm:incons` -/
noncomputable def ordinarySemidecidableComputation :
    SemidecidableComputation (fun n => 0 < n) where
  machine := positiveHaltMachine
  input n := n
  input_poly := ⟨_, PolyFueled.id⟩
  truth_iff n := (positiveHaltMachine_halts_iff n).symm

/-- **N+.** The bounded-computation premise is inhabited, with a genuinely index-varying
truth predicate: `Code.zero` on input `0` finishes within `n` interpreter steps exactly
when `n` is positive (a zero clock always fails).  The horizon is the identity `f n = n`,
named by a program via `ComputableHorizon.of`.  Kind `N+`, provenance (a): every field is
discharged in-project, with no operational hypothesis.
Paper node: `thm:pac`, `thm:pazfc` -/
noncomputable def ordinaryBoundedComputation : BoundedComputation (fun n => 0 < n) where
  machine := Nat.Partrec.Code.zero
  input _ := 0
  input_poly := ⟨_, PolyFueled.const 0⟩
  steps n := n
  horizon := .of Computable.id
  truth_iff n := by
    cases n with
    | zero => simp [CodeHaltsWithin, Nat.Partrec.Code.evaln]
    | succ k => simp [CodeHaltsWithin, Nat.Partrec.Code.evaln]

#print axioms ordinarySemidecidableComputation
#print axioms ordinaryBoundedComputation

/-! ## Constructors for the three MetaLearning boundaries -/

/-- Constructor for the decidable-claims boundary from a concrete computation.
Paper node: `thm:pac` -/
noncomputable def representedDecidableClaimsOfComputation
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    {truth : ℕ → Prop} (Q : ComputationTheoryPresentation DP T)
    (C : BoundedComputation truth) :
    RepresentedDecidableClaims DP truth where
  sentence n := boundedHaltingClaimSentence
    (boundedHaltingClaimInput C.machine (C.input n) C.horizon.program n)
  sentence_poly := RpnSentenceCodes.ofPolySentenceCodes <| boundedHaltingClaimSentence_poly <|
    boundedHaltingClaimInput_poly
      ⟨_, PolyFueled.const (Encodable.encode C.machine)⟩ C.input_poly C.horizon.program
  provable_of_true n hn := by
    apply Q.boundedHalting_enters
    apply (re_complete (T := T) universalBoundedHalts_re).mp
    exact (universalBoundedHalts_claimInput _ _ _ _ _ (C.horizon.program_spec n)).mpr
      ((C.truth_iff n).mp hn)
  disprovable_of_false n hn := by
    apply Q.boundedFailure_refutes
    apply (re_complete (T := T) universalBoundedFailure_re).mp
    exact (universalBoundedFailure_claimInput _ _ _ _ _ (C.horizon.program_spec n)).mpr
      (fun hb => hn ((C.truth_iff n).mpr hb))

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

/-- The `thm:dontwait` claim family: `⌜qₙ⌝ halts on ⌜yₙ⌝ within ⌜f⌝(⌜n⌝) steps`, with the
horizon term deferred so that no growth bound on `f` is needed. -/
noncomputable def representedBoundedHaltingClaims
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T)
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs)
    (hh : ComputableHorizon horizons) :
    RepresentedDecidableClaims DP
      (fun n => CodeHaltsWithin (machines n) (inputs n) (horizons n)) where
  sentence n := boundedHaltingClaimSentence
    (boundedHaltingClaimInput (machines n) (inputs n) hh.program n)
  sentence_poly := RpnSentenceCodes.ofPolySentenceCodes <| boundedHaltingClaimSentence_poly
    (boundedHaltingClaimInput_poly hm hi hh.program)
  provable_of_true n hn := by
    apply Q.boundedHalting_enters
    apply (re_complete (T := T) universalBoundedHalts_re).mp
    exact (universalBoundedHalts_claimInput _ _ _ _ _ (hh.program_spec n)).mpr hn
  disprovable_of_false n hn := by
    apply Q.boundedFailure_refutes
    apply (re_complete (T := T) universalBoundedFailure_re).mp
    exact (universalBoundedFailure_claimInput _ _ _ _ _ (hh.program_spec n)).mpr hn

/-! ## Direct paper-facing consumers -/

/-- Finitistic-consistency belief, with the representation boundary discharged by a
concrete computation.  The horizon `f` of `C` is an arbitrary computable function, named in
the claim by its program (`ComputableHorizon`) and left unevaluated — the paper's class.
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

/-- Same statement and same arbitrary-computable-horizon class as `thm:pac`; only the
supplied finite-consistency predicate differs.
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

/-- The horizon sequence is arbitrary computable — `hh` names its program rather than
bounding its growth — which is the paper's "let `f` be any computable function".
Paper node: `thm:dontwait` -/
theorem lic_does_not_anticipate_halting_ofComputation
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T)
    (P : History) [IsLogicalInductor P DP]
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (hm : PolyMachineCodes machines) (hi : PolyNatCodes inputs)
    (hh : ComputableHorizon horizons)
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

/-- `N+`: the everywhere-zero program as horizon supplies a concrete false bounded claim
(zero interpreter fuel) and exercises the separate complementary-schema/refutation path. -/
lemma computationRepresentation_negative_path
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (Q : ComputationTheoryPresentation DP T) :
    ∃ k, (∼boundedHaltingClaimSentence
      (boundedHaltingClaimInput Nat.Partrec.Code.zero 0 Nat.Partrec.Code.zero 0)) ∈ DP.D k := by
  apply Q.boundedFailure_refutes
  apply (re_complete (T := T) universalBoundedFailure_re).mp
  refine (universalBoundedFailure_claimInput _ _ _ _ 0 ?_).mpr ?_
  · exact Part.mem_some 0
  · simp [CodeHaltsWithin, Nat.Partrec.Code.evaln]

#print axioms universalCodeHalts_re
#print axioms universalBoundedHalts_re
#print axioms universalBoundedFailure_re
#print axioms universalHaltingSchema_spec
#print axioms universalBoundedSchemas_exclusive
#print axioms ComputableHorizon.ackermann
#print axioms not_polyNatCodes_ack
#print axioms ComputationClaim.godelCode_injective
#print axioms computationClaimSentence_poly
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
