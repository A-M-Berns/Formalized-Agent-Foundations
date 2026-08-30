import LogicalInduction.Construction.Witnesses.BoundedEvaluation
import LogicalInduction.Properties.MetaLearning
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.Syntax.Predicate.Rew
import Foundation.FirstOrder.Bootstrapping.Syntax.Theory
import Mathlib.Computability.Ackermann
import LogicalInduction.Framework.WriteOut
import LogicalInduction.Framework.SubstOccurrence

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
decidable claim is *not* refutable from weak representation, so every refutation field of
`ComputationTheoryPresentation` consumes the literal negation `T ⊢ ∼σ` of the same sentence
`σ` its positive partner consumes — never a second, independent r.e. schema.  Supplying
those negative literals is the job of the paper's own representability premise
(`Framework/RepresentsComputations.lean`), exercised in `ComputationRepresented.lean`; the
bounded-halting *claim families* of `thm:pac`, `thm:pazfc` and `thm:dontwait` therefore live
there, over `paperTheoryDP`, rather than here.
-/

namespace LogicalInduction

open LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## Foundation bridge: soundness-free Σ₁ completeness

This file is the development's only importer of `Foundation.FirstOrder.Arithmetic.R0.Representation`
and sits upstream of every other consumer of weak representation, so the shared bridge
lemma lives here. -/

/-- Weak representation of an r.e. predicate, **positive direction only**.

Foundation's `re_complete` is an `Iff` stated under `[T.SoundOnHierarchy 𝚺 1]`, but only its
`.mpr` direction (`T ⊢ … → A x`) consumes soundness: the forward direction is
`sigma_one_completeness`, which needs nothing beyond `[𝗥₀ ⪯ T]`.  Every call site in this
development that only pushes a *true* r.e. fact into `T` should use this lemma, so that the
soundness instance does not propagate through the syntax layer.

Kind `C` (composition).  Provenance: (b) Foundation citation —
`sigma_one_completeness` (`R0/Basic.lean:143`) and `codeOfREPred_spec`
(`R0/Representation.lean:247`); the proof is `re_complete`'s own forward branch with the
soundness instance dropped. -/
lemma re_complete_mp {T : ArithmeticTheory} [𝗥₀ ⪯ T] {A : ℕ → Prop} (hp : REPred A) {x : ℕ} :
    A x → T ⊢ (codeOfREPred A)/[‘↑x’] := fun h =>
  sigma_one_completeness (by simp [codeOfREPred, codeOfPartrec'])
    (by simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton] using
      (codeOfREPred_spec hp (x := x)).mpr h)

/-! ## Universal arithmetic computation predicates -/

/-- Decode the left component as a repository program — from its **source** encoding
(`Code.ofSource`, `Framework/CodeSource.lean`), not from `Encodable.encode` — and run it on
the right component.  The decoding happens *inside* the represented computation, so the
schema instance names the source and the machine is recovered by the arithmetic. -/
def UniversalCodeHalts (z : ℕ) : Prop :=
  ((Nat.Partrec.Code.ofSource z.unpair.1).eval z.unpair.2).Dom

/-- The universal unbounded halting predicate is recursively enumerable. -/
lemma universalCodeHalts_re : REPred UniversalCodeHalts := by
  apply Partrec.dom_re
  exact Nat.Partrec.Code.eval_part.comp
    (Nat.Partrec.Code.ofSource_primrec.comp
      (Primrec.fst.comp Primrec.unpair)).to_comp
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
  Nat.Partrec.Code.ofSource z.unpair.1.unpair.1

/-- Decode `z = ⟨⟨machine, input⟩, ⟨horizon program, day⟩⟩` into its machine input. -/
def boundedClaimInput (z : ℕ) : ℕ := z.unpair.1.unpair.2

/-- Decode `z = ⟨⟨machine, input⟩, ⟨horizon program, day⟩⟩` into its horizon program `⌜f⌝`. -/
def boundedClaimHorizon (z : ℕ) : Nat.Partrec.Code :=
  Nat.Partrec.Code.ofSource z.unpair.2.unpair.1

/-- Decode `z = ⟨⟨machine, input⟩, ⟨horizon program, day⟩⟩` into the day the horizon
program is applied to.  It is *not* evaluated in the name. -/
def boundedClaimDay (z : ℕ) : ℕ := z.unpair.2.unpair.2

/-- `⌜machine⌝` halts on `⌜input⌝` within `⌜f⌝(⌜day⌝)` steps: run the horizon program on
the day to obtain the step budget, then run the clocked interpreter under it. -/
def UniversalBoundedHalts (z : ℕ) : Prop :=
  ∃ m ∈ (boundedClaimHorizon z).eval (boundedClaimDay z),
    CodeHaltsWithin (boundedClaimMachine z) (boundedClaimInput z) m

/-- The deferred-horizon claim is recursively enumerable: semi-decide by running the
horizon program to convergence and then testing the (decidable) clocked run against `b`.
Unlike the evaluated-horizon schema it is not *computable*, because the horizon term may
diverge — but r.e. is all that FFL's `re_complete` consumes. -/
private lemma universalBoundedRun_re (b : Bool) :
    REPred (fun z : ℕ => ∃ m ∈ (boundedClaimHorizon z).eval (boundedClaimDay z),
      (Nat.Partrec.Code.evaln m (boundedClaimMachine z) (boundedClaimInput z)).isSome = b) := by
  have hmachP : Primrec boundedClaimMachine :=
    Nat.Partrec.Code.ofSource_primrec.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
  have hinputP : Primrec boundedClaimInput :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hhorP : Primrec boundedClaimHorizon :=
    Nat.Partrec.Code.ofSource_primrec.comp
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

/-- FFL's quoted arithmetic schema for universal unbounded halting. -/
noncomputable def universalHaltingSchema : ArithmeticSemisentence 1 :=
  codeOfREPred UniversalCodeHalts

/-- FFL's quoted arithmetic schema for bounded halting at a deferred horizon. -/
noncomputable def universalBoundedHaltingSchema : ArithmeticSemisentence 1 :=
  codeOfREPred UniversalBoundedHalts

/-- The unbounded schema has exactly the intended standard-model meaning. -/
lemma universalHaltingSchema_spec (z : ℕ) :
    universalHaltingSchema.Evalb ![z] ↔ UniversalCodeHalts z :=
  codeOfREPred_spec universalCodeHalts_re (x := z)

/-- The bounded schema has exactly the intended standard-model meaning. -/
lemma universalBoundedHaltingSchema_spec (z : ℕ) :
    universalBoundedHaltingSchema.Evalb ![z] ↔ UniversalBoundedHalts z :=
  codeOfREPred_spec universalBoundedHalts_re (x := z)

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

/-- Pair a repository machine's **source** number and its input without running the machine.
The name is `Code.sourceNat`, linear in the machine's syntax tree — see the representation
note at `DigitMachineCodes`. -/
def haltingClaimInput (machine : Nat.Partrec.Code) (input : ℕ) : ℕ :=
  Nat.pair (Nat.Partrec.Code.sourceNat machine) input

/-- Pair a repository machine code, an input, and the **unevaluated** horizon term
`⌜f⌝(⌜day⌝)`.  Nothing is run: `horizon` is the program `⌜f⌝` and `day` is the numeral. -/
def boundedHaltingClaimInput (machine : Nat.Partrec.Code) (input : ℕ)
    (horizon : Nat.Partrec.Code) (day : ℕ) : ℕ :=
  Nat.pair (Nat.pair (Nat.Partrec.Code.sourceNat machine) input)
    (Nat.pair (Nat.Partrec.Code.sourceNat horizon) day)

@[simp] lemma universalCodeHalts_claimInput (machine : Nat.Partrec.Code) (input : ℕ) :
    UniversalCodeHalts (haltingClaimInput machine input) ↔ CodeHalts machine input := by
  simp [UniversalCodeHalts, haltingClaimInput, CodeHalts,
    Nat.Partrec.Code.ofSource_sourceNat]

/-- The four projections invert the packing. -/
lemma boundedClaimInput_decode (machine : Nat.Partrec.Code) (input : ℕ)
    (horizon : Nat.Partrec.Code) (day : ℕ) :
    boundedClaimMachine (boundedHaltingClaimInput machine input horizon day) = machine ∧
      boundedClaimInput (boundedHaltingClaimInput machine input horizon day) = input ∧
      boundedClaimHorizon (boundedHaltingClaimInput machine input horizon day) = horizon ∧
      boundedClaimDay (boundedHaltingClaimInput machine input horizon day) = day := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [boundedClaimMachine, boundedClaimInput, boundedClaimHorizon, boundedClaimDay,
      boundedHaltingClaimInput, Nat.Partrec.Code.ofSource_sourceNat]

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

/-! ## The whole-value naming classes — strictness foils, not the paper's class

Neither structure below renders `def:ec`.  Both bound the *numeric value* of the name, which
is what a poly-time writer of the name's **symbols** does not bound: `def:ec` meters the time
to write an object out (tex:753-755, explicitly at tex:1931-1933), so a name of `poly n`
symbols and magnitude up to `2^poly(n)` is admissible.  They are retained only as the foils
that make the write-out classes provably wider — `not_polyNatCodes_ack`,
`bigDigits_two_pow_not_polyNatCodes`, `digitMachineCodes_nest_not_polyMachineCodes` — and
carry no `Paper node` line for that reason.  The paper's class for machine names is
`DigitMachineCodes` (`Framework/WriteOut.lean`); for naturals it is `BigDigits`. -/

/-- Whole-value polynomial naming of a machine sequence: the machine's *source* number
`Code.sourceNat` is itself poly-fueled, not merely its digits.  A strictness foil for
`DigitMachineCodes`; see the section note. -/
structure PolyMachineCodes (machines : ℕ → Nat.Partrec.Code) where
  code : Nat.Partrec.Code
  code_poly : PolyFueled code (fun n => Nat.Partrec.Code.sourceNat (machines n))

/-- Whole-value polynomial naming of a natural-number sequence.  A strictness foil for
`BigDigits`; see the section note. -/
structure PolyNatCodes (values : ℕ → ℕ) where
  code : Nat.Partrec.Code
  code_poly : PolyFueled code values

/-- The claim name is assembled from the machine code, the schema and the input by
`Nat.pair` and `+1` alone — nothing reads the value back — so digit access to the parts
gives digit access to the whole.  This is the write-out rendering of the paper's e.c.
requirement: polynomially many digits, value free to be exponential. -/
lemma computationClaimSentence_digits
    (kind : ComputationClaimKind) (schema : ArithmeticSemisentence 1)
    {input : ℕ → ℕ} (hinput : BigDigits input) :
    DigitSentenceCodes (fun n => computationClaimSentence ⟨kind, schema, input n⟩) := by
  have hclaim := (BigDigits.const kind.godelCode).natPair
    ((BigDigits.const (Encodable.encode schema)).natPair hinput)
  exact ((BigDigits.const 1).natPair hclaim).succ.of_eq (fun _ => rfl)

/-- Write-out access to the packed `⟨⌜mₙ⌝, xₙ⟩` machine/input name.

**Who uses this.**  Two lanes, for two different reasons.  `thm:incons`
(`inconsistentTheoryClaimsOfComputation` below) still runs on the tag-keyed atom over
`theoremDP`, where this is the claim *name*.  And since the R5-F08 repair it is again live
for `thm:halts`/`thm:loops`: those endpoints are stated over `paperTheoryDP` at the fixed
`universalHaltingSchema`, and the pair is written *into the sentence* as the compact numeral
`binNumeral (haltingClaimInput (machines n) (inputs n))`, whose symbol run this certificate
is what supplies (`representedHaltingClaims`, `ComputationRepresented.lean`).  So `hm` and
`hi` are load-bearing on the `def:ec` obligation there, not merely on a computability step.

The superseded reading — machine and input hidden *inside* a `codeOfREPred` schema, with
`hm`/`hi` consumed only by an r.e.-ness step — was extensional and named no machine; see the
header of `ComputationRepresented.lean`. -/
lemma haltingClaimInput_digits {machines : ℕ → Nat.Partrec.Code} {inputs : ℕ → ℕ}
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs) :
    BigDigits (fun n => haltingClaimInput (machines n) (inputs n)) :=
  (hm.natPair hi).of_eq (fun _ => rfl)

/-- The deferred-horizon claim name is write-out in the day for **every** computable
horizon: `⌜f⌝` enters as a constant and the day enters unevaluated.  No hypothesis on `f`
appears — this is the whole point of the deferred schema. -/
lemma boundedHaltingClaimInput_digits
    {machines : ℕ → Nat.Partrec.Code} {inputs : ℕ → ℕ}
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (horizon : Nat.Partrec.Code) :
    BigDigits (fun n => boundedHaltingClaimInput (machines n) (inputs n) horizon n) :=
  ((hm.natPair hi).natPair
    ((BigDigits.const (Nat.Partrec.Code.sourceNat horizon)).natPair
      (BigDigits.of_polyFueled PolyFueled.id))).of_eq (fun _ => rfl)

/-- **No consumer as of the `thm:halts`/`thm:loops` migration.**  This was the claim-sentence
generator for the unbounded halting lane over `theoremDP`; that lane is now stated over
`paperTheoryDP` at the day-indexed schema, whose sentences are emitted by
`schemaDayClaimSentence_bigSentenceCodes` (`ComputationRepresented.lean`) instead.  Retained
rather than deleted, pending a consolidation ruling.  `boundedHaltingClaimSentence_digits`
below is orphaned the same way, by the earlier bounded-lane migration; the two
`thm:incons` generators (`inconsistencyClaimSentence_digits`,
`consistencyClaimSentence_digits`) are still live, at
`inconsistentTheoryClaimsOfComputation`. -/
lemma haltingClaimSentence_digits {input : ℕ → ℕ} (hinput : BigDigits input) :
    DigitSentenceCodes (fun n => haltingClaimSentence (input n)) :=
  computationClaimSentence_digits .halting universalHaltingSchema hinput

lemma boundedHaltingClaimSentence_digits {input : ℕ → ℕ} (hinput : BigDigits input) :
    DigitSentenceCodes (fun n => boundedHaltingClaimSentence (input n)) :=
  computationClaimSentence_digits .boundedHalting universalBoundedHaltingSchema hinput

lemma inconsistencyClaimSentence_digits {input : ℕ → ℕ} (hinput : BigDigits input) :
    DigitSentenceCodes (fun n => inconsistencyClaimSentence (input n)) :=
  computationClaimSentence_digits .inconsistency universalHaltingSchema hinput

lemma consistencyClaimSentence_digits {input : ℕ → ℕ} (hinput : BigDigits input) :
    DigitSentenceCodes (fun n => consistencyClaimSentence (input n)) :=
  computationClaimSentence_digits .consistency (∼universalHaltingSchema) hinput

/-! ## The narrow background-theory translation premise -/

/-- A recursively presented arithmetic theory whose proofs of the fixed universal
computation schemas are translated into the corresponding public propositional literals.

Every field pair is a *literal complement over one sentence*: the refutation fields consume
`T ⊢ ∼σ` for the same `σ` the positive field consumes, never a second, independent r.e.
schema.  That is what lets the constructed process
(`ComputationDP.theoremPresentation`) keep a consistent world at every stage from
consistency of `T` alone.  The bounded lane's *supply* of those negative literals is the
paper's representability premise, not weak Σ₁-representation: see
`ComputationRepresented.lean`.
Paper node: `thm:pac`, `thm:pazfc`, `thm:incons`, `thm:halts`, `thm:loops`, `thm:dontwait` -/
structure ComputationTheoryPresentation
    (DP : DeductiveProcess) (T : ArithmeticTheory) where
  theory_deltaOne : LO.FirstOrder.Theory.Δ₁ T
  process : DeductiveProcessComputation DP
  halting_enters : ∀ z : ℕ,
    T ⊢ universalHaltingSchema/[↑z] →
      ∃ k, haltingClaimSentence z ∈ DP.D k
  /-- **No consumer as of the `thm:halts`/`thm:loops` migration.**  The only endpoint that
  read this field was the `theoremDP` form of `thm:loops`; that endpoint is now stated over
  `paperTheoryDP` at the day-indexed halting schema
  (`Construction/Witnesses/ComputationRepresented.lean`) and gets its negative literal from
  its own `hloops` premise instead.  The field is still *discharged* — by
  `theoremPresentation` in `ComputationDP.lean` and by `ProductDefinition.lean` — and is
  still frozen in `AxiomAudit.lean`'s `#assert_fields` block, so nothing is broken; it is
  retained deliberately, pending a consolidation ruling on whether the field stays. -/
  halting_refutes : ∀ z : ℕ,
    T ⊢ ∼(universalHaltingSchema/[↑z]) →
      ∃ k, (∼haltingClaimSentence z) ∈ DP.D k
  boundedHalting_enters : ∀ z : ℕ,
    T ⊢ universalBoundedHaltingSchema/[↑z] →
      ∃ k, boundedHaltingClaimSentence z ∈ DP.D k
  boundedFailure_refutes : ∀ z : ℕ,
    T ⊢ ∼(universalBoundedHaltingSchema/[↑z]) →
      ∃ k, (∼boundedHaltingClaimSentence z) ∈ DP.D k
  inconsistency_enters : ∀ z : ℕ,
    T ⊢ universalHaltingSchema/[↑z] →
      ∃ k, inconsistencyClaimSentence z ∈ DP.D k
  inconsistency_refutesConsistency : ∀ z : ℕ,
    T ⊢ universalHaltingSchema/[↑z] →
      ∃ k, (∼consistencyClaimSentence z) ∈ DP.D k

/-! ## Operational predicate presentations -/

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

/-! ### Strictness of the write-out machine/input classes

The paper's `⟨m⟩` and `⟨x⟩` are objects a polynomial-time machine can *write down*
(tex:1931-1933).  A poly-time writer emits polynomially many **symbols**, so it can name an
`n`-bit object, whose numeric value is `2^n`.  The two witnesses below show that this is a
real gap and not a bookkeeping preference: the same sequence is admissible for the write-out
class and provably inadmissible for the whole-value one. -/

/-- **Input strictness.**  `xₙ = 2ⁿ` is an `n`-bit string — the paper's own `⟨x⟩` shape — so a
poly-time writer emits it, and `BigDigits` accepts it.  Its numeric *value* is exponential, so
`PolyNatCodes` rejects it. -/
lemma bigDigits_two_pow_not_polyNatCodes :
    BigDigits (fun n => 2 ^ n) ∧ ¬ Nonempty (PolyNatCodes (fun n => 2 ^ n)) :=
  ⟨bigDigits_two_pow, fun ⟨h⟩ => not_polyFueled_two_pow h.code h.code_poly⟩

/-- **Machine strictness, at the paper's own example.**  `Nat.Partrec.Code.nest` — the
family `nest 0 = zero`, `nest (n+1) = pair (nest n) zero` — is a *real* machine sequence
whose source is `2n + 1` symbols long, so a poly-time writer emits it (tex:1931-1933) and
`DigitMachineCodes` accepts it (`bigDigits_sourceNat_nest`).  Its source *number*
`Code.sourceNat (nest n)` is at least `2 ^ n`, so the whole-value class rejects it.  This is
the `thm:halts`/`thm:loops`/`thm:dontwait` analogue of
`digitRatCodes_two_pow_inv_not_polyRatCodes`, and it is the same family that the erratum note
at `DigitMachineCodes` records as *doubly* exponential under Mathlib's `Encodable.encode` —
which is why `encode` is not the naming map. -/
lemma digitMachineCodes_nest_not_polyMachineCodes :
    DigitMachineCodes Nat.Partrec.Code.nest ∧
      ¬ Nonempty (PolyMachineCodes Nat.Partrec.Code.nest) := by
  refine ⟨Nat.Partrec.Code.bigDigits_sourceNat_nest, ?_⟩
  rintro ⟨h⟩
  obtain ⟨_, _, hf, _⟩ := h.code_poly
  exact not_isPolyBounded_two_pow
    (hf.of_le (fun n => Nat.Partrec.Code.two_pow_le_sourceNat_nest n))

/-- **Every `nest` machine halts on every input.**  `nest 0 = zero` returns `0`, and
`nest (n+1) = pair (nest n) zero` pairs two convergent runs.  This is what makes
`Nat.Partrec.Code.nest` usable as a `thm:halts` instance and not merely as a class witness:
the family has genuinely growing source *and* a discharged halting hypothesis. -/
lemma codeHalts_nest (n x : ℕ) : CodeHalts (Nat.Partrec.Code.nest n) x := by
  induction n with
  | zero => trivial
  | succ n ih =>
      simpa [CodeHalts, Nat.Partrec.Code.nest, Nat.Partrec.Code.eval, Seq.seq] using
        ⟨ih, trivial⟩

/-- **A machine that halts on nothing.**  `rfind'` searches for a zero of its argument;
`succ` never returns `0`, so the search never terminates. -/
def neverHaltMachine : Nat.Partrec.Code := .rfind' .succ

lemma not_codeHalts_neverHaltMachine (x : ℕ) : ¬ CodeHalts neverHaltMachine x := by
  intro h
  rw [CodeHalts, Part.dom_iff_mem] at h
  obtain ⟨v, hv⟩ := h
  simp only [neverHaltMachine, Nat.Partrec.Code.eval, Nat.unpaired, Part.mem_map_iff,
    Nat.mem_rfind] at hv
  obtain ⟨a, ⟨h1, -⟩, -⟩ := hv
  simp at h1

/-- **The universal halting schema is not argument-insensitive.**

`universalHaltingSchema` is picked by `Classical.epsilon`, so its *shape* is unreachable from
the API — but its defining spec is not nothing.  Because `UniversalCodeHalts` is itself
non-constant (`Code.zero` halts on `0`, `neverHaltMachine` does not), the chosen formula
cannot be one that ignores its argument.

This is the side condition of the substitution-injectivity lemma that the syntactic
separation of claim sentences in `ComputationRepresented.lean` would need: the missing piece
there is the general lemma `t ≠ t' → σ/[t] ≠ σ/[t']` for a `σ` mentioning `#0`, not the
hypothesis that this particular `σ` mentions `#0`.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citation —
`codeOfREPred_spec` through `universalHaltingSchema_spec`. -/
lemma universalHaltingSchema_not_argument_insensitive :
    ¬ ∀ z z' : ℕ, universalHaltingSchema.Evalb ![z] ↔ universalHaltingSchema.Evalb ![z'] := by
  intro h
  have hz : universalHaltingSchema.Evalb ![haltingClaimInput Nat.Partrec.Code.zero 0] :=
    (universalHaltingSchema_spec _).mpr
      ((universalCodeHalts_claimInput Nat.Partrec.Code.zero 0).mpr trivial)
  have hz' : ¬ universalHaltingSchema.Evalb ![haltingClaimInput neverHaltMachine 0] := by
    intro hx
    exact not_codeHalts_neverHaltMachine 0
      ((universalCodeHalts_claimInput neverHaltMachine 0).mp
        ((universalHaltingSchema_spec _).mp hx))
  exact hz' ((h _ _).mp hz)

/-- **The universal halting schema mentions its argument.**  The occurrence form of
`universalHaltingSchema_not_argument_insensitive`: a formula that does not mention `#0` has
the *same* instance at every closed term (`Semiformula.subst_eq_of_not_mentions`), so it
would have the same truth value at every argument.  This is the side condition of
substitution injectivity, and with it the syntactic separation of claim sentences in
`ComputationRepresented.lean` is a theorem rather than queued infrastructure.

Kind `P` (proved).  Provenance: (a) derived in-project from
`universalHaltingSchema_not_argument_insensitive`; (b) Foundation citations —
`Semiformula.subst_eq_of_not_mentions` (`Framework/SubstOccurrence.lean`),
`Semiformula.eval_substs`. -/
lemma universalHaltingSchema_mentions_zero :
    (universalHaltingSchema : ArithmeticSemisentence 1).Mentions 0 := by
  by_contra hmem
  refine universalHaltingSchema_not_argument_insensitive fun z z' => ?_
  have key : ∀ w : ℕ,
      Semiformula.Evalb (M := ℕ) (![] : Fin 0 → ℕ)
          (universalHaltingSchema/[(‘↑w’ : Semiterm ℒₒᵣ Empty 0)])
        ↔ universalHaltingSchema.Evalb ![w] := by
    intro w
    simp [Semiformula.eval_substs, Matrix.constant_eq_singleton]
  have hsub := Semiformula.subst_eq_of_not_mentions hmem
    (‘↑z’ : Semiterm ℒₒᵣ Empty 0) (‘↑z'’ : Semiterm ℒₒᵣ Empty 0)
  rw [← key z, ← key z', hsub]

/-- A constant machine sequence is write-out named for free. -/
lemma digitMachineCodes_const (c : Nat.Partrec.Code) :
    DigitMachineCodes (fun _ => c) :=
  BigDigits.const (Nat.Partrec.Code.sourceNat c)

#print axioms universalHaltingSchema_not_argument_insensitive

/-! ## Positive and negative path witnesses -/

/-- `N+`: the positive path fires for the repository's everywhere-zero program. -/
lemma computationRepresentation_positive_path
    {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗥₀ ⪯ T]
    (Q : ComputationTheoryPresentation DP T) :
    ∃ k, haltingClaimSentence (haltingClaimInput Nat.Partrec.Code.zero 0) ∈ DP.D k := by
  apply Q.halting_enters
  apply re_complete_mp (T := T) universalCodeHalts_re
  rw [universalCodeHalts_claimInput]
  rw [CodeHalts]
  rw [Part.dom_iff_mem]
  refine ⟨0, Nat.Partrec.Code.evaln_sound (k := 1) ?_⟩
  simp [Nat.Partrec.Code.evaln]

#print axioms universalCodeHalts_re
#print axioms universalBoundedHalts_re
#print axioms universalHaltingSchema_spec
#print axioms ComputableHorizon.ackermann
#print axioms not_polyNatCodes_ack
#print axioms bigDigits_two_pow_not_polyNatCodes
#print axioms digitMachineCodes_nest_not_polyMachineCodes
#print axioms ComputationClaim.godelCode_injective
#print axioms computationClaimSentence_digits
#print axioms computationRepresentation_positive_path

end LogicalInduction
