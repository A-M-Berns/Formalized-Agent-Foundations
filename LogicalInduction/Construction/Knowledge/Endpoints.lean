import LogicalInduction.Construction.Paper.TheoremDP
import LogicalInduction.Construction.Knowledge.SubstEmission
import LogicalInduction.Framework.Theory.R0Instances
import LogicalInduction.Framework.Theory.RepresentsComputations
import LogicalInduction.Framework.Theory.BoundedConsistency
import LogicalInduction.Construction.Knowledge.SourceWindow
import LogicalInduction.Construction.Knowledge.DayMachine

/-!
# Computation claims that name their machine, at the paper's representability premise

This module renders the §4.10 computational-knowledge theorems — `thm:halts` (tex:1923),
`thm:loops` (tex:1935), `thm:dontwait` (tex:1946-1952), `thm:pac` (tex:1869),
`thm:pazfc` (tex:1881) and `thm:incons` (tex:1893) — all over the single paper-facing
market `liaHistory (paperDP T)`, whose `paperTheoryDP` component is the paper's own
`Θ`-complete theorem stream, and at the paper's own §2 representability premise
(tex:600-606).

## The design

What is *represented* is a **universal** object, fixed once per theorem and independent of
the machine sequence:

* the total computable `universalRunValue f : ℕ → ℕ`, which decodes a packed
  `⟨⟨source, input⟩, day⟩` argument, runs the decoded machine for `f day` interpreter steps
  and returns `1`/`0` — one `γ` per horizon program `f`.  Note precisely what `γ`
  represents: the **composite** decider `universalRunValue f`, not the horizon `f` alone.
  The paper's `⌜f⌝(⌜n⌝)` is read here as `⌜g⌝(⟨⟨m, x⟩, n⟩) ≠ 0` for that composite `g`.
  This costs no extra hypothesis: `RepresentsComputations` supplies a representing `γ` for
  *any* total computable function, and `universalRunValue f` is total computable exactly
  when `f` is (`universalRunValue_computable`), so `g` and `f` stand on the same premise;
* the fixed r.e. `universalHaltingSchema = codeOfREPred UniversalCodeHalts`, whose argument
  is a packed `⟨source, input⟩` pair (`Construction/Knowledge/Syntax.lean`);
* the fixed r.e. `inconsistencySchema = codeOfREPred MachineTheoryInconsistent`, whose
  argument is a machine's source number.

The day's machine, input and theory then enter the *sentence*, as the argument written into
that fixed object.  This composite reading is stated here once and cited, not restated, at
each endpoint.

**Why the argument and not the schema carries the data.**  A family built instead as
`codeOfREPred` of a sequence-mentioning predicate, or as `RepresentsComputations.repr` of a
decider that mentions the sequence, depends on that predicate's **extension** alone; and
each endpoint's own hypothesis pins the extension to a constant (`∀ n, halts` gives
`fun _ => True`, `hnever` the constant `0`, `hconsistent` the constant `1`).  Such a family
would be one sentence repeated, naming no machine.  Here the day-`n` sentence is a fixed
object at the argument term `binNumeral (haltingClaimInput ⌜mₙ⌝ xₙ)`, so two sequences with
the same extension but different programs give literally different argument terms — and the
separation is a theorem, not an intention:

* `haltingArgClaimSentence_ne_of_source_ne` separates two claim families by their machines'
  *source numbers alone*, whatever those machines do;
  `haltingArgClaimSentence_ne_of_claimInput_ne` by the whole argument;
  `inconsistencyArgClaimSentence_ne_of_arg_ne` likewise on the `thm:incons` lane.  These are
  unconditional, so they may be invoked *inside* a single family, no endpoint hypothesis
  constraining the machine names.  The step from different arguments to different sentences
  (`σ/[t] ≠ σ/[t']` for `t ≠ t'`, false for a `σ` not mentioning `#0`) rests on
  `Semiformula.Mentions` and its transport lemmas (`Framework/Theory/SubstOccurrence.lean`), with
  the side condition discharged by `universalHaltingSchema_mentions_zero` /
  `inconsistencySchema_mentions_zero`.
* On the bounded lane `representedClaimSentence_ne_of_const_ne` and
  `representedClaimSentence_ne_of_arg_ne` say the same thing with the occurrence condition
  `γ.Mentions 0` as a hypothesis, because `γ` is supplied existentially by
  `RepresentsComputations` and is not a fixed object here.
* `haltingArgClaimSentence_ne_of_halts_ne` and `representedClaimSentence_ne_of_runValue_ne`
  are the weaker behavioural companions: they separate arguments on which the represented
  run *disagrees*, so they separate families whose behaviour differs, not days within one
  family.

## Naming a big argument inside `def:ec`

The argument `⟨⟨⌜mₙ⌝, xₙ⟩, n⟩` has a value exponential in the day, so it is spelled by the
**compact** Horner term `binNumeral` (`Construction/LUV/SourceCodec.lean`), `O(log v)` `ℒₒᵣ` nodes,
whose symbol run is emitted digit by digit from the very write-out certificates the paper's
hypotheses supply: `hm : DigitMachineCodes machines` and `hi : BigDigits inputs`.  Those
two hypotheses are therefore load-bearing on the `def:ec` obligation — they are the only
route to the `sentence_poly` field of each represented-claims bundle — and not decorative.
Foundation's *unary* `Semiterm.Operator.numeral` would cost the argument's value in symbols;
that is a Foundation artifact, and the paper fixes no numeral notation (tex:564, tex:614).
Provability is insensitive to the choice (`provable_subst_iff_of_val`), so only the cost
changes.

The `def:ec` obligation on each family is **discharged**, not assumed: the paper's source
language writes `∀ν (γ(t,ν) ⟺ ν = 0̄)` with one `iff` node over a fixed skeleton and one
compact-numeral run for `t`, whatever `γ` is (`Construction/Knowledge/SubstEmission.lean`).

## The claim families and their endpoints

* `representedBoundedClaims`, and its `thm:dontwait` specialisation
  `representedBoundedHaltingClaims` → `lic_does_not_anticipate_halting_ofComputation` and
  `lic_does_not_anticipate_halting_unconditional`;
* `representedConClaims` → `lic_belief_finitistic_consistency_unconditional`,
  `lic_belief_stronger_theory_consistency_unconditional`;
* `representedHaltingClaims` → `lic_learns_halting_patterns_ofComputation`,
  `lic_learns_provable_nonhalting_patterns_ofComputation` and their unconditional forms;
* `representedInconsistentTheoryClaims` → `lic_disbelief_inconsistent_theories_unconditional`.

## What the premise buys, and what it does not

* **Both literals come from one sentence** on the bounded lane.  For the total
  `{0,1}`-valued universal decider, the claim `∀ν (γ(t, ν) ⟺ ν = 0̄)` is provable exactly
  when the run *fails* and refutable exactly when it *succeeds* (`represents_proves` /
  `represents_refutes_all`).  Weak Σ₁-representation would give only the positive direction.
* **The deductive process is the paper's own.**  Because `γ` is supplied *existentially* by
  `RepresentsComputations` there is no computable map to `⌜γ⌝`, so no fixed schema can be
  dovetailed; `paperDP`'s theorem stream publishes *every* `T`-provable proposition and
  needs none.
* **No endpoint here takes a soundness instance.**

Two design choices are cited in a clause where they bear and explained once in the glossary
in `LogicalInduction.lean`: `dd:symbolcount`, the §4.10 symbol measure on derivations, and
`dd:machinetheory`, reading a machine as a presentation of a theory.

## Residual hypotheses

`[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the strengthenings beyond the paper, which assumes only that
`Θ` is consistent, c.e., and represents computations.  `[T.Δ₁]` asks for a Δ₁ axiom set
where the paper assumes only c.e.; by Craig's trick every c.e. theory has a deductively
equivalent Δ₁ axiomatization, so the theorems transfer, and that reduction is not formalized
here.  `[𝗣𝗔⁻ ⪯ T]` is the Σ₁-completeness the paper's own §4.10 proofs use without stating
(`re_complete_mp`).  Both are disclosed globally in `LogicalInduction/README.md`, and each
endpoint cites this section in a clause rather than restating them.  On the `thm:incons`
lane both are hypotheses on the **market's** theory only: the day's theories carry no `Δ₁`
hypothesis at all.  `[𝗜𝚺₁ ⪯ T]` is not among them: `paperTheoryDP`'s computability runs through
Foundation's internal provability predicate at `V := ℕ`, whose side condition is
`ℕ ⊧* 𝗜𝚺₁`, true outright.  Nothing on this lane assumes `T` proves any induction.

## The two premises not discharged here

* `thm:loops`'s `hloops` is witnessed by `loopsTheory`, and there **by axiom fiat**: the
  universal object is a `codeOfREPred` chosen by `Classical.epsilon`, so only *positive*
  bridges to `T ⊢ ·` exist.  The disclosure is at `loopsTheory` itself.
* The uniform half of `theoryOf`'s surjectivity — that every r.e. set of sentences is
  `theoryOf m` for a single `m` — is not formalized, and no endpoint consumes it
  (`hinc` is stated at the caller's own machine).  `theoryOf_const_ofNNF` proves the
  singleton half exactly.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-! ## The claim sentence

`reprAllTerm γ y t` is the paper's `∀ν : γ(t, ν) ↔ ν = ȳ`, with the argument named by the
closed term `t`.  Foundation keeps formulas in negation normal form, so `∼(∀⁰ ψ)` is `∃⁰ ∼ψ`
on the nose, and `paperPrimeDecompose` sends the two to complementary propositional literals
over one atom. -/

/-- Equation for the negative-prime (`.all`) case of the paper decomposition, stated at
`Semiformula.all` rather than at the `∀⁰` closure notation, which is only *definitionally*
that constructor. -/
lemma paperPrimeDecompose_all (ψ : ArithmeticSemiformula ℕ 1) :
    paperPrimeDecompose (Semiformula.all ψ) = ∼paperPrimeSentence true ((∼ψ).exs) := by
  simp only [paperPrimeDecompose]

/-- Equation for the positive-prime (`.exs`) case. -/
lemma paperPrimeDecompose_exs (χ : ArithmeticSemiformula ℕ 1) :
    paperPrimeDecompose (Semiformula.exs χ) = paperPrimeSentence true (Semiformula.exs χ) := by
  simp only [paperPrimeDecompose]

/-- The public propositional atom naming the bounded claim whose argument is named by the
closed term `t`.  It is the *prime* of `reprAllTerm γ 0 t`, so that
`paperPrimeDecompose (reprAllTerm γ 0 t)` is its negation and
`paperPrimeDecompose (∼reprAllTerm γ 0 t)` is the atom itself. -/
def representedClaimSentence (γ : ArithmeticSemisentence 2) (t : Semiterm.Const ℒₒᵣ) :
    Sentence :=
  paperPrimeSentence true
    (Semiformula.exs (∼(Rewriting.emb (reprBodyTerm γ 0 t) : ArithmeticSemiformula ℕ 1)))

/-- The paper decomposition of the claim `∀ν (γ(t, ν) ⟺ ν = 0̄)` is the **negative**
literal: the proposition splits as `∼representedClaimSentence γ t`. -/
lemma paperPrimeDecompose_reprAllTerm (γ : ArithmeticSemisentence 2)
    (t : Semiterm.Const ℒₒᵣ) :
    paperPrimeDecompose ((reprAllTerm γ 0 t : ArithmeticSentence) : ArithmeticProposition)
      = ∼representedClaimSentence γ t := by
  have h : ((reprAllTerm γ 0 t : ArithmeticSentence) : ArithmeticProposition)
      = Semiformula.all (Rewriting.emb (reprBodyTerm γ 0 t) : ArithmeticSemiformula ℕ 1) := by
    simp [reprAllTerm]
    rfl
  rw [h, paperPrimeDecompose_all, representedClaimSentence]

/-- The paper decomposition of the *negated* claim is the **positive** literal
`representedClaimSentence γ t`, the two forming one propositional pair. -/
lemma paperPrimeDecompose_neg_reprAllTerm (γ : ArithmeticSemisentence 2)
    (t : Semiterm.Const ℒₒᵣ) :
    paperPrimeDecompose ((∼(reprAllTerm γ 0 t) : ArithmeticSentence) : ArithmeticProposition)
      = representedClaimSentence γ t := by
  have h : ((∼(reprAllTerm γ 0 t) : ArithmeticSentence) : ArithmeticProposition)
      = Semiformula.exs
        (∼(Rewriting.emb (reprBodyTerm γ 0 t) : ArithmeticSemiformula ℕ 1)) := by
    simp [reprAllTerm]
    rfl
  rw [h, paperPrimeDecompose_exs, representedClaimSentence]

/-- **The claim family is `def:ec` emittable, for every `γ` and every emittable argument
naming.**  Definitionally the source certificate of
`Construction/Knowledge/SubstEmission.lean`: the public atom *is* the paper-prime of the
negated body, and the paper's source language writes that body with one `⟺` node over a
fixed skeleton plus the argument term's own symbol run.

This is where `hm`/`hi` do their work downstream: `henc` is supplied by the compact
numeral's digit-driven emitter, which consumes the write-out certificates.

Kind `C` (composition).  Provenance: (a) derived in-project from
`bigSentenceCodes_reprArgClaim`. -/
lemma representedClaimSentence_bigSentenceCodes (γ : ArithmeticSemisentence 2)
    (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ l : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))) :
    BigSentenceCodes (fun n => representedClaimSentence γ (τ n)) :=
  bigSentenceCodes_reprArgClaim γ τ henc

variable (T : ArithmeticTheory)

/-- The theorem process publishes the claim atom when `T` refutes the value-`0` sentence. -/
lemma paperDP_covers_representedClaim [T.Δ₁]
    (γ : ArithmeticSemisentence 2) (t : Semiterm.Const ℒₒᵣ)
    (h : T ⊢ ∼(reprAllTerm γ 0 t)) :
    ∃ k, representedClaimSentence γ t ∈ (paperDP T).D k := by
  have := paperTheoryDP_covers_outer_provable T _ h
  rw [paperPrimeDecompose_neg_reprAllTerm] at this
  exact paperDP_covers_of_paperTheoryDP T this

/-- The theorem process publishes the negated claim atom when `T` proves the value-`0`
sentence. -/
lemma paperDP_covers_representedClaim_neg [T.Δ₁]
    (γ : ArithmeticSemisentence 2) (t : Semiterm.Const ℒₒᵣ)
    (h : T ⊢ reprAllTerm γ 0 t) :
    ∃ k, (∼representedClaimSentence γ t) ∈ (paperDP T).D k := by
  have := paperTheoryDP_covers_outer_provable T _ h
  rw [paperPrimeDecompose_reprAllTerm] at this
  exact paperDP_covers_of_paperTheoryDP T this

/-! ## Transferring provability to the compact spelling

Every literal below is derived at Foundation's unary numeral — that is the form
`RepresentsComputations` and `re_complete_mp` speak — and then carried to the compact
spelling by one value-transfer step.  The transfer is Gödel completeness in both directions
and adds no hypothesis on `T` beyond the `[𝗣𝗔⁻ ⪯ T]` the endpoints here carry
explicitly. -/

/-- **The compact and unary spellings of an argument are interprovable.**  Instance of
`provable_subst_iff_of_val` at `binNumeral_val`.

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma provable_subst_binNumeral_iff [𝗣𝗔⁻ ⪯ T] (φ : ArithmeticSemisentence 1) (v : ℕ) :
    T ⊢ (φ/[(binNumeral v).const] : ArithmeticSentence) ↔
      T ⊢ (φ/[↑v] : ArithmeticSentence) :=
  provable_subst_iff_of_val T φ (binNumeral v) v fun _ _ _ => binNumeral_val v

/-- Substitution into a closed-term slot commutes with negation. -/
private lemma subst_neg (φ : ArithmeticSemisentence 1)
    (s : ArithmeticSemiterm Empty 0) :
    ((∼φ)/[s] : ArithmeticSentence) = ∼(φ/[s] : ArithmeticSentence) := by simp

/-- **The bounded claim sentence at the compact spelling is provable exactly when it is at
the unary one.**

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma provable_reprAllTerm_binNumeral_iff [𝗣𝗔⁻ ⪯ T] (γ : ArithmeticSemisentence 2)
    (v : ℕ) :
    T ⊢ reprAllTerm γ 0 (binNumeral v) ↔ T ⊢ reprAll γ 0 v := by
  rw [← reprAllSchema_subst_term γ 0 (binNumeral v), ← reprAllSchema_subst γ 0 v]
  exact provable_subst_binNumeral_iff T (reprAllSchema γ 0) v

/-- The negative half of the same transfer. -/
lemma provable_neg_reprAllTerm_binNumeral_iff [𝗣𝗔⁻ ⪯ T] (γ : ArithmeticSemisentence 2)
    (v : ℕ) :
    T ⊢ ∼(reprAllTerm γ 0 (binNumeral v)) ↔ T ⊢ ∼(reprAll γ 0 v) := by
  rw [← reprAllSchema_subst_term γ 0 (binNumeral v), ← reprAllSchema_subst γ 0 v,
    ← subst_neg, ← subst_neg]
  exact provable_subst_binNumeral_iff T (∼reprAllSchema γ 0) v

/-! ## The universal bounded decider, and the argument that names a machine

`RepresentsComputations` quantifies over *total* computable `ℕ → ℕ` functions, so what is
represented here is the universal bounded-run decider at a fixed horizon program.  It takes
a packed argument `⟨⟨source, input⟩, day⟩`, decodes the source with `Code.ofSource`
(everywhere defined) and runs it under `evaln` (everywhere defined) for `f day` steps.  No
partiality enters, and — the point of the whole design — the function does not mention any
machine sequence, so the formula `γ` representing it is fixed once for the horizon `f` and
the *sequence* appears only in the argument written into the sentence. -/

/-- The argument of the bounded claim: the machine's source, its input and the day, packed.
`⟨⟨⌜mₙ⌝, xₙ⟩, n⟩`. -/
def boundedArg (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.pair (haltingClaimInput (machines n) (inputs n)) n

/-- Write-out digit access to the packed argument, from the paper's own two classes.  This
is the load-bearing use of `hm` and `hi`: they are what makes the claim family `def:ec`.

Kind `C` (composition).  Provenance: (a) derived in-project from `haltingClaimInput_digits`
and `BigDigits.natPair`. -/
lemma boundedArg_digits {machines : ℕ → Nat.Partrec.Code} {inputs : ℕ → ℕ}
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs) :
    BigDigits (boundedArg machines inputs) :=
  (haltingClaimInput_digits hm hi).natPair (BigDigits.of_polyFueled PolyFueled.id)

/-- **The universal bounded-run decider at a horizon.**  `1` if the machine whose source is
`z.unpair.1.unpair.1` halts on `z.unpair.1.unpair.2` within `steps z.unpair.2` interpreter
steps, else `0`.  Total, and independent of every machine sequence. -/
def universalRunValue (steps : ℕ → ℕ) (z : ℕ) : ℕ :=
  if (Nat.Partrec.Code.evaln (steps z.unpair.2)
      (Nat.Partrec.Code.ofSource z.unpair.1.unpair.1) z.unpair.1.unpair.2).isSome then 1
  else 0

/-- `1` if `machines n` halts on `input n` within `steps n` interpreter steps, else `0` —
the *value* the universal decider takes at the day-`n` argument. -/
def boundedRunValue (machines : ℕ → Nat.Partrec.Code) (input steps : ℕ → ℕ) (n : ℕ) : ℕ :=
  if (Nat.Partrec.Code.evaln (steps n) (machines n) (input n)).isSome then 1 else 0

@[simp] lemma boundedRunValue_eq_one_iff (machines : ℕ → Nat.Partrec.Code)
    (input steps : ℕ → ℕ) (n : ℕ) :
    boundedRunValue machines input steps n = 1 ↔
      CodeHaltsWithin (machines n) (input n) (steps n) := by
  unfold boundedRunValue CodeHaltsWithin
  split <;> simp_all

@[simp] lemma boundedRunValue_eq_zero_iff (machines : ℕ → Nat.Partrec.Code)
    (input steps : ℕ → ℕ) (n : ℕ) :
    boundedRunValue machines input steps n = 0 ↔
      ¬CodeHaltsWithin (machines n) (input n) (steps n) := by
  unfold boundedRunValue CodeHaltsWithin
  split <;> simp_all

/-- **The universal decider, at the argument naming a machine, is that machine's bounded
run.**  `Code.ofSource` inverts `Code.sourceNat`, so nothing is lost in the round trip
through the argument.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation/Mathlib citation —
`Nat.Partrec.Code.ofSource_sourceNat`. -/
lemma universalRunValue_boundedArg (machines : ℕ → Nat.Partrec.Code) (inputs steps : ℕ → ℕ)
    (n : ℕ) :
    universalRunValue steps (boundedArg machines inputs n)
      = boundedRunValue machines inputs steps n := by
  simp only [universalRunValue, boundedArg, boundedRunValue, haltingClaimInput,
    Nat.unpair_pair, Nat.Partrec.Code.ofSource_sourceNat]

/-- A write-out named machine sequence is computable: the source number is primitive
recursive by `BigDigits.primrec`, and `Code.ofSource` inverts it. -/
lemma DigitMachineCodes.computable {machines : ℕ → Nat.Partrec.Code}
    (hm : DigitMachineCodes machines) : Computable machines :=
  ((Nat.Partrec.Code.ofSource_primrec.comp (BigDigits.primrec hm)).to_comp).of_eq fun _ =>
    Nat.Partrec.Code.ofSource_sourceNat _

/-- A horizon named by a program is a computable function: the program's evaluation is
partial recursive and total at every day. -/
lemma ComputableHorizon.computable {steps : ℕ → ℕ} (h : ComputableHorizon steps) :
    Computable steps :=
  (Nat.Partrec.Code.eval_part.comp (Computable.const h.program) Computable.id).of_eq
    fun n => Part.eq_some_iff.mpr (h.program_spec n)

/-- The universal decider is computable whenever the horizon is — which is all
`RepresentsComputations` needs to hand back a `γ` for it.  Nothing about a machine sequence
enters.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Mathlib citations —
`Nat.Partrec.Code.primrec_evaln`, `Nat.Partrec.Code.ofSource_primrec`. -/
lemma universalRunValue_computable {steps : ℕ → ℕ} (hs : Computable steps) :
    Computable (universalRunValue steps) := by
  have hz1 : Computable fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair |>.to_comp
  have hz2 : Computable fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair |>.to_comp
  have hsrc : Computable fun z : ℕ => Nat.Partrec.Code.ofSource z.unpair.1.unpair.1 :=
    (Nat.Partrec.Code.ofSource_primrec.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))).to_comp
  have hin : Computable fun z : ℕ => z.unpair.1.unpair.2 :=
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))).to_comp
  have hev : Computable fun z : ℕ =>
      (Nat.Partrec.Code.evaln (steps z.unpair.2)
        (Nat.Partrec.Code.ofSource z.unpair.1.unpair.1) z.unpair.1.unpair.2).isSome :=
    (Primrec.option_isSome.comp Nat.Partrec.Code.primrec_evaln).to_comp.comp
      (((hs.comp hz2).pair hsrc).pair hin)
  exact (Computable.cond hev (Computable.const 1) (Computable.const 0)).of_eq fun z => by
    unfold universalRunValue
    cases (Nat.Partrec.Code.evaln (steps z.unpair.2)
      (Nat.Partrec.Code.ofSource z.unpair.1.unpair.1) z.unpair.1.unpair.2).isSome <;> simp

/-- The compact argument name is injective as a term-in-context: two distinct values give
distinct `binNumeral` constants even after they are lifted into a one-variable context. -/
lemma binNumeral_const_ne (v v' : ℕ) (h : v ≠ v') :
    ((binNumeral v).const : ArithmeticSemiterm Empty 1)
      ≠ ((binNumeral v').const : ArithmeticSemiterm Empty 1) := by
  intro hconst
  refine h ?_
  have hval : ∀ w : ℕ, Semiterm.val (![0] : Fin 1 → ℕ) Empty.elim
      ((binNumeral w).const : ArithmeticSemiterm Empty 1) = w := by
    intro w
    simpa using binNumeral_val (M := ℕ) w
  have := congrArg (Semiterm.val (![0] : Fin 1 → ℕ) Empty.elim) hconst
  rwa [hval, hval] at this

/-- **The claim atom determines its body.**  Unwrapping the paper-prime pairing, the
existential and the semisentence embedding is the shared first step of both separation
lemmas on this lane. -/
private lemma reprBodyTerm_eq_of_representedClaimSentence_eq {γ : ArithmeticSemisentence 2}
    {t t' : Semiterm.Const ℒₒᵣ}
    (h : representedClaimSentence γ t = representedClaimSentence γ t') :
    reprBodyTerm γ 0 t = reprBodyTerm γ 0 t' := by
  have hpair := paperPrimeSentence_injective
    (a₁ := (true, Semiformula.exs (∼(Rewriting.emb (reprBodyTerm γ 0 t) :
      ArithmeticSemiformula ℕ 1))))
    (a₂ := (true, Semiformula.exs (∼(Rewriting.emb (reprBodyTerm γ 0 t') :
      ArithmeticSemiformula ℕ 1))))
    h
  have hexs := congrArg Prod.snd hpair
  simp only [Semiformula.exs.injEq, Semiformula.neg_inj] at hexs
  exact Rewriting.emb_injective hexs

/-- **Syntactic separation of represented claims at distinct arguments.**  The bounded-lane
analogue of `schemaArgClaimSentence_ne_of_const_ne`: if the representing formula `γ` really
mentions its first argument, distinct closed argument terms give distinct claim atoms, with
no hypothesis on the represented run.

The occurrence side condition is stated rather than discharged here, because `γ` is supplied
existentially by `RepresentsComputations` and is not a fixed object of this file.  It **is**
derivable from the representation specification alone whenever the represented function is
non-constant — that is `mentions_zero_of_repr_ne`
(`Framework/Theory/RepresentsComputations.lean`) — and only then: for a constant decider a `γ`
ignoring `#0` represents it correctly.  Consumers on a lane whose decider is provably
non-constant should discharge it (see `conGamma_mentions_zero` and its sufficient
conditions below); the hypothesis stays here because this lemma is stated for an arbitrary
`γ`.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`Semiformula.eq_of_rew_eq_of_mentions` (`Framework/Theory/SubstOccurrence.lean`),
`paperPrimeSentence_injective`, `Rewriting.emb_injective`. -/
lemma representedClaimSentence_ne_of_const_ne (γ : ArithmeticSemisentence 2)
    (hγ : γ.Mentions 0) (t t' : Semiterm.Const ℒₒᵣ)
    (h : (t.const : ArithmeticSemiterm Empty 1) ≠ (t'.const : ArithmeticSemiterm Empty 1)) :
    representedClaimSentence γ t ≠ representedClaimSentence γ t' := by
  intro heq
  refine h ?_
  have hbody := reprBodyTerm_eq_of_representedClaimSentence_eq heq
  rw [reprBodyTerm, reprBodyTerm, Semiformula.iff_eq, Semiformula.iff_eq] at hbody
  simp only [Semiformula.and_inj, Semiformula.or_inj, Semiformula.neg_inj] at hbody
  have hrew : (Rew.subst ![(t.const : ArithmeticSemiterm Empty 1), #0]) ▹ γ
      = (Rew.subst ![(t'.const : ArithmeticSemiterm Empty 1), #0]) ▹ γ := hbody.1.1
  simpa using Semiformula.eq_of_rew_eq_of_mentions (k := (0 : Fin 2)) (by simpa using hγ) hrew

/-- The bounded-lane anti-extensionality corollary at the compact argument name. -/
lemma representedClaimSentence_ne_of_arg_ne (γ : ArithmeticSemisentence 2)
    (hγ : γ.Mentions 0) {v v' : ℕ} (h : v ≠ v') :
    representedClaimSentence γ (binNumeral v) ≠ representedClaimSentence γ (binNumeral v') :=
  representedClaimSentence_ne_of_const_ne γ hγ _ _ (binNumeral_const_ne _ _ h)

/-- **Behavioural separation on the `thm:dontwait`/`thm:pac`/`thm:pazfc` lane.**

If the represented decider takes different values at two arguments, the two claim sentences
are different propositions.  The proof needs nothing about `γ` beyond the representability
premise itself: `T` proves the value-`0` sentence at the first argument and (by consistency,
which the premise supplies) cannot prove it at the second, so the two sentences cannot be
equal.

*What this is not.*  It is **not** the standing extensionality test of `KNOWLEDGE.md`
("same extension, different program ⇒ different sentence"): its hypothesis is a difference
in *run values*, and no endpoint on this lane can supply that within one claim family —
`hconsistent` pins the decider to the constant `1` and `hnever` to the constant `0`.  Machine
dependence of the sentence is definitional instead (the argument terms `binNumeral z` and
`binNumeral z'` differ, `binNumeral` and `Code.sourceNat` being injective); promoting that to
sentence inequality needs the substitution-injectivity lemma discussed in the module
docstring, which Foundation lacks.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`paperPrimeSentence_injective`, `Rewriting.emb_injective`. -/
lemma representedClaimSentence_ne_of_runValue_ne [𝗣𝗔⁻ ⪯ T] {steps : ℕ → ℕ}
    (γ : ArithmeticSemisentence 2)
    (hγ : ∀ z y : ℕ, y = universalRunValue steps z ↔ T ⊢ reprAll γ y z)
    (z z' : ℕ) (hz : universalRunValue steps z = 0)
    (hz' : universalRunValue steps z' ≠ 0) :
    representedClaimSentence γ (binNumeral z)
      ≠ representedClaimSentence γ (binNumeral z') := by
  intro heq
  have hbody := reprBodyTerm_eq_of_representedClaimSentence_eq heq
  have hall : reprAllTerm γ 0 (binNumeral z) = reprAllTerm γ 0 (binNumeral z') := by
    simp only [reprAllTerm, hbody]
  have h0 : T ⊢ reprAll γ 0 z := (hγ z 0).mp hz.symm
  have h0' : T ⊢ reprAll γ 0 z' := by
    refine (provable_reprAllTerm_binNumeral_iff T γ z').mp ?_
    rw [← hall]
    exact (provable_reprAllTerm_binNumeral_iff T γ z).mpr h0
  exact hz' ((hγ z' 0).mpr h0').symm

/-! ## The represented claim family -/

/-- The day-indexed claim family of a bounded computation, stated at the paper's
representability premise, with the machine named in the sentence.

`hγ` is exactly one instance of `RepresentsComputations.repr` — the caller obtains it from
the class at the **universal** decider `universalRunValue steps`, which mentions no machine
sequence, so one `γ` serves every sequence at that horizon.  The day-`n` sentence is that
`γ` at the argument `⟨⟨⌜mₙ⌝, xₙ⟩, n⟩`, written compactly.

`hm` and `hi` are consumed by the `def:ec` obligation — they are the digit certificates the
compact argument numeral is emitted from — and by nothing else; the *literals* come from
`hγ`.

Kind `C` (composition).  Provenance: (a) derived in-project from
`RepresentsComputations`; the deductive process is `paperDP`, which is soundness-free.
This is the `thm:dontwait` claim family; the paper node itself is carried by the endpoint
that consumes it, not by this constructor. -/
noncomputable def representedBoundedClaims [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    {machines : ℕ → Nat.Partrec.Code} {inputs steps : ℕ → ℕ}
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (γ : ArithmeticSemisentence 2)
    (hγ : ∀ z y : ℕ, y = universalRunValue steps z ↔ T ⊢ reprAll γ y z) :
    RepresentedDecidableClaims (paperDP T)
      (fun n => CodeHaltsWithin (machines n) (inputs n) (steps n)) where
  sentence n := representedClaimSentence γ (binNumeral (boundedArg machines inputs n))
  sentence_poly :=
    representedClaimSentence_bigSentenceCodes γ _
      (polySegStream_binNumeral_const (boundedArg_digits hm hi))
  provable_of_true n hn := by
    refine paperDP_covers_representedClaim T γ _ ?_
    refine (provable_neg_reprAllTerm_binNumeral_iff T γ _).mpr ?_
    refine represents_refutes_all T γ _ ?_
    refine (hγ _ 1).mp ?_
    rw [universalRunValue_boundedArg]
    exact ((boundedRunValue_eq_one_iff machines inputs steps n).mpr hn).symm
  disprovable_of_false n hn := by
    refine paperDP_covers_representedClaim_neg T γ _ ?_
    refine (provable_reprAllTerm_binNumeral_iff T γ _).mpr ?_
    refine (hγ _ 0).mp ?_
    rw [universalRunValue_boundedArg]
    exact ((boundedRunValue_eq_zero_iff machines inputs steps n).mpr hn).symm

/-- The paper's standing assumption on `T`, at the universal bounded decider: **one** `γ`
per horizon program, independent of every machine sequence.  This is the paper's `⌜f⌝`. -/
lemma exists_reprAll_of_representsComputations [RepresentsComputations T]
    {steps : ℕ → ℕ} (hs : Computable steps) :
    ∃ γ : ArithmeticSemisentence 2,
      ∀ z y : ℕ, y = universalRunValue steps z ↔ T ⊢ reprAll γ y z :=
  RepresentsComputations.repr _ (universalRunValue_computable hs)

/-! ## The paper-facing bounded-claim constructors

Both constructors below name the day-`n` claim the way the paper does — through the
representation of a *total* computable function (tex:600-606), applied to an argument that
names the machine and its input (tex:1931) — and therefore carry both literals over one
sentence.  Neither consumes a semantic hypothesis on `T`: the process is `paperDP`,
whose non-vacuity is `paperDP_nonvacuous`, from consistency alone.
-/

/-- The `thm:dontwait` claim family: `⌜qₙ⌝ halts on ⌜yₙ⌝ within ⌜f⌝(⌜n⌝) steps`, named
through `⌜f⌝` as the paper writes it and applied to the compact name of `⟨⟨⌜qₙ⌝, yₙ⟩, n⟩`.
`hm` and `hi` are the paper's write-out classes, and are what the argument's symbol run is
emitted from; `hh` names an arbitrary computable horizon by its program, with no growth
bound. -/
noncomputable def representedBoundedHaltingClaims [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [RepresentsComputations T]
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hh : ComputableHorizon horizons) :
    RepresentedDecidableClaims (paperDP T)
      (fun n => CodeHaltsWithin (machines n) (inputs n) (horizons n)) :=
  representedBoundedClaims T hm hi _
    (exists_reprAll_of_representsComputations T hh.computable).choose_spec

/-! ## §4.10: the arithmetized finite-consistency family

`thm:pac` and `thm:pazfc` are about one specific claim family — the paper's
`Con(Θ′)(⌜f⌝(⌜n⌝))`, "no proof of `⊥` from `⌜Θ′⌝` within `f(n)`" (tex:1855-1866) — and this
section builds it.  The family is parametric in **two** theories: the represent*ing* theory
`T`, whose provable propositions the market enumerates (the paper's `Θ`), and the *metered*
theory `T'`, whose finite proof searches the claims are about (the paper's `Θ′`).  `thm:pac`
is the diagonal `T' = T`; `thm:pazfc` is a genuinely different, stronger `T'`.

The design is the bounded lane's, with the extensionality trap taken seriously.  What is
represented is the **universal bounded-provability decider at the horizon**,
`conRunValue T' f` (`Framework/Theory/BoundedConsistency.lean`): it takes a packed
`⟨sentence code, day⟩`, evaluates `f` at the day *inside*, and decides whether the coded
sentence has a `T'`-derivation of at most `f(day)` symbols.  Its extension varies with
`T'`'s theorems, so the `γ` `RepresentsComputations T` returns for it genuinely names the
metered theory; one `γ` serves every day at that horizon.  `⊥` then enters the *sentence*,
as the first component of the compact argument `binNumeral ⟨⌜⊥⌝, n⟩`.

Representing the *consistency* predicate directly would have been the trap: for a
consistent `T'`, `fun n => conWithin T' (f n)` is extensionally `True` and its indicator is
the constant `0`, so a representing `γ` would name nothing at all — the extensionality
trap.

One disclosure at this boundary — and it is a *convention*, not a substitution.  The finite
search is metered by the derivation's symbol count, as the paper meters it, under the
counting convention of `Framework/Theory/DerivationSize.lean` (`dd:symbolcount`, glossary in
`LogicalInduction.lean`); the paper fixes no encoding or alphabet, so a convention is
unavoidable, and the truth of every instance is independent of it.  And the propositional
rendering of `Con` is a *negated* atom:
the paper's `Con(Θ)(ν)` is `∀ν' (γ(⟨⌜⊥⌝,n⟩, ν') ⟺ ν' = 0̄)`, a universal sentence, whose
paper-prime decomposition is the negation of the prime `∃`-sentence
`representedClaimSentence`.  That is the paper's own decomposition, not a choice made here.
-/

/-- The day-`n` argument of the Con family: `⟨⌜⊥⌝, n⟩`, the paper's `⌜⊥⌝` paired with the
day whose horizon value bounds the search. -/
noncomputable def conClaimArg (n : ℕ) : ℕ := Nat.pair ⌜(⊥ : ArithmeticSentence)⌝ n

/-- The argument is write-out emittable: a constant paired with the day.

Kind `C` (composition).  Provenance: (a) derived in-project from `BigDigits.const` and
`BigDigits.natPair`. -/
lemma conClaimArg_digits : BigDigits conClaimArg :=
  (BigDigits.const _).natPair (BigDigits.of_polyFueled PolyFueled.id)

/-- **The paper's `Con(Θ′)(⌜f⌝(⌜n⌝))`, as a propositional claim.**  The value-`0` sentence
of the representing formula `γ` at the compact name of `⟨⌜⊥⌝, n⟩`, decomposed the paper's
way: a universal sentence is not prime, so the atom is its `∃` negation and the claim is
that atom's negation. -/
noncomputable def conClaimSentence (γ : ArithmeticSemisentence 2) (n : ℕ) : Sentence :=
  ∼representedClaimSentence γ (binNumeral (conClaimArg n))

/-- The Con family is `def:ec` emittable: the negation tag over the claim atom, whose own
argument run is the compact numeral of `⟨⌜⊥⌝, n⟩`.

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma conClaimSentence_bigSentenceCodes (γ : ArithmeticSemisentence 2) :
    BigSentenceCodes (conClaimSentence γ) :=
  BigSentenceCodes.neg
    (representedClaimSentence_bigSentenceCodes γ _
      (polySegStream_binNumeral_const conClaimArg_digits))

/-- **The Con family names the day.**  Distinct days give distinct claims, with no
hypothesis on `T`'s theorems, because `Nat.pair` and `binNumeral` are injective.

The occurrence side condition `γ.Mentions 0` is stated rather than discharged *here*, because
this lemma is about an arbitrary `γ`.  It **is** derivable from the representation spec for
the Con lane's own `γ` as soon as `conRunValue T' horizons` is non-constant —
`conGamma_mentions_zero` below, with `conGamma_mentions_zero_of_bProv` and
`conGamma_mentions_zero_of_horizon_unbounded` as usable sufficient conditions, and
`conGamma_mentions_zero_ackermann` as a fully discharged instance.

The degenerate end is real and is exactly what the non-constancy hypothesis excludes: at a
horizon that is constantly `0`, `conRunValue T' horizons` is the constant `0` function,
which a `γ` ignoring its first argument does represent, and the whole day-indexed sentence
family may then collapse to one sentence.  So the side condition is not derivable from the
representation spec alone, but the obstruction reaches only constant deciders.

Kind `C` (composition).  Provenance: (a) derived in-project from
`representedClaimSentence_ne_of_arg_ne`. -/
lemma conClaimSentence_ne_of_day_ne (γ : ArithmeticSemisentence 2) (hγ : γ.Mentions 0)
    {m n : ℕ} (h : m ≠ n) : conClaimSentence γ m ≠ conClaimSentence γ n := by
  simp only [conClaimSentence, ne_eq, LO.Propositional.Formula.neg_inj]
  refine representedClaimSentence_ne_of_arg_ne γ hγ (fun hpair => h ?_)
  simpa [conClaimArg] using congrArg (fun z : ℕ => z.unpair.2) hpair

/-- **One `γ` per horizon and metered theory**, for the universal bounded-provability
decider.  This is the paper's `⌜f⌝`: `RepresentsComputations` supplies a representing
formula for any total computable function, and `conRunValue T' f` is total computable
exactly when `f` is.

The two theories are independent.  `T` is the theory that *represents* — the one the
market's deductive process enumerates, the paper's `Θ` — and `T'` is the theory whose
finite proof searches are *metered*, the paper's `Θ′`.  Nothing here relates them:
`conRunValue T' f` is a total computable function of naturals whatever `T'` is, and `T`
represents every such function.  `thm:pac` is the diagonal `T' = T`; `thm:pazfc` is the
general case. -/
lemma exists_reprAll_conRunValue (T' : ArithmeticTheory) [T'.Δ₁] [RepresentsComputations T]
    {horizons : ℕ → ℕ} (hh : Computable horizons) :
    ∃ γ : ArithmeticSemisentence 2,
      ∀ z y : ℕ, y = conRunValue T' horizons z ↔ T ⊢ reprAll γ y z :=
  RepresentsComputations.repr _ (conRunValue_computable T' hh)

/-- The `T`-formula representing `T'`'s bounded-provability decider at a horizon. -/
noncomputable def conGamma (T' : ArithmeticTheory) [T'.Δ₁] [RepresentsComputations T]
    {horizons : ℕ → ℕ} (hh : ComputableHorizon horizons) : ArithmeticSemisentence 2 :=
  (exists_reprAll_conRunValue T T' hh.computable).choose

/-- The representation specification of `conGamma`: `T` proves the value-`y` sentence at `z`
exactly when `conRunValue T' horizons z = y`. -/
lemma conGamma_spec (T' : ArithmeticTheory) [T'.Δ₁] [RepresentsComputations T]
    {horizons : ℕ → ℕ} (hh : ComputableHorizon horizons) (z y : ℕ) :
    y = conRunValue T' horizons z ↔ T ⊢ reprAll (conGamma T T' hh) y z :=
  (exists_reprAll_conRunValue T T' hh.computable).choose_spec z y

/-! ### The occurrence side condition on the Con lane, discharged

`conClaimSentence_ne_of_day_ne` — the statement that the day-indexed Con family does not
collapse to a single sentence — takes `(conGamma T T' hh).Mentions 0` as a side condition,
because `conGamma` is supplied existentially and its shape is unreachable.  That condition
is **not** a permanent boundary: the representation specification forces it as soon as the
represented decider takes two different values (`mentions_zero_of_repr_ne`), and the three
lemmas below take that from progressively more usable hypotheses, ending at a concrete
instance with nothing left to the caller.

The degenerate end is the only thing the hypothesis excludes.  At a horizon constantly `0`
the decider `conRunValue T' horizons` is constantly `0`, a `γ` ignoring its first argument
represents it correctly, and the day family may genuinely collapse.  Every horizon that is
unbounded — the paper's own illustration, `Ack`, among them — is on the other side of the
line. -/

/-- **The Con lane's occurrence side condition, from non-constancy of the decider.**  If the
universal bounded-provability decider takes different values at two packed arguments, its
representing formula must mention the argument slot.

Kind `C` (composition).  Provenance: (a) derived in-project from `mentions_zero_of_repr_ne`
and `conGamma_spec`. -/
lemma conGamma_mentions_zero (T' : ArithmeticTheory) [T'.Δ₁] [RepresentsComputations T]
    {horizons : ℕ → ℕ} (hh : ComputableHorizon horizons) {z z' : ℕ}
    (h : conRunValue T' horizons z ≠ conRunValue T' horizons z') :
    (conGamma T T' hh).Mentions 0 :=
  mentions_zero_of_repr_ne _ (conGamma_spec T T' hh) h

/-- **A usable sufficient condition: one derivation under one day's horizon.**  If some
sentence code has a `T'`-derivation of at most `horizons n` symbols, the decider is `1`
there and `0` at `⌜⊥⌝` on the same day (consistency of `T'`), so it is non-constant.

Kind `C` (composition).  Provenance: (a) derived in-project from
`conRunValue_pair_eq_one_iff` and `conRunValue_bot_eq_zero`. -/
lemma conGamma_mentions_zero_of_bProv (T' : ArithmeticTheory) [T'.Δ₁]
    [RepresentsComputations T] {horizons : ℕ → ℕ} (hh : ComputableHorizon horizons)
    (hcons : Entailment.Consistent T') {φcode n : ℕ}
    (hp : BProv T' φcode (horizons n)) :
    (conGamma T T' hh).Mentions 0 := by
  refine conGamma_mentions_zero T T' hh (z := Nat.pair φcode n)
    (z' := Nat.pair ⌜(⊥ : ArithmeticSentence)⌝ n) ?_
  rw [conRunValue_bot_eq_zero T' hcons n,
    (conRunValue_pair_eq_one_iff T' horizons φcode n).mpr hp]
  exact _root_.one_ne_zero

/-- **The condition every interesting horizon satisfies.**  `⊤` is `T'`-provable, so it has
*some* derivation, and that derivation has *some* symbol count; an unbounded horizon
eventually exceeds it, and the previous lemma applies.  This is the form a caller can
actually discharge: it asks nothing of `T'` beyond
the consistency the endpoint already assumes, and nothing of the horizon beyond
unboundedness.

Kind `C` (composition).  Provenance: (a) derived in-project; (b) Foundation citation —
`Bootstrapping.provable_iff_provable` (through `provableCode_quote_verum`). -/
lemma conGamma_mentions_zero_of_horizon_unbounded (T' : ArithmeticTheory) [T'.Δ₁]
    [RepresentsComputations T] {horizons : ℕ → ℕ} (hh : ComputableHorizon horizons)
    (hcons : Entailment.Consistent T') (hub : ∀ k : ℕ, ∃ n, k < horizons n) :
    (conGamma T T' hh).Mentions 0 := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, Bootstrapping.Proof (V := ℕ) T' d ⌜(⊤ : ArithmeticSentence)⌝ :=
    provableCode_quote_verum T'
  obtain ⟨n, hn⟩ := hub (dSize d)
  exact conGamma_mentions_zero_of_bProv T T' hh hcons
    (φcode := ⌜(⊤ : ArithmeticSentence)⌝) (n := n) ⟨d, hd, le_of_lt hn⟩

/-- **The §4.10 claim family.**  Day `n` claims that `T'` proves no contradiction with a
derivation of at most `horizons n` symbols; the claim is *true* on every day, by consistency of
`T'` alone (`conWithin_of_consistent`), and hence `T`-provable through the representation.

`T` is the represent*ing* theory — the paper's `Θ`, whose provable propositions the market
enumerates — and `T'` the metered one, the paper's `Θ′`.  `thm:pac` instantiates this at
the diagonal `T' = T`, where the consistency argument is supplied by
`RepresentsComputations.consistent`; `thm:pazfc` at a genuinely different `T'`, where it is
the paper's own explicit premise on `Θ′`.

The negative field is unreachable: its hypothesis contradicts `hcons`.  The paper's proof
likewise uses only the positive literal ("each statement is computable and true, and `Θ`
represents computations, so each is provable"; tex:4472).

Note what is *not* assumed: no relation whatever between `T` and `T'`.  That **matches** the
paper, which asks only that `Θ′` be "any recursively axiomatizable consistent theory"
(tex:1882) and states no containment hypothesis; and it matches the argument, which
needs only that `T` represent a computable function, that function's totality and
computability being facts about `T'`'s derivation codes rather than about `T`.

Kind `C` (composition).  Provenance: (a) derived in-project from `RepresentsComputations`
and `conWithin_of_consistent`.  The measure of the finite search is the paper's — symbols —
under this development's counting convention (`dd:symbolcount`); no modelling substitution
is charged here. -/
noncomputable def representedConClaims (T' : ArithmeticTheory) [T.Δ₁] [T'.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [RepresentsComputations T] (hcons : Entailment.Consistent T') {horizons : ℕ → ℕ}
    (hh : ComputableHorizon horizons) :
    RepresentedDecidableClaims (paperDP T) (fun n => conWithin T' (horizons n)) where
  sentence n := conClaimSentence (conGamma T T' hh) n
  sentence_poly := conClaimSentence_bigSentenceCodes _
  provable_of_true n _ := by
    refine paperDP_covers_representedClaim_neg T _ _ ?_
    refine (provable_reprAllTerm_binNumeral_iff T _ _).mpr ?_
    refine (conGamma_spec T T' hh _ 0).mp ?_
    exact (conRunValue_bot_eq_zero T' hcons n).symm
  disprovable_of_false n hn := absurd (conWithin_of_consistent T' hcons (horizons n)) hn

/-! ## The paper-facing endpoints, over the single market

`paperDP T` publishes every `T`-provable proposition (through its `paperTheoryDP`
component) alongside the computation and quotation literals, is computable
(`paperDP_computable`), and has a world consistent with every stage
(`paperDP_nonvacuous`).  Together with the two literals of `RepresentsComputations` this
leaves the three bounded-claim endpoints below with no semantic hypothesis on `T`, no
presentation argument, and no `hworld` argument. -/

/-- Market non-vacuity in the stage-indexed form these endpoints take, with consistency
supplied as a term rather than an instance — the bounded endpoints get it from the
representability premise (`RepresentsComputations.consistent`), the halting endpoints
assume it directly. -/
private lemma paperDP_hworld_stages [T.Δ₁] [𝗣𝗔⁻ ⪯ T] (hcon : Entailment.Consistent T) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP T).D n) := by
  haveI := hcon
  exact paperDP_hworld T

section Endpoints

variable [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [RepresentsComputations T]

/-- The horizon sequence is arbitrary computable — `hh` names its program rather than
bounding its growth — which is the paper's "let `f` be any computable function".
*Residual hypotheses (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the module's disclosed
strengthenings (module header; `LogicalInduction/README.md`).
Paper node: `thm:dontwait` -/
theorem lic_does_not_anticipate_halting_ofComputation
    (P : History) [IsLogicalInductor P (paperDP T)]
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hh : ComputableHorizon horizons)
    (hnever : ∀ n, ¬CodeHalts (machines n) (inputs n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP T).D n)) :
    (fun n => P n
      ((representedBoundedHaltingClaims T machines inputs horizons hm hi hh).sentence n))
        ≈ₙ fun _ => 0 :=
  lic_does_not_anticipate_halting P (paperDP T) machines inputs horizons
    (representedBoundedHaltingClaims T machines inputs horizons hm hi hh) hnever hworld

/-! ### Unconditional over the constructed `LIA`

Nothing remains but the caller's own computation and the (true) hypothesis about it: no
market, no inductor, no presentation, no `hworld`, and no semantic assumption on `T`. -/

/-- **Belief in Finitistic Consistency** (`thm:pac`), unconditional over `LIA`, at the
paper's own subject matter.

The day-`n` claim is this development's rendering of the paper's `Con(Θ)(⌜f⌝(⌜n⌝))`: the
value-`0` sentence of the formula `γ` representing the universal bounded-provability decider
`conRunValue T f`, at the compact name of the argument `⟨⌜⊥⌝, n⟩`.  Read out, it says that no
`T`-derivation of `⊥` has `f(n)` or fewer symbols — the paper's own reading.

*It is a paraphrase, in two disclosed respects, and is not asserted to BE the paper's
sentence.*  What `γ` represents is the **composite** decider `conRunValue T f` — the paper's
`⌜f⌝(⌜n⌝)` read as `⌜g⌝(⟨⌜⊥⌝, n⟩) = 0̄` for that composite `g` — rather than `f` alone; this
is the module header's standing disclosure and costs no extra hypothesis, since
`RepresentsComputations` represents any total computable function.  The finite search itself
is metered as the paper meters it, in symbols, under the counting convention of
`Framework/Theory/DerivationSize.lean` (`dd:symbolcount`) — a convention, not a substitution.

The horizon is an arbitrary computable function, named by its program and evaluated *inside*
the represented decider; both ends of that range are live.  It may grow as fast as `Ack` (the
paper's own illustration, witnessed below).  It may also be *degenerate*: at a horizon
constantly `0` the represented decider is constant, `conGamma`'s occurrence side condition
fails to be derivable, and the day-indexed sentence family may collapse to a single sentence
— the conclusion stays true, but names one claim rather than a genuine family.  Day
separation for the non-degenerate case is `conClaimSentence_ne_of_day_ne` together with
`conGamma_mentions_zero` (discharged for an unbounded horizon by
`conGamma_mentions_zero_of_horizon_unbounded`, and at `Ack` by
`conGamma_mentions_zero_ackermann`).

Nothing is left to the caller but the horizon.  There is no consistency hypothesis — the
consistency of `T` comes from `RepresentsComputations` — and no truth hypothesis: the truth
of every day's claim is `conWithin_of_consistent`, proved from that consistency alone.

*Residual hypotheses (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the module's disclosed
strengthenings (module header; `LogicalInduction/README.md`).  The finite proof search is
metered in symbols, as the paper meters it, under the counting convention of
`Framework/Theory/DerivationSize.lean` (`dd:symbolcount`).
Paper node: `thm:pac` -/
theorem lic_belief_finitistic_consistency_unconditional
    (horizons : ℕ → ℕ) (hh : ComputableHorizon horizons) :
    (fun n => liaHistory (paperDP T) n
      (conClaimSentence (conGamma T T hh) n)) ≈ₙ fun _ => 1 :=
  haveI := paperLIA T
  lic_belief_finitistic_consistency (liaHistory (paperDP T)) (paperDP T)
    (fun n => conWithin T (horizons n))
    (representedConClaims T T (RepresentsComputations.consistent T)
      hh).toRepresentedSemidecidableClaims
    (fun n => conWithin_of_consistent T (RepresentsComputations.consistent T) (horizons n))
    (paperDP_hworld_stages T (RepresentsComputations.consistent T))

/-- **Belief in the Consistency of a Stronger Theory** (`thm:pazfc`), unconditional over
`LIA`, at the paper's own subject matter.

The market is `Θ`'s: `paperDP T` publishes the propositions `T` proves, and the
inductor is trained on that process alone.  The *claims*, however, are about a second
theory `T'` — the paper's `Θ′`, "any recursively axiomatizable consistent theory"
(tex:1882); the informal framing that `Θ′` may be *stronger* than `Θ`, in that it proves `Θ`
consistent, is at tex:1879, and `ZFC` is the paper's worked example (tex:1889).  Day `n`
renders the arithmetized
`Con(Θ′)(⌜f⌝(⌜n⌝))`: no `T'`-derivation of `⊥` has `f(n)` or fewer symbols, written as
the value-`0` sentence of the `T`-formula representing `T'`'s bounded-provability decider.
So the inductor, which can prove nothing about `T'` from its own theory, nevertheless comes
to believe every finite consistency statement about it.

*A paraphrase in the same disclosed respect as `thm:pac`*: `γ` represents the
**composite** decider `conRunValue T' f`, not `f` alone (the module header's standing
disclosure).  The search itself is metered as the paper meters it, in symbols, under the
counting convention of `Framework/Theory/DerivationSize.lean` (`dd:symbolcount`) — a convention,
not a substitution.  The horizon ranges over *all* computable functions,
not only fast-growing ones: `Ack` is the witness below, and a degenerate horizon (constantly
`0`) makes the represented decider constant, so the day family may then collapse to a single
sentence.  Day separation in the non-degenerate case is `conClaimSentence_ne_of_day_ne` with
`conGamma_mentions_zero_of_horizon_unbounded`.

`hcons` is the paper's own premise on `Θ′` and is what makes each day's claim *true*; the
representability of `T` then carries truth to `T`-provability, and no soundness assumption
appears anywhere.

*The hypotheses are the paper's.*  tex:1882 assumes of `Θ′` only that it is a recursively
axiomatizable consistent theory — there is **no** `Θ ⊆ Θ′` hypothesis in the
paper — and no hypothesis relating `T` and `T'` is stated here either, because none is used:
the argument needs only that `T` represents computable functions and that `T'` is consistent.
What makes the theorem *interesting* is the informal case where `Θ` cannot prove `Con(Θ′)`,
and the `𝗜𝚺₁`/`𝗣𝗔` witness below carries that concretely.

*Residual hypotheses (disclosed).*  `[T.Δ₁]`, `[T'.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the module's
disclosed strengthenings (module header; `LogicalInduction/README.md`); the paper asks of
`Θ′` only that it be consistent and recursively axiomatizable.  The finite proof search is
metered in symbols, as the paper meters it, under the counting convention of
`Framework/Theory/DerivationSize.lean` (`dd:symbolcount`).
Paper node: `thm:pazfc` -/
theorem lic_belief_stronger_theory_consistency_unconditional
    (T' : ArithmeticTheory) [T'.Δ₁] (hcons : Entailment.Consistent T')
    (horizons : ℕ → ℕ) (hh : ComputableHorizon horizons) :
    (fun n => liaHistory (paperDP T) n
      (conClaimSentence (conGamma T T' hh) n)) ≈ₙ fun _ => 1 :=
  haveI := paperLIA T
  lic_belief_finitistic_consistency (liaHistory (paperDP T)) (paperDP T)
    (fun n => conWithin T' (horizons n))
    (representedConClaims T T' hcons hh).toRepresentedSemidecidableClaims
    (fun n => conWithin_of_consistent T' hcons (horizons n))
    (paperDP_hworld_stages T (RepresentsComputations.consistent T))

/-- `thm:dontwait`, unconditional over `LIA`.  `hh` supplies the horizon program for an
arbitrary computable `f` — no growth bound — which is the paper's own quantifier, and `hm`
and `hi` are the write-out metered machine/input classes, which is the paper's e.c. sequence
of bitstrings `⟨y⟩` (tex:1946-1952).  The three are independent hypotheses of one signature.
*Residual hypotheses (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the module's disclosed
strengthenings (module header; `LogicalInduction/README.md`).
Paper node: `thm:dontwait` -/
theorem lic_does_not_anticipate_halting_unconditional
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hh : ComputableHorizon horizons)
    (hnever : ∀ n, ¬CodeHalts (machines n) (inputs n)) :
    (fun n => liaHistory (paperDP T) n
      ((representedBoundedHaltingClaims T machines inputs horizons hm hi hh).sentence n))
        ≈ₙ fun _ => 0 :=
  haveI := paperLIA T
  lic_does_not_anticipate_halting_ofComputation T (liaHistory (paperDP T))
    machines inputs horizons hm hi hh hnever
    (paperDP_hworld_stages T (RepresentsComputations.consistent T))

/-- **`thm:dontwait`, applied.**  A machine that provably halts on nothing
(`neverHaltMachine`), the paper's `⟨y⟩` bitstring inputs `2 ^ n`, and the identity horizon
supplied through `ComputableHorizon.of`.  The non-halting hypothesis is proved, not assumed;
nothing is left to the caller. -/
example :
    (fun n => liaHistory (paperDP T) n
      ((representedBoundedHaltingClaims T
          (fun _ => neverHaltMachine) (fun n => 2 ^ n) (fun n => n)
          (digitMachineCodes_const neverHaltMachine) bigDigits_two_pow
          (ComputableHorizon.of Computable.id)).sentence n))
        ≈ₙ fun _ => 0 :=
  lic_does_not_anticipate_halting_unconditional T
    (fun _ => neverHaltMachine) (fun n => 2 ^ n) (fun n => n)
    (digitMachineCodes_const neverHaltMachine) bigDigits_two_pow
    (ComputableHorizon.of Computable.id)
    (fun n => not_codeHalts_neverHaltMachine (2 ^ n))

/-- **`thm:pac`, applied.**  The horizon is Ackermann's function on the diagonal — the
paper's own illustration is `Con(PA)(⌜Ack(10,10)⌝)` (tex:1859) — and the theory is `𝗜𝚺₁`,
for which all three instances are discharged in the repository
(`Framework/Theory/R0Instances.lean`).  Nothing is assumed: this is a
belief-in-consistency statement about a named theory, with the consistency claim itself
arithmetized.

This is the first endpoint of the development whose subject matter is a `Con(Θ)` family
rather than a caller-supplied bounded computation. -/
example :
    (fun n => liaHistory (paperDP 𝗜𝚺₁) n
      (conClaimSentence (conGamma 𝗜𝚺₁ 𝗜𝚺₁ ComputableHorizon.ackermann) n)) ≈ₙ fun _ => 1 :=
  lic_belief_finitistic_consistency_unconditional 𝗜𝚺₁ _ ComputableHorizon.ackermann

/-- **`thm:pazfc`, applied — the paper's own illustration.**  The inductor is trained on
`𝗜𝚺₁`, and the claims are the finite consistency statements of `𝗣𝗔`, a strictly stronger
theory: `𝗜𝚺₁ ⊬ Con(𝗣𝗔)`, yet the `𝗜𝚺₁`-trained inductor's belief in `Con(𝗣𝗔)(⌜Ack(n,n)⌝)`
converges to `1`.

Both theories are named, and nothing is left to the caller: `𝗜𝚺₁`'s three instances are
discharged in the repository (`Framework/Theory/R0Instances.lean`), `𝗣𝗔.Δ₁` is
Foundation's, and `Entailment.Consistent 𝗣𝗔` is Foundation's instance too, obtained from
soundness at the standard model (`Foundation`'s `Arithmetic/Schemata.lean`).  That semantic
route lives *inside this
witness only* — the endpoint above takes consistency as a hypothesis, exactly as the paper
does, and no soundness assumption reaches the trust surface. -/
example :
    (fun n => liaHistory (paperDP 𝗜𝚺₁) n
      (conClaimSentence (conGamma 𝗜𝚺₁ 𝗣𝗔 ComputableHorizon.ackermann) n)) ≈ₙ fun _ => 1 :=
  lic_belief_stronger_theory_consistency_unconditional 𝗜𝚺₁ 𝗣𝗔 inferInstance _
    ComputableHorizon.ackermann

/-- **The occurrence side condition, fully discharged at the paper's own illustration.**  The
diagonal Ackermann horizon is unbounded (`lt_ack_right`), so `conGamma 𝗜𝚺₁ 𝗜𝚺₁ ack` mentions
its argument slot with nothing left to the caller.

Kind `C` (composition).  Provenance: (a) derived in-project; (b) Mathlib citation —
`lt_ack_right`. -/
lemma conGamma_mentions_zero_ackermann :
    (conGamma 𝗜𝚺₁ 𝗜𝚺₁ ComputableHorizon.ackermann).Mentions 0 :=
  conGamma_mentions_zero_of_horizon_unbounded 𝗜𝚺₁ 𝗜𝚺₁ ComputableHorizon.ackermann
    (RepresentsComputations.consistent 𝗜𝚺₁) fun k => ⟨k, _root_.lt_ack_right k k⟩

/-- **The `thm:pac` family does not collapse: two concrete days, two different sentences.**
Applied at the same theory and horizon as the `thm:pac` witness above, with the occurrence
side condition discharged rather than assumed. -/
example :
    conClaimSentence (conGamma 𝗜𝚺₁ 𝗜𝚺₁ ComputableHorizon.ackermann) 0
      ≠ conClaimSentence (conGamma 𝗜𝚺₁ 𝗜𝚺₁ ComputableHorizon.ackermann) 1 :=
  conClaimSentence_ne_of_day_ne _ conGamma_mentions_zero_ackermann (by decide)

end Endpoints

/-! ## The unbounded halting family, at the paper's process

§4.10's `thm:halts` and `thm:loops` name the day-`n` claim "`⌜mₙ⌝ halts on `⌜xₙ⌝`".  Both
are stated below over `paperDP`, the single paper-facing market, and therefore
carry **no semantic hypothesis on `T`**: the positive literal is Σ₁-completeness
(`re_complete_mp`, which needs `[𝗥₀ ⪯ T]` and nothing else), the negative literal is the
paper's own object-level refutation premise, and market non-vacuity is
`paperDP_nonvacuous`, from consistency alone.

Two representation points, both shared with `thm:dontwait` above.

* **The schema is universal; the data is in the argument.**  The claim family is the
  instance family of the ONE fixed Σ₁ schema `universalHaltingSchema` — Foundation's r.e.
  formula for `UniversalCodeHalts z := (Code.ofSource z.unpair.1).eval z.unpair.2 |>.Dom`
  (`Construction/Knowledge/Syntax.lean`) — at the argument `⟨⌜mₙ⌝, xₙ⟩`
  (`haltingClaimInput`), spelled by the compact `binNumeral`.  So the day-`n` sentence names the
  day-`n` machine and its input, as the paper's `⌜mₙ⌝`/`⌜xₙ⌝` do (tex:1931).

  Putting the sequences *inside* the schema instead, as
  `codeOfREPred (fun n => CodeHalts (machines n) (inputs n))`, would be extensional: under
  `thm:halts`'s own `hhalts` the predicate is `fun _ => True` and under `thm:loops`'s premise
  it is refuted uniformly, so the schema — and hence the whole sentence family — would be the
  same for every admissible machine sequence and would name nothing.  Nor does a compact name
  cost anything in symbols: `binNumeral (haltingClaimInput mₙ xₙ)` costs `O(log)` of the
  pair's value, i.e. `O(|source of mₙ| + |digits of xₙ|)` symbols, and that is exactly the
  quantity `hm : DigitMachineCodes machines` and `hi : BigDigits inputs` bound polynomially.
  `hm` and `hi` are therefore consumed by the `def:ec` obligation, on which they are
  load-bearing, rather than by a free r.e.-ness step.

* **The vacuous existential.**  `paperPrimeDecompose` contracts a whole sentence to a single
  prime only at an `.exs` head (and at its `.all` negation); a `codeOfREPred` schema's head
  constructor is `Classical.epsilon`-chosen and unreachable, so no equation for its
  decomposition can be written.  `schemaArgClaim` therefore wraps the instance in one
  existential that binds nothing.  That changes nothing about what is claimed, and it is a
  theorem rather than a convention: `provable_schemaArgClaim_iff` and
  `provable_neg_schemaArgClaim_iff` show `T` proves (refutes) the wrapper exactly when it
  proves (refutes) the bare instance — so the wrapper never appears in an endpoint's
  hypothesis. -/

section Halting

/-- The claim of a fixed one-variable schema at an argument named by the closed term `t`:
`σ(t)` under one vacuous existential. -/
def schemaArgClaim (σ : ArithmeticSemisentence 1) (t : Semiterm.Const ℒₒᵣ) :
    ArithmeticSentence :=
  ∃⁰ (schemaArgBody σ t)

/-- The public propositional atom naming that claim: its paper-prime. -/
def schemaArgClaimSentence (σ : ArithmeticSemisentence 1) (t : Semiterm.Const ℒₒᵣ) :
    Sentence :=
  paperPrimeSentence true
    (Semiformula.exs (Rewriting.emb (schemaArgBody σ t) : ArithmeticSemiformula ℕ 1))

/-- **The claim family is `def:ec` emittable, for every `σ` and every emittable argument
naming.**  Definitionally the source certificate of
`Construction/Knowledge/SubstEmission.lean`: a fixed skeleton plus the argument term's own
symbol run, which is where the write-out hypotheses are spent.

Kind `C` (composition).  Provenance: (a) derived in-project from
`bigSentenceCodes_schemaArgClaim`. -/
lemma schemaArgClaimSentence_bigSentenceCodes (σ : ArithmeticSemisentence 1)
    (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ l : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))) :
    BigSentenceCodes (fun n => schemaArgClaimSentence σ (τ n)) :=
  bigSentenceCodes_schemaArgClaim σ τ henc

/-- The paper decomposition of the schema claim `∃ν σ(t, ν)` is the **positive** literal
`schemaArgClaimSentence σ t`. -/
lemma paperPrimeDecompose_schemaArgClaim (σ : ArithmeticSemisentence 1)
    (t : Semiterm.Const ℒₒᵣ) :
    paperPrimeDecompose ((schemaArgClaim σ t : ArithmeticSentence) : ArithmeticProposition)
      = schemaArgClaimSentence σ t := by
  have h : ((schemaArgClaim σ t : ArithmeticSentence) : ArithmeticProposition)
      = Semiformula.exs (Rewriting.emb (schemaArgBody σ t) : ArithmeticSemiformula ℕ 1) := by
    simp [schemaArgClaim]
    rfl
  rw [h, paperPrimeDecompose_exs, schemaArgClaimSentence]

/-- The paper decomposition of the *negated* schema claim is the **negative** literal
`∼schemaArgClaimSentence σ t`, the two forming one propositional pair. -/
lemma paperPrimeDecompose_neg_schemaArgClaim (σ : ArithmeticSemisentence 1)
    (t : Semiterm.Const ℒₒᵣ) :
    paperPrimeDecompose ((∼(schemaArgClaim σ t) : ArithmeticSentence) : ArithmeticProposition)
      = ∼schemaArgClaimSentence σ t := by
  have h : ((∼(schemaArgClaim σ t) : ArithmeticSentence) : ArithmeticProposition)
      = Semiformula.all
        (∼(Rewriting.emb (schemaArgBody σ t) : ArithmeticSemiformula ℕ 1)) := by
    simp [schemaArgClaim]
    rfl
  rw [h, paperPrimeDecompose_all, schemaArgClaimSentence]
  simp

/-- **Provability is invariant under a semantic equivalence.**  Both directions of the
completeness theorem for first-order theories: soundness carries a derivation to every model,
completeness carries validity back.  No hypothesis on `T`.

Kind `C` (composition).  Provenance: (b) Foundation citation —
`Theory.Proof.complete_iff`. -/
lemma provable_iff_of_realize_iff {T : ArithmeticTheory} {σ τ : ArithmeticSentence}
    (h : ∀ (M : Type) [Nonempty M] [Structure ℒₒᵣ M], σ.Realize M ↔ τ.Realize M) :
    T ⊢ σ ↔ T ⊢ τ := by
  rw [← LO.FirstOrder.Theory.Proof.complete_iff, ← LO.FirstOrder.Theory.Proof.complete_iff]
  simp only [consequence_iff, models_iff]
  exact ⟨fun H M _ _ hT => (h M).mp (H M hT), fun H M _ _ hT => (h M).mpr (H M hT)⟩

/-- **The vacuous existential is invisible to `T`, positively.**  The wrapper binds nothing,
so it is true in a model exactly when the bare instance is. -/
lemma provable_schemaArgClaim_iff (T : ArithmeticTheory) (σ : ArithmeticSemisentence 1)
    (t : Semiterm.Const ℒₒᵣ) :
    T ⊢ schemaArgClaim σ t ↔ T ⊢ (σ/[t.const] : ArithmeticSentence) :=
  provable_iff_of_realize_iff fun M _ _ => by
    simp [schemaArgClaim, schemaArgBody, Semiformula.eval_substs]

/-- **The vacuous existential is invisible to `T`, negatively.**  This is what lets
`thm:loops` state its premise at the bare instance. -/
lemma provable_neg_schemaArgClaim_iff (T : ArithmeticTheory) (σ : ArithmeticSemisentence 1)
    (t : Semiterm.Const ℒₒᵣ) :
    T ⊢ ∼(schemaArgClaim σ t) ↔ T ⊢ ∼(σ/[t.const] : ArithmeticSentence) :=
  provable_iff_of_realize_iff fun M _ _ => by
    simp [schemaArgClaim, schemaArgBody, Semiformula.eval_substs]

/-- The theorem process publishes the claim atom when `T` proves the argument instance. -/
lemma paperDP_covers_schemaArgClaim [T.Δ₁] (σ : ArithmeticSemisentence 1)
    (t : Semiterm.Const ℒₒᵣ) (h : T ⊢ (σ/[t.const] : ArithmeticSentence)) :
    ∃ k, schemaArgClaimSentence σ t ∈ (paperDP T).D k := by
  have := paperTheoryDP_covers_outer_provable T _ ((provable_schemaArgClaim_iff T σ t).mpr h)
  rw [paperPrimeDecompose_schemaArgClaim] at this
  exact paperDP_covers_of_paperTheoryDP T this

/-- The theorem process publishes the negated claim atom when `T` refutes the argument
instance. -/
lemma paperDP_covers_schemaArgClaim_neg [T.Δ₁]
    (σ : ArithmeticSemisentence 1) (t : Semiterm.Const ℒₒᵣ)
    (h : T ⊢ ∼(σ/[t.const] : ArithmeticSentence)) :
    ∃ k, (∼schemaArgClaimSentence σ t) ∈ (paperDP T).D k := by
  have := paperTheoryDP_covers_outer_provable T _
    ((provable_neg_schemaArgClaim_iff T σ t).mpr h)
  rw [paperPrimeDecompose_neg_schemaArgClaim] at this
  exact paperDP_covers_of_paperTheoryDP T this

/-! ### The halting claim: the universal schema at a machine-naming argument -/

/-- The `thm:halts`/`thm:loops` claim sentence for the day-`n` machine and input: the fixed
universal halting schema at the compact name of `⟨⌜mₙ⌝, xₙ⟩`.

This is where the machine dependence lives: the sentence depends on `machines` and
`inputs` through the *argument*, not through the schema, so distinct machine source numbers
give distinct sentences outright (`haltingArgClaimSentence_ne_of_source_ne`), and a fortiori
distinct halting behaviour does (`haltingArgClaimSentence_ne_of_halts_ne`). -/
noncomputable def haltingArgClaimSentence (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (n : ℕ) : Sentence :=
  schemaArgClaimSentence universalHaltingSchema
    (binNumeral (haltingClaimInput (machines n) (inputs n)))

/-- The bare arithmetic sentence under the claim atom: `⌜mₙ⌝ halts on ⌜xₙ⌝`, spelled with the
compact argument name.  `thm:loops` states its refutation premise here — literally the
negation of the sentence whose atom the endpoint's conclusion is about. -/
noncomputable def haltingArgClaimInstance (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (n : ℕ) : ArithmeticSentence :=
  universalHaltingSchema/[(binNumeral (haltingClaimInput (machines n) (inputs n))).const]

/-- **The claim sentence names the machine, in the standard model.**  The universal schema at
the compact name of `⟨⌜m⌝, x⌝` is true in `ℕ` exactly when `m` halts on `x`.  `binNumeral`
names its value in `ℕ` (a model of `𝗣𝗔⁻`), and `Code.ofSource` inverts `Code.sourceNat`.

Kind `C` (composition).  Provenance: (a) derived in-project; (b) Foundation citations —
`universalHaltingSchema_spec`, `binNumeral_val`. -/
lemma haltingArgClaimInstance_true_iff (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (n : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧ haltingArgClaimInstance machines inputs n ↔
      CodeHalts (machines n) (inputs n) := by
  have hval : (binNumeral (haltingClaimInput (machines n) (inputs n))).val
      (![] : Fin 0 → ℕ) = haltingClaimInput (machines n) (inputs n) := by
    simpa using binNumeral_val (M := ℕ) (haltingClaimInput (machines n) (inputs n))
  have hspec := universalHaltingSchema_spec (haltingClaimInput (machines n) (inputs n))
  rw [universalCodeHalts_claimInput] at hspec
  simp only [haltingArgClaimInstance, models_iff, Semiformula.eval_substs]
  rw [show (Semiterm.val ![] Empty.elim ∘
        ![((binNumeral (haltingClaimInput (machines n) (inputs n))).const :
          ArithmeticSemiterm Empty 0)])
      = ![(haltingClaimInput (machines n) (inputs n) : ℕ)] from ?_]
  · exact hspec
  · funext i
    fin_cases i
    simpa using hval

/-- **The schema claim atom determines its body.**  The same unwrapping for a fixed
one-variable schema, shared by the two separation lemmas below. -/
private lemma schemaArgBody_eq_of_schemaArgClaimSentence_eq {σ : ArithmeticSemisentence 1}
    {t t' : Semiterm.Const ℒₒᵣ}
    (h : schemaArgClaimSentence σ t = schemaArgClaimSentence σ t') :
    schemaArgBody σ t = schemaArgBody σ t' := by
  have hpair := paperPrimeSentence_injective
    (a₁ := (true, Semiformula.exs (Rewriting.emb (schemaArgBody σ t) :
      ArithmeticSemiformula ℕ 1)))
    (a₂ := (true, Semiformula.exs (Rewriting.emb (schemaArgBody σ t') :
      ArithmeticSemiformula ℕ 1)))
    h
  have hexs := congrArg Prod.snd hpair
  simp only [Semiformula.exs.injEq] at hexs
  exact Rewriting.emb_injective hexs

/-- **Behavioural separation of halting claims.**

Two `(machine, input)` pairs that differ in halting behaviour get **different** claim
sentences.

*What this is not.*  It is **not** the standing extensionality test of `KNOWLEDGE.md`
("same extension, different program ⇒ different sentence"), and it cannot be invoked inside
a single claim family: `thm:halts`'s `hhalts` and `thm:loops`'s `hloops` both forbid the
halting behaviour from varying with the day.  What it separates is two families that behave
differently.

Machine dependence of the sentence is proved separately, and more strongly, by
`haltingArgClaimSentence_ne_of_source_ne`: distinct machine source numbers give distinct
sentences whatever the machines do.  That is the standing extensionality test; this lemma is
the behavioural companion to it, not a substitute for it.

Kind `P` (proved).  Provenance: (a) derived in-project from
`haltingArgClaimInstance_true_iff`; (b) Foundation citations — `paperPrimeSentence_injective`,
`Rewriting.emb_injective`. -/
lemma haltingArgClaimSentence_ne_of_halts_ne
    (machines machines' : ℕ → Nat.Partrec.Code) (inputs inputs' : ℕ → ℕ) (n n' : ℕ)
    (h : CodeHalts (machines n) (inputs n))
    (h' : ¬ CodeHalts (machines' n') (inputs' n')) :
    haltingArgClaimSentence machines inputs n
      ≠ haltingArgClaimSentence machines' inputs' n' := by
  intro heq
  have hbody := schemaArgBody_eq_of_schemaArgClaimSentence_eq heq
  have key : ∀ (m : ℕ → Nat.Partrec.Code) (x : ℕ → ℕ) (k : ℕ),
      (schemaArgBody universalHaltingSchema
          (binNumeral (haltingClaimInput (m k) (x k)))).Evalb (![0] : Fin 1 → ℕ)
        ↔ CodeHalts (m k) (x k) := by
    intro m x k
    have hval : (binNumeral (haltingClaimInput (m k) (x k))).val (![] : Fin 0 → ℕ)
        = haltingClaimInput (m k) (x k) := by
      simpa using binNumeral_val (M := ℕ) (haltingClaimInput (m k) (x k))
    have hspec := universalHaltingSchema_spec (haltingClaimInput (m k) (x k))
    rw [universalCodeHalts_claimInput] at hspec
    simp only [schemaArgBody, Semiformula.eval_substs]
    rw [show (Semiterm.val ![(0 : ℕ)] Empty.elim ∘
          ![((binNumeral (haltingClaimInput (m k) (x k))).const :
            ArithmeticSemiterm Empty 1)])
        = ![(haltingClaimInput (m k) (x k) : ℕ)] from ?_]
    · exact hspec
    · funext i
      fin_cases i
      simpa using hval
  exact h' ((key machines' inputs' n').mp (hbody ▸ (key machines inputs n).mpr h))

/-- **Syntactic separation of schema claims at distinct arguments.**  If the fixed schema
`σ` really mentions its argument, then distinct closed argument terms give distinct claim
atoms — no behavioural hypothesis at all.  This is the general form of the standing
extensionality test recorded in `KNOWLEDGE.md`.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`Semiformula.eq_of_rew_eq_of_mentions` (`Framework/Theory/SubstOccurrence.lean`),
`paperPrimeSentence_injective`, `Rewriting.emb_injective`. -/
lemma schemaArgClaimSentence_ne_of_const_ne (σ : ArithmeticSemisentence 1)
    (hσ : σ.Mentions 0) (t t' : Semiterm.Const ℒₒᵣ)
    (h : (t.const : ArithmeticSemiterm Empty 1) ≠ (t'.const : ArithmeticSemiterm Empty 1)) :
    schemaArgClaimSentence σ t ≠ schemaArgClaimSentence σ t' := by
  intro heq
  refine h ?_
  have hbody := schemaArgBody_eq_of_schemaArgClaimSentence_eq heq
  have hrew : (Rew.subst ![(t.const : ArithmeticSemiterm Empty 1)]) ▹ σ
      = (Rew.subst ![(t'.const : ArithmeticSemiterm Empty 1)]) ▹ σ := hbody
  simpa using Semiformula.eq_of_rew_eq_of_mentions (k := (0 : Fin 1)) (by simpa using hσ) hrew

/-- **The standing extensionality test, proved.**  Two `(machine, input)` pairs with
distinct *names* — not merely distinct halting behaviour — get distinct claim sentences.

This is the test recorded in `KNOWLEDGE.md`: substitute two sequences with the same
extension but different programs; if the sentences coincided, the rendering would be
extensional.  They do not coincide.  Unlike `haltingArgClaimSentence_ne_of_halts_ne` this
*can* be invoked inside a single claim family, because no endpoint hypothesis constrains
the machine names.

Kind `P` (proved).  Provenance: (a) derived in-project from
`schemaArgClaimSentence_ne_of_const_ne`, `universalHaltingSchema_mentions_zero`,
`binNumeral_const_ne`. -/
lemma haltingArgClaimSentence_ne_of_claimInput_ne
    (machines machines' : ℕ → Nat.Partrec.Code) (inputs inputs' : ℕ → ℕ) (n n' : ℕ)
    (h : haltingClaimInput (machines n) (inputs n)
      ≠ haltingClaimInput (machines' n') (inputs' n')) :
    haltingArgClaimSentence machines inputs n
      ≠ haltingArgClaimSentence machines' inputs' n' :=
  schemaArgClaimSentence_ne_of_const_ne _ universalHaltingSchema_mentions_zero _ _
    (binNumeral_const_ne _ _ h)

/-- **The claim sentence names the program, not its behaviour.**  Distinct machine *source
numbers* on the two days give distinct claim sentences, whatever the machines do.

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma haltingArgClaimSentence_ne_of_source_ne
    (machines machines' : ℕ → Nat.Partrec.Code) (inputs inputs' : ℕ → ℕ) (n n' : ℕ)
    (h : Nat.Partrec.Code.sourceNat (machines n)
      ≠ Nat.Partrec.Code.sourceNat (machines' n')) :
    haltingArgClaimSentence machines inputs n
      ≠ haltingArgClaimSentence machines' inputs' n' := by
  refine haltingArgClaimSentence_ne_of_claimInput_ne _ _ _ _ _ _ ?_
  intro he
  exact h (Nat.pair_eq_pair.mp he).1

/-- **The `thm:halts`/`thm:loops` claim family, over the paper's own deductive process.**

The positive obligation is discharged by Σ₁-completeness at the *universal* schema; the
`def:ec` obligation is discharged internally by `schemaArgClaimSentence_bigSentenceCodes` at
the compact argument name, and that is what `hm` and `hi` are consumed by.

Kind `C` (composition).  Provenance: (a) derived in-project; (b) Foundation citation —
`codeOfREPred` and `sigma_one_completeness` (through `re_complete_mp`).  The paper nodes are
carried by the endpoints that consume it, not by this constructor. -/
noncomputable def representedHaltingClaims [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs) :
    RepresentedSemidecidableClaims (paperDP T)
      (fun n => CodeHalts (machines n) (inputs n)) where
  sentence := haltingArgClaimSentence machines inputs
  sentence_poly :=
    schemaArgClaimSentence_bigSentenceCodes universalHaltingSchema _
      (polySegStream_binNumeral_const (haltingClaimInput_digits hm hi))
  provable_of_true n hn := by
    refine paperDP_covers_schemaArgClaim T universalHaltingSchema _ ?_
    refine (provable_subst_binNumeral_iff T universalHaltingSchema _).mpr ?_
    exact re_complete_mp (T := T) universalCodeHalts_re
      ((universalCodeHalts_claimInput (machines n) (inputs n)).mpr hn)

/-! ### The paper-facing halting endpoints -/

section HaltingEndpoints

variable [T.Δ₁] [𝗣𝗔⁻ ⪯ T]

/-- **Learning of Halting Patterns** over the paper's theorem process.  `hm` and `hi` are the
paper's own e.c. classes, metered by *write-out*: tex:1931-1933 asks that the source of `mₙ`
be writable in time polynomial in `n`, and a poly-time writer emits polynomially many
symbols, so an `n`-digit description with an exponential Gödel code is admissible and `⟨x⟩`
is a sequence of bitstrings.  These classes are strictly wider than the corresponding
whole-value classes — see `digitMachineCodes_nest_not_polyMachineCodes` and
`bigDigits_two_pow_not_polyNatCodes`.
*Residual hypotheses (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the module's disclosed
strengthenings (module header; `LogicalInduction/README.md`).
Paper node: `thm:halts` -/
theorem lic_learns_halting_patterns_ofComputation
    (P : History) [IsLogicalInductor P (paperDP T)]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hhalts : ∀ n, CodeHalts (machines n) (inputs n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP T).D n)) :
    (fun n => P n ((representedHaltingClaims T machines inputs hm hi).sentence n)) ≈ₙ
      fun _ => 1 :=
  lic_learns_halting_patterns P (paperDP T) machines inputs
    (representedHaltingClaims T machines inputs hm hi) hhalts hworld

/-- **Learning of Provable Non-Halting Patterns** over the paper's theorem process.  `hloops`
is the paper's premise, literal object-level `T`-refutability of the day instance — not a
deductive-process emission surrogate, and not stated at the vacuous wrapper.
*Residual hypotheses (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the module's disclosed
strengthenings (module header; `LogicalInduction/README.md`).
Paper node: `thm:loops` -/
theorem lic_learns_provable_nonhalting_patterns_ofComputation
    (P : History) [IsLogicalInductor P (paperDP T)]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hloops : ∀ n : ℕ, T ⊢ ∼(haltingArgClaimInstance machines inputs n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP T).D n)) :
    (fun n => P n ((representedHaltingClaims T machines inputs hm hi).sentence n)) ≈ₙ
      fun _ => 0 :=
  lic_learns_provable_nonhalting_patterns P (paperDP T) machines inputs
    (representedHaltingClaims T machines inputs hm hi)
    (fun n => paperDP_covers_schemaArgClaim_neg T universalHaltingSchema _
      (hloops n)) hworld

variable [Entailment.Consistent T]

/-- `thm:halts`, unconditional over `LIA`.  The deductive process is the single
paper-facing market's, is proved computable (`paperDP_computable`), and its market
non-vacuity follows from
consistency of `T` alone, so nothing remains beyond the theory instances and the (true)
hypothesis that the machines halt.  In particular there is no soundness instance.
*Residual hypotheses (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the module's disclosed
strengthenings (module header; `LogicalInduction/README.md`).
Paper node: `thm:halts` -/
theorem lic_learns_halting_patterns_unconditional
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hhalts : ∀ n, CodeHalts (machines n) (inputs n)) :
    (fun n => liaHistory (paperDP T) n
      ((representedHaltingClaims T machines inputs hm hi).sentence n)) ≈ₙ fun _ => 1 :=
  haveI := paperLIA T
  lic_learns_halting_patterns_ofComputation T (liaHistory (paperDP T))
    machines inputs hm hi hhalts (paperDP_hworld_stages T inferInstance)

/-- `thm:loops`, unconditional over `LIA`.  `hm` and `hi` are the write-out metered classes
shared with `thm:halts`; `hloops` is the object-level refutation premise, which cannot be
discharged for an arbitrary `T` — see `loopsTheory` below for its witness.
*Residual hypotheses (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the module's disclosed
strengthenings (module header; `LogicalInduction/README.md`).
Paper node: `thm:loops` -/
theorem lic_learns_provable_nonhalting_patterns_unconditional
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hloops : ∀ n : ℕ, T ⊢ ∼(haltingArgClaimInstance machines inputs n)) :
    (fun n => liaHistory (paperDP T) n
      ((representedHaltingClaims T machines inputs hm hi).sentence n)) ≈ₙ fun _ => 0 :=
  haveI := paperLIA T
  lic_learns_provable_nonhalting_patterns_ofComputation T (liaHistory (paperDP T))
    machines inputs hm hi hloops (paperDP_hworld_stages T inferInstance)

/-- **`thm:halts`, applied.**  The machine family is `Nat.Partrec.Code.nest`, whose source
grows linearly in the day and whose source *number* is exponential (so the whole-value class
excludes it, `digitMachineCodes_nest_not_polyMachineCodes`), and whose halting hypothesis is
*proved* rather than assumed (`codeHalts_nest`).  The inputs are the paper's own `⟨x⟩` shape,
the `n`-bit string `2 ^ n`.  Nothing is left for the caller. -/
example :
    (fun n => liaHistory (paperDP T) n
      ((representedHaltingClaims T Nat.Partrec.Code.nest (fun n => 2 ^ n)
          Nat.Partrec.Code.bigDigits_sourceNat_nest bigDigits_two_pow).sentence n))
        ≈ₙ fun _ => 1 :=
  lic_learns_halting_patterns_unconditional T
    Nat.Partrec.Code.nest (fun n => 2 ^ n)
    Nat.Partrec.Code.bigDigits_sourceNat_nest bigDigits_two_pow
    (fun n => codeHalts_nest n (2 ^ n))

/-- **`thm:loops`, applied.**  Same growing machine family as `thm:halts`, same inputs, both
class hypotheses discharged — but `hloops` remains a hypothesis of the `example`, because it
is object-level `T`-refutability of a Π₁ fact and, *with the installed substrate*, there is
no route to it for an arbitrary `T`.  The obstruction is representational: the only bridges
Foundation gives to `T ⊢ …` for a `codeOfREPred` schema are positive (`re_complete`,
`re_complete_mp`), and the schema itself is picked by `Classical.epsilon`, so its shape is
unreachable and no `T` can be *shown* to refute a particular false instance.  What the
example establishes is that everything else in the signature is inhabitable at a genuinely
varying family.  `hloops` itself is separately shown inhabitable — at a specific, true, `Δ₁`
theory — by `loopsTheory_refutes` and `thm_loops_applied_at_loopsTheory` below. -/
example
    (hloops : ∀ n : ℕ,
      T ⊢ ∼(haltingArgClaimInstance Nat.Partrec.Code.nest (fun n => 2 ^ n) n)) :
    (fun n => liaHistory (paperDP T) n
      ((representedHaltingClaims T Nat.Partrec.Code.nest (fun n => 2 ^ n)
          Nat.Partrec.Code.bigDigits_sourceNat_nest bigDigits_two_pow).sentence n))
        ≈ₙ fun _ => 0 :=
  lic_learns_provable_nonhalting_patterns_unconditional T
    Nat.Partrec.Code.nest (fun n => 2 ^ n)
    Nat.Partrec.Code.bigDigits_sourceNat_nest bigDigits_two_pow hloops

end HaltingEndpoints

/-! ### N+ for `thm:loops`'s refutation premise

`lic_learns_provable_nonhalting_patterns_unconditional` carries the premise

  `hloops : ∀ n, T ⊢ ∼(haltingArgClaimInstance machines inputs n)`

— object-level `T`-**refutability** of the day-`n` halting claim, literally the negation of
the sentence the endpoint's conclusion is about.  Every other premise of that endpoint is
discharged at concrete data in the client section above; this one is not, and this section
supplies its witness.

The witness is a theory, not a derivation, and that is forced **by the installed substrate**,
not by mathematics.  Two arguments that look like they force it do not, and are recorded here
so nobody re-derives them:

* Σ₁-soundness does *not* forbid `T ⊢ ∼σ` for a false Σ₁ instance `σ`.  Refuting a false Σ₁
  sentence is proving a true Π₁ sentence, which `𝗜𝚺₁` and `𝗣𝗔` do routinely.
* Foundation's `incomplete_of_REPred_not_ComputablePred_Nat'` refutes only the *uniform*
  negative representation principle — that some `T` refutes *every* false instance.  It says
  nothing about any single instance, and a natural arithmetization of "`rfind' succ`
  diverges" is refutable in `𝗜𝚺₁` by a one-line induction.

What actually blocks a natural `T` here is *opacity of the schema*.
`universalHaltingSchema` is a `codeOfREPred`, chosen by `Classical.epsilon`
(`R0/Representation.lean:232-247`), so nothing about the chosen formula is provable beyond
its defining spec `codeOfREPred_spec`, which is a statement about standard-model truth.  The
only lemmas taking that spec to `T ⊢ …` are positive (`re_complete`, `re_complete_mp`), so
there is no handle by which any `T` could be *shown* to refute a particular false instance.
Hence no natural theory (`𝗜𝚺₁`, `𝗣𝗔`, `𝗭𝗙𝗖`) can be exhibited here *with this substrate*, and
the honest witness puts the Π₁ sentence into the theory as an axiom — the same device
Foundation uses for `T.Con` and `T.Incon`.

The witness family is constant, so one axiom covers every day: the sentence
`haltingArgClaimInstance (fun _ => neverHaltMachine) (fun _ => 0) n` does not depend on `n`.
That is a consequence of the machine sequence being constant, not of the day being absent
from the claim — at a varying family the witness would need a universally quantified axiom
over the argument slot. -/

/-- The one Π₁ sentence the witness theory adds: "`neverHaltMachine` does not halt on `0`",
spelled as the literal negation of the claim sentence the endpoint is about. -/
noncomputable def loopsWitnessSentence : ArithmeticSentence :=
  ∼(haltingArgClaimInstance (fun _ => neverHaltMachine) (fun _ => 0) 0)

/-- The added axiom is **true**, not merely consistent: `neverHaltMachine` provably halts on
nothing (`not_codeHalts_neverHaltMachine`).

Kind `C` (composition).  Provenance: (a) derived in-project from
`haltingArgClaimInstance_true_iff`. -/
lemma models_loopsWitnessSentence : ℕ↓[ℒₒᵣ] ⊧ loopsWitnessSentence := by
  have h := haltingArgClaimInstance_true_iff (fun _ => neverHaltMachine) (fun _ => 0) 0
  simp only [loopsWitnessSentence, models_iff, LogicalConnective.HomClass.map_neg]
  simp only [models_iff] at h
  exact fun hx => not_codeHalts_neverHaltMachine 0 (h.mp hx)

/-- **The witness theory for `thm:loops`'s refutation premise.**  `𝗜𝚺₁` together with one
true Π₁ axiom: "`neverHaltMachine` does not halt on `0`".

*What this establishes.*  The premise set of
`lic_learns_provable_nonhalting_patterns_unconditional` is inhabited by a theory that is
`Δ₁`-axiomatized, extends `𝗜𝚺₁` (hence `𝗥₀`), and is consistent — all instance arguments of
the endpoint are *discharged*, not assumed — and by a machine family whose non-halting is
*proved* (`not_codeHalts_neverHaltMachine`), so the endpoint's `≈ₙ fun _ => 0` conclusion is
semantically correct rather than vacuously satisfied.  Since every axiom is true in `ℕ`,
consistency comes from `ℕ↓[ℒₒᵣ] ⊧* loopsTheory` rather than from an unproved assumption.

*Disclosed weakness.*  `T ⊢ ∼σ` holds here **by axiom fiat**: `loopsTheory_refutes` is
`Entailment.by_axm`, not arithmetic reasoning.  This is the strongest witness available *with
the installed substrate*, and the obstruction is representational, not mathematical.  It is
emphatically **not** that refuting `σ` is impossible for a natural theory: `∼σ` is a true Π₁
sentence, and `𝗜𝚺₁` would refute a natural arithmetization of this particular non-halting
fact by induction.  The obstruction is that `universalHaltingSchema` is a `codeOfREPred`,
whose formula Foundation picks by `Classical.epsilon`: its shape is unreachable from the API,
the only property of it that can be cited is `codeOfREPred_spec` (standard-model truth), and
the only lemmas carrying that to `T ⊢ …` are the positive ones.

*The honest strengthenings,* if this premise is ever to be discharged for a natural `T`, are:
(i) a Π₁-reflection hypothesis on `T`, which is a genuine strengthening of the endpoint's
hypotheses and would have to be stated as such; or (ii) replacing `codeOfREPred` for this
schema by a hand-rolled Δ₀/Σ₁ halting formula carrying its own representability lemma, which
restores the shape of the formula to the API and would also address the other places in this
development where `Classical.epsilon`-chosen schemas are opaque.

Kind `N+`, provenance: (a) the `Δ₁`, `⪯`, consistency and non-halting facts are derived
in-project; (b) `𝗜𝚺₁.Δ₁`, `Theory.Δ₁.insert`, `WeakerThan.ofSubset` and the
`ℕ ⊧* T → T.SoundOn F` instance are Foundation citations; (c) **the refutation premise
itself** — the sentence is an axiom of the witness theory rather than a consequence of
arithmetic.
Paper node: `thm:loops` -/
noncomputable def loopsTheory : ArithmeticTheory := insert loopsWitnessSentence 𝗜𝚺₁

/-- Every axiom of `loopsTheory` is true in the standard model.  Σ₁-soundness and
consistency both follow from this, so neither is assumed. -/
instance models_loopsTheory : ℕ↓[ℒₒᵣ] ⊧* loopsTheory :=
  Semantics.ModelsSet.insert_iff.mpr ⟨models_loopsWitnessSentence, inferInstance⟩

/-- Adjoining one sentence to a `Δ₁` axiom set keeps it `Δ₁`, which supplies the
`[loopsTheory.Δ₁]` instance argument of `thm_loops_applied_at_loopsTheory`. -/
noncomputable instance loopsTheory_delta1 : loopsTheory.Δ₁ :=
  inferInstanceAs (LO.FirstOrder.Theory.Δ₁ (insert loopsWitnessSentence 𝗜𝚺₁))

/-- `loopsTheory` extends `𝗜𝚺₁`, which is where `thm_loops_applied_at_loopsTheory`'s
`[𝗣𝗔⁻ ⪯ loopsTheory]` instance argument comes from. -/
instance loopsTheory_isigma1 : (𝗜𝚺₁ : ArithmeticTheory) ⪯ loopsTheory :=
  Entailment.WeakerThan.ofSubset (Set.subset_insert _ _)

/-- The witness theory is **consistent**, so the premise set is not inhabited by a theory
that proves everything.  This is the Lean witness for the first sentence of `loopsTheory`'s
disclosure: the endpoint's instance arguments are *discharged*, not assumed. -/
lemma loopsTheory_consistent : Entailment.Consistent loopsTheory := inferInstance

/-- The witness theory is Σ₁-sound, from truth in `ℕ`; no endpoint here takes a soundness
instance. -/
lemma loopsTheory_soundOnSigma1 : loopsTheory.SoundOnHierarchy 𝚺 1 := inferInstance

/-- `loopsTheory` provably does not halt on the constant family — the endpoint's
`≈ₙ fun _ => 0` conclusion is therefore the semantically correct one.  This is the Lean
witness for the second sentence of `loopsTheory`'s disclosure: a machine family whose
non-halting is *proved*. -/
lemma loopsWitness_never_halts (n : ℕ) :
    ¬ CodeHalts ((fun _ => neverHaltMachine) n) ((fun _ => 0) n) :=
  not_codeHalts_neverHaltMachine 0

/-- **The refutation premise, discharged.**  By axiom membership — see the disclosure at
`loopsTheory`.  The claim sentence does not depend on the day here because the machine
sequence is constant. -/
lemma loopsTheory_refutes (n : ℕ) :
    loopsTheory ⊢ ∼(haltingArgClaimInstance (fun _ => neverHaltMachine) (fun _ => 0) n) :=
  Entailment.by_axm (Set.mem_insert _ _)

/-- **`thm:loops`, applied with nothing left to the caller.**  Every hypothesis and every
instance argument of `lic_learns_provable_nonhalting_patterns_unconditional` is discharged:
the write-out classes at the constant family, and the refutation premise at `loopsTheory`.
The machine family is constant here — the growth of the machine/input sequence is exercised
separately by the `thm:halts` and `thm:dontwait` clients above — because what this witness
exists to show is that the refutation premise is inhabitable at all.
Paper node: `thm:loops` -/
theorem thm_loops_applied_at_loopsTheory :
    (fun n => liaHistory (paperDP loopsTheory) n
      ((representedHaltingClaims loopsTheory (fun _ => neverHaltMachine) (fun _ => 0)
          (digitMachineCodes_const neverHaltMachine) (BigDigits.const 0)).sentence n))
        ≈ₙ fun _ => 0 :=
  lic_learns_provable_nonhalting_patterns_unconditional loopsTheory
    (fun _ => neverHaltMachine) (fun _ => 0)
    (digitMachineCodes_const neverHaltMachine) (BigDigits.const 0) loopsTheory_refutes

end Halting

/-! ## §4.10: disbelief in inconsistent theories, at the paper's process

`thm:incons` (tex:1893-1903) says: for an e.c. sequence `⟨Θ′⟩` of recursively axiomatizable
**inconsistent** theories, `ℙₙ(⌜⌜Θ′ₙ⌝ is inconsistent⌝) ≈ₙ 1`, and hence
`ℙₙ(⌜⌜Θ′ₙ⌝ is consistent⌝) ≈ₙ 0`.

**What the sentence is.**  The paper's `⌜Θ′⌝ is inconsistent` is the negation of the universal
generalization of `Con(Θ′)(ν)` (tex:1863-1866) — the unbounded `∃` over proofs of `⊥` from
`⌜Θ′⌝`.  It is therefore Σ₁, not decidable, so this lane is the *halting* lane's shape, not
the bounded lane's: one fixed r.e. schema, with the day's data in the argument.  No horizon
appears and no symbol measure is in play — the existential is over all proofs either way, so
the counting convention of `dd:symbolcount` does not reach this node.

**Which theories: the paper's own.**  `Θ′ₙ` is `theoryOf (mₙ)`, the theory whose axioms are
enumerated by an arbitrary partial recursive machine — that is, an arbitrary recursively
axiomatized theory.  There is **no base theory**: the day's theory is freestanding, is neither
required to extend nor to be extended by the market's theory `T`, may be infinitely
axiomatized (`thm_incons_applied_infinite` below exhibits a day-theory with infinitely many
axioms), and carries no `Δ₁` hypothesis of its own.  The premises are exactly the paper's two:
that the sequence is efficiently *named* (`hm`, on the machines' written sources — tex:1905,
tex:1931) and that each named theory is inconsistent (`hinc`).

**How one fixed sentence speaks of an arbitrary theory: compactness.**  Foundation's
derivability predicate takes its theory as a *meta* parameter (`Derivation T` is
`(construction T).Fixpoint`), so there is no uniform-in-theory-code derivability predicate to
represent, and building one would need a truth predicate over coded formulas, which Foundation
does not have.  This rendering never forms one.  It quantifies over coded machines
**externally**, at `V := ℕ`, and uses the fact that inconsistency is always witnessed by
*finitely many* axioms (`exists_inconsistent_list`, `Framework/Theory/BoundedConsistency.lean`;
Foundation's proof object carries its own axiom list, so no induction is needed).  A finite
list of written axioms splices into a single written conjunction (`combineSourceNats`,
`Construction/Knowledge/SourceWindow.lean`), and refuting that conjunction is a question of
**pure logic** — the empty theory, `Theory.Δ₁.empty`.  So the represented predicate is
`MachineTheoryInconsistent`: *some finite window of the machine's output, conjoined, is
refutable in `∅`*.  One r.e. predicate, no base theory, every recursively axiomatized theory
in range, and the day's theory entering only through the **argument**.

**The `def:ec` premise.**  The day's theory is named by the numeral naming its machine's
written source (`Nat.Partrec.Code.sourceNat`, `Framework/Emission/CodeSource.lean`), and the
premise is `hm : DigitMachineCodes m` — the standing write-out class for machine sequences,
the same one `thm:halts` uses.  This is the paper's own reading: "it must be possible to
write out the source code specifying `mₙ` in time polynomial in `n`.  The runtime of an
individual `mₙ` is
immaterial" (tex:1931); for theories, tex:1905 asks that they be "efficiently named".  Nothing
about the axioms themselves is metered: the day's axiom sources are produced *inside* the
machine, and the spliced window is parsed *inside* the represented predicate, where the paper
asks only for recursive enumerability.  `thm_incons_applied_deep` exercises exactly that gap —
a short machine source whose single axiom has `2 ^ Ω(n)` nodes in normal form.

**Presentation convention.**  Reading a machine as a presentation of a theory requires
fixing a convention; ours is `dd:machinetheory`, stated in the glossary in
`LogicalInduction.lean`.  Any other convention gives a coextensive class of theories but a
different represented predicate, and hence a different schema — which is why it is stated
rather than left implicit.

**The gate is load-bearing, not hygiene.**  "Names no sentence" has to be *decided*, because
the window is a computation, and `AdmissibleName`
(`Construction/Knowledge/SourceWindow.lean`) is what decides it; the ways an ungated splice
admits a machine presenting the *empty* theory are recorded there.  With the gate,
`machineTheoryInconsistent_iff` proves the represented predicate **equivalent** to the
convention's claim, in both directions.

**How far the convention reaches.**  What is *proved* is that every one-axiom theory is
presented, exactly — `theoryOf_const_ofNNF` shows `theoryOf (Code.const ⌜written σ⌝) = {σ}` —
and hence that the convention is not restrictive in what a single day's axiom may be:
`ArithSource.ofNNF` writes every sentence.  What is **not formalized** is the uniform half of
surjectivity: that for every r.e. set of sentences there is a *single* machine enumerating
their names.  That would need `encodeArithmeticFormulaSymbols` to be certified primitive
recursive at the level of Foundation formula codes, which this development does not do (the
emission side is metered instead, at `PolyArithmeticSourceSeq.bigDigits_sourceNat`).  The
endpoint does not consume it: `hinc` is stated at `theoryOf (m n)` for the machine the caller
supplies, so no enumeration theorem is needed to apply the theorem — the witnesses
`thm_incons_applied_deep` and `thm_incons_applied_infinite` construct their machines directly,
the second with infinitely many axioms per day.

**One family, not two.**  `consistencySentence` is the syntactic negation of
`inconsistencySentence`, as the paper defines it; the second conjunct costs no second
representation premise. -/

section Inconsistency

/-! ### The theory a machine presents -/

/-- **The theory enumerated by `m`.**  Its axioms are the sentences whose *written sources* `m`
outputs; an output that names no written sentence contributes nothing.  As a set this asks no
computability of `m` at all, and nothing bounds the number of axioms.

Every one-axiom theory is presented exactly (`theoryOf_const_ofNNF`); the uniform enumeration
half of surjectivity onto the recursively axiomatized theories is *not* formalized, and the
endpoint does not consume it — see the "How far the convention reaches" paragraph in the
section header, which states precisely what is and is not proved.

*Proof kind:* `Def`.  Reading a machine as a theory presentation is the convention
`dd:machinetheory`; see the section header. -/
def theoryOf (m : Nat.Partrec.Code) : ArithmeticTheory :=
  {σ : ArithmeticSentence | ∃ (b i : ℕ) (s : ArithSource 0),
      Nat.Partrec.Code.evaln b m i = some s.sourceNat ∧
      ArithSource.compile s = (↑σ : ArithmeticSemiformula ℕ 0)}

/-- Membership in `theoryOf`, in the form the witnesses use. -/
lemma mem_theoryOf {m : Nat.Partrec.Code} {σ : ArithmeticSentence} {b i : ℕ}
    {s : ArithSource 0} (hev : Nat.Partrec.Code.evaln b m i = some s.sourceNat)
    (hc : ArithSource.compile s = (↑σ : ArithmeticSemiformula ℕ 0)) : σ ∈ theoryOf m :=
  ⟨b, i, s, hev, hc⟩

/-- A theory with a logically refutable axiom is inconsistent — the cheapest route from a
machine's output to the endpoint's `hinc`.

Kind `C` (composition).  Provenance: (b) Foundation citations — `Entailment.by_axm`,
`Entailment.weakening!`, `Entailment.inconsistent_iff_provable_bot`, `Entailment.N!_iff_CO!`. -/
lemma not_consistent_of_refutable_mem {S : ArithmeticTheory} {σ : ArithmeticSentence}
    (hmem : σ ∈ S) (href : (∅ : ArithmeticTheory) ⊢ ∼σ) : ¬Entailment.Consistent S := by
  rw [Entailment.not_consistent_iff_inconsistent, Entailment.inconsistent_iff_provable_bot]
  exact (LO.Entailment.N!_iff_CO!.mp
    (Entailment.wk! (Set.empty_subset S) href)) ⨀ Entailment.by_axm hmem

/-- **The finite window, found.**  Any finite list of `m`'s axioms is emitted together in a
single budget-`b` run at some list of inputs, and — at that budget or any larger one — the
window's spliced writing denotes exactly the conjunction of the list.  This is the step that
turns the paper's premise into something one fixed r.e. predicate can check: the budget is
taken as the maximum over the list, so `Nat.Partrec.Code.evaln_mono` upgrades every earlier
output at once.

Kind `P` (proved).  Provenance: (a) derived in-project from `conjSource` and
`ArithSource.compile`; (b) Mathlib citation — `Nat.Partrec.Code.evaln_mono`. -/
lemma exists_window (m : Nat.Partrec.Code) :
    ∀ l : List ArithmeticSentence, (∀ σ ∈ l, σ ∈ theoryOf m) →
      ∃ (b : ℕ) (is : List ℕ) (ss : List (ArithSource 0)),
        (∀ b', b ≤ b' →
            is.map
                (fun i => gateName ((Nat.Partrec.Code.evaln b' m i).getD verumSourceNat))
              = ss.map ArithSource.sourceNat) ∧
        ArithSource.compile (conjSource ss)
          = (↑(listConj l) : ArithmeticSemiformula ℕ 0) := by
  intro l
  induction l with
  | nil =>
      intro _
      exact ⟨0, [], [], by simp, by simp [conjSource, ArithSource.compile]⟩
  | cons σ t ih =>
      intro hmem
      obtain ⟨b₀, i₀, s₀, hev, hcomp⟩ := hmem σ (by simp)
      obtain ⟨b₁, is, ss, hmap, hc⟩ := ih (fun τ hτ => hmem τ (by simp [hτ]))
      refine ⟨max b₀ b₁, i₀ :: is, s₀ :: ss, ?_, ?_⟩
      · intro b' hb'
        have h0 : Nat.Partrec.Code.evaln b' m i₀ = some s₀.sourceNat :=
          Nat.Partrec.Code.evaln_mono (le_trans (le_max_left _ _) hb') hev
        simp [h0, gateName_sourceNat hcomp, hmap b' (le_trans (le_max_right _ _) hb')]
      · simp only [conjSource, ArithSource.compile, hcomp, hc, listConj_cons]
        simp

/-! ### The represented predicate -/

/-- **The name of a source that writes a sentence names that sentence's negation.**  The
bridge between the emission side, which sees only written runs, and the deduction side, which
speaks of sentences.

Kind `C` (composition).  Provenance: (a) `negSourceFormulaCode_sourceNat` derived in-project;
(b) Foundation citations — `Semiformula.encode_emb`, `Semiformula.quote_eq_encode`. -/
lemma negSourceFormulaCode_sourceNat_of_sentence (s : ArithSource 0) (φ : ArithmeticSentence)
    (h : ArithSource.compile s = (↑φ : ArithmeticSemiformula ℕ 0)) :
    negSourceFormulaCode s.sourceNat = ⌜∼φ⌝ := by
  rw [negSourceFormulaCode_sourceNat, h]
  simp [LO.FirstOrder.Sentence.quote_eq_encode]

/-- **The day-window code, at a window that writes a list of sentences.**  The bridge between
the machine side, which emits numbers, and the deduction side, which speaks of sentences. -/
lemma negWindowCode_eq_quote {z w : ℕ} {ss : List (ArithSource 0)}
    {l : List ArithmeticSentence}
    (hw : axiomWindow z w = ss.map ArithSource.sourceNat)
    (hc : ArithSource.compile (conjSource ss)
      = (↑(listConj l) : ArithmeticSemiformula ℕ 0)) :
    negWindowCode z w = ⌜∼listConj l⌝ := by
  rw [negWindowCode, hw, combineSourceNats_map_sourceNat,
    negSourceFormulaCode_sourceNat_of_sentence (conjSource ss) (listConj l) hc]

/-- **What `thm:incons`'s sentence represents**: the machine written down by `z` emits, in some
finite window, axioms whose conjunction **pure logic** refutes.  It mentions no base theory at
all, and — because the window admits only names of written *sentences* — it is *equivalent* to
the presented theory being inconsistent, not merely implied by it: compactness gives the
forward direction (`machineTheoryInconsistent_of_not_consistent`), the gate gives the converse
(`not_consistent_theoryOf_of_machineTheoryInconsistent`), and `machineTheoryInconsistent_iff`
packages the two.

*Proof kind:* `Def`. -/
def MachineTheoryInconsistent (z : ℕ) : Prop :=
  ∃ w, ProvableCode (∅ : ArithmeticTheory) (negWindowCode z w)

/-- **The predicate is r.e.**  Not by an r.e.-projection theorem — Mathlib has none — but
because the matrix is *decidable*: `Bootstrapping.Proof` is `𝚫₁`, so `ProofPacked ∅` is a
`ComputablePred` (`proofPacked_computable`), and an existential over a decidable matrix is r.e.
by `Partrec.rfind` and `Partrec.dom_re`.

Kind `C` (composition).  Provenance: (a) `negWindowCode_computable`, `proofPacked_computable`
derived in-project; (b) Mathlib citations — `ComputablePred.computable_iff`, `Partrec.rfind`,
`Partrec.dom_re`, `Nat.rfind_dom`. -/
lemma machineTheoryInconsistent_re : REPred MachineTheoryInconsistent := by
  obtain ⟨g, hg, hgspec⟩ := ComputablePred.computable_iff.mp
    (proofPacked_computable (∅ : ArithmeticTheory))
  have key : ∀ z : ℕ, MachineTheoryInconsistent z ↔
      ∃ u : ℕ, g (Nat.pair u.unpair.1 (negWindowCode z u.unpair.2)) = true := by
    intro z
    constructor
    · rintro ⟨w, d, hd⟩
      refine ⟨Nat.pair d w, ?_⟩
      have hpk : ProofPacked (∅ : ArithmeticTheory) (Nat.pair d (negWindowCode z w)) := by
        rw [proofPacked_pair_iff]; exact hd
      rw [hgspec] at hpk
      simpa using hpk
    · rintro ⟨u, hu⟩
      refine ⟨u.unpair.2, u.unpair.1, ?_⟩
      have hpk : ProofPacked (∅ : ArithmeticTheory)
          (Nat.pair u.unpair.1 (negWindowCode z u.unpair.2)) := by
        rw [hgspec]; exact hu
      rw [proofPacked_pair_iff] at hpk
      exact hpk
  have hF : Computable₂ fun z u : ℕ => g (Nat.pair u.unpair.1 (negWindowCode z u.unpair.2)) :=
    hg.comp (Primrec₂.natPair.to_comp.comp
      (Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp Computable.snd))
      (negWindowCode_computable.comp Computable.fst
        (Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp Computable.snd))))
  refine ((Partrec.rfind hF.partrec₂).dom_re).of_eq fun z => ?_
  simp [Nat.rfind_dom, key z]

/-- **The universal inconsistency schema.**  Foundation's r.e. formula for
`MachineTheoryInconsistent`: one schema for the whole theorem, with the day's theory entering
only through the argument.  Note what does *not* appear — no base theory, no `Δ₁` hypothesis on
the day's theory, no relation to the market's theory. -/
noncomputable def inconsistencySchema : ArithmeticSemisentence 1 :=
  codeOfREPred MachineTheoryInconsistent

/-- The schema has exactly the intended standard-model meaning. -/
lemma inconsistencySchema_spec (z : ℕ) :
    inconsistencySchema.Evalb ![z] ↔ MachineTheoryInconsistent z :=
  codeOfREPred_spec machineTheoryInconsistent_re (x := z)

/-! ### The truth obligation, and its converse witness -/

/-- **The paper's premise, delivered to the schema.**  If the theory a machine presents is
inconsistent then the machine's *name* satisfies the represented predicate.  The chain is:
compactness gives a finite inconsistent sublist of the day's axioms
(`exists_inconsistent_list`); a common budget and input list emit all of them at once
(`exists_window`); their spliced writing names their conjunction
(`combineSourceNats_map_sourceNat`); pure logic refutes that conjunction
(`provable_neg_listConj_of_not_consistent`); and that arithmetizes by
`Bootstrapping.provable_iff_provable`.

Kind `C` (composition).  Provenance: (a) derived in-project throughout; (b) Foundation
citations — `Theory.Proof`, `Entailment.deduction_iff`,
`Bootstrapping.provable_iff_provable`. -/
lemma machineTheoryInconsistent_of_not_consistent {m : Nat.Partrec.Code}
    (h : ¬Entailment.Consistent (theoryOf m)) :
    MachineTheoryInconsistent m.sourceNat := by
  obtain ⟨l, hmem, hinc⟩ := exists_inconsistent_list h
  obtain ⟨b, is, ss, hmap, hc⟩ := exists_window m l hmem
  refine ⟨Nat.pair b (Encodable.encode is), ?_⟩
  have hw : axiomWindow m.sourceNat (Nat.pair b (Encodable.encode is))
      = ss.map ArithSource.sourceNat := by
    rw [axiomWindow]
    simp only [Nat.unpair_pair, Nat.Partrec.Code.ofSource_sourceNat, Denumerable.ofNat_encode]
    exact hmap b le_rfl
  rw [negWindowCode_eq_quote hw hc, provableCode_quote_iff]
  exact provable_neg_listConj_of_not_consistent hinc

/-- The sentences a window's sources denote, as a list, together with where each one comes
from: either it is the inert `⊤` or it is an axiom of the presented theory. -/
private lemma exists_listConj_of_window_sources {m : Nat.Partrec.Code} {b : ℕ}
    {ss : List (ArithSource 0)}
    (hall : ∀ s ∈ ss, ∃ σ : ArithmeticSentence,
      ArithSource.compile s = (↑σ : ArithmeticSemiformula ℕ 0) ∧
        (σ = ⊤ ∨ ∃ i, Nat.Partrec.Code.evaln b m i = some (ArithSource.sourceNat s))) :
    ∃ l : List ArithmeticSentence,
      ArithSource.compile (conjSource ss) = (↑(listConj l) : ArithmeticSemiformula ℕ 0) ∧
        ∀ σ ∈ l, σ = ⊤ ∨ σ ∈ theoryOf m := by
  induction ss with
  | nil => exact ⟨[], by simp [conjSource], by simp⟩
  | cons s ss ih =>
      obtain ⟨σ, hc, hor⟩ := hall s (by simp)
      obtain ⟨l, hcl, hml⟩ := ih fun t ht => hall t (by simp [ht])
      refine ⟨σ :: l, ?_, ?_⟩
      · simp only [conjSource, ArithSource.compile, hc, hcl, listConj_cons]
        simp
      · intro τ hτ
        rcases List.mem_cons.mp hτ with heq | hτ'
        · subst heq
          rcases hor with hσ | ⟨i, hi⟩
          · exact Or.inl hσ
          · exact Or.inr (mem_theoryOf hi hc)
        · exact hml τ hτ'

/-- **The converse: a refutable window means an inconsistent theory.**  This is what makes
the represented sentence *say* the convention's inconsistency claim rather than merely follow
from it.  The gate (`AdmissibleName`, `Construction/Knowledge/SourceWindow.lean`) is what
buys it: at *every* argument `w`, the window is literally a list of names of written
sentences (`exists_sources_axiomWindow`), each of which the machine emitted — the inert `⊤`
filler excepted, which any theory proves.  So a window that pure logic refutes is a finite
subset of `theoryOf m`, padded with `⊤`s, that pure logic refutes.

Ungated, this direction is **false**, not merely unproved: two incomplete runs splice into
one complete refutable run, and non-names decode like names, so a machine presenting the
empty theory could satisfy the predicate.

Kind `P` (proved).  Provenance: (a) `exists_sources_axiomWindow`,
`exists_listConj_of_window_sources`, `negWindowCode_eq_quote` derived in-project;
(b) Foundation citations — `Bootstrapping.provable_iff_provable`, `Entailment.by_axm`,
`Entailment.wk!`, `Entailment.N!_iff_CO!`. -/
lemma not_consistent_theoryOf_of_machineTheoryInconsistent {m : Nat.Partrec.Code}
    (h : MachineTheoryInconsistent m.sourceNat) :
    ¬Entailment.Consistent (theoryOf m) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨ss, hmap, hall⟩ := exists_sources_axiomWindow m.sourceNat w
  rw [Nat.Partrec.Code.ofSource_sourceNat] at hall
  obtain ⟨l, hc, hml⟩ := exists_listConj_of_window_sources hall
  rw [negWindowCode_eq_quote hmap hc, provableCode_quote_iff] at hw
  have hprov : theoryOf m ⊢ listConj l :=
    provable_listConj (theoryOf m) fun φ hφ => by
      rcases hml φ hφ with hφ' | hφ'
      · rw [hφ']; cl_prover
      · exact Entailment.by_axm hφ'
  intro hcons
  exact hcons.not_bot
    ((LO.Entailment.N!_iff_CO!.mp (Entailment.wk! (Set.empty_subset _) hw)) ⨀ hprov)

/-- **The represented predicate is exactly the convention's inconsistency claim.**  Both
directions, at every machine: no gap between what `thm:incons`'s day-`n` sentence says and
what `hinc` supplies.  This is the faithfulness bridge for the node — it is what licenses
reading `inconsistencySentence n` as the paper's "`⌜Θ′ₙ⌝` is inconsistent" rather than as
some broader emitted-stream property — so it is inventoried and axiom-checked with the
node's endpoints.

Kind `C` (composition) of `machineTheoryInconsistent_of_not_consistent` (compactness) and
`not_consistent_theoryOf_of_machineTheoryInconsistent` (the gate).
Paper node: `thm:incons` -/
lemma machineTheoryInconsistent_iff (m : Nat.Partrec.Code) :
    MachineTheoryInconsistent m.sourceNat ↔ ¬Entailment.Consistent (theoryOf m) :=
  ⟨not_consistent_theoryOf_of_machineTheoryInconsistent,
    machineTheoryInconsistent_of_not_consistent⟩

private lemma compile_conjSource_replicate_verum (k : ℕ) :
    ArithSource.compile
        (conjSource (List.replicate k (ArithSource.leaf (⊤ : ArithmeticSemiformula ℕ 0))))
      = (↑(listConj (List.replicate k (⊤ : ArithmeticSentence)))
          : ArithmeticSemiformula ℕ 0) := by
  induction k with
  | zero => simp [conjSource, ArithSource.compile]
  | succ k ih => simp [List.replicate_succ, conjSource, ArithSource.compile, ih]

/-- **A machine that never outputs presents the empty theory, and the predicate knows it.**
Every window is then a conjunction of `⊤`s, which pure logic proves rather than refutes.  This
is the negative half of the schema's argument-sensitivity, and it needs **no consistency
hypothesis on anything**: the represented predicate is non-constant outright.

Kind `P` (proved).  Provenance: (a) derived in-project from `consistent_empty` and
`provable_listConj`. -/
lemma not_machineTheoryInconsistent_of_diverges {m : Nat.Partrec.Code}
    (h : ∀ b i, Nat.Partrec.Code.evaln b m i = none) :
    ¬ MachineTheoryInconsistent m.sourceNat := by
  rintro ⟨w, hw⟩
  have hwin : axiomWindow m.sourceNat w
      = (List.replicate (Denumerable.ofNat (List ℕ) w.unpair.2).length
          (ArithSource.leaf (⊤ : ArithmeticSemiformula ℕ 0))).map ArithSource.sourceNat := by
    rw [axiomWindow, List.map_replicate]
    simp only [Nat.Partrec.Code.ofSource_sourceNat, h, Option.getD_none,
      gateName_verumSourceNat]
    exact List.map_const'
  rw [negWindowCode_eq_quote hwin (compile_conjSource_replicate_verum _),
    provableCode_quote_iff] at hw
  have hprov : (∅ : ArithmeticTheory) ⊢
      listConj (List.replicate (Denumerable.ofNat (List ℕ) w.unpair.2).length
        (⊤ : ArithmeticSentence)) :=
    provable_listConj ∅ (fun φ hφ => by
      rw [List.eq_of_mem_replicate hφ]; cl_prover)
  exact consistent_empty.not_bot ((LO.Entailment.N!_iff_CO!.mp hw) ⨀ hprov)

/-- The never-halting machine never emits, at any budget: `evaln` is sound for `eval`. -/
lemma evaln_neverHaltMachine (b i : ℕ) :
    Nat.Partrec.Code.evaln b neverHaltMachine i = none := by
  rcases hv : Nat.Partrec.Code.evaln b neverHaltMachine i with _ | v
  · rfl
  · exact absurd (Part.dom_iff_mem.mpr ⟨v, Nat.Partrec.Code.evaln_sound hv⟩)
      (not_codeHalts_neverHaltMachine i)

/-- The one-token source `⊥`: the shortest inconsistent axiom there is, used to inhabit the
positive half of the schema's argument-sensitivity. -/
def falsumSource : ArithSource 0 := ArithSource.leaf (⊥ : ArithmeticSemiformula ℕ 0)

@[simp] lemma compile_falsumSource :
    ArithSource.compile falsumSource =
      (↑(⊥ : ArithmeticSentence) : ArithmeticSemiformula ℕ 0) := by
  simp [falsumSource, ArithSource.compile]

/-- A machine that outputs a constant reaches that output at some budget. -/
private lemma exists_evaln_const (v i : ℕ) :
    ∃ b, Nat.Partrec.Code.evaln b (Nat.Partrec.Code.const v) i = some v := by
  have hv : v ∈ Nat.Partrec.Code.eval (Nat.Partrec.Code.const v) i := by simp
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
  exact ⟨k, hk⟩

/-- The machine that keeps writing `⊥` presents an inconsistent theory. -/
lemma not_consistent_theoryOf_falsumMachine :
    ¬Entailment.Consistent (theoryOf (Nat.Partrec.Code.const falsumSource.sourceNat)) := by
  obtain ⟨b, hb⟩ := exists_evaln_const falsumSource.sourceNat 0
  exact not_consistent_of_refutable_mem (mem_theoryOf hb compile_falsumSource) (by cl_prover)

/-- **Every one-axiom theory is presented, exactly.**  The machine that keeps writing the name
of `σ`'s own written source presents `{σ}` and nothing else — so the presentation convention
`dd:machinetheory` reaches every singleton theory, with no slack in either direction.

The `⊇` half is the naming round trip; the `⊆` half is where the convention earns its keep:
a machine's output is a *number*, and two different sources may share a written run
(`leaf (φ ⋏ ψ)` and `and (leaf φ) (leaf ψ)` do), but sources with equal runs compile to equal
formulas (`ArithSource.compile_eq_of_sourceTokens_eq`), so a run names at most one sentence.

This is the *proved* part of the surjectivity claim at `theoryOf`; see the disclosure there
for what is not proved.

Kind `P` (proved).  Provenance: (a) `ArithSource.sourceNat_ne_of_sourceTokens_ne`,
`ArithSource.compile_eq_of_sourceTokens_eq` derived in-project; (b) Mathlib/Foundation
citations — `Nat.Partrec.Code.evaln_sound`, `Rewriting.emb_injective`.
Paper node: `thm:incons` -/
lemma theoryOf_const_ofNNF (σ : ArithmeticSentence) :
    theoryOf (Nat.Partrec.Code.const
        (ArithSource.ofNNF (↑σ : ArithmeticSemiformula ℕ 0)).sourceNat) = {σ} := by
  ext τ
  constructor
  · rintro ⟨b, i, s, hev, hc⟩
    have hmem := Nat.Partrec.Code.evaln_sound hev
    have hval : ArithSource.sourceNat s
        = (ArithSource.ofNNF (↑σ : ArithmeticSemiformula ℕ 0)).sourceNat := by
      simpa using hmem
    have htok : ArithSource.sourceTokens s
        = ArithSource.sourceTokens (ArithSource.ofNNF (↑σ : ArithmeticSemiformula ℕ 0)) := by
      by_contra hne
      exact ArithSource.sourceNat_ne_of_sourceTokens_ne hne hval
    have hcs := ArithSource.compile_eq_of_sourceTokens_eq htok
    rw [hc, ArithSource.compile_ofNNF] at hcs
    exact Rewriting.emb_injective hcs
  · rintro rfl
    obtain ⟨b, hb⟩ :=
      exists_evaln_const (ArithSource.ofNNF (↑τ : ArithmeticSemiformula ℕ 0)).sourceNat 0
    exact mem_theoryOf hb (ArithSource.compile_ofNNF _)

/-- **The schema is not argument-insensitive** — with no hypothesis at all.  Its shape is
unreachable (`codeOfREPred` is picked by `Classical.epsilon`), but its defining spec is not
nothing: the machine that keeps writing `⊥` presents an inconsistent theory, and the machine
that never writes anything presents the empty one.

Kind `P` (proved).  Provenance: (a) derived in-project from
`machineTheoryInconsistent_of_not_consistent` and
`not_machineTheoryInconsistent_of_diverges`. -/
lemma inconsistencySchema_not_argument_insensitive :
    ¬ ∀ z z' : ℕ, inconsistencySchema.Evalb ![z] ↔ inconsistencySchema.Evalb ![z'] := by
  intro h
  have hz : inconsistencySchema.Evalb
      ![(Nat.Partrec.Code.const falsumSource.sourceNat).sourceNat] :=
    (inconsistencySchema_spec _).mpr
      (machineTheoryInconsistent_of_not_consistent not_consistent_theoryOf_falsumMachine)
  have hz' : ¬ inconsistencySchema.Evalb ![neverHaltMachine.sourceNat] := fun hx =>
    not_machineTheoryInconsistent_of_diverges evaln_neverHaltMachine
      ((inconsistencySchema_spec _).mp hx)
  exact hz' ((h _ _).mp hz)

/-- **The schema mentions its argument**, the occurrence form of the previous lemma and the
side condition of substitution injectivity — again with no hypothesis.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`Semiformula.subst_eq_of_not_mentions` (`Framework/Theory/SubstOccurrence.lean`),
`Semiformula.eval_substs`. -/
lemma inconsistencySchema_mentions_zero :
    (inconsistencySchema : ArithmeticSemisentence 1).Mentions 0 := by
  by_contra hmem
  refine inconsistencySchema_not_argument_insensitive fun z z' => ?_
  have key : ∀ w : ℕ,
      Semiformula.Evalb (M := ℕ) (![] : Fin 0 → ℕ)
          (inconsistencySchema/[(‘↑w’ : Semiterm ℒₒᵣ Empty 0)])
        ↔ inconsistencySchema.Evalb ![w] := by
    intro w
    simp [Semiformula.eval_substs]
  have hsub := Semiformula.subst_eq_of_not_mentions hmem
    (‘↑z’ : Semiterm ℒₒᵣ Empty 0) (‘↑z'’ : Semiterm ℒₒᵣ Empty 0)
  rw [← key z, ← key z', hsub]

/-! ### The claim family and the endpoint -/

/-- **The day-`n` name of the theory `Θ′ₙ`**: the numeral naming the day's machine **as it is
written**.

`def:ec` (tex:753, tex:1931) meters a trader by the symbols it emits, and what this sentence
emits is the day machine's source run, read as a base-`16` numeral by
`Nat.Partrec.Code.sourceNat` (`Framework/Emission/CodeSource.lean`).  The theory's axioms are not
written out and are not metered — the machine produces them, and the paper is explicit that
"the runtime of an individual `mₙ` is immaterial".  This is the same naming doctrine the
halting lane applies to machines (`DigitMachineCodes`, `Framework/Emission/WriteOut.lean`),
and it is what admits day-theories whose axioms are astronomically large, or infinitely
many. -/
def machineArg (m : ℕ → Nat.Partrec.Code) (n : ℕ) : ℕ := (m n).sourceNat

/-- **The paper's “`⌜Θ′ₙ⌝` is inconsistent”**: the universal inconsistency schema at the
compact name of the day's machine. -/
noncomputable def inconsistencyArgClaimSentence (m : ℕ → Nat.Partrec.Code) (n : ℕ) :
    Sentence :=
  schemaArgClaimSentence inconsistencySchema (binNumeral (machineArg m n))

/-- The bare arithmetic sentence under the claim atom, for callers that need it. -/
noncomputable def inconsistencyArgClaimInstance (m : ℕ → Nat.Partrec.Code) (n : ℕ) :
    ArithmeticSentence :=
  inconsistencySchema/[(binNumeral (machineArg m n)).const]

/-- **The standing extensionality test, proved with no hypothesis.**  Days whose theories are
*presented differently* — not merely days whose theories behave differently — get distinct
claim sentences.  This is what makes `m` load-bearing rather than decorative, and it is
unconditional here because `inconsistencySchema_mentions_zero` is.

Kind `C` (composition).  Provenance: (a) derived in-project from
`schemaArgClaimSentence_ne_of_const_ne`, `inconsistencySchema_mentions_zero`,
`binNumeral_const_ne`. -/
lemma inconsistencyArgClaimSentence_ne_of_arg_ne (m m' : ℕ → Nat.Partrec.Code) (n n' : ℕ)
    (h : machineArg m n ≠ machineArg m' n') :
    inconsistencyArgClaimSentence m n ≠ inconsistencyArgClaimSentence m' n' :=
  schemaArgClaimSentence_ne_of_const_ne _ inconsistencySchema_mentions_zero _ _
    (binNumeral_const_ne _ _ h)

/-- **The `thm:incons` claim family, over the paper's own deductive process.**

The positive obligation is Σ₁-completeness at the universal schema (`re_complete_mp`, which
needs `[𝗣𝗔⁻ ⪯ T]` and nothing else); the `def:ec` obligation is discharged at the numeral naming
the day's machine, and that is what `hm` is consumed by.  No semantic hypothesis on `T`, no
hypothesis relating `T` to the day's theories, and no hypothesis on the day's theories beyond
the paper's own — that they are inconsistent.

Kind `C` (composition).  Provenance: (a) derived in-project; (b) Foundation citations —
`codeOfREPred` and `sigma_one_completeness` (through `re_complete_mp`),
`Theory.Proof` / `Entailment.deduction_iff` / `Bootstrapping.provable_iff_provable` (through
`machineTheoryInconsistent_of_not_consistent`). -/
noncomputable def representedInconsistentTheoryClaims [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    (m : ℕ → Nat.Partrec.Code) (hm : DigitMachineCodes m) :
    InconsistentTheoryClaims (paperDP T)
      (fun n => ¬Entailment.Consistent (theoryOf (m n))) where
  inconsistencySentence := inconsistencyArgClaimSentence m
  inconsistency_poly :=
    schemaArgClaimSentence_bigSentenceCodes inconsistencySchema _
      (polySegStream_binNumeral_const hm)
  inconsistency_provable n hn := by
    refine paperDP_covers_schemaArgClaim T inconsistencySchema _ ?_
    refine (provable_subst_binNumeral_iff T inconsistencySchema _).mpr ?_
    exact re_complete_mp (T := T) machineTheoryInconsistent_re
      (machineTheoryInconsistent_of_not_consistent hn)

/-- **Disbelief in Inconsistent Theories** (`thm:incons`), unconditional over `LIA`.  Both of
the paper's conjuncts: belief in the day-`n` inconsistency sentence tends to `1`, and belief in
its negation — the paper's consistency sentence — tends to `0`.

The premises are the paper's own two, and no others.  `hm` is `def:ec` on the *naming* of the
theory sequence, stated on the machines' written sources; `hinc` is the paper's premise that
each `Θ′ₙ` is inconsistent, stated at the theory `theoryOf (mₙ)` itself rather than at any
provability surrogate.  The day's theories are arbitrary recursively axiomatized theories:
freestanding, possibly infinitely axiomatized, unrelated to `T`, and carrying no `Δ₁`
hypothesis.

*Residual hypotheses (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the module's disclosed
strengthenings, and here they bear on the **market's** theory only (module header;
`LogicalInduction/README.md`).

*Paper defect (recorded in `LogicalInduction/notes/paper-errata.md`).*  The paper's proof
(tex:4487-4491) argues "provable in `𝗣𝗔`, and `Θ` can represent computable functions, therefore
provable in `Θ`".  Representability of computable functions does not give `𝗣𝗔 ⊢ ψ ⇒ Θ ⊢ ψ`;
Σ₁-completeness does, and the paper never states it.  This development takes the
Σ₁-completeness route (`re_complete_mp`, `[𝗣𝗔⁻ ⪯ T]`), i.e. it is correct where the printed
proof is loose.
Paper node: `thm:incons` -/
theorem lic_disbelief_inconsistent_theories_unconditional [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] (m : ℕ → Nat.Partrec.Code) (hm : DigitMachineCodes m)
    (hinc : ∀ n, ¬Entailment.Consistent (theoryOf (m n))) :
    ((fun n => liaHistory (paperDP T) n
        ((representedInconsistentTheoryClaims T m hm).inconsistencySentence n))
          ≈ₙ fun _ => 1) ∧
      ((fun n => liaHistory (paperDP T) n
        ((representedInconsistentTheoryClaims T m hm).consistencySentence n))
          ≈ₙ fun _ => 0) :=
  haveI := paperLIA T
  lic_disbelief_inconsistent_theories (liaHistory (paperDP T)) (paperDP T) _
    (representedInconsistentTheoryClaims T m hm) hinc
    (paperDP_hworld_stages T inferInstance)

/-! ### Witnesses

Both are day-varying and both discharge every hypothesis and every instance argument.  They
share one fixed program, `deepSourceCode`, which writes the source of the day's axiom; the
day number
reaches it through `dayMachine` (`Construction/Knowledge/DayMachine.lean`), which carries the
day inside the machine's own source and therefore discharges `def:ec` by
`digitMachineCodes_dayMachine`.

The day-`k` axiom is the paper-written

    (∀x. A(x) ⟺ A(x) ⟺ ⋯ ⟺ A(x)) ∧ ⊥

with `k` biconditionals: `5k + 7` symbols to write, `≥ 2 ^ k` nodes in Foundation's normal
form (`two_pow_le_encode_iffChain`), and a Gödel code doubly exponential in *that*.  None of
that is metered here — only the day machine's source is — which is exactly the width the
`def:ec` premise is supposed to have. -/

/-- The day-`k` axiom, as the paper writes it: `k` biconditionals under a quantifier,
conjoined with `⊥`.  `⟺` is one of the paper's own primitive connectives (tex:560), so the
writing is `5k + 7` symbols. -/
def deepInconsistentSource (k : ℕ) : ArithSource 0 :=
  .and (.all (iffChainSource k)) (.leaf (⊥ : ArithmeticSemiformula ℕ 0))

/-- The sentence that writing denotes.  In Foundation's negation normal form it has `≥ 2 ^ k`
nodes (`two_pow_le_encode_iffChain`), and its Gödel code is doubly exponential in that. -/
noncomputable def deepInconsistentAxiom (k : ℕ) : ArithmeticSentence :=
  Semiformula.all (iffChain k) ⋏ ⊥

lemma compile_deepInconsistentSource (k : ℕ) :
    ArithSource.compile (deepInconsistentSource k) =
      (↑(deepInconsistentAxiom k) : ArithmeticSemiformula ℕ 0) := by
  have hall (ψ : ArithmeticSemisentence 1) :
      (Rewriting.emb (Semiformula.all ψ) : ArithmeticSemiformula ℕ 0)
        = Semiformula.all (Rewriting.emb ψ) := by
    have h := Rewriting.app_all (Rew.emb : Rew ℒₒᵣ Empty 0 ℕ 0) ψ
    rw [Rew.q_emb] at h
    exact h
  simp [deepInconsistentSource, deepInconsistentAxiom, ArithSource.compile,
    compile_iffChainSource, hall]

/-- **The paper's meter on the day's axiom, discharged.**  A repeated tag run, a repeated atom
block, one quantifier and one conjunction.  Nothing in the endpoint consumes this — the
`def:ec` premise is on the *machine's* source — but it is what makes the day's axiom a thing
the paper would let a trader write, and it is what supplies the primitive recursion below.

Kind `C` (composition).  Provenance: (a) derived in-project from
`iffChainSource_polyArithmeticSourceSeq` and the `PolyArithmeticSourceSeq` closure lemmas. -/
lemma deepInconsistentSource_polyArithmeticSourceSeq :
    PolyArithmeticSourceSeq deepInconsistentSource :=
  PolyArithmeticSourceSeq.and
    (PolyArithmeticSourceSeq.all iffChainSource_polyArithmeticSourceSeq)
    (PolyArithmeticSourceSeq.leaf (PolySegStream.constList _))

/-- The written run grows by five tokens a day. -/
lemma sourceTokens_deepInconsistentSource_length (k : ℕ) :
    (ArithSource.sourceTokens (deepInconsistentSource k)).length = 5 * k + 7 := by
  have hbot : encodeArithmeticFormulaSymbols (⊥ : ArithmeticSemiformula ℕ 0) = [10] := rfl
  simp [deepInconsistentSource, ArithSource.sourceTokens,
    sourceTokens_iffChainSource_length, hbot]

/-- The day's axiom source is primitive recursive in the day: its emitted run is a
`PolySegStream` (`deepInconsistentSource_polyArithmeticSourceSeq`) and the naming map is
primitive recursive (`tokenListNat_primrec`). -/
lemma primrec_deepInconsistentSourceNat :
    Primrec fun k => (deepInconsistentSource k).sourceNat :=
  tokenListNat_primrec.comp
    (deepInconsistentSource_polyArithmeticSourceSeq.primrec)

/-- **The one fixed program the witnesses share**: on input `k` it writes the source of the
day-`k` axiom.  Its own source is a fixed finite string, so every `dayMachine` built over it is
`def:ec`-admissible. -/
noncomputable def deepSourceCode : Nat.Partrec.Code :=
  (Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp primrec_deepInconsistentSourceNat.to_comp.partrec)).choose

lemma deepSourceCode_eval (k : ℕ) :
    deepSourceCode.eval k = Part.some (deepInconsistentSource k).sourceNat := by
  rw [deepSourceCode,
    (Nat.Partrec.Code.exists_code.mp
      (Partrec.nat_iff.mp primrec_deepInconsistentSourceNat.to_comp.partrec)).choose_spec]
  rfl

/-- The evaluation reaches the output at some budget. -/
private lemma exists_evaln_of_eval_some {c : Nat.Partrec.Code} {i v : ℕ}
    (h : c.eval i = Part.some v) : ∃ b, Nat.Partrec.Code.evaln b c i = some v := by
  have hv : v ∈ c.eval i := by rw [h]; exact Part.mem_some v
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
  exact ⟨k, hk⟩

/-- Every day's axiom is refuted by pure logic: it has `⊥` as a conjunct. -/
lemma provable_neg_deepInconsistentAxiom (k : ℕ) :
    (∅ : ArithmeticTheory) ⊢ ∼deepInconsistentAxiom k := by
  rw [deepInconsistentAxiom]; cl_prover

/-! #### Witness (i): one huge axiom a day -/

/-- The day-`n` machine of the first witness: on every input it writes the source of the day's
single axiom. -/
noncomputable def deepDayMachine (n : ℕ) : Nat.Partrec.Code :=
  dayMachine (.comp deepSourceCode .left) n

lemma deepDayMachine_eval (n i : ℕ) :
    (deepDayMachine n).eval i = Part.some (deepInconsistentSource n).sourceNat := by
  rw [deepDayMachine, dayMachine_eval]
  simp [Nat.Partrec.Code.eval, deepSourceCode_eval]

/-- The day's axiom really is one of the day's theory's axioms. -/
lemma deepInconsistentAxiom_mem_theoryOf (n : ℕ) :
    deepInconsistentAxiom n ∈ theoryOf (deepDayMachine n) := by
  obtain ⟨b, hb⟩ := exists_evaln_of_eval_some (deepDayMachine_eval n 0)
  exact mem_theoryOf hb (compile_deepInconsistentSource n)

/-- …so every day's theory is genuinely inconsistent. -/
lemma not_consistent_theoryOf_deepDayMachine (n : ℕ) :
    ¬Entailment.Consistent (theoryOf (deepDayMachine n)) :=
  not_consistent_of_refutable_mem (deepInconsistentAxiom_mem_theoryOf n)
    (provable_neg_deepInconsistentAxiom n)

/-- **`thm:incons`, applied at an unboundedly day-varying family with nothing left to the
caller.**  Every hypothesis and every instance argument is discharged: the `def:ec` premise by
`digitMachineCodes_dayMachine`, the inconsistency of each day's theory by
`not_consistent_theoryOf_deepDayMachine`, and the theory instances by Foundation's own `𝗜𝚺₁`
instances.  The day-`n` theory takes a different value for every `n`, and the day-separation
lemma below fires at every pair of distinct days.
Paper node: `thm:incons` -/
theorem thm_incons_applied_deep :
    ((fun n => liaHistory (paperDP 𝗜𝚺₁) n
        ((representedInconsistentTheoryClaims 𝗜𝚺₁ deepDayMachine
          (digitMachineCodes_dayMachine _)).inconsistencySentence n)) ≈ₙ fun _ => 1) ∧
      ((fun n => liaHistory (paperDP 𝗜𝚺₁) n
        ((representedInconsistentTheoryClaims 𝗜𝚺₁ deepDayMachine
          (digitMachineCodes_dayMachine _)).consistencySentence n)) ≈ₙ fun _ => 0) :=
  lic_disbelief_inconsistent_theories_unconditional 𝗜𝚺₁ deepDayMachine
    (digitMachineCodes_dayMachine _) not_consistent_theoryOf_deepDayMachine

/-- **The day-separation theorem, applied at every pair of distinct days** — no hypothesis and
no behavioural side condition. -/
lemma inconsistencyArgClaimSentence_deep_ne {a b : ℕ} (h : a ≠ b) :
    inconsistencyArgClaimSentence deepDayMachine a
      ≠ inconsistencyArgClaimSentence deepDayMachine b :=
  inconsistencyArgClaimSentence_ne_of_arg_ne _ _ a b (dayMachine_sourceNat_ne _ h)

/-! #### Witness (ii): infinitely many axioms a day

A family `Θ′ₙ = Θ₀ ∪ {σₙ}` adjoins **one** sentence, so it can exhibit neither an
infinite axiom set nor a theory inconsistent for a reason spread across its axioms.  Here
the day-`n`
machine writes a *different* axiom on every input, so `theoryOf (mₙ)` is infinite
(`infinite_theoryOf_infiniteDayMachine`) — genuinely recursively axiomatized rather than
finitely axiomatized — while nevertheless being inconsistent, and the day machine's source is
`O(n)` symbols. -/

/-- The day-`n` machine of the second witness: on input `i` it writes the source of the
`⟨n, i⟩`-th axiom, so the day's theory has one axiom per input. -/
noncomputable def infiniteDayMachine (n : ℕ) : Nat.Partrec.Code := dayMachine deepSourceCode n

lemma infiniteDayMachine_eval (n i : ℕ) :
    (infiniteDayMachine n).eval i
      = Part.some (deepInconsistentSource (Nat.pair n i)).sourceNat := by
  rw [infiniteDayMachine, dayMachine_eval, deepSourceCode_eval]

lemma deepInconsistentAxiom_mem_theoryOf_infinite (n i : ℕ) :
    deepInconsistentAxiom (Nat.pair n i) ∈ theoryOf (infiniteDayMachine n) := by
  obtain ⟨b, hb⟩ := exists_evaln_of_eval_some (infiniteDayMachine_eval n i)
  exact mem_theoryOf hb (compile_deepInconsistentSource _)

/-- The day's axioms are pairwise distinct **as sentences**: distinct chain heights give
distinct normal forms (`iffChain_injective`), and `Nat.pair` is injective in its second
argument. -/
lemma deepInconsistentAxiom_injective : Function.Injective deepInconsistentAxiom := by
  intro a b h
  rw [deepInconsistentAxiom, deepInconsistentAxiom] at h
  exact iffChain_injective (by simpa using h)

/-- **Every day's theory is infinitely axiomatized.**  The paper's `Θ′ₙ` is only required to be
*recursively* axiomatizable, and this is the witness that the rendering really admits that:
`𝗣𝗔` and `𝗭𝗙𝗖`, the paper's own examples (tex:1859, tex:1889), are schema-generated and
infinite. -/
lemma infinite_theoryOf_infiniteDayMachine (n : ℕ) :
    (theoryOf (infiniteDayMachine n)).Infinite :=
  Set.infinite_of_injective_forall_mem
    (f := fun i : ℕ => deepInconsistentAxiom (Nat.pair n i))
    (fun i j hij => by
      have h := deepInconsistentAxiom_injective hij
      simpa using congrArg (fun z : ℕ => z.unpair.2) h)
    (fun i => deepInconsistentAxiom_mem_theoryOf_infinite n i)

/-- …and inconsistent all the same. -/
lemma not_consistent_theoryOf_infiniteDayMachine (n : ℕ) :
    ¬Entailment.Consistent (theoryOf (infiniteDayMachine n)) :=
  not_consistent_of_refutable_mem (deepInconsistentAxiom_mem_theoryOf_infinite n 0)
    (provable_neg_deepInconsistentAxiom _)

/-- **`thm:incons`, applied at a family of infinitely axiomatized day-theories, with nothing
left to the caller.**  Each `Θ′ₙ` here has infinitely many axioms
(`infinite_theoryOf_infiniteDayMachine`), each of which is astronomically large in normal form,
and the whole sequence is named by machine sources of `O(n)` symbols.
Paper node: `thm:incons` -/
theorem thm_incons_applied_infinite :
    ((fun n => liaHistory (paperDP 𝗜𝚺₁) n
        ((representedInconsistentTheoryClaims 𝗜𝚺₁ infiniteDayMachine
          (digitMachineCodes_dayMachine _)).inconsistencySentence n)) ≈ₙ fun _ => 1) ∧
      ((fun n => liaHistory (paperDP 𝗜𝚺₁) n
        ((representedInconsistentTheoryClaims 𝗜𝚺₁ infiniteDayMachine
          (digitMachineCodes_dayMachine _)).consistencySentence n)) ≈ₙ fun _ => 0) :=
  lic_disbelief_inconsistent_theories_unconditional 𝗜𝚺₁ infiniteDayMachine
    (digitMachineCodes_dayMachine _) not_consistent_theoryOf_infiniteDayMachine

end Inconsistency

end LogicalInduction
