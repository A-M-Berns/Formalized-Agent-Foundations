import LogicalInduction.Construction.Witnesses.PaperTheoryDP
import LogicalInduction.Construction.Witnesses.SubstEmission
import LogicalInduction.Construction.Witnesses.R0Representability
import LogicalInduction.Framework.RepresentsComputations
import LogicalInduction.Framework.BoundedConsistency

/-!
# Computation claims that name their machine, at the paper's representability premise

The paper's computational-knowledge theorems name the day-`n` claim by *naming the machine
it is about*: `thm:halts` and `thm:loops` assert "`⌜mₙ⌝` halts on `⌜xₙ⌝`" (tex:1931), and
`thm:dontwait`, `thm:pac`, `thm:pazfc` go through the representation `⌜f⌝(⌜n⌝)` of a total
computable function (tex:600–606).  This file states all five families that way, over the
paper's own `Θ`-complete deductive process `paperTheoryDP`.

## The design, and the error it replaces

What is represented is a **universal** object, fixed once per theorem and independent of the
machine sequence:

* the total computable `universalRunValue f : ℕ → ℕ`, which decodes a packed
  `⟨⟨source, input⟩, day⟩` argument, runs the decoded machine for `f day` interpreter steps
  and returns `1`/`0` — one `γ` per horizon program `f`.  Note precisely what `γ` represents:
  the **composite** decider `universalRunValue f`, not the horizon `f` alone.  The paper's
  `⌜f⌝(⌜n⌝)` is read here as `⌜g⌝(⟨⟨m, x⟩, n⟩) ≠ 0` for that composite `g`.  This costs no
  extra hypothesis: `RepresentsComputations` supplies a representing `γ` for *any* total
  computable function, and `universalRunValue f` is total computable exactly when `f` is
  (`universalRunValue_computable`), so `g` and `f` stand on the same premise;
* the fixed r.e. `universalHaltingSchema = codeOfREPred UniversalCodeHalts`, whose argument
  is a packed `⟨source, input⟩` pair (`ComputationSyntax.lean`).

The machine and its input then enter the *sentence*, as the argument written into that fixed
object — which is what makes the claim family actually depend on the machine sequence.

This replaces a design that did not (`R5-F08`/`R5-F09`, blind audit 2026-08-30).  Building
the family instead as `codeOfREPred (fun n => CodeHalts (mₙ) (xₙ))`, or as
`RepresentsComputations.repr` of a decider that mentions the sequence, makes the sentence
depend on that predicate's **extension** only; and each endpoint's own hypothesis pins the
extension to a constant (`∀ n, halts` gives `fun _ => True`, `hnever` gives the constant `0`,
`hconsistent` the constant `1`).  The claim family was then literally the same sentence
family for every admissible machine sequence, named no machine, and left `hm`/`hi`
decorative.  The standing test, recorded in `KNOWLEDGE.md`: substitute two sequences with the
same extension but different programs — if the sentences coincide, the rendering is
extensional and wrong.

## The test is proved here

The day-`n` sentence is a fixed object — `universalHaltingSchema`, or the `γ` representing
`universalRunValue f` — at the argument term `binNumeral (haltingClaimInput ⌜mₙ⌝ xₙ)`, so two
sequences with the same extension but different programs give literally *different argument
terms* inside the sentence.  The step from different arguments to different sentences —
`σ/[t] ≠ σ/[t']` for `t ≠ t'`, false for a `σ` that does not mention `#0` — is now available:
`Framework/SubstOccurrence.lean` supplies the missing occurrence notion
(`Semiformula.Mentions`) and the two transport lemmas (`rew_eq_of_not_mentions`,
`eq_of_rew_eq_of_mentions`) that Foundation does not expose, and
`universalHaltingSchema_mentions_zero` (`ComputationSyntax.lean`) discharges the side
condition for the fixed halting schema, from
`universalHaltingSchema_not_argument_insensitive`.

So the **full** syntactic separation is a theorem of this file:
`haltingArgClaimSentence_ne_of_source_ne` separates two claim families by their machines'
*source numbers alone*, whatever those machines do, and
`haltingArgClaimSentence_ne_of_claimInput_ne` by the whole argument.  Unlike the behavioural
lemmas, these can be invoked inside a single claim family, because no endpoint hypothesis
constrains the machine names.  On the bounded lane `representedClaimSentence_ne_of_const_ne`
and `representedClaimSentence_ne_of_arg_ne` are the same statement, with the occurrence side
condition `γ.Mentions 0` stated as a hypothesis rather than discharged, because `γ` is
supplied existentially by `RepresentsComputations` and is not a fixed object here.

The older `_ne_of_` lemmas remain and prove something weaker and different: *behavioural*
separation.  `haltingArgClaimSentence_ne_of_halts_ne` and
`representedClaimSentence_ne_of_runValue_ne` separate arguments on which the represented run
*disagrees*.  No endpoint can invoke them within one claim family, because each endpoint's own
hypothesis (`hhalts`, `hnever`, `hconsistent`) forbids that disagreement; they separate
families whose behaviour differs, not days within a family.

The load-bearing role of `hm`/`hi` is the independent one recorded in the next section: they
are the only route to the `sentence_poly` field of each represented-claims bundle, so they
pass the deletion test — remove either and the build fails.

## Naming a big argument inside `def:ec`

The argument `⟨⟨⌜mₙ⌝, xₙ⟩, n⟩` has a value exponential in the day, so it is spelled by the
**compact** Horner term `binNumeral` (`StructuredPaperRpn.lean`), `O(log v)` `ℒₒᵣ` nodes,
whose symbol run is emitted digit by digit from the very write-out certificates the paper's
hypotheses supply: `hm : DigitMachineCodes machines` and `hi : BigDigits inputs`.  Those two
hypotheses are therefore load-bearing on the `def:ec` obligation, not decorative.
Foundation's *unary* `Semiterm.Operator.numeral` would cost the argument's value in symbols;
that is a Foundation artifact, and the paper fixes no numeral notation (tex:614, tex:757).
Provability is insensitive to the choice (`provable_subst_iff_of_val`), so only the cost
changes.

## What the premise buys

* **Both literals come from one sentence** on the bounded lane.  For the total `{0,1}`-valued
  universal decider, the claim `∀ν (γ(t, ν) ⟺ ν = 0̄)` is provable exactly when the run
  *fails* and refutable exactly when it *succeeds* (`represents_proves` /
  `represents_refutes_all`).  Weak Σ₁-representation gives only the positive direction, which
  is why the superseded design carried a second, complementary r.e. schema and needed
  Σ₁-soundness to keep the two apart.
* **The deductive process is the paper's own.**  Because `γ` is supplied *existentially* by
  `RepresentsComputations` there is no computable map to `⌜γ⌝`, so no fixed schema can be
  dovetailed; `paperTheoryDP` enumerates *every* `T`-provable proposition and needs none.

The `def:ec` obligation on each family is **discharged**, not assumed: the paper's source
language writes `∀ν (γ(t,ν) ⟺ ν = 0̄)` with one `iff` node over a fixed skeleton and one
compact-numeral run for `t`, whatever `γ` is (`SubstEmission.lean`).

## Residual hypothesis

`[T.Δ₁]` is the strengthening beyond the paper, which assumes only that `Θ` is consistent,
c.e., and represents computations; it is disclosed at each endpoint.  The `[𝗜𝚺₁ ⪯ T]` that
accompanied it through tranche 6 has been **deleted** (tranche 7).  It was never used:
`paperTheoryDP`'s computability goes through Foundation's internal provability predicate
instantiated at `V := ℕ`, so the side condition discharged is `ℕ ⊧* 𝗜𝚺₁`, which holds
outright, not `𝗜𝚺₁ ⪯ T`.  Nothing on this lane assumes `T` proves any induction.
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

lemma paperPrimeDecompose_reprAllTerm (γ : ArithmeticSemisentence 2)
    (t : Semiterm.Const ℒₒᵣ) :
    paperPrimeDecompose ((reprAllTerm γ 0 t : ArithmeticSentence) : ArithmeticProposition)
      = ∼representedClaimSentence γ t := by
  have h : ((reprAllTerm γ 0 t : ArithmeticSentence) : ArithmeticProposition)
      = Semiformula.all (Rewriting.emb (reprBodyTerm γ 0 t) : ArithmeticSemiformula ℕ 1) := by
    simp [reprAllTerm]
    rfl
  rw [h, paperPrimeDecompose_all, representedClaimSentence]

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
naming.**  Definitionally the source certificate of `SubstEmission.lean`: the public atom
*is* the paper-prime of the negated body, and the paper's source language writes that body
with one `⟺` node over a fixed skeleton plus the argument term's own symbol run.

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
lemma paperTheoryDP_covers_representedClaim [T.Δ₁]
    (γ : ArithmeticSemisentence 2) (t : Semiterm.Const ℒₒᵣ)
    (h : T ⊢ ∼(reprAllTerm γ 0 t)) :
    ∃ k, representedClaimSentence γ t ∈ (paperTheoryDP T).D k := by
  have := paperTheoryDP_covers_outer_provable T _ h
  rwa [paperPrimeDecompose_neg_reprAllTerm] at this

/-- The theorem process publishes the negated claim atom when `T` proves the value-`0`
sentence. -/
lemma paperTheoryDP_covers_representedClaim_neg [T.Δ₁]
    (γ : ArithmeticSemisentence 2) (t : Semiterm.Const ℒₒᵣ)
    (h : T ⊢ reprAllTerm γ 0 t) :
    ∃ k, (∼representedClaimSentence γ t) ∈ (paperTheoryDP T).D k := by
  have := paperTheoryDP_covers_outer_provable T _ h
  rwa [paperPrimeDecompose_reprAllTerm] at this

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

/-- **Syntactic separation of represented claims at distinct arguments.**  The bounded-lane
analogue of `schemaArgClaimSentence_ne_of_const_ne`: if the representing formula `γ` really
mentions its first argument, distinct closed argument terms give distinct claim atoms, with
no hypothesis on the represented run.

The occurrence side condition is stated rather than discharged here, because `γ` is supplied
existentially by `RepresentsComputations` and is not a fixed object of this file.  It **is**
derivable from the representation specification alone whenever the represented function is
non-constant — that is `mentions_zero_of_repr_ne`
(`Framework/RepresentsComputations.lean`) — and only then: for a constant decider a `γ`
ignoring `#0` represents it correctly.  Consumers on a lane whose decider is provably
non-constant should discharge it (see `conGamma_mentions_zero` and its sufficient
conditions below); the hypothesis stays here because this lemma is stated for an arbitrary
`γ`.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`Semiformula.eq_of_rew_eq_of_mentions` (`Framework/SubstOccurrence.lean`),
`paperPrimeSentence_injective`, `Rewriting.emb_injective`. -/
lemma representedClaimSentence_ne_of_const_ne (γ : ArithmeticSemisentence 2)
    (hγ : γ.Mentions 0) (t t' : Semiterm.Const ℒₒᵣ)
    (h : (t.const : ArithmeticSemiterm Empty 1) ≠ (t'.const : ArithmeticSemiterm Empty 1)) :
    representedClaimSentence γ t ≠ representedClaimSentence γ t' := by
  intro heq
  refine h ?_
  have hpair := paperPrimeSentence_injective
    (a₁ := (true, Semiformula.exs (∼(Rewriting.emb (reprBodyTerm γ 0 t) :
      ArithmeticSemiformula ℕ 1))))
    (a₂ := (true, Semiformula.exs (∼(Rewriting.emb (reprBodyTerm γ 0 t') :
      ArithmeticSemiformula ℕ 1))))
    heq
  have hexs := congrArg Prod.snd hpair
  simp only [Semiformula.exs.injEq, Semiformula.neg_inj] at hexs
  have hbody : reprBodyTerm γ 0 t = reprBodyTerm γ 0 t' := Rewriting.emb_injective hexs
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

The superseded rendering could not even state this weaker test at a fixed `γ`: its `γ` was
`RepresentsComputations.repr` of a decider that mentioned the machine sequence, and the
endpoints' own hypotheses pinned that decider to a constant, so no two arguments could ever
take different values and the family was one sentence repeated.

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
  have hpair := paperPrimeSentence_injective
    (a₁ := (true, Semiformula.exs (∼(Rewriting.emb (reprBodyTerm γ 0 (binNumeral z)) :
      ArithmeticSemiformula ℕ 1))))
    (a₂ := (true, Semiformula.exs (∼(Rewriting.emb (reprBodyTerm γ 0 (binNumeral z')) :
      ArithmeticSemiformula ℕ 1))))
    heq
  have hexs := congrArg Prod.snd hpair
  simp only [Semiformula.exs.injEq] at hexs
  have hemb : (Rewriting.emb (reprBodyTerm γ 0 (binNumeral z)) :
      ArithmeticSemiformula ℕ 1)
      = Rewriting.emb (reprBodyTerm γ 0 (binNumeral z')) := by
    simpa using congrArg (fun φ => ∼φ) hexs
  have hbody := Rewriting.emb_injective hemb
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
`RepresentsComputations`; the deductive process is `paperTheoryDP`, which is soundness-free.
This is the `thm:dontwait` claim family; the paper node itself is carried by the endpoint
that consumes it, not by this constructor. -/
noncomputable def representedBoundedClaims [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    {machines : ℕ → Nat.Partrec.Code} {inputs steps : ℕ → ℕ}
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (γ : ArithmeticSemisentence 2)
    (hγ : ∀ z y : ℕ, y = universalRunValue steps z ↔ T ⊢ reprAll γ y z) :
    RepresentedDecidableClaims (paperTheoryDP T)
      (fun n => CodeHaltsWithin (machines n) (inputs n) (steps n)) where
  sentence n := representedClaimSentence γ (binNumeral (boundedArg machines inputs n))
  sentence_poly :=
    representedClaimSentence_bigSentenceCodes γ _
      (polySegStream_binNumeral_const (boundedArg_digits hm hi))
  provable_of_true n hn := by
    refine paperTheoryDP_covers_representedClaim T γ _ ?_
    refine (provable_neg_reprAllTerm_binNumeral_iff T γ _).mpr ?_
    refine represents_refutes_all T γ _ ?_
    refine (hγ _ 1).mp ?_
    rw [universalRunValue_boundedArg]
    exact ((boundedRunValue_eq_one_iff machines inputs steps n).mpr hn).symm
  disprovable_of_false n hn := by
    refine paperTheoryDP_covers_representedClaim_neg T γ _ ?_
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
sentence.  Neither consumes a semantic hypothesis on `T`: the process is `paperTheoryDP`,
whose non-vacuity is `paperTheoryDP_nonvacuous`, from consistency alone.
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
    RepresentedDecidableClaims (paperTheoryDP T)
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
`conRunValue T' f` (`Framework/BoundedConsistency.lean`): it takes a packed
`⟨sentence code, day⟩`, evaluates `f` at the day *inside*, and decides whether the coded
sentence has a `T'`-derivation with Gödel number below `f(day)`.  Its extension varies with
`T'`'s theorems, so the `γ` `RepresentsComputations T` returns for it genuinely names the
metered theory; one `γ` serves every day at that horizon.  `⊥` then enters the *sentence*,
as the first component of the compact argument `binNumeral ⟨⌜⊥⌝, n⟩`.

Representing the *consistency* predicate directly would have been the trap: for a
consistent `T'`, `fun n => conWithin T' (f n)` is extensionally `True` and its indicator is
the constant `0`, so a representing `γ` would name nothing at all (`R5-F08`,
`KNOWLEDGE.md`).

Two disclosures at this boundary.  The finite search is metered by the derivation's Gödel
number rather than the paper's symbol count (`dd:proofcode`, glossary in
`LogicalInduction.lean`).  And the propositional rendering of `Con` is a *negated* atom:
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
family may then collapse to one sentence.  Earlier prose here (and at
`representedClaimSentence_ne_of_const_ne`) claimed the side condition could *never* be
discharged from the spec; that was wrong — the counterexample bounds the claim to constant
deciders only.

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
sentence code has a `T'`-derivation with Gödel number below `horizons n`, the decider is `1`
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
*some* derivation code; an unbounded horizon eventually exceeds it, and the previous lemma
applies.  This is the form a caller can actually discharge: it asks nothing of `T'` beyond
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
  obtain ⟨n, hn⟩ := hub d
  exact conGamma_mentions_zero_of_bProv T T' hh hcons
    (φcode := ⌜(⊤ : ArithmeticSentence)⌝) (n := n) ⟨d, hn, hd⟩

/-- **The §4.10 claim family.**  Day `n` claims that `T'` proves no contradiction with a
derivation code below `horizons n`; the claim is *true* on every day, by consistency of
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
paper, which asks only that `Θ′` be "a stronger consistent recursively axiomatizable theory"
(tex:1881-1886) and states no containment hypothesis; and it matches the argument, which
needs only that `T` represent a computable function, that function's totality and
computability being facts about `T'`'s derivation codes rather than about `T`.

Kind `C` (composition).  Provenance: (a) derived in-project from `RepresentsComputations`
and `conWithin_of_consistent`; (c) modelling substitution `dd:proofcode` on the measure of
the finite search. -/
noncomputable def representedConClaims (T' : ArithmeticTheory) [T.Δ₁] [T'.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [RepresentsComputations T] (hcons : Entailment.Consistent T') {horizons : ℕ → ℕ}
    (hh : ComputableHorizon horizons) :
    RepresentedDecidableClaims (paperTheoryDP T) (fun n => conWithin T' (horizons n)) where
  sentence n := conClaimSentence (conGamma T T' hh) n
  sentence_poly := conClaimSentence_bigSentenceCodes _
  provable_of_true n _ := by
    refine paperTheoryDP_covers_representedClaim_neg T _ _ ?_
    refine (provable_reprAllTerm_binNumeral_iff T _ _).mpr ?_
    refine (conGamma_spec T T' hh _ 0).mp ?_
    exact (conRunValue_bot_eq_zero T' hcons n).symm
  disprovable_of_false n hn := absurd (conWithin_of_consistent T' hcons (horizons n)) hn

/-! ## The paper-facing endpoints, over the paper's own deductive process

`paperTheoryDP T` enumerates every `T`-provable proposition, is computable
(`paperTheoryDP_computable`), and has a world consistent with every stage from
**consistency of `T` alone** (`paperTheoryDP_nonvacuous`).  Together with the two literals
of `RepresentsComputations` this leaves the three bounded-claim endpoints below with no
semantic hypothesis on `T`, no presentation argument, and no `hworld` argument. -/

/-- Market non-vacuity for the paper's theorem process, from **consistency of `T` alone**.
Shared by the bounded endpoints below — which get consistency from the representability
premise (`RepresentsComputations.consistent`) — and by the halting endpoints, which assume
it directly. -/
private lemma paperTheoryDP_hworld_stages [T.Δ₁] (hcon : Entailment.Consistent T) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperTheoryDP T).D n) := by
  haveI := hcon
  obtain ⟨v, hv⟩ := paperTheoryDP_nonvacuous T
  exact fun n => ⟨v, hv n⟩

/-- The constructed inductor over the paper's theorem process. -/
private noncomputable abbrev paperLIA [T.Δ₁] :
    IsLogicalInductor (liaHistory (paperTheoryDP T)) (paperTheoryDP T) :=
  LIA_is_logical_inductor (paperTheoryDP T) (paperTheoryDP_computable T)

section Endpoints

variable [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [RepresentsComputations T]

/-- The horizon sequence is arbitrary computable — `hh` names its program rather than
bounding its growth — which is the paper's "let `f` be any computable function".
*Residual hypothesis (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the strengthenings beyond the paper (see the global
disclosure in `LogicalInduction/README.md`),
which assumes only that `Θ` is consistent, c.e. and represents computations: it asks for a
Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e. theory has a
deductively equivalent Δ₁ axiomatization, so the theorems transfer; that reduction is not
formalized here.  The `[𝗜𝚺₁ ⪯ T]` this endpoint used to carry is **gone** (tranche 7): the
r.e.-ness of provability in `T` runs through Foundation's internal provability predicate at
`V := ℕ`, whose side condition is `ℕ ⊧* 𝗜𝚺₁` — true outright — and never `𝗜𝚺₁ ⪯ T`.
Paper node: `thm:dontwait` -/
theorem lic_does_not_anticipate_halting_ofComputation
    (P : History) [IsLogicalInductor P (paperTheoryDP T)]
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hh : ComputableHorizon horizons)
    (hnever : ∀ n, ¬CodeHalts (machines n) (inputs n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperTheoryDP T).D n)) :
    (fun n => P n
      ((representedBoundedHaltingClaims T machines inputs horizons hm hi hh).sentence n))
        ≈ₙ fun _ => 0 :=
  lic_does_not_anticipate_halting P (paperTheoryDP T) machines inputs horizons
    (representedBoundedHaltingClaims T machines inputs horizons hm hi hh) hnever hworld

/-! ### Unconditional over the constructed `LIA`

Nothing remains but the caller's own computation and the (true) hypothesis about it: no
market, no inductor, no presentation, no `hworld`, and no semantic assumption on `T`. -/

/-- **Belief in Finitistic Consistency** (`thm:pac`), unconditional over `LIA`, at the
paper's own subject matter.

The day-`n` claim is this development's rendering of the paper's `Con(Θ)(⌜f⌝(⌜n⌝))`: the
value-`0` sentence of the formula `γ` representing the universal bounded-provability decider
`conRunValue T f`, at the compact name of the argument `⟨⌜⊥⌝, n⟩`.  Read out, it says that no
`T`-derivation of `⊥` has Gödel number below `f(n)`.

*It is a paraphrase, in two disclosed respects, and is not asserted to BE the paper's
sentence.*  What `γ` represents is the **composite** decider `conRunValue T f` — the paper's
`⌜f⌝(⌜n⌝)` read as `⌜g⌝(⟨⌜⊥⌝, n⟩) = 0̄` for that composite `g` — rather than `f` alone; this
is the module header's standing disclosure and costs no extra hypothesis, since
`RepresentsComputations` represents any total computable function.  And the finite search is
metered by the derivation's Gödel number rather than by the paper's symbol count
(`dd:proofcode`).

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

*Residual hypotheses (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the strengthenings beyond the paper (see the global
disclosure in `LogicalInduction/README.md`),
which assumes only that `Θ` is consistent, c.e. and represents computations: it asks for a
Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e. theory has a
deductively equivalent Δ₁ axiomatization, so the theorems transfer; that reduction is not
formalized here.  The finite proof search is metered by the derivation's Gödel number
rather than by the paper's symbol count (`dd:proofcode`).
Paper node: `thm:pac` -/
theorem lic_belief_finitistic_consistency_unconditional
    (horizons : ℕ → ℕ) (hh : ComputableHorizon horizons) :
    (fun n => liaHistory (paperTheoryDP T) n
      (conClaimSentence (conGamma T T hh) n)) ≈ₙ fun _ => 1 :=
  haveI := paperLIA T
  lic_belief_finitistic_consistency (liaHistory (paperTheoryDP T)) (paperTheoryDP T)
    (fun n => conWithin T (horizons n))
    (representedConClaims T T (RepresentsComputations.consistent T)
      hh).toRepresentedSemidecidableClaims
    (fun n => conWithin_of_consistent T (RepresentsComputations.consistent T) (horizons n))
    (paperTheoryDP_hworld_stages T (RepresentsComputations.consistent T))

/-- **Belief in the Consistency of a Stronger Theory** (`thm:pazfc`), unconditional over
`LIA`, at the paper's own subject matter.

The market is `Θ`'s: `paperTheoryDP T` enumerates the propositions `T` proves, and the
inductor is trained on that process alone.  The *claims*, however, are about a second
theory `T'` — the paper's `Θ′`, "a stronger consistent recursively axiomatizable theory,
such as `𝗣𝗔 + Con(𝗣𝗔)` or `ZFC`" (tex:1881-1886).  Day `n` renders the arithmetized
`Con(Θ′)(⌜f⌝(⌜n⌝))`: no `T'`-derivation of `⊥` has Gödel number below `f(n)`, written as
the value-`0` sentence of the `T`-formula representing `T'`'s bounded-provability decider.
So the inductor, which can prove nothing about `T'` from its own theory, nevertheless comes
to believe every finite consistency statement about it.

*A paraphrase, in the same two disclosed respects as `thm:pac`*: `γ` represents the
**composite** decider `conRunValue T' f`, not `f` alone (the module header's standing
disclosure), and the search is metered by the derivation's Gödel number rather than by the
paper's symbol count (`dd:proofcode`).  The horizon ranges over *all* computable functions,
not only fast-growing ones: `Ack` is the witness below, and a degenerate horizon (constantly
`0`) makes the represented decider constant, so the day family may then collapse to a single
sentence.  Day separation in the non-degenerate case is `conClaimSentence_ne_of_day_ne` with
`conGamma_mentions_zero_of_horizon_unbounded`.

`hcons` is the paper's own premise on `Θ′` and is what makes each day's claim *true*; the
representability of `T` then carries truth to `T`-provability, and no soundness assumption
appears anywhere.

*The hypotheses are the paper's.*  tex:1881-1886 assumes of `Θ′` only that it is a stronger
consistent recursively axiomatizable theory — there is **no** `Θ ⊆ Θ′` hypothesis in the
paper — and no hypothesis relating `T` and `T'` is stated here either, because none is used:
the argument needs only that `T` represents computable functions and that `T'` is consistent.
What makes the theorem *interesting* is the informal case where `Θ` cannot prove `Con(Θ′)`,
and the `𝗜𝚺₁`/`𝗣𝗔` witness below carries that concretely.

*Residual hypotheses (disclosed).*  `[T.Δ₁]`, `[T'.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the strengthenings beyond the paper (see the global
disclosure in `LogicalInduction/README.md`),
which assumes only that `Θ` is consistent, c.e. and represents computations, and that `Θ′`
is consistent and recursively axiomatizable: it asks for a
Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e. theory has a
deductively equivalent Δ₁ axiomatization, so the theorems transfer; that reduction is not
formalized here.  The finite proof search is metered by the derivation's Gödel number
rather than by the paper's symbol count (`dd:proofcode`).
Paper node: `thm:pazfc` -/
theorem lic_belief_stronger_theory_consistency_unconditional
    (T' : ArithmeticTheory) [T'.Δ₁] (hcons : Entailment.Consistent T')
    (horizons : ℕ → ℕ) (hh : ComputableHorizon horizons) :
    (fun n => liaHistory (paperTheoryDP T) n
      (conClaimSentence (conGamma T T' hh) n)) ≈ₙ fun _ => 1 :=
  haveI := paperLIA T
  lic_belief_finitistic_consistency (liaHistory (paperTheoryDP T)) (paperTheoryDP T)
    (fun n => conWithin T' (horizons n))
    (representedConClaims T T' hcons hh).toRepresentedSemidecidableClaims
    (fun n => conWithin_of_consistent T' hcons (horizons n))
    (paperTheoryDP_hworld_stages T (RepresentsComputations.consistent T))

/-- `thm:dontwait`, unconditional over `LIA`.  `hh` supplies the horizon program for an
arbitrary computable `f` — no growth bound — which is the paper's own quantifier, and `hm`
and `hi` are the write-out metered machine/input classes, which is the paper's e.c. sequence
of bitstrings `⟨y⟩` (tex:1946-1952).  The three are independent hypotheses of one signature.
*Residual hypothesis (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the strengthenings beyond the paper (see the global
disclosure in `LogicalInduction/README.md`),
which assumes only that `Θ` is consistent, c.e. and represents computations: it asks for a
Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e. theory has a
deductively equivalent Δ₁ axiomatization, so the theorems transfer; that reduction is not
formalized here.  The `[𝗜𝚺₁ ⪯ T]` this endpoint used to carry is **gone** (tranche 7): the
r.e.-ness of provability in `T` runs through Foundation's internal provability predicate at
`V := ℕ`, whose side condition is `ℕ ⊧* 𝗜𝚺₁` — true outright — and never `𝗜𝚺₁ ⪯ T`.
Paper node: `thm:dontwait` -/
theorem lic_does_not_anticipate_halting_unconditional
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hh : ComputableHorizon horizons)
    (hnever : ∀ n, ¬CodeHalts (machines n) (inputs n)) :
    (fun n => liaHistory (paperTheoryDP T) n
      ((representedBoundedHaltingClaims T machines inputs horizons hm hi hh).sentence n))
        ≈ₙ fun _ => 0 :=
  haveI := paperLIA T
  lic_does_not_anticipate_halting_ofComputation T (liaHistory (paperTheoryDP T))
    machines inputs horizons hm hi hh hnever (paperTheoryDP_hworld_stages T (RepresentsComputations.consistent T))

/-- **`thm:dontwait`, applied.**  A machine that provably halts on nothing
(`neverHaltMachine`), the paper's `⟨y⟩` bitstring inputs `2 ^ n`, and the identity horizon
supplied through `ComputableHorizon.of`.  The non-halting hypothesis is proved, not assumed;
nothing is left to the caller. -/
example :
    (fun n => liaHistory (paperTheoryDP T) n
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
(`Construction/Witnesses/R0Representability.lean`).  Nothing is assumed: this is a
belief-in-consistency statement about a named theory, with the consistency claim itself
arithmetized.

This is the first endpoint of the development whose subject matter is a `Con(Θ)` family
rather than a caller-supplied bounded computation. -/
example :
    (fun n => liaHistory (paperTheoryDP 𝗜𝚺₁) n
      (conClaimSentence (conGamma 𝗜𝚺₁ 𝗜𝚺₁ ComputableHorizon.ackermann) n)) ≈ₙ fun _ => 1 :=
  lic_belief_finitistic_consistency_unconditional 𝗜𝚺₁ _ ComputableHorizon.ackermann

/-- **`thm:pazfc`, applied — the paper's own illustration.**  The inductor is trained on
`𝗜𝚺₁`, and the claims are the finite consistency statements of `𝗣𝗔`, a strictly stronger
theory: `𝗜𝚺₁ ⊬ Con(𝗣𝗔)`, yet the `𝗜𝚺₁`-trained inductor's belief in `Con(𝗣𝗔)(⌜Ack(n,n)⌝)`
converges to `1`.

Both theories are named, and nothing is left to the caller: `𝗜𝚺₁`'s three instances are
discharged in the repository (`Construction/Witnesses/R0Representability.lean`), `𝗣𝗔.Δ₁` is
Foundation's, and `Entailment.Consistent 𝗣𝗔` is Foundation's instance too, obtained from
soundness at the standard model (`Schemata.lean`).  That semantic route lives *inside this
witness only* — the endpoint above takes consistency as a hypothesis, exactly as the paper
does, and no soundness assumption reaches the trust surface. -/
example :
    (fun n => liaHistory (paperTheoryDP 𝗜𝚺₁) n
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
are stated below over `paperTheoryDP`, the paper's own `Θ`-complete process, and therefore
carry **no semantic hypothesis on `T`**: the positive literal is Σ₁-completeness
(`re_complete_mp`, which needs `[𝗥₀ ⪯ T]` and nothing else), the negative literal is the
paper's own object-level refutation premise, and market non-vacuity is
`paperTheoryDP_nonvacuous`, from consistency alone.  That retires the
`[T.SoundOnHierarchy 𝚺 1]` instance the superseded fixed-schema pair carried, which was
load-bearing only through the *other* process's fiber-exclusivity step.

Two representation points, both shared with `thm:dontwait` above.

* **The schema is universal; the data is in the argument.**  The claim family is the
  instance family of the ONE fixed Σ₁ schema `universalHaltingSchema` — Foundation's r.e.
  formula for `UniversalCodeHalts z := (Code.ofSource z.unpair.1).eval z.unpair.2 |>.Dom`
  (`ComputationSyntax.lean`) — at the argument `⟨⌜mₙ⌝, xₙ⟩` (`haltingClaimInput`), spelled by
  the compact `binNumeral`.  So the day-`n` sentence names the day-`n` machine and its input,
  as the paper's `⌜mₙ⌝`/`⌜xₙ⌝` do (tex:1931).

  The superseded design instead put the sequences *inside* the schema, as
  `codeOfREPred (fun n => CodeHalts (machines n) (inputs n))`.  That is extensional: under
  `thm:halts`'s own `hhalts` the predicate is `fun _ => True` and under `thm:loops`'s premise
  it is refuted uniformly, so the schema — and hence the whole sentence family — was the same
  for every admissible machine sequence and named nothing.  The unary-numeral cost objection
  that motivated it does not apply to a compact name: `binNumeral (haltingClaimInput mₙ xₙ)`
  costs `O(log)` of the pair's value, i.e. `O(|source of mₙ| + |digits of xₙ|)` symbols, and
  that is exactly the quantity `hm : DigitMachineCodes machines` and `hi : BigDigits inputs`
  bound polynomially.  `hm` and `hi` are therefore consumed by the `def:ec` obligation, on
  which they are load-bearing, rather than by a free r.e.-ness step.

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
naming.**  Definitionally the source certificate of `SubstEmission.lean`: a fixed skeleton
plus the argument term's own symbol run, which is where the write-out hypotheses are spent.

Kind `C` (composition).  Provenance: (a) derived in-project from
`bigSentenceCodes_schemaArgClaim`. -/
lemma schemaArgClaimSentence_bigSentenceCodes (σ : ArithmeticSemisentence 1)
    (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ l : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))) :
    BigSentenceCodes (fun n => schemaArgClaimSentence σ (τ n)) :=
  bigSentenceCodes_schemaArgClaim σ τ henc

lemma paperPrimeDecompose_schemaArgClaim (σ : ArithmeticSemisentence 1)
    (t : Semiterm.Const ℒₒᵣ) :
    paperPrimeDecompose ((schemaArgClaim σ t : ArithmeticSentence) : ArithmeticProposition)
      = schemaArgClaimSentence σ t := by
  have h : ((schemaArgClaim σ t : ArithmeticSentence) : ArithmeticProposition)
      = Semiformula.exs (Rewriting.emb (schemaArgBody σ t) : ArithmeticSemiformula ℕ 1) := by
    simp [schemaArgClaim]
    rfl
  rw [h, paperPrimeDecompose_exs, schemaArgClaimSentence]

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
`Theory.Proof.complete_iff` (`Completeness/CounterModel.lean:253`). -/
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
lemma paperTheoryDP_covers_schemaArgClaim [T.Δ₁] (σ : ArithmeticSemisentence 1)
    (t : Semiterm.Const ℒₒᵣ) (h : T ⊢ (σ/[t.const] : ArithmeticSentence)) :
    ∃ k, schemaArgClaimSentence σ t ∈ (paperTheoryDP T).D k := by
  have := paperTheoryDP_covers_outer_provable T _ ((provable_schemaArgClaim_iff T σ t).mpr h)
  rwa [paperPrimeDecompose_schemaArgClaim] at this

/-- The theorem process publishes the negated claim atom when `T` refutes the argument
instance. -/
lemma paperTheoryDP_covers_schemaArgClaim_neg [T.Δ₁]
    (σ : ArithmeticSemisentence 1) (t : Semiterm.Const ℒₒᵣ)
    (h : T ⊢ ∼(σ/[t.const] : ArithmeticSentence)) :
    ∃ k, (∼schemaArgClaimSentence σ t) ∈ (paperTheoryDP T).D k := by
  have := paperTheoryDP_covers_outer_provable T _
    ((provable_neg_schemaArgClaim_iff T σ t).mpr h)
  rwa [paperPrimeDecompose_neg_schemaArgClaim] at this

/-! ### The halting claim: the universal schema at a machine-naming argument -/

/-- The `thm:halts`/`thm:loops` claim sentence for the day-`n` machine and input: the fixed
universal halting schema at the compact name of `⟨⌜mₙ⌝, xₙ⟩`.

This is the declaration the whole R5-F08 repair turns on.  It depends on `machines` and
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

The superseded rendering failed the extensionality test outright: its sentence family was
built from `codeOfREPred (fun n => CodeHalts (machines n) (inputs n))`, which sees only the
predicate's extension, so under each endpoint's own hypothesis it was literally the *same*
family for every admissible machine sequence.

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
  have hpair := paperPrimeSentence_injective
    (a₁ := (true, Semiformula.exs (Rewriting.emb (schemaArgBody universalHaltingSchema
      (binNumeral (haltingClaimInput (machines n) (inputs n)))) :
        ArithmeticSemiformula ℕ 1)))
    (a₂ := (true, Semiformula.exs (Rewriting.emb (schemaArgBody universalHaltingSchema
      (binNumeral (haltingClaimInput (machines' n') (inputs' n')))) :
        ArithmeticSemiformula ℕ 1)))
    heq
  have hexs := congrArg Prod.snd hpair
  simp only [Semiformula.exs.injEq] at hexs
  have hbody := Rewriting.emb_injective hexs
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
`Semiformula.eq_of_rew_eq_of_mentions` (`Framework/SubstOccurrence.lean`),
`paperPrimeSentence_injective`, `Rewriting.emb_injective`. -/
lemma schemaArgClaimSentence_ne_of_const_ne (σ : ArithmeticSemisentence 1)
    (hσ : σ.Mentions 0) (t t' : Semiterm.Const ℒₒᵣ)
    (h : (t.const : ArithmeticSemiterm Empty 1) ≠ (t'.const : ArithmeticSemiterm Empty 1)) :
    schemaArgClaimSentence σ t ≠ schemaArgClaimSentence σ t' := by
  intro heq
  refine h ?_
  have hpair := paperPrimeSentence_injective
    (a₁ := (true, Semiformula.exs (Rewriting.emb (schemaArgBody σ t) :
      ArithmeticSemiformula ℕ 1)))
    (a₂ := (true, Semiformula.exs (Rewriting.emb (schemaArgBody σ t') :
      ArithmeticSemiformula ℕ 1)))
    heq
  have hexs := congrArg Prod.snd hpair
  simp only [Semiformula.exs.injEq] at hexs
  have hbody : schemaArgBody σ t = schemaArgBody σ t' := Rewriting.emb_injective hexs
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
    RepresentedSemidecidableClaims (paperTheoryDP T)
      (fun n => CodeHalts (machines n) (inputs n)) where
  sentence := haltingArgClaimSentence machines inputs
  sentence_poly :=
    schemaArgClaimSentence_bigSentenceCodes universalHaltingSchema _
      (polySegStream_binNumeral_const (haltingClaimInput_digits hm hi))
  provable_of_true n hn := by
    refine paperTheoryDP_covers_schemaArgClaim T universalHaltingSchema _ ?_
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
is a sequence of bitstrings.  Strictly wider than the whole-value pair this once took — see
`digitMachineCodes_nest_not_polyMachineCodes` and `bigDigits_two_pow_not_polyNatCodes`.
*Residual hypothesis (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the strengthenings beyond the paper (see the global
disclosure in `LogicalInduction/README.md`),
which assumes only that `Θ` is consistent, c.e. and represents computations: it asks for a
Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e. theory has a
deductively equivalent Δ₁ axiomatization, so the theorems transfer; that reduction is not
formalized here.  The `[𝗜𝚺₁ ⪯ T]` this endpoint used to carry is **gone** (tranche 7): the
r.e.-ness of provability in `T` runs through Foundation's internal provability predicate at
`V := ℕ`, whose side condition is `ℕ ⊧* 𝗜𝚺₁` — true outright — and never `𝗜𝚺₁ ⪯ T`.
Paper node: `thm:halts` -/
theorem lic_learns_halting_patterns_ofComputation
    (P : History) [IsLogicalInductor P (paperTheoryDP T)]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hhalts : ∀ n, CodeHalts (machines n) (inputs n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperTheoryDP T).D n)) :
    (fun n => P n ((representedHaltingClaims T machines inputs hm hi).sentence n)) ≈ₙ
      fun _ => 1 :=
  lic_learns_halting_patterns P (paperTheoryDP T) machines inputs
    (representedHaltingClaims T machines inputs hm hi) hhalts hworld

/-- **Learning of Provable Non-Halting Patterns** over the paper's theorem process.  `hloops`
is the paper's premise, literal object-level `T`-refutability of the day instance — not a
deductive-process emission surrogate, and not stated at the vacuous wrapper.
*Residual hypothesis (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the strengthenings beyond the paper (see the global
disclosure in `LogicalInduction/README.md`),
which assumes only that `Θ` is consistent, c.e. and represents computations: it asks for a
Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e. theory has a
deductively equivalent Δ₁ axiomatization, so the theorems transfer; that reduction is not
formalized here.  The `[𝗜𝚺₁ ⪯ T]` this endpoint used to carry is **gone** (tranche 7): the
r.e.-ness of provability in `T` runs through Foundation's internal provability predicate at
`V := ℕ`, whose side condition is `ℕ ⊧* 𝗜𝚺₁` — true outright — and never `𝗜𝚺₁ ⪯ T`.
Paper node: `thm:loops` -/
theorem lic_learns_provable_nonhalting_patterns_ofComputation
    (P : History) [IsLogicalInductor P (paperTheoryDP T)]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hloops : ∀ n : ℕ, T ⊢ ∼(haltingArgClaimInstance machines inputs n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperTheoryDP T).D n)) :
    (fun n => P n ((representedHaltingClaims T machines inputs hm hi).sentence n)) ≈ₙ
      fun _ => 0 :=
  lic_learns_provable_nonhalting_patterns P (paperTheoryDP T) machines inputs
    (representedHaltingClaims T machines inputs hm hi)
    (fun n => paperTheoryDP_covers_schemaArgClaim_neg T universalHaltingSchema _
      (hloops n)) hworld

variable [Entailment.Consistent T]

/-- `thm:halts`, unconditional over `LIA`.  The deductive process is the paper's own, is
proved computable (`paperTheoryDP_computable`), and its market non-vacuity follows from
consistency of `T` alone, so nothing remains beyond the theory instances and the (true)
hypothesis that the machines halt.  In particular there is no soundness instance.
*Residual hypothesis (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the strengthenings beyond the paper (see the global
disclosure in `LogicalInduction/README.md`),
which assumes only that `Θ` is consistent, c.e. and represents computations: it asks for a
Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e. theory has a
deductively equivalent Δ₁ axiomatization, so the theorems transfer; that reduction is not
formalized here.  The `[𝗜𝚺₁ ⪯ T]` this endpoint used to carry is **gone** (tranche 7): the
r.e.-ness of provability in `T` runs through Foundation's internal provability predicate at
`V := ℕ`, whose side condition is `ℕ ⊧* 𝗜𝚺₁` — true outright — and never `𝗜𝚺₁ ⪯ T`.
Paper node: `thm:halts` -/
theorem lia_learns_halting_patterns_unconditional
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hhalts : ∀ n, CodeHalts (machines n) (inputs n)) :
    (fun n => liaHistory (paperTheoryDP T) n
      ((representedHaltingClaims T machines inputs hm hi).sentence n)) ≈ₙ fun _ => 1 :=
  haveI := paperLIA T
  lic_learns_halting_patterns_ofComputation T (liaHistory (paperTheoryDP T))
    machines inputs hm hi hhalts (paperTheoryDP_hworld_stages T inferInstance)

/-- `thm:loops`, unconditional over `LIA`.  `hm` and `hi` are the write-out metered classes
shared with `thm:halts`; `hloops` is the object-level refutation premise, which cannot be
discharged for an arbitrary `T` — see `loopsTheory` below for its witness.
*Residual hypothesis (disclosed).*  `[T.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the strengthenings beyond the paper (see the global
disclosure in `LogicalInduction/README.md`),
which assumes only that `Θ` is consistent, c.e. and represents computations: it asks for a
Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e. theory has a
deductively equivalent Δ₁ axiomatization, so the theorems transfer; that reduction is not
formalized here.  The `[𝗜𝚺₁ ⪯ T]` this endpoint used to carry is **gone** (tranche 7): the
r.e.-ness of provability in `T` runs through Foundation's internal provability predicate at
`V := ℕ`, whose side condition is `ℕ ⊧* 𝗜𝚺₁` — true outright — and never `𝗜𝚺₁ ⪯ T`.
Paper node: `thm:loops` -/
theorem lic_learns_provable_nonhalting_patterns_unconditional
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hloops : ∀ n : ℕ, T ⊢ ∼(haltingArgClaimInstance machines inputs n)) :
    (fun n => liaHistory (paperTheoryDP T) n
      ((representedHaltingClaims T machines inputs hm hi).sentence n)) ≈ₙ fun _ => 0 :=
  haveI := paperLIA T
  lic_learns_provable_nonhalting_patterns_ofComputation T (liaHistory (paperTheoryDP T))
    machines inputs hm hi hloops (paperTheoryDP_hworld_stages T inferInstance)

/-- **`thm:halts`, applied.**  The machine family is `Nat.Partrec.Code.nest`, whose source
grows linearly in the day and whose source *number* is exponential (so the whole-value class
excludes it, `digitMachineCodes_nest_not_polyMachineCodes`), and whose halting hypothesis is
*proved* rather than assumed (`codeHalts_nest`).  The inputs are the paper's own `⟨x⟩` shape,
the `n`-bit string `2 ^ n`.  Nothing is left for the caller. -/
example :
    (fun n => liaHistory (paperTheoryDP T) n
      ((representedHaltingClaims T Nat.Partrec.Code.nest (fun n => 2 ^ n)
          Nat.Partrec.Code.bigDigits_sourceNat_nest bigDigits_two_pow).sentence n))
        ≈ₙ fun _ => 1 :=
  lia_learns_halting_patterns_unconditional T
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
    (fun n => liaHistory (paperTheoryDP T) n
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

noncomputable instance loopsTheory_delta1 : loopsTheory.Δ₁ :=
  inferInstanceAs (LO.FirstOrder.Theory.Δ₁ (insert loopsWitnessSentence 𝗜𝚺₁))

instance loopsTheory_isigma1 : (𝗜𝚺₁ : ArithmeticTheory) ⪯ loopsTheory :=
  Entailment.WeakerThan.ofSubset (Set.subset_insert _ _)

instance loopsTheory_r0 : (𝗥₀ : ArithmeticTheory) ⪯ loopsTheory :=
  Entailment.WeakerThan.trans (𝓢 := (𝗥₀ : ArithmeticTheory)) (𝓣 := (𝗜𝚺₁ : ArithmeticTheory))
    inferInstance loopsTheory_isigma1

/-- The witness theory is **consistent**, so the premise set is not inhabited by a theory
that proves everything. -/
lemma loopsTheory_consistent : Entailment.Consistent loopsTheory := inferInstance

/-- The witness theory is Σ₁-sound — from truth in `ℕ`, not by assumption.  The halting
endpoints no longer consume soundness; this records the quality of the witness. -/
lemma loopsTheory_soundOnSigma1 : loopsTheory.SoundOnHierarchy 𝚺 1 := inferInstance

/-- `loopsTheory` provably does not halt on the constant family — the endpoint's
`≈ₙ fun _ => 0` conclusion is therefore the semantically correct one. -/
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
    (fun n => liaHistory (paperTheoryDP loopsTheory) n
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
appears and `dd:proofcode` is not in play — the existential is over all proofs either way.

**Which theories.**  *Disclosed paraphrase.*  The theory sequence is the **deduction family**
`Θ′ₙ := Θ₀ ∪ {σₙ}` over a fixed `Δ₁` base theory `Θ₀`, not an arbitrary e.c. sequence of
theories.  Foundation's derivability predicate takes its theory as a *meta* parameter
(`Derivation T` is `(construction T).Fixpoint`), so there is no uniform-in-theory-code
derivability to represent and no way for a sequence of theories to enter one sentence as an
argument.  For a deduction family the deduction theorem collapses the day's theory to a single
sentence code: `Θ′ₙ` is inconsistent exactly when `Θ₀ ⊢ ∼σₙ`, i.e. exactly when `⌜∼σₙ⌝` is
`Θ₀`-provable (`provableCode_neg_iff_not_consistent_adjoin`).  So the day-`n` claim is the
universal provability schema of `Θ₀` at the compact name of `⌜∼σₙ⌝`, and it genuinely names
the day's theory — the extensionality test is a theorem
(`inconsistencyArgClaimSentence_ne_of_arg_ne`), not a hope.  The general e.c.-sequence-of-
theories rendering is deferred; the restriction is recorded at the endpoint and in the
README, never silently.

**The `def:ec` premise.**  What the day-`n` sentence writes out is the code of `∼σₙ` — the
name of `Θ′ₙ` under the deduction-theorem reduction — so that is the sequence the write-out
class is stated on (`hσ : BigDigits (deductionFamilyArg σ)`).  It is the exact analogue of
`hm`/`hi` on the halting lane, and it is load-bearing: it is the only route to
`inconsistency_poly`.

**One family, not two.**  `consistencySentence` is the syntactic negation of
`inconsistencySentence`, as the paper defines it; the second conjunct costs no second
representation premise. -/

section Inconsistency

/-- **The universal provability schema of a base theory.**  Foundation's r.e. formula for
"the sentence with code `z` is `T'`-provable".  At `z = ⌜∼σ⌝` its standard-model content is
exactly "`T' ∪ {σ}` is inconsistent", so one schema per base theory serves every day and every
adjoined axiom, and the day's theory enters only through the *argument*.

Representing "`T'` is inconsistent" directly would have been the extensionality trap (`R5-F08`,
`KNOWLEDGE.md`): under the theorem's own hypothesis that predicate is constantly `True`, and a
schema built from it would name nothing. -/
noncomputable def inconsistencySchema (T' : ArithmeticTheory) [T'.Δ₁] :
    ArithmeticSemisentence 1 :=
  codeOfREPred (ProvableCode T')

/-- The schema has exactly the intended standard-model meaning. -/
lemma inconsistencySchema_spec (T' : ArithmeticTheory) [T'.Δ₁] (z : ℕ) :
    (inconsistencySchema T').Evalb ![z] ↔ ProvableCode T' z :=
  codeOfREPred_spec (provableCode_re T') (x := z)

/-- **The schema is not argument-insensitive.**  Its shape is unreachable (`codeOfREPred` is
picked by `Classical.epsilon`), but its defining spec is not nothing: a consistent `T'` proves
`⊤` and not `⊥`, so the chosen formula cannot be one that ignores its argument.

Kind `P` (proved).  Provenance: (a) derived in-project from `provableCode_quote_verum` and
`not_provableCode_quote_falsum`. -/
lemma inconsistencySchema_not_argument_insensitive (T' : ArithmeticTheory) [T'.Δ₁]
    (hcon : Entailment.Consistent T') :
    ¬ ∀ z z' : ℕ,
      (inconsistencySchema T').Evalb ![z] ↔ (inconsistencySchema T').Evalb ![z'] := by
  intro h
  have hz : (inconsistencySchema T').Evalb ![(⌜(⊤ : ArithmeticSentence)⌝ : ℕ)] :=
    (inconsistencySchema_spec T' _).mpr (provableCode_quote_verum T')
  have hz' : ¬ (inconsistencySchema T').Evalb ![(⌜(⊥ : ArithmeticSentence)⌝ : ℕ)] := fun hx =>
    not_provableCode_quote_falsum T' hcon ((inconsistencySchema_spec T' _).mp hx)
  exact hz' ((h _ _).mp hz)

/-- **The schema mentions its argument**, the occurrence form of the previous lemma and the
side condition of substitution injectivity.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`Semiformula.subst_eq_of_not_mentions` (`Framework/SubstOccurrence.lean`),
`Semiformula.eval_substs`. -/
lemma inconsistencySchema_mentions_zero (T' : ArithmeticTheory) [T'.Δ₁]
    (hcon : Entailment.Consistent T') :
    (inconsistencySchema T' : ArithmeticSemisentence 1).Mentions 0 := by
  by_contra hmem
  refine inconsistencySchema_not_argument_insensitive T' hcon fun z z' => ?_
  have key : ∀ w : ℕ,
      Semiformula.Evalb (M := ℕ) (![] : Fin 0 → ℕ)
          ((inconsistencySchema T')/[(‘↑w’ : Semiterm ℒₒᵣ Empty 0)])
        ↔ (inconsistencySchema T').Evalb ![w] := by
    intro w
    simp [Semiformula.eval_substs, Matrix.constant_eq_singleton]
  have hsub := Semiformula.subst_eq_of_not_mentions hmem
    (‘↑z’ : Semiterm ℒₒᵣ Empty 0) (‘↑z'’ : Semiterm ℒₒᵣ Empty 0)
  rw [← key z, ← key z', hsub]

/-- **The day-`n` name of the theory `Θ′ₙ = Θ₀ ∪ {σₙ}`**: the code of `∼σₙ`.  Under the
deduction theorem this single code determines whether `Θ′ₙ` is inconsistent, and it is what the
day-`n` claim sentence writes out.

*Metering disclosure — `BigDigits (deductionFamilyArg σ)` is STRONGER than the paper's
`def:ec`, not equal to it.*  `BigDigits` bounds the base-4 **digit count** of the natural
number it is applied to, which is the right meter when that number is the *written form* of
the object (a bitstring input; a machine named by the linear `Code.sourceNat` — the doctrine
is stated at `DigitMachineCodes`, `Framework/WriteOut.lean`, and for formulas at the header
of `Construction/Witnesses/ArithmeticSource.lean`).  Here the number is a **Gödel code of a
formula**, and Foundation's encoding pairs at every node, so the code value is roughly
doubly exponential and its digit count roughly `2 ^ depth` — the same failure mode that made
`Encodable.encode` unusable as a machine-naming map.  The class therefore admits only
families of `O(log n)` formula depth (a `binNumeral`-spelled family is the intended shape)
and **excludes** paper-admissible families whose *source text* is short but whose parse tree
is deep — the `iffChain`-style families that `PolyArithmeticSourceSeq` was introduced for.

This is a live over-strength hypothesis on `thm:incons`, disclosed rather than repaired here:
the faithful repair is to meter the day's theory name on the source language
(`PolyArithmeticSourceSeq`, `ArithmeticSource.lean`) instead of on the Gödel code, which is
queued as source-metered re-rendering work and deliberately not attempted in this round.
Being a strengthening of a *hypothesis*, it narrows which theory sequences the endpoint
covers; it does not weaken the conclusion at those it does cover. -/
noncomputable def deductionFamilyArg (σ : ℕ → ArithmeticSentence) (n : ℕ) : ℕ := ⌜∼(σ n)⌝

/-- **The paper's “`⌜Θ′ₙ⌝` is inconsistent”**: the base theory's provability schema at the
compact name of `⌜∼σₙ⌝`. -/
noncomputable def inconsistencyArgClaimSentence (T' : ArithmeticTheory) [T'.Δ₁]
    (σ : ℕ → ArithmeticSentence) (n : ℕ) : Sentence :=
  schemaArgClaimSentence (inconsistencySchema T') (binNumeral (deductionFamilyArg σ n))

/-- The bare arithmetic sentence under the claim atom, for callers that need it. -/
noncomputable def inconsistencyArgClaimInstance (T' : ArithmeticTheory) [T'.Δ₁]
    (σ : ℕ → ArithmeticSentence) (n : ℕ) : ArithmeticSentence :=
  (inconsistencySchema T')/[(binNumeral (deductionFamilyArg σ n)).const]

/-- **The standing extensionality test, proved.**  Days whose adjoined axioms have distinct
negation *codes* — not merely distinct consistency behaviour — get distinct claim sentences,
with no hypothesis on the day's theories beyond consistency of the base.  This is what makes
`hσ` and the sequence `σ` load-bearing rather than decorative.

Kind `C` (composition).  Provenance: (a) derived in-project from
`schemaArgClaimSentence_ne_of_const_ne`, `inconsistencySchema_mentions_zero`,
`binNumeral_const_ne`. -/
lemma inconsistencyArgClaimSentence_ne_of_arg_ne (T' : ArithmeticTheory) [T'.Δ₁]
    (hcon : Entailment.Consistent T') (σ σ' : ℕ → ArithmeticSentence) (n n' : ℕ)
    (h : deductionFamilyArg σ n ≠ deductionFamilyArg σ' n') :
    inconsistencyArgClaimSentence T' σ n ≠ inconsistencyArgClaimSentence T' σ' n' :=
  schemaArgClaimSentence_ne_of_const_ne _ (inconsistencySchema_mentions_zero T' hcon) _ _
    (binNumeral_const_ne _ _ h)

/-- **The `thm:incons` claim family, over the paper's own deductive process.**

The positive obligation is Σ₁-completeness at the universal schema (`re_complete_mp`, which
needs `[𝗣𝗔⁻ ⪯ T]` and nothing else); the `def:ec` obligation is discharged at the compact
argument name, and that is what `hσ` is consumed by.  No semantic hypothesis on `T`, no
hypothesis relating `T` to `T'`, and no consistency hypothesis on `T'` — an inconsistent base
theory makes every day's claim true, which the endpoint's conclusion tracks correctly.

Kind `C` (composition).  Provenance: (a) derived in-project; (b) Foundation citations —
`codeOfREPred` and `sigma_one_completeness` (through `re_complete_mp`),
`Bootstrapping.provable_iff_provable` and `Entailment.deduction_iff` (through
`provableCode_neg_iff_not_consistent_adjoin`); (c) modelling substitution — the deduction-family
paraphrase of the paper's arbitrary e.c. theory sequence, disclosed in the section header. -/
noncomputable def representedInconsistentTheoryClaims [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    (T' : ArithmeticTheory) [T'.Δ₁] (σ : ℕ → ArithmeticSentence)
    (hσ : BigDigits (deductionFamilyArg σ)) :
    InconsistentTheoryClaims (paperTheoryDP T)
      (fun n => ¬Entailment.Consistent (σ n ∷ T')) where
  inconsistencySentence := inconsistencyArgClaimSentence T' σ
  inconsistency_poly :=
    schemaArgClaimSentence_bigSentenceCodes (inconsistencySchema T') _
      (polySegStream_binNumeral_const hσ)
  inconsistency_provable n hn := by
    refine paperTheoryDP_covers_schemaArgClaim T (inconsistencySchema T') _ ?_
    refine (provable_subst_binNumeral_iff T (inconsistencySchema T') _).mpr ?_
    exact re_complete_mp (T := T) (provableCode_re T')
      ((provableCode_neg_iff_not_consistent_adjoin T' (σ n)).mpr hn)

/-- **Disbelief in Inconsistent Theories** (`thm:incons`), unconditional over `LIA`.  Both of
the paper's conjuncts: belief in the day-`n` inconsistency sentence tends to `1`, and belief in
its negation — the paper's consistency sentence — tends to `0`.

`hinc` is the paper's own premise, that each `Θ′ₙ` is inconsistent, stated at the theory
`σₙ ∷ Θ₀` itself rather than at any provability surrogate.

*Modelling substitution (disclosed).*  The theory sequence is the deduction family
`Θ′ₙ = Θ₀ ∪ {σₙ}` rather than an arbitrary e.c. sequence of recursively axiomatizable
theories; see the section header for the Foundation obstruction that forces it and for why the
day's theory is nevertheless genuinely named in the sentence.
*Over-strength `def:ec` hypothesis (disclosed).*  `hσ` meters the day's theory name by the
base-4 digit count of a formula's **Gödel code**, not by the length of its source text.
Foundation's formula encoding pairs at every node, so that digit count is roughly
`2 ^ depth`: the class admits only `O(log n)`-depth (e.g. `binNumeral`-spelled) families and
excludes paper-admissible families that are short to write but deep to parse.  The paper's
`def:ec` meters the writing (tex:753-755, tex:1931-1933); the faithful repair is to state
this premise on the source language (`PolyArithmeticSourceSeq`,
`Construction/Witnesses/ArithmeticSource.lean`) and is queued, not done.  Full statement of
the boundary at `deductionFamilyArg`.
*Residual hypothesis (disclosed).*  `[T.Δ₁]`, `[T'.Δ₁]` and `[𝗣𝗔⁻ ⪯ T]` are the strengthenings
beyond the paper (see the global disclosure in `LogicalInduction/README.md`), which assumes
only that the theories are consistent (for `Θ`), c.e. and represent computations: they ask for
a Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e. theory has a
deductively equivalent Δ₁ axiomatization, so the theorems transfer; that reduction is not
formalized here.
Paper node: `thm:incons` -/
theorem lic_disbelief_inconsistent_theories_unconditional [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] (T' : ArithmeticTheory) [T'.Δ₁]
    (σ : ℕ → ArithmeticSentence) (hσ : BigDigits (deductionFamilyArg σ))
    (hinc : ∀ n, ¬Entailment.Consistent (σ n ∷ T')) :
    ((fun n => liaHistory (paperTheoryDP T) n
        ((representedInconsistentTheoryClaims T T' σ hσ).inconsistencySentence n))
          ≈ₙ fun _ => 1) ∧
      ((fun n => liaHistory (paperTheoryDP T) n
        ((representedInconsistentTheoryClaims T T' σ hσ).consistencySentence n))
          ≈ₙ fun _ => 0) :=
  haveI := paperLIA T
  lic_disbelief_inconsistent_theories (liaHistory (paperTheoryDP T)) (paperTheoryDP T) _
    (representedInconsistentTheoryClaims T T' σ hσ) hinc
    (paperTheoryDP_hworld_stages T inferInstance)

/-- **`thm:incons`, applied with nothing left to the caller.**  The market is over `𝗜𝚺₁`, the
base theory of the deduction family is `𝗜𝚺₁`, and the adjoined axiom is `⊥`, so every day's
theory `𝗜𝚺₁ ∪ {⊥}` is **actually inconsistent** — `hinc` is discharged by the deduction bridge,
the write-out class by `BigDigits.const`, and every instance argument by Foundation's own
`𝗜𝚺₁` instances.  This replaces the superseded `0 < n` stand-in, whose predicate was not even
a statement about a theory.

This witness is constant in the day; the day-varying one is
`thm_incons_applied_alternating` below. -/
example :
    ((fun n => liaHistory (paperTheoryDP 𝗜𝚺₁) n
        ((representedInconsistentTheoryClaims 𝗜𝚺₁ 𝗜𝚺₁ (fun _ => ⊥)
          (BigDigits.const _)).inconsistencySentence n)) ≈ₙ fun _ => 1) ∧
      ((fun n => liaHistory (paperTheoryDP 𝗜𝚺₁) n
        ((representedInconsistentTheoryClaims 𝗜𝚺₁ 𝗜𝚺₁ (fun _ => ⊥)
          (BigDigits.const _)).consistencySentence n)) ≈ₙ fun _ => 0) :=
  lic_disbelief_inconsistent_theories_unconditional 𝗜𝚺₁ 𝗜𝚺₁ (fun _ => ⊥) (BigDigits.const _)
    (fun _ => by rw [not_consistent_adjoin_iff]; simp)

/-! ### A day-varying `thm:incons` witness, and what is still missing

The constant witness above leaves the day-separation theorem
`inconsistencyArgClaimSentence_ne_of_arg_ne` unexercised: its hypothesis is that two days'
axiom codes differ, and at a constant family they never do.  The family below is genuinely
day-varying — it alternates between two refutable axioms — so the separation theorem fires
at two concrete days with nothing assumed.

*What this witness does and does not establish.*  It shows that the endpoint's premise set
admits a family whose day-`n` theory really changes with `n`, and that the rendering assigns
those days distinct sentences.  It does **not** exhibit a family with *unboundedly many*
distinct theories: this one takes two values.  A family of unbounded description length — the
natural candidate being `σₙ := “binNumeral n ≠ binNumeral n”`, refutable on every day, whose
*source text* is `O(log n)` symbols — cannot be admitted, because `hσ` meters the Gödel
**code** rather than the source (the boundary stated at `deductionFamilyArg`), and the
required certificate is not reachable from the digit calculus as it stands:

  -- TODO(thm:incons): need `BigDigits (fun n => ⌜∼(binNumeral-spelled σ n)⌝)`.
  -- Blocked on a missing combinator, not on size: for such a σ the code's base-4 digit
  -- count is polynomial (bit length `Θ(√n)`), so the statement is true.  What is absent is
  -- closure of `BigDigits` under an UNBOUNDED-DEPTH `Nat.pair` nesting.  Foundation's
  -- `Semiformula.toNat`/`Semiterm.toNat` pair at every constructor node, so `⌜∼σₙ⌝` is a
  -- `Nat.pair`-shell iterated `Θ(log n)` times over the Horner recursion of `binNumeral`;
  -- every `BigDigits` closure in `Framework/DigitArith.lean` (`const`, `natPair`, `succ`,
  -- `add`, `mul`, `ifZero`, `comp`) composes only a CONSTANT number of times, and
  -- `PolyFueled.prec` cannot iterate because its `IsPolyBounded` state hypothesis forbids a
  -- bignum-valued state.  The missing lemma is a `BigDigits.precBig`: poly-fueled digit
  -- access to `F k` uniformly in `(k, j)` for a pairing-shell recurrence
  -- `F (k+1) = shell (F k)`, together with the base-4 digit theory of `Nat.pair` at
  -- unbounded nesting that it rests on.  `BigDigits.ofBase16Digits`
  -- (`Framework/CodeSource.lean`) — the tool that made `bigDigits_sourceNat_nest`
  -- tractable — does not apply, because `Nat.pair` is not digit concatenation.
  -- The faithful repair is the other one: meter this premise on the source language
  -- (`PolyArithmeticSourceSeq`), where the family is admissible by
  -- `polySegStream_binNumeralEnc` and no code-digit theory is needed at all. -/

/-- The day-varying adjoined axiom: `⊥` on even days, `⊥ ⋏ ⊥` on odd ones.  Both are refutable
in every theory, so every day's theory is actually inconsistent; their Gödel codes differ, so
the claim sentences do too. -/
noncomputable def alternatingInconsistentAxiom (n : ℕ) : ArithmeticSentence :=
  if n % 2 = 0 then ⊥ else ⊥ ⋏ ⊥

/-- The write-out premise at the alternating family: a two-way dispatch on a poly-fueled
parity test between two constant codes.

Kind `C` (composition).  Provenance: (a) derived in-project from `BigDigits.ifZero`,
`BigDigits.const`, `BigDigits.mod_two`. -/
lemma alternatingInconsistentAxiom_digits :
    BigDigits (deductionFamilyArg alternatingInconsistentAxiom) := by
  obtain ⟨c, hc⟩ := (BigDigits.of_polyFueled PolyFueled.id).mod_two
  refine (BigDigits.ifZero (BigDigits.const ⌜∼(⊥ : ArithmeticSentence)⌝)
    (BigDigits.const ⌜∼((⊥ : ArithmeticSentence) ⋏ ⊥)⌝) hc).of_eq fun n => ?_
  by_cases h : n % 2 = 0 <;>
    simp [deductionFamilyArg, alternatingInconsistentAxiom, h]

/-- Every day's theory really is inconsistent, by the deduction bridge. -/
lemma alternatingInconsistentAxiom_inconsistent (T' : ArithmeticTheory) (n : ℕ) :
    ¬Entailment.Consistent (alternatingInconsistentAxiom n ∷ T') := by
  rw [not_consistent_adjoin_iff]
  by_cases h : n % 2 = 0
  · simp [alternatingInconsistentAxiom, h]
  · simp only [alternatingInconsistentAxiom, if_neg h]
    cl_prover

/-- Distinct adjoined axioms have distinct names: the day's theory code is the Gödel code of
`∼σₙ`, and Foundation's quote at `ℕ` is `Encodable.encode`, which is injective.

Kind `C` (composition).  Provenance: (b) Foundation citations —
`LO.FirstOrder.Sentence.quote_def` (`rfl`), `Semiformula.quote_inj_iff`,
`Rewriting.emb_injective`. -/
lemma deductionFamilyArg_ne_of_ne {σ : ℕ → ArithmeticSentence} {m n : ℕ}
    (h : σ m ≠ σ n) : deductionFamilyArg σ m ≠ deductionFamilyArg σ n := by
  intro hq
  refine h ?_
  have hq' : (⌜(Rewriting.emb (∼(σ m)) : ArithmeticSemiformula ℕ 0)⌝ : ℕ)
      = ⌜(Rewriting.emb (∼(σ n)) : ArithmeticSemiformula ℕ 0)⌝ := hq
  simpa using Rewriting.emb_injective (Semiformula.quote_inj_iff.mp hq')

/-- **`thm:incons`, applied at a day-varying family with nothing left to the caller.**  Every
hypothesis and every instance argument is discharged: the write-out premise at
`alternatingInconsistentAxiom_digits`, the inconsistency of each day's theory at
`alternatingInconsistentAxiom_inconsistent`, and the theory instances by Foundation's own
`𝗜𝚺₁` instances.  Unlike the constant witness above, the day-`n` theory really changes with
`n`, so the day-separation theorem below applies non-trivially.
Paper node: `thm:incons` -/
theorem thm_incons_applied_alternating :
    ((fun n => liaHistory (paperTheoryDP 𝗜𝚺₁) n
        ((representedInconsistentTheoryClaims 𝗜𝚺₁ 𝗜𝚺₁ alternatingInconsistentAxiom
          alternatingInconsistentAxiom_digits).inconsistencySentence n)) ≈ₙ fun _ => 1) ∧
      ((fun n => liaHistory (paperTheoryDP 𝗜𝚺₁) n
        ((representedInconsistentTheoryClaims 𝗜𝚺₁ 𝗜𝚺₁ alternatingInconsistentAxiom
          alternatingInconsistentAxiom_digits).consistencySentence n)) ≈ₙ fun _ => 0) :=
  lic_disbelief_inconsistent_theories_unconditional 𝗜𝚺₁ 𝗜𝚺₁ alternatingInconsistentAxiom
    alternatingInconsistentAxiom_digits (alternatingInconsistentAxiom_inconsistent 𝗜𝚺₁)

/-- **The day-separation theorem, applied.**  Days `0` and `1` of the alternating family get
different claim sentences — no hypothesis, no behavioural side condition. -/
example :
    inconsistencyArgClaimSentence 𝗜𝚺₁ alternatingInconsistentAxiom 0
      ≠ inconsistencyArgClaimSentence 𝗜𝚺₁ alternatingInconsistentAxiom 1 :=
  inconsistencyArgClaimSentence_ne_of_arg_ne 𝗜𝚺₁ (RepresentsComputations.consistent 𝗜𝚺₁)
    _ _ 0 1 (deductionFamilyArg_ne_of_ne (by simp [alternatingInconsistentAxiom]))

end Inconsistency

#print axioms representedClaimSentence_bigSentenceCodes
#print axioms representedBoundedClaims
#print axioms representedBoundedHaltingClaims
#print axioms lic_does_not_anticipate_halting_ofComputation
#print axioms lic_belief_finitistic_consistency_unconditional
#print axioms lic_belief_stronger_theory_consistency_unconditional
#print axioms lic_does_not_anticipate_halting_unconditional
#print axioms schemaArgClaimSentence_bigSentenceCodes
#print axioms provable_schemaArgClaim_iff
#print axioms provable_neg_schemaArgClaim_iff
#print axioms provable_subst_binNumeral_iff
#print axioms universalRunValue_computable
#print axioms universalRunValue_boundedArg
#print axioms boundedArg_digits
#print axioms haltingArgClaimInstance_true_iff
#print axioms schemaArgClaimSentence_ne_of_const_ne
#print axioms binNumeral_const_ne
#print axioms haltingArgClaimSentence_ne_of_claimInput_ne
#print axioms haltingArgClaimSentence_ne_of_source_ne
#print axioms representedClaimSentence_ne_of_const_ne
#print axioms representedClaimSentence_ne_of_arg_ne
#print axioms haltingArgClaimSentence_ne_of_halts_ne
#print axioms representedClaimSentence_ne_of_runValue_ne
#print axioms representedHaltingClaims
#print axioms lic_learns_halting_patterns_ofComputation
#print axioms lic_learns_provable_nonhalting_patterns_ofComputation
#print axioms lia_learns_halting_patterns_unconditional
#print axioms lic_learns_provable_nonhalting_patterns_unconditional
#print axioms models_loopsWitnessSentence
#print axioms loopsTheory
#print axioms loopsTheory_consistent
#print axioms loopsTheory_soundOnSigma1
#print axioms loopsWitness_never_halts
#print axioms loopsTheory_refutes
#print axioms thm_loops_applied_at_loopsTheory
#print axioms conClaimArg_digits
#print axioms conClaimSentence_bigSentenceCodes
#print axioms conClaimSentence_ne_of_day_ne
#print axioms conGamma
#print axioms conGamma_spec
#print axioms conGamma_mentions_zero
#print axioms conGamma_mentions_zero_of_bProv
#print axioms conGamma_mentions_zero_of_horizon_unbounded
#print axioms conGamma_mentions_zero_ackermann
#print axioms representedConClaims
#print axioms inconsistencySchema
#print axioms inconsistencySchema_spec
#print axioms inconsistencySchema_not_argument_insensitive
#print axioms inconsistencySchema_mentions_zero
#print axioms deductionFamilyArg
#print axioms deductionFamilyArg_ne_of_ne
#print axioms inconsistencyArgClaimSentence
#print axioms inconsistencyArgClaimInstance
#print axioms inconsistencyArgClaimSentence_ne_of_arg_ne
#print axioms representedInconsistentTheoryClaims
#print axioms lic_disbelief_inconsistent_theories_unconditional
#print axioms alternatingInconsistentAxiom_digits
#print axioms alternatingInconsistentAxiom_inconsistent
#print axioms thm_incons_applied_alternating

end LogicalInduction
