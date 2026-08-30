import LogicalInduction.Construction.Witnesses.PaperTheoryDP
import LogicalInduction.Construction.Witnesses.SubstEmission
import LogicalInduction.Framework.RepresentsComputations

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

## What is, and is not, proved about that test here

Under the current rendering the sentence's dependence on the machine is **definitional**, not
a theorem of this file.  The day-`n` sentence is a fixed object — `universalHaltingSchema`, or
the `γ` representing `universalRunValue f` — at the argument term
`binNumeral (haltingClaimInput ⌜mₙ⌝ xₙ)`; `Code.sourceNat` and `binNumeral` are injective, so
two sequences with the same extension but different programs give literally *different
argument terms* inside the sentence.  What is missing is only the last step, from different
arguments to different sentences: `σ/[t] ≠ σ/[t']` for `t ≠ t'` requires a
substitution-injectivity / occurrence lemma for `σ` (it is false for a `σ` that does not
mention `#0`), and Foundation exposes none.  The side condition does hold here —
`universalHaltingSchema_not_argument_insensitive` proves the universal schema is not
argument-insensitive — so the full syntactic separation is true; supplying the missing lemma
is **queued infrastructure**, not a defect of the rendering.

The two `_ne_of_` lemmas below therefore prove something weaker and different: *behavioural*
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

`[𝗜𝚺₁ ⪯ T]` is a strengthening beyond the paper, which assumes only that `Θ` is consistent,
c.e., and represents computations.  It is needed here for exactly one thing — `paperTheoryDP`
is proved computable through Foundation's internal provability predicate, which needs `𝗜𝚺₁`
— and is scheduled for removal when that is re-proved from c.e.-ness alone.  It is disclosed
at each of the five endpoints.
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
lemma paperTheoryDP_covers_representedClaim [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    (γ : ArithmeticSemisentence 2) (t : Semiterm.Const ℒₒᵣ)
    (h : T ⊢ ∼(reprAllTerm γ 0 t)) :
    ∃ k, representedClaimSentence γ t ∈ (paperTheoryDP T).D k := by
  have := paperTheoryDP_covers_outer_provable T _ h
  rwa [paperPrimeDecompose_neg_reprAllTerm] at this

/-- The theorem process publishes the negated claim atom when `T` proves the value-`0`
sentence. -/
lemma paperTheoryDP_covers_representedClaim_neg [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    (γ : ArithmeticSemisentence 2) (t : Semiterm.Const ℒₒᵣ)
    (h : T ⊢ reprAllTerm γ 0 t) :
    ∃ k, (∼representedClaimSentence γ t) ∈ (paperTheoryDP T).D k := by
  have := paperTheoryDP_covers_outer_provable T _ h
  rwa [paperPrimeDecompose_reprAllTerm] at this

/-! ## Transferring provability to the compact spelling

Every literal below is derived at Foundation's unary numeral — that is the form
`RepresentsComputations` and `re_complete_mp` speak — and then carried to the compact
spelling by one value-transfer step.  The transfer is Gödel completeness in both directions
and adds no hypothesis on `T`: `𝗣𝗔⁻ ⪯ T` follows from the `[𝗜𝚺₁ ⪯ T]` every endpoint here
already carries. -/

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
noncomputable def representedBoundedClaims [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗥₀ ⪯ T]
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
noncomputable def representedBoundedHaltingClaims [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗥₀ ⪯ T]
    [RepresentsComputations T]
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (hm : DigitMachineCodes machines) (hi : BigDigits inputs)
    (hh : ComputableHorizon horizons) :
    RepresentedDecidableClaims (paperTheoryDP T)
      (fun n => CodeHaltsWithin (machines n) (inputs n) (horizons n)) :=
  representedBoundedClaims T hm hi _
    (exists_reprAll_of_representsComputations T hh.computable).choose_spec

/-- Constructor for the decidable-claims boundary from a concrete bounded computation, at
the paper's representability premise.  `C.truth_iff` transports the represented bounded-run
family onto the caller's truth predicate.  `C`'s machine is fixed, so the constant machine
sequence is named by `digitMachineCodes_const`; the sentence still names it, and the day
still enters the argument through the horizon slot.
Paper node: `thm:pac` -/
noncomputable def representedDecidableClaimsOfComputation [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗥₀ ⪯ T]
    [RepresentsComputations T]
    {truth : ℕ → Prop} (C : BoundedComputation truth) :
    RepresentedDecidableClaims (paperTheoryDP T) truth :=
  let R := representedBoundedClaims T (machines := fun _ => C.machine) (inputs := C.input)
    (steps := C.steps) (digitMachineCodes_const C.machine) C.input_poly _
    (exists_reprAll_of_representsComputations T C.horizon.computable).choose_spec
  { sentence := R.sentence
    sentence_poly := R.sentence_poly
    provable_of_true := fun n hn => R.provable_of_true n ((C.truth_iff n).mp hn)
    disprovable_of_false := fun n hn =>
      R.disprovable_of_false n fun hb => hn ((C.truth_iff n).mpr hb) }

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
private lemma paperTheoryDP_hworld_stages [T.Δ₁] [𝗜𝚺₁ ⪯ T] (hcon : Entailment.Consistent T) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperTheoryDP T).D n) := by
  haveI := hcon
  obtain ⟨v, hv⟩ := paperTheoryDP_nonvacuous T
  exact fun n => ⟨v, hv n⟩

/-- The constructed inductor over the paper's theorem process. -/
private noncomputable abbrev paperLIA [T.Δ₁] [𝗜𝚺₁ ⪯ T] :
    IsLogicalInductor (liaHistory (paperTheoryDP T)) (paperTheoryDP T) :=
  LIA_is_logical_inductor (paperTheoryDP T) (paperTheoryDP_computable T)

section Endpoints

variable [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗥₀ ⪯ T] [RepresentsComputations T]

/-- Finitistic-consistency belief, with the representation boundary discharged by a
concrete computation and named through the paper's own `⌜f⌝(⌜n⌝)`.  The horizon `f` of `C`
is an arbitrary computable function, named in the claim by its program
(`ComputableHorizon`) and left unevaluated — the paper's class.
*Residual hypothesis (disclosed).*  `[𝗜𝚺₁ ⪯ T]` is a strengthening beyond the paper,
which assumes only that `Θ` is consistent, c.e. and represents computations; it is needed
solely so that provability in `T` is recursively enumerable through Foundation's internal
provability predicate, and is scheduled for removal.  `[T.Δ₁]` is the second strengthening:
it asks for a Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e.
theory has a deductively equivalent Δ₁ axiomatization, so the theorems transfer; that
reduction is not formalized here.
Paper node: `thm:pac` -/
theorem lic_belief_finitistic_consistency_ofComputation
    (P : History) [IsLogicalInductor P (paperTheoryDP T)]
    (consistentWithin : ℕ → Prop) (C : BoundedComputation consistentWithin)
    (hconsistent : ∀ n, consistentWithin n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperTheoryDP T).D n)) :
    (fun n => P n ((representedDecidableClaimsOfComputation T C).sentence n)) ≈ₙ
      fun _ => 1 :=
  lic_belief_finitistic_consistency P (paperTheoryDP T) consistentWithin
    (representedDecidableClaimsOfComputation T C) hconsistent hworld

/-- Same statement and same arbitrary-computable-horizon class as `thm:pac`; only the
supplied finite-consistency predicate differs.
*Residual hypothesis (disclosed).*  `[𝗜𝚺₁ ⪯ T]` is a strengthening beyond the paper,
which assumes only that `Θ` is consistent, c.e. and represents computations; it is needed
solely so that provability in `T` is recursively enumerable through Foundation's internal
provability predicate, and is scheduled for removal.  `[T.Δ₁]` is the second strengthening:
it asks for a Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e.
theory has a deductively equivalent Δ₁ axiomatization, so the theorems transfer; that
reduction is not formalized here.
Paper node: `thm:pazfc` -/
theorem lic_belief_stronger_theory_consistency_ofComputation
    (P : History) [IsLogicalInductor P (paperTheoryDP T)]
    (strongerConsistentWithin : ℕ → Prop)
    (C : BoundedComputation strongerConsistentWithin)
    (hconsistent : ∀ n, strongerConsistentWithin n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperTheoryDP T).D n)) :
    (fun n => P n ((representedDecidableClaimsOfComputation T C).sentence n)) ≈ₙ
      fun _ => 1 :=
  lic_belief_stronger_theory_consistency P (paperTheoryDP T) strongerConsistentWithin
    (representedDecidableClaimsOfComputation T C) hconsistent hworld

/-- The horizon sequence is arbitrary computable — `hh` names its program rather than
bounding its growth — which is the paper's "let `f` be any computable function".
*Residual hypothesis (disclosed).*  `[𝗜𝚺₁ ⪯ T]` is a strengthening beyond the paper,
which assumes only that `Θ` is consistent, c.e. and represents computations; it is needed
solely so that provability in `T` is recursively enumerable through Foundation's internal
provability predicate, and is scheduled for removal.  `[T.Δ₁]` is the second strengthening:
it asks for a Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e.
theory has a deductively equivalent Δ₁ axiomatization, so the theorems transfer; that
reduction is not formalized here.
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

/-- `thm:pac`, unconditional over `LIA`, at the paper's horizon class: `C`'s step budget is
any computable `f`, named by its program and evaluated by the arithmetic schema rather than
by the sentence emitter.
*Residual hypothesis (disclosed).*  `[𝗜𝚺₁ ⪯ T]` is a strengthening beyond the paper,
which assumes only that `Θ` is consistent, c.e. and represents computations; it is needed
solely so that provability in `T` is recursively enumerable through Foundation's internal
provability predicate, and is scheduled for removal.  `[T.Δ₁]` is the second strengthening:
it asks for a Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e.
theory has a deductively equivalent Δ₁ axiomatization, so the theorems transfer; that
reduction is not formalized here.
Paper node: `thm:pac` -/
theorem lic_belief_finitistic_consistency_unconditional
    (consistentWithin : ℕ → Prop) (C : BoundedComputation consistentWithin)
    (hconsistent : ∀ n, consistentWithin n) :
    (fun n => liaHistory (paperTheoryDP T) n
      ((representedDecidableClaimsOfComputation T C).sentence n)) ≈ₙ fun _ => 1 :=
  haveI := paperLIA T
  lic_belief_finitistic_consistency_ofComputation T (liaHistory (paperTheoryDP T))
    consistentWithin C hconsistent (paperTheoryDP_hworld_stages T (RepresentsComputations.consistent T))

/-- `thm:pazfc`, unconditional over `LIA`, at the same arbitrary-computable-horizon class
as `thm:pac`.
*Residual hypothesis (disclosed).*  `[𝗜𝚺₁ ⪯ T]` is a strengthening beyond the paper,
which assumes only that `Θ` is consistent, c.e. and represents computations; it is needed
solely so that provability in `T` is recursively enumerable through Foundation's internal
provability predicate, and is scheduled for removal.  `[T.Δ₁]` is the second strengthening:
it asks for a Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e.
theory has a deductively equivalent Δ₁ axiomatization, so the theorems transfer; that
reduction is not formalized here.
Paper node: `thm:pazfc` -/
theorem lic_belief_stronger_theory_consistency_unconditional
    (strongerConsistentWithin : ℕ → Prop)
    (C : BoundedComputation strongerConsistentWithin)
    (hconsistent : ∀ n, strongerConsistentWithin n) :
    (fun n => liaHistory (paperTheoryDP T) n
      ((representedDecidableClaimsOfComputation T C).sentence n)) ≈ₙ fun _ => 1 :=
  haveI := paperLIA T
  lic_belief_stronger_theory_consistency_ofComputation T (liaHistory (paperTheoryDP T))
    strongerConsistentWithin C hconsistent (paperTheoryDP_hworld_stages T (RepresentsComputations.consistent T))

/-- `thm:dontwait`, unconditional over `LIA`.  `hh` supplies the horizon program for an
arbitrary computable `f` — no growth bound — which is the paper's own quantifier, and `hm`
and `hi` are the write-out metered machine/input classes, which is the paper's e.c. sequence
of bitstrings `⟨y⟩` (tex:1946-1952).  The three are independent hypotheses of one signature.
*Residual hypothesis (disclosed).*  `[𝗜𝚺₁ ⪯ T]` is a strengthening beyond the paper,
which assumes only that `Θ` is consistent, c.e. and represents computations; it is needed
solely so that provability in `T` is recursively enumerable through Foundation's internal
provability predicate, and is scheduled for removal.  `[T.Δ₁]` is the second strengthening:
it asks for a Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e.
theory has a deductively equivalent Δ₁ axiomatization, so the theorems transfer; that
reduction is not formalized here.
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

/-- **`thm:pac` and `thm:pazfc`, applied.**  The bounded computation is
`alwaysBoundedComputation` — `Code.zero` on input `0` within `n + 1` interpreter steps — whose
truth predicate holds on every day.  So `hconsistent` is *proved*, not assumed: the premise
pair `(C, hconsistent)` of both endpoints is jointly inhabited, and nothing is left to the
caller beyond the theory instances.

Two things this example does not hide.  First, `thm:pac` and `thm:pazfc` are, at every layer
of this development, the **same theorem**: `lic_belief_finitistic_consistency_unconditional`
and `lic_belief_stronger_theory_consistency_unconditional` have literally the same statement
once the supplied predicate is fixed, and each is `rfl`-interchangeable with the other (as the
`example` below records).  The paper's distinction between them is the *choice* of
consistency predicate, which this layer takes as given data.  Second, that choice is where
the remaining work is: rendering the paper's `Con(Θ)(⌜f⌝(⌜n⌝))` as an arithmetized
consistency statement about a specific theory is the queued §4.10 project, and is not started
here. -/
example :
    (fun n => liaHistory (paperTheoryDP T) n
      ((representedDecidableClaimsOfComputation T alwaysBoundedComputation).sentence n))
        ≈ₙ fun _ => 1 :=
  lic_belief_finitistic_consistency_unconditional T (fun _ => True)
    alwaysBoundedComputation (fun _ => trivial)

/-- `thm:pac` and `thm:pazfc` are the same statement at this layer — literally `rfl`. -/
example (truth : ℕ → Prop) (C : BoundedComputation truth) (h : ∀ n, truth n) :
    lic_belief_finitistic_consistency_unconditional T truth C h
      = lic_belief_stronger_theory_consistency_unconditional T truth C h :=
  rfl

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
lemma paperTheoryDP_covers_schemaArgClaim [T.Δ₁] [𝗜𝚺₁ ⪯ T] (σ : ArithmeticSemisentence 1)
    (t : Semiterm.Const ℒₒᵣ) (h : T ⊢ (σ/[t.const] : ArithmeticSentence)) :
    ∃ k, schemaArgClaimSentence σ t ∈ (paperTheoryDP T).D k := by
  have := paperTheoryDP_covers_outer_provable T _ ((provable_schemaArgClaim_iff T σ t).mpr h)
  rwa [paperPrimeDecompose_schemaArgClaim] at this

/-- The theorem process publishes the negated claim atom when `T` refutes the argument
instance. -/
lemma paperTheoryDP_covers_schemaArgClaim_neg [T.Δ₁] [𝗜𝚺₁ ⪯ T]
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
`inputs` through the *argument*, not through the schema, so distinct machines give distinct
sentences whenever they differ in halting behaviour
(`haltingArgClaimSentence_ne_of_halts_ne`). -/
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

Machine dependence of the sentence is not proved here because it is **definitional**: the
day-`n` sentence is `universalHaltingSchema` at the argument term
`binNumeral (haltingClaimInput ⌜mₙ⌝ xₙ)`, and `Code.sourceNat` and `binNumeral` are injective,
so different programs give different argument terms.  The remaining step — from `t ≠ t'` to
`σ/[t] ≠ σ/[t']` — needs a substitution-injectivity/occurrence lemma for `σ` that Foundation
does not expose (queued infrastructure).  Its side condition, that `σ` actually mentions its
argument, *is* discharged for this schema by
`universalHaltingSchema_not_argument_insensitive`, so the full syntactic separation is true —
merely unavailable at the current substrate.

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

/-- **The `thm:halts`/`thm:loops` claim family, over the paper's own deductive process.**

The positive obligation is discharged by Σ₁-completeness at the *universal* schema; the
`def:ec` obligation is discharged internally by `schemaArgClaimSentence_bigSentenceCodes` at
the compact argument name, and that is what `hm` and `hi` are consumed by.

Kind `C` (composition).  Provenance: (a) derived in-project; (b) Foundation citation —
`codeOfREPred` and `sigma_one_completeness` (through `re_complete_mp`).  The paper nodes are
carried by the endpoints that consume it, not by this constructor. -/
noncomputable def representedHaltingClaims [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗥₀ ⪯ T]
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

variable [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗥₀ ⪯ T]

/-- **Learning of Halting Patterns** over the paper's theorem process.  `hm` and `hi` are the
paper's own e.c. classes, metered by *write-out*: tex:1931-1933 asks that the source of `mₙ`
be writable in time polynomial in `n`, and a poly-time writer emits polynomially many
symbols, so an `n`-digit description with an exponential Gödel code is admissible and `⟨x⟩`
is a sequence of bitstrings.  Strictly wider than the whole-value pair this once took — see
`digitMachineCodes_nest_not_polyMachineCodes` and `bigDigits_two_pow_not_polyNatCodes`.
*Residual hypothesis (disclosed).*  `[𝗜𝚺₁ ⪯ T]` is a strengthening beyond the paper,
which assumes only that `Θ` is consistent, c.e. and represents computations; it is needed
solely so that provability in `T` is recursively enumerable through Foundation's internal
provability predicate, and is scheduled for removal.  `[T.Δ₁]` is the second strengthening:
it asks for a Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e.
theory has a deductively equivalent Δ₁ axiomatization, so the theorems transfer; that
reduction is not formalized here.
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
*Residual hypothesis (disclosed).*  `[𝗜𝚺₁ ⪯ T]` is a strengthening beyond the paper,
which assumes only that `Θ` is consistent, c.e. and represents computations; it is needed
solely so that provability in `T` is recursively enumerable through Foundation's internal
provability predicate, and is scheduled for removal.  `[T.Δ₁]` is the second strengthening:
it asks for a Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e.
theory has a deductively equivalent Δ₁ axiomatization, so the theorems transfer; that
reduction is not formalized here.
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
*Residual hypothesis (disclosed).*  `[𝗜𝚺₁ ⪯ T]` is a strengthening beyond the paper,
which assumes only that `Θ` is consistent, c.e. and represents computations; it is needed
solely so that provability in `T` is recursively enumerable through Foundation's internal
provability predicate, and is scheduled for removal.  `[T.Δ₁]` is the second strengthening:
it asks for a Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e.
theory has a deductively equivalent Δ₁ axiomatization, so the theorems transfer; that
reduction is not formalized here.
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
*Residual hypothesis (disclosed).*  `[𝗜𝚺₁ ⪯ T]` is a strengthening beyond the paper,
which assumes only that `Θ` is consistent, c.e. and represents computations; it is needed
solely so that provability in `T` is recursively enumerable through Foundation's internal
provability predicate, and is scheduled for removal.  `[T.Δ₁]` is the second strengthening:
it asks for a Δ₁ axiom set where the paper assumes only c.e.  By Craig's trick every c.e.
theory has a deductively equivalent Δ₁ axiomatization, so the theorems transfer; that
reduction is not formalized here.
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

#print axioms representedClaimSentence_bigSentenceCodes
#print axioms representedBoundedClaims
#print axioms representedBoundedHaltingClaims
#print axioms representedDecidableClaimsOfComputation
#print axioms lic_belief_finitistic_consistency_ofComputation
#print axioms lic_belief_stronger_theory_consistency_ofComputation
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

end LogicalInduction
