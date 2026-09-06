import LogicalInduction.Construction.LUV.ArithmeticSource
import LogicalInduction.Framework.Theory.RepresentsComputations

/-!
# Substituted closed-term instances are token-metered emittable

This module renders the `def:ec` (tex:753) emission certificate for the represented claim
families: writing a closed term into a fixed arithmetic schema is token-metered emittable,
for an arbitrary and Lean-opaque schema.  It supports `thm:halts`, `thm:loops`,
`thm:dontwait` and `thm:incons`; it is not itself a paper node.

The premise it discharges is the paper's §2 representability hypothesis (tex:600-606),
which hands a two-variable arithmetic formula `γ_f` about which nothing is known — at the
Lean level a concrete but entirely opaque `Semiformula` value, possibly obtained through
`Classical.choice`.  Downstream the paper writes a closed term naming the argument into
its first slot and asks that the resulting one-variable family be efficiently written out.

The main results are `polyArithmeticFormulaSeq_subst_arg` (two-variable schema) and
`polyArithmeticFormulaSeq_schemaArgBody` (one-variable schema), each for **every**
closed-term family `τ` whose own symbol runs the caller certifies by the parameter `henc`,
together with the sentence-class corollaries `bigSentenceCodes_reprArgClaim` and
`bigSentenceCodes_schemaArgClaim`, which
`Construction/Knowledge/Endpoints.lean` consumes.

The substituted term family is a *parameter* rather than the day numeral, so that one
theorem serves both the unary day numeral and a compact `binNumeral`
(`Construction/LUV/SourceCodec.lean`) naming a packed (machine source, input) pair.  That is the
route by which a public claim atom names the machine and input it is about, as the paper's
own sentences do (tex:606, tex:614), while staying inside the paper's write-out classes
`DigitMachineCodes` / `BigDigits`.

Hiding the varying data inside the schema is not a legitimate alternative: a
`codeOfREPred` schema depends only on the extension of the predicate it codes, so such a
claim family collapses to a constant family as soon as an endpoint's hypothesis pins that
extension, and the sentence then names no machine at all.

The proof needs no computability, decidability, or syntactic inspection of `γ`, and none
is available.  What makes it go through is that a *fixed* formula's symbol list is a fixed
skeleton with copies of the substituted term's run at finitely many fixed positions, and
`PolySegStream` is already closed under exactly the operations that build such a skeleton:
`PolySegStream.constList` accepts any fixed list however obtained, `PolySegStream.append`
glues, and `henc` emits the substituted run.  The skeleton is assembled by ordinary
structural recursion on the `Semiformula` *value*, to which `Classical.choice` is
irrelevant.

The de Bruijn bookkeeping under `∀⁰`/`∃⁰` is carried by the invariant `GoodRew`: every
source bound variable goes to the substituted closed term or to a bound variable.  Passing
a quantifier replaces `ω` by `Rew.q ω`, which sends `#0 ↦ #0` and
`#i.succ ↦ Rew.bShift (ω #i)`; `Rew.bShift` fixes any closed operator constant
(Foundation's `@[simp] Rew.const`) and shifts a bound variable to a bound variable, so the
invariant survives (`GoodRew.q`).  This is also why `henc` is quantified over the arity:
the induction re-enters at depth `l + 1` under a quantifier.

The biconditional closure is taken on the **source** language, not on
`PolyArithmeticFormulaSeq`: `⟺` is a primitive of the paper's syntax (tex:560) and only a
duplicating macro in Foundation's normal form (`dd:nnf`).

The vacuous `∃⁰` wrapper is deliberate: `paperPrimeDecompose` contracts a whole sentence
to a single prime only at an `.exs` head, and a `codeOfREPred` schema is chosen by
`Classical.epsilon`, so its head constructor is unreachable.
`provable_schemaDayClaim_iff` (`Construction/Knowledge/Endpoints.lean`) proves the wrapper changes
nothing.

The day-numeral families (`polyArithmeticFormulaSeq_subst_numeral`, `reprBodySource`,
`schemaDaySource` and their companions) are the numeral instance of the argument-term
route, with `schemaDayBody_eq_arg` recording that the day form *is* the argument form at
the day numeral; the certificate path the endpoints consume is the argument-term family.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## The unary numeral block

Foundation's `Semiterm.Operator.numeral` is unary — the numeral for `v` is a left-nested
fold of `one` under `add` — so its symbol encoding is two constant-tag runs whose lengths
are `v - 1` and `v`, and the zero numeral is the bare `zero` tag.  That is the shape
`PolySegStream.repeatTag` emits, which is why the *day* numeral costs polynomially many
tokens rather than constantly many.

The unary cost is a Foundation artifact and not the paper's notation — the paper fixes no
numeral notation and writes numerals positionally (tex:614, tex:757) — which is why nothing
below is tied to it: a value too large to name in unary is named by `binNumeral` instead,
and the general lemmas take whichever certificate the caller has. -/

/-- Symbol list of Foundation's unary numeral for `v`, zero included. -/
private def numeralEnc (v : ℕ) : List ℕ :=
  if v = 0 then [5] else List.replicate (v - 1) 7 ++ List.replicate v 6

/-- Kind `P` (proved).  Provenance: (a) derived in-project from
`encodeArithmeticTermSymbols_numeral`. -/
private lemma encodeArithmeticTermSymbols_numeralConst {k : ℕ} (v : ℕ) :
    encodeArithmeticTermSymbols
      ((Semiterm.Operator.numeral ℒₒᵣ v).const : ArithmeticSemiterm ℕ k) =
      numeralEnc v := by
  by_cases h : v = 0
  · subst h; rfl
  · rw [numeralEnc, if_neg h, encodeArithmeticTermSymbols_numeral v h]

/-- Numerals of a poly-fueled value stream are emittable, zero included: the two tag runs
are `repeatTag` blocks, and the zero case is selected by the same `ifZero` dispatch the
runtime uses.

Kind `P` (proved).  Provenance: (a) derived in-project. -/
private lemma numeralEnc_polySegStream {cv : Nat.Partrec.Code} {v : ℕ → ℕ}
    (hv : PolyFueled cv v) : PolySegStream (fun n => numeralEnc (v n)) := by
  have hpred : PolyFueled _ (fun n => v n - 1) :=
    (subc_polyFueled.comp (hv.pair (PolyFueled.const 1))).of_eq fun n => by
      simp only [Nat.unpair_pair]
  have hpos : PolySegStream (fun n => List.replicate (v n - 1) 7 ++
      List.replicate (v n) 6) :=
    (PolySegStream.repeatTag 7 hpred).append (PolySegStream.repeatTag 6 hv)
  refine ((PolySegStream.constList [5]).ifZero hpos hv).of_eq fun n => ?_
  by_cases h : v n = 0
  · rw [if_pos h, numeralEnc, if_pos h]
  · rw [if_neg h, numeralEnc, if_neg h]

/-- The day-numeral instance of the emission hypothesis the general lemmas below take:
the unary numeral for `n`, at every arity.

Kind `C` (composition).  Provenance: (a) derived in-project. -/
private lemma polySegStream_numeralConst (m : ℕ) :
    PolySegStream (fun n => encodeArithmeticTermSymbols
      ((Semiterm.Operator.numeral ℒₒᵣ n).const : ArithmeticSemiterm ℕ m)) :=
  (numeralEnc_polySegStream PolyFueled.id).of_eq fun n =>
    (encodeArithmeticTermSymbols_numeralConst (k := m) n).symm

/-! ## The substitution invariant

`GoodRew τ ω` says the family of rewritings `ω` writes the closed term `τ n` or a bound
variable into every source slot — nothing else.  It is exactly what the encoder needs: a
`τ`-slot contributes the run `henc` certifies, a bound-variable slot contributes a fixed
list, and no slot can contribute anything that grows in an uncontrolled way. -/

/-- Every source bound variable is sent to the substituted closed term or to a bound
variable. -/
private def GoodRew {k l : ℕ} (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (ω : ℕ → Rew ℒₒᵣ Empty k ℕ l) : Prop :=
  ∀ i : Fin k,
    (∀ n, ω n (Semiterm.bvar i) = ((τ n).const : ArithmeticSemiterm ℕ l)) ∨
    (∃ j : Fin l, ∀ n, ω n (Semiterm.bvar i) = Semiterm.bvar j)

/-- The invariant survives a quantifier.  `Rew.q ω` fixes `#0` and sends `#i.succ` to
`Rew.bShift (ω #i)`; `Rew.bShift` leaves any closed operator constant alone and carries a
bound variable to a bound variable.

Kind `P` (proved).  Provenance: (b) Foundation citations — `Rew.q_bvar_zero`,
`Rew.q_bvar_succ`, `Rew.const`. -/
private lemma GoodRew.q {k l : ℕ} {τ : ℕ → Semiterm.Const ℒₒᵣ}
    {ω : ℕ → Rew ℒₒᵣ Empty k ℕ l} (hω : GoodRew τ ω) :
    GoodRew τ (fun n => (ω n).q) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact Or.inr ⟨0, fun n => by simp⟩
  · intro i'
    rcases hω i' with h | ⟨j, hj⟩
    · exact Or.inl fun n => by
        show Rew.q (ω n) (Semiterm.bvar i'.succ) = _
        rw [Rew.q_bvar_succ, h n]; simp
    · exact Or.inr ⟨j.succ, fun n => by
        show Rew.q (ω n) (Semiterm.bvar i'.succ) = _
        rw [Rew.q_bvar_succ, hj n]; simp⟩

/-! ## The structural induction

Both inductions run over the *value* of the Foundation syntax tree.  They never decide
anything about it, so an opaque `γ` is as admissible as a literal one. -/

/-- Term half: a good substitution instance of a fixed closed-variable term is emittable.

Kind `P` (proved).  Provenance: (a) derived in-project. -/
private lemma polySegStream_term {k l : ℕ} {τ : ℕ → Semiterm.Const ℒₒᵣ}
    (henc : ∀ m : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ m)))
    {ω : ℕ → Rew ℒₒᵣ Empty k ℕ l} (hω : GoodRew τ ω)
    (t : Semiterm ℒₒᵣ Empty k) :
    PolySegStream (fun n => encodeArithmeticTermSymbols (ω n t)) := by
  induction t with
  | bvar x =>
      rcases hω x with h | ⟨j, hj⟩
      · exact (henc l).of_eq fun n => by rw [h n]
      · exact (PolySegStream.constList
          (encodeArithmeticTermSymbols (Semiterm.bvar j : ArithmeticSemiterm ℕ l))).of_eq
            fun n => by rw [hj n]
  | fvar x => exact x.elim
  | func f v ih =>
      cases f with
      | zero =>
          exact (PolySegStream.constList [5]).of_eq fun n => by
            simp only [Rew.func]; rfl
      | one =>
          exact (PolySegStream.constList [6]).of_eq fun n => by
            simp only [Rew.func]; rfl
      | add =>
          exact (((PolySegStream.constList [7]).append (ih 0)).append (ih 1)).of_eq
            fun n => by simp [Rew.func, encodeArithmeticTermSymbols]
      | mul =>
          exact (((PolySegStream.constList [8]).append (ih 0)).append (ih 1)).of_eq
            fun n => by simp [Rew.func, encodeArithmeticTermSymbols]

/-- Formula half: a good substitution instance of a fixed sentence-schema is emittable.
Generalized over the target depth `l` and the substitution `ω`, which is what lets the
quantifier cases re-enter at `Rew.q` — and why `henc` must hold at every arity.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`Semiformula.rec'`, `Rewriting.app_all`, `Rewriting.app_exs`. -/
private lemma polySegStream_formula {k : ℕ} (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ m : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ m)))
    (φ : Semiformula ℒₒᵣ Empty k) :
    ∀ (l : ℕ) (ω : ℕ → Rew ℒₒᵣ Empty k ℕ l), GoodRew τ ω →
      PolySegStream (fun n => encodeArithmeticFormulaSymbols ((ω n) ▹ φ)) := by
  induction φ using Semiformula.rec' with
  | hverum =>
      intro l ω _
      exact (PolySegStream.constList [9]).of_eq fun n => rfl
  | hfalsum =>
      intro l ω _
      exact (PolySegStream.constList [10]).of_eq fun n => rfl
  | hrel r v =>
      intro l ω hω
      cases r with
      | eq =>
          exact (((PolySegStream.constList [11]).append
            (polySegStream_term henc hω (v 0))).append
              (polySegStream_term henc hω (v 1))).of_eq fun n => by
                simp [encodeArithmeticFormulaSymbols]
      | lt =>
          exact (((PolySegStream.constList [13]).append
            (polySegStream_term henc hω (v 0))).append
              (polySegStream_term henc hω (v 1))).of_eq fun n => by
                simp [encodeArithmeticFormulaSymbols]
  | hnrel r v =>
      intro l ω hω
      cases r with
      | eq =>
          exact (((PolySegStream.constList [12]).append
            (polySegStream_term henc hω (v 0))).append
              (polySegStream_term henc hω (v 1))).of_eq fun n => by
                simp [encodeArithmeticFormulaSymbols]
      | lt =>
          exact (((PolySegStream.constList [14]).append
            (polySegStream_term henc hω (v 0))).append
              (polySegStream_term henc hω (v 1))).of_eq fun n => by
                simp [encodeArithmeticFormulaSymbols]
  | hand φ ψ ihφ ihψ =>
      intro l ω hω
      exact (((PolySegStream.constList [15]).append (ihφ l ω hω)).append
        (ihψ l ω hω)).of_eq fun n => by simp [encodeArithmeticFormulaSymbols]
  | hor φ ψ ihφ ihψ =>
      intro l ω hω
      exact (((PolySegStream.constList [16]).append (ihφ l ω hω)).append
        (ihψ l ω hω)).of_eq fun n => by simp [encodeArithmeticFormulaSymbols]
  | hall φ ih =>
      intro l ω hω
      exact ((PolySegStream.constList [17]).append
        (ih (l + 1) (fun n => (ω n).q) hω.q)).of_eq fun n => by
          simp [encodeArithmeticFormulaSymbols]
  | hexs φ ih =>
      intro l ω hω
      exact ((PolySegStream.constList [18]).append
        (ih (l + 1) (fun n => (ω n).q) hω.q)).of_eq fun n => by
          simp [encodeArithmeticFormulaSymbols]

/-! ## The paper-facing families -/

/-- **Writing an emittable closed term into a fixed two-variable formula is emittable.**

For an arbitrary `γ` — including one produced by the representability hypothesis, hence
Lean-opaque and possibly `Classical.choice`-obtained — and an arbitrary closed-term family
`τ` whose symbol runs are certified by `henc`, the family `n ↦ γ(τ n, ν)` is token-metered
emittable.  The cost is the fixed skeleton of `γ` plus one copy of `τ n`'s run for each of
the finitely many occurrences of the substituted slot.

Kind `P` (proved).  Provenance: (a) derived in-project from `polySegStream_formula`. -/
lemma polyArithmeticFormulaSeq_subst_arg (γ : ArithmeticSemisentence 2)
    (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ l : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))) :
    PolyArithmeticFormulaSeq (fun n : ℕ =>
      ((Semiformula.subst γ ![(τ n).const, #0] : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1)) := by
  have hgood : GoodRew τ (fun n : ℕ =>
      (Rew.emb.comp (Rew.subst ![((τ n).const : Semiterm ℒₒᵣ Empty 1), Semiterm.bvar 0])
        : Rew ℒₒᵣ Empty 2 ℕ 1)) := by
    intro i
    fin_cases i
    · exact Or.inl fun n => by simp [Rew.comp_app]
    · exact Or.inr ⟨0, fun n => by simp [Rew.comp_app]⟩
  refine (polySegStream_formula τ henc γ 1 _ hgood).of_eq fun n => ?_
  refine congrArg encodeArithmeticFormulaSymbols ?_
  simp only [Semiformula.subst, TransitiveRewriting.comp_app]

/-- **Writing the day numeral into a fixed two-variable formula is emittable.**  The
day-numeral instance of `polyArithmeticFormulaSeq_subst_arg`: the substituted run is the
unary numeral block, of length `2n - 1`.

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma polyArithmeticFormulaSeq_subst_numeral (γ : ArithmeticSemisentence 2) :
    PolyArithmeticFormulaSeq (fun n : ℕ =>
      ((Semiformula.subst γ ![‘↑n’, #0] : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1)) :=
  polyArithmeticFormulaSeq_subst_arg γ (fun n => Semiterm.Operator.numeral ℒₒᵣ n)
    polySegStream_numeralConst

/-! ## The biconditional closure on the source language

The corollary this file is *for* is `BigSentenceCodes (representedClaimSentence γ)`, the
last hypothesis of `representedBoundedClaims` in `Construction/Knowledge/Endpoints.lean`.

It is discharged on the **source** language (`Construction/LUV/ArithmeticSource.lean`), not on the
normal-form-metered `PolyArithmeticFormulaSeq`.  That is not a convenience: `🡘` is a
*primitive* of the paper's syntax (tex:560) and only a duplicating macro in Foundation's
negation normal form, so metering the body `γ(τ n, ν) ⟺ ν = 0̄` after normal-form expansion
would charge the `γ`-instance twice and would need an exact-stream negation map on the
normal form.  On the source it is one `iff` node over two leaves, and the normal-form
expansion happens in the parser, off the emitted stream (`dd:nnf`).
-/

open ArithSource in
/-- The represented body `γ(t, ν) ⟺ ν = 0̄` as a paper source, at an arbitrary closed term
`t`: one `iff` node over the substituted `γ`-instance and the fixed value equation. -/
def reprArgBodySource (γ : ArithmeticSemisentence 2) (t : Semiterm.Const ℒₒᵣ) :
    ArithSource 1 :=
  .iff (.leaf ((Semiformula.subst γ ![t.const, #0] : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1))
    (.leaf (((“#0 = ↑(0 : ℕ)” : ArithmeticSemisentence 1)) : ArithmeticSemiformula ℕ 1))

/-- The day-`n` case: the term is the day numeral. -/
def reprBodySource (γ : ArithmeticSemisentence 2) (n : ℕ) : ArithSource 1 :=
  reprArgBodySource γ (Semiterm.Operator.numeral ℒₒᵣ n)

/-- The source compiles to the biconditional body at `t`.

Kind `P` (proved).  Provenance: (a) derived in-project. -/
lemma compile_reprArgBodySource (γ : ArithmeticSemisentence 2) (t : Semiterm.Const ℒₒᵣ) :
    ArithSource.compile (reprArgBodySource γ t) =
      (Rewriting.emb (Semiformula.subst γ ![t.const, #0] 🡘
        (“#0 = ↑(0 : ℕ)” : ArithmeticSemisentence 1)) : ArithmeticSemiformula ℕ 1) := by
  simp [reprArgBodySource, ArithSource.compile]

/-- The source compiles to exactly the proposition under the quantifier of `reprAll γ 0 n`.

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma compile_reprBodySource (γ : ArithmeticSemisentence 2) (n : ℕ) :
    ArithSource.compile (reprBodySource γ n) =
      (Rewriting.emb (reprBody γ 0 n) : ArithmeticSemiformula ℕ 1) := by
  simp [reprBodySource, reprArgBodySource, ArithSource.compile, reprBody]

/-- The whole claim body at `t`, quantified and negated, as a source of arity `0`: the
shape `paperPrimeSentence true` contracts on. -/
def reprArgClaimSource (γ : ArithmeticSemisentence 2) (t : Semiterm.Const ℒₒᵣ) :
    ArithSource 0 :=
  .exs (.not (reprArgBodySource γ t))

/-- The day-`n` case. -/
def reprClaimSource (γ : ArithmeticSemisentence 2) (n : ℕ) : ArithSource 0 :=
  reprArgClaimSource γ (Semiterm.Operator.numeral ℒₒᵣ n)

/-- The claim source compiles to the negated body under one existential. -/
lemma compile_reprArgClaimSource (γ : ArithmeticSemisentence 2)
    (t : Semiterm.Const ℒₒᵣ) :
    ArithSource.compile (reprArgClaimSource γ t) =
      Semiformula.exs (∼(Rewriting.emb (Semiformula.subst γ ![t.const, #0] 🡘
        (“#0 = ↑(0 : ℕ)” : ArithmeticSemisentence 1)) : ArithmeticSemiformula ℕ 1)) := by
  simp [reprArgClaimSource, ArithSource.compile, compile_reprArgBodySource]

/-- The day-numeral instance of `compile_reprArgClaimSource`. -/
lemma compile_reprClaimSource (γ : ArithmeticSemisentence 2) (n : ℕ) :
    ArithSource.compile (reprClaimSource γ n) =
      Semiformula.exs (∼(Rewriting.emb (reprBody γ 0 n) : ArithmeticSemiformula ℕ 1)) := by
  have hbody := compile_reprBodySource γ n
  simp only [reprBodySource] at hbody
  simp [reprClaimSource, reprArgClaimSource, ArithSource.compile, hbody]

/-- **The body family is source-metered emittable.**  The `γ`-instance leaf is
`polyArithmeticFormulaSeq_subst_arg`; the value equation is a fixed list; the `⟺` is one
token.

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma reprArgBodySource_polyArithmeticSourceSeq (γ : ArithmeticSemisentence 2)
    (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ l : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))) :
    PolyArithmeticSourceSeq (fun n => reprArgBodySource γ (τ n)) := by
  refine PolyArithmeticSourceSeq.iff ?_ ?_
  · exact PolyArithmeticSourceSeq.leaf (polyArithmeticFormulaSeq_subst_arg γ τ henc)
  · exact PolyArithmeticSourceSeq.leaf
      (PolySegStream.constList (encodeArithmeticFormulaSymbols
        (((“#0 = ↑(0 : ℕ)” : ArithmeticSemisentence 1)) : ArithmeticSemiformula ℕ 1)))

/-- The whole claim source is source-metered: the body, negated, under one `∃` node. -/
lemma reprArgClaimSource_polyArithmeticSourceSeq (γ : ArithmeticSemisentence 2)
    (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ l : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))) :
    PolyArithmeticSourceSeq (fun n => reprArgClaimSource γ (τ n)) :=
  (reprArgBodySource_polyArithmeticSourceSeq γ τ henc).not.exs

/-- The day-numeral instance of `reprArgBodySource_polyArithmeticSourceSeq`. -/
lemma reprBodySource_polyArithmeticSourceSeq (γ : ArithmeticSemisentence 2) :
    PolyArithmeticSourceSeq (reprBodySource γ) :=
  reprArgBodySource_polyArithmeticSourceSeq γ (fun n => Semiterm.Operator.numeral ℒₒᵣ n)
    polySegStream_numeralConst

/-- The day-numeral instance of `reprArgClaimSource_polyArithmeticSourceSeq`. -/
lemma reprClaimSource_polyArithmeticSourceSeq (γ : ArithmeticSemisentence 2) :
    PolyArithmeticSourceSeq (reprClaimSource γ) :=
  reprArgClaimSource_polyArithmeticSourceSeq γ (fun n => Semiterm.Operator.numeral ℒₒᵣ n)
    polySegStream_numeralConst

/-- **The emission certificate for the represented claim family, at an arbitrary
closed-term stream.**

For *every* `γ` — including one produced by `RepresentsComputations`, hence Lean-opaque and
possibly `Classical.choice`-obtained — and every closed-term family `τ` with an emission
certificate, the family of public claim atoms `γ(τ n, ν) ⟺ ν = 0̄` is in the paper's
`def:ec` sentence class.  Nothing is assumed about `γ`: the emitter writes a fixed
skeleton, one copy of `τ n`'s run per substituted slot, and the framing of a single source
prime block.

Kind `C` (composition).  Provenance: (a) derived in-project from
`polyArithmeticFormulaSeq_subst_arg` and `parseRpn_structuredPaperSourcePrimeBlock`. -/
lemma rpnSentenceCodes_reprArgClaim (γ : ArithmeticSemisentence 2)
    (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ l : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))) :
    RpnSentenceCodes (fun n => paperPrimeSentence true
      (Semiformula.exs (∼(Rewriting.emb
        (Semiformula.subst γ ![(τ n).const, #0] 🡘
          (“#0 = ↑(0 : ℕ)” : ArithmeticSemisentence 1)) :
            ArithmeticSemiformula ℕ 1)))) := by
  refine ⟨fun n => structuredPaperSourcePrimeBlock true (reprArgClaimSource γ (τ n)),
    structuredPaperSourcePrimeBlock_polySegStream true _
      (reprArgClaimSource_polyArithmeticSourceSeq γ τ henc), fun n => ?_⟩
  have hlen : 1 ≤
      (structuredPaperSourcePrimeBlock true (reprArgClaimSource γ (τ n))).length :=
    structuredPaperSourcePrimeBlock_length_pos true _
  have := parseRpn_structuredPaperSourcePrimeBlock true (reprArgClaimSource γ (τ n)) []
    (fuel := (structuredPaperSourcePrimeBlock true (reprArgClaimSource γ (τ n))).length)
    hlen
  simpa [compile_reprArgClaimSource] using this

/-- **The write-out certificate for the represented claim family at an arbitrary
closed-term stream.**

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma bigSentenceCodes_reprArgClaim (γ : ArithmeticSemisentence 2)
    (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ l : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))) :
    BigSentenceCodes (fun n => paperPrimeSentence true
      (Semiformula.exs (∼(Rewriting.emb
        (Semiformula.subst γ ![(τ n).const, #0] 🡘
          (“#0 = ↑(0 : ℕ)” : ArithmeticSemisentence 1)) : ArithmeticSemiformula ℕ 1)))) :=
  BigSentenceCodes.ofRpnSentenceCodes (rpnSentenceCodes_reprArgClaim γ τ henc)

/-- The day-numeral instance.

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma rpnSentenceCodes_reprClaim (γ : ArithmeticSemisentence 2) :
    RpnSentenceCodes (fun n => paperPrimeSentence true
      (Semiformula.exs (∼(Rewriting.emb (reprBody γ 0 n) :
        ArithmeticSemiformula ℕ 1)))) :=
  rpnSentenceCodes_reprArgClaim γ (fun n => Semiterm.Operator.numeral ℒₒᵣ n)
    polySegStream_numeralConst

/-- The day-numeral instance of `bigSentenceCodes_reprArgClaim`. -/
lemma bigSentenceCodes_reprClaim (γ : ArithmeticSemisentence 2) :
    BigSentenceCodes (fun n => paperPrimeSentence true
      (Semiformula.exs (∼(Rewriting.emb (reprBody γ 0 n) : ArithmeticSemiformula ℕ 1)))) :=
  BigSentenceCodes.ofRpnSentenceCodes (rpnSentenceCodes_reprClaim γ)

/-! ## The instance family of a fixed one-variable schema

`thm:halts` and `thm:loops` name the stage-`n` claim by writing a closed term into one
fixed Σ₁ schema, exactly as `thm:dontwait` does.  The schema is fixed and *universal* — one
represented object for the whole family — and everything that varies with `n` is written
into the sentence, as the substituted term `τ n`, so that the sentence names the machine
and input it is about.  That argument is a packed pair `(machine source, input)`, or a
triple with a day when a horizon is needed; the day is at most one component of it, and for
`thm:halts`/`thm:loops` it does not appear at all.  Hence the `Arg` names below: only the
`polyArithmeticFormulaSeq_schemaDayBody` / `bigSentenceCodes_schemaDayClaim` instances
below them are genuinely about the day numeral.

Writing that data in is what `polyArithmeticFormulaSeq_schemaArgBody` charges for, and
the charge is paid by the caller's `henc`.  Under Foundation's unary
`Semiterm.Operator.numeral` a term naming a value `v` costs `v` tokens, so only a
poly-fueled value stream can be substituted that way; under the compact `binNumeral` it
costs `O(log v)` — `O(|source| + |input digits|)` for a machine/input pair — which is
exactly what the paper's write-out classes `DigitMachineCodes`/`BigDigits` bound
polynomially.  The unary cost is a Foundation artifact and not the paper's notation: the
paper fixes no numeral notation and writes numerals positionally (tex:614, tex:757).

Hiding the varying data *inside* the schema instead is not a legitimate alternative.  A
`codeOfREPred` schema depends only on the extension of the predicate it codes, so a claim
family built that way collapses to a constant family as soon as an endpoint's own
hypothesis pins that extension — and the sentence then names no machine at all.  That is
why the term family is a parameter here.

The `∃⁰` wrapper is vacuous, and deliberate.  `paperPrimeDecompose` contracts a whole
sentence to a single prime only at an `.exs` head (and its `.all` negation); a
`codeOfREPred` schema is chosen by `Classical.epsilon`, so its head constructor is
unreachable and no equation for its decomposition can be written.  Wrapping in one
existential that binds nothing puts a head on the claim that the decomposition can see,
without changing what the claim says — `provable_schemaDayClaim_iff`
(`Construction/Knowledge/Endpoints.lean`) is the proof that it does not. -/

/-- The instance of a fixed one-variable schema at a closed term, in a context that still
carries one (unused) bound variable — the body of the vacuous existential. -/
def schemaArgBody (σ : ArithmeticSemisentence 1) (t : Semiterm.Const ℒₒᵣ) :
    ArithmeticSemisentence 1 :=
  Semiformula.subst σ ![(t.const : ArithmeticSemiterm Empty 1)]

/-- The day-`n` instance of a fixed one-variable schema. -/
def schemaDayBody (σ : ArithmeticSemisentence 1) (n : ℕ) : ArithmeticSemisentence 1 :=
  Semiformula.subst σ ![(‘↑n’ : ArithmeticSemiterm Empty 1)]

/-- The day instance is the closed-term instance at the day numeral — definitionally, since
Foundation's `‘↑n’` *is* `(Semiterm.Operator.numeral ℒₒᵣ n).const`.  Stated so that
`schemaDayBody` keeps unfolding to a bare `Semiformula.subst` for downstream `simp` sets.

Kind `P` (proved).  Provenance: (a) derived in-project. -/
lemma schemaDayBody_eq_arg (σ : ArithmeticSemisentence 1) (n : ℕ) :
    schemaDayBody σ n = schemaArgBody σ (Semiterm.Operator.numeral ℒₒᵣ n) := rfl

/-- **Writing an emittable closed term into a fixed one-variable schema is emittable.**
The one-variable analogue of `polyArithmeticFormulaSeq_subst_arg`, and equally indifferent
to what `σ` is: the emitter writes `σ`'s fixed skeleton plus one copy of `τ n`'s run per
substituted slot.

Kind `P` (proved).  Provenance: (a) derived in-project from `polySegStream_formula`. -/
lemma polyArithmeticFormulaSeq_schemaArgBody (σ : ArithmeticSemisentence 1)
    (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ l : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))) :
    PolyArithmeticFormulaSeq (fun n : ℕ =>
      ((schemaArgBody σ (τ n) : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1)) := by
  have hgood : GoodRew τ (fun n : ℕ =>
      (Rew.emb.comp (Rew.subst ![((τ n).const : Semiterm ℒₒᵣ Empty 1)])
        : Rew ℒₒᵣ Empty 1 ℕ 1)) := by
    intro i
    fin_cases i
    · exact Or.inl fun n => by simp [Rew.comp_app]
  refine (polySegStream_formula τ henc σ 1 _ hgood).of_eq fun n => ?_
  refine congrArg encodeArithmeticFormulaSymbols ?_
  simp only [schemaArgBody, Semiformula.subst, TransitiveRewriting.comp_app]

/-- **Writing the day numeral into a fixed one-variable schema is emittable.**

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma polyArithmeticFormulaSeq_schemaDayBody (σ : ArithmeticSemisentence 1) :
    PolyArithmeticFormulaSeq (fun n : ℕ =>
      ((schemaDayBody σ n : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)) :=
  polyArithmeticFormulaSeq_schemaArgBody σ (fun n => Semiterm.Operator.numeral ℒₒᵣ n)
    polySegStream_numeralConst

open ArithSource in
/-- The claim at a closed term as a paper source: one `∃` node over the substituted
schema. -/
def schemaArgSource (σ : ArithmeticSemisentence 1) (t : Semiterm.Const ℒₒᵣ) :
    ArithSource 0 :=
  .exs (.leaf ((schemaArgBody σ t : ArithmeticSemisentence 1) :
    ArithmeticSemiformula ℕ 1))

/-- The day-`n` case. -/
def schemaDaySource (σ : ArithmeticSemisentence 1) (n : ℕ) : ArithSource 0 :=
  schemaArgSource σ (Semiterm.Operator.numeral ℒₒᵣ n)

/-- The claim source at a closed term compiles to the vacuously quantified schema
instance. -/
lemma compile_schemaArgSource (σ : ArithmeticSemisentence 1)
    (t : Semiterm.Const ℒₒᵣ) :
    ArithSource.compile (schemaArgSource σ t) =
      Semiformula.exs (Rewriting.emb (schemaArgBody σ t) :
        ArithmeticSemiformula ℕ 1) := by
  simp [schemaArgSource, ArithSource.compile]

/-- The day-numeral instance of `compile_schemaArgSource`. -/
lemma compile_schemaDaySource (σ : ArithmeticSemisentence 1) (n : ℕ) :
    ArithSource.compile (schemaDaySource σ n) =
      Semiformula.exs (Rewriting.emb (schemaDayBody σ n) : ArithmeticSemiformula ℕ 1) :=
  compile_schemaArgSource σ (Semiterm.Operator.numeral ℒₒᵣ n)

/-- The claim sources at a certified closed-term family are source-metered: one `∃` node
over the substituted schema leaf. -/
lemma schemaArgSource_polyArithmeticSourceSeq (σ : ArithmeticSemisentence 1)
    (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ l : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))) :
    PolyArithmeticSourceSeq (fun n => schemaArgSource σ (τ n)) :=
  (PolyArithmeticSourceSeq.leaf
    (polyArithmeticFormulaSeq_schemaArgBody σ τ henc)).exs

/-- The day-numeral instance of `schemaArgSource_polyArithmeticSourceSeq`. -/
lemma schemaDaySource_polyArithmeticSourceSeq (σ : ArithmeticSemisentence 1) :
    PolyArithmeticSourceSeq (schemaDaySource σ) :=
  schemaArgSource_polyArithmeticSourceSeq σ (fun n => Semiterm.Operator.numeral ℒₒᵣ n)
    polySegStream_numeralConst

/-- **The emission certificate for the schema-instance claim family at an arbitrary
closed-term stream.**  For *every* `σ` — including a `codeOfREPred` schema, hence
Lean-opaque and `Classical.epsilon`-obtained — and every closed-term family `τ` with an
emission certificate, the family of public claim atoms is in the paper's `def:ec` sentence
class.

Kind `C` (composition).  Provenance: (a) derived in-project from
`polyArithmeticFormulaSeq_schemaArgBody` and
`parseRpn_structuredPaperSourcePrimeBlock`. -/
lemma rpnSentenceCodes_schemaArgClaim (σ : ArithmeticSemisentence 1)
    (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ l : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))) :
    RpnSentenceCodes (fun n => paperPrimeSentence true
      (Semiformula.exs (Rewriting.emb (schemaArgBody σ (τ n)) :
        ArithmeticSemiformula ℕ 1))) := by
  refine ⟨fun n => structuredPaperSourcePrimeBlock true (schemaArgSource σ (τ n)),
    structuredPaperSourcePrimeBlock_polySegStream true _
      (schemaArgSource_polyArithmeticSourceSeq σ τ henc), fun n => ?_⟩
  have hlen : 1 ≤
      (structuredPaperSourcePrimeBlock true (schemaArgSource σ (τ n))).length :=
    structuredPaperSourcePrimeBlock_length_pos true _
  have := parseRpn_structuredPaperSourcePrimeBlock true (schemaArgSource σ (τ n)) []
    (fuel := (structuredPaperSourcePrimeBlock true (schemaArgSource σ (τ n))).length)
    hlen
  simpa [compile_schemaArgSource] using this

/-- **The write-out certificate for the schema-instance claim family at an arbitrary
closed-term stream.**

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma bigSentenceCodes_schemaArgClaim (σ : ArithmeticSemisentence 1)
    (τ : ℕ → Semiterm.Const ℒₒᵣ)
    (henc : ∀ l : ℕ, PolySegStream (fun n =>
      encodeArithmeticTermSymbols ((τ n).const : ArithmeticSemiterm ℕ l))) :
    BigSentenceCodes (fun n => paperPrimeSentence true
      (Semiformula.exs (Rewriting.emb (schemaArgBody σ (τ n)) :
        ArithmeticSemiformula ℕ 1))) :=
  BigSentenceCodes.ofRpnSentenceCodes (rpnSentenceCodes_schemaArgClaim σ τ henc)

/-! ### The day-numeral instances

The day-numeral instances are the argument-term route at
`τ n := Semiterm.Operator.numeral ℒₒᵣ n`; `schemaDayBody_eq_arg` records that they are
definitionally the same.  The claim families consume the argument-term form, because a
claim's argument is a compact `binNumeral` naming a packed (machine source, input) pair,
not a unary day numeral. -/

/-- The day-numeral instance.

Kind `C` (composition).  Provenance: (a) derived in-project. -/
lemma rpnSentenceCodes_schemaDayClaim (σ : ArithmeticSemisentence 1) :
    RpnSentenceCodes (fun n => paperPrimeSentence true
      (Semiformula.exs (Rewriting.emb (schemaDayBody σ n) :
        ArithmeticSemiformula ℕ 1))) :=
  rpnSentenceCodes_schemaArgClaim σ (fun n => Semiterm.Operator.numeral ℒₒᵣ n)
    polySegStream_numeralConst

/-- The day-numeral instance of `bigSentenceCodes_schemaArgClaim`. -/
lemma bigSentenceCodes_schemaDayClaim (σ : ArithmeticSemisentence 1) :
    BigSentenceCodes (fun n => paperPrimeSentence true
      (Semiformula.exs (Rewriting.emb (schemaDayBody σ n) : ArithmeticSemiformula ℕ 1))) :=
  BigSentenceCodes.ofRpnSentenceCodes (rpnSentenceCodes_schemaDayClaim σ)

end LogicalInduction
