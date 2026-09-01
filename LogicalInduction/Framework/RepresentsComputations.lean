/-
# The paper's standing assumption on the background theory: `Θ` represents computations

The paper (§2, "Representing computations", arXiv:1609.03543v5 lines 600–606) fixes one
standing hypothesis on the first-order background theory `Θ` used from §4.9 onward: that

> for every (total) computable function `f : ℕ⁺ → ℕ⁺` there exists a `Θ`-formula `γ_f` with
> two free variables such that for all `n, y ∈ ℕ⁺`,
> `y = f(n)` if and only if `Θ ⊢ ∀ν : γ_f(⌜n⌝, ν) ↔ ν = ⌜y⌝`.

This is the *representability theorem for computable functions*, taken as a hypothesis on
`Θ` rather than proved about a particular theory.  It is a purely **proof-theoretic**
condition: it says what `Θ` derives, not what is true.  In particular it is *not* a
semantic soundness assumption, and this development uses it in place of Σ₁-soundness
wherever the paper's own argument only needs the paper's own premise.

The paper notes (line 604) that the condition already forces `Θ` to be consistent;
`RepresentsComputations.consistent` below is that observation.

Because the assumption is an *existential* over `γ_f`, it supplies no computable map
`f ↦ ⌜γ_f⌝`.  Downstream users get, for each fixed total computable `f`, one fixed formula
and both literals over it.
-/
import Foundation.FirstOrder.Arithmetic.R0.Basic
import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
import Foundation.FirstOrder.Arithmetic.Schemata
import Foundation.Meta.ClProver
import Mathlib.Computability.Partrec
import Mathlib.Tactic.FinCases
import LogicalInduction.Framework.SubstOccurrence

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-- **The paper's standing assumption on `Θ` (`arXiv:1609.03543v5`, §2, lines 600–606).**

`T` *represents computations*: every total computable `f : ℕ → ℕ` has a two-variable
`T`-formula `γ_f` for which `T` proves, and only proves, the correct value graph in the
strong "unique value" form

`y = f n ↔ T ⊢ ∀ν, (γ_f(n̄, ν) ↔ ν = ȳ)`.

The paper writes `⌜f⌝(⌜n⌝)` for `γ_f(n̄, ν)` (line 606) and observes that this condition
already implies `T` is consistent (line 604; see `RepresentsComputations.consistent`).

Note what this is *not*: it is a condition on `T`'s derivations, with no reference to
truth in the standard model.  It is strictly weaker in kind than Σ₁-soundness, which is
what this development previously assumed and which the paper never assumes.

*Index-shift strengthening (disclosed).*  The quantifier here is over `f : ℕ → ℕ` and the
biconditional is asserted at **every** `y : ℕ`, including `y = 0`, where the paper's is over
`f : ℕ⁺ → ℕ⁺` and `n, y ∈ ℕ⁺`.  Day indexing throughout this development is `ℕ` from `0`
(the paper's is `ℕ⁺`), so this is the same inessential index shift applied to the premise
rather than to the conclusion: it asks `T` for slightly more than the paper does, and is
therefore a strengthening of the hypothesis on `T`, not a weakening of any theorem taking
it.  It is realized: the committed instances (`Construction/Witnesses/R0Representability.lean`,
at `𝗣𝗔⁻`, `𝗜𝚺₁`, `𝗣𝗔`) satisfy the `ℕ`-indexed form, so no endpoint's premise set is
narrowed by the shift. -/
class RepresentsComputations (T : ArithmeticTheory) : Prop where
  repr : ∀ f : ℕ → ℕ, Computable f → ∃ γ : ArithmeticSemisentence 2,
    ∀ n y : ℕ, y = f n ↔
      T ⊢ (∀⁰ (Semiformula.subst γ ![‘↑n’, #0] 🡘 (“#0 = ↑y” : ArithmeticSemisentence 1)))

/-! ## The two literals over a represented formula

Both directions are derived from the interface alone, under `[𝗥₀ ⪯ T]` for the numeral
apparatus.  Neither uses soundness or any semantic hypothesis. -/

/-- Distinct numerals are provably distinct in any theory extending `𝗥₀`.

Kind `C` (composition).  Provenance: (b) Foundation citation — `R0.Ω₃`. -/
lemma numeral_ne_prov (T : ArithmeticTheory) [h : 𝗥₀ ⪯ T] (n m : ℕ) (hnm : n ≠ m) :
    T ⊢ (“↑n ≠ ↑m” : ArithmeticSentence) :=
  weakening h (Entailment.by_axm (R0.Ω₃ n m hnm))

/-- Reflexivity of equality at a numeral, from `𝗥₀`'s equality axioms.

Kind `C` (composition).  Provenance: (b) Foundation citations — `Theory.eqAxiom.refl`,
`R0.equal`, `Theory.Proof.specialize`. -/
lemma numeral_eq_refl_prov (T : ArithmeticTheory) [h : 𝗥₀ ⪯ T] (y : ℕ) :
    T ⊢ (“↑y = ↑y” : ArithmeticSentence) := by
  have hax : T ⊢ (“∀ x, x = x” : ArithmeticSentence) :=
    weakening h (Entailment.by_axm (R0.equal _ Theory.eqAxiom.refl))
  have := (LO.FirstOrder.Theory.Proof.specialize
    (T := T) (“#0 = #0” : ArithmeticSemisentence 1) ‘↑y’) ⨀ (by simpa using hax)
  simpa using this

/-- Substituting a numeral into a one-variable substitution instance of a two-variable
formula is the two-numeral substitution instance.

This is the composition lemma the literal derivations need; note that `congr`/`ext` do not
close it — the rewrite must go through `Rew.subst_comp_subst`. -/
lemma subst_subst_two (γ : ArithmeticSemisentence 2) (z y : ℕ) :
    (Semiformula.subst (Semiformula.subst γ ![‘↑z’, #0]) ![‘↑y’] : ArithmeticSentence)
      = Semiformula.subst γ ![‘↑z’, ‘↑y’] := by
  simp only [Semiformula.subst, ← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
  refine congrArg (fun v => Rewriting.app (Rew.subst v) γ) ?_
  funext i
  fin_cases i <;> simp

/-- The substitution instance of the representation body at a numeral: both sides of the
`🡘` substitute independently. -/
lemma subst_iff_numeral (γ : ArithmeticSemisentence 2) (z y w : ℕ) :
    ((Semiformula.subst γ ![‘↑z’, #0] 🡘 (“#0 = ↑y” : ArithmeticSemisentence 1)).subst
        ![(‘↑w’)] : ArithmeticSentence)
      = ((Semiformula.subst γ ![‘↑z’, ‘↑w’] : ArithmeticSentence) 🡘
        (“↑w = ↑y” : ArithmeticSentence)) := by
  simp only [Semiformula.subst, LogicalConnective.HomClass.map_iff]
  congr 1
  · exact subst_subst_two γ z w
  · simp

/-- **The positive literal.**  From the representation at the *correct* value, `T` proves
the value instance of `γ`.

Kind `P` (proved).  Provenance: (a) derived in-project from `RepresentsComputations`;
(b) Foundation `Theory.Proof.specialize`. -/
lemma represents_proves (T : ArithmeticTheory) [𝗥₀ ⪯ T] (γ : ArithmeticSemisentence 2)
    (z y : ℕ)
    (hrep : T ⊢ (∀⁰ (Semiformula.subst γ ![‘↑z’, #0] 🡘
      (“#0 = ↑y” : ArithmeticSemisentence 1)))) :
    T ⊢ (Semiformula.subst γ ![‘↑z’, ‘↑y’] : ArithmeticSentence) := by
  have hinst := (LO.FirstOrder.Theory.Proof.specialize
    (T := T) (Semiformula.subst γ ![‘↑z’, #0] 🡘 (“#0 = ↑y” : ArithmeticSemisentence 1))
    ‘↑y’) ⨀ hrep
  have heq : T ⊢ (“↑y = ↑y” : ArithmeticSentence) := numeral_eq_refl_prov T y
  rw [subst_iff_numeral γ z y y] at hinst
  cl_prover [hinst, heq]

/-- **The negative literal.**  From the representation at the value `0`, `T` *refutes* the
value-`1` instance of the *same* formula.

This is the step that replaces Σ₁-soundness: previously a false decidable claim was
refutable only by moving to a second, complementary r.e. schema, since weak representation
gives nothing negative.  The paper's representability premise gives both literals over one
formula.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`R0.Ω₃` (via `numeral_ne_prov`) and `Theory.Proof.specialize`. -/
lemma represents_refutes (T : ArithmeticTheory) [𝗥₀ ⪯ T] (γ : ArithmeticSemisentence 2)
    (z : ℕ)
    (hrep : T ⊢ (∀⁰ (Semiformula.subst γ ![‘↑z’, #0] 🡘
      (“#0 = ↑(0:ℕ)” : ArithmeticSemisentence 1)))) :
    T ⊢ ∼(Semiformula.subst γ ![‘↑z’, ‘↑(1:ℕ)’] : ArithmeticSentence) := by
  have hinst := (LO.FirstOrder.Theory.Proof.specialize
    (T := T) (Semiformula.subst γ ![‘↑z’, #0] 🡘
      (“#0 = ↑(0:ℕ)” : ArithmeticSemisentence 1)) ‘↑(1:ℕ)’) ⨀ hrep
  have hne : T ⊢ (“↑(1:ℕ) ≠ ↑(0:ℕ)” : ArithmeticSentence) := numeral_ne_prov T 1 0 (by decide)
  rw [subst_iff_numeral γ z 0 1] at hinst
  cl_prover [hinst, hne]

/-- **The negative literal in the paper's `∀`-form.**  If `T` represents the value `1` at
`z`, it refutes the whole `∀ν (γ(z̄,ν) ↔ ν = 0̄)` sentence — the *same* sentence whose
positive form the representation at value `0` supplies.

This is the pair of literals the public claim family uses: one sentence, both literals,
neither of them semantic.

Kind `P` (proved).  Provenance: (a) derived in-project. -/
lemma represents_refutes_all (T : ArithmeticTheory) [𝗥₀ ⪯ T] (γ : ArithmeticSemisentence 2)
    (z : ℕ)
    (h1 : T ⊢ (∀⁰ (Semiformula.subst γ ![‘↑z’, #0] 🡘
      (“#0 = ↑(1:ℕ)” : ArithmeticSemisentence 1)))) :
    T ⊢ ∼(∀⁰ (Semiformula.subst γ ![‘↑z’, #0] 🡘
      (“#0 = ↑(0:ℕ)” : ArithmeticSemisentence 1))) := by
  have hpos : T ⊢ (Semiformula.subst γ ![‘↑z’, ‘↑(1:ℕ)’] : ArithmeticSentence) :=
    represents_proves T γ z 1 h1
  have hspec := LO.FirstOrder.Theory.Proof.specialize (T := T)
    (Semiformula.subst γ ![‘↑z’, #0] 🡘 (“#0 = ↑(0:ℕ)” : ArithmeticSemisentence 1)) ‘↑(1:ℕ)’
  rw [subst_iff_numeral γ z 0 1] at hspec
  have hne : T ⊢ (“↑(1:ℕ) ≠ ↑(0:ℕ)” : ArithmeticSentence) := numeral_ne_prov T 1 0 (by decide)
  cl_prover [hspec, hpos, hne]

/-! ## The claim sentence and its fixed schema

`reprAll γ y z` is the paper's `∀ν : γ(z̄, ν) ↔ ν = ȳ` — the sentence the public claim
families are named by.  As `z` varies this is the numeral-instance family of one *fixed*
`ArithmeticSemisentence 1`, which is what makes provability of the family recursively
enumerable by the existing fixed-schema machinery even though `γ` itself is supplied
existentially. -/

/-- The representation body at day `z` and value `y`: `γ(z̄, ν) ↔ ν = ȳ`. -/
def reprBody (γ : ArithmeticSemisentence 2) (y z : ℕ) : ArithmeticSemisentence 1 :=
  Semiformula.subst γ ![‘↑z’, #0] 🡘 (“#0 = ↑y” : ArithmeticSemisentence 1)

/-- The paper's `⌜f⌝(⌜z⌝) = ȳ`: `∀ν (γ(z̄, ν) ↔ ν = ȳ)`. -/
def reprAll (γ : ArithmeticSemisentence 2) (y z : ℕ) : ArithmeticSentence :=
  ∀⁰ (reprBody γ y z)

/-- The one-variable schema whose numeral instances are the `reprAll` family: the day slot
is left as the free variable `#1` under the quantifier. -/
def reprAllSchema (γ : ArithmeticSemisentence 2) (y : ℕ) : ArithmeticSemisentence 1 :=
  ∀⁰ (Semiformula.subst γ ![#1, #0] 🡘 (“#0 = ↑y” : ArithmeticSemisentence 2))

/-- **The family is a fixed schema's numeral instances.**

This is what lets `provable_instances_re` — which dovetails a *fixed* formula — enumerate
`{z | T ⊢ reprAll γ y z}` even though `γ` came from an existential and no computable map
`f ↦ ⌜γ_f⌝` is available.  The quantifier lift is `Rewriting.app_all` plus
`Rew.subst_comp_subst`; `congr`/`ext` do not close it. -/
lemma reprAllSchema_subst (γ : ArithmeticSemisentence 2) (y z : ℕ) :
    (Semiformula.subst (reprAllSchema γ y) ![‘↑z’] : ArithmeticSentence) = reprAll γ y z := by
  simp only [reprAllSchema, reprAll, reprBody, Semiformula.subst, Rewriting.app_all]
  refine congrArg Semiformula.all ?_
  simp only [LogicalConnective.HomClass.map_iff]
  congr 1
  · simp only [← TransitiveRewriting.comp_app, Rew.q_subst, Rew.subst_comp_subst]
    refine congrArg (fun v => Rewriting.app (Rew.subst v) γ) ?_
    funext i
    fin_cases i <;> simp
  · simp

/-- **The representation spec forces the representing formula to mention its argument slot,
as soon as the represented function is non-constant.**

If `γ` did not mention `#0`, substituting two different day numerals into it would give the
*same* formula, hence the same sentence `reprAll γ y z = reprAll γ y z'`, and the
representation biconditional read at `y = g z` would then force `g z = g z'`.

This is the general discharge of the occurrence side condition that
`representedClaimSentence_ne_of_const_ne`, `conClaimSentence_ne_of_day_ne` and the rest of
the syntactic-separation family take as a hypothesis.  It applies to **any** representing
formula obtained from `RepresentsComputations`, at any two arguments where the represented
function differs; the hypothesis is exactly that non-constancy, and it cannot be dropped —
for a constant `g` (a horizon that is constantly `0` makes `conRunValue` constant, for
instance) a `γ` ignoring `#0` really does represent `g` correctly.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citation —
`Semiformula.rew_eq_of_not_mentions` (`Framework/SubstOccurrence.lean`). -/
lemma mentions_zero_of_repr_ne {T : ArithmeticTheory} {g : ℕ → ℕ}
    (γ : ArithmeticSemisentence 2)
    (hγ : ∀ z y : ℕ, y = g z ↔ T ⊢ reprAll γ y z)
    {z z' : ℕ} (h : g z ≠ g z') :
    γ.Mentions 0 := by
  by_contra hmem
  refine h ?_
  have hsub : (Semiformula.subst γ ![‘↑z’, #0] : ArithmeticSemisentence 1)
      = Semiformula.subst γ ![‘↑z'’, #0] := by
    simp only [Semiformula.subst]
    refine Semiformula.rew_eq_of_not_mentions (k := 0) hmem ?_ (fun x => x.elim)
    intro x hx
    fin_cases x
    · simp at hx
    · simp
  have hall : reprAll γ (g z) z = reprAll γ (g z) z' := by
    simp only [reprAll, reprBody, hsub]
  exact (hγ z' (g z)).mpr (hall ▸ (hγ z (g z)).mp rfl)

/-! ## Naming the argument by an arbitrary closed term

The paper writes the represented instance as `⌜f⌝(⌜n⌝)` (tex:606): a *name* for the
argument, with no notation fixed for how that name is spelled — the paper writes numerals
positionally (tex:614, tex:757) and never commits to a numeral notation.  That freedom is
load-bearing here.  Where the argument is a machine/input pair rather than a day index, its
*value* is exponential in the day, so Foundation's unary `Semiterm.Operator.numeral` is not
an admissible spelling — its symbol count is the value itself — while the compact Horner
term `binNumeral` (`Construction/Witnesses/StructuredPaperRpn.lean`) is, at `O(log v)`
nodes.

The declarations below state the claim sentence at an arbitrary closed term, and
`provable_subst_iff_of_val` transfers provability between two closed terms naming the same
value.  Both are indifferent to which spelling a consumer picks. -/

/-- The representation body with the argument named by a closed term `t` rather than by a
numeral: `γ(t, ν) ⟺ ν = ȳ`. -/
def reprBodyTerm (γ : ArithmeticSemisentence 2) (y : ℕ) (t : Semiterm.Const ℒₒᵣ) :
    ArithmeticSemisentence 1 :=
  Semiformula.subst γ ![t.const, #0] 🡘 (“#0 = ↑y” : ArithmeticSemisentence 1)

/-- The paper's `⌜f⌝(t) = ȳ` with the argument named by a closed term:
`∀ν (γ(t, ν) ⟺ ν = ȳ)`. -/
def reprAllTerm (γ : ArithmeticSemisentence 2) (y : ℕ) (t : Semiterm.Const ℒₒᵣ) :
    ArithmeticSentence :=
  ∀⁰ (reprBodyTerm γ y t)

/-- The numeral spelling is the `t = n̄` instance of the term spelling. -/
lemma reprBody_eq_reprBodyTerm (γ : ArithmeticSemisentence 2) (y z : ℕ) :
    reprBody γ y z = reprBodyTerm γ y (Semiterm.Operator.numeral ℒₒᵣ z) := rfl

lemma reprAll_eq_reprAllTerm (γ : ArithmeticSemisentence 2) (y z : ℕ) :
    reprAll γ y z = reprAllTerm γ y (Semiterm.Operator.numeral ℒₒᵣ z) := rfl

/-- **The family is a fixed schema's closed-term instances.**  The term-argument
generalization of `reprAllSchema_subst`: whatever closed term names the argument, the claim
sentence is one substitution instance of the *same* one-variable schema, which is what keeps
provability of the family enumerable by the fixed-schema machinery even though `γ` came from
an existential.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`Rewriting.app_all`, `Rew.subst_comp_subst`.  `congr`/`ext` do not close it. -/
lemma reprAllSchema_subst_term (γ : ArithmeticSemisentence 2) (y : ℕ)
    (t : Semiterm.Const ℒₒᵣ) :
    (Semiformula.subst (reprAllSchema γ y) ![t.const] : ArithmeticSentence)
      = reprAllTerm γ y t := by
  simp only [reprAllSchema, reprAllTerm, reprBodyTerm, Semiformula.subst, Rewriting.app_all]
  refine congrArg Semiformula.all ?_
  simp only [LogicalConnective.HomClass.map_iff]
  congr 1
  · simp only [← TransitiveRewriting.comp_app, Rew.q_subst, Rew.subst_comp_subst]
    refine congrArg (fun v => Rewriting.app (Rew.subst v) γ) ?_
    funext i
    fin_cases i <;> simp
  · simp

/-- **Provability of a schema instance depends only on the *value* of the closed term that
names the argument.**

This is what licenses spelling a large argument compactly.  The proof is Gödel completeness
in both directions — soundness carries a derivation into every model of `T`, the two terms
evaluate alike there because `𝗣𝗔⁻ ⪯ T`, and completeness carries validity back — so it is
not a semantic *hypothesis* on `T`: the conclusion is about `T`'s derivations only.

`hval` is discharged for the compact numeral by `binNumeral_val`.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`Arithmetic.complete`, `Theory.Proof.sound`, `ModelsTheory.of_provably_subtheory`. -/
lemma provable_subst_iff_of_val (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T]
    (φ : ArithmeticSemisentence 1) (t : Semiterm.Const ℒₒᵣ) (v : ℕ)
    (hval : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻],
      t.val (![] : Fin 0 → M) = (v : M)) :
    T ⊢ (φ/[t.const] : ArithmeticSentence) ↔ T ⊢ (φ/[↑v] : ArithmeticSentence) := by
  haveI : 𝗘𝗤 ℒₒᵣ ⪯ T :=
    Entailment.WeakerThan.trans (𝓣 := (𝗣𝗔⁻ : ArithmeticTheory)) inferInstance inferInstance
  have key : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻],
      (M↓[ℒₒᵣ] ⊧ (φ/[t.const] : ArithmeticSentence)) ↔
        (M↓[ℒₒᵣ] ⊧ (φ/[↑v] : ArithmeticSentence)) := by
    intro M _ _
    simp only [models_iff, Semiformula.eval_substs]
    refine iff_of_eq (congrArg (fun w => (Semiformula.Eval w Empty.elim) φ) ?_)
    funext i
    fin_cases i
    simpa [Structure.numeral_eq_numeral, numeral_eq_natCast] using hval M
  constructor
  · intro h
    refine Arithmetic.complete.{0} T _ fun M _ _ => ?_
    haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := ModelsTheory.of_provably_subtheory M 𝗣𝗔⁻ T inferInstance
    exact (key M).mp (consequence_iff.mp (Theory.Proof.sound h) M inferInstance)
  · intro h
    refine Arithmetic.complete.{0} T _ fun M _ _ => ?_
    haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := ModelsTheory.of_provably_subtheory M 𝗣𝗔⁻ T inferInstance
    exact (key M).mpr (consequence_iff.mp (Theory.Proof.sound h) M inferInstance)

/-- **The paper's own observation (line 604): representing computations forces consistency.**

If `T` were inconsistent it would prove every sentence, so the representation `Iff` for the
constant-`0` function would yield `1 = 0`.

Kind `P` (proved).  Provenance: (a) derived in-project from `RepresentsComputations`. -/
lemma RepresentsComputations.consistent (T : ArithmeticTheory) [h : RepresentsComputations T] :
    Entailment.Consistent T := by
  by_contra hcon
  have hinc : Entailment.Inconsistent T := Entailment.not_consistent_iff_inconsistent.mp hcon
  obtain ⟨γ, hγ⟩ := h.repr (fun _ => 0) (Computable.const 0)
  exact absurd ((hγ 0 1).mpr (hinc _)) (by decide)

#print axioms reprAllSchema_subst_term
#print axioms provable_subst_iff_of_val
#print axioms mentions_zero_of_repr_ne

end LogicalInduction
