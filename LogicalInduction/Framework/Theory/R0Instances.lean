import LogicalInduction.Framework.Theory.QuoteRepresentability
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
import Foundation.FirstOrder.Arithmetic.Induction

/-!
# Non-vacuity of `RepresentsComputations`: the standard arithmetical theories satisfy it

`LogicalInduction.RepresentsComputations` is the paper's standing hypothesis on the
background theory `Θ` (arXiv:1609.03543v5, §2, lines 600–606).  A hypothesis carries no
content until some theory is *shown* to satisfy it, so this file discharges it for the
theories the development actually names: `𝗣𝗔⁻`, `𝗜𝚺₁`, and `𝗣𝗔`.

The witness formula is Foundation's `code c` for a `Nat.ArithPart₁.Code` of the graph of
`f` (`Foundation/FirstOrder/Arithmetic/R0/Representation.lean`), with its two bound
variables swapped so that argument `#0` is the *input* and `#1` the *value*, as the class
demands.  The two halves of the class's `Iff` are proved by opposite routes:

* `→` (`y = f n` implies provability): the biconditional
  `∀ν (code c (ν, n̄) ↔ ν = ȳ)` is *valid in every model of `𝗣𝗔⁻`* — `←` of the inner
  `Iff` by Σ₁-completeness (`bold_sigma_one_completeness'`, which needs only `𝗥₀`), `→` by
  single-valuedness of `code c` in every model (`code_uniq`).  Gödel completeness
  (`Arithmetic.complete`) then turns validity into a `𝗣𝗔⁻`-proof, and `𝗣𝗔⁻ ⪯ U` transports
  it to `U`.
* `←` (provability implies `y = f n`): soundness of `U` at the standard model, which is
  why the hypothesis `[ℕ↓[ℒₒᵣ] ⊧* U]` appears.  This direction is genuinely
  *anti*-monotone in the theory — a theory with more theorems can prove the biconditional
  for a *wrong* `y` — so `RepresentsComputations` does **not** transport along `⪯` for
  free, and there is deliberately no `of_weakerThan` lemma here.  The honest transport is
  the hypothesis `[ℕ↓[ℒₒᵣ] ⊧* U]` carried by `representsComputations_of_peanoMinus`.

**Every registered instance is `ℕ`-sound, and that is a gap in the non-vacuity argument.**
`representsComputations_of_peanoMinus` requires `[ℕ↓[ℒₒᵣ] ⊧* U]`, and the three
instances registered below (`𝗣𝗔⁻`, `𝗜𝚺₁`, `𝗣𝗔`) are all true in the standard model.  The
*class* is strictly weaker than that — it is a condition on `U`'s derivations only, and the
paper's `Θ` is assumed consistent, c.e. and representing computations, with no soundness —
so a theory such as `𝗣𝗔 + ¬Con(𝗣𝗔)` is admitted by the class, is consistent, and is the
interesting unsound case.  It is **unwitnessed here**: nothing in this file exhibits an
`ℕ`-unsound model of `RepresentsComputations`, because the `←` direction of the class
(provability implies correctness of the value) is anti-monotone in the theory and this file
gets it from soundness alone.  Discharging it needs a genuinely *syntactic* representability
proof — Rosser-style strong representability inside `𝗥`/`𝗣𝗔⁻`, whose `←` direction runs
through the theory's own numeral apparatus rather than through `ℕ` — which is an upstream
(Foundation) candidate rather than a repair to make here.  Consumers are unaffected: no
endpoint inherits a semantic hypothesis from this file, and the instances are used only to
show the premise set is inhabited at all.

The single-valuedness lemmas `codeAux_uniq`/`code_uniq` that the `→` direction rests on
live in `Framework/Theory/QuoteRepresentability.lean`, which the quotation layer also cites.

**Why `𝗣𝗔⁻` and not `𝗥₀`.**  Foundation's `code_uniq` is commented out, and the commented
text reads `𝗥₀`; it does not go through.  The `rfind` case compares two putative witnesses
`z`, `z'` and needs them to be comparable.  `𝗥₀ =
Ω₁–Ω₄` has no trichotomy axiom (the classical strong-representability theorem is for
Robinson's `R`, which adds `Ω₅ : ∀x (x ≤ n̄ ∨ n̄ ≤ x)`), and Foundation records
`𝗥₀ ⪱ 𝗣𝗔⁻`.  Keeping the ambient theory at `𝗣𝗔⁻` — whose models carry a `LinearOrder` —
is what makes the `wlog z < z'` step legitimate.  Everything else in the argument needs
only `𝗥₀`.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

section Representation

open Nat.ArithPart₁

/-- Swap the two bound variables of a two-variable semisentence.

`Foundation`'s `code c` puts the *value* at `#0` and the *argument* at `#1`;
`RepresentsComputations` wants the argument at `#0` and the value at `#1`. -/
private def swapArgs (φ : ArithmeticSemisentence 2) : ArithmeticSemisentence 2 :=
  Semiformula.subst φ ![#1, #0]

/-- Substituting a numeral for the (swapped) first argument recovers a substitution
directly into `φ`.  As with `LogicalInduction.subst_subst_two`, `congr`/`ext` do not close
this — the rewrite must go through `Rew.subst_comp_subst`. -/
private lemma subst_swapArgs (φ : ArithmeticSemisentence 2) (n : ℕ) :
    (Semiformula.subst (swapArgs φ) ![‘↑n’, #0] : ArithmeticSemisentence 1)
      = Semiformula.subst φ ![#0, ‘↑n’] := by
  simp only [swapArgs, Semiformula.subst, ← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
  refine congrArg (fun v => Rewriting.app (Rew.subst v) φ) ?_
  funext i
  fin_cases i <;> simp

/-- **The graph of `code c` is exactly the value graph, in every model of `𝗣𝗔⁻`.**

`←` is Σ₁-completeness (`bold_sigma_one_completeness'`, which needs only `𝗥₀`); `→` is
`code_uniq`.  Note that `z` ranges over *all* of `M`, including nonstandard elements — that
is what makes the resulting biconditional a `∀`-statement the theory can prove.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`models_code`, `code_sigma_one`, `bold_sigma_one_completeness'`. -/
private lemma eval_code_iff {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {c : Code 1} {g : List.Vector ℕ 1 →. ℕ} (hc : c.eval g) {n y : ℕ}
    (hy : y ∈ g (List.Vector.ofFn ![n])) (z : M) :
    Semiformula.Evalb (M := M) ![z, ORingStructure.numeral n] (code c)
      ↔ z = ORingStructure.numeral y := by
  have hstd : Semiformula.Evalb (M := ℕ) ![y, n] (code c) := by
    have := (models_code hc y ![n]).mpr hy
    simpa using this
  have hM : Semiformula.Evalb (M := M)
      ![(ORingStructure.numeral y : M), ORingStructure.numeral n] (code c) := by
    have := bold_sigma_one_completeness' (M := M) (code_sigma_one c) hstd
    simpa [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton] using this
  constructor
  · intro h; exact code_uniq (v := ![(ORingStructure.numeral n : M)]) h hM
  · rintro rfl; exact hM

/-- The class's sentence, `∀ν (γ(n̄,ν) ↔ ν = ȳ)` for `γ = swapArgs (code c)`, holds in
every model of `𝗣𝗔⁻` whenever `y` really is the value.

Kind `C` (composition) over `eval_code_iff`. -/
private lemma models_repr_sentence {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {c : Code 1} {g : List.Vector ℕ 1 →. ℕ} (hc : c.eval g) {n y : ℕ}
    (hy : y ∈ g (List.Vector.ofFn ![n])) :
    M↓[ℒₒᵣ] ⊧ (∀⁰ (Semiformula.subst (swapArgs (code c)) ![‘↑n’, #0] 🡘
      (“#0 = ↑y” : ArithmeticSemisentence 1))) := by
  rw [subst_swapArgs]
  simp only [models_iff, Semiformula.eval_all, LogicalConnective.HomClass.map_iff,
    Semiformula.eval_substs]
  intro x
  have h := eval_code_iff (M := M) hc hy x
  simpa [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    Matrix.empty_eq, Structure.numeral_eq_numeral] using h

/-- **Every `ℕ`-sound extension of `𝗣𝗔⁻` represents computations.**

This discharges the paper's standing hypothesis on `Θ` for a concrete class of theories,
so `RepresentsComputations` is not a vacuous premise.

Both hypotheses are load-bearing and neither is removable:

* `[𝗣𝗔⁻ ⪯ U]` drives the `→` direction, through validity in all models of `𝗣𝗔⁻` plus
  Gödel completeness.  It cannot be weakened to `[𝗥₀ ⪯ U]` by this argument — see the file
  header.
* `[ℕ↓[ℒₒᵣ] ⊧* U]` drives the `←` direction.  Some such hypothesis is unavoidable: the
  `←` direction is anti-monotone in the theory, so no `⪯`-transport lemma can replace it.

Note the asymmetry with the class itself, which is deliberately *not* a soundness
assumption: soundness is used here to **verify** the hypothesis for particular theories,
not by any consumer of it.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`Nat.ArithPart₁.exists_code`, `models_code`, `Arithmetic.complete`, `Theory.Proof.sound`,
`ModelsTheory.of_provably_subtheory`. -/
lemma representsComputations_of_peanoMinus (U : ArithmeticTheory)
    [𝗣𝗔⁻ ⪯ U] [ℕ↓[ℒₒᵣ] ⊧* U] : RepresentsComputations U := by
  haveI : 𝗘𝗤 ℒₒᵣ ⪯ U := Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance
  refine ⟨fun f hf => ?_⟩
  have hcomp : Computable fun v : List.Vector ℕ 1 => f (v.get 0) :=
    hf.comp (Primrec.to_comp <| Primrec.vector_get.comp Primrec.id (Primrec.const (0 : Fin 1)))
  obtain ⟨c, hc⟩ := Nat.ArithPart₁.exists_code
    (Nat.ArithPart₁.of_partrec (Nat.Partrec'.of_part (Computable.partrec hcomp)))
  refine ⟨swapArgs (code c), fun n y => ?_⟩
  constructor
  · rintro rfl
    refine Arithmetic.complete.{0} U _ fun M _ _ => ?_
    haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := ModelsTheory.of_provably_subtheory M 𝗣𝗔⁻ U inferInstance
    exact models_repr_sentence hc (by simp)
  · intro h
    have hN := consequence_iff.mp (Theory.Proof.sound h) ℕ inferInstance
    rw [subst_swapArgs] at hN
    simp only [models_iff, Semiformula.eval_all, LogicalConnective.HomClass.map_iff,
      Semiformula.eval_substs] at hN
    have h2 : Semiformula.Evalb (M := ℕ) ![f n, n] (code c) :=
      (models_code hc (f n) ![n]).mpr (by simp)
    have h1 := hN (f n)
    have h3 : Semiformula.Evalb (M := ℕ) ![f n, n] (code c) ↔ f n = y := by
      simpa [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
        Matrix.empty_eq, Structure.numeral_eq_numeral] using h1
    exact (h3.mp h2).symm

end Representation

/-! ## The concrete witnesses

Registered as instances so that downstream statements carrying `[RepresentsComputations T]`
are inhabited at the theories this development names. -/

instance : RepresentsComputations 𝗣𝗔⁻ := representsComputations_of_peanoMinus 𝗣𝗔⁻

instance : RepresentsComputations 𝗜𝚺₁ := representsComputations_of_peanoMinus 𝗜𝚺₁

instance : RepresentsComputations 𝗣𝗔 := representsComputations_of_peanoMinus 𝗣𝗔

/-! ## Non-vacuity -/

example : RepresentsComputations 𝗜𝚺₁ := inferInstance

example : RepresentsComputations 𝗣𝗔 := inferInstance

/-- The class's own consistency observation is therefore not vacuous either. -/
example : Entailment.Consistent 𝗜𝚺₁ := RepresentsComputations.consistent 𝗜𝚺₁

end LogicalInduction
