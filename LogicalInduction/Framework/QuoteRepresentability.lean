/-
# One code formula, two value fibers: provable exclusivity for quoted decisions

The quotation apparatus (`Construction/Witnesses/QuotationAffine.lean`) names a Boolean
decision by a *positive* and a *negative* arithmetic schema and needs the two never to be
provable together.  Building them as two independent r.e. schemas (`codeOfREPred`) makes
their exclusivity a fact about the **standard model** only, which is why the quotation
family used to carry `[T.SoundOnHierarchy 𝚺 1]`.

This file supplies the soundness-free replacement.  Both schemas come from the *same*
Foundation `code c` formula for one partial recursive function, read at two different
values: `valueSchema c 1` and `valueSchema c 0`.  Single-valuedness of `code c` in every
model of `𝗣𝗔⁻` (`code_uniq`) plus Gödel completeness then make exclusivity a *theorem of
the theory*, so the quotation tag closes from consistency exactly like the halting tags.

Two directions, two strengths:

* `valueSchema_prov` (a true value is provable) is Σ₁-completeness — `[𝗥₀ ⪯ T]` only.
* `valueSchema_exclusive_prov` (two different values are refutable together) is
  `code_uniq` + `Arithmetic.complete` — `[𝗣𝗔⁻ ⪯ T]`, for the reason recorded at
  `codeAux_uniq`: the `rfind` case needs `<` to be linear.

`codeAux_uniq`/`code_uniq` are Foundation's own commented-out lemmas
(`Foundation/FirstOrder/Arithmetic/R0/Representation.lean`, lines 115–162), revived and
reproved here **at their original `𝗣𝗔⁻` hypothesis**.  The `𝗥₀` in the commented text is
not the statement they were retired from: Foundation commit 593d63d8 commented the block
out *and* weakened `𝗣𝗔⁻` to `𝗥₀` in one stroke, so the visible `𝗥₀` version never
compiled.  This revival restores the hypothesis the lemmas actually had, and the reason
they had it is the `rfind` case below.  They were first revived in
`Construction/Witnesses/R0Representability.lean`; they live here now so that both that
file and the quotation layer can cite one copy.
-/
import LogicalInduction.Framework.RepresentsComputations
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
import Foundation.FirstOrder.Arithmetic.Induction

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

section Uniq

open Nat.ArithPart₁

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- Single-valuedness of `codeAux c` in every model of `𝗣𝗔⁻`.

This is Foundation's commented-out `codeAux_uniq`
(`Foundation/FirstOrder/Arithmetic/R0/Representation.lean`, lines 115–162), revived and
reproved at its **original** `𝗣𝗔⁻` hypothesis — the `𝗥₀` visible in the commented text is
dead code that never compiled (commit 593d63d8 commented the block out and weakened
`𝗣𝗔⁻` to `𝗥₀` together).  `𝗣𝗔⁻` is exactly what the `rfind` case needs: the `wlog z < z'`
step requires `<` to be linear on `M`, which `𝗥₀` does not provide.

Kind `P` (proved).  Provenance: (a) derived in-project; (b) Foundation citations —
`codeAux`, `PeanoMinus`'s `LinearOrder` on models. -/
lemma codeAux_uniq {k} {c : Code k} {v : Fin k → M} {z z' : M} :
    Semiformula.Evalf (M := M) (z :> v) (codeAux c) →
    Semiformula.Evalf (M := M) (z' :> v) (codeAux c) → z = z' := by
  induction c generalizing z z' <;> simp [codeAux]
  case zero => rintro rfl rfl; rfl
  case one  => rintro rfl rfl; rfl
  case add  => rintro rfl rfl; rfl
  case mul  => rintro rfl rfl; rfl
  case proj => rintro rfl rfl; rfl
  case equal i j =>
    by_cases hv : v i = v j <;> simp [hv]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case lt i j =>
    rintro (⟨h₁, rfl⟩ | ⟨h₁, rfl⟩) (⟨h₂, rfl⟩ | ⟨h₂, rfl⟩) <;>
      first
        | rfl
        | exact absurd h₁ (not_lt.mpr h₂)
        | exact absurd h₂ (not_lt.mpr h₁)
  case comp m n c d ihc ihd =>
    simp [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']
    intro w₁ hc₁ hd₁ w₂ hc₂ hd₂
    have : w₁ = w₂ := funext fun i => ihd i (hd₁ i) (hd₂ i)
    rcases this with rfl
    exact ihc hc₁ hc₂
  case rfind c ih =>
    simp [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']
    intro h₁ hm₁ h₂ hm₂
    by_contra hz
    wlog h : z < z' with Hz
    case inr =>
      have : z' < z := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hz)
      exact Hz (k := k) c ih h₂ hm₂ h₁ hm₁ (Ne.symm hz) this
    have : ∃ x, x ≠ 0 ∧ (Semiformula.Evalf (M := M) (x :> z :> fun i => v i)) (codeAux c) := hm₂ z h
    rcases this with ⟨x, xz, hx⟩
    exact xz (ih hx h₁)

/-- Single-valuedness of `code c` in every model of `𝗣𝗔⁻` — Foundation's commented-out
`code_uniq`, revived at the `𝗣𝗔⁻` hypothesis it originally carried (see the file header:
the `𝗥₀` in the commented text is dead code from the commit that retired the block).

Kind `C` (composition) over `codeAux_uniq`. -/
lemma code_uniq {k} {c : Code k} {v : Fin k → M} {z z' : M} :
    Semiformula.Evalb (M := M) (z :> v) (code c) →
    Semiformula.Evalb (M := M) (z' :> v) (code c) → z = z' := by
  simp [code, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def]
  exact codeAux_uniq

end Uniq

/-! ## Value fibers of one code formula -/

section ValueSchema

open Nat.ArithPart₁

/-- The schema "the computation coded by `c` returns `y` on the input `#0`".

`Foundation`'s `code c` carries the *value* at `#0` and the *argument* at `#1`; fixing the
value slot to the numeral `ȳ` leaves a one-variable schema in the argument. -/
noncomputable def valueSchema (c : Code 1) (y : ℕ) : ArithmeticSemisentence 1 :=
  (code c)/[‘↑y’, #0]

/-- Substituting the argument numeral gives the two-numeral instance of `code c`. -/
lemma valueSchema_subst (c : Code 1) (y z : ℕ) :
    ((valueSchema c y)/[‘↑z’] : ArithmeticSentence) = (code c)/[‘↑y’, ‘↑z’] :=
  subst_subst_two (code c) y z

/-- The numeral instance is `𝚺 1`, so Σ₁-completeness applies to it. -/
lemma valueSchema_sigma_one (c : Code 1) (y z : ℕ) :
    Hierarchy 𝚺 1 ((valueSchema c y)/[‘↑z’] : ArithmeticSentence) := by
  rw [valueSchema_subst]
  simp

/-- Standard-model truth of a numeral instance is exactly the value fact. -/
lemma models_valueSchema {c : Code 1} {g : List.Vector ℕ 1 →. ℕ} (hc : c.eval g) (y z : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧ ((valueSchema c y)/[‘↑z’] : ArithmeticSentence)
      ↔ y ∈ g (List.Vector.ofFn ![z]) := by
  rw [valueSchema_subst]
  simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton]
    using models_code hc y ![z]

/-- **The positive literal.**  A true value fact is provable, by Σ₁-completeness alone.

Kind `C` (composition).  Provenance: (b) Foundation citations — `models_code`,
`sigma_one_completeness`. -/
lemma valueSchema_prov (T : ArithmeticTheory) [𝗥₀ ⪯ T] {c : Code 1}
    {g : List.Vector ℕ 1 →. ℕ} (hc : c.eval g) {y z : ℕ}
    (hy : y ∈ g (List.Vector.ofFn ![z])) :
    T ⊢ ((valueSchema c y)/[‘↑z’] : ArithmeticSentence) :=
  sigma_one_completeness (valueSchema_sigma_one c y z)
    ((models_valueSchema hc y z).mpr hy)

/-- **The negative literal, without soundness.**  Two *different* value fibers of the same
code formula are refuted together by any extension of `𝗣𝗔⁻`.

This is what replaces `[T.SoundOnHierarchy 𝚺 1]` in the quotation layer: exclusivity of
the positive and negative quote schemas is a theorem of `T`, not a fact about `ℕ`.

Kind `P` (proved).  Provenance: (a) derived in-project from `code_uniq`; (b) Foundation
citations — `Arithmetic.complete`, `ModelsTheory.of_provably_subtheory`,
`numeral_inj_iff`. -/
lemma valueSchema_exclusive_prov (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] (c : Code 1)
    {y y' : ℕ} (hne : y ≠ y') (z : ℕ) :
    T ⊢ ∼(((valueSchema c y)/[‘↑z’] : ArithmeticSentence) ⋏ (valueSchema c y')/[‘↑z’]) := by
  haveI : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance
  refine Arithmetic.complete.{0} T _ fun M _ _ => ?_
  haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := ModelsTheory.of_provably_subtheory M 𝗣𝗔⁻ T inferInstance
  simp only [valueSchema_subst, models_iff, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs]
  rintro ⟨h1, h2⟩
  have hval : (ORingStructure.numeral y : M) = ORingStructure.numeral y' := by
    refine code_uniq (M := M) (c := c) (v := ![(ORingStructure.numeral z : M)]) ?_ ?_
    · simpa [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
        Matrix.empty_eq, Structure.numeral_eq_numeral] using h1
    · simpa [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
        Matrix.empty_eq, Structure.numeral_eq_numeral] using h2
  exact hne (by simpa using hval)

end ValueSchema

end LogicalInduction
