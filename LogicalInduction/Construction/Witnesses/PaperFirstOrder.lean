import LogicalInduction.Construction.Witnesses.SemanticSource
import Foundation.FirstOrder.Basic.Coding

/-!
# Paper first-order sentences at the propositional ABI

The Logical Induction paper treats its public language as propositional logic over the
prime sentences of an older first-order language.  This file implements that boundary for
Foundation's arithmetic language without changing FAF's public `Sentence` type.

Boolean connectives are preserved as propositional connectives.  Atomic and quantified
first-order sentences receive compact public atom names in the reserved tag-`7` namespace.
Negated relations and universal quantifiers are represented by propositional negation of
their positive prime, matching the paper's prime decomposition convention.

This is only the syntax half of the paper-facing LUV repair.  A later fixed theorem process
must enumerate the decompositions of proved first-order sentences, and the LUV compiler must
construct the appropriate rational-threshold formulas.  Keeping this layer separate makes
the source-language ownership fact unconditional and kernel checked.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.Propositional

/-- Reserved public-atom tag for prime sentences of the pre-extension arithmetic language.

Existing computation, quotation, product-definition, and semantic-prime atoms use tags
`0` through `6`.  Tag `7` therefore records language ownership syntactically and is disjoint
from semantic handles by construction. -/
def paperPrimeTag : ℕ := 7

/-- Compact public name of a first-order prime reading.  The Boolean records whether the
stored formula is read positively.  Negative prime heads store their original formula with
polarity `false`; the outer propositional negation then recovers the formula's truth. -/
def paperPrimeCode (positive : Bool) (φ : ArithmeticSentence) : ℕ :=
  Nat.pair paperPrimeTag (Nat.pair (Encodable.encode positive) (Encodable.encode φ))

/-- A first-order prime reading embedded into FAF's existing propositional language. -/
def paperPrimeSentence (positive : Bool) (φ : ArithmeticSentence) : Sentence :=
  Formula.atom (paperPrimeCode positive φ)

@[simp] lemma paperPrimeCode_unpair_tag (positive : Bool) (φ : ArithmeticSentence) :
    (paperPrimeCode positive φ).unpair.1 = paperPrimeTag := by
  simp [paperPrimeCode]

lemma paperPrimeCode_injective :
    Function.Injective (fun p : Bool × ArithmeticSentence => paperPrimeCode p.1 p.2) := by
  rintro ⟨b, φ⟩ ⟨c, ψ⟩ h
  simp only [paperPrimeCode, Nat.pair_eq_pair] at h
  exact Prod.ext (Encodable.encode_inj.mp h.2.1) (Encodable.encode_inj.mp h.2.2)

lemma paperPrimeSentence_injective :
    Function.Injective (fun p : Bool × ArithmeticSentence => paperPrimeSentence p.1 p.2) := by
  rintro ⟨b, φ⟩ ⟨c, ψ⟩ h
  apply paperPrimeCode_injective
  injection h

/-- Prime decomposition of an arithmetic sentence into the existing FAF language.

Only conjunction and disjunction are traversed.  Quantifiers remain opaque prime
sentences.  Foundation stores formulas in negation-normal form, so `.nrel` and `.all` are
the two negative-prime cases. -/
def paperPrimeDecompose : ArithmeticSentence → Sentence
  | .verum => ⊤
  | .falsum => ⊥
  | .and φ ψ => paperPrimeDecompose φ ⋏ paperPrimeDecompose ψ
  | .or φ ψ => paperPrimeDecompose φ ⋎ paperPrimeDecompose ψ
  | .rel r v => paperPrimeSentence true (.rel r v)
  | .nrel r v => ∼paperPrimeSentence false (.nrel r v)
  | .exs φ => paperPrimeSentence true (.exs φ)
  | .all φ => ∼paperPrimeSentence false (.all φ)

@[simp] lemma paperPrimeDecompose_verum :
    paperPrimeDecompose (Semiformula.verum : ArithmeticSentence) = (⊤ : Sentence) := by
  simp [paperPrimeDecompose]

@[simp] lemma paperPrimeDecompose_falsum :
    paperPrimeDecompose (Semiformula.falsum : ArithmeticSentence) = (⊥ : Sentence) := by
  simp [paperPrimeDecompose]

@[simp] lemma paperPrimeDecompose_and (φ ψ : ArithmeticSentence) :
    paperPrimeDecompose (.and φ ψ) = paperPrimeDecompose φ ⋏ paperPrimeDecompose ψ := by
  simp [paperPrimeDecompose]

@[simp] lemma paperPrimeDecompose_or (φ ψ : ArithmeticSentence) :
    paperPrimeDecompose (.or φ ψ) = paperPrimeDecompose φ ⋎ paperPrimeDecompose ψ := by
  simp [paperPrimeDecompose]

@[simp] lemma sentenceAtomCodes_paperPrimeSentence (positive : Bool) (φ : ArithmeticSentence) :
    sentenceAtomCodes (paperPrimeSentence positive φ) = {paperPrimeCode positive φ} := rfl

/-- Every atom introduced by the first-order compiler has the old-language tag. -/
lemma paperPrimeDecompose_atom_tag :
    ∀ (φ : ArithmeticSentence) a, a ∈ sentenceAtomCodes (paperPrimeDecompose φ) →
      a.unpair.1 = paperPrimeTag := by
  intro φ
  fun_induction paperPrimeDecompose φ <;>
    simp_all [paperPrimeSentence, paperPrimeCode, paperPrimeTag] <;>
    aesop

/-- Compiled paper formulas cannot mention semantic-prime handles.  This is the
source-language separation fact that flat arbitrary `LUV` syntax lacks. -/
lemma paperPrimeDecompose_semanticPrimeFresh (φ : ArithmeticSentence) :
    SemanticPrimeFreshSentence (paperPrimeDecompose φ) := by
  intro a ha hsemantic
  have hpaper := paperPrimeDecompose_atom_tag φ a ha
  rw [hpaper] at hsemantic
  norm_num [paperPrimeTag, semanticPrimeTag] at hsemantic

/-! ## Model semantics

The valuation below is intentionally defined by ownership rather than by decoding an
arbitrary natural.  Injectivity of `paperPrimeCode` makes its value on every compiled atom
canonical, while atoms outside tag `7` remain false. -/

/-- The propositional world induced by a first-order arithmetic structure. -/
noncomputable def paperPrimeWorld (M : Type*) [Nonempty M] [Structure ℒₒᵣ M] : PCWorld :=
  fun a => ∃ (positive : Bool) (φ : ArithmeticSentence),
    a = paperPrimeCode positive φ ∧ if positive then M ↓[ℒₒᵣ] ⊧ φ else ¬M ↓[ℒₒᵣ] ⊧ φ

@[simp] lemma paperPrimeWorld_paperPrimeCode (M : Type*) [Nonempty M] [Structure ℒₒᵣ M]
    (positive : Bool) (φ : ArithmeticSentence) :
    paperPrimeWorld M (paperPrimeCode positive φ) ↔
      if positive then M ↓[ℒₒᵣ] ⊧ φ else ¬M ↓[ℒₒᵣ] ⊧ φ := by
  constructor
  · rintro ⟨polarity, ψ, hcode, hψ⟩
    have hp : (positive, φ) = (polarity, ψ) := paperPrimeCode_injective hcode
    cases hp
    exact hψ
  · intro hφ
    exact ⟨positive, φ, rfl, hφ⟩

/-- Prime decomposition preserves first-order truth in the induced p.c. world. -/
lemma paperPrimeWorld_holds_decompose (M : Type*) [Nonempty M] [Structure ℒₒᵣ M] :
    ∀ φ : ArithmeticSentence,
      (paperPrimeWorld M).Holds (paperPrimeDecompose φ) ↔ M ↓[ℒₒᵣ] ⊧ φ := by
  intro φ
  fun_induction paperPrimeDecompose φ with
  | case1 =>
      simp [PCWorld.Holds,
        show (Semiformula.verum : ArithmeticSentence) = ⊤ from rfl,
        LO.Propositional.Formula.Boolean.val]
  | case2 =>
      simp [PCWorld.Holds,
        show (Semiformula.falsum : ArithmeticSentence) = ⊥ from rfl,
        LO.Propositional.Formula.Boolean.val]
  | case3 φ ψ ihφ ihψ =>
      simpa [PCWorld.Holds, models_iff,
        show Semiformula.and φ ψ = φ ⋏ ψ from rfl,
        LogicalConnective.HomClass.map_and,
        LO.Propositional.Formula.Boolean.val] using and_congr ihφ ihψ
  | case4 φ ψ ihφ ihψ =>
      simpa [PCWorld.Holds, models_iff,
        show Semiformula.or φ ψ = φ ⋎ ψ from rfl,
        LogicalConnective.HomClass.map_or,
        LO.Propositional.Formula.Boolean.val] using or_congr ihφ ihψ
  | case5 arity r v =>
      change paperPrimeWorld M (paperPrimeCode true (.rel r v)) ↔
        M ↓[ℒₒᵣ] ⊧ (.rel r v)
      exact paperPrimeWorld_paperPrimeCode M true (.rel r v)
  | case6 arity r v =>
      change (¬paperPrimeWorld M (paperPrimeCode false (.nrel r v))) ↔
        M ↓[ℒₒᵣ] ⊧ (.nrel r v)
      have h := paperPrimeWorld_paperPrimeCode M false (.nrel r v)
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      constructor
      · intro hn
        by_contra hm
        exact hn (h.mpr hm)
      · intro hm hw
        exact (h.mp hw) hm
  | case7 ψ =>
      change paperPrimeWorld M (paperPrimeCode true (.exs ψ)) ↔
        M ↓[ℒₒᵣ] ⊧ (.exs ψ)
      exact paperPrimeWorld_paperPrimeCode M true (.exs ψ)
  | case8 ψ =>
      change (¬paperPrimeWorld M (paperPrimeCode false (.all ψ))) ↔
        M ↓[ℒₒᵣ] ⊧ (.all ψ)
      have h := paperPrimeWorld_paperPrimeCode M false (.all ψ)
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      constructor
      · intro hn
        by_contra hm
        exact hn (h.mpr hm)
      · intro hm hw
        exact (h.mp hw) hm

#print axioms paperPrimeCode_injective
#print axioms paperPrimeDecompose_atom_tag
#print axioms paperPrimeDecompose_semanticPrimeFresh
#print axioms paperPrimeWorld_holds_decompose

end LogicalInduction
