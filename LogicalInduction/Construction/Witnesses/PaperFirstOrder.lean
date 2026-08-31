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

Existing computation, quotation, product-definition, and semantic-prime atoms use payload
tags `0`–`4`.  Tag `5` therefore records language ownership syntactically and is disjoint
from semantic handles by construction.  See the global atom-payload allocation table at
`ComputationClaimKind.godelCode`.

The `RpnSentence`/`Criterion` parsers spell this tag as the literal `5` (they are upstream
of this definition); `parseStructuredPaperPrime_spec` in `StructuredPaperRpn.lean` is the
bridge, and both must move together. -/
def paperPrimeTag : ℕ := 5

/-- Compact public name of a first-order prime reading.  The Boolean records whether the
stored formula is read positively.  Negative prime heads store their original formula with
polarity `false`; the outer propositional negation then recovers the formula's truth. -/
def paperPrimeCode (positive : Bool) (φ : ArithmeticProposition) : ℕ :=
  Nat.pair paperPrimeTag (Nat.pair (Encodable.encode positive) (Encodable.encode φ))

/-- A first-order prime reading embedded into FAF's existing propositional language. -/
def paperPrimeSentence (positive : Bool) (φ : ArithmeticProposition) : Sentence :=
  Formula.atom (paperPrimeCode positive φ)

@[simp] lemma paperPrimeCode_unpair_tag (positive : Bool) (φ : ArithmeticProposition) :
    (paperPrimeCode positive φ).unpair.1 = paperPrimeTag := by
  simp [paperPrimeCode]

lemma paperPrimeCode_injective :
    Function.Injective (fun p : Bool × ArithmeticProposition => paperPrimeCode p.1 p.2) := by
  rintro ⟨b, φ⟩ ⟨c, ψ⟩ h
  simp only [paperPrimeCode, Nat.pair_eq_pair] at h
  exact Prod.ext (Encodable.encode_inj.mp h.2.1) (Encodable.encode_inj.mp h.2.2)

lemma paperPrimeSentence_injective :
    Function.Injective (fun p : Bool × ArithmeticProposition => paperPrimeSentence p.1 p.2) := by
  rintro ⟨b, φ⟩ ⟨c, ψ⟩ h
  apply paperPrimeCode_injective
  injection h

/-- Prime decomposition of an arithmetic sentence into the existing FAF language.

Only conjunction and disjunction are traversed.  Quantifiers remain opaque prime
sentences.  Foundation stores formulas in negation-normal form, so `.nrel` and `.all` are
the two negative-prime cases. -/
def paperPrimeDecompose : ArithmeticProposition → Sentence
  | .verum => ⊤
  | .falsum => ⊥
  | .and φ ψ => paperPrimeDecompose φ ⋏ paperPrimeDecompose ψ
  | .or φ ψ => paperPrimeDecompose φ ⋎ paperPrimeDecompose ψ
  | .rel r v => paperPrimeSentence true (.rel r v)
  | .nrel r v => ∼paperPrimeSentence true (.rel r v)
  | .exs φ => paperPrimeSentence true (.exs φ)
  | .all φ => ∼paperPrimeSentence true (.exs (∼φ))

@[simp] lemma paperPrimeDecompose_verum :
    paperPrimeDecompose (Semiformula.verum : ArithmeticProposition) = (⊤ : Sentence) := by
  simp [paperPrimeDecompose]

@[simp] lemma paperPrimeDecompose_falsum :
    paperPrimeDecompose (Semiformula.falsum : ArithmeticProposition) = (⊥ : Sentence) := by
  simp [paperPrimeDecompose]

@[simp] lemma paperPrimeDecompose_and (φ ψ : ArithmeticProposition) :
    paperPrimeDecompose (.and φ ψ) = paperPrimeDecompose φ ⋏ paperPrimeDecompose ψ := by
  simp [paperPrimeDecompose]

@[simp] lemma paperPrimeDecompose_or (φ ψ : ArithmeticProposition) :
    paperPrimeDecompose (.or φ ψ) = paperPrimeDecompose φ ⋎ paperPrimeDecompose ψ := by
  simp [paperPrimeDecompose]

lemma PCWorld.holds_paperPrimeDecompose_neg (v : PCWorld)
    (φ : ArithmeticProposition) :
    v.Holds (paperPrimeDecompose (∼φ)) ↔
      ¬v.Holds (paperPrimeDecompose φ) := by
  fun_induction paperPrimeDecompose φ with
  | case1 =>
      simp [Semiformula.neg_eq, Semiformula.neg,
        PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | case2 =>
      simp [Semiformula.neg_eq, Semiformula.neg,
        PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | case3 φ ψ ihφ ihψ =>
      rw [Semiformula.neg_eq] at ihφ ihψ
      simp only [Semiformula.neg_eq, Semiformula.neg, paperPrimeDecompose]
      rw [PCWorld.holds_or, PCWorld.holds_and, ihφ, ihψ]
      tauto
  | case4 φ ψ ihφ ihψ =>
      rw [Semiformula.neg_eq] at ihφ ihψ
      simp only [Semiformula.neg_eq, Semiformula.neg, paperPrimeDecompose]
      rw [PCWorld.holds_or, PCWorld.holds_and, ihφ, ihψ]
      tauto
  | case5 arity r t =>
      simp only [Semiformula.neg_eq, Semiformula.neg, paperPrimeDecompose]
      exact PCWorld.holds_neg v (paperPrimeSentence true (.rel r t))
  | case6 arity r t =>
      simp only [Semiformula.neg_eq, Semiformula.neg, paperPrimeDecompose,
        PCWorld.holds_neg]
      tauto
  | case7 ψ =>
      simp only [Semiformula.neg_eq, Semiformula.neg, paperPrimeDecompose]
      rw [Semiformula.neg_neg]
      exact PCWorld.holds_neg v (paperPrimeSentence true (.exs ψ))
  | case8 ψ =>
      simp only [Semiformula.neg_eq, Semiformula.neg, paperPrimeDecompose,
        PCWorld.holds_neg]
      tauto

lemma PCWorld.holds_paperPrimeDecompose_imp (v : PCWorld)
    (φ ψ : ArithmeticProposition) :
    v.Holds (paperPrimeDecompose (φ 🡒 ψ)) ↔
      (v.Holds (paperPrimeDecompose φ) →
        v.Holds (paperPrimeDecompose ψ)) := by
  change v.Holds (paperPrimeDecompose (.or (∼φ) ψ)) ↔ _
  rw [paperPrimeDecompose_or, PCWorld.holds_or,
    PCWorld.holds_paperPrimeDecompose_neg]
  tauto

@[simp] lemma sentenceAtomCodes_paperPrimeSentence (positive : Bool) (φ : ArithmeticProposition) :
    sentenceAtomCodes (paperPrimeSentence positive φ) = {paperPrimeCode positive φ} := rfl

/-- Every atom introduced by the first-order compiler has the old-language tag. -/
lemma paperPrimeDecompose_atom_tag :
    ∀ (φ : ArithmeticProposition) a, a ∈ sentenceAtomCodes (paperPrimeDecompose φ) →
      a.unpair.1 = paperPrimeTag := by
  intro φ
  fun_induction paperPrimeDecompose φ <;>
    simp_all [paperPrimeSentence, paperPrimeCode, paperPrimeTag] <;>
    aesop

/-- Compiled paper formulas cannot mention semantic-prime handles.  This is the
source-language separation fact that flat arbitrary `LUV` syntax lacks. -/
lemma paperPrimeDecompose_semanticPrimeFresh (φ : ArithmeticProposition) :
    SemanticPrimeFreshSentence (paperPrimeDecompose φ) := by
  intro a ha hsemantic
  have hpaper := paperPrimeDecompose_atom_tag φ a ha
  rw [hpaper] at hsemantic
  norm_num [paperPrimeTag, semanticPrimeTag] at hsemantic

/-! ## Model semantics

The valuation below is intentionally defined by ownership rather than by decoding an
arbitrary natural.  Injectivity of `paperPrimeCode` makes its value on every compiled atom
canonical, while atoms outside tag `5` remain false. -/

/-- The propositional world induced by a first-order arithmetic structure. -/
noncomputable def paperPrimeWorld (M : Type*) [Nonempty M] [Structure ℒₒᵣ M]
    (f : ℕ → M) : PCWorld :=
  fun a => ∃ (positive : Bool) (φ : ArithmeticProposition),
    a = paperPrimeCode positive φ ∧ if positive then φ.Evalf f else ¬φ.Evalf f

@[simp] lemma paperPrimeWorld_paperPrimeCode (M : Type*) [Nonempty M] [Structure ℒₒᵣ M]
    (f : ℕ → M) (positive : Bool) (φ : ArithmeticProposition) :
    paperPrimeWorld M f (paperPrimeCode positive φ) ↔
      if positive then φ.Evalf f else ¬φ.Evalf f := by
  constructor
  · rintro ⟨polarity, ψ, hcode, hψ⟩
    have hp : (positive, φ) = (polarity, ψ) := paperPrimeCode_injective hcode
    cases hp
    exact hψ
  · intro hφ
    exact ⟨positive, φ, rfl, hφ⟩

/-- Prime decomposition preserves first-order truth in the induced p.c. world. -/
lemma paperPrimeWorld_holds_decompose (M : Type*) [Nonempty M] [Structure ℒₒᵣ M]
    (f : ℕ → M) : ∀ φ : ArithmeticProposition,
      (paperPrimeWorld M f).Holds (paperPrimeDecompose φ) ↔ φ.Evalf f := by
  intro φ
  fun_induction paperPrimeDecompose φ with
  | case1 =>
      simp [PCWorld.Holds,
        show (Semiformula.verum : ArithmeticProposition) = ⊤ from rfl,
        LO.Propositional.Formula.Boolean.val]
  | case2 =>
      simp [PCWorld.Holds,
        show (Semiformula.falsum : ArithmeticProposition) = ⊥ from rfl,
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
      change paperPrimeWorld M f (paperPrimeCode true (.rel r v)) ↔
        Semiformula.Evalf f (.rel r v)
      exact paperPrimeWorld_paperPrimeCode M f true (.rel r v)
  | case6 arity r v =>
      change (¬paperPrimeWorld M f (paperPrimeCode true (.rel r v))) ↔
        Semiformula.Evalf f (.nrel r v)
      exact not_congr (paperPrimeWorld_paperPrimeCode M f true (.rel r v))
  | case7 ψ =>
      change paperPrimeWorld M f (paperPrimeCode true (.exs ψ)) ↔
        Semiformula.Evalf f (.exs ψ)
      exact paperPrimeWorld_paperPrimeCode M f true (.exs ψ)
  | case8 ψ =>
      change (¬paperPrimeWorld M f (paperPrimeCode true (.exs (∼ψ)))) ↔
        Semiformula.Evalf f (.all ψ)
      have hall : (Semiformula.all ψ : ArithmeticProposition) = ∼(.exs (∼ψ)) := by
        calc
          Semiformula.all ψ = Semiformula.all (∼∼ψ) :=
            congrArg Semiformula.all (Semiformula.neg_neg ψ).symm
          _ = ∼(Semiformula.exs (∼ψ)) := rfl
      rw [hall, LogicalConnective.HomClass.map_neg]
      exact not_congr (paperPrimeWorld_paperPrimeCode M f true (.exs (∼ψ)))

#print axioms paperPrimeCode_injective
#print axioms paperPrimeDecompose_atom_tag
#print axioms paperPrimeDecompose_semanticPrimeFresh
#print axioms paperPrimeWorld_holds_decompose

end LogicalInduction
