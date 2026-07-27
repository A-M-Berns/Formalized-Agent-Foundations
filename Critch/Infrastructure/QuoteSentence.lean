/-
  Sentence-level quote-commutation lemmas.

  Foundation proves quote/connective commutation for *syntactic* semiformulas but
  does not restate it for `Sentence`-level (closed, `Empty`-variable) quotes, which
  is the form arithmetized-provability arguments consume. These three lemmas fill
  that gap; they are paper-independent and are **Foundation-upstream candidates**
  (surfaced by audit finding R1-F13).

  All three are measure-independent vocabulary: each is `simp [Sentence.quote_eq]`.
-/

import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Coding

namespace LO.FirstOrder

open Arithmetic ISigma1 Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- The untyped code of a negated sentence is `Bootstrapping.neg` of its code.
Foundation-upstream candidate (Sentence-level companion to
`Semiformula.quote_neg`-style facts).

Paper node: infrastructure — no paper node; Foundation-upstream candidate (R1-F13). -/
lemma quote_neg_sentence (φ : Sentence L) :
    (⌜(∼φ : Sentence L)⌝ : V) = Bootstrapping.neg L ⌜φ⌝ := by
  simp [Sentence.quote_eq]

/-- The untyped code of a conjunction of sentences is the `^⋏` of their codes.
Foundation-upstream candidate.

Paper node: infrastructure — no paper node; Foundation-upstream candidate (R1-F13). -/
lemma quote_and_sentence (φ ψ : Sentence L) :
    (⌜(φ ⋏ ψ : Sentence L)⌝ : V) = (⌜φ⌝ : V) ^⋏ (⌜ψ⌝ : V) := by
  simp [Sentence.quote_eq]

/-- The untyped code of a disjunction of sentences is the `^⋎` of their codes.
Foundation-upstream candidate.

Paper node: infrastructure — no paper node; Foundation-upstream candidate (R1-F13). -/
lemma quote_or_sentence (φ ψ : Sentence L) :
    (⌜(φ ⋎ ψ : Sentence L)⌝ : V) = (⌜φ⌝ : V) ^⋎ (⌜ψ⌝ : V) := by
  simp [Sentence.quote_eq]

end LO.FirstOrder
