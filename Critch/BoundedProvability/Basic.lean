/-
  Bounded provability abstractions for Critch 2019, Definition 1.

  This file will contain the bounded provability predicate and bounded HBL
  assumptions used in the abstract proof of Theorems 1 and 2.
-/

import Critch.BoundedProvability.Asymp
import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic

namespace LO

open LO.Entailment

namespace FirstOrder
namespace Critch

variable {L₀ L : Language}

/--
Bounded provability predicate family.

This mirrors Foundation's `Provability` structure, with the box indexed by a
meta-level proof bound. The `bew_def` field is the bounded D1 direction used to
turn an ordinary proof into some bounded proof.
-/
structure BoundedProvability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  bprov : Nat → Semisentence L₀ 1
  /-- Bounded D1: a proof in `T` has some bounded proof predicate in `T₀`. -/
  bew_def {σ : Sentence L} : T ⊢ σ → ∃ k, T₀ ⊢ (bprov k)/[⌜σ⌝]

namespace BoundedProvability

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

/-- Apply a bounded provability predicate at bound `k` to a sentence. -/
@[coe] def pr (𝔅 : BoundedProvability T₀ T) (k : Nat) (σ : Sentence L) :
    Sentence L₀ :=
  (𝔅.bprov k)/[⌜σ⌝]

/-- Coerce `𝔅` to its two-argument bounded-box operation. -/
instance : CoeFun (BoundedProvability T₀ T) (fun _ ↦ Nat → Sentence L → Sentence L₀) :=
  ⟨pr⟩

/-- Notation for the bounded box at meta-level bound `k`. -/
notation:90 𝔅 "[" k "]" σ => BoundedProvability.pr 𝔅 k σ

/-- Bounded D1 from the `BoundedProvability` structure. -/
lemma D1 {𝔅 : BoundedProvability T₀ T} {σ : Sentence L} :
    T ⊢ σ → ∃ k, T₀ ⊢ 𝔅 k σ :=
  𝔅.bew_def

/--
Critch §4, Property 1: bounded implication distribution.

The bound arithmetic is meta-level arithmetic on the indices of the bounded box.
-/
class BImpDistr (𝔅 : BoundedProvability T₀ T) where
  c : Nat
  impDistr {a b : Nat} {σ τ : Sentence L} :
    T₀ ⊢ 𝔅 a (σ 🡒 τ) 🡒 𝔅 b σ 🡒 𝔅 (a + b + c) τ

export BImpDistr (c impDistr)

/--
Critch §4, Property 2: bounded quantifier distribution.

The premise and conclusion are meta-level implications between provability
claims. The object-level universal is specialized at the meta-natural `k`, and
the resulting bound is computed externally as `C + 2 * N + lg k`.
-/
class BQuantDistr [L.Zero] [L.One] [L.Add] (𝔅 : BoundedProvability T₀ T) where
  C : Nat
  quantDistr {N k : Nat} {φ : Semisentence L 1} :
    T₀ ⊢ 𝔅 N (∀⁰ φ : Sentence L) →
      T₀ ⊢ 𝔅 (C + 2 * N + lg k) (φ/[.numeral k] : Sentence L)

export BQuantDistr (C quantDistr)

variable [L.ReferenceableBy L] {T₀ T : Theory L}

/--
Critch §4, Property 3: bounded necessitation.

The threshold is existential, matching the paper's use of a formula-dependent
proof bound without exposing a global proof-length oracle.
-/
class BNec (𝔅 : BoundedProvability T₀ T) where
  nec {σ : Sentence L} : T₀ ⊢ σ → ∃ k₀, ∀ k, k₀ ≤ k → T₀ ⊢ 𝔅 k σ

export BNec (nec)

/--
Critch §4, Property 4: bounded inner necessitation.

The field `expand` is Critch's proof-expansion function.
-/
class BInnerNec (𝔅 : BoundedProvability T₀ T) where
  expand : Nat → Nat
  innerNec {k : Nat} {σ : Sentence L} : T₀ ⊢ 𝔅 k σ 🡒 𝔅 (expand k) (𝔅 k σ)

export BInnerNec (expand innerNec)

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

/--
Bound monotonicity for bounded provability.

Critch uses this implicitly when replacing a bounded proof claim by the same
claim at a larger bound.
-/
class BMono (𝔅 : BoundedProvability T₀ T) where
  mono {a b : Nat} (h : a ≤ b) {σ : Sentence L} : T₀ ⊢ 𝔅 a σ 🡒 𝔅 b σ

export BMono (mono)

variable [L.ReferenceableBy L] [L.Zero] [L.One] [L.Add] {T₀ T : Theory L}

/--
Convenience bundle for the bounded derivability assumptions used in Critch §4.

The separate classes above remain the primary interface; this bundle is only for
theorems that need the full collection.
-/
class BHBL (𝔅 : BoundedProvability T₀ T) extends
    𝔅.BImpDistr, 𝔅.BQuantDistr, 𝔅.BNec, 𝔅.BInnerNec, 𝔅.BMono

end BoundedProvability
end Critch
end FirstOrder
end LO
