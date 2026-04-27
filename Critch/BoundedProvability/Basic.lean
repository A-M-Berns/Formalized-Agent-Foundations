/-
  Bounded provability abstractions for Critch 2019.

  This file will contain the bounded provability predicate and bounded HBL
  assumptions used in the abstract proof of Theorems 1 and 2.
-/

import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic

namespace LO

open LO.Entailment

namespace FirstOrder
namespace Critch

variable {L₀ L : Language}

structure BoundedProvability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  prov : ℕ → Semisentence L₀ 1

namespace BoundedProvability

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

@[coe] def pr (𝔅 : BoundedProvability T₀ T) (e : ℕ) (σ : Sentence L) :
    Sentence L₀ :=
  (𝔅.prov e)/[⌜σ⌝]

instance : CoeFun (BoundedProvability T₀ T) (fun _ ↦ ℕ → Sentence L → Sentence L₀) :=
  ⟨pr⟩

class Monotone (𝔅 : BoundedProvability T₀ T) where
  mono {e e' : ℕ} (h : e ≤ e') {σ : Sentence L} : T₀ ⊢ 𝔅 e σ 🡒 𝔅 e' σ

export Monotone (mono)

class BoundedD1 (𝔅 : BoundedProvability T₀ T) where
  D1 {σ : Sentence L} : T ⊢ σ → ∃ e, T₀ ⊢ 𝔅 e σ

export BoundedD1 (D1)

class BoundedD2 (𝔅 : BoundedProvability T₀ T) (mpBound : ℕ → ℕ → ℕ) where
  D2 {e₁ e₂ : ℕ} {σ τ : Sentence L} :
    T₀ ⊢ 𝔅 e₁ (σ 🡒 τ) 🡒 𝔅 e₂ σ 🡒 𝔅 (mpBound e₁ e₂) τ

export BoundedD2 (D2)

variable [L.ReferenceableBy L] {T₀ T : Theory L}

class BoundedD3 (𝔅 : BoundedProvability T₀ T) (boxBound : ℕ → ℕ) where
  D3 {e : ℕ} {σ : Sentence L} : T₀ ⊢ 𝔅 e σ 🡒 𝔅 (boxBound e) (𝔅 e σ)

export BoundedD3 (D3)

end BoundedProvability
end Critch
end FirstOrder
end LO
