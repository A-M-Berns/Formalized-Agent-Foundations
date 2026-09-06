import Foundation.FirstOrder.Basic.Syntax.Rew

/-!
# Bound-variable occurrence for semiformulas

Foundation records the bound variables of a *term* (`LO.FirstOrder.Semiterm.bv`) but
offers no occurrence notion for formulas. This module supplies one.

* `Semiformula.Mentions φ k` says that `#k` occurs in `φ`, counted under quantifiers, so
  that `(∀⁰ φ).Mentions k ↔ φ.Mentions (k + 1)`. It comes with a full `@[simp]` equation
  set on the NNF constructors, plus `mentions_neg` for the meta-level involution.
* It rests on two term-level transport lemmas, `Semiterm.rew_eq_of_bvEqOn` and
  `Semiterm.eq_of_rew_eq_of_mem_bv`.
* `rew_eq_of_not_mentions` — rewrites agreeing off `#k` agree on a formula that does not
  mention `#k`.
* `eq_of_rew_eq_of_mentions` — rewrites agreeing on a formula that *does* mention `#k`
  already agree at `#k`.
* The arity-one corollaries are the consumable ones: `subst_injective_of_mentions`
  (substitution into a formula mentioning `#0` is injective) and `subst_eq_of_not_mentions`
  (substitution into one that does not is constant).

They are spent in `Framework/Theory/RepresentsComputations.lean`, where `mentions_zero_of_repr_ne`
discharges the occurrence side condition of the syntactic-separation family
(`representedClaimSentence_ne_of_const_ne`, `conClaimSentence_ne_of_day_ne`).
-/

namespace LO.FirstOrder

variable {L : Language} {ξ : Type*} {n m : ℕ}

private lemma bShift_injective :
    Function.Injective (Rew.bShift : Semiterm L ξ n → Semiterm L ξ (n + 1)) :=
  Rew.map_inj (Fin.succ_injective n) Function.injective_id

/-! ## Occurrence in terms -/

namespace Semiterm

/-- Two rewrites that agree on the bound variables occurring in `t`, and on all free
variables, agree on `t`. -/
lemma rew_eq_of_bvEqOn {t : Semiterm L ξ n} {ω₁ ω₂ : Rew L ξ n ξ m}
    (hb : ∀ x ∈ t.bv, ω₁ #x = ω₂ #x) (hf : ∀ x : ξ, ω₁ &x = ω₂ &x) : ω₁ t = ω₂ t := by
  induction t
  case bvar x => exact hb x (by simp)
  case fvar x => exact hf x
  case func ar f v ih =>
    simp only [Rew.func, func.injEq, heq_eq_eq, true_and]
    funext i
    refine ih i fun x hx ↦ hb x ?_
    rw [bv_func]
    simpa using ⟨i, hx⟩

/-- If `#k` occurs in `t`, two rewrites agreeing on `t` agree at `#k`. -/
lemma eq_of_rew_eq_of_mem_bv {t : Semiterm L ξ n} {k : Fin n} (hk : k ∈ t.bv)
    {ω₁ ω₂ : Rew L ξ n ξ m} (h : ω₁ t = ω₂ t) : ω₁ #k = ω₂ #k := by
  induction t
  case bvar x =>
    rw [bv_bvar, Finset.mem_singleton] at hk
    subst hk
    exact h
  case fvar x => simp at hk
  case func ar f v ih =>
    rw [bv_func] at hk
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hk
    obtain ⟨i, hi⟩ := hk
    refine ih i hi ?_
    simp only [Rew.func, func.injEq, heq_eq_eq, true_and] at h
    exact congrFun h i

end Semiterm

namespace Semiformula

/-! ## Occurrence in formulas -/

/-- `φ.Mentions k` : the bound variable `#k` occurs in `φ`, counting under quantifiers,
so that `(∀⁰ φ).Mentions k ↔ φ.Mentions (k + 1)`. -/
def Mentions : {n : ℕ} → Semiformula L ξ n → ℕ → Prop
  | _,        ⊤, _ => False
  | _,        ⊥, _ => False
  | _,  rel _ v, k => ∃ i, ∃ x ∈ (v i).bv, (x : ℕ) = k
  | _, nrel _ v, k => ∃ i, ∃ x ∈ (v i).bv, (x : ℕ) = k
  | _,    φ ⋏ ψ, k => φ.Mentions k ∨ ψ.Mentions k
  | _,    φ ⋎ ψ, k => φ.Mentions k ∨ ψ.Mentions k
  | _,     ∀⁰ φ, k => φ.Mentions (k + 1)
  | _,     ∃⁰ φ, k => φ.Mentions (k + 1)

@[simp] lemma mentions_verum {k : ℕ} : ¬(⊤ : Semiformula L ξ n).Mentions k := id

@[simp] lemma mentions_falsum {k : ℕ} : ¬(⊥ : Semiformula L ξ n).Mentions k := id

@[simp] lemma mentions_rel {ar : ℕ} (r : L.Rel ar) (v : Fin ar → Semiterm L ξ n) (k : ℕ) :
    (rel r v).Mentions k ↔ ∃ i, ∃ x ∈ (v i).bv, (x : ℕ) = k := Iff.rfl

@[simp] lemma mentions_nrel {ar : ℕ} (r : L.Rel ar) (v : Fin ar → Semiterm L ξ n) (k : ℕ) :
    (nrel r v).Mentions k ↔ ∃ i, ∃ x ∈ (v i).bv, (x : ℕ) = k := Iff.rfl

@[simp] lemma mentions_and (φ ψ : Semiformula L ξ n) (k : ℕ) :
    (φ ⋏ ψ).Mentions k ↔ φ.Mentions k ∨ ψ.Mentions k := Iff.rfl

@[simp] lemma mentions_or (φ ψ : Semiformula L ξ n) (k : ℕ) :
    (φ ⋎ ψ).Mentions k ↔ φ.Mentions k ∨ ψ.Mentions k := Iff.rfl

@[simp] lemma mentions_all (φ : Semiformula L ξ (n + 1)) (k : ℕ) :
    (∀⁰ φ).Mentions k ↔ φ.Mentions (k + 1) := Iff.rfl

@[simp] lemma mentions_exs (φ : Semiformula L ξ (n + 1)) (k : ℕ) :
    (∃⁰ φ).Mentions k ↔ φ.Mentions (k + 1) := Iff.rfl

@[simp] lemma mentions_neg {φ : Semiformula L ξ n} {k : ℕ} :
    (∼φ).Mentions k ↔ φ.Mentions k := by
  induction φ using rec' generalizing k <;> simp [*]

/-! ## Rewrites that agree off an occurrence -/

private lemma rew_eq_aux : ∀ {n : ℕ} (φ : Semiformula L ξ n) (m k : ℕ)
    (ω₁ ω₂ : Rew L ξ n ξ m), ¬φ.Mentions k →
      (∀ x : Fin n, (x : ℕ) ≠ k → ω₁ #x = ω₂ #x) → (∀ x : ξ, ω₁ &x = ω₂ &x) →
      ω₁ ▹ φ = ω₂ ▹ φ := by
  intro n φ
  induction φ using rec'
  case hverum => intro m k ω₁ ω₂ _ _ _; simp
  case hfalsum => intro m k ω₁ ω₂ _ _ _; simp
  case hrel n ar r v =>
    intro m k ω₁ ω₂ hk hb hf
    simp only [rew_rel, rel.injEq, heq_eq_eq, true_and]
    funext i
    exact Semiterm.rew_eq_of_bvEqOn (fun x hx ↦ hb x fun e ↦ hk ⟨i, x, hx, e⟩) hf
  case hnrel n ar r v =>
    intro m k ω₁ ω₂ hk hb hf
    simp only [rew_nrel, nrel.injEq, heq_eq_eq, true_and]
    funext i
    exact Semiterm.rew_eq_of_bvEqOn (fun x hx ↦ hb x fun e ↦ hk ⟨i, x, hx, e⟩) hf
  case hand n φ ψ ihφ ihψ =>
    intro m k ω₁ ω₂ hk hb hf
    simp only [LogicalConnective.HomClass.map_and, and_inj]
    exact ⟨ihφ m k ω₁ ω₂ (fun h ↦ hk (Or.inl h)) hb hf,
      ihψ m k ω₁ ω₂ (fun h ↦ hk (Or.inr h)) hb hf⟩
  case hor n φ ψ ihφ ihψ =>
    intro m k ω₁ ω₂ hk hb hf
    simp only [LogicalConnective.HomClass.map_or, or_inj]
    exact ⟨ihφ m k ω₁ ω₂ (fun h ↦ hk (Or.inl h)) hb hf,
      ihψ m k ω₁ ω₂ (fun h ↦ hk (Or.inr h)) hb hf⟩
  case hall n φ ih =>
    intro m k ω₁ ω₂ hk hb hf
    simp only [Rewriting.app_all, all_inj]
    refine ih (m + 1) (k + 1) ω₁.q ω₂.q hk ?_ fun x ↦ by simp [hf x]
    intro x hx
    cases x using Fin.cases with
    | zero => simp
    | succ i =>
      have hik : (i : ℕ) ≠ k := fun e ↦ hx (by simp [e])
      simp [hb i hik]
  case hexs n φ ih =>
    intro m k ω₁ ω₂ hk hb hf
    simp only [Rewriting.app_exs, exs_inj]
    refine ih (m + 1) (k + 1) ω₁.q ω₂.q hk ?_ fun x ↦ by simp [hf x]
    intro x hx
    cases x using Fin.cases with
    | zero => simp
    | succ i =>
      have hik : (i : ℕ) ≠ k := fun e ↦ hx (by simp [e])
      simp [hb i hik]

/-- If `#k` does not occur in `φ`, two rewrites that agree off `#k` — and on all free
variables — agree on `φ`. -/
lemma rew_eq_of_not_mentions {n m : ℕ} {φ : Semiformula L ξ n} {k : ℕ}
    (hk : ¬φ.Mentions k) {ω₁ ω₂ : Rew L ξ n ξ m}
    (hb : ∀ x : Fin n, (x : ℕ) ≠ k → ω₁ #x = ω₂ #x)
    (hf : ∀ x : ξ, ω₁ &x = ω₂ &x) :
    ω₁ ▹ φ = ω₂ ▹ φ :=
  rew_eq_aux φ m k ω₁ ω₂ hk hb hf

/-! ## Substitution injectivity -/

private lemma eq_of_rew_eq_aux : ∀ {n : ℕ} (φ : Semiformula L ξ n) (m : ℕ) (k : Fin n)
    (ω₁ ω₂ : Rew L ξ n ξ m), φ.Mentions (k : ℕ) → ω₁ ▹ φ = ω₂ ▹ φ → ω₁ #k = ω₂ #k := by
  intro n φ
  induction φ using rec'
  case hverum => intro m k ω₁ ω₂ hk _; exact hk.elim
  case hfalsum => intro m k ω₁ ω₂ hk _; exact hk.elim
  case hrel n ar r v =>
    intro m k ω₁ ω₂ hk h
    obtain ⟨i, x, hx, hxk⟩ := hk
    have hxk' : x = k := Fin.val_injective hxk
    subst hxk'
    refine Semiterm.eq_of_rew_eq_of_mem_bv hx ?_
    simp only [rew_rel, rel.injEq, heq_eq_eq, true_and] at h
    exact congrFun h i
  case hnrel n ar r v =>
    intro m k ω₁ ω₂ hk h
    obtain ⟨i, x, hx, hxk⟩ := hk
    have hxk' : x = k := Fin.val_injective hxk
    subst hxk'
    refine Semiterm.eq_of_rew_eq_of_mem_bv hx ?_
    simp only [rew_nrel, nrel.injEq, heq_eq_eq, true_and] at h
    exact congrFun h i
  case hand n φ ψ ihφ ihψ =>
    intro m k ω₁ ω₂ hk h
    simp only [LogicalConnective.HomClass.map_and, and_inj] at h
    rcases hk with hk | hk
    · exact ihφ m k ω₁ ω₂ hk h.1
    · exact ihψ m k ω₁ ω₂ hk h.2
  case hor n φ ψ ihφ ihψ =>
    intro m k ω₁ ω₂ hk h
    simp only [LogicalConnective.HomClass.map_or, or_inj] at h
    rcases hk with hk | hk
    · exact ihφ m k ω₁ ω₂ hk h.1
    · exact ihψ m k ω₁ ω₂ hk h.2
  case hall n φ ih =>
    intro m k ω₁ ω₂ hk h
    simp only [Rewriting.app_all, all_inj] at h
    have hk' : φ.Mentions ((k.succ : Fin (n + 1)) : ℕ) := by simpa using hk
    have := ih (m + 1) k.succ ω₁.q ω₂.q hk' h
    simp only [Rew.q_bvar_succ] at this
    exact bShift_injective this
  case hexs n φ ih =>
    intro m k ω₁ ω₂ hk h
    simp only [Rewriting.app_exs, exs_inj] at h
    have hk' : φ.Mentions ((k.succ : Fin (n + 1)) : ℕ) := by simpa using hk
    have := ih (m + 1) k.succ ω₁.q ω₂.q hk' h
    simp only [Rew.q_bvar_succ] at this
    exact bShift_injective this

/-- **Substitution injectivity, general form.** If `#k` occurs in `φ` and two rewrites
agree on `φ`, then they agree at `#k`. -/
lemma eq_of_rew_eq_of_mentions {n m : ℕ} {φ : Semiformula L ξ n} {k : Fin n}
    (hk : φ.Mentions k) {ω₁ ω₂ : Rew L ξ n ξ m} (h : ω₁ ▹ φ = ω₂ ▹ φ) :
    ω₁ #k = ω₂ #k :=
  eq_of_rew_eq_aux φ m k ω₁ ω₂ hk h

/-- **Substitution injectivity.** Substituting into a formula that mentions `#0` is
injective in the substituted term. -/
lemma subst_injective_of_mentions {σ : Semiformula L ξ 1} (hσ : σ.Mentions 0)
    {t t' : Semiterm L ξ 0} (h : σ/[t] = σ/[t']) : t = t' := by
  have := eq_of_rew_eq_of_mentions (k := (0 : Fin 1)) (by simpa using hσ) h
  simpa using this

/-- Substituting into a formula that does not mention `#0` is constant. -/
lemma subst_eq_of_not_mentions {σ : Semiformula L ξ 1} (hσ : ¬σ.Mentions 0)
    (t t' : Semiterm L ξ 0) : σ/[t] = σ/[t'] :=
  rew_eq_of_not_mentions hσ (fun x hx ↦ absurd (Nat.lt_one_iff.mp x.isLt) hx)
    fun x ↦ by simp

end Semiformula

end LO.FirstOrder
