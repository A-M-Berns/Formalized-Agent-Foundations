module

public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import ProvabilityLogic.Logic.GL.Basic

@[expose] public section

open scoped Formula

open LO
open LO.FirstOrder.ProvabilityAbstraction

variable {α : Type*}
variable {L : FirstOrder.Language} [L.ReferenceableBy L] {T₀ T U : FirstOrder.Theory L} {𝔅 : Provability T₀ T}

/-- A realization mapping modal propositional variables to first-order sentences. -/
structure Realization (α : Type*) (𝔅 : Provability T₀ T) where
  val : α → FirstOrder.Sentence L

abbrev StandardRealization (α : Type*) (T : FirstOrder.ArithmeticTheory) [T.Δ₁] := Realization α T.standardProvability


namespace Formula

@[grind]
def interpret (f : Realization α 𝔅) : Formula α → FirstOrder.Sentence L
  | .atom a    => f.val a
  | .bot     => ⊥
  | .imp A B => (A.interpret f) 🡒 (B.interpret f)
  | .box A    => 𝔅 (A.interpret f)

instance : CoeFun (Realization α 𝔅) (fun _ ↦ Formula α → FirstOrder.Sentence L) := ⟨interpret⟩

variable {f : Realization α 𝔅} {A : Formula α}

@[simp, grind =]
lemma interpret_boxItr {n : ℕ} : (□^[n]A).interpret f = 𝔅^[n] (f A) := by
  induction n with
  | zero => simp [Formula.boxItr];
  | succ n ih => simp only [boxItr, Function.iterate_succ_apply', interpret, ih];

end Formula


section interpret_map

variable {β : Type*}

/-- Interpreting a renamed formula is interpreting under the pulled-back realization. -/
lemma Formula.interpret_map {f : Realization β 𝔅} {g : α → β} {A : Formula α} :
    Formula.interpret f (A.map g) = Formula.interpret (⟨f.val ∘ g⟩ : Realization α 𝔅) A := by
  induction A with
  | atom a => rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [Formula.subst_imp, Formula.interpret, ihA, ihB]
  | box A ih => simp only [Formula.subst_box, Formula.interpret, ih]

/-- Two realizations agreeing on the atoms of `A` interpret `A` identically. -/
lemma Formula.interpret_congr_atoms [DecidableEq α] {f₁ f₂ : Realization α 𝔅} {A : Formula α}
    (h : ∀ a ∈ A.atoms, f₁.val a = f₂.val a) :
    Formula.interpret f₁ A = Formula.interpret f₂ A := by
  induction A with
  | atom a => exact h a (by simp [Formula.atoms])
  | bot => rfl
  | imp A B ihA ihB =>
    simp only [Formula.interpret];
    rw [ihA (fun a ha => h a (by simp [Formula.atoms, ha])),
      ihB (fun a ha => h a (by simp [Formula.atoms, ha]))];
  | box A ih =>
    simp only [Formula.interpret];
    rw [ih (fun a ha => h a (by simpa [Formula.atoms] using ha))];

/-- Interpreting a substituted formula is interpreting under the realization composed with
the substitution's own interpretation. -/
lemma Formula.interpret_subst {f : Realization α 𝔅} {s : Formula.Substitution α α} {A : Formula α} :
    Formula.interpret f (A⟦s⟧) = Formula.interpret (⟨fun a => Formula.interpret f (s a)⟩ : Realization α 𝔅) A := by
  induction A with
  | atom a => rfl
  | _ => simp_all [Formula.interpret, Formula.subst_imp, Formula.subst_box]

/-- Realizations that agree on every atom up to `T₀`-provable equivalence interpret every
formula equivalently. -/
lemma Formula.interpret_iff_congr [L.DecidableEq] [T₀ ⪯ T] [𝔅.Ext] {f₁ f₂ : Realization α 𝔅}
    (h : ∀ a, T₀ ⊢ (f₁.val a) 🡘 (f₂.val a)) (A : Formula α) :
    T₀ ⊢ (f₁ A) 🡘 (f₂ A) := by
  induction A with
  | atom a => exact h a
  | bot => dsimp [Formula.interpret]; cl_prover
  | imp A B ihA ihB => dsimp [Formula.interpret]; cl_prover [ihA, ihB]
  | box A ih => exact 𝔅.ext' ih

end interpret_map


section compact

/-- Compactness: a proof from a theory factors through a finite subtheory, presented as a
finite conjunction implying the goal. -/
private lemma _root_.LO.FirstOrder.Theory.compact_conj
    {L : FirstOrder.Language} [L.DecidableEq] {T : FirstOrder.Theory L} {φ : FirstOrder.Sentence L}
    (h : T ⊢ φ) : ∃ (s : { s : Finset (FirstOrder.Sentence L) // ↑s ⊆ T }), (∅ : FirstOrder.Theory L) ⊢ s.1.conj 🡒 φ := by
  obtain ⟨𝓕, h𝓕sub, h𝓕fin, h𝓕⟩ := LO.Entailment.Compact.finite_provable h
  have h𝓕fin' : 𝓕.Finite := by simpa using h𝓕fin
  set s : Finset (FirstOrder.Sentence L) := h𝓕fin'.toFinset with hs_def
  have hcoe : (↑s : FirstOrder.Theory L) = 𝓕 := h𝓕fin'.coe_toFinset
  have h𝓕' : (↑s : FirstOrder.Theory L) ⊢ φ := by rw [hcoe]; exact h𝓕
  have H : (↑(insert s.conj ∅ : FirstOrder.Theory L)) ⊢* (↑s : FirstOrder.Theory L) := by
    intro ψ hψ
    exact LO.Entailment.left_Fconj!_intro (by simpa using hψ) ⨀ (LO.Entailment.by_axm (by simp))
  exact ⟨⟨s, hcoe ▸ h𝓕sub⟩,
    LO.Entailment.Deduction.of_insert!
      (LO.Entailment.StrongCut.cut! (𝓣 := (↑s : FirstOrder.Theory L)) H h𝓕')⟩

/-- Compactness for a theory union, isolating the contribution of `U`. -/
lemma _root_.LO.FirstOrder.Theory.compact_add_right
    {L : FirstOrder.Language} [L.DecidableEq] {T U : FirstOrder.Theory L}
    [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)] {φ : FirstOrder.Sentence L}
    (h : (T ∪ U) ⊢ φ) : ∃ (s : { s : Finset (FirstOrder.Sentence L) // ↑s ⊆ U }), T ⊢ s.1.conj 🡒 φ := by
  obtain ⟨⟨s, hsTU⟩, hs⟩ := LO.FirstOrder.Theory.compact_conj h;
  let sT := { ψ ∈ s | ψ ∈ T };
  let sU := { ψ ∈ s | ψ ∈ U };
  use ⟨sU, λ _ => by simp [sU]⟩;
  have : (∅ : FirstOrder.Theory _) ⊢ sT.conj 🡒 sU.conj 🡒 φ := LO.Entailment.CK!_iff_CC!.mp $ LO.Entailment.C!_trans LO.Entailment.CKFconjFconjUnion! $ by
    have : sT ∪ sU = s:= by
      ext ψ;
      constructor;
      . grind;
      . intro hψ; rcases hsTU hψ with (hψT | hψU) <;> grind;
    rwa [this];
  apply LO.Entailment.mdp! $ LO.Entailment.Axiomatized.weakening! (λ _ => by simp) this;
  apply LO.Entailment.FConj!_iff_forall_provable.mpr;
  intro ψ hψ;
  apply LO.Entailment.by_axm;
  simp_all [sT];

/-- Compactness for a theory union, isolating the contribution of `T`. -/
lemma _root_.LO.FirstOrder.Theory.compact_add_left
    {L : FirstOrder.Language} [L.DecidableEq] {T U : FirstOrder.Theory L}
    [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)] {φ : FirstOrder.Sentence L}
    (h : (T ∪ U) ⊢ φ) : ∃ (s : { s : Finset (FirstOrder.Sentence L) // ↑s ⊆ T }), U ⊢ s.1.conj 🡒 φ := by
  rw [show (T ∪ U = U ∪ T) from Set.union_comm T U] at h
  simpa using LO.FirstOrder.Theory.compact_add_right h;

end compact


abbrev LetterlessRealization (𝔅 : Provability T₀ T) := Realization Empty 𝔅

namespace LetterlessFormula

variable {A B : LetterlessFormula} {f f₁ f₂ : LetterlessRealization 𝔅}

@[grind .]
lemma eq_interpret : f₁ A = f₂ A := by induction A <;> grind;

@[grind .]
lemma iff_provable_interpret : T ⊢ f₁ A ↔ T ⊢ f₂ A := by
  rw [eq_interpret];

end LetterlessFormula



@[grind]
def LO.FirstOrder.ArithmeticTheory.provabilityLogicRelativeTo (T U : FirstOrder.ArithmeticTheory) [T.Δ₁] : Logic α := {A | ∀ f : StandardRealization α T, U ⊢ f A}

abbrev LO.FirstOrder.ArithmeticTheory.provabilityLogic (T : FirstOrder.ArithmeticTheory) [T.Δ₁] : Logic α := T.provabilityLogicRelativeTo T



end
