module

public import ProvabilityLogic.Formula.Substitution

/-!
# Modalized formulas

This file collects purely syntactic notions around *modalization* of a `Formula`:

- `Formula.ModalizedIn`: `p` occurs only in the scope of `□` in `A` (termed "`p` is modalized
  in `A`" in the source).
- `Formula.Modalized`: every atom of `A` is modalized in `A`.
- `Formula.modalize`: replace every non-modalized atom of `A` by `⊥`, turning `A` into a
  `Modalized` formula.

- [SV82]
-/

@[expose]
public section

open scoped Formula

variable {α : Type u} [DecidableEq α]

namespace Formula

variable {p q : α} {A B C : Formula α}

/-- `p` occurs only in the scope of `□` in `A` (termed "`p` is modalized in `A`" in the source).

- [SV82]
-/
@[grind]
def ModalizedIn (p : α) : Formula α → Prop
  | .atom a    => a ≠ p
  | .bot     => True
  | .imp A B => A.ModalizedIn p ∧ B.ModalizedIn p
  | .box _    => True

lemma ModalizedIn.of_not_mem_atoms (h : p ∉ A.atoms) : A.ModalizedIn p := by
  induction A <;> grind [atoms]

omit [DecidableEq α] in
@[simp] lemma ModalizedIn.box : (□A).ModalizedIn p := by simp [ModalizedIn]

/-- Substituting fresh `q` for a modalized `p` yields a formula in which `q` is modalized. -/
lemma ModalizedIn.subst_single (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    (A⟦p ↦ #q⟧).ModalizedIn q := by
  induction A <;> grind [atoms, ModalizedIn]

/-- `A` is modalized: every atom of `A` occurs within the scope of a `□`. -/
abbrev Modalized (A : Formula α) : Prop := ∀ a, A.ModalizedIn a

/--
Replace every non-modalized (top-level, unboxed) atom of `A` by `⊥`, keeping the
maximal boxed subformulas. Turns `f(□C₁, …, □Cₙ, p₁, …, pₘ)` into
`f(□C₁, …, □Cₙ, ⊥, …, ⊥)`.

- [Bek89, Lemma 11]
-/
@[grind]
def modalize : Formula α → Formula α
  | .atom _    => ⊥
  | .bot     => ⊥
  | .imp A B => A.modalize 🡒 B.modalize
  | .box A    => □A

omit [DecidableEq α] in
/-- The modalization of any formula is `Modalized`. -/
@[simp, grind .]
lemma modalized_modalize : A.modalize.Modalized := by
  intro a; induction A <;> grind;

/-- Modalization only removes atoms. -/
@[simp, grind .]
lemma atoms_modalize_subset : A.modalize.atoms ⊆ A.atoms := by
  induction A <;> grind;

end Formula
