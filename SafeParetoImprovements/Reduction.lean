import SafeParetoImprovements.Game
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Iterated elimination of strictly dominated actions, and its path independence

Assumption 1 removes **one** strictly dominated action at a time.  "Fully reducing" a game
(§4.4.2, §4.4.3, Definition 5) means iterating this until no strictly dominated action
is left, and the paper relies — as game theory does — on the result not depending on the
order of removals.  Appendix D.1's Lemma 19 is the local fact from which path
independence follows ("this lemma does not by itself prove … path independence.  However,
path independence follows from the property shown by this lemma"; the printed text says
"path dependence", erratum D11).

This file carries:

* `Game.Elim Γ Γ'` — `Γ'` arises from `Γ` by removing one strictly dominated action;
  `Game.ElimStar` is its reflexive–transitive closure ("obtained by iterated elimination
  of strictly dominated strategies").
* **Lemma 19** (`isStrictlyDominated_erase`): a strictly dominated action stays strictly
  dominated after removing a *different* strictly dominated action.
* The **diamond property** of single-step elimination, hence confluence
  (`Relation.church_rosser`), hence **uniqueness of the fully reduced game** reachable
  from `Γ` (`reduced_unique`): this is the path independence the paper cites [1, 19, 41].
* `Game.reduce Γ`, the canonical full reduction — defined by well-founded recursion on
  the total number of actions, and characterized by `reduce_reduced`, `elimStar_reduce`
  and `reduce_eq_of_reduced_of_elimStar` — so that Definition 5's "if we fully reduce
  `Γˢ` and `Γ`" and the book construction of §4.4.3 have one canonical object to name.

Games along an elimination chain keep the same payoff function literally
(`Game.erase` is `Game.restrict` with the same `u`), so the uniqueness statement is Lean
equality of games, not merely `Game.EqOn`.
-/

namespace SafeParetoImprovements

open Relation

universe u v

variable {N : Type u} {𝒜 : N → Type v}

namespace Game

/-- Two games with the same action sets and the same (total) payoff function are equal. -/
lemma ext' {Γ Γ' : Game N 𝒜} (hS : Γ.S = Γ'.S) (hu : Γ.u = Γ'.u) : Γ = Γ' := by
  cases Γ; cases Γ'
  cases hS; cases hu
  rfl

section dominance

variable [DecidableEq N]

/-- Strict dominance restricts to subset games with the same payoffs: if `a'` strictly
dominates `a` in `Γ` and both survive in a subset game `Γ'` with `Γ'.u = Γ.u`, then `a'`
strictly dominates `a` in `Γ'`. -/
lemma strictlyDominates_of_subset {Γ Γ' : Game N 𝒜} (hsub : Γ'.IsSubsetGameOf Γ)
    (hu : Γ'.u = Γ.u) {i : N} {a' a : 𝒜 i} (h : Γ.StrictlyDominates i a' a)
    (ha' : a' ∈ Γ'.S i) (ha : a ∈ Γ'.S i) : Γ'.StrictlyDominates i a' a := by
  rw [strictlyDominates_iff] at h ⊢
  refine ⟨ha', ha, fun b hb => ?_⟩
  rw [hu]
  exact h.2.2 b (hsub.profiles_subset hb)

/-- Strict dominance is transitive. -/
lemma StrictlyDominates.trans {Γ : Game N 𝒜} {i : N} {a b c : 𝒜 i}
    (hab : Γ.StrictlyDominates i a b) (hbc : Γ.StrictlyDominates i b c) :
    Γ.StrictlyDominates i a c := by
  rw [strictlyDominates_iff] at hab hbc ⊢
  exact ⟨hab.1, hbc.2.1, fun d hd => (hbc.2.2 d hd).trans (hab.2.2 d hd)⟩

/-- A strictly dominating action is distinct from the action it dominates. -/
lemma StrictlyDominates.ne {Γ : Game N 𝒜} {i : N} {a b : 𝒜 i}
    (h : Γ.StrictlyDominates i a b) : a ≠ b := by
  rintro rfl
  rw [strictlyDominates_iff] at h
  obtain ⟨d, hd⟩ := Γ.profiles_nonempty
  exact lt_irrefl _ (h.2.2 d hd)

end dominance

section elim

variable [DecidableEq N] [∀ i, DecidableEq (𝒜 i)]

lemma erase_S_apply (Γ : Game N 𝒜) (i : N) (ã : 𝒜 i) (h : ((Γ.S i).erase ã).Nonempty) (j : N) :
    (Γ.erase i ã h).S j = if hj : j = i then (hj ▸ (Γ.S i).erase ã) else Γ.S j := by
  by_cases hj : j = i
  · subst hj; simp [erase]
  · simp [erase, hj]

@[simp] lemma erase_S_self (Γ : Game N 𝒜) (i : N) (ã : 𝒜 i) (h : ((Γ.S i).erase ã).Nonempty) :
    (Γ.erase i ã h).S i = (Γ.S i).erase ã := by simp [erase]

lemma erase_S_of_ne (Γ : Game N 𝒜) (i : N) (ã : 𝒜 i) (h : ((Γ.S i).erase ã).Nonempty)
    {j : N} (hj : j ≠ i) : (Γ.erase i ã h).S j = Γ.S j := by
  simp [erase, Function.update_of_ne hj]

@[simp] lemma erase_u (Γ : Game N 𝒜) (i : N) (ã : 𝒜 i) (h : ((Γ.S i).erase ã).Nonempty) :
    (Γ.erase i ã h).u = Γ.u := rfl

/-- **Lemma 19** (path independence of iterated strict dominance): let `a` (of player
`i`) be strictly dominated in `Γ`, and let `Γ'` be obtained from `Γ` by removing a
strictly dominated action `b` (of any player `j`) other than `a` — here: such that `a`
survives in `Γ'`.  Then `a` is strictly dominated in `Γ'`.

Paper node: `Lemma 19` -/
theorem isStrictlyDominated_erase {Γ : Game N 𝒜} {i : N} {a : 𝒜 i}
    (ha : Γ.IsStrictlyDominated i a) {j : N} {b : 𝒜 j} (hb : Γ.IsStrictlyDominated j b)
    (hsurv : a ∈ (Γ.erase j b hb.erase_nonempty).S i) :
    (Γ.erase j b hb.erase_nonempty).IsStrictlyDominated i a := by
  obtain ⟨a', ha'⟩ := ha
  have hsub := Γ.erase_isSubsetGameOf j b hb.erase_nonempty
  by_cases hsurv' : a' ∈ (Γ.erase j b hb.erase_nonempty).S i
  · -- Case 2: the dominating action survives.
    exact ⟨a', strictlyDominates_of_subset hsub rfl ha' hsurv' hsurv⟩
  · -- Case 1: the removed action is `a'` itself, so `j = i` and `b = a'`.
    have hmem : a' ∈ Γ.S i := by
      rw [strictlyDominates_iff] at ha'; exact ha'.1
    have hji : j = i := by
      by_contra hne
      exact hsurv' (by rw [Γ.erase_S_of_ne j b _ (Ne.symm hne)]; exact hmem)
    subst hji
    have hba' : b = a' := by
      by_contra hne
      exact hsurv' (by rw [Γ.erase_S_self]; exact Finset.mem_erase.2 ⟨Ne.symm hne, hmem⟩)
    subst hba'
    obtain ⟨â, hâ⟩ := hb
    refine ⟨â, strictlyDominates_of_subset hsub rfl (hâ.trans ha') ?_ hsurv⟩
    rw [Γ.erase_S_self]
    refine Finset.mem_erase.2 ⟨hâ.ne, ?_⟩
    rw [strictlyDominates_iff] at hâ; exact hâ.1

/-- Single-step elimination: `Γ'` arises from `Γ` by removing one strictly dominated
action. -/
def Elim (Γ Γ' : Game N 𝒜) : Prop :=
  ∃ (i : N) (a : 𝒜 i) (h : Γ.IsStrictlyDominated i a), Γ' = Γ.erase i a h.erase_nonempty

/-- Iterated elimination: the reflexive–transitive closure of `Elim` ("`Γ'` is obtained
from `Γ` by iterated elimination of strictly dominated strategies"). -/
def ElimStar : Game N 𝒜 → Game N 𝒜 → Prop := ReflTransGen Elim

lemma Elim.isSubsetGameOf {Γ Γ' : Game N 𝒜} (h : Γ.Elim Γ') : Γ'.IsSubsetGameOf Γ := by
  obtain ⟨i, a, ha, rfl⟩ := h
  exact Γ.erase_isSubsetGameOf i a _

lemma Elim.u_eq {Γ Γ' : Game N 𝒜} (h : Γ.Elim Γ') : Γ'.u = Γ.u := by
  obtain ⟨i, a, ha, rfl⟩ := h; rfl

lemma ElimStar.isSubsetGameOf {Γ Γ' : Game N 𝒜} (h : Γ.ElimStar Γ') : Γ'.IsSubsetGameOf Γ := by
  induction h with
  | refl => exact IsSubsetGameOf.refl _
  | tail _ hstep ih => exact hstep.isSubsetGameOf.trans ih

lemma ElimStar.u_eq {Γ Γ' : Game N 𝒜} (h : Γ.ElimStar Γ') : Γ'.u = Γ.u := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact hstep.u_eq.trans ih

/-- Removing two distinct dominated actions commutes. -/
lemma erase_erase_comm (Γ : Game N 𝒜) {i : N} {a : 𝒜 i} {j : N} {b : 𝒜 j}
    (ha : Γ.IsStrictlyDominated i a) (hb : Γ.IsStrictlyDominated j b)
    (hab : a ∈ (Γ.erase j b hb.erase_nonempty).S i) (hba : b ∈ (Γ.erase i a ha.erase_nonempty).S j) :
    (Γ.erase j b hb.erase_nonempty).erase i a (isStrictlyDominated_erase ha hb hab).erase_nonempty =
      (Γ.erase i a ha.erase_nonempty).erase j b (isStrictlyDominated_erase hb ha hba).erase_nonempty := by
  have hS : ∀ k, ((Γ.erase j b hb.erase_nonempty).erase i a
      (isStrictlyDominated_erase ha hb hab).erase_nonempty).S k =
      ((Γ.erase i a ha.erase_nonempty).erase j b
      (isStrictlyDominated_erase hb ha hba).erase_nonempty).S k := by
    intro k
    by_cases hki : k = i
    · subst hki
      by_cases hkj : k = j
      · subst hkj
        simp only [erase_S_self]
        exact Finset.erase_right_comm
      · rw [erase_S_self, erase_S_of_ne _ _ _ _ hkj, erase_S_of_ne _ _ _ _ hkj, erase_S_self]
    · by_cases hkj : k = j
      · subst hkj
        rw [erase_S_of_ne _ _ _ _ hki, erase_S_self, erase_S_self, erase_S_of_ne _ _ _ _ hki]
      · rw [erase_S_of_ne _ _ _ _ hki, erase_S_of_ne _ _ _ _ hkj,
          erase_S_of_ne _ _ _ _ hkj, erase_S_of_ne _ _ _ _ hki]
  exact ext' (funext hS) rfl

/-- **Lemma 20** (the diamond property of single-step elimination, from Lemma 19 twice):
if two single eliminations lead from `Γ` to `Γ₁` and to `Γ₂`, then either the two removed
actions coincide and `Γ₁ = Γ₂`, or each of `Γ₁`, `Γ₂` eliminates in one further step to a
common game.  The paper writes the outcome correspondences of Assumption 1 for the
elimination steps; here a step is `Game.Elim`.  The printed first alternative reads
`Γ = Γ̂` (the reduct equal to the game it came from), which its own proof shows must be
`Γ = Γ̃`, the two reducts coinciding (erratum D20); that is what is stated.

Paper node: `Lemma 20` -/
theorem elim_diamond (Γ Γ₁ Γ₂ : Game N 𝒜) (h₁ : Γ.Elim Γ₁) (h₂ : Γ.Elim Γ₂) :
    Γ₁ = Γ₂ ∨ ∃ Γ₃, Γ₁.Elim Γ₃ ∧ Γ₂.Elim Γ₃ := by
  obtain ⟨i, a, ha, rfl⟩ := h₁
  obtain ⟨j, b, hb, rfl⟩ := h₂
  by_cases hab : a ∈ (Γ.erase j b hb.erase_nonempty).S i
  · -- the two removed actions differ, so both can still be removed from the other game
    have hba : b ∈ (Γ.erase i a ha.erase_nonempty).S j := by
      have hbmem : b ∈ Γ.S j := hb.mem
      by_cases hji : j = i
      · subst hji
        rw [erase_S_self]
        refine Finset.mem_erase.2 ⟨fun hba => ?_, hbmem⟩
        subst hba
        rw [erase_S_self] at hab
        exact (Finset.mem_erase.1 hab).1 rfl
      · rw [erase_S_of_ne _ _ _ _ hji]; exact hbmem
    refine Or.inr ⟨(Γ.erase i a ha.erase_nonempty).erase j b
      (isStrictlyDominated_erase hb ha hba).erase_nonempty,
      ⟨j, b, isStrictlyDominated_erase hb ha hba, rfl⟩, ?_⟩
    exact ⟨i, a, isStrictlyDominated_erase ha hb hab, (erase_erase_comm Γ ha hb hab hba).symm⟩
  · -- the same action was removed both times: the two games coincide
    have hamem : a ∈ Γ.S i := ha.mem
    have hji : j = i := by
      by_contra hne
      exact hab (by rw [erase_S_of_ne _ _ _ _ (Ne.symm hne)]; exact hamem)
    subst hji
    have hba : b = a := by
      by_contra hne
      exact hab (by rw [erase_S_self]; exact Finset.mem_erase.2 ⟨Ne.symm hne, hamem⟩)
    subst hba
    exact Or.inl rfl

/-- Lemma 20 in the shape Mathlib's Church–Rosser lemma consumes. -/
lemma elim_diamond_reflGen (Γ Γ₁ Γ₂ : Game N 𝒜) (h₁ : Γ.Elim Γ₁) (h₂ : Γ.Elim Γ₂) :
    ∃ Γ₃, ReflGen Elim Γ₁ Γ₃ ∧ ReflTransGen Elim Γ₂ Γ₃ := by
  rcases elim_diamond Γ Γ₁ Γ₂ h₁ h₂ with rfl | ⟨Γ₃, h₁₃, h₂₃⟩
  · exact ⟨_, ReflGen.refl, ReflTransGen.refl⟩
  · exact ⟨Γ₃, ReflGen.single h₁₃, ReflTransGen.single h₂₃⟩

/-- No elimination step leaves a fully reduced game. -/
lemma Reduced.not_elim {Γ Γ' : Game N 𝒜} (h : Γ.Reduced) : ¬ Γ.Elim Γ' := by
  rintro ⟨i, a, ha, -⟩
  exact h i a ha

lemma Reduced.eq_of_elimStar {Γ Γ' : Game N 𝒜} (h : Γ.Reduced) (hh : Γ.ElimStar Γ') : Γ' = Γ := by
  rcases ReflTransGen.cases_head hh with rfl | ⟨c, hc, -⟩
  · rfl
  · exact absurd hc h.not_elim

/-- **Path independence of iterated strict dominance**: any two fully reduced games
obtained from `Γ` by iterated elimination of strictly dominated actions are equal.  The
paper cites this as well known [1, 19, 41] and gives Lemma 19 as its local core; here it
is Lemma 19 → Lemma 20 (the diamond property) → Church–Rosser. -/
lemma reduced_unique {Γ Γ₁ Γ₂ : Game N 𝒜} (h₁ : Γ.ElimStar Γ₁) (h₂ : Γ.ElimStar Γ₂)
    (r₁ : Γ₁.Reduced) (r₂ : Γ₂.Reduced) : Γ₁ = Γ₂ := by
  obtain ⟨d, hd₁, hd₂⟩ := church_rosser elim_diamond_reflGen h₁ h₂
  exact (r₁.eq_of_elimStar hd₁).symm.trans (r₂.eq_of_elimStar hd₂)

end elim

/-! ### The canonical full reduction -/

section reduce

variable [DecidableEq N] [∀ i, DecidableEq (𝒜 i)]

/-- The total number of actions, the measure that iterated elimination decreases. -/
def size [Fintype N] (Γ : Game N 𝒜) : ℕ := ∑ i, (Γ.S i).card

lemma size_erase_lt [Fintype N] (Γ : Game N 𝒜) (i : N) (ã : 𝒜 i) (h : ((Γ.S i).erase ã).Nonempty)
    (hmem : ã ∈ Γ.S i) : (Γ.erase i ã h).size < Γ.size := by
  unfold size
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : j = i
    · subst hj; rw [erase_S_self]; exact (Finset.card_erase_lt_of_mem hmem).le
    · rw [erase_S_of_ne _ _ _ _ hj]
  · exact ⟨i, Finset.mem_univ _, by rw [erase_S_self]; exact Finset.card_erase_lt_of_mem hmem⟩

/-- A strictly dominated action of a game that is not fully reduced, chosen classically. -/
noncomputable def pickDominated (Γ : Game N 𝒜) (h : ¬ Γ.Reduced) :
    Σ i : N, {a : 𝒜 i // Γ.IsStrictlyDominated i a} :=
  have hex : ∃ i, ∃ a, Γ.IsStrictlyDominated i a := by
    simp only [Reduced, not_forall, not_not] at h; exact h
  ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec⟩

/-- The game after removing the classically chosen dominated action. -/
noncomputable def eraseStep (Γ : Game N 𝒜) (h : ¬ Γ.Reduced) : Game N 𝒜 :=
  Γ.erase (Γ.pickDominated h).1 (Γ.pickDominated h).2.1 (Γ.pickDominated h).2.2.erase_nonempty

lemma elim_eraseStep (Γ : Game N 𝒜) (h : ¬ Γ.Reduced) : Γ.Elim (Γ.eraseStep h) :=
  ⟨_, _, (Γ.pickDominated h).2.2, rfl⟩

lemma size_eraseStep_lt [Fintype N] (Γ : Game N 𝒜) (h : ¬ Γ.Reduced) : (Γ.eraseStep h).size < Γ.size :=
  size_erase_lt Γ _ _ _ (Γ.pickDominated h).2.2.mem

open Classical in
/-- The **canonical full reduction** of `Γ`: remove strictly dominated actions one at a
time until none is left.  The choice of which action to remove at each step is by
`Classical.choice` (`pickDominated`); by `reduced_unique` it does not matter. -/
noncomputable def reduce [Fintype N] (Γ : Game N 𝒜) : Game N 𝒜 :=
  if h : Γ.Reduced then Γ else reduce (Γ.eraseStep h)
termination_by Γ.size
decreasing_by exact Γ.size_eraseStep_lt h

open Classical in
lemma reduce_of_reduced [Fintype N] {Γ : Game N 𝒜} (h : Γ.Reduced) : Γ.reduce = Γ := by
  rw [reduce.eq_def, dif_pos h]

open Classical in
lemma reduce_of_not_reduced [Fintype N] {Γ : Game N 𝒜} (h : ¬ Γ.Reduced) :
    Γ.reduce = (Γ.eraseStep h).reduce := by
  rw [reduce.eq_def, dif_neg h]

/-- `reduce Γ` is reachable from `Γ` by iterated elimination. -/
lemma elimStar_reduce [Fintype N] (Γ : Game N 𝒜) : Γ.ElimStar Γ.reduce := by
  by_cases h : Γ.Reduced
  · rw [reduce_of_reduced h]; exact ReflTransGen.refl
  · rw [reduce_of_not_reduced h]
    exact ReflTransGen.head (Γ.elim_eraseStep h) (elimStar_reduce (Γ.eraseStep h))
termination_by Γ.size
decreasing_by exact Γ.size_eraseStep_lt h

/-- `reduce Γ` contains no strictly dominated action. -/
lemma reduce_reduced [Fintype N] (Γ : Game N 𝒜) : Γ.reduce.Reduced := by
  by_cases h : Γ.Reduced
  · rw [reduce_of_reduced h]; exact h
  · rw [reduce_of_not_reduced h]
    exact reduce_reduced (Γ.eraseStep h)
termination_by Γ.size
decreasing_by exact Γ.size_eraseStep_lt h

/-- The characterisation of the canonical reduction: any fully reduced game obtained from
`Γ` by iterated elimination *is* `reduce Γ`. -/
lemma reduce_eq_of_reduced_of_elimStar [Fintype N] {Γ Γ' : Game N 𝒜} (h : Γ.ElimStar Γ')
    (hr : Γ'.Reduced) : Γ.reduce = Γ' :=
  reduced_unique (elimStar_reduce Γ) h (reduce_reduced Γ) hr

/-- Eliminating a strictly dominated action does not change the full reduction — the fact
the book construction of §4.4.3 needs for Assumption 1. -/
lemma reduce_erase [Fintype N] (Γ : Game N 𝒜) {i : N} {a : 𝒜 i} (ha : Γ.IsStrictlyDominated i a) :
    (Γ.erase i a ha.erase_nonempty).reduce = Γ.reduce :=
  (reduce_eq_of_reduced_of_elimStar
    (ReflTransGen.head ⟨i, a, ha, rfl⟩ (elimStar_reduce _)) (reduce_reduced _)).symm

lemma reduce_isSubsetGameOf [Fintype N] (Γ : Game N 𝒜) : Γ.reduce.IsSubsetGameOf Γ :=
  (elimStar_reduce Γ).isSubsetGameOf

@[simp] lemma reduce_u [Fintype N] (Γ : Game N 𝒜) : Γ.reduce.u = Γ.u := (elimStar_reduce Γ).u_eq

/-! ### Reduction respects the paper's equality of games

`Game.EqOn` (`dd:total-utility`) is the paper's equality: same action sets, same payoffs on
the profiles.  Strict dominance respects it (`strictlyDominates_of_eqOn`), hence so does
every elimination step and the full reduction: `reduce Γ'` is `reduce Γ` with `Γ'`'s payoffs
(`EqOn.reduce_eq_withPayoffs`), in particular `EqOn`-equal to it.  This is what lets a play
family built from reductions be a function of the paper's game rather than of its
presentation (`Play.RespectsEqOn`). -/

section withPayoffs

omit [DecidableEq N] [∀ i, DecidableEq (𝒜 i)]

/-- The game with the action sets of `Γ₁` and the payoffs of `Γ'`. -/
def withPayoffs (Γ₁ Γ' : Game N 𝒜) : Game N 𝒜 where
  S := Γ₁.S
  nonempty := Γ₁.nonempty
  u := Γ'.u

@[simp] lemma withPayoffs_S (Γ₁ Γ' : Game N 𝒜) : (Γ₁.withPayoffs Γ').S = Γ₁.S := rfl
@[simp] lemma withPayoffs_u (Γ₁ Γ' : Game N 𝒜) : (Γ₁.withPayoffs Γ').u = Γ'.u := rfl

end withPayoffs

section eqOn

omit [DecidableEq N] [∀ i, DecidableEq (𝒜 i)] in
/-- Giving a subset game `G` of `Γ` the payoffs of `Γ'` in place of `Γ`'s leaves it
`EqOn`-equal to `G`, when `Γ.EqOn Γ'`. -/
lemma EqOn.withPayoffs_eqOn {Γ Γ' G : Game N 𝒜} (h : Γ.EqOn Γ') (hG : G.IsSubsetGameOf Γ)
    (hu : G.u = Γ.u) : (G.withPayoffs Γ').EqOn G :=
  ⟨rfl, fun a ha i => by rw [withPayoffs_u, hu]; exact (h.2 a (hG.profiles_subset ha) i).symm⟩

lemma withPayoffs_erase {Γ' G : Game N 𝒜} {i : N} {a : 𝒜 i} (h : ((G.S i).erase a).Nonempty)
    (h' : (((G.withPayoffs Γ').S i).erase a).Nonempty) :
    (G.erase i a h).withPayoffs Γ' = (G.withPayoffs Γ').erase i a h' :=
  Game.ext' (funext fun j => by
    by_cases hj : j = i
    · subst hj; rw [withPayoffs_S, Game.erase_S_self, Game.erase_S_self, withPayoffs_S]
    · rw [withPayoffs_S, Game.erase_S_of_ne _ _ _ _ hj, Game.erase_S_of_ne _ _ _ _ hj, withPayoffs_S])
    rfl

/-- Iterated elimination transports across `EqOn`. -/
lemma EqOn.elimStar_withPayoffs {Γ Γ' G : Game N 𝒜} (h : Γ.EqOn Γ') (hE : Γ.ElimStar G) :
    Γ'.ElimStar (G.withPayoffs Γ') := by
  have key : (Γ.withPayoffs Γ').ElimStar (G.withPayoffs Γ') := by
    induction hE with
    | refl => exact Relation.ReflTransGen.refl
    | tail hchain hstep ih =>
      obtain ⟨i, a, hd, rfl⟩ := hstep
      obtain ⟨b, hb⟩ := hd
      have hb' := strictlyDominates_of_eqOn (h.withPayoffs_eqOn (ElimStar.isSubsetGameOf hchain)
        (ElimStar.u_eq hchain)).symm hb
      have hd' : (_ : Game N 𝒜).IsStrictlyDominated i a := ⟨b, hb'⟩
      exact ih.tail ⟨i, a, hd', withPayoffs_erase _ hd'.erase_nonempty⟩
  have hself : Γ.withPayoffs Γ' = Γ' := Game.ext' h.1 rfl
  have transport : ∀ H : Game N 𝒜, H = Γ' → H.ElimStar (G.withPayoffs Γ') →
      Γ'.ElimStar (G.withPayoffs Γ') := fun H hH hE => hH ▸ hE
  exact transport _ hself key

/-- **The full reduction respects the paper's equality of games**: `reduce Γ'` is
`reduce Γ` with `Γ'`'s payoffs. -/
lemma EqOn.reduce_eq_withPayoffs [Fintype N] {Γ Γ' : Game N 𝒜} (h : Γ.EqOn Γ') :
    Γ'.reduce = Γ.reduce.withPayoffs Γ' :=
  reduce_eq_of_reduced_of_elimStar (h.elimStar_withPayoffs Γ.elimStar_reduce)
    ((h.withPayoffs_eqOn Γ.reduce_isSubsetGameOf Γ.reduce_u).reduced_iff.2 Γ.reduce_reduced)

lemma EqOn.reduce_S [Fintype N] {Γ Γ' : Game N 𝒜} (h : Γ.EqOn Γ') : Γ'.reduce.S = Γ.reduce.S := by
  rw [h.reduce_eq_withPayoffs, withPayoffs_S]

lemma EqOn.reduce_eqOn [Fintype N] {Γ Γ' : Game N 𝒜} (h : Γ.EqOn Γ') : Γ.reduce.EqOn Γ'.reduce := by
  rw [h.reduce_eq_withPayoffs]
  exact (h.withPayoffs_eqOn Γ.reduce_isSubsetGameOf Γ.reduce_u).symm

end eqOn

/-! ### The canonical presentation of a game

`Game.canon Γ` zeroes the payoffs outside the profiles: it is `EqOn`-equal to `Γ`, and two
`EqOn`-equal games have the *same* canonical presentation (`EqOn.canon_eq`).  Anything
chosen classically from `Γ.canon` is therefore a function of the paper's game. -/

section canon

omit [DecidableEq N] [∀ i, DecidableEq (𝒜 i)]

open Classical in
/-- The canonical presentation: `Γ` with its payoffs zeroed outside the profiles. -/
noncomputable def canon (Γ : Game N 𝒜) : Game N 𝒜 where
  S := Γ.S
  nonempty := Γ.nonempty
  u a i := if a ∈ Γ.profiles then Γ.u a i else 0

@[simp] lemma canon_S (Γ : Game N 𝒜) : Γ.canon.S = Γ.S := rfl

lemma canon_profiles (Γ : Game N 𝒜) : Γ.canon.profiles = Γ.profiles := rfl

lemma canon_u_of_mem (Γ : Game N 𝒜) {a : ∀ i, 𝒜 i} (ha : a ∈ Γ.profiles) (i : N) :
    Γ.canon.u a i = Γ.u a i := by
  simp [canon, ha]

lemma canon_eqOn (Γ : Game N 𝒜) : Γ.EqOn Γ.canon :=
  ⟨rfl, fun _ ha i => (Γ.canon_u_of_mem ha i).symm⟩

/-- `EqOn`-equal games have the same canonical presentation. -/
lemma EqOn.canon_eq {Γ Γ' : Game N 𝒜} (h : Γ.EqOn Γ') : Γ.canon = Γ'.canon := by
  refine Game.ext' h.1 (funext fun a => funext fun i => ?_)
  simp only [canon]
  have hprof : a ∈ Γ.profiles ↔ a ∈ Γ'.profiles := by simp [Game.profiles, h.1]
  by_cases ha : a ∈ Γ.profiles
  · rw [if_pos ha, if_pos (hprof.1 ha), h.2 a ha i]
  · rw [if_neg ha, if_neg (fun h' => ha (hprof.2 h'))]

end canon

end reduce

end Game

end SafeParetoImprovements
