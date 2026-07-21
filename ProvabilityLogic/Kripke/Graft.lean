module

public import ProvabilityLogic.Kripke.Rank
public import ProvabilityLogic.Kripke.ReflexiveWorld

@[expose]
public section

open scoped Formula

variable [Nonempty κ]

namespace RootedModel

variable {M : RootedModel κ α}

lemma not_rel_root [IsTrans _ M.Rel] [Std.Irrefl M.Rel] {x : M.World} : ¬x ≺ M.root.1 := by
  intro h;
  by_cases hx : x = M.root.1;
  . subst hx; exact Std.Irrefl.irrefl _ h;
  . exact Std.Irrefl.irrefl x $ IsTrans.trans _ _ _ h (M.root.2 x hx);

/-- Worlds of the grafted model: the original worlds plus a chain of length `k`. -/
abbrev graft.World (M : RootedModel κ α) (k : ℕ) : Type _ := M.World ⊕ Fin k

/--
  The rooted model obtained by grafting a chain of length `k` between the root and `a`
  (`root ≺ chain ≺ a` and its cone): a "bone lengthening" construction. Hanging the chain
  directly below the root keeps the rank of every world other than the root unchanged, so that
  the height is exactly `max M.height (a.rank + k + 1)`.

  - [AB05, Lemma 12]
-/
abbrev graft (M : RootedModel κ α) (a : M.NonRoot) (k : ℕ) : RootedModel (graft.World M k) α where
  Rel' x y :=
    match x, y with
    | .inl x, .inl y => M.Rel x y
    | .inl x, .inr _ => x = M.root.1
    | .inr _, .inl y => y = a.1 ∨ M.Rel a.1 y
    | .inr i, .inr j => j < i
  Val' x p :=
    match x with
    | .inl x => M.Val x p
    | .inr _ => M.Val a.1 p
  root := ⟨.inl M.root.1, by
    rintro (x | i) hx;
    . exact M.root.2 x (by simpa using hx);
    . simp [Model.Rel];⟩

namespace graft

variable {a : M.NonRoot} {k : ℕ}

lemma ne_root_of_rel [IsTrans _ M.Rel] [Std.Irrefl M.Rel] (_Rra : M.root.1 ≺ a.1) : a.1 ≠ M.root.1 :=
  a.2

@[reducible]
def isFiniteGL [M.IsFiniteGL] (Rra : M.root.1 ≺ a.1) : (M.graft a k).IsFiniteGL where
  trans := by
    have hne : a.1 ≠ M.root.1 := a.2;
    have hnr : ∀ x : M.World, ¬x ≺ M.root.1 := fun _ => not_rel_root;
    have htr : ∀ x y z : M.World, x ≺ y → y ≺ z → x ≺ z := fun _ _ _ h h' => IsTrans.trans _ _ _ h h';
    rintro (x | i) (y | j) (z | l) Rxy Ryz <;> simp_all only [Model.Rel] <;> grind;
  irrefl := by
    rintro (x | i) <;> simp only [Model.Rel];
    . exact Std.Irrefl.irrefl x;
    . exact lt_irrefl i;
  finite := by
    have : Finite M.World := inferInstance;
    infer_instance;

section Rank

variable [Fintype M.World] [M.IsGL]

omit [Fintype M.World] [M.IsGL] in
/-- `inl` preserves `relItr`. -/
lemma relItr_inl {x y : M.World} {n : ℕ} (h : x ≺^[n] y) :
    Model.RelItr (M := (M.graft a k).toModel) n (.inl x) (.inl y) := by
  induction n generalizing x with
  | zero => simp_all;
  | succ n ih =>
    obtain ⟨z, Rxz, hz⟩ := h;
    exact ⟨.inl z, Rxz, ih hz⟩;

omit [Fintype M.World] in
/-- A chain starting from a non-root `inl` world stays inside `inl` and projects to a chain in `M`. -/
lemma relItr_from_inl {x : M.World} {n : ℕ} {w : (M.graft a k).World}
    (hx : x ≠ M.root.1) (h : Model.RelItr (M := (M.graft a k).toModel) n (.inl x) w) :
    ∃ y : M.World, w = .inl y ∧ x ≺^[n] y ∧ y ≠ M.root.1 := by
  induction n generalizing x with
  | zero => exact ⟨x, by simp_all, by simp_all, hx⟩;
  | succ n ih =>
    obtain ⟨v, Rxv, hv⟩ := h;
    match v with
    | .inr i => exact absurd Rxv hx;
    | .inl y =>
      have Rxy : x ≺ y := Rxv;
      obtain ⟨z, rfl, hyz, hz⟩ := ih (fun h => not_rel_root (h ▸ Rxy)) hv;
      exact ⟨z, rfl, ⟨y, Rxy, hyz⟩, hz⟩;

/-- The length of a chain starting from a grafted world is bounded by `i + 1 + a.rank`. -/
lemma relItr_from_inr_le (_Rra : M.root.1 ≺ a.1) {i : Fin k} {n : ℕ} {w : (M.graft a k).World}
    (h : Model.RelItr (M := (M.graft a k).toModel) n (.inr i) w) :
    n ≤ i + 1 + Model.World.rank a.1 := by
  induction n generalizing i w with
  | zero => omega;
  | succ n ih =>
    obtain ⟨v, Riv, hv⟩ := h;
    match v with
    | .inr j =>
      have : (j : ℕ) < i := Riv;
      have := ih hv;
      omega;
    | .inl y =>
      have hya : y = a.1 ∨ a.1 ≺ y := Riv;
      have hy : y ≠ M.root.1 := by
        rcases hya with rfl | hay;
        . exact a.2;
        . exact fun h => not_rel_root (h ▸ hay);
      obtain ⟨z, rfl, hyz, _⟩ := relItr_from_inl hy hv;
      have hn : n ≤ Model.World.rank (M := M.toModel) y := Model.iff_le_rank.mpr ⟨z, hyz⟩;
      have : Model.World.rank (M := M.toModel) y ≤ Model.World.rank a.1 := by
        rcases hya with rfl | hay;
        . rfl;
        . exact le_of_lt (Model.rank_lt_of_rel hay);
      omega;

omit [Fintype M.World] [M.IsGL] in
/-- There is a chain of length `i + 1` from the grafted world `inr i` down to `inl a`. -/
lemma inr_relItr_inl_a {i : Fin k} :
    Model.RelItr (M := (M.graft a k).toModel) ((i : ℕ) + 1) (.inr i) (.inl a.1) := by
  suffices ∀ (m : ℕ) (i : Fin k), (i : ℕ) = m →
      Model.RelItr (M := (M.graft a k).toModel) (m + 1) (.inr i) (.inl a.1) by
    exact this i i rfl;
  intro m;
  induction m with
  | zero =>
    intro i _;
    exact ⟨.inl a.1, Or.inl rfl, by simp⟩;
  | succ m ih =>
    intro i hi;
    have hm : m < k := by omega;
    use .inr ⟨m, hm⟩;
    exact ⟨show m < (i : ℕ) by omega, ih ⟨m, hm⟩ rfl⟩;

/-- The length of a chain starting from the root is bounded by `max M.height (a.rank + k + 1)`. -/
lemma relItr_from_root_le (Rra : M.root.1 ≺ a.1) {n : ℕ} {w : (M.graft a k).World}
    (h : Model.RelItr (M := (M.graft a k).toModel) n (.inl M.root.1) w) :
    n ≤ max M.height (Model.World.rank a.1 + k + 1) := by
  match n with
  | 0 => omega;
  | n + 1 =>
    obtain ⟨v, Rrv, hv⟩ := h;
    match v with
    | .inl y =>
      have Rry : M.root.1 ≺ y := Rrv;
      obtain ⟨z, rfl, hyz, _⟩ := relItr_from_inl (fun h => not_rel_root (h ▸ Rry)) hv;
      have h₁ : n ≤ Model.World.rank y := Model.iff_le_rank.mpr ⟨z, hyz⟩;
      have h₂ : Model.World.rank y < M.height := rank_lt_height Rry;
      omega;
    | .inr i =>
      have h₁ : n ≤ (i : ℕ) + 1 + Model.World.rank a.1 := relItr_from_inr_le Rra hv;
      have h₂ : (i : ℕ) < k := i.2;
      omega;

/--
  Height formula: `(M.graft a k).height = max M.height (a.rank + k + 1)`.
  Note that Foundation's axiom `boneLengthening.eq_height` (claiming `M.height + k`)
  is false in general when some other branch is higher; this `max` form holds exactly.

  - [AB05, Lemma 12]
-/
lemma height_eq (Rra : M.root.1 ≺ a.1)
    [Fintype (M.graft a k).World] [(M.graft a k).IsGL] :
    (M.graft a k).height = max M.height (Model.World.rank a.1 + k + 1) := by
  apply le_antisymm;
  . -- Upper bound: from the bound on chain lengths
    apply Nat.lt_succ_iff.mp;
    apply Model.iff_rank_lt.mpr;
    intro w hw;
    have := relItr_from_root_le Rra hw;
    omega;
  . -- Lower bound: embed the two chains respectively
    apply max_le;
    . -- Embedding of the root chain of M
      apply Model.iff_le_rank.mpr;
      obtain ⟨t, ht⟩ := Model.exists_rank_terminal (M := M.toModel) M.root.1;
      exact ⟨.inl t, relItr_inl ht⟩;
    . -- root ≺ (grafted chain) ≺ a ≺ (a chain of length a.rank)
      apply Model.iff_le_rank.mpr;
      obtain ⟨t, ht⟩ := Model.exists_rank_terminal (M := M.toModel) a.1;
      match k with
      | 0 =>
        use .inl t;
        rw [show Model.World.rank a.1 + 0 + 1 = 1 + Model.World.rank a.1 by omega];
        exact Model.relItr_comp ⟨.inl a.1, Rra, by simp⟩ (relItr_inl ht);
      | k + 1 =>
        use .inl t;
        rw [show Model.World.rank a.1 + (k + 1) + 1 = ((k + 1) + Model.World.rank a.1) + 1 by omega];
        refine ⟨.inr ⟨k, Nat.lt_succ_self k⟩, rfl, Model.relItr_comp (n := k + 1) ?_ (relItr_inl ht)⟩;
        simpa using inr_relItr_inl_a (M := M) (a := a) (i := (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)));

/-- `inl` preserves the rank of non-root worlds. -/
lemma rank_inl [Fintype (M.graft a k).World] [(M.graft a k).IsGL]
    {x : M.World} (hx : x ≠ M.root.1) :
    Model.World.rank (M := (M.graft a k).toModel) (.inl x) = Model.World.rank x := by
  apply le_antisymm;
  . apply Nat.lt_succ_iff.mp;
    apply Model.iff_rank_lt.mpr;
    intro w hw;
    obtain ⟨y, rfl, hxy, -⟩ := relItr_from_inl hx hw;
    exact Model.iff_rank_lt.mp (Nat.lt_succ_self _) y hxy;
  . apply Model.iff_le_rank.mpr;
    obtain ⟨t, ht⟩ := Model.exists_rank_terminal x;
    exact ⟨.inl t, relItr_inl ht⟩;

/-- The rank of the grafted world `inr i` is exactly `i + 1 + a.rank`. -/
lemma rank_inr [Fintype (M.graft a k).World] [(M.graft a k).IsGL]
    (Rra : M.root.1 ≺ a.1) {i : Fin k} :
    Model.World.rank (M := (M.graft a k).toModel) (.inr i)
      = (i : ℕ) + 1 + Model.World.rank a.1 := by
  apply le_antisymm;
  . apply Nat.lt_succ_iff.mp;
    apply Model.iff_rank_lt.mpr;
    intro w hw;
    have := relItr_from_inr_le Rra hw;
    omega;
  . apply Model.iff_le_rank.mpr;
    obtain ⟨t, ht⟩ := Model.exists_rank_terminal a.1;
    exact ⟨.inl t, Model.relItr_comp inr_relItr_inl_a (relItr_inl ht)⟩;

end Rank

section Mainlemma

open Model.World

variable [DecidableEq α] {A : Formula α}

/--
  Main lemma (forcing-preservation): if `a` forces every axiom T instance for the boxed
  subformulas of `A`, then for every subformula `C` of `A`, forcing at the grafted chain
  worlds agrees with `a`, and forcing at the `inl` worlds agrees with the original model.

  - [AB05, Lemma 12]
-/
lemma mainlemma [IsTrans _ M.Rel] [Std.Irrefl M.Rel] (a : M.ReflexiveWorldOf A.subfmls)
  (Rra : M.root.1 ≺ (a : M.World))
  {C : Formula α} (hC : C ∈ A.subfmls)
  :
  (∀ i : Fin k, (Forces (M := (M.graft ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩ k).toModel) (.inr i) C ↔
    Forces (M := (M.graft ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩ k).toModel) (.inl a) C)) ∧
  (∀ x : M.World, (Forces (M := (M.graft ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩ k).toModel) (.inl x) C ↔ x ⊩ C)) := by
  have hane : (a : M.World) ≠ M.root.1 := fun h => Std.Irrefl.irrefl _ (h ▸ Rra);
  induction C with
  | box B ihB =>
    obtain ⟨ihB₁, ihB₂⟩ := ihB (by grind);
    have h₂ : ∀ x : M.World, (Forces (M := (M.graft ⟨a, hane⟩ k).toModel) (.inl x) (□B) ↔ x ⊩ □B) := by
      intro x;
      constructor;
      . intro h y Rxy;
        exact ihB₂ y |>.mp (h (.inl y) Rxy);
      . rintro h (y | i) Rxy;
        . exact ihB₂ y |>.mpr (h y Rxy);
        . have hx : x = M.root.1 := Rxy;
          exact ihB₁ i |>.mpr (ihB₂ a |>.mpr (h a (by rw [hx]; exact Rra)));
    refine ⟨?_, h₂⟩;
    intro i;
    constructor;
    . rintro h (y | j) Ray;
      . exact h (.inl y) (Or.inr Ray);
      . exact absurd Ray hane;
    . intro h;
      have haB : a.1 ⊩ B := a.2 (by grind) (h₂ a |>.mp h);
      rintro (y | j) Riy;
      . rcases Riy with rfl | hay;
        . exact ihB₂ _ |>.mpr haB;
        . exact h (.inl y) hay;
      . exact ihB₁ j |>.mpr (ihB₂ a |>.mpr haB);
  | _ => grind;

end Mainlemma

end graft

end RootedModel

end
