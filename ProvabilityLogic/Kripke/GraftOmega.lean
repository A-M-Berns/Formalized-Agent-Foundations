module

public import ProvabilityLogic.Kripke.Graft

/-!
# The ω-grafted model `graftOmega`

`RootedModel.graftOmega a` grafts an infinite descending chain between the root
and a point `a` above it -- the "expansion of the point `a` to length ω". This file collects
the generic structural facts about this construction (GL-ness, the depth/rank analysis of its
embedded and chain points, the forcing-preservation main lemma) that are independent of any
particular application. The D-model-specific material (`phi0`, almost-defining formulas, Lemma 9)
lives in `ProvabilityLogic/Kripke/AlmostDefiningFormula.lean`.

- [Bek90, Lemma 5, Lemma 9]
-/

@[expose]
public section

open scoped Formula

variable [Nonempty κ]

namespace RootedModel

variable {M : RootedModel κ α}

/-- Worlds of the ω-grafted model: the original worlds plus an infinite descending chain. -/
abbrev graftOmega.World (M : RootedModel κ α) : Type _ := M.World ⊕ ℕ

/--
  The rooted model obtained by grafting an infinite descending chain between the root
  and `a` (`root ≺ ⋯ ≺ chain (n + 1) ≺ chain n ≺ ⋯ ≺ chain 0 ≺ a` and its cone).
  Unlike `Model.toPseudoTail`, the root keeps its other cones (the *lateral cones* of
  the resulting ω-model), which is essential to refute the axioms of `LogicD`.

  - [Bek90, Lemma 5]
-/
abbrev graftOmega (M : RootedModel κ α) (a : M.NonRoot) : RootedModel (graftOmega.World M) α where
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

namespace graftOmega

open Model Model.World
open Model.World (Forces)

variable {a : M.NonRoot}

/-- `M.graftOmega a` is a (necessarily infinite) GL model whenever `M` is a finite
GL model and `a` lies strictly above the root. -/
@[reducible]
def isGL [M.IsFiniteGL] (Rra : M.root.1 ≺ a.1) : (M.graftOmega a).IsGL where
  trans := by
    have hne : a.1 ≠ M.root.1 := a.2;
    have hnr : ∀ x : M.World, ¬x ≺ M.root.1 := fun _ => not_rel_root;
    have htr : ∀ x y z : M.World, x ≺ y → y ≺ z → x ≺ z := fun _ _ _ h h' => IsTrans.trans _ _ _ h h';
    rintro (x | i) (y | j) (z | l) Rxy Ryz <;> simp_all only [Model.Rel] <;> grind;
  cwf := by
    have hne : a.1 ≠ M.root.1 := a.2;
    apply ConverseWellFounded.iff_has_max.mpr;
    intro s hs;
    by_cases hs₁ : {x : M.World | Sum.inl x ∈ s ∧ x ≠ M.root.1}.Nonempty;
    . -- A maximal non-root `inl` world of `s` is maximal in `s`.
      obtain ⟨m, ⟨hm₁, hm₂⟩, hm₃⟩ :=
        ConverseWellFounded.has_max (IsConverseWellFounded.cwf (rel := M.Rel)) _ hs₁;
      use .inl m, hm₁;
      rintro (y | j) hy;
      . intro R;
        have R' : m ≺ y := R;
        exact hm₃ y ⟨hy, fun h => not_rel_root (h ▸ R')⟩ R';
      . exact fun h => hm₂ h;
    . by_cases hs₂ : {i : ℕ | Sum.inr i ∈ s}.Nonempty;
      . -- The least chain index in `s` is maximal in `s`.
        obtain ⟨i₀, hi₀, hmin⟩ := (wellFounded_lt (α := ℕ)).has_min _ hs₂;
        use .inr i₀, hi₀;
        rintro (y | j) hy;
        . rintro (rfl | R);
          . exact hs₁ ⟨a.1, hy, hne⟩;
          . exact hs₁ ⟨y, hy, fun h => not_rel_root (h ▸ R)⟩;
        . exact fun R => hmin j hy R;
      . -- Otherwise `s` can only contain the (embedded) root.
        obtain ⟨w, hw⟩ := hs;
        have hw_root : w = Sum.inl M.root.1 := by
          match w with
          | .inl x =>
            by_contra hx;
            exact hs₁ ⟨x, hw, fun h => hx (by rw [h])⟩;
          | .inr i => exact absurd ⟨i, hw⟩ hs₂;
        subst hw_root;
        use .inl M.root.1, hw;
        rintro (y | j) hy;
        . intro R;
          have R' : M.root.1 ≺ y := R;
          exact hs₁ ⟨y, hy, fun h => not_rel_root (h ▸ R')⟩;
        . exact fun _ => hs₂ ⟨j, hy⟩;

/-- There is a chain of length `n` from the grafted world `inr n` down to `inr 0`. -/
lemma inr_relItr_inr_zero {n : ℕ} :
    Model.RelItr (M := (M.graftOmega a).toModel) n (.inr n) (.inr 0) := by
  induction n with
  | zero => simp;
  | succ n ih =>
    use .inr n;
    exact ⟨show n < n + 1 by omega, ih⟩;

open Model.World in
/-- The root of `M.graftOmega a` has infinite depth: it refutes `□^[n]⊥` for
every `n`, hence forces every `TBB n` (and `∼(□^[n]⊥)`). -/
lemma root_not_forces_boxItr_bot {n : ℕ} :
    ¬((M.graftOmega a).root.1 ⊩ (□^[n]⊥)) := by
  intro h;
  match n with
  | 0 => exact h;
  | n + 1 =>
    have hchain : Model.RelItr (M := (M.graftOmega a).toModel) (n + 1)
        (.inl M.root.1) (.inr 0) :=
      ⟨.inr n, rfl, inr_relItr_inr_zero⟩;
    exact forces_boxItr.mp h _ hchain;

/-- `Sum.inl` preserves chains of `M` in the ω-grafted model. -/
lemma relItr_inl {x y : M.World} {n : ℕ} (h : x ≺^[n] y) :
  Model.RelItr (M := (M.graftOmega a).toModel) n (.inl x) (.inl y) := by
  induction n generalizing x with
  | zero => simp_all;
  | succ n ih =>
    obtain ⟨z, Rxz, hz⟩ := h;
    exact ⟨.inl z, Rxz, ih hz⟩;

/-- Chain points are never the root of the ω-grafted model. -/
lemma inr_ne_root {i : ℕ} :
  (Sum.inr i : (M.graftOmega a).World) ≠ (M.graftOmega a).root.1 := by
  show (Sum.inr i : (M.graftOmega a).World) ≠ Sum.inl M.root.1;
  exact Sum.inr_ne_inl;

/-- `y` **covers** `x` if `y` is an immediate `≺`-successor of `x`: `x ≺ y` and
nothing lies strictly between them.

- [Bek90, Section 4]
-/
def _root_.Model.World.Covers {M : Model κ α} (y x : M.World) : Prop :=
  x ≺ y ∧ ∀ w : M.World, x ≺ w → w ≺ y → False

/-- `x` is a **branch point** if it has at least two distinct covering points.

- [Bek90, Lemma 9.2]
-/
def _root_.Model.World.IsBranchPoint {M : Model κ α} (x : M.World) : Prop :=
  ∃ y₁ y₂ : M.World, y₁ ≠ y₂ ∧ y₁.Covers x ∧ y₂.Covers x

section

variable [IsTrans _ M.Rel] [Std.Irrefl M.Rel]

omit [IsTrans _ M.Rel] [Std.Irrefl M.Rel] in
/--
  No chain point of the ω-grafted model is a branch point. `chainPoint i`'s
  *unique* immediate cover is `chainPoint (i - 1)` if `i > 0`, or the embedded point
  `a` if `i = 0`. Unlike arbitrary points of the base model `M`, the freshly grafted chain
  points can never be branch points.

  - [Bek90, Lemma 9.2]
-/
lemma not_isBranchPoint_chainPoint (i : ℕ) :
  ¬ Model.World.IsBranchPoint (M := (M.graftOmega a).toModel) (Sum.inr i) := by
  rintro ⟨y₁, y₂, hne, ⟨h1, hcov1⟩, ⟨h2, hcov2⟩⟩;
  -- Both `y₁`, `y₂` must equal the unique cover of `chainPoint i`, contradicting
  -- `hne`.
  suffices h : ∀ y : (M.graftOmega a).World,
      Sum.inr i ≺ y → (∀ w, Sum.inr i ≺ w → w ≺ y → False) →
      y = (if h : i = 0 then Sum.inl a.1 else Sum.inr (i - 1)) by
    exact hne (h y₁ h1 hcov1 |>.trans (h y₂ h2 hcov2).symm);
  intro y hiy hcov;
  rcases i with _ | i;
  · simp only [↓reduceDIte];
    rcases y with z | j;
    · -- `y = .inl z` with `z ∈ cone(a)`; if `z ≠ a` then `.inl a` lies strictly
      -- between `chainPoint 0` and `y`, contradicting `hcov`.
      have hz : z = a.1 ∨ M.Rel a.1 z := hiy;
      rcases hz with rfl | haz;
      · rfl;
      · exact absurd haz (fun h => hcov (.inl a.1) (Or.inl rfl) h);
    · exact absurd hiy (by omega);
  · rcases y with z | j;
    · -- `y = .inl z`; `chainPoint i` lies strictly between `chainPoint (i + 1)` and
      -- `y`, contradicting `hcov`.
      exact absurd (hcov (.inr i) (by omega) hiy) id;
    · -- `y = .inr j`; if `j < i` then `.inr i` lies strictly between, contradicting
      -- `hcov`; hence `j = i`.
      have hj : j < i + 1 := hiy;
      rw [dif_neg (Nat.succ_ne_zero i)];
      congr 1;
      by_contra hji;
      exact hcov (.inr i) (by omega) (by show j < i; omega);

end

section

variable [IsTrans _ M.Rel] [Std.Irrefl M.Rel]

/-- A chain starting from a non-root `inl` world of the ω-grafted model stays inside
`inl` and projects to a chain in `M`. -/
lemma relItr_from_inl {x : M.World} {n : ℕ}
  {w : (M.graftOmega a).World}
  (hx : x ≠ M.root.1) (h : Model.RelItr (M := (M.graftOmega a).toModel) n (.inl x) w) :
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

/-- A non-root world forcing `□^[n]⊥` in `M` also forces it as an `inl` world of the
ω-grafted model. -/
lemma inl_forces_boxItr_bot {x : M.World} {n : ℕ}
  (hx : x ≠ M.root.1) (h : x ⊩ (□^[n]⊥)) :
  Forces (M := (M.graftOmega a).toModel) (.inl x) (□^[n]⊥) := by
  apply forces_boxItr.mpr;
  intro w hw;
  obtain ⟨y, rfl, hxy, -⟩ := relItr_from_inl hx hw;
  exact forces_boxItr.mp h y hxy;

end

section Mainlemma

open Model.World

variable [DecidableEq α] {A : Formula α}

/--
  Forcing preservation for ω-expansion: if `a` forces every axiom T instance for the boxed
  subformulas of `A`, then for every subformula `C` of `A`, forcing at the grafted
  chain worlds agrees with `a`, and forcing at the `inl` worlds agrees with the
  original model. The ω-analogue of `graft.mainlemma`.

  - [Bek90, Lemma 5]
-/
lemma mainlemma [IsTrans _ M.Rel] [Std.Irrefl M.Rel] (a : M.ReflexiveWorldOf A.subfmls)
  (Rra : M.root.1 ≺ (a : M.World)) :
  ∀ {C : Formula α}, C ∈ A.subfmls →
  (∀ i : ℕ, (Forces (M := (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).toModel) (.inr i) C ↔
    Forces (M := (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).toModel) (.inl a) C)) ∧
  (∀ x : M.World, (Forces (M := (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).toModel) (.inl x) C ↔ x ⊩ C)) := by
  have hane : (a : M.World) ≠ M.root.1 := fun h => Std.Irrefl.irrefl _ (h ▸ Rra);
  intro C;
  induction C with
  | box B ihB =>
    intro hB;
    obtain ⟨ihB₁, ihB₂⟩ := ihB (by grind);
    have h₂ : ∀ x : M.World,
        (Forces (M := (M.graftOmega ⟨a, hane⟩).toModel) (.inl x) (□B) ↔ x ⊩ □B) := by
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
      have haB : a.1 ⊩ B := a.2 hB (h₂ a |>.mp h);
      rintro (y | j) Riy;
      . rcases (show y = a.1 ∨ a.1 ≺ y from Riy) with hya | hay;
        . subst hya; exact ihB₂ _ |>.mpr haB;
        . exact h (.inl y) hay;
      . exact ihB₁ j |>.mpr (ihB₂ a |>.mpr haB);
  | _ => grind;

end Mainlemma

end graftOmega

end RootedModel

end
