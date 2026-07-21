module

public import ProvabilityLogic.Kripke.Simplification

/-!
# Tree unravelling of GL-models

This file ports Foundation's `Frame.mkTransTreeUnravelling` to ProvabilityLogic's model
setting. Given a rooted model `M`, its *tree unravelling* `M.unravelling`
is the rooted model whose worlds are the `M.Rel`-chains starting at `M`'s root,
ordered by proper prefix. Since GL-models are transitive, the (transitively
closed) accessibility relation is exactly *proper prefix extension*, which is
automatically transitive, irreflexive and a tree (`RootedModel.IsTree`): the
ancestors of a chain are precisely its prefixes, which are linearly ordered.

The last-element map `x ↦ x.1.getLast` is a p-morphism onto `M`, so the root of
the unravelling is modally equivalent to `M`'s root. When `M` is a finite
GL-model, so is its unravelling; hence validity over the (smaller) class of
finite GL *tree* models already entails GL-provability -- the new item of
`LogicGL.provability_TFAE`.
-/

@[expose]
public section

open scoped Formula

universe u

variable [Nonempty κ] {α : Type u}

namespace RootedModel

variable (M : RootedModel κ α)

/-- Worlds of the tree unravelling: `M.Rel`-chains starting from the root. -/
abbrev unravelling.World : Type _ :=
  { c : List M.World // [M.root.1] <+: c ∧ c.IsChain M.Rel }

namespace unravelling

variable {M} (x : unravelling.World M)

lemma root_prefix : [M.root.1] <+: x.1 := x.2.1

lemma isChain : x.1.IsChain M.Rel := x.2.2

@[simp]
lemma ne_nil : x.1 ≠ [] := by
  intro h;
  simpa [h] using x.2.1;

/-- The last world of a chain: the "current" point the chain represents. -/
def World.last : M.World := x.1.getLast (ne_nil x)

instance instNonempty : Nonempty (unravelling.World M) :=
  ⟨⟨[M.root.1], List.prefix_refl _, by simp⟩⟩

end unravelling

open unravelling in
/-- The tree unravelling of a rooted model `M`: worlds are `M.Rel`-chains from
the root, accessibility is proper prefix extension, and the valuation is that of
the last world of the chain. -/
def unravelling : RootedModel (unravelling.World M) α where
  Rel' x y := x.1 <+: y.1 ∧ x.1.length < y.1.length
  Val' x q := M.Val (unravelling.World.last x) q
  root := ⟨⟨[M.root.1], List.prefix_refl _, by simp⟩, by
    rintro ⟨x, hx₁, hx₂⟩ hx;
    refine ⟨hx₁, ?_⟩;
    obtain ⟨t, rfl⟩ := hx₁;
    cases t with
    | nil => simp at hx;
    | cons a t => simp;⟩

namespace unravelling

variable {M} {x y : (M.unravelling).World}

@[simp]
lemma rel_iff : x ≺ y ↔ x.1 <+: y.1 ∧ x.1.length < y.1.length := Iff.rfl

@[simp]
lemma val_iff {q : α} : (M.unravelling).Val x q ↔ M.Val (World.last x) q := Iff.rfl

@[simp]
lemma root_val : (M.unravelling).root.1.1 = [M.root.1] := rfl

@[simp]
lemma root_last : World.last (M.unravelling).root.1 = M.root.1 := by
  simp [World.last];

instance instIsTrans : IsTrans _ (M.unravelling).Rel := by
  constructor;
  rintro x y z ⟨h₁, h₂⟩ ⟨h₃, h₄⟩;
  exact ⟨h₁.trans h₃, by omega⟩;

instance instIrrefl : Std.Irrefl (M.unravelling).Rel := by
  constructor;
  rintro x ⟨-, h⟩;
  omega;

instance instIsTree : (M.unravelling).IsTree := by
  constructor;
  rintro x y z ⟨hxz, -⟩ ⟨hyz, -⟩;
  rcases List.prefix_or_prefix_of_prefix hxz hyz with h | h;
  . rcases lt_or_eq_of_le h.length_le with hl | hl;
    . right; left; exact ⟨h, hl⟩;
    . left; exact Subtype.ext $ h.eq_of_length hl;
  . rcases lt_or_eq_of_le h.length_le with hl | hl;
    . right; right; exact ⟨h, hl⟩;
    . left; exact Subtype.ext $ (h.eq_of_length hl).symm;

instance instFinite [M.IsFiniteGL] : Finite (M.unravelling).World := by
  haveI := Classical.decEq M.World;
  haveI : Finite { l : List M.World // l.IsChain M.Rel } := List.chains_finite;
  apply Finite.of_injective
    (fun x => (⟨x.1, x.2.2⟩ : { l : List M.World // l.IsChain M.Rel }));
  intro x y h;
  apply Subtype.ext;
  simpa using congrArg Subtype.val h;

instance instIsFiniteGL [M.IsFiniteGL] : (M.unravelling).IsFiniteGL where
  finite := instFinite

/-- The last-element map is a p-morphism from the tree unravelling onto `M`. -/
def pMorphism [M.IsGL] : (M.unravelling).toModel →ₚ M.toModel where
  toFun := World.last
  forth := by
    haveI := Classical.decEq M.World;
    rintro x y ⟨hp, hl⟩;
    apply List.rel_getLast_of_isChain_trans (isChain y) (ne_nil y);
    . exact hp.subset $ List.getLast_mem (ne_nil x);
    . obtain ⟨t, ht⟩ := hp;
      have htne : t ≠ [] := by
        rintro rfl;
        simp only [List.append_nil] at ht;
        rw [ht] at hl;
        omega;
      have hd : x.1.Disjoint t :=
        List.disjoint_of_nodup_append $ ht ▸ (isChain y).noDup_of_irrefl_trans;
      have he : y.1.getLast (ne_nil y) = t.getLast htne := by
        rw [show y.1.getLast (ne_nil y) = (x.1 ++ t).getLast (ht ▸ ne_nil y) by simp [ht]];
        exact List.getLast_append_of_ne_nil _ htne;
      rw [he];
      intro e;
      exact hd (e ▸ List.getLast_mem (ne_nil x)) (List.getLast_mem htne);
  back := by
    rintro x v hv;
    refine ⟨⟨x.1.concat v, ?_, ?_⟩, ?_, ?_, ?_⟩;
    . exact x.2.1.trans (by simp);
    . exact (List.isChain_concat_of_not_nil (ne_nil x)).mpr ⟨isChain x, hv⟩;
    . simp [World.last];
    . simp;
    . simp;
  atomic := Iff.rfl

/-- The root of the tree unravelling is modally equivalent to `M`'s root. -/
lemma modal_equivalence_root [M.IsGL] :
    (M.unravelling).root.1 ↭ M.root.1 := by
  have h : (M.unravelling).root.1 ↭ (pMorphism (M := M)).toFun (M.unravelling).root.1 :=
    (pMorphism (M := M)).modal_equivalence _;
  rwa [show (pMorphism (M := M)).toFun (M.unravelling).root.1 = M.root.1 from root_last]
    at h;

section GraftOmega

open Model.World (IsProperPredecessorOf)

/-- The unravelling world `[root, a]`, for `a` a successor of the root: the canonical
point of the tree unravelling covering its root and projecting onto `a`. -/
def coverPoint {a : M.World} (Rra : M.root.1 ≺ a) : (M.unravelling).NonRoot :=
  ⟨⟨[M.root.1, a], ⟨[a], rfl⟩, by simpa using Rra⟩, by
    intro h;
    have h' := congrArg Subtype.val h;
    simp at h';⟩

@[simp]
lemma coverPoint_last {a : M.World} (Rra : M.root.1 ≺ a) :
  World.last (coverPoint Rra).1 = a := by
  simp [coverPoint, World.last];

/-- `coverPoint Rra` lies above the unravelling's root. -/
lemma root_rel_coverPoint {a : M.World} (Rra : M.root.1 ≺ a) :
  (M.unravelling).root.1 ≺ (coverPoint Rra).1 :=
  ⟨⟨[a], rfl⟩, by simp [coverPoint]⟩

/-- `coverPoint Rra` covers the unravelling's root: its only proper predecessor is the
root itself. -/
lemma coverPoint_covers_root {a : M.World} (Rra : M.root.1 ≺ a) :
  ∀ x : (M.unravelling).World,
  IsProperPredecessorOf (M := (M.unravelling).toModel) x (coverPoint Rra).1 →
  x = (M.unravelling).root.1 := by
  rintro ⟨l, hpre, hchain⟩ ⟨-, hl₁, hl₂⟩;
  apply Subtype.ext;
  have hlen : l.length = 1 := by
    have := hpre.length_le;
    simp only [coverPoint, List.length_cons] at hl₂;
    simp_all;
    omega;
  exact hpre.eq_of_length (by simp [hlen]) |>.symm;

/-- The root of the tree unravelling is the only unravelling world whose last
element is `M`'s root. -/
lemma eq_root_of_last_eq_root [M.IsGL] {t : (M.unravelling).World}
  (h : World.last t = M.root.1) : t = (M.unravelling).root.1 := by
  -- In a GL model nothing lies below the root, so a chain from the root ends at
  -- the root only if it is the trivial chain.
  apply Subtype.ext;
  obtain ⟨rest, hrest⟩ := root_prefix t;
  match rest, hrest with
  | [], hrest => exact hrest.symm;
  | b :: rest, hrest =>
    exfalso;
    have hnd : t.1.Nodup := (isChain t).noDup_of_irrefl_trans;
    have hd : List.Disjoint [M.root.1] (b :: rest) :=
      List.disjoint_of_nodup_append (hrest ▸ hnd);
    have hmem : M.root.1 ∈ (b :: rest) := by
      have hlast : t.1.getLast (ne_nil t) = (b :: rest).getLast (by simp) := by
        rw [show t.1.getLast (ne_nil t)
          = ([M.root.1] ++ (b :: rest)).getLast (hrest ▸ ne_nil t) by simp [← hrest]];
        exact List.getLast_append_of_ne_nil _ (by simp);
      rw [show M.root.1 = World.last t from h.symm, World.last, hlast];
      exact List.getLast_mem _;
    exact hd (by simp) hmem;

/--
  Unravelling commutes with grafting the ω-chain, up to a pseudo-epimorphism: the
  last-element map sends `(M.unravelling).graftOmega (coverPoint Rra)` onto
  `M.graftOmega a`. This converts an arbitrary `graftOmega`-shaped ω-model
  into one over a finite *tree* whose grafted point *covers* the root -- the standing
  hypotheses of the simplification machinery.

  - [Bek90, Lemma 8, §4]
-/
def graftOmegaPseudoEpimorphism (M : RootedModel κ α) [M.IsGL] {a : M.World}
  (Rra : M.root.1 ≺ a) :
  ((M.unravelling).graftOmega (coverPoint Rra)).toModel →ₚ
  (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).toModel where
  toFun := fun
    | .inl t => .inl (World.last t)
    | .inr i => .inr i
  forth := by
    rintro (t | i) (s | j) Rxy;
    . exact (pMorphism (M := M)).forth Rxy;
    . show World.last t = M.root.1;
      rw [show t = (M.unravelling).root.1 from Rxy];
      exact root_last;
    . show World.last s = a ∨ M.Rel a (World.last s);
      rcases Rxy with rfl | hR;
      . exact Or.inl (coverPoint_last Rra);
      . exact Or.inr (coverPoint_last Rra ▸ (pMorphism (M := M)).forth hR);
    . exact Rxy;
  back := by
    rintro (t | i) ((w | j)) h;
    . obtain ⟨s, hs, hts⟩ := (pMorphism (M := M)).back h;
      exact ⟨.inl s, congrArg Sum.inl hs, hts⟩;
    . have ht : t = (M.unravelling).root.1 := eq_root_of_last_eq_root h;
      exact ⟨.inr j, rfl, ht⟩;
    . rcases (show w = a ∨ M.Rel a w from h) with rfl | hR;
      . exact ⟨.inl (coverPoint Rra).1, congrArg Sum.inl (coverPoint_last Rra), Or.inl rfl⟩;
      . have hR' : (pMorphism (M := M)).toFun (coverPoint Rra).1 ≺ w := by
          rw [show (pMorphism (M := M)).toFun (coverPoint Rra).1 = a from coverPoint_last Rra];
          exact hR;
        obtain ⟨s, hs, hts⟩ := (pMorphism (M := M)).back hR';
        exact ⟨.inl s, congrArg Sum.inl hs, Or.inr hts⟩;
    . exact ⟨.inr j, rfl, h⟩;
  atomic := by
    rintro (t | i) q;
    . exact Iff.rfl;
    . show M.Val (World.last (coverPoint Rra).1) q ↔ M.Val a q;
      rw [coverPoint_last Rra];

/-- Root forcing transfers from an arbitrary `graftOmega`-shaped ω-model to its
tree unravelling counterpart. -/
lemma graftOmega_root_forces_iff [M.IsGL] {a : M.World} (Rra : M.root.1 ≺ a)
  {C : Formula α} :
  ((M.unravelling).graftOmega (coverPoint Rra)).root.1 ⊩ C ↔
  (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1 ⊩ C := by
  have h := (graftOmegaPseudoEpimorphism M Rra).modal_equivalence
    ((M.unravelling).graftOmega (coverPoint Rra)).root.1 (A := C);
  rwa [show (graftOmegaPseudoEpimorphism M Rra).toFun
      ((M.unravelling).graftOmega (coverPoint Rra)).root.1
    = (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1
    from congrArg Sum.inl root_last] at h;

end GraftOmega

end unravelling

end RootedModel

end
