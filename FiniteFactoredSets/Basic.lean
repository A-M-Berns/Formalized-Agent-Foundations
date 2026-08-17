import Mathlib.Data.Setoid.Partition
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Partitions, factorizations, and chimera functions

This file is §2.1–§2.5 of Garrabrant, *Temporal Inference with Finite Factored Sets*
(arXiv:2109.11513): partitions of a set and their order, factorizations, factored sets,
and the chimera function that splices two elements along a set of factors.

## Modeling decisions

* `dd:partition` — the paper's Definition 2 partition (a set `X ⊆ 𝒫(S)` of nonempty
  blocks covering `S` disjointly) is modeled as a `Setoid S`, matching the choice already
  made in `CartesianFrames/`.  Definition 5's `∼_X` is then the setoid relation itself and
  Definition 4's `[s]_X` is `part`.  Proposition 1 becomes the setoid's own `iseqv`.
* `dd:order-flip` — **the paper's order glyphs are inverted relative to Mathlib's.**  The
  paper writes `X ≥_S Y` for "`X` is finer than `Y`" (Definition 6), so the paper's `≥_S`
  is Mathlib's `≤` on `Setoid`.  Likewise Definition 8's *common refinement* `⋁_S(C)` —
  a join in the paper's notation — is Mathlib's `sInf`.  Mathlib's `⊥` (equality) is the
  paper's `Dis_S` and Mathlib's `⊤` is `Ind_S`.  This file uses Mathlib's order
  throughout and never introduces the paper's glyphs; every statement is written so that
  it reads correctly under Mathlib's convention.
* `dd:quotient` — Definition 9's Cartesian product `∏(B)` (functions choosing one block
  from each partition) is modeled as the dependent product `(b : B) → Quotient b`, and
  Definition 10's `π` as `fun s b => ⟦s⟧`.  `Quotient b` is canonically the set of blocks
  of `b`, so this is a change of presentation, not of content.

## Note on triviality

Definition 3 calls a partition trivial when it has *exactly one* block, and Definition 7
sets `Ind_S = {}` when `S` is empty.  So the empty set's indiscrete partition has **no**
blocks and is therefore *not* trivial.  `IsTrivialPartition` below carries the
`Nonempty S` conjunct that makes this come out right; rendering "nontrivial" as the more
obvious `∃ s t, ¬ b s t` would wrongly exclude every partition of the empty set.
-/

universe u

namespace FiniteFactoredSets

variable {S : Type u}

/-! ## §2.1 Partitions -/

/-- The block of the partition `b` containing `s`.

Paper node: Definition 4 (§2.1). -/
def part (b : Setoid S) (s : S) : Set S := {t | b t s}

@[simp] lemma mem_part {b : Setoid S} {s t : S} : t ∈ part b s ↔ b t s := Iff.rfl

lemma self_mem_part (b : Setoid S) (s : S) : s ∈ part b s := b.refl' s

lemma part_eq_of_mem {b : Setoid S} {s t : S} (h : t ∈ part b s) : part b t = part b s :=
  -- `part b s` is definitionally Mathlib's equivalence class `{x | b x s}`, so this is
  -- `Setoid.eq_of_mem_classes` with no glue — not a fact this development proves.
  Setoid.eq_of_mem_classes (Setoid.mem_classes b t) (b.refl' t) (Setoid.mem_classes b s) h

/-- Two elements lie in the same block exactly when they are related — Definition 5
read through Definition 4. -/
lemma part_eq_iff {b : Setoid S} {s t : S} : part b s = part b t ↔ b s t := by
  constructor
  · intro h
    have hs : s ∈ part b t := h ▸ self_mem_part b s
    exact hs
  · intro h
    exact (part_eq_of_mem (b.symm' h)).symm

/-- Definition 5's `∼_X` is an equivalence relation.  Under `dd:partition` this is the
setoid's own proof, so the content of the paper's proposition is discharged by the
modeling choice rather than reproved.

Paper node: Proposition 1 (§2.1). -/
theorem equivalence_setoid (b : Setoid S) : Equivalence (b : S → S → Prop) := b.iseqv

/-- Definition 3: a partition is trivial when it has exactly one block.  The
`Nonempty S` conjunct is what makes `|X| = 1` — rather than `|X| ≤ 1` — and it is
load-bearing over the empty set, where `Ind_S = {}` has no blocks at all.

Paper node: Definition 3 (§2.1). -/
def IsTrivialPartition (b : Setoid S) : Prop := Nonempty S ∧ ∀ s t : S, b s t

lemma isTrivialPartition_top [Nonempty S] : IsTrivialPartition (⊤ : Setoid S) :=
  ⟨‹_›, fun _ _ => trivial⟩

/-- Over the empty type the indiscrete partition is *not* trivial: it has no blocks. -/
lemma not_isTrivialPartition_of_isEmpty [IsEmpty S] (b : Setoid S) :
    ¬ IsTrivialPartition b := fun h => (IsEmpty.false (h.1.some))

/-- Definition 7's `Dis_S` is Mathlib's `⊥` and `Ind_S` is Mathlib's `⊤`; Definition 6's
"finer" is Mathlib's `≤` (see `dd:order-flip`).  This is the paper's Proposition 2, whose
partial-order half is Mathlib's `PartialOrder (Setoid S)` instance.

Paper node: Proposition 2 (§2.1). -/
theorem bot_le_and_le_top (b : Setoid S) : ⊥ ≤ b ∧ b ≤ ⊤ := ⟨bot_le, le_top⟩

/-- The blocks of `Ind_S` over a nonempty `S`: the single block `S`.  Mathlib has no
`Setoid.classes_top`; note the `Nonempty` hypothesis is genuinely needed, since over the
empty type `(⊤ : Setoid S).classes = ∅` (Definition 7's `Ind_∅ = {}`). -/
lemma classes_top (hS : Nonempty S) : (⊤ : Setoid S).classes = {Set.univ} := by
  ext c
  constructor
  · rintro ⟨y, rfl⟩
    exact Set.eq_univ_of_forall fun _ => trivial
  · rintro rfl
    exact ⟨Classical.arbitrary S, (Set.eq_univ_of_forall fun _ => trivial).symm⟩

/-- Definition 8's common refinement `⋁_S(C)`.  In Mathlib's order this is `sInf`, not a
supremum (`dd:order-flip`); `Setoid.sInf_iff` is exactly the paper's defining property.

Paper node: Definition 8 (§2.1). -/
def commonRefinement (C : Set (Setoid S)) : Setoid S := sInf C

lemma commonRefinement_iff {C : Set (Setoid S)} {s t : S} :
    commonRefinement C s t ↔ ∀ b ∈ C, b s t := Setoid.sInf_iff

/-! ## §2.2 Factorizations -/

/-- Definition 10: a factorization of `S` is a set of nontrivial partitions whose
joint-coordinate map `π` is a bijection.  `dd:quotient` renders `∏(B)` as the dependent
product of the quotients.

Paper node: Definition 10 (§2.2). -/
structure IsFactorization (B : Set (Setoid S)) : Prop where
  nontrivial : ∀ b ∈ B, ¬ IsTrivialPartition b
  bijective : Function.Bijective (fun (s : S) (b : B) => Quotient.mk (b : Setoid S) s)

/-- Definition 11: a factored set is a set together with a factorization of it.

Paper node: Definition 11 (§2.2). -/
structure FactoredSet (S : Type u) where
  B : Set (Setoid S)
  isFactorization : IsFactorization B

namespace FactoredSet

variable (F : FactoredSet S)

/-- The coordinate equivalence `π` of Definition 10, packaged. -/
noncomputable def coord : S ≃ ((b : F.B) → Quotient (b : Setoid S)) :=
  Equiv.ofBijective _ F.isFactorization.bijective

@[simp] lemma coord_apply (s : S) (b : F.B) :
    F.coord s b = Quotient.mk (b : Setoid S) s := rfl

lemma nontrivial_of_mem {b : Setoid S} (hb : b ∈ F.B) : ¬ IsTrivialPartition b :=
  F.isFactorization.nontrivial b hb

/-- Elements agreeing on every factor are equal.

Paper node: Proposition 3 (§2.2). -/
theorem eq_of_forall_rel {s t : S} (h : ∀ b ∈ F.B, (b : Setoid S) s t) : s = t :=
  F.isFactorization.bijective.1 (funext fun b => Quotient.sound (h b b.2))

end FactoredSet

/-! ## §2.3 Chimera functions -/

/-- Theorem 1: for a set of nontrivial partitions, being a factorization is equivalent to
every choice function `g : B → S` being matched by a *unique* element of `S`.  This is the
alternate characterization the chimera function is defined from.

Paper node: Theorem 1 (§2.3). -/
theorem isFactorization_iff_existsUnique {B : Set (Setoid S)}
    (hB : ∀ b ∈ B, ¬ IsTrivialPartition b) :
    IsFactorization B ↔ ∀ g : B → S, ∃! s : S, ∀ b : B, (b : Setoid S) s (g b) := by
  constructor
  · rintro ⟨-, hbij⟩ g
    let e : S ≃ ((b : B) → Quotient (b : Setoid S)) := Equiv.ofBijective _ hbij
    refine ⟨e.symm fun b => Quotient.mk (b : Setoid S) (g b), fun b => ?_, fun s hs => ?_⟩
    · exact Quotient.exact (congrFun (e.apply_symm_apply _) b)
    · refine e.injective ?_
      rw [e.apply_symm_apply]
      funext b
      exact Quotient.sound (hs b)
  · intro h
    refine ⟨hB, ?_, ?_⟩
    · intro s₀ s₁ hs
      obtain ⟨w, -, huniq⟩ := h fun _ => s₀
      exact (huniq s₀ fun b => (b : Setoid S).refl' s₀).trans
        (huniq s₁ fun b => (b : Setoid S).symm' (Quotient.exact (congrFun hs b))).symm
    · intro y
      obtain ⟨s, hs, -⟩ := h fun b => Quotient.out (y b)
      exact ⟨s, funext fun b => (Quotient.sound (hs b)).trans (Quotient.out_eq (y b))⟩

namespace FactoredSet

open scoped Classical

variable (F : FactoredSet S)

/-- Some element sits in a different block from `s`, for any factor.  This is the use the
paper makes of nontriviality in Corollary 1's proof ("there must be some other `T' ∈ b₀`
with `T ∩ T' = {}`"). -/
lemma exists_not_rel {b : Setoid S} (hb : b ∈ F.B) (s : S) : ∃ u : S, ¬ b u s := by
  by_contra hall
  have hall' : ∀ u, b u s := fun u => not_not.1 fun hc => hall ⟨u, hc⟩
  exact F.nontrivial_of_mem hb ⟨⟨s⟩, fun x y => b.trans' (hall' x) (b.symm' (hall' y))⟩

/-- **Corollary 1** — distinct factors share no block.  This is the fact that makes
`b ↦ [s]_b` injective on `B`, and hence (in §5) makes every monomial of a characteristic
polynomial squarefree.

Paper node: Corollary 1 (§2.3). -/
theorem eq_of_part_eq {b₀ b₁ : Setoid S} (h₀ : b₀ ∈ F.B) (h₁ : b₁ ∈ F.B) {s t : S}
    (h : part b₀ s = part b₁ t) : b₀ = b₁ := by
  by_contra hne
  obtain ⟨u, hus⟩ := F.exists_not_rel h₀ s
  -- The paper's `g`: choose `u` at the factor `b₀`, and `t` at every other factor.
  set r : S := F.coord.symm fun b =>
    if (b : Setoid S) = b₀ then Quotient.mk (b : Setoid S) u
    else Quotient.mk (b : Setoid S) t with hr
  have hcoord : ∀ b : F.B, F.coord r b
      = if (b : Setoid S) = b₀ then Quotient.mk (b : Setoid S) u
        else Quotient.mk (b : Setoid S) t := fun b => congrFun (F.coord.apply_symm_apply _) b
  have hr0 : b₀ r u := by
    have := hcoord ⟨b₀, h₀⟩
    rw [if_pos rfl] at this
    exact Quotient.exact this
  have hr1 : b₁ r t := by
    have := hcoord ⟨b₁, h₁⟩
    rw [if_neg (Ne.symm hne)] at this
    exact Quotient.exact this
  have hmem : r ∈ part b₀ s := h ▸ (mem_part.2 hr1 : r ∈ part b₁ t)
  exact hus (b₀.trans' (b₀.symm' hr0) (mem_part.1 hmem))

/-- Definition 12: the chimera function `χ^F`, fusing a choice function `g : B → S` into
the unique element agreeing with `g b` on each factor `b`.

Paper node: Definition 12 (§2.3). -/
noncomputable def chimeraFun (g : F.B → S) : S :=
  F.coord.symm fun b => Quotient.mk (b : Setoid S) (g b)

@[simp] lemma coord_chimeraFun (g : F.B → S) (b : F.B) :
    F.coord (F.chimeraFun g) b = Quotient.mk (b : Setoid S) (g b) :=
  congrFun (F.coord.apply_symm_apply _) b

lemma chimeraFun_rel (g : F.B → S) (b : F.B) : (b : Setoid S) (F.chimeraFun g) (g b) :=
  Quotient.exact (F.coord_chimeraFun g b)

/-- Definition 13: `χ^F_C(s,t)` agrees with `s` on the factors in `C` and with `t` off it.

Paper node: Definition 13 (§2.3). -/
noncomputable def chimera (C : Set (Setoid S)) (s t : S) : S :=
  F.chimeraFun fun b => if (b : Setoid S) ∈ C then s else t

/-- Definition 13's setwise extension `χ^F_C(T,R) = {χ^F_C(t,r) | t ∈ T, r ∈ R}`.  This is
the form Definition 16 (generation) and Propositions 10 and 20 quantify over, so it is
part of the node, not a convenience.

Paper node: Definition 13 (§2.3). -/
noncomputable def chimeraImage (C : Set (Setoid S)) (T R : Set S) : Set S :=
  {u | ∃ t ∈ T, ∃ r ∈ R, F.chimera C t r = u}

lemma mem_chimeraImage {C : Set (Setoid S)} {T R : Set S} {u : S} :
    u ∈ F.chimeraImage C T R ↔ ∃ t ∈ T, ∃ r ∈ R, F.chimera C t r = u := Iff.rfl

@[simp] lemma coord_chimera (C : Set (Setoid S)) (s t : S) (b : F.B) :
    F.coord (F.chimera C s t) b
      = if (b : Setoid S) ∈ C then F.coord s b else F.coord t b := by
  rw [chimera, coord_chimeraFun]
  split_ifs <;> rfl

/-- Proposition 4, clauses 1 and 2: `χ^F_C(s,t)` is `∼_b`-related to `s` on `C` and to
`t` off `C`.  Kept as separate lemmas because every later proof uses them pointwise;
Proposition 4 itself is assembled in `chimera_spec`. -/
lemma chimera_rel_of_mem {C : Set (Setoid S)} (s t : S) {b : Setoid S}
    (hb : b ∈ F.B) (hbC : b ∈ C) : b (F.chimera C s t) s := by
  have := F.coord_chimera C s t ⟨b, hb⟩
  rw [if_pos hbC] at this
  exact Quotient.exact this

lemma chimera_rel_of_notMem {C : Set (Setoid S)} (s t : S) {b : Setoid S}
    (hb : b ∈ F.B) (hbC : b ∉ C) : b (F.chimera C s t) t := by
  have := F.coord_chimera C s t ⟨b, hb⟩
  rw [if_neg hbC] at this
  exact Quotient.exact this

private lemma chimera_ext {x y : S} (h : ∀ b : F.B, F.coord x b = F.coord y b) : x = y :=
  F.coord.injective (funext h)

/-- **Proposition 4** — the eleven identities the paper lists for `χ^F_C`, in order.

The paper fixes `C, D ⊆ B`; this statement leaves them arbitrary, which is *stronger*,
not weaker: `chimera` consults `C` only at `b ∈ F.B`, so `chimera C = chimera (C ∩ F.B)`,
and every clause survives the generalization.  The price is that clause 1 carries an
explicit `c ∈ F.B` guard which the paper gets for free from `C ⊆ B`; a client holding
`hC : C ⊆ F.B` discharges it as `hC hc`.

Paper node: Proposition 4 (§2.3). -/
theorem chimera_spec (C D : Set (Setoid S)) (s t r : S) :
    (∀ c ∈ C, c ∈ F.B → c (F.chimera C s t) s) ∧
    (∀ b ∈ F.B, b ∉ C → b (F.chimera C s t) t) ∧
    F.chimera C s s = s ∧
    F.chimera (F.B \ C) s t = F.chimera C t s ∧
    F.chimera (C ∪ D) s t = F.chimera C s (F.chimera D s t) ∧
    F.chimera (C ∩ D) s t = F.chimera C (F.chimera D s t) t ∧
    (F.chimera C (F.chimera C s t) r = F.chimera C s r ∧
      F.chimera C s (F.chimera C t r) = F.chimera C s r) ∧
    F.chimera C s (F.chimera D t r)
      = F.chimera D (F.chimera C s t) (F.chimera C s r) ∧
    F.chimera C (F.chimera D s t) r
      = F.chimera D (F.chimera C s r) (F.chimera C t r) ∧
    F.chimera F.B s t = s ∧
    F.chimera ∅ s t = t := by
  refine ⟨fun c hcC hcB => F.chimera_rel_of_mem s t hcB hcC,
    fun b hbB hbC => F.chimera_rel_of_notMem s t hbB hbC, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    refine F.chimera_ext fun b => ?_ <;>
    simp only [coord_chimera, Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_empty_iff_false, b.2, true_and] <;>
    split_ifs <;> tauto

/-! ### Named projections of Proposition 4

`chimera_spec` is a single eleven-clause conjunction, so a downstream use of one clause
would otherwise be a chain of `.2`s whose length is the only thing distinguishing clause
10 from clause 11.  These nine names are the clauses §3 and §4 consume; they add no
mathematics, and they live here once rather than being restated per file. -/

/-- Clause 3 of Proposition 4: `χ^F_C(s,s) = s`. -/
lemma chimera_self (C : Set (Setoid S)) (s : S) : F.chimera C s s = s :=
  (F.chimera_spec C C s s s).2.2.1

/-- Clause 4 of Proposition 4: `χ^F_{B∖C}(s,t) = χ^F_C(t,s)`. -/
lemma chimera_sdiff (C : Set (Setoid S)) (s t : S) :
    F.chimera (F.B \ C) s t = F.chimera C t s :=
  (F.chimera_spec C C s t t).2.2.2.1

/-- Clause 5 of Proposition 4: `χ^F_{C∪D}(s,t) = χ^F_C(s, χ^F_D(s,t))`. -/
lemma chimera_union (C D : Set (Setoid S)) (s t : S) :
    F.chimera (C ∪ D) s t = F.chimera C s (F.chimera D s t) :=
  (F.chimera_spec C D s t t).2.2.2.2.1

/-- Clause 6 of Proposition 4: `χ^F_{C∩D}(s,t) = χ^F_C(χ^F_D(s,t), t)`. -/
lemma chimera_inter (C D : Set (Setoid S)) (s t : S) :
    F.chimera (C ∩ D) s t = F.chimera C (F.chimera D s t) t :=
  (F.chimera_spec C D s t t).2.2.2.2.2.1

/-- Clause 7 of Proposition 4, first half: `χ^F_C(χ^F_C(s,t), r) = χ^F_C(s,r)`. -/
lemma chimera_left_idem (C : Set (Setoid S)) (s t r : S) :
    F.chimera C (F.chimera C s t) r = F.chimera C s r :=
  (F.chimera_spec C C s t r).2.2.2.2.2.2.1.1

/-- Clause 7 of Proposition 4, second half: `χ^F_C(s, χ^F_C(t,r)) = χ^F_C(s,r)`. -/
lemma chimera_right_idem (C : Set (Setoid S)) (s t r : S) :
    F.chimera C s (F.chimera C t r) = F.chimera C s r :=
  (F.chimera_spec C C s t r).2.2.2.2.2.2.1.2

/-- Clause 8 of Proposition 4:
`χ^F_C(s, χ^F_D(t,r)) = χ^F_D(χ^F_C(s,t), χ^F_C(s,r))`. -/
lemma chimera_left_comm (C D : Set (Setoid S)) (s t r : S) :
    F.chimera C s (F.chimera D t r)
      = F.chimera D (F.chimera C s t) (F.chimera C s r) :=
  (F.chimera_spec C D s t r).2.2.2.2.2.2.2.1

/-- Clause 10 of Proposition 4: `χ^F_B(s,t) = s`. -/
lemma chimera_basis (s t : S) : F.chimera F.B s t = s :=
  (F.chimera_spec F.B F.B s t t).2.2.2.2.2.2.2.2.2.1

/-- Clause 11 of Proposition 4: `χ^F_∅(s,t) = t`. -/
lemma chimera_empty (s t : S) : F.chimera ∅ s t = t :=
  (F.chimera_spec ∅ ∅ s t t).2.2.2.2.2.2.2.2.2.2

end FactoredSet

/-! ## §2.4 Trivial factorizations

Nothing here needs `S` finite; `dd:finiteness-minimal` (see `FiniteFactoredSets.lean`)
keeps `Fintype`/`Finite` off every statement that does not actually require it. -/

/-- Definition 14: a factorization is trivial when it has at most one factor.

Paper node: Definition 14 (§2.4). -/
def IsTrivialFactorization (B : Set (Setoid S)) : Prop :=
  IsFactorization B ∧ B.Subsingleton

/-- The empty basis factors exactly the one-element sets: with no factors the coordinate
product is a single point, so `π` is a bijection precisely when `S` is one too. -/
lemma isFactorization_empty_iff :
    IsFactorization (∅ : Set (Setoid S)) ↔ (Nonempty S ∧ Subsingleton S) := by
  constructor
  · rintro ⟨-, hinj, hsurj⟩
    obtain ⟨s, -⟩ := hsurj fun b => b.2.elim
    exact ⟨⟨s⟩, ⟨fun x y => hinj (funext fun b => b.2.elim)⟩⟩
  · rintro ⟨⟨s⟩, hsub⟩
    refine ⟨by rintro b ⟨⟩, fun x y _ => hsub.elim x y, fun y => ⟨s, funext fun b => b.2.elim⟩⟩

/-- The discrete basis `{Dis_S}` factors exactly the sets that are *not* one-element:
over a singleton `Dis_S` is trivial and so barred as a factor, and everywhere else the
coordinate map is the identity up to the canonical `S ≃ Quotient ⊥`. -/
lemma isFactorization_singleton_bot_iff :
    IsFactorization ({⊥} : Set (Setoid S)) ↔ ¬ (Nonempty S ∧ Subsingleton S) := by
  constructor
  · rintro ⟨hnt, -⟩ ⟨hne, hsub⟩
    exact hnt ⊥ rfl ⟨hne, fun s t => hsub.elim s t⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rintro b rfl ⟨hne, hall⟩
      exact h ⟨hne, ⟨fun s t => hall s t⟩⟩
    · intro x y hxy
      exact Quotient.exact (congrFun hxy ⟨⊥, rfl⟩)
    · intro y
      refine ⟨Quotient.out (y ⟨⊥, rfl⟩), funext fun b => ?_⟩
      obtain ⟨b, hb⟩ := b
      simp only [Set.mem_singleton_iff] at hb
      subst hb
      exact Quotient.out_eq _

/-- A one-factor basis is a factorization only if that factor is `Dis_S`. -/
lemma eq_bot_of_isFactorization_singleton {b : Setoid S}
    (h : IsFactorization ({b} : Set (Setoid S))) : b = ⊥ := by
  refine le_antisymm (fun {x y} hxy => ?_) bot_le
  exact h.bijective.1 (funext fun c => by
    obtain ⟨c, hc⟩ := c
    simp only [Set.mem_singleton_iff] at hc
    subst hc
    exact Quotient.sound hxy)

/-- **Proposition 5** — both of its sentences.  Every set has exactly one trivial
factorization; that factorization is `{Dis_S}` when `|S| ≠ 1`, and the empty basis when
`|S| = 1`.

The `|S| = 1` split is not an edge case bolted on: over a singleton `Dis_S` *is* the
indiscrete partition, so Definition 10's nontriviality bars it, and the empty basis is
what is left.  `Cardinal.eq_one_iff_unique` is what turns the paper's `|S| = 1` into the
`Nonempty S ∧ Subsingleton S` the two branch lemmas are stated over.

Paper node: Proposition 5 (§2.4). -/
theorem existsUnique_trivialFactorization (S : Type u) :
    (∃! B : Set (Setoid S), IsTrivialFactorization B) ∧
      (Cardinal.mk S ≠ 1 → IsTrivialFactorization ({⊥} : Set (Setoid S))) ∧
      (Cardinal.mk S = 1 → IsTrivialFactorization (∅ : Set (Setoid S))) := by
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : Nonempty S ∧ Subsingleton S
    · refine ⟨∅, ⟨isFactorization_empty_iff.2 h, Set.subsingleton_empty⟩, ?_⟩
      rintro B ⟨hB, hsub⟩
      by_contra hne
      obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.2 hne
      refine hB.nontrivial b hb ⟨h.1, fun s t => ?_⟩
      have hst : s = t := h.2.elim s t
      subst hst
      exact b.refl' s
    · refine ⟨{⊥}, ⟨isFactorization_singleton_bot_iff.2 h, Set.subsingleton_singleton⟩, ?_⟩
      rintro B ⟨hB, hsub⟩
      rcases Set.Subsingleton.eq_empty_or_singleton hsub with rfl | ⟨b, rfl⟩
      · exact absurd (isFactorization_empty_iff.1 hB) h
      · exact congrArg _ (eq_bot_of_isFactorization_singleton hB)
  · intro h
    exact ⟨isFactorization_singleton_bot_iff.2 fun hc =>
      h (Cardinal.eq_one_iff_unique.2 hc.symm), Set.subsingleton_singleton⟩
  · intro h
    exact ⟨isFactorization_empty_iff.2 (Cardinal.eq_one_iff_unique.1 h).symm,
      Set.subsingleton_empty⟩

/-! ## §2.5 Finite factored sets

Definition 15 names two independent finiteness conditions, and the difference between
them is the whole reason `dd:finiteness-minimal` exists: everything through §4 needs only
finite *dimension*, and only §5's characteristic polynomials need finite *size*. -/

/-- `Setoid α` is determined by its relation (`Equivalence` is `Prop`-valued, so proof
irrelevance applies to `iseqv`), so it embeds in `α → α → Prop` and is finite whenever
`α` is.  Mathlib has no such instance; this one is repo-generic and upstreamable, and it
is what makes Proposition 6 a two-liner. -/
instance instFiniteSetoid [Finite S] : Finite (Setoid S) :=
  Finite.of_injective (fun r : Setoid S => ⇑r) fun _ _ h => Setoid.eq_iff_rel_eq.2 h

/-- Over a subsingleton there is only one partition.  `Setoid S` is extensional (see
`instFiniteSetoid`), and any two elements are related by any equivalence relation because
they are already equal.  This is the paper's "if `|S| = 0` or `|S| = 1` then
`|Parts(S)| = 1`", which is the whole of Proposition 8's first two cases. -/
lemma subsingleton_setoid [Subsingleton S] : Subsingleton (Setoid S) :=
  ⟨fun r₁ r₂ => Setoid.ext fun a b => by
    rw [Subsingleton.elim a b]
    exact ⟨fun _ => r₂.refl' b, fun _ => r₁.refl' b⟩⟩

/-- `Ω` is additive over a finite product of nonzero naturals.  Mathlib supplies the
`Multiset` form (`ArithmeticFunction.cardFactors_multiset_prod`); this is its `Finset`
transcription, used to count the factors of a factorization in Proposition 9. -/
private lemma cardFactors_finsetProd {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, f i ≠ 0) :
    ArithmeticFunction.cardFactors (∏ i ∈ s, f i)
      = ∑ i ∈ s, ArithmeticFunction.cardFactors (f i) := by
  have h0 : (Multiset.map f s.val).prod ≠ 0 := by
    rw [← Finset.prod_eq_multiset_prod]
    exact Finset.prod_ne_zero_iff.mpr h
  rw [Finset.prod_eq_multiset_prod, ArithmeticFunction.cardFactors_multiset_prod h0,
    Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

/-- A list of primes has exactly as many prime factors, counted with multiplicity, as it
has entries — the reading of "`|S| = p₀ ⋯ p_{k-1}` is a product of `k` primes" that
Proposition 9's fourth clause needs. -/
private lemma cardFactors_listProd (l : List ℕ) (hl : ∀ p ∈ l, p.Prime) :
    ArithmeticFunction.cardFactors l.prod = l.length := by
  induction l with
  | nil => simp
  | cons p t ih =>
    have hp : p.Prime := hl p (List.mem_cons_self ..)
    have ht : ∀ q ∈ t, q.Prime := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have h0 : t.prod ≠ 0 := (List.prod_pos fun a ha => (ht a ha).pos).ne'
    rw [List.prod_cons, ArithmeticFunction.cardFactors_mul hp.ne_zero h0,
      ArithmeticFunction.cardFactors_apply_prime hp, ih ht, List.length_cons]
    omega

/-- The paper's "if `|B|` were greater than `k` we could express `|S|` as a product of more
than `k` naturals `≥ 2`, which is impossible".  Counting with `Ω`, which is additive and at
least `1` on every factor `≥ 2`, makes it a three-line computation. -/
private lemma card_le_length_of_prod_eq {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (hf : ∀ i, 2 ≤ f i) (l : List ℕ) (hl : ∀ p ∈ l, p.Prime)
    (heq : ∏ i, f i = l.prod) :
    Fintype.card ι ≤ l.length :=
  calc Fintype.card ι = ∑ _i : ι, 1 := by simp
    _ ≤ ∑ i, ArithmeticFunction.cardFactors (f i) :=
        Finset.sum_le_sum fun i _ => ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (hf i)
    _ = ArithmeticFunction.cardFactors (∏ i, f i) :=
        (cardFactors_finsetProd _ _ fun i _ => by have := hf i; omega).symm
    _ = ArithmeticFunction.cardFactors l.prod := by rw [heq]
    _ = l.length := cardFactors_listProd l hl

namespace FactoredSet

variable (F : FactoredSet S)

/-- Definition 15's `size(F)`: the cardinality of the underlying set.

Paper node: Definition 15 (§2.5). -/
noncomputable def size (_F : FactoredSet S) : Cardinal := Cardinal.mk S

/-- Definition 15's `dim(F)`: the cardinality of the factorization.

Paper node: Definition 15 (§2.5). -/
noncomputable def dim : Cardinal := Cardinal.mk F.B

/-- **Proposition 6** — a finite factored set is finite-dimensional.

The paper's proof is the cardinality bound `|B| ≤ 2^(2^|S|)`, `B` being a set of sets of
subsets of `S`.  Under `dd:partition` the same fact is the finiteness of `Setoid S`.

Note the converse fails, which is exactly why `dd:finiteness-minimal` keeps the two
conditions apart: a finite-dimensional factored set may have infinite size.

Paper node: Proposition 6 (§2.5). -/
theorem finite_basis_of_finite [Finite S] : Finite F.B := Subtype.finite

/-- **Proposition 7** — `|S| = ∏_{b ∈ B} |b|`, where `|b|` is the number of blocks of `b`
(under `dd:quotient`, the cardinality of `Quotient b`).  The paper states this for finite
factored sets; it holds for all of them, being the cardinality of the coordinate
bijection `S ≃ ∏(B)`, and `dd:finiteness-minimal` states it that way.

Paper node: Proposition 7 (§2.5). -/
theorem size_eq_prod : F.size = Cardinal.prod fun b : F.B => Cardinal.mk (Quotient (b : Setoid S)) :=
  (Cardinal.mk_congr F.coord).trans (Cardinal.mk_pi _)

/-- Definition 15's `size` unfolded.  Public, so that a client can use the definition
without `rfl`-unfolding a `noncomputable def`. -/
@[simp] lemma size_eq_mk : F.size = Cardinal.mk S := rfl

/-- Definition 15's `dim` unfolded; see `size_eq_mk`. -/
@[simp] lemma dim_eq_mk : F.dim = Cardinal.mk F.B := rfl

/-- Dimension zero means no factors at all. -/
lemma dim_eq_zero_iff : F.dim = 0 ↔ F.B = ∅ := by
  rw [dim_eq_mk]
  exact Cardinal.mk_eq_zero_iff.trans Set.isEmpty_coe_sort

/-- Proposition 7 counted in `ℕ`, which is the shape the arithmetic of Propositions 8 and 9
runs on.  Only the *dimension* need be finite: `Nat.card_pi` holds for any `Fintype` index,
and `Nat.card` of an infinite type is `0` on both sides. -/
lemma natCard_eq_prod [Fintype F.B] :
    Nat.card S = ∏ b : F.B, Nat.card (Quotient (b : Setoid S)) :=
  (Nat.card_congr F.coord).trans Nat.card_pi

/-- Every factor of a nonempty factored set with finitely many blocks has at least two of
them.  This is where the *counting* in Propositions 8 and 9 uses Definition 10's
nontriviality condition; Proposition 9's `size = 1` clause uses it a second time, by a
different route (through `isFactorization_singleton_bot_iff`).  Over the empty set the
statement genuinely fails (there `Quotient b` is empty), which is why `Nonempty S` is a
hypothesis and not decoration.  Only the factor's own block set need be finite; callers
holding `Finite S` get `Finite (Quotient b)` by instance search. -/
lemma one_lt_natCard_quotient [Nonempty S] {b : Setoid S} [Finite (Quotient b)]
    (hb : b ∈ F.B) : 1 < Nat.card (Quotient b) := by
  obtain ⟨s⟩ := ‹Nonempty S›
  obtain ⟨u, hus⟩ := F.exists_not_rel hb s
  exact Finite.one_lt_card_iff_nontrivial.2
    ⟨⟨Quotient.mk b u, Quotient.mk b s, fun h => hus (Quotient.exact h)⟩⟩

/-- Proposition 8's prime case, in the form Proposition 9 reuses.  By Proposition 7 each
factor's block count divides `p`; nontriviality rules out `1`, so every factor has exactly
`p` blocks and `p = p ^ dim(F)` forces at most one factor. -/
lemma subsingleton_basis_of_card_prime {p : ℕ} (hp : p.Prime) (hS : Cardinal.mk S = p) :
    F.B.Subsingleton := by
  haveI : Finite S := Cardinal.lt_aleph0_iff_finite.1 (by rw [hS]; exact Cardinal.natCast_lt_aleph0)
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Finite F.B := F.finite_basis_of_finite
  haveI : Fintype F.B := Fintype.ofFinite _
  have hcard : Nat.card S = p := by
    rw [Nat.card_eq_fintype_card, ← Cardinal.mk_toNat_eq_card, hS, Cardinal.toNat_natCast]
  haveI : Nonempty S := (Nat.card_pos_iff.1 (by rw [hcard]; exact hp.pos)).1
  have hall : ∀ b : F.B, Nat.card (Quotient (b : Setoid S)) = p := by
    intro b
    have hdvd : Nat.card (Quotient (b : Setoid S)) ∣ p := by
      rw [← hcard, F.natCard_eq_prod]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ b)
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · have := F.one_lt_natCard_quotient b.2
      omega
    · exact h
  have hpow : p ^ 1 = p ^ Fintype.card F.B := by
    rw [pow_one]
    calc p = Nat.card S := hcard.symm
      _ = ∏ b : F.B, Nat.card (Quotient (b : Setoid S)) := F.natCard_eq_prod
      _ = ∏ _b : F.B, p := Finset.prod_congr rfl fun b _ => hall b
      _ = p ^ Fintype.card F.B := by rw [Finset.prod_const, Finset.card_univ]
  have hone : Fintype.card F.B = 1 := (Nat.pow_right_injective hp.two_le hpow).symm
  exact (Set.subsingleton_coe F.B).1 (Fintype.card_le_one_iff_subsingleton.1 hone.le)

end FactoredSet

/-- **Proposition 8** — when `|S|` is `0`, `1`, or a prime, the trivial factorization is the
only factorization of `S`: every factorization is trivial (and Proposition 5 makes it
*the* trivial one).  Stated over `Cardinal.mk S` so that no separate finiteness hypothesis
is needed — a set of cardinality `0`, `1`, or `p` is finite.

Paper node: Proposition 8 (§2.5). -/
theorem isTrivialFactorization_of_isFactorization
    (h : Cardinal.mk S = 0 ∨ Cardinal.mk S = 1 ∨ ∃ p : ℕ, p.Prime ∧ Cardinal.mk S = p)
    {B : Set (Setoid S)} (hB : IsFactorization B) : IsTrivialFactorization B := by
  refine ⟨hB, ?_⟩
  -- The `|S| ≤ 1` cases are the paper's `|Parts(S)| = 1`: with only one partition to
  -- choose from, *every* subset of `Parts(S)` is a subsingleton.
  have hsmall : Cardinal.mk S ≤ 1 → B.Subsingleton := fun hle => by
    haveI : Subsingleton S := Cardinal.le_one_iff_subsingleton.1 hle
    haveI := subsingleton_setoid (S := S)
    exact fun a _ b _ => Subsingleton.elim a b
  rcases h with h | h | ⟨p, hp, hS⟩
  · exact hsmall (by rw [h]; exact zero_le_one)
  · exact hsmall h.le
  · exact (⟨B, hB⟩ : FactoredSet S).subsingleton_basis_of_card_prime hp hS

namespace FactoredSet

variable (F : FactoredSet S)

/-- **Proposition 9** — size bounds dimension.  Clause 4 renders "`size(F)` is a product of
`k ≥ 2` primes" as a list of primes of length `k ≥ 2` whose product is the size.  Stated
over `size`/`dim` (`Cardinal`s), so the paper's standing "finite" hypothesis is implied by
each clause's hypothesis rather than assumed.

Paper node: Proposition 9 (§2.5). -/
theorem dim_spec :
    (F.size = 0 → F.dim = 1) ∧
    (F.size = 1 → F.dim = 0) ∧
    (∀ p : ℕ, p.Prime → F.size = p → F.dim = 1) ∧
    (∀ l : List ℕ, (∀ p ∈ l, p.Prime) → 2 ≤ l.length → F.size = l.prod →
      1 ≤ F.dim ∧ F.dim ≤ l.length) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `|S| = 0`: Proposition 8 leaves at most one factor, and the empty basis is barred
    -- because it factors only the one-element sets (Proposition 5's `|S| = 1` branch).
    intro h0
    rw [size_eq_mk] at h0
    haveI : IsEmpty S := Cardinal.mk_eq_zero_iff.1 h0
    rcases (isTrivialFactorization_of_isFactorization (Or.inl h0)
      F.isFactorization).2.eq_empty_or_singleton with hE | ⟨b, hb⟩
    · have hfb : IsFactorization (∅ : Set (Setoid S)) := hE ▸ F.isFactorization
      exact (IsEmpty.false (isFactorization_empty_iff.1 hfb).1.some).elim
    · rw [dim_eq_mk, hb, Cardinal.mk_singleton]
  · -- `|S| = 1`: a one-factor basis would have to be `{Dis_S}`, which is exactly what
    -- Definition 10's nontriviality bars over a singleton.
    intro h1
    rw [size_eq_mk] at h1
    rcases (isTrivialFactorization_of_isFactorization (Or.inr (Or.inl h1))
      F.isFactorization).2.eq_empty_or_singleton with hE | ⟨b, hb⟩
    · exact F.dim_eq_zero_iff.2 hE
    · exfalso
      have hfb : IsFactorization ({b} : Set (Setoid S)) := hb ▸ F.isFactorization
      have hbot : IsFactorization ({⊥} : Set (Setoid S)) :=
        eq_bot_of_isFactorization_singleton hfb ▸ hfb
      exact isFactorization_singleton_bot_iff.1 hbot
        ⟨Cardinal.mk_ne_zero_iff.1 (by rw [h1]; exact one_ne_zero),
          Cardinal.le_one_iff_subsingleton.1 h1.le⟩
  · -- `|S| = p` prime: Proposition 8 again, and now the empty basis is the barred one.
    intro p hp hsize
    rw [size_eq_mk] at hsize
    rcases (isTrivialFactorization_of_isFactorization (Or.inr (Or.inr ⟨p, hp, hsize⟩))
      F.isFactorization).2.eq_empty_or_singleton with hE | ⟨b, hb⟩
    · exfalso
      have hfb : IsFactorization (∅ : Set (Setoid S)) := hE ▸ F.isFactorization
      obtain ⟨hne, hsub⟩ := isFactorization_empty_iff.1 hfb
      have hone : (p : Cardinal) = 1 := hsize ▸ Cardinal.mk_eq_one S
      exact hp.one_lt.ne' (by exact_mod_cast hone)
    · rw [dim_eq_mk, hb, Cardinal.mk_singleton]
  · -- `|S| = p₀ ⋯ p_{k-1}`: Proposition 7 writes `|S|` as a product of `dim(F)` naturals
    -- each at least `2`, and `Ω` counts that against the `k` prime factors of `|S|`.
    intro l hl hk hsize
    rw [size_eq_mk] at hsize
    have hΩ : ArithmeticFunction.cardFactors l.prod = l.length := cardFactors_listProd l hl
    have hlt : 1 < l.prod := ArithmeticFunction.cardFactors_pos_iff_one_lt.1 (by omega)
    haveI : Finite S :=
      Cardinal.lt_aleph0_iff_finite.1 (by rw [hsize]; exact Cardinal.natCast_lt_aleph0)
    haveI : Fintype S := Fintype.ofFinite S
    haveI : Finite F.B := F.finite_basis_of_finite
    haveI : Fintype F.B := Fintype.ofFinite _
    have hcard : Nat.card S = l.prod := by
      rw [Nat.card_eq_fintype_card, ← Cardinal.mk_toNat_eq_card, hsize, Cardinal.toNat_natCast]
    haveI : Nonempty S := (Nat.card_pos_iff.1 (by rw [hcard]; omega)).1
    have hprod : ∏ b : F.B, Nat.card (Quotient (b : Setoid S)) = l.prod := by
      rw [← F.natCard_eq_prod, hcard]
    have hle : Fintype.card F.B ≤ l.length :=
      card_le_length_of_prod_eq _ (fun b => F.one_lt_natCard_quotient b.2) l hl hprod
    have hpos : 0 < Fintype.card F.B := by
      rw [Fintype.card_pos_iff]
      by_contra hemp
      rw [not_nonempty_iff] at hemp
      rw [Finset.univ_eq_empty, Finset.prod_empty] at hprod
      omega
    rw [dim_eq_mk, Cardinal.mk_fintype]
    exact ⟨by exact_mod_cast hpos, by exact_mod_cast hle⟩

end FactoredSet

/-! ### Client-style uses of the §2.5 endpoints -/

namespace FactoredSet

/-- Proposition 7 in its `Cardinal` form (`size_eq_prod`), used the way a client would:
if every factor is binary, the size is `2 ^ dim`, for a factored set of any size and any
dimension. -/
example (F : FactoredSet S)
    (h : ∀ b : F.B, Cardinal.mk (Quotient (b : Setoid S)) = 2) :
    F.size = 2 ^ F.dim := by
  rw [F.size_eq_prod, funext h, Cardinal.prod_const', dim_eq_mk]

/-- Proposition 7 in its `ℕ` form (`natCard_eq_prod`), used the way a client would: if
every factor is binary, the size is a power of two. -/
example (F : FactoredSet S) [Fintype F.B]
    (h : ∀ b : F.B, Nat.card (Quotient (b : Setoid S)) = 2) :
    Nat.card S = 2 ^ Fintype.card F.B := by
  rw [F.natCard_eq_prod, Finset.prod_congr rfl fun b _ => h b, Finset.prod_const,
    Finset.card_univ]

/-- Proposition 9, used the way a client would: a factored set of size `6` has at most two
factors, because `6 = 2 · 3`. -/
example (F : FactoredSet S) (h : F.size = ((6 : ℕ) : Cardinal)) : F.dim ≤ 2 := by
  have hl : ∀ p ∈ [2, 3], Nat.Prime p := by decide
  have := F.dim_spec.2.2.2 [2, 3] hl (by decide) (by simpa using h)
  simpa using this.2

end FactoredSet

end FiniteFactoredSets
