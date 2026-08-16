import Mathlib.Data.Setoid.Partition

/-!
# Partitions, factorizations, and chimera functions

This file is §2.1–§2.3 of Garrabrant, *Temporal Inference with Finite Factored Sets*
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

end FactoredSet

end FiniteFactoredSets
