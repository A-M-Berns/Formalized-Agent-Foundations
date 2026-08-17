import FiniteFactoredSets.Basic
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Tactic.TFAE

/-!
# Generation and history

This file is §3.1–§3.2 of Garrabrant, *Temporal Inference with Finite Factored Sets*
(arXiv:2109.11513): when a set of factors *generates* a partition, and the *history* of a
partition — the smallest set of factors that generates it.

## Finiteness

The paper states everything here for finite factored sets.  Under `dd:finiteness-minimal`
the definitions carry no finiteness at all, and `Finite F.B` (finite *dimension*, not
finite size) appears exactly where the paper's proofs use it: Proposition 12 shows the
history is itself generating by expressing it as a *finite* intersection of generating
sets, and this genuinely fails for infinite `B` — over `S = ℕ → Bool` with the coordinate
factors, every cofinite subset of `B` generates the "eventually equal" partition, so the
intersection of all generating subsets is empty and generates nothing.  Nothing in this
file requires `S` finite.

## Orientation

Recall `dd:order-flip`: the paper's `X ≤_S Y` is Mathlib's `Y ≤ X`, its binary join
`X ∨_S Y` is Mathlib's `X ⊓ Y`, and `⋁_S(C)` is `sInf C` (`commonRefinement`).  Every
statement below is written in Mathlib's order.
-/

universe u

namespace FiniteFactoredSets

variable {S : Type u}

namespace FactoredSet

open scoped Classical

variable (F : FactoredSet S)

/-! ## §3.1 Generating a partition with factors -/

/-- Definition 16: `C` generates `X` (in `F`), written `C ⊢^F X`, when `χ^F_C(x, S) = x`
for every block `x` of `X`.

The paper takes `C ⊆ B`.  As with `chimera`, `C` is left arbitrary here: `chimera`
consults `C` only at factors, so `Generates C = Generates (C ∩ F.B)`, and every
statement of Proposition 11 survives without a subset hypothesis.  Proposition 10's
clause 7 (`sInf C ≤ X`) is the one place the restriction is load-bearing, and there it
appears as an explicit hypothesis.

Paper node: Definition 16 (§3.1). -/
def Generates (C : Set (Setoid S)) (X : Setoid S) : Prop :=
  ∀ x ∈ X.classes, F.chimeraImage C x Set.univ = x

/-- Clause 6 of Proposition 10, without the subset hypothesis: this is the form every
proof in this file actually uses. -/
lemma generates_iff_rel (C : Set (Setoid S)) (X : Setoid S) :
    F.Generates C X ↔ ∀ s t : S, X (F.chimera C s t) s := by
  constructor
  · intro h s t
    have hmem : F.chimera C s t ∈ F.chimeraImage C {x | X x s} Set.univ :=
      ⟨s, X.refl' s, t, Set.mem_univ t, rfl⟩
    rw [h _ (X.mem_classes s)] at hmem
    exact hmem
  · rintro h x ⟨y, rfl⟩
    ext u
    constructor
    · rintro ⟨t, ht, r, -, rfl⟩
      exact X.trans' (h t r) ht
    · intro hu
      exact ⟨u, hu, u, Set.mem_univ u, F.chimera_self C u⟩

/-- **Proposition 10** — the seven equivalent forms of `C ⊢^F X`, for `C ⊆ B`.  Clause 7 is
the paper's `X ≤_S ⋁_S(C)`, which under `dd:order-flip` reads `sInf C ≤ X`.

Paper node: Proposition 10 (§3.1). -/
theorem generates_tfae {C : Set (Setoid S)} (hC : C ⊆ F.B) (X : Setoid S) :
    [F.Generates C X,
     ∀ x ∈ X.classes, F.chimeraImage C x Set.univ = x,
     ∀ x ∈ X.classes, F.chimeraImage C x Set.univ ⊆ x,
     ∀ x ∈ X.classes, ∀ y ∈ X.classes, F.chimeraImage C x y ⊆ x,
     ∀ s t : S, F.chimera C s t ∈ part X s,
     ∀ s t : S, X (F.chimera C s t) s,
     commonRefinement C ≤ X].TFAE := by
  -- 1 ↔ 2 is the definition; 5 ↔ 6 is `mem_part`.
  tfae_have 1 ↔ 2 := Iff.rfl
  -- 2 → 3: an equality of sets is in particular an inclusion.
  tfae_have 2 → 3 := fun h x hx => (h x hx).subset
  -- 3 → 4: `χ^F_C(x, y) ⊆ χ^F_C(x, S)` since `y ⊆ S`.
  tfae_have 3 → 4 := by
    rintro h x hx y - u ⟨t, ht, r, -, rfl⟩
    exact h x hx ⟨t, ht, r, Set.mem_univ r, rfl⟩
  -- 4 → 5: instantiate at the blocks `[s]_X` and `[t]_X`.
  tfae_have 4 → 5 := fun h s t =>
    h (part X s) (X.mem_classes s) (part X t) (X.mem_classes t)
      ⟨s, X.refl' s, t, X.refl' t, rfl⟩
  tfae_have 5 ↔ 6 := Iff.rfl
  -- 6 → 7: if `s ∼_{⋁ C} t` then `χ^F_C(s,t) = t`, so `t ∼_X s`.  No subset hypothesis is
  -- needed: `b ∈ C` already supplies `s ∼_b t`, and `b ∉ C` supplies `χ^F_C(s,t) ∼_b t`.
  tfae_have 6 → 7 := by
    intro h s t hst
    have heq : F.chimera C s t = t := F.eq_of_forall_rel fun b hb => by
      by_cases hbC : b ∈ C
      · exact b.trans' (F.chimera_rel_of_mem s t hb hbC) (commonRefinement_iff.1 hst b hbC)
      · exact F.chimera_rel_of_notMem s t hb hbC
    have hrel := h s t
    rw [heq] at hrel
    exact X.symm' hrel
  -- 7 → 1: here `C ⊆ B` is load-bearing — it is what makes `χ^F_C(s,t) ∼_b s` for `b ∈ C`.
  tfae_have 7 → 1 := fun h =>
    (F.generates_iff_rel C X).2 fun s t =>
      h (commonRefinement_iff.2 fun b hb => F.chimera_rel_of_mem s t (hC hb) hb)
  tfae_finish

/-- Clause 7 of Proposition 10, isolated: for `C ⊆ B`, generation is the order relation
`sInf C ≤ X`. -/
lemma generates_iff_sInf_le {C : Set (Setoid S)} (hC : C ⊆ F.B) (X : Setoid S) :
    F.Generates C X ↔ commonRefinement C ≤ X :=
  (F.generates_tfae hC X).out 0 6

/-- **Proposition 11** — the basic properties of `⊢^F`, in the paper's order.  Clause 1's
`X ≤_S Y` is Mathlib's `Y ≤ X`, and clause 2's `X ∨_S Y` is `X ⊓ Y` (`dd:order-flip`).

Paper node: Proposition 11 (§3.1). -/
theorem generates_spec (C D : Set (Setoid S)) (X Y : Setoid S) :
    (Y ≤ X → F.Generates C Y → F.Generates C X) ∧
    (F.Generates C X → F.Generates C Y → F.Generates C (X ⊓ Y)) ∧
    F.Generates F.B X ∧
    (F.Generates ∅ X ↔ X = ⊤) ∧
    (C ⊆ D → F.Generates C X → F.Generates D X) ∧
    (F.Generates C X → F.Generates D X → F.Generates (C ∩ D) X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hYX hY
    rw [F.generates_iff_rel] at hY ⊢
    exact fun s t => hYX (hY s t)
  · intro hX hY
    rw [F.generates_iff_rel] at hX hY ⊢
    exact fun s t => Setoid.inf_iff_and.2 ⟨hX s t, hY s t⟩
  · rw [F.generates_iff_rel]
    intro s t
    -- `χ^F_B(s,t) = s`, so the goal closes by reflexivity of `∼_X`.
    rw [F.chimera_basis]
  · rw [F.generates_iff_rel, Setoid.eq_top_iff]
    constructor
    · intro h s t
      have hrel := h t s
      rwa [F.chimera_empty] at hrel
    · intro h s t
      rw [F.chimera_empty]
      exact h t s
  · intro hCD hX
    rw [F.generates_iff_rel] at hX ⊢
    intro s t
    have key : F.chimera C s (F.chimera D s t) = F.chimera D s t := by
      rw [← F.chimera_union, Set.union_eq_right.2 hCD]
    have hrel := hX s (F.chimera D s t)
    rwa [key] at hrel
  · intro hX hD
    rw [F.generates_iff_rel] at hX hD ⊢
    intro s t
    rw [F.chimera_inter]
    exact X.trans' (hX (F.chimera D s t) t) (hD s t)

/-! ## §3.2 History -/

/-- Definition 17: the history `h^F(X)` of a partition — the smallest subset of `B`
generating `X`.  Rendered as the intersection of all generating subsets of `B`; that this
is itself generating (so that "smallest" is earned) is Proposition 12, and it is where
`Finite F.B` enters.

Paper node: Definition 17 (§3.2). -/
def history (X : Setoid S) : Set (Setoid S) :=
  ⋂₀ {C | C ⊆ F.B ∧ F.Generates C X}

lemma history_subset (X : Setoid S) : F.history X ⊆ F.B :=
  Set.sInter_subset_of_mem
    (show F.B ∈ {C | C ⊆ F.B ∧ F.Generates C X} from
      ⟨subset_rfl, (F.generates_spec F.B F.B X X).2.2.1⟩)

lemma history_subset_of_generates {C : Set (Setoid S)} {X : Setoid S} (hC : C ⊆ F.B)
    (h : F.Generates C X) : F.history X ⊆ C :=
  Set.sInter_subset_of_mem (show C ∈ {C | C ⊆ F.B ∧ F.Generates C X} from ⟨hC, h⟩)

/-- The paper's "we can express `h^F(X)` as a composition of finitely many binary
intersections", as an induction: a finite family of generating sets, intersected into any
generating `D`, still generates.  Clause 6 of Proposition 11 is the induction step and
`D` carries the nonemptiness the paper's argument needs. -/
private lemma generates_inter_sInter (X : Setoid S) {𝒞 : Set (Set (Setoid S))}
    (hfin : 𝒞.Finite) :
    (∀ C ∈ 𝒞, F.Generates C X) →
      ∀ D : Set (Setoid S), F.Generates D X → F.Generates (D ∩ ⋂₀ 𝒞) X := by
  induction 𝒞, hfin using Set.Finite.induction_on with
  | empty => intro _ D hD; simpa using hD
  | @insert a s _ _ ih =>
    intro hall D hD
    rw [Set.sInter_insert, ← Set.inter_assoc]
    exact ih (fun C hC => hall C (Set.mem_insert_of_mem _ hC)) (D ∩ a)
      ((F.generates_spec D a X X).2.2.2.2.2 hD (hall a (Set.mem_insert _ _)))

lemma generates_history [Finite F.B] (X : Setoid S) : F.Generates (F.history X) X := by
  have hfam : {C : Set (Setoid S) | C ⊆ F.B ∧ F.Generates C X}.Finite :=
    ((Set.toFinite F.B).finite_subsets).subset fun _ hC => hC.1
  have h : F.Generates (F.B ∩ F.history X) X :=
    F.generates_inter_sInter X hfam (fun _ hC => hC.2) F.B
      (F.generates_spec F.B F.B X X).2.2.1
  rwa [Set.inter_eq_self_of_subset_right (F.history_subset X)] at h

/-- **Proposition 12** — the history is well-defined: `h^F(X)` is the least subset of `B`
generating `X`.  Finite dimension is what makes the defining intersection finite.

Paper node: Proposition 12 (§3.2). -/
theorem history_isLeast [Finite F.B] (X : Setoid S) :
    IsLeast {C | C ⊆ F.B ∧ F.Generates C X} (F.history X) :=
  ⟨⟨F.history_subset X, F.generates_history X⟩,
    fun _ hC => F.history_subset_of_generates hC.1 hC.2⟩

/-- For `C ⊆ B`, `C` generates `X` exactly when it contains the history. -/
lemma generates_iff_history_subset [Finite F.B] {C : Set (Setoid S)} (hC : C ⊆ F.B)
    (X : Setoid S) : F.Generates C X ↔ F.history X ⊆ C :=
  ⟨F.history_subset_of_generates hC, fun h =>
    (F.generates_spec (F.history X) C X X).2.2.2.2.1 h (F.generates_history X)⟩

/-- The fact every §3.3–§3.4 proof runs on: for `C ⊆ B`, the paper's
`X ≤_S ⋁_S(C)` — Mathlib's `sInf C ≤ X` — says exactly that `C` contains the history of
`X`.  This is clause 7 of Proposition 10 composed with Proposition 12, and it is the step
the paper opens its proof of Proposition 16 with. -/
lemma le_iff_history_subset [Finite F.B] {C : Set (Setoid S)} (hC : C ⊆ F.B) (X : Setoid S) :
    commonRefinement C ≤ X ↔ F.history X ⊆ C :=
  (F.generates_iff_sInf_le hC X).symm.trans (F.generates_iff_history_subset hC X)

/-- The history of `X` generates `X`, in order form: the paper's `X ≤_S ⋁_S(h^F(X))`. -/
lemma commonRefinement_history_le [Finite F.B] (X : Setoid S) :
    commonRefinement (F.history X) ≤ X :=
  (F.le_iff_history_subset (F.history_subset X) X).2 subset_rfl

/-- **Proposition 13** — the basic properties of history.  Clause 1's `X ≤_S Y` is
Mathlib's `Y ≤ X` and clause 2's `X ∨_S Y` is `X ⊓ Y` (`dd:order-flip`); clause 3's
`Ind_S` is `⊤`.

Paper node: Proposition 13 (§3.2). -/
theorem history_spec [Finite F.B] (X Y : Setoid S) :
    (Y ≤ X → F.history X ⊆ F.history Y) ∧
    F.history (X ⊓ Y) = F.history X ∪ F.history Y ∧
    (F.history X = ∅ ↔ X = ⊤) ∧
    (Nonempty S → ∀ b ∈ F.B, F.history b = {b}) := by
  have mono : ∀ {X Y : Setoid S}, Y ≤ X → F.history X ⊆ F.history Y := by
    intro X Y hYX
    exact F.history_subset_of_generates (F.history_subset Y)
      ((F.generates_spec (F.history Y) (F.history Y) X Y).1 hYX (F.generates_history Y))
  refine ⟨mono, ?_, ?_, ?_⟩
  · refine Set.Subset.antisymm ?_ (Set.union_subset (mono inf_le_left) (mono inf_le_right))
    refine F.history_subset_of_generates
      (Set.union_subset (F.history_subset X) (F.history_subset Y)) ?_
    exact (F.generates_spec (F.history X ∪ F.history Y) (F.history X ∪ F.history Y) X Y).2.1
      ((F.generates_spec (F.history X) _ X X).2.2.2.2.1 Set.subset_union_left
        (F.generates_history X))
      ((F.generates_spec (F.history Y) _ Y Y).2.2.2.2.1 Set.subset_union_right
        (F.generates_history Y))
  · constructor
    · intro h
      have hgen : F.Generates ∅ X := by rw [← h]; exact F.generates_history X
      exact (F.generates_spec ∅ ∅ X X).2.2.2.1.1 hgen
    · intro h
      exact Set.subset_empty_iff.1 (F.history_subset_of_generates (Set.empty_subset _)
        ((F.generates_spec ∅ ∅ X X).2.2.2.1.2 h))
  · intro hS b hb
    -- `{b} ⊢^F b` by clause 7 of Proposition 10, since `⋁_S({b}) = b`.
    have hbB : ({b} : Set (Setoid S)) ⊆ F.B := Set.singleton_subset_iff.2 hb
    have hgen : F.Generates {b} b :=
      (F.generates_iff_sInf_le hbB b).2 (le_of_eq (sInf_singleton : sInf {b} = b))
    rcases Set.subset_singleton_iff_eq.1 (F.history_subset_of_generates hbB hgen) with h | h
    · -- `h^F(b) = {}` would make `b` indiscrete, contradicting nontriviality of a factor.
      exfalso
      have h0 : F.Generates ∅ b := by rw [← h]; exact F.generates_history b
      have htop : b = ⊤ := (F.generates_spec ∅ ∅ b b).2.2.2.1.1 h0
      refine F.nontrivial_of_mem hb ⟨hS, fun s t => ?_⟩
      rw [htop]
      exact trivial
    · exact h

/-- Client's-eye use of the endpoints: Proposition 10 is consumed by projecting the
equivalence it needs out of the `TFAE`, and Proposition 13 by projecting a clause. -/
example {C : Set (Setoid S)} (hC : C ⊆ F.B) (X : Setoid S) (h : F.Generates C X) (s t : S) :
    X (F.chimera C s t) s := by
  have h6 : ∀ s t : S, X (F.chimera C s t) s := ((F.generates_tfae hC X).out 0 5).1 h
  exact h6 s t

example [Finite F.B] (X Y : Setoid S) :
    F.history (X ⊓ Y) = F.history X ∪ F.history Y :=
  (F.history_spec X Y).2.1

/-- Proposition 11 read as a client would: enlarging the set of factors (clause 5) and
coarsening the partition (clause 1) both preserve generation, so a client chains the two
clauses it needs and never unfolds `Generates`. -/
example {C D : Set (Setoid S)} (hCD : C ⊆ D) (X Y : Setoid S) (hYX : Y ≤ X)
    (h : F.Generates C Y) : F.Generates D X :=
  (F.generates_spec D D X Y).1 hYX ((F.generates_spec C D Y Y).2.2.2.2.1 hCD h)

/-- Proposition 12 read as a client would: `IsLeast` is consumed by its two projections —
the history generates, and it is below any other generating subset of `B`. -/
example [Finite F.B] {C : Set (Setoid S)} (X : Setoid S) (hC : C ⊆ F.B)
    (h : F.Generates C X) : F.Generates (F.history X) X ∧ F.history X ⊆ C :=
  ⟨(F.history_isLeast X).1.2, (F.history_isLeast X).2 ⟨hC, h⟩⟩

end FactoredSet

end FiniteFactoredSets
