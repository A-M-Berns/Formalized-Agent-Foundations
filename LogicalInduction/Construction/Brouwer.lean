/-
# Brouwer fixed-point theorem (`lem:fpl` dependency)

Mathlib has no Brouwer or Kakutani fixed-point theorem, so this file proves Brouwer from
scratch: Sperner's lemma over the Freudenthal/Kuhn triangulation of the standard simplex
(`BrouwerProof.Sperner`), lifted to an arbitrary nonempty compact convex
`K ⊆ EuclideanSpace ℝ (Fin d)` (`BrouwerProof`), concluding in
`LogicalInduction.brouwer_fixed_point` — the exact statement the market maker's
price-adjustment fixed point consumes.

Provenance: autoformalized by Harmonic's Aristotle (runs 1d7dc5e0 / c712e6d9), built
there against Lean v4.28.0 + Mathlib v4.28.0, re-validated against this project's
toolchain (v4.28.0-rc1, Mathlib master @ 58d8468). `#print axioms brouwer_fixed_point`
must show only `propext`, `Classical.choice`, `Quot.sound` — checked at the bottom of
this file. Only the final theorem is part of the trust surface; the internal
`BrouwerProof.*` machinery is proof plumbing.

Imports trimmed from Aristotle's original `import Mathlib` umbrella to the minimal set
below (found by `linter.minImports`); the build stays green on that set.
-/
import Mathlib.Tactic.Cases
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.CompleteField
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Algebra.Module.Cardinality

-- The Sperner interior below is machine-generated (see the provenance note above); we do
-- not hand-edit generated proof bodies, so the unused-simp-arg/variable linters are
-- silenced rather than chased.
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

-- The generated combinatorial interior is elaboration-heavy — long `simp_all`/`grind`
-- chains over `Fin`-indexed sums and permutations — and exceeds the default budget.
set_option maxHeartbeats 1000000

namespace LogicalInduction

namespace BrouwerProof.Sperner

open Set Function Finset
open scoped Classical


/-!
# Sperner's lemma and Brouwer for the standard simplex

We work with the standard `n`-simplex with `n+1` barycentric coordinates indexed by
`Fin (n+1)`.  The `m`-fold subdivision has lattice points `p : Fin (n+1) → ℤ` with
`p i ≥ 0` and `∑ i, p i = m`.  A maximal cell of the Freudenthal/Kuhn triangulation is
given by a base lattice point `P` and a permutation `σ : Equiv.Perm (Fin n)`, with
`n+1` vertices `cellVert P σ k` (`k : Fin (n+1)`).
-/

/-- The `j`-th coordinate of the `k`-th vertex of the Freudenthal cell `(P, σ)`.
Increment from vertex `k-1` to `k` adds `e_{(σ (k-1)).castSucc} - e_{(σ (k-1)).succ}`. -/
def cellVert {n : ℕ} (P : Fin (n+1) → ℤ) (σ : Equiv.Perm (Fin n))
    (k : Fin (n+1)) (j : Fin (n+1)) : ℤ :=
  P j + ∑ l : Fin n, (if (l.castSucc : Fin (n+1)) < k then
      ((if (σ l).castSucc = j then (1:ℤ) else 0) - (if (σ l).succ = j then 1 else 0)) else 0)

lemma cellVert_zero {n : ℕ} (P : Fin (n+1) → ℤ) (σ : Equiv.Perm (Fin n)) :
    cellVert P σ 0 = P := by
  exact funext fun x => by unfold cellVert; aesop;

/-- `p` is a lattice point of the `m`-dilated simplex. -/
def IsLat {n : ℕ} (m : ℤ) (p : Fin (n+1) → ℤ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = m

/-- A cell `(P, σ)` is valid if all its vertices are lattice points of the simplex. -/
def ValidCell {n : ℕ} (m : ℤ) (P : Fin (n+1) → ℤ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k, IsLat m (cellVert P σ k)

/-- A cell is *fully labeled* (panchromatic) if its vertices realize all `n+1` labels. -/
def IsFull {n : ℕ} (l : (Fin (n+1) → ℤ) → Fin (n+1)) (P : Fin (n+1) → ℤ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  Surjective (fun k => l (cellVert P σ k))

/-- The finite set of valid cells (base point with coordinates in `[0,m]`, any permutation). -/
noncomputable def cellFin (n : ℕ) (m : ℤ) :
    Finset ((Fin (n+1) → ℤ) × Equiv.Perm (Fin n)) :=
  ((Fintype.piFinset (fun _ : Fin (n+1) => Finset.Icc (0:ℤ) m)) ×ˢ Finset.univ).filter
    (fun pσ => ValidCell m pσ.1 pσ.2)

/-
Every valid cell lies in `cellFin`.
-/
lemma mem_cellFin {n : ℕ} {m : ℤ} {P : Fin (n+1) → ℤ} {σ : Equiv.Perm (Fin n)}
    (hv : ValidCell m P σ) : (P, σ) ∈ cellFin n m := by
  unfold cellFin;
  have := hv 0;
  simp_all +decide [ IsLat, cellVert ];
  exact fun i => this.2 ▸ Finset.single_le_sum ( fun a _ => this.1 a ) ( Finset.mem_univ i )

/-
**Cell-side door count.** For a labeling `g` of the `n+1` vertices by `n+1` labels,
the number of vertices whose removal leaves exactly the labels `≠ last` (each once) is
odd iff `g` is surjective (i.e. the cell is fully labeled).
-/
lemma doorIdx_card_odd_iff {N : ℕ} (g : Fin (N+1) → Fin (N+1)) :
    Odd ((Finset.univ.filter (fun k0 =>
      (Finset.univ.erase k0).image g = Finset.univ.erase (Fin.last N))).card)
      ↔ Surjective g := by
  constructor;
  · contrapose!;
    intro h_not_surjective
    by_cases h_last_in_range : Fin.last N ∈ Set.range g;
    · by_cases h_last_unique : ∀ k0, g k0 = Fin.last N → ∀ k1, g k1 = Fin.last N → k0 = k1;
      · obtain ⟨k0, hk0⟩ : ∃ k0, g k0 = Fin.last N ∧ ∀ k1, g k1 = Fin.last N → k1 = k0 := by
          exact ⟨ h_last_in_range.choose, h_last_in_range.choose_spec, fun k hk => h_last_unique _ hk _ h_last_in_range.choose_spec ⟩;
        -- If `g` is not surjective and `last` is hit exactly once, then `k0` cannot be in `D`.
        have h_k0_not_in_D : ¬(Finset.image g (Finset.univ.erase k0) = Finset.univ.erase (Fin.last N)) := by
          intro h_eq
          have h_surjective : ∀ y, y ≠ Fin.last N → ∃ x, x ≠ k0 ∧ g x = y := by
            intro y hy; replace h_eq := Finset.ext_iff.mp h_eq y; aesop;
          exact h_not_surjective fun y => if hy : y = Fin.last N then hy.symm ▸ ⟨ k0, hk0.1 ⟩ else by obtain ⟨ x, hx₁, hx₂ ⟩ := h_surjective y hy; exact ⟨ x, hx₂ ⟩ ;
        rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
        grind;
      · rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
        intro k hk; simp_all +decide [ Finset.ext_iff ] ;
        obtain ⟨ x, hx, y, hy, hxy ⟩ := h_last_unique; specialize hk ( Fin.last N ) ; simp_all +decide ;
        grind;
    · by_cases h_other_missed : ∃ j ≠ Fin.last N, j ∉ Set.range g;
      · rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
        intro x hx; obtain ⟨ j, hj₁, hj₂ ⟩ := h_other_missed; replace hx := Finset.ext_iff.mp hx j; simp_all +decide [ Finset.mem_image ] ;
      · -- If no other label is missed, then `g` maps onto `univ.erase last` with exactly one label `b` attained twice (say at `k1 ≠ k2`), all others once.
        obtain ⟨b, hb⟩ : ∃ b : Fin (N + 1), b ≠ Fin.last N ∧ Finset.card (Finset.filter (fun k => g k = b) Finset.univ) = 2 := by
          have h_card : ∑ j ∈ Finset.univ.erase (Fin.last N), Finset.card (Finset.filter (fun k => g k = j) Finset.univ) = N + 1 := by
            rw [ ← Finset.card_biUnion ];
            · convert Finset.card_fin ( N + 1 ) ; ext x ; aesop;
            · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
          have h_card : ∑ j ∈ Finset.univ.erase (Fin.last N), (Finset.card (Finset.filter (fun k => g k = j) Finset.univ) - 1) = 1 := by
            zify at *;
            rw [ Finset.sum_congr rfl fun x hx => Nat.cast_sub <| Finset.card_pos.mpr <| by
              exact not_not.mp fun h => h_other_missed ⟨ x, by aesop ⟩ ] ; aesop;
          obtain ⟨ b, hb ⟩ := Finset.exists_ne_zero_of_sum_ne_zero ( by linarith : ∑ j ∈ Finset.univ.erase ( Fin.last N ), ( Finset.card ( Finset.filter ( fun k => g k = j ) Finset.univ ) - 1 ) ≠ 0 );
          exact ⟨ b, Finset.ne_of_mem_erase hb.1, by linarith [ Nat.sub_add_cancel ( show 1 ≤ Finset.card ( Finset.filter ( fun k => g k = b ) Finset.univ ) from Finset.card_pos.mpr <| by obtain ⟨ k, hk ⟩ := not_not.mp fun h => h_other_missed ⟨ b, Finset.ne_of_mem_erase hb.1, h ⟩ ; exact ⟨ k, by aesop ⟩ ), Finset.single_le_sum ( fun x _ => Nat.zero_le ( Finset.card ( Finset.filter ( fun k => g k = x ) Finset.univ ) - 1 ) ) hb.1, Nat.pos_of_ne_zero hb.2 ] ⟩;
        -- Then `k0 ∈ D` (condition (ii): every non-last label still attained after removing `k0`) iff `k0 ∈ {k1, k2}` (removing a non-doubled index would lose that label).
        have h_door_set : Finset.filter (fun k0 => Finset.image g (Finset.univ.erase k0) = Finset.univ.erase (Fin.last N)) Finset.univ = Finset.filter (fun k => g k = b) Finset.univ := by
          ext k0; simp [hb];
          constructor <;> intro hk0;
          · have := Finset.card_image_iff.mp ( by aesop : Finset.card ( Finset.image g ( Finset.univ.erase k0 ) ) = Finset.card ( Finset.univ.erase k0 ) ) ; simp_all +decide [ Finset.card_image_of_injective ] ;
            obtain ⟨ k1, hk1, k2, hk2, hne ⟩ := Finset.one_lt_card.mp ( by linarith ) ; simp_all +decide [ InjOn ] ;
            grind;
          · ext j; simp [hk0];
            constructor;
            · grind;
            · intro hj_ne_last
              obtain ⟨a, ha⟩ : ∃ a, g a = j := by
                exact not_not.mp fun h => h_other_missed ⟨ j, hj_ne_last, h ⟩;
              by_cases ha_eq_k0 : a = k0;
              · obtain ⟨ a, ha ⟩ := Finset.exists_mem_ne ( by linarith ) k0; use a; aesop;
              · use a;
        grind;
  · intro hg
    have h_card : Finset.card (Finset.univ.filter (fun k0 => (Finset.univ.erase k0).image g = Finset.univ.erase (Fin.last N))) = 1 := by
      obtain ⟨a, ha⟩ : ∃ a : Fin (N + 1), g a = Fin.last N ∧ ∀ b : Fin (N + 1), g b = Fin.last N → b = a := by
        have h_inj : Function.Injective g := by
          exact Finite.injective_iff_surjective.mpr hg;
        exact ⟨ Classical.choose ( hg ( Fin.last N ) ), Classical.choose_spec ( hg ( Fin.last N ) ), fun b hb => h_inj ( hb.trans ( Classical.choose_spec ( hg ( Fin.last N ) ) |> Eq.symm ) ) ⟩;
      rw [ Finset.card_eq_one ] ; use a ; ext k0 ; simp_all +decide [ Finset.ext_iff ] ;
      constructor <;> intro hk0;
      · contrapose! hk0;
        exact ⟨ Fin.last N, Or.inl ⟨ ⟨ a, by tauto, ha.1 ⟩, rfl ⟩ ⟩;
      · exact fun x => ⟨ fun ⟨ y, hy, hy' ⟩ => by aesop, fun hx => by obtain ⟨ y, hy ⟩ := hg x; exact ⟨ y, by aesop ⟩ ⟩;
    exact h_card.symm ▸ by decide;

/-- The set of *half-doors*: a valid cell together with an omitted vertex index whose
removal leaves exactly the labels `≠ last`. -/
noncomputable def halfDoors (n : ℕ) (m : ℤ) (l : (Fin (n+1) → ℤ) → Fin (n+1)) :
    Finset (((Fin (n+1) → ℤ) × Equiv.Perm (Fin n)) × Fin (n+1)) :=
  (cellFin n m ×ˢ Finset.univ).filter (fun x =>
    (Finset.univ.erase x.2).image (fun k => l (cellVert x.1.1 x.1.2 k))
      = Finset.univ.erase (Fin.last n))

/-
**Cell-side count.** The number of half-doors has the same parity as the number of
fully-labeled valid cells.
-/
lemma halfDoors_card_modEq {n : ℕ} {m : ℤ}
    (l : (Fin (n+1) → ℤ) → Fin (n+1)) :
    (halfDoors n m l).card ≡ ((cellFin n m).filter (fun pσ => IsFull l pσ.1 pσ.2)).card [MOD 2] := by
  -- For a cell `pσ = (P,σ)`, let `D pσ := (univ.filter (fun k0 => (univ.erase k0).image (fun k => l (cellVert P σ k)) = univ.erase (Fin.last n)))`, the door-index set. Because `halfDoors` is the filter of the product `cellFin ×ˢ univ` by a predicate depending on `(cell, k0)`, its cardinality is the sum over cells in `cellFin` of `(D pσ).card`:
  have h_card : (halfDoors n m l).card = ∑ pσ ∈ cellFin n m, (Finset.univ.filter (fun k0 => (Finset.univ.erase k0).image (fun k => l (cellVert pσ.1 pσ.2 k)) = Finset.univ.erase (Fin.last n))).card := by
    rw [ halfDoors, Finset.card_filter ];
    erw [ Finset.sum_product ] ; aesop;
  -- By `doorIdx_card_odd_iff`, `(D pσ).card % 2 = 1` iff `IsFull l P σ`, else `0`.
  have h_parity : ∀ pσ ∈ cellFin n m, (Finset.univ.filter (fun k0 => (Finset.univ.erase k0).image (fun k => l (cellVert pσ.1 pσ.2 k)) = Finset.univ.erase (Fin.last n))).card % 2 = if IsFull l pσ.1 pσ.2 then 1 else 0 := by
    intro pσ hpσ
    have h_parity : Odd ((Finset.univ.filter (fun k0 => (Finset.univ.erase k0).image (fun k => l (cellVert pσ.1 pσ.2 k)) = Finset.univ.erase (Fin.last n))).card) ↔ IsFull l pσ.1 pσ.2 := by
      convert doorIdx_card_odd_iff ( fun k => l ( cellVert pσ.1 pσ.2 k ) ) using 1;
      exact Iff.rfl;
    grind;
  rw [ h_card, Nat.ModEq, Finset.sum_nat_mod, Finset.sum_congr rfl h_parity ] ; aesop

/-
Parity from an involution: a self-inverse map on a finset has cardinality congruent
mod 2 to the number of its fixed points.
-/
lemma card_modEq_card_fixed {α : Type*} [DecidableEq α] (s : Finset α) (τ : α → α)
    (hmap : ∀ a ∈ s, τ a ∈ s) (hinv : ∀ a ∈ s, τ (τ a) = a) :
    s.card ≡ (s.filter (fun a => τ a = a)).card [MOD 2] := by
  have h_even_T : Even (Finset.card (s.filter (fun a => τ a ≠ a))) := by
    -- Since τ is an involution on T, we can partition T into pairs {a, τ(a)}.
    have h_partition : ∃ T' : Finset (Finset α), (∀ t ∈ T', t.card = 2) ∧ (∀ t ∈ T', ∀ a ∈ t, a ∈ s.filter (fun a => τ a ≠ a)) ∧ (∀ a ∈ s.filter (fun a => τ a ≠ a), ∃ t ∈ T', a ∈ t) ∧ (∀ t₁ t₂, t₁ ∈ T' → t₂ ∈ T' → t₁ ≠ t₂ → Disjoint t₁ t₂) := by
      refine' ⟨ Finset.image ( fun a => { a, τ a } ) ( s.filter ( fun a => τ a ≠ a ) ), _, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
      · grind;
      · grind;
      · exact fun a ha ha' => ⟨ a, ⟨ ha, ha' ⟩, Or.inl rfl ⟩;
      · grind;
    obtain ⟨ T', hT₁, hT₂, hT₃, hT₄ ⟩ := h_partition; rw [ show { a ∈ s | τ a ≠ a } = Finset.biUnion T' id from ?_ ] ; rw [ Finset.card_biUnion ] ; simp_all +decide [ parity_simps ] ;
    · exact fun x hx y hy hxy => hT₄ x y hx hy hxy;
    · grind;
  rw [ Nat.ModEq ] ; rw [ show #s = # ( Finset.filter ( fun a => τ a ≠ a ) s ) + # ( Finset.filter ( fun a => τ a = a ) s ) by rw [ Finset.card_filter, Finset.card_filter ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.card_eq_sum_ones ] ; congr ; ext x ; aesop ] ; simp_all +decide [ Nat.even_iff.mp h_even_T, Nat.add_mod ] ;

/-
Base case of Sperner's parity: in dimension `0` there is exactly one valid cell and it
is fully labeled.
-/
lemma sperner_card_odd_zero {m : ℤ} (hm : 1 ≤ m)
    (l : (Fin 1 → ℤ) → Fin 1)
    (_hadm : ∀ p : Fin 1 → ℤ, IsLat m p → p (l p) ≠ 0) :
    Odd ((cellFin 0 m).filter (fun pσ => IsFull l pσ.1 pσ.2)).card := by
  refine' ⟨ 0, _ ⟩;
  refine' Finset.card_eq_one.mpr _;
  refine' ⟨ ⟨ fun _ => m, 1 ⟩, _ ⟩ ; ext ; simp +decide [ IsFull ];
  constructor <;> intro h <;> simp_all +decide [ cellFin, ValidCell ];
  · rename_i x; rcases h with ⟨ ⟨ ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩, ha₃ ⟩, ha₄ ⟩ ; simp_all +decide [ IsLat, cellVert ] ;
    exact funext fun x => by fin_cases x; exact ha₃;
  · unfold IsLat cellVert; simp_all +decide [ Fin.eq_zero ] ;
    linarith

/-- The labeling on the `x_last = 0` face (dimension `n`), induced by a labeling `l` in
dimension `n+1`: extend a face point by `0` in the last coordinate, label it with `l`, and
read the result as an element of `Fin (n+1)` (it is never `last` on the face). -/
noncomputable def faceLabel {n : ℕ} (l : (Fin (n+2) → ℤ) → Fin (n+2)) :
    (Fin (n+1) → ℤ) → Fin (n+1) :=
  fun q => if h : l (Fin.snoc q 0) = Fin.last (n+1) then 0 else (l (Fin.snoc q 0)).castPred h

/-
The induced face labeling is admissible.
-/
lemma faceLabel_admissible {n : ℕ} {m : ℤ}
    (l : (Fin (n+2) → ℤ) → Fin (n+2))
    (hadm : ∀ p, IsLat m p → p (l p) ≠ 0) :
    ∀ q : Fin (n+1) → ℤ, IsLat m q → q (faceLabel l q) ≠ 0 := by
  intro q hq; specialize hadm ( Fin.snoc q 0 ) ?_ <;> simp_all +decide [ IsLat ] ;
  · intro i; refine' Fin.lastCases _ _ i <;> simp +decide [ * ] ;
  · unfold faceLabel; split_ifs at * <;> simp_all +decide [ Fin.snoc ] ;
    obtain ⟨hle, hne⟩ := hadm; exact hne;

/-- The edge vector `e_{j.castSucc} - e_{j.succ}` in dimension `n+1`. -/
def edgeVec {n : ℕ} (j : Fin (n+1)) : Fin (n+2) → ℤ :=
  fun i => (if j.castSucc = i then (1:ℤ) else 0) - (if j.succ = i then 1 else 0)

/-- The pivot partner of a half-door `(P, σ, k0)` in dimension `n+1`: the (unique) other cell
sharing the facet obtained by omitting vertex `k0`.  Interior omissions swap two adjacent
edges of `σ`; the two endpoint omissions shift the base and rotate `σ`. -/
def pivot {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1))) (k0 : Fin (n+2)) :
    ((Fin (n+2) → ℤ) × Equiv.Perm (Fin (n+1))) × Fin (n+2) :=
  if k0 = 0 then ((cellVert P σ 1, (finRotate (n+1)).trans σ), Fin.last (n+1))
  else if hl : k0 = Fin.last (n+1) then
    ((fun i => P i - edgeVec (σ (Fin.last n)) i, (finRotate (n+1)).symm.trans σ), 0)
  else
    ((P, (Equiv.swap (⟨k0.val-1, by omega⟩ : Fin (n+1)) (⟨k0.val, Fin.val_lt_last hl⟩ : Fin (n+1))).trans σ), k0)

/-
The pivot is an involution.
-/
lemma pivot_pivot {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1))) (k0 : Fin (n+2)) :
    pivot (pivot P σ k0).1.1 (pivot P σ k0).1.2 (pivot P σ k0).2 = ((P, σ), k0) := by
  unfold pivot;
  by_cases h : k0 = 0 <;> by_cases h' : k0 = Fin.last ( n + 1 ) <;> simp +decide [ h, h' ];
  · simp_all +decide [ Fin.ext_iff ];
  · unfold cellVert edgeVec; simp +decide [ Fin.sum_univ_succ ] ;
    exact Equiv.ext fun x => by simp +decide [ finRotate ] ;
  · constructor;
    · ext i; simp +decide [ cellVert, edgeVec ] ;
      rw [ show ( -1 : Fin ( n + 1 ) ) = Fin.last n from by { exact Fin.ext ( by norm_num ) } ] ; ring;
    · ext x; simp +decide [ finRotate ] ;
  · grind +locals

/-
Swapping two edges `a, b` of `σ` that are both before or both after `k` leaves vertex
`k` unchanged.
-/
lemma cellVert_swap_eq {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1)))
    (a b : Fin (n+1)) (k : Fin (n+2)) (h : (a.castSucc < k) ↔ (b.castSucc < k)) :
    cellVert P ((Equiv.swap a b).trans σ) k = cellVert P σ k := by
  ext j; simp [cellVert] ;
  rw [ ← Equiv.sum_comp ( Equiv.swap a b ) ] ; simp +decide [ h ] ;
  refine' Finset.sum_congr rfl fun x hx => _ ; by_cases hx' : x = a <;> by_cases hx'' : x = b <;> simp_all +decide [ Equiv.swap_apply_def ] ;

/-
Vertex correspondence for the `k0 = 0` pivot: the partner's vertex `k.castSucc` equals
the original vertex `k.succ`.
-/
lemma cellVert_pivot_zero {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1)))
    (k : Fin (n+1)) :
    cellVert (cellVert P σ 1) ((finRotate (n+1)).trans σ) k.castSucc = cellVert P σ k.succ := by
  ext j;
  unfold cellVert; simp +decide [ Finset.sum_ite ] ;
  rw [ show ( Finset.filter ( fun x => x ≤ k ) Finset.univ : Finset ( Fin ( n + 1 ) ) ) = Finset.image ( fun x : Fin ( n + 1 ) => x + 1 ) ( Finset.filter ( fun x => x < k ) Finset.univ ) ∪ { 0 } from ?_, Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter ];
  · rw [ Finset.sum_union, Finset.sum_union ] <;> norm_num;
    · rw [ Finset.preimage ] ; simp +decide [ Finset.filter_singleton ] ; ring;
      split_ifs <;> simp_all +decide [ Finset.filter_image ] ; ring;
      · grind;
      · rw [ show ( Finset.filter ( fun x => x + -1 < k ) Finset.univ : Finset ( Fin ( n + 1 ) ) ) = Finset.image ( fun x : Fin ( n + 1 ) => x + 1 ) ( Finset.filter ( fun x => x < k ) Finset.univ ) from ?_, Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter ];
        · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num ; ring;
        · ext x; simp [Finset.mem_image];
      · rw [ show ( Finset.filter ( fun x => x + -1 < k ) Finset.univ : Finset ( Fin ( n + 1 ) ) ) = Finset.image ( fun x : Fin ( n + 1 ) => x + 1 ) ( Finset.filter ( fun x => x < k ) Finset.univ ) from ?_, Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter ];
        · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num ; ring;
        · ext x; simp [Finset.mem_image];
      · rw [ show ( Finset.filter ( fun x => x + -1 < k ) Finset.univ : Finset ( Fin ( n + 1 ) ) ) = Finset.image ( fun x : Fin ( n + 1 ) => x + 1 ) ( Finset.filter ( fun x => x < k ) Finset.univ ) from ?_, Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter ];
        · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num [ Fin.ext_iff ] ;
        · ext x; simp [Finset.mem_image];
    · rw [ Fin.le_def, Fin.coe_neg_one ]; exact k.is_le;
    · rw [ Fin.le_def, Fin.coe_neg_one ]; exact k.is_le;
  · ext x; simp [Finset.mem_union];
    rcases x with ⟨ _ | x, hx ⟩ <;> norm_num [ Fin.add_def, Fin.lt_def ];
    norm_num [ ( by ring : x + 1 + n = n + 1 + x ), Nat.mod_eq_of_lt hx ];
    rw [ Nat.mod_eq_of_lt ( by linarith ) ] ; exact ⟨ fun h => Nat.lt_of_succ_le h, fun h => Nat.succ_le_of_lt h ⟩ ;

/-
Vertex correspondence for the `k0 = last` pivot: the partner's vertex `k.succ` equals
the original vertex `k.castSucc`.
-/
lemma cellVert_pivot_last {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1)))
    (k : Fin (n+1)) :
    cellVert (fun i => P i - edgeVec (σ (Fin.last n)) i) ((finRotate (n+1)).symm.trans σ) k.succ
      = cellVert P σ k.castSucc := by
  ext j; simp [cellVert, edgeVec];
  rw [ Finset.sum_eq_add_sum_sdiff_singleton_of_mem ( Finset.mem_univ 0 ) ] ; simp +decide [ Finset.sum_ite ] ; ring;
  rw [ show ( Finset.filter ( fun x => x ≤ k ) ( Finset.univ \ { 0 } ) : Finset ( Fin ( n + 1 ) ) ) = Finset.image ( fun x : Fin ( n + 1 ) => x + 1 ) ( Finset.filter ( fun x => x < k ) Finset.univ ) from ?_, Finset.card_filter, Finset.card_filter ];
  · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num [ Fin.ext_iff ];
    rw [ show ( -1 : Fin ( n + 1 ) ) = Fin.last n from by { exact Fin.ext ( by norm_num ) } ] ; ring;
  · ext x; simp [Finset.mem_image];
    rcases x with ⟨ _ | x, hx ⟩ <;> norm_num [ Fin.add_def, Fin.lt_def ];
    · exact Nat.le_of_lt_succ k.2;
    · norm_num [ ( by ring : x + 1 + n = n + 1 + x ), Nat.mod_eq_of_lt hx ];
      rw [ Nat.mod_eq_of_lt ( by linarith ) ] ; exact ⟨ fun h => Nat.lt_of_succ_le h, fun h => Nat.succ_le_of_lt h ⟩ ;

/-
The pivot preserves the facet (the set of vertices other than the omitted one).
-/
lemma pivot_facet {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1))) (k0 : Fin (n+2)) :
    (Finset.univ.erase (pivot P σ k0).2).image
        (fun k => cellVert (pivot P σ k0).1.1 (pivot P σ k0).1.2 k)
      = (Finset.univ.erase k0).image (fun k => cellVert P σ k) := by
  by_cases h : k0 = 0 <;> by_cases h' : k0 = Fin.last ( n + 1 ) <;> simp +decide [ h, h', pivot ] at *;
  · rw [ show ( Finset.univ.erase ( Fin.last ( n + 1 ) ) : Finset ( Fin ( n + 2 ) ) ) = Finset.image Fin.castSucc Finset.univ from ?_, show ( Finset.univ.erase 0 : Finset ( Fin ( n + 2 ) ) ) = Finset.image Fin.succ Finset.univ from ?_ ];
    · rw [ Finset.image_image, Finset.image_image ];
      exact Finset.image_congr fun x hx => cellVert_pivot_zero P σ x;
    · ext ( _ | i ) <;> simp +decide [ Fin.ext_iff ];
    · ext i; simp [Finset.mem_image];
  · rw [ show ( Finset.univ.erase 0 : Finset ( Fin ( n + 2 ) ) ) = Finset.image ( fun k : Fin ( n + 1 ) => Fin.succ k ) Finset.univ from ?_, show ( Finset.univ.erase ( Fin.last ( n + 1 ) ) : Finset ( Fin ( n + 2 ) ) ) = Finset.image ( fun k : Fin ( n + 1 ) => Fin.castSucc k ) Finset.univ from ?_ ];
    · rw [ Finset.image_image, Finset.image_image ];
      exact Finset.image_congr fun x hx => cellVert_pivot_last P σ x;
    · ext i; simp [Finset.mem_erase];
    · ext ( _ | i ) <;> simp +decide [ Fin.ext_iff ];
  · refine' Finset.image_congr fun x hx => _;
    apply cellVert_swap_eq;
    rw [ Fin.lt_def, Fin.lt_def ] at * ; norm_num at * ; omega

/-
The pivot strictly changes the half-door.
-/
lemma pivot_ne {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1))) (k0 : Fin (n+2)) :
    pivot P σ k0 ≠ ((P, σ), k0) := by
  by_contra h;
  unfold pivot at h;
  rcases k0 with ⟨ _ | k0, hk0 ⟩ <;> norm_num [ Fin.ext_iff ] at h;
  split_ifs at h <;> simp_all +decide [ Equiv.Perm.ext_iff ];
  specialize h ⟨ k0, by linarith ⟩ ; simp_all +decide [ Equiv.swap_apply_def ]

/-- The *boundary* half-doors: those whose pivot partner is not a valid cell. -/
noncomputable def boundaryDoors (n : ℕ) (m : ℤ) (l : (Fin (n+2) → ℤ) → Fin (n+2)) :
    Finset (((Fin (n+2) → ℤ) × Equiv.Perm (Fin (n+1))) × Fin (n+2)) :=
  (halfDoors (n+1) m l).filter
    (fun x => ¬ ValidCell m (pivot x.1.1 x.1.2 x.2).1.1 (pivot x.1.1 x.1.2 x.2).1.2)

/-
The pivot involution pairs up interior half-doors, so the number of half-doors has the
same parity as the number of boundary half-doors.
-/
lemma halfDoors_card_modEq_boundary {n : ℕ} {m : ℤ}
    (l : (Fin (n+2) → ℤ) → Fin (n+2)) :
    (halfDoors (n+1) m l).card ≡ (boundaryDoors n m l).card [MOD 2] := by
  -- Define the involution τ
  set τ : (((Fin (n + 2) → ℤ) × Equiv.Perm (Fin (n + 1))) × Fin (n + 2)) → (((Fin (n + 2) → ℤ) × Equiv.Perm (Fin (n + 1))) × Fin (n + 2)) := fun x =>
    if ValidCell m (pivot x.1.1 x.1.2 x.2).1.1 (pivot x.1.1 x.1.2 x.2).1.2 then
      (pivot x.1.1 x.1.2 x.2)
    else x;
  convert card_modEq_card_fixed ( halfDoors ( n + 1 ) m l ) τ _ _ using 1;
  · congr with x ; simp +decide [ boundaryDoors ];
    grind +suggestions;
  · intro x hx; unfold τ; split_ifs <;> simp_all +decide [ halfDoors ] ;
    refine' ⟨ _, _ ⟩;
    · exact mem_cellFin ‹_›;
    · convert congr_arg ( Finset.image l ) ( pivot_facet x.1.1 x.1.2 x.2 ) using 1;
      · grind +qlia;
      · grind;
  · intro x hx; simp_all +decide [ halfDoors ] ;
    unfold τ; split_ifs <;> simp_all +decide [ pivot_pivot ] ;
    exact False.elim <| ‹¬ValidCell m x.1.1 x.1.2› <| by unfold cellFin at hx; aesop;

/-
The last coordinate of a vertex: it drops by `1` once the edge pointing at the last
vertex (`σ.symm (Fin.last n)`) has been crossed.
-/
lemma cellVert_last_coord {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1)))
    (k : Fin (n+2)) :
    cellVert P σ k (Fin.last (n+1))
      = P (Fin.last (n+1)) - (if (σ.symm (Fin.last n)).castSucc < k then 1 else 0) := by
  unfold cellVert;
  rw [ Finset.sum_eq_single ( σ.symm ( Fin.last n ) ) ] <;> simp +decide [ Fin.ext_iff, Fin.val_last ];
  · split_ifs <;> ring;
  · grind +suggestions

/-- Lift a face permutation to dimension `n+1`: send `0` to `Fin.last n` (the first edge
points at the last coordinate) and `j.succ` to `(s j).castSucc`. -/
noncomputable def liftPerm {n : ℕ} (s : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv n).trans ((Equiv.optionCongr s).trans (finSuccEquiv' (Fin.last n)).symm)

/-- Lift a face base point to dimension `n+1`. -/
def liftBase {n : ℕ} (Pb : Fin (n+1) → ℤ) : Fin (n+2) → ℤ :=
  fun i => (Fin.snoc Pb (0:ℤ) : Fin (n+2) → ℤ) i - edgeVec (Fin.last n) i

/-
`liftPerm` sends `0` to `Fin.last n`.
-/
lemma liftPerm_zero {n : ℕ} (s : Equiv.Perm (Fin n)) : liftPerm s 0 = Fin.last n := by
  unfold liftPerm;
  simp +decide [ finSuccEquiv, finSuccEquiv' ]

/-
`liftPerm` sends `j.succ` to `(s j).castSucc`.
-/
lemma liftPerm_succ {n : ℕ} (s : Equiv.Perm (Fin n)) (j : Fin n) :
    liftPerm s j.succ = (s j).castSucc := by
  unfold liftPerm;
  simp +decide [ finSuccEquiv, finSuccEquiv' ]

/-
The on-face vertices of the lifted cell project to the vertices of the face cell.
-/
lemma cellVert_lift {n : ℕ} (Pb : Fin (n+1) → ℤ) (s : Equiv.Perm (Fin n))
    (k i : Fin (n+1)) :
    cellVert (liftBase Pb) (liftPerm s) k.succ i.castSucc = cellVert Pb s k i := by
  unfold cellVert liftBase liftPerm;
  rw [ Fin.sum_univ_succ ] ; simp +decide [ Fin.snoc, edgeVec ] ; ring;
  grind +qlia

/-
An on-face vertex of the lifted cell is the corresponding face vertex with a `0`
appended in the last coordinate.
-/
lemma cellVert_lift_snoc {n : ℕ} (Pb : Fin (n+1) → ℤ) (s : Equiv.Perm (Fin n))
    (k : Fin (n+1)) :
    cellVert (liftBase Pb) (liftPerm s) k.succ = Fin.snoc (cellVert Pb s k) 0 := by
  convert funext _;
  intro i; induction i using Fin.lastCases <;> simp_all +decide [ Fin.snoc ] ;
  · rw [ cellVert_last_coord, liftBase, liftPerm ];
    simp +decide [ Fin.snoc, edgeVec ];
    simp +decide [ finSuccEquiv, Equiv.optionCongr ];
  · convert cellVert_lift Pb s k _ using 1;
    exact if_pos ( Nat.le_of_lt_succ ( Fin.is_lt _ ) )

/-
A valid face cell has its last-coordinate base `≥ 1` (its bottom vertex on that
coordinate is `Pb (Fin.last n) - 1 ≥ 0`).
-/
lemma face_last_ge {n : ℕ} {m : ℤ} {Pb : Fin (n+1) → ℤ} {s : Equiv.Perm (Fin n)}
    (hm : 1 ≤ m) (hv : ValidCell m Pb s) : 1 ≤ Pb (Fin.last n) := by
  -- By definition of `ValidCell`, we know that `cellVert Pb s (Fin.last n) (Fin.last n) ≥ 0`.
  have h_last_coord : cellVert Pb s (Fin.last n) (Fin.last n) ≥ 0 := by
    exact hv _ |>.1 _;
  rcases n with ( _ | n ) <;> simp_all +decide [ cellVert_last_coord ];
  have := hv 0; simp_all +decide [ IsLat, cellVert ] ;

/-
The lift of a valid face cell is a valid cell.
-/
lemma liftCell_valid {n : ℕ} {m : ℤ} {Pb : Fin (n+1) → ℤ} {s : Equiv.Perm (Fin n)}
    (hm : 1 ≤ m) (hv : ValidCell m Pb s) : ValidCell m (liftBase Pb) (liftPerm s) := by
  intro k;
  induction' k using Fin.inductionOn with k ih;
  · have := hv 0;
    unfold cellVert at this ⊢; simp_all +decide [ Fin.sum_univ_castSucc, Fin.succ_last ] ;
    constructor <;> simp_all +decide [ IsLat, liftBase ];
    · intro i; unfold edgeVec; simp +decide [ Fin.snoc ] ;
      grind +suggestions;
    · unfold edgeVec; simp +decide [ Finset.sum_ite ] ;
      show (1 - ∑ x : Fin (n+2), if Fin.last (n+1) = x then (1:ℤ) else 0) = 0;
      simp [ Finset.sum_ite_eq ] ;
  · rw [ cellVert_lift_snoc ] ; exact ⟨ by
      intro i; cases i using Fin.lastCases <;> simp +decide [ * ] ;
      exact hv k |>.1 _, by
      rw [ Fin.sum_univ_castSucc ] ; simp +decide [ hv k |>.2 ] ⟩ ;

/-
The base point recovered from a lifted cell is the original face base.
-/
lemma liftBase_proj {n : ℕ} (Pb : Fin (n+1) → ℤ) (s : Equiv.Perm (Fin n)) (i : Fin (n+1)) :
    cellVert (liftBase Pb) (liftPerm s) 1 i.castSucc = Pb i := by
  convert cellVert_lift Pb s 0 i using 1;
  · unfold cellVert; aesop;
  · unfold cellVert; simp +decide [ Finset.sum_ite ] ;

/-
The label of an on-face point lifts to the face label via `castSucc`.
-/
lemma faceLabel_castSucc {n : ℕ} {m : ℤ} (l : (Fin (n+2) → ℤ) → Fin (n+2))
    (hadm : ∀ p, IsLat m p → p (l p) ≠ 0) {q : Fin (n+1) → ℤ}
    (hq : IsLat m (Fin.snoc q 0)) :
    (faceLabel l q).castSucc = l (Fin.snoc q 0) := by
  unfold faceLabel; split_ifs <;> simp_all +decide [ Fin.snoc ] ;
  exact hadm _ hq ( by simp +decide [ *, Fin.snoc ] )

/-
A permutation fixing `0 ↦ Fin.last n` is in the image of `liftPerm`.
-/
lemma exists_facePerm {n : ℕ} {σ : Equiv.Perm (Fin (n+1))} (h0 : σ 0 = Fin.last n) :
    ∃ s : Equiv.Perm (Fin n), liftPerm s = σ := by
  by_contra h_contra;
  -- By definition of `liftPerm`, we know that `liftPerm s = σ` if and only if `s` is the permutation of `Fin n` induced by `σ ∘ Fin.succ`.
  obtain ⟨s, hs⟩ : ∃ s : Fin n → Fin n, ∀ j : Fin n, σ j.succ = (s j).castSucc := by
    have h_induced : ∀ j : Fin n, σ j.succ ≠ Fin.last n := by
      exact fun j => by intro h; have := σ.injective ( h.trans h0.symm ) ; aesop;
    exact ⟨ fun j => ⟨ σ j.succ |> Fin.val, lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using h_induced j ) ⟩, fun j => by simp +decide [ Fin.ext_iff ] ⟩;
  -- Since `s` is a bijection, it is a permutation of `Fin n`.
  have hs_perm : Function.Bijective s := by
    have hs_inj : Function.Injective s := by
      intro i j hij; have := σ.injective ( by aesop : σ i.succ = σ j.succ ) ; aesop;
    exact ⟨ hs_inj, Finite.injective_iff_surjective.mp hs_inj ⟩;
  refine' h_contra ⟨ Equiv.ofBijective s hs_perm, _ ⟩;
  ext i; induction i using Fin.inductionOn <;> simp_all +decide [ liftPerm ] ;

/-- The lift map from face cells to dimension-`(n+1)` cells. -/
noncomputable def liftCell {n : ℕ} (c : (Fin (n+1) → ℤ) × Equiv.Perm (Fin n)) :
    ((Fin (n+2) → ℤ) × Equiv.Perm (Fin (n+1))) × Fin (n+2) :=
  ((liftBase c.1, liftPerm c.2), 0)

/-
The lift of a fully-labeled face cell is a boundary half-door.
-/
lemma liftCell_mem {n : ℕ} {m : ℤ} (hm : 1 ≤ m) (l : (Fin (n+2) → ℤ) → Fin (n+2))
    (hadm : ∀ p, IsLat m p → p (l p) ≠ 0) {c : (Fin (n+1) → ℤ) × Equiv.Perm (Fin n)}
    (hc : c ∈ (cellFin n m).filter (fun pσ => IsFull (faceLabel l) pσ.1 pσ.2)) :
    liftCell c ∈ boundaryDoors n m l := by
  unfold liftCell boundaryDoors; simp +decide [ halfDoors, pivot ] ;
  constructor;
  · constructor;
    · have h_liftCell_valid : ValidCell m (liftBase c.1) (liftPerm c.2) := by
        exact liftCell_valid hm ( by unfold cellFin at hc; aesop );
      grind +suggestions;
    · rw [ show ( Finset.univ.erase 0 : Finset ( Fin ( n + 2 ) ) ) = Finset.image ( fun k : Fin ( n + 1 ) => Fin.succ k ) Finset.univ from ?_, Finset.image_image ];
      · convert congr_arg ( Finset.image Fin.castSucc ) ( show Finset.image ( fun k => faceLabel l ( cellVert c.1 c.2 k ) ) Finset.univ = Finset.univ from ?_ ) using 1;
        · ext; simp [cellVert_lift_snoc];
          constructor <;> rintro ⟨ a, rfl ⟩ <;> use a;
          · apply faceLabel_castSucc;
            exact hadm;
            unfold cellFin at hc; simp_all +decide [ ValidCell, IsLat ] ;
            intro i; induction i using Fin.lastCases <;> simp +decide [ * ] ;
          · rw [ faceLabel_castSucc ];
            exact hadm;
            unfold cellFin at hc; simp_all +decide [ ValidCell, IsLat ] ;
            intro i; induction i using Fin.lastCases <;> simp +decide [ * ] ;
        · ext i; simp [Finset.mem_erase];
        · unfold IsFull at hc; aesop;
      · ext ( _ | i ) <;> simp +decide [ Fin.ext_iff ];
  · intro h; have := h ( Fin.last _ ) ; simp_all +decide [ IsLat ] ;
    convert this.1 ( Fin.last _ ) using 1 ; simp +decide [ cellVert_last_coord ];
    rw [ if_pos ];
    · unfold liftBase; simp +decide [ edgeVec ] ;
    · exact Equiv.symm_apply_eq _ |>.2 ( by simp +decide [ liftPerm_zero ] )

/-
The `j`-th coordinate of vertex `k` as a difference of edge-counts.
-/
lemma cellVert_coord {n : ℕ} (P : Fin (n+1) → ℤ) (σ : Equiv.Perm (Fin n))
    (k : Fin (n+1)) (j : Fin (n+1)) :
    cellVert P σ k j = P j
      + ((Finset.univ.filter (fun l => l.castSucc < k ∧ (σ l).castSucc = j)).card : ℤ)
      - ((Finset.univ.filter (fun l => l.castSucc < k ∧ (σ l).succ = j)).card : ℤ) := by
  unfold cellVert; simp +decide [ Finset.sum_ite ] ;
  simp +decide [ Finset.filter_filter, add_sub_assoc ]

/-
Indicator form of the coordinate (each fiber has at most one element since `σ` is
injective).
-/
lemma cellVert_coord_ind {n : ℕ} (P : Fin (n+1) → ℤ) (σ : Equiv.Perm (Fin n))
    (k : Fin (n+1)) (j : Fin (n+1)) :
    cellVert P σ k j = P j
      + (if ∃ l, l.castSucc < k ∧ (σ l).castSucc = j then (1:ℤ) else 0)
      - (if ∃ l, l.castSucc < k ∧ (σ l).succ = j then (1:ℤ) else 0) := by
  rw [ cellVert_coord ];
  split_ifs <;> norm_num [ Finset.Nonempty ];
  · rw [ Finset.card_eq_one.mpr, Finset.card_eq_one.mpr ];
    · norm_num;
    · obtain ⟨ l, hl₁, hl₂ ⟩ := ‹∃ l, l.castSucc < k ∧ ( σ l ).succ = j›; use l; ext x; simp +decide [ hl₁ ] ;
      constructor <;> intro h <;> aesop;
    · obtain ⟨ l, hl₁, hl₂ ⟩ := ‹∃ l, l.castSucc < k ∧ ( σ l ).castSucc = j›; use l; ext; aesop;
  · rw [ Finset.card_eq_one.mpr, Finset.card_eq_zero.mpr ] <;> aesop;
  · rw [ Finset.card_eq_zero.mpr, Finset.card_eq_one.mpr ] <;> aesop;
  · rw [ Finset.card_eq_zero.mpr, Finset.card_eq_zero.mpr ] <;> aesop

/-- **Propagation.** For a valid cell with `P j = 0`, if at every vertex other than `k0` an
incoming edge for `j` before that vertex is matched by an outgoing edge for `j` before it,
then that vertex has coordinate `0` at `j`. -/
lemma facet_coord_zero {n : ℕ} {m : ℤ} {P : Fin (n+1) → ℤ} {σ : Equiv.Perm (Fin n)}
    (hv : ValidCell m P σ) {j : Fin (n+1)} {k0 : Fin (n+1)} (hP : P j = 0)
    (h : ∀ k, k ≠ k0 → (∃ l, l.castSucc < k ∧ (σ l).castSucc = j)
      → (∃ l, l.castSucc < k ∧ (σ l).succ = j)) :
    ∀ k, k ≠ k0 → cellVert P σ k j = 0 := by
  intro k hk
  have hge := (hv k).1 j
  rw [cellVert_coord_ind, hP] at hge ⊢
  by_cases hin : ∃ l, l.castSucc < k ∧ (σ l).castSucc = j
  · rw [if_pos hin, if_pos (h k hk hin)]; ring
  · rw [if_neg hin] at hge ⊢
    by_cases hout : ∃ l, l.castSucc < k ∧ (σ l).succ = j
    · rw [if_pos hout] at hge; omega
    · rw [if_neg hout]; ring

/-
Coordinate formula for the top vertex `Fin.last (n+1)` of a cell: every edge is included,
so the correction is `+1` at every coordinate except `Fin.last (n+1)` and `-1` at every
coordinate except `0`.
-/
lemma cellVert_last_all {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1))) (j : Fin (n+2)) :
    cellVert P σ (Fin.last (n+1)) j
      = P j + (if j = Fin.last (n+1) then 0 else 1) - (if j = 0 then 0 else 1) := by
  by_cases h : j = Fin.last ( n + 1 ) <;> simp_all +decide [ cellVert ];
  · rw [ show ( Finset.univ.filter fun x : Fin ( n + 1 ) => σ x = Fin.last n ) = { σ.symm ( Fin.last n ) } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ by aesop, fun x hx => σ.injective <| by aesop ⟩ ] ; aesop;
  · split_ifs <;> simp_all +decide [ Finset.filter_eq' ];
    · rw [ Finset.card_eq_one ];
      exact ⟨ σ.symm 0, by ext; simp +decide [ Equiv.eq_symm_apply ] ⟩;
    · rw [ Finset.card_eq_one.mpr, Finset.card_eq_one.mpr ];
      · norm_num;
      · obtain ⟨ a, ha ⟩ := Fin.exists_succ_eq_of_ne_zero ‹_›;
        use σ.symm a; ext x; aesop;
      · obtain ⟨ a, ha ⟩ := Fin.exists_castSucc_eq.mpr h; use σ.symm a; ext x; aesop;

/-
Coordinate formula for vertex `1` of a cell: only the first edge `σ 0` is included.
-/
lemma cellVert_one_all {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1))) (j : Fin (n+2)) :
    cellVert P σ 1 j
      = P j + (if (σ 0).castSucc = j then 1 else 0) - (if (σ 0).succ = j then 1 else 0) := by
  unfold cellVert; simp +decide [ Fin.sum_univ_succ ] ;
  ring

/-
The vertex `k0` of the interior-swapped cell differs from the original vertex `k0` by
removing edge `σ a` and adding edge `σ b`, where `a, b` are the swapped positions
(`a.val = k0.val - 1`, `b.val = k0.val`).
-/
lemma cellVert_swap_pivot_vertex {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1)))
    {k0 : Fin (n+2)} (a b : Fin (n+1)) (ha : a.val = k0.val - 1) (hb : b.val = k0.val)
    (h0 : k0 ≠ 0) (j : Fin (n+2)) :
    cellVert P ((Equiv.swap a b).trans σ) k0 j
      = cellVert P σ k0 j - edgeVec (σ a) j + edgeVec (σ b) j := by
  unfold cellVert edgeVec;
  simp +decide [ Finset.sum_ite, Equiv.swap_apply_def ];
  rw [ show ( Finset.filter ( fun x => x.castSucc < k0 ) Finset.univ : Finset ( Fin ( n + 1 ) ) ) = Finset.filter ( fun x => x.castSucc < k0 ∧ x ≠ a ∧ x ≠ b ) Finset.univ ∪ { a } from ?_, Finset.filter_union ];
  · rw [ Finset.filter_union, Finset.filter_singleton ] ; simp +decide [ Finset.filter_singleton ] ; ring;
    split_ifs <;> simp_all +decide [ Finset.filter_insert ] <;> try ring;
    all_goals congr! 3;
    all_goals first
      | exact congrArg Finset.card
          (Finset.filter_congr (by rintro x hx; simp_all +decide))
      | exact Finset.filter_congr (by rintro x hx; simp_all +decide);
  · ext x; by_cases hx : x = a <;> by_cases hx' : x = b <;> simp +decide [ * ] ;
    · grind;
    · exact Nat.lt_of_le_of_lt ( Nat.le_refl _ ) ( show ( a : ℕ ) < k0 from by omega );
    · exact iff_of_false ( by rw [ Fin.lt_def ] ; aesop ) ( by aesop )

/-
Consecutive vertices of a cell differ by one edge vector.
-/
lemma cellVert_consecutive {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1)))
    (k : Fin (n+1)) (j : Fin (n+2)) :
    cellVert P σ k.succ j = cellVert P σ k.castSucc j + edgeVec (σ k) j := by
  unfold cellVert edgeVec;
  rw [ Finset.sum_eq_add_sum_sdiff_singleton_of_mem ( Finset.mem_univ k ) ];
  rw [ Finset.sum_eq_add_sum_sdiff_singleton_of_mem ( Finset.mem_univ k ) ];
  simp +decide [ Finset.sum_ite ];
  rw [ show ( Finset.filter ( fun x => x ≤ k ) ( Finset.univ \ { k } ) ) = Finset.filter ( fun x => x < k ) ( Finset.univ \ { k } ) from Finset.filter_congr fun x hx => by rw [ le_iff_lt_or_eq, or_iff_left ( by aesop ) ] ] ; ring

/-
The vertex `k0` of the interior-swapped cell equals the (valid) vertex `a.castSucc`
immediately below `k0` plus the edge `σ b`.
-/
lemma cellVert_swap_pivot_vertex_below {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1)))
    {k0 : Fin (n+2)} (a b : Fin (n+1)) (ha : a.val = k0.val - 1) (hb : b.val = k0.val)
    (h0 : k0 ≠ 0) (j : Fin (n+2)) :
    cellVert P ((Equiv.swap a b).trans σ) k0 j = cellVert P σ a.castSucc j + edgeVec (σ b) j := by
  rw [ cellVert_swap_pivot_vertex ];
  · rw [ show k0 = Fin.succ a from Fin.ext ( by cases k0 using Fin.inductionOn <;> aesop ) ] ; linarith [ cellVert_consecutive P σ a j ] ;
  · exact ha;
  · exact hb;
  · assumption

/-
The components of an interior pivot (`k0 ≠ 0`, `k0 ≠ Fin.last (n+1)`): same base `P`,
the permutation with the two adjacent positions `a, b` swapped, and same omitted vertex.
-/
lemma pivot_interior_components {n : ℕ} (P : Fin (n+2) → ℤ) (σ : Equiv.Perm (Fin (n+1)))
    {k0 : Fin (n+2)} (h0 : k0 ≠ 0) (hlast : k0 ≠ Fin.last (n+1))
    (a b : Fin (n+1)) (ha : a.val = k0.val - 1) (hb : b.val = k0.val) :
    (pivot P σ k0).1.1 = P ∧ (pivot P σ k0).1.2 = (Equiv.swap a b).trans σ := by
  unfold pivot; simp +decide [ * ] ;
  congr 2 <;> aesop

/-
The `k0 = 0` endpoint case of `pivot_invalid_facet`.
-/
lemma pivot_invalid_facet_zero {n : ℕ} {m : ℤ} {P : Fin (n+2) → ℤ} {σ : Equiv.Perm (Fin (n+1))}
    (hv : ValidCell m P σ)
    (hinv : ¬ ValidCell m (pivot P σ 0).1.1 (pivot P σ 0).1.2) :
    ∃ j, ∀ k, k ≠ 0 → cellVert P σ k j = 0 := by
  by_cases hP : P (σ 0).succ = 0;
  · use (σ 0).succ;
    apply facet_coord_zero hv hP;
    grind +suggestions;
  · contrapose! hinv;
    intro k; by_cases hk : k = Fin.last _ <;> simp_all +decide [ pivot ] ;
    · constructor;
      · intro i; rw [ cellVert_last_all ] ; split_ifs <;> simp_all +decide [ cellVert_one_all ] ;
        · split_ifs <;> simp_all +decide [ ValidCell ];
          · have := hv 0; unfold IsLat at this; simp_all +decide [ cellVert ] ;
            obtain ⟨ k, hk₁, hk₂ ⟩ := hinv ( Fin.last ( n + 1 ) ) ; simp_all +decide [ Finset.sum_ite ] ;
            rw [ show ( Finset.filter ( fun x => σ x = Fin.last n ) ( Finset.filter ( fun x => x.castSucc < k ) Finset.univ ) ) = { 0 } from ?_ ] at hk₂ ; simp_all +decide [ Finset.filter_eq' ];
            · exact lt_of_le_of_ne ( this.1 _ ) ( Ne.symm hP ) |> lt_of_le_of_ne <| Ne.symm <| by omega;
            · ext x; simp [Finset.mem_filter, Finset.mem_univ];
              exact ⟨ fun hx => σ.injective <| by aesop, fun hx => ⟨ by subst hx; exact Fin.pos_iff_ne_zero.mpr hk₁, by subst hx; aesop ⟩ ⟩;
          · have := hv ( Fin.last _ ) ; simp_all +decide [ IsLat ] ;
            have := hv ( Fin.last _ ) ; simp_all +decide [ cellVert ] ;
            have := this.1 ( Fin.last _ ) ; simp_all +decide [ Finset.filter_eq' ] ;
            exact le_trans ( mod_cast Finset.card_pos.mpr ⟨ σ.symm ( Fin.last n ), by aesop ⟩ ) this;
        · have := hv 0; simp_all +decide [ IsLat ] ;
          unfold cellVert at this; simp_all +decide [ Fin.sum_univ_succ ] ;
          split_ifs <;> linarith [ this.1 0 ];
        · have := hv 0; have := this.1 i; simp_all +decide [ cellVert ] ;
          grind;
      · have hsum : ∀ (R : Fin (n + 2) → ℤ) (ρ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 2)), ∑ i, cellVert R ρ w i = ∑ i, R i := by
          unfold cellVert; simp +decide [ Finset.sum_add_distrib, Finset.sum_comm ] ;
        rw [ hsum, hv 1 |>.2 ];
    · obtain ⟨ w, rfl ⟩ := Fin.eq_castSucc_of_ne_last hk; simp_all +decide [ cellVert_pivot_zero ] ;
      exact hv _

/-
The interior case (`k0 ≠ 0` and `k0 ≠ Fin.last (n+1)`) of `pivot_invalid_facet`.
-/
lemma pivot_invalid_facet_interior {n : ℕ} {m : ℤ} {P : Fin (n+2) → ℤ}
    {σ : Equiv.Perm (Fin (n+1))} {k0 : Fin (n+2)} (h0 : k0 ≠ 0) (hlast : k0 ≠ Fin.last (n+1))
    (hv : ValidCell m P σ)
    (hinv : ¬ ValidCell m (pivot P σ k0).1.1 (pivot P σ k0).1.2) :
    ∃ j, ∀ k, k ≠ k0 → cellVert P σ k j = 0 := by
  obtain ⟨a, b, ha, hb, hk1⟩ : ∃ a b : Fin (n + 1), a.val = k0.val - 1 ∧ b.val = k0.val ∧ 1 ≤ k0.val := by
    refine' ⟨ ⟨ k0.val - 1, _ ⟩, ⟨ k0.val, _ ⟩, _, _, _ ⟩ <;> norm_num at *;
    · exact Nat.le_of_lt_succ ( Fin.is_lt k0 );
    · exact Nat.le_of_lt_succ ( lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using hlast ) );
    · exact Nat.pos_of_ne_zero fun h => h0 <| Fin.ext h;
  obtain ⟨j, hj⟩ : ∃ j, cellVert (pivot P σ k0).1.1 (pivot P σ k0).1.2 k0 j < 0 := by
    contrapose! hinv;
    intro k; by_cases hk : k = k0 <;> simp_all +decide [ pivot_interior_components ] ;
    · have hsum : ∀ (R : Fin (n + 2) → ℤ) (ρ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 2)), ∑ i, cellVert R ρ w i = ∑ i, R i := by
        unfold cellVert; simp +decide [ Finset.sum_add_distrib, Finset.sum_comm ] ;
      have := hv 0; simp_all +decide [ IsLat ] ;
      unfold pivot; aesop;
    · have hfacet : cellVert (pivot P σ k0).1.1 (pivot P σ k0).1.2 k = cellVert P σ k := by
        convert cellVert_swap_eq P σ a b k _ using 1;
        · rw [ pivot_interior_components P σ h0 hlast a b ha hb |>.1, pivot_interior_components P σ h0 hlast a b ha hb |>.2 ];
        · grind +suggestions;
      exact hfacet.symm ▸ hv k;
  have hcoord : j = (σ b).succ := by
    have hcoord : cellVert (pivot P σ k0).1.1 (pivot P σ k0).1.2 k0 j = cellVert P σ a.castSucc j + edgeVec (σ b) j := by
      rw [ pivot_interior_components P σ h0 hlast a b ha hb |>.1, pivot_interior_components P σ h0 hlast a b ha hb |>.2 ] ; exact cellVert_swap_pivot_vertex_below P σ a b ha hb h0 j;
    contrapose! hj;
    exact hcoord.symm ▸ add_nonneg ( hv _ |>.1 _ ) ( by unfold edgeVec; aesop );
  have hw0 : cellVert P σ a.castSucc (σ b).succ = 0 := by
    have := cellVert_swap_pivot_vertex_below P σ a b ha hb h0 j; simp_all +decide [ edgeVec ] ;
    have := hv a.castSucc; simp_all +decide [ IsLat ] ;
    grind +suggestions;
  have hPj : P (σ b).succ = 0 := by
    rw [ cellVert_coord_ind ] at hw0;
    have := hv 0; simp_all +decide [ IsLat ] ;
    split_ifs at hw0 <;> simp_all +decide [ cellVert_zero ];
    · linarith [ this.1 ( σ b |> Fin.succ ) ];
    · omega;
  have hin0 : ¬∃ l : Fin (n + 1), l.castSucc < a.castSucc ∧ (σ l).castSucc = (σ b).succ := by
    contrapose! hw0; simp_all +decide [ cellVert_coord_ind ] ;
    grind;
  refine' ⟨ ( σ b ).succ, fun k hk => facet_coord_zero hv hPj _ k hk ⟩;
  grind +suggestions

/-- **Pivot invalidity implies a boundary facet.** If the pivot of a valid cell at `k0` is
invalid, then all the facet vertices (those `≠ k0`) lie on a common coordinate hyperplane. -/
lemma pivot_invalid_facet {n : ℕ} {m : ℤ} {P : Fin (n+2) → ℤ} {σ : Equiv.Perm (Fin (n+1))}
    {k0 : Fin (n+2)} (hv : ValidCell m P σ)
    (hinv : ¬ ValidCell m (pivot P σ k0).1.1 (pivot P σ k0).1.2) :
    ∃ j, ∀ k, k ≠ k0 → cellVert P σ k j = 0 := by
  by_cases h0 : k0 = 0
  · subst h0; exact pivot_invalid_facet_zero hv hinv
  by_cases hlast : k0 = Fin.last (n+1)
  · subst hlast
    have hpe1 : (pivot P σ (Fin.last (n+1))).1.1 = (fun i => P i - edgeVec (σ (Fin.last n)) i) := by
      simp [pivot, h0]
    have hpe2 : (pivot P σ (Fin.last (n+1))).1.2 = (finRotate (n+1)).symm.trans σ := by
      simp [pivot, h0]
    rw [hpe1, hpe2] at hinv
    refine ⟨(σ (Fin.last n)).castSucc, ?_⟩
    have hPj : P (σ (Fin.last n)).castSucc = 0 := by
      by_contra hPne
      apply hinv
      intro k'
      induction k' using Fin.cases with
      | zero =>
        rw [cellVert_zero]
        refine ⟨fun i => ?_, ?_⟩
        · simp only [edgeVec]
          rcases eq_or_ne ((σ (Fin.last n)).castSucc) i with rfl | hi
          · have hge : 0 ≤ P ((σ (Fin.last n)).castSucc) := (hv 0).1 _ |>.trans_eq (by rw [cellVert_zero])
            have hne : (σ (Fin.last n)).succ ≠ (σ (Fin.last n)).castSucc := by
              simp [Fin.ext_iff, Fin.val_succ]
            rw [if_pos rfl, if_neg hne]; omega
          · rcases eq_or_ne ((σ (Fin.last n)).succ) i with rfl | hi2
            · rw [if_neg hi, if_pos rfl]
              have := (hv 0).1 ((σ (Fin.last n)).succ); rw [cellVert_zero] at this; omega
            · rw [if_neg hi, if_neg hi2]
              have := (hv 0).1 i; rw [cellVert_zero] at this; omega
        · have hsum : ∑ i, (P i - edgeVec (σ (Fin.last n)) i) = (∑ i, P i) - ∑ i, edgeVec (σ (Fin.last n)) i := by
            rw [Finset.sum_sub_distrib]
          rw [hsum]
          have he0 : ∑ i, edgeVec (σ (Fin.last n)) i = 0 := by
            simp only [edgeVec, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
            simp
          rw [he0, sub_zero]
          have := (hv 0).2; rwa [cellVert_zero] at this
      | succ k =>
        rw [cellVert_pivot_last]
        exact hv k.castSucc
    apply facet_coord_zero hv hPj
    rintro k hk ⟨l, hl1, hl2⟩
    have hll : l = Fin.last n := by
      have : (σ l).castSucc = (σ (Fin.last n)).castSucc := hl2
      have : σ l = σ (Fin.last n) := Fin.castSucc_injective _ this
      exact σ.injective this
    subst hll
    exfalso
    apply hk
    have hkv : (Fin.last n).castSucc < k := hl1
    rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last] at hkv
    have : k.val = n + 1 := by omega
    exact Fin.ext (by rw [this, Fin.val_last])
  · exact pivot_invalid_facet_interior h0 hlast hv hinv

/-- Structure of a boundary half-door: the omitted vertex is the base (`k0 = 0`), the first
edge points at the last coordinate (`σ 0 = Fin.last n`), and the last coordinate of the base
is `1`. -/
lemma boundary_door_struct {n : ℕ} {m : ℤ} (_hm : 1 ≤ m) (l : (Fin (n+2) → ℤ) → Fin (n+2))
    (hadm : ∀ p, IsLat m p → p (l p) ≠ 0) {x : ((Fin (n+2) → ℤ) × Equiv.Perm (Fin (n+1))) × Fin (n+2)}
    (hx : x ∈ boundaryDoors n m l) :
    x.2 = 0 ∧ x.1.2 0 = Fin.last n ∧ x.1.1 (Fin.last (n+1)) = 1 := by
  rw [boundaryDoors, Finset.mem_filter] at hx
  obtain ⟨hhalf, hinv⟩ := hx
  rw [halfDoors, Finset.mem_filter, Finset.mem_product] at hhalf
  obtain ⟨⟨hcellmem, _⟩, hdoor⟩ := hhalf
  rw [cellFin, Finset.mem_filter] at hcellmem
  have hv : ValidCell m x.1.1 x.1.2 := hcellmem.2
  obtain ⟨j, hj⟩ := pivot_invalid_facet hv hinv
  -- the door forces the common-zero coordinate to be the last one
  have hjlast : j = Fin.last (n+1) := by
    by_contra hjne
    have hjmem : j ∈ (Finset.univ.erase x.2).image (fun k => l (cellVert x.1.1 x.1.2 k)) := by
      rw [hdoor]; exact Finset.mem_erase.mpr ⟨hjne, Finset.mem_univ _⟩
    obtain ⟨k, hkmem, hkl⟩ := Finset.mem_image.mp hjmem
    have hkne : k ≠ x.2 := (Finset.mem_erase.mp hkmem).1
    have hne0 := hadm (cellVert x.1.1 x.1.2 k) (hv k)
    rw [hkl] at hne0
    exact hne0 (hj k hkne)
  subst hjlast
  -- last coordinate of base is ≥ 1
  have hPlast : 1 ≤ x.1.1 (Fin.last (n+1)) := by
    have h0 := (hv (Fin.last (n+1))).1 (Fin.last (n+1))
    rw [cellVert_last_coord, if_pos (Fin.castSucc_lt_last _)] at h0
    omega
  -- k0 = 0
  have hk0 : x.2 = 0 := by
    by_contra hk0ne
    have h := hj 0 (Ne.symm hk0ne)
    rw [cellVert_last_coord, if_neg (Fin.not_lt_zero _)] at h
    omega
  -- from vertex 1 (≠ 0) get the remaining facts
  have hone : (1 : Fin (n+2)) ≠ x.2 := by rw [hk0]; exact Fin.ext_iff.not.mpr (by simp)
  have h1 := hj 1 hone
  rw [cellVert_last_coord] at h1
  have hposlt : (x.1.2.symm (Fin.last n)).castSucc < (1 : Fin (n+2)) := by
    by_contra hcon
    rw [if_neg hcon] at h1
    omega
  have hPone : x.1.1 (Fin.last (n+1)) = 1 := by
    rw [if_pos hposlt] at h1; omega
  have hsig : x.1.2 0 = Fin.last n := by
    have hlt : (x.1.2.symm (Fin.last n)).val < 1 := by
      have h := hposlt
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_one] at h
      omega
    have hpos0 : x.1.2.symm (Fin.last n) = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    have h2 := congrArg x.1.2 hpos0
    rw [Equiv.apply_symm_apply] at h2
    exact h2.symm
  exact ⟨hk0, hsig, hPone⟩

/-
Every boundary half-door is the lift of a fully-labeled face cell.
-/
set_option maxRecDepth 16384 in
lemma boundary_isLift {n : ℕ} {m : ℤ} (hm : 1 ≤ m) (l : (Fin (n+2) → ℤ) → Fin (n+2))
    (hadm : ∀ p, IsLat m p → p (l p) ≠ 0) {x : ((Fin (n+2) → ℤ) × Equiv.Perm (Fin (n+1))) × Fin (n+2)}
    (hx : x ∈ boundaryDoors n m l) :
    ∃ c ∈ (cellFin n m).filter (fun pσ => IsFull (faceLabel l) pσ.1 pσ.2), x = liftCell c := by
  obtain ⟨c, hc⟩ : ∃ c : (Fin (n+1) → ℤ) × Equiv.Perm (Fin n), liftCell c = x := by
    obtain ⟨c, hc⟩ : ∃ c : Fin (n+1) → ℤ, x.1.1 = liftBase c := by
      use fun i => x.1.1 i.castSucc + edgeVec (Fin.last n) i.castSucc;
      ext i; induction i using Fin.lastCases <;> simp +decide [ *, liftBase, edgeVec ] ;
      exact boundary_door_struct hm l hadm hx |>.2.2;
    have := boundary_door_struct hm l hadm hx; obtain ⟨s, hs⟩ := exists_facePerm (by
    exact this.2.1 : x.1.2 0 = Fin.last n); use (c, s); aesop;
  unfold liftCell at *; simp_all +decide [ boundaryDoors, halfDoors ] ;
  refine' ⟨ c.1, c.2, ⟨ _, _ ⟩, hc.symm ⟩;
  · convert mem_cellFin ?_;
    unfold cellFin at hx; simp_all +decide [ ValidCell, IsLat ] ;
    intro k; specialize hx; have := hx.1.1.2 k.succ; simp_all +decide [ cellVert_lift_snoc ] ;
    subst hc;
    have := hx.1.1.2 k.succ;
    rw [ cellVert_lift_snoc ] at this;
    refine ⟨ fun i => by simpa using this.1 i.castSucc, ?_ ⟩;
    have hsum := this.2;
    rw [ Fin.sum_univ_castSucc ] at hsum; simpa using hsum;
  · subst hc; simp_all +decide [ IsFull ] ;
    rw [ show ( Finset.univ.erase 0 : Finset ( Fin ( n + 2 ) ) ) = Finset.image ( fun k : Fin ( n + 1 ) => Fin.succ k ) Finset.univ from ?_, Finset.image_image ] at hx;
    · intro i; replace hx := Finset.ext_iff.mp hx.1.2 ( i.castSucc ) ; simp_all +decide [ Finset.mem_image ] ;
      obtain ⟨ a, ha ⟩ := hx; use a; rw [ ← Fin.castSucc_inj ] ; simp_all +decide [ cellVert_lift_snoc ] ;
      unfold faceLabel; simp_all +decide [ Fin.snoc ] ;
    · ext ( _ | i ) <;> simp +decide [ Fin.ext_iff ]

/-
The lift map is injective.
-/
lemma liftCell_inj {n : ℕ} : Function.Injective (liftCell (n := n)) := by
  -- To prove injectivity, we show that if `liftCell c₁ = liftCell c₂`, then `c₁` must equal `c₂`.
  intro c₁ c₂ h_eq
  simp [liftCell] at h_eq;
  -- By definition of `liftBase`, we have `liftBase c₁.1 = liftBase c₂.1`.
  have h_base : c₁.1 = c₂.1 := by
    ext i; exact (by
    have := congr_fun h_eq.1 ( Fin.castSucc i ) ; simp_all +decide [ liftBase, edgeVec ] ;);
  simp_all +decide [ funext_iff, liftPerm ];
  simp_all +decide [ Equiv.ext_iff, Fin.forall_fin_succ ];
  exact Prod.ext ( funext fun i => by induction i using Fin.inductionOn <;> aesop ) ( Equiv.ext fun i => h_eq i )

/-- The boundary half-doors biject with the fully-labeled cells of the `x_last = 0` face. -/
lemma boundaryDoors_card_eq {n : ℕ} {m : ℤ} (hm : 1 ≤ m)
    (l : (Fin (n+2) → ℤ) → Fin (n+2))
    (hadm : ∀ p, IsLat m p → p (l p) ≠ 0) :
    (boundaryDoors n m l).card
      = ((cellFin n m).filter (fun pσ => IsFull (faceLabel l) pσ.1 pσ.2)).card := by
  have key : boundaryDoors n m l
      = ((cellFin n m).filter (fun pσ => IsFull (faceLabel l) pσ.1 pσ.2)).image liftCell := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := boundary_isLift hm l hadm hx
      exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    · intro y hy
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
      exact liftCell_mem hm l hadm hc
  rw [key, Finset.card_image_of_injOn (Function.Injective.injOn liftCell_inj)]

/-- **Facet-side parity.** The number of half-doors (dimension `n+1`) has the same parity
as the number of fully-labeled cells of the `x_last = 0` face (dimension `n`). -/
lemma halfDoors_card_modEq_face {n : ℕ} {m : ℤ} (hm : 1 ≤ m)
    (l : (Fin (n+2) → ℤ) → Fin (n+2))
    (hadm : ∀ p, IsLat m p → p (l p) ≠ 0) :
    (halfDoors (n+1) m l).card
      ≡ ((cellFin n m).filter (fun pσ => IsFull (faceLabel l) pσ.1 pσ.2)).card [MOD 2] := by
  have h1 := halfDoors_card_modEq_boundary (m := m) l
  rw [boundaryDoors_card_eq hm l hadm] at h1
  exact h1

/-- **Inductive step (facet side).** Given Sperner's parity in dimension `n`, it holds in
dimension `n+1`. -/
lemma sperner_step {n : ℕ} {m : ℤ} (hm : 1 ≤ m)
    (ih : ∀ (l : (Fin (n+1) → ℤ) → Fin (n+1)),
        (∀ p, IsLat m p → p (l p) ≠ 0) →
        Odd ((cellFin n m).filter (fun pσ => IsFull l pσ.1 pσ.2)).card)
    (l : (Fin (n+2) → ℤ) → Fin (n+2))
    (hadm : ∀ p, IsLat m p → p (l p) ≠ 0) :
    Odd ((cellFin (n+1) m).filter (fun pσ => IsFull l pσ.1 pσ.2)).card := by
  have h1 := halfDoors_card_modEq (n := n+1) (m := m) l
  have h2 := halfDoors_card_modEq_face hm l hadm
  have h3 := ih (faceLabel l) (faceLabel_admissible l hadm)
  have h4 := h1.symm.trans h2
  rw [Nat.odd_iff] at h3 ⊢
  rw [Nat.ModEq] at h4
  omega

/-- **Sperner parity**: the number of valid fully-labeled cells is odd. -/
lemma sperner_card_odd {n : ℕ} {m : ℤ} (hm : 1 ≤ m)
    (l : (Fin (n+1) → ℤ) → Fin (n+1))
    (hadm : ∀ p : Fin (n+1) → ℤ, IsLat m p → p (l p) ≠ 0) :
    Odd ((cellFin n m).filter (fun pσ => IsFull l pσ.1 pσ.2)).card := by
  induction n with
  | zero => exact sperner_card_odd_zero hm l hadm
  | succ n ih => exact sperner_step hm (fun l' hadm' => ih l' hadm') l hadm

/-- **Sperner's lemma** (existence form): an admissible labeling of the lattice has a
fully-labeled (panchromatic) cell. -/
lemma sperner {n : ℕ} {m : ℤ} (hm : 1 ≤ m)
    (l : (Fin (n+1) → ℤ) → Fin (n+1))
    (hadm : ∀ p : Fin (n+1) → ℤ, IsLat m p → p (l p) ≠ 0) :
    ∃ (P : Fin (n+1) → ℤ) (σ : Equiv.Perm (Fin n)),
      ValidCell m P σ ∧ Surjective (fun k => l (cellVert P σ k)) := by
  have hodd := sperner_card_odd hm l hadm
  have hne : ((cellFin n m).filter (fun pσ => IsFull l pσ.1 pσ.2)).Nonempty := by
    rw [← Finset.card_pos]; exact hodd.pos
  obtain ⟨⟨P, σ⟩, hmem⟩ := hne
  rw [Finset.mem_filter] at hmem
  obtain ⟨hcell, hfull⟩ := hmem
  rw [cellFin, Finset.mem_filter] at hcell
  exact ⟨P, σ, hcell.2, hfull⟩

/-
The base vertex (`k = 0`) of a cell is its base point.
-/
/-
Each coordinate of every vertex of a cell is within `n` of the base point.
-/
lemma cellVert_coord_dist {n : ℕ} (P : Fin (n+1) → ℤ) (σ : Equiv.Perm (Fin n))
    (k j : Fin (n+1)) : |cellVert P σ k j - P j| ≤ (n : ℤ) := by
  unfold cellVert;
  simp +zetaDelta at *;
  exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum fun i hi ↦ show |_| ≤ 1 by split_ifs <;> norm_num ) ( by norm_num ) )

/-
On the simplex, there is always a coordinate that is positive and not increased by `f`.
-/
lemma exists_label {n : ℕ} (x fx : Fin n → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin n)) (hfx : fx ∈ stdSimplex ℝ (Fin n)) :
    ∃ i, 0 < x i ∧ fx i ≤ x i := by
  by_contra! h_contra;
  -- Since $x$ is in the standard simplex, there must be some $i$ such that $0 < x_i$.
  obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
    exact not_forall_not.mp fun h => by have := hx.2; rw [ Finset.sum_congr rfl fun i _ => le_antisymm ( le_of_not_gt fun hi => h i hi ) ( hx.1 i ) ] at this; aesop;
  have h_sum : ∑ i, x i < ∑ i, fx i := by
    exact Finset.sum_lt_sum ( fun j _ => if hj : 0 < x j then le_of_lt ( h_contra j hj ) else by linarith [ hx.1 j, hfx.1 j ] ) ⟨ i, Finset.mem_univ i, h_contra i hi ⟩;
  linarith [ hx.2, hfx.2 ]

/-- The real point associated to a lattice point at resolution `m`. -/
noncomputable def ptOf {n : ℕ} (m : ℕ) (p : Fin (n+1) → ℤ) : Fin (n+1) → ℝ := fun i => (p i : ℝ) / m

/-
Approximate fixed point at resolution `m`, via Sperner's lemma.
-/
lemma simplex_approx {n : ℕ}
    (f : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ))
    (hmaps : MapsTo f (stdSimplex ℝ (Fin (n+1))) (stdSimplex ℝ (Fin (n+1))))
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ z ∈ stdSimplex ℝ (Fin (n+1)), ∀ i, ∃ w ∈ stdSimplex ℝ (Fin (n+1)),
      (∀ j, |w j - z j| ≤ (n : ℝ) / m) ∧ f w i ≤ w i := by
  revert hm f hmaps;
  intro f hf hm
  have h_ptmem : ∀ p : Fin (n + 1) → ℤ, IsLat (m : ℤ) p → ptOf m p ∈ stdSimplex ℝ (Fin (n + 1)) := by
    unfold IsLat ptOf stdSimplex;
    simp +contextual [ ← Finset.sum_div _ _ _, ne_of_gt ( zero_lt_one.trans_le hm ) ];
    exact fun p hp₁ hp₂ => ⟨ fun i => div_nonneg ( mod_cast hp₁ i ) ( by positivity ), by rw [ ← Int.cast_sum, hp₂, Int.cast_natCast, div_self ( by positivity ) ] ⟩;
  obtain ⟨l, hl⟩ : ∃ l : (Fin (n + 1) → ℤ) → Fin (n + 1), (∀ p : Fin (n + 1) → ℤ, IsLat (m : ℤ) p → p (l p) ≠ 0) ∧ (∀ p : Fin (n + 1) → ℤ, IsLat (m : ℤ) p → 0 < ptOf m p (l p) ∧ f (ptOf m p) (l p) ≤ ptOf m p (l p)) := by
    have h_exists_label : ∀ p : Fin (n + 1) → ℤ, IsLat (m : ℤ) p → ∃ i : Fin (n + 1), 0 < ptOf m p i ∧ f (ptOf m p) i ≤ ptOf m p i := by
      exact fun p hp => exists_label _ _ ( h_ptmem p hp ) ( hf ( h_ptmem p hp ) );
    choose! l hl₁ hl₂ using h_exists_label;
    refine' ⟨ l, _, _ ⟩ <;> intro p hp <;> specialize hl₁ p hp <;> specialize hl₂ p hp <;> simp_all +decide [ ptOf ];
    exact fun h => by norm_num [ h ] at hl₁;
  obtain ⟨ P, σ, hPσ, hsurj ⟩ := sperner ( show ( 1 : ℤ ) ≤ m by norm_cast ) l hl.1;
  refine' ⟨ ptOf m P, h_ptmem P _, fun i => _ ⟩;
  · simpa [ cellVert_zero ] using hPσ 0;
  · obtain ⟨ k, hk ⟩ := hsurj i;
    refine' ⟨ ptOf m ( cellVert P σ k ), h_ptmem _ ( hPσ k ), _, _ ⟩ <;> simp_all +decide [ ptOf ];
    · intro j; rw [ ← sub_div ] ; rw [ abs_div ] ; norm_num [ abs_of_nonneg, hm ] ;
      gcongr ; norm_cast ; exact cellVert_coord_dist P σ k j;
    · simpa only [ hk ] using hl.2 ( cellVert P σ k ) ( hPσ k ) |>.2

/-
Brouwer's fixed point theorem for the standard simplex (deep combinatorial core).
-/
lemma simplex_brouwer {n : ℕ} (hn : 0 < n)
    (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf : ContinuousOn f (stdSimplex ℝ (Fin n)))
    (hmaps : MapsTo f (stdSimplex ℝ (Fin n)) (stdSimplex ℝ (Fin n))) :
    ∃ x ∈ stdSimplex ℝ (Fin n), f x = x := by
  -- By definition of $n$, we know that $n = n' + 1$ for some $n'$.
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := Nat.exists_eq_succ_of_ne_zero hn.ne';
  -- By `simplex_approx`, for each `k : ℕ` apply `simplex_approx f hmaps (k+1) (by omega)` and use choice to obtain:
  have h_seq : ∀ k : ℕ, ∃ z ∈ stdSimplex ℝ (Fin (n' + 1)), ∀ i, ∃ w ∈ stdSimplex ℝ (Fin (n' + 1)), (∀ j, |w j - z j| ≤ (n' : ℝ) / (k + 1)) ∧ f w i ≤ w i := by
    intro k;
    convert simplex_approx f hmaps ( k + 1 ) ( by linarith ) using 1;
    norm_cast;
  choose z hz w hw hw' hw'' using h_seq;
  -- By `(isCompact_stdSimplex (Fin (n'+1))).tendsto_subseq hz` get `x ∈ stdSimplex`, a strictly monotone `φ : ℕ → ℕ`, with `Tendsto (z ∘ φ) atTop (𝓝 x)`.
  obtain ⟨x, hx, φ, hφ_mono, hφ_tendsto⟩ : ∃ x ∈ stdSimplex ℝ (Fin (n' + 1)), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (fun k => z (φ k)) Filter.atTop (nhds x) := by
    have h_compact : IsCompact (stdSimplex ℝ (Fin (n' + 1))) :=
      isCompact_stdSimplex ℝ _;
    have := h_compact.isSeqCompact fun k => hz k; aesop;
  -- Claim for each `i`: `Tendsto (fun k => w (φ k) i) atTop (𝓝 x)`.
  have h_w_tendsto : ∀ i, Filter.Tendsto (fun k => w (φ k) i) Filter.atTop (nhds x) := by
    intro i
    have h_w_tendsto_i : ∀ j, Filter.Tendsto (fun k => w (φ k) i j) Filter.atTop (nhds (x j)) := by
      intro j
      have h_w_tendsto_i_j : Filter.Tendsto (fun k => w (φ k) i j - z (φ k) j) Filter.atTop (nhds 0) := by
        exact squeeze_zero_norm ( fun k => hw' _ _ _ ) ( tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ <| tendsto_natCast_atTop_atTop.comp hφ_mono.tendsto_atTop );
      simpa using h_w_tendsto_i_j.add ( tendsto_pi_nhds.mp hφ_tendsto j );
    exact tendsto_pi_nhds.mpr h_w_tendsto_i;
  -- Then `f` is continuous within the simplex at `x` (`hf.continuousWithinAt hx`), and `w (φ k) i ∈ stdSimplex` with `w (φ k) i → x`, so `Tendsto (fun k => f (w (φ k) i)) atTop (𝓝 (f x))`.
  have h_f_tendsto : ∀ i, Filter.Tendsto (fun k => f (w (φ k) i)) Filter.atTop (nhds (f x)) := by
    intro i;
    apply Filter.Tendsto.comp;
    apply_rules [ ContinuousOn.continuousWithinAt ];
    exact tendsto_nhdsWithin_iff.mpr ⟨ h_w_tendsto i, Filter.Eventually.of_forall fun k => hw _ _ ⟩;
  -- This holds for every `i`. Since `x, f x ∈ stdSimplex`, `∑ i, x i = 1 = ∑ i, f x i`, so `∑ i, (x i - f x i) = 0` with every term `x i - f x i ≥ 0`; by `Finset.sum_eq_zero_iff_of_nonneg` each `x i - f x i = 0`, i.e. `f x = x` (funext).
  have h_eq : ∀ i, f x i ≤ x i := by
    exact fun i => le_of_tendsto_of_tendsto' ( tendsto_pi_nhds.mp ( h_f_tendsto i ) i ) ( tendsto_pi_nhds.mp ( h_w_tendsto i ) i ) fun k => hw'' ( φ k ) i;
  have h_sum_eq : ∑ i, f x i = ∑ i, x i := by
    have := hmaps hx; simp_all +decide [ stdSimplex ] ;
  exact ⟨ x, hx, funext fun i => le_antisymm ( h_eq i ) ( by simpa [ h_sum_eq ] using Finset.single_le_sum ( fun i _ => sub_nonneg_of_le ( h_eq i ) ) ( Finset.mem_univ i ) ) ⟩


end BrouwerProof.Sperner

namespace BrouwerProof

open Set Function


/-- The fixed point property for a subset `s` of a topological space:
every continuous self-map of the subspace `s` has a fixed point. -/
def HasFPP {V : Type*} [TopologicalSpace V] (s : Set V) : Prop :=
  ∀ g : s → s, Continuous g → ∃ x : s, g x = x

/-
The fixed point property transfers along a homeomorphism of subspaces.
-/
lemma HasFPP.congr {V W : Type*} [TopologicalSpace V] [TopologicalSpace W]
    {s : Set V} {t : Set W} (e : s ≃ₜ t) (hs : HasFPP s) : HasFPP t := by
  intro g hg;
  obtain ⟨ x, hx ⟩ := hs ( fun x => e.symm ( g ( e x ) ) ) ( e.symm.continuous.comp ( hg.comp e.continuous ) );
  exact ⟨ e x, by simpa [ eq_comm ] using congr_arg e hx ⟩

/-
If `s ⊆ t`, `r : t → s` is a continuous retraction (identity on `s`), and `t`
has the fixed point property, then so does `s`.
-/
lemma HasFPP.of_retract {V : Type*} [TopologicalSpace V] {s t : Set V} (hst : s ⊆ t)
    (r : t → s) (hr : Continuous r) (hid : ∀ x : s, (r ⟨(x : V), hst x.2⟩ : V) = (x : V))
    (ht : HasFPP t) : HasFPP s := by
  intro g hg;
  obtain ⟨ x, hx ⟩ := ht ( fun y => ⟨ g ( r y ), by
    exact hst ( g ( r y ) |>.2 ) ⟩ ) ( by
    fun_prop )
  generalize_proofs at *;
  grind

/-
The fixed point property, in terms of `ContinuousOn`/`MapsTo`.
-/
lemma fixed_of_hasFPP {V : Type*} [TopologicalSpace V] {s : Set V} (hs : HasFPP s)
    {f : V → V} (hf : ContinuousOn f s) (hmap : MapsTo f s s) : ∃ x ∈ s, f x = x := by
  obtain ⟨x, hx⟩ : ∃ x : s, (fun x : s => ⟨f x, hmap x.2⟩ : s → s) x = x := by
    apply hs;
    exact Continuous.subtype_mk ( hf.comp_continuous ( continuous_subtype_val ) fun x => x.2 ) _;
  grind

/-
The nearest-point projection onto a closed convex nonempty set is a continuous
retraction.
-/
lemma exists_continuous_retraction {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) (hK_nonempty : K.Nonempty) :
    ∃ r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      Continuous r ∧ (∀ x, r x ∈ K) ∧ (∀ x ∈ K, r x = x) := by
  obtain ⟨r, hr⟩ : ∃ r : EuclideanSpace ℝ (Fin d) → K, ∀ u, ‖u - r u‖ = ⨅ w : K, ‖u - w‖ := by
    have := fun u => exists_norm_eq_iInf_of_complete_convex hK_nonempty ( hK_closed.isComplete ) hK_convex u;
    exact ⟨ fun u => ⟨ Classical.choose ( this u ), Classical.choose_spec ( this u ) |>.1 ⟩, fun u => Classical.choose_spec ( this u ) |>.2 ⟩;
  have h_var : ∀ u : EuclideanSpace ℝ (Fin d), ∀ w : K, inner ℝ (u - r u) (w - r u) ≤ 0 := by
    intro u w; have := hr u; exact (by
    convert ( norm_eq_iInf_iff_real_inner_le_zero hK_convex ( r u |>.2 ) ) |>.1 ( hr u ) w w.2 using 1);
  have h_lip : ∀ u v : EuclideanSpace ℝ (Fin d), ‖(r u : EuclideanSpace ℝ (Fin d)) - (r v : EuclideanSpace ℝ (Fin d))‖ ≤ ‖u - v‖ := by
    intros u v
    have h_inner : inner ℝ (u - v) ((r u : EuclideanSpace ℝ (Fin d)) - (r v : EuclideanSpace ℝ (Fin d))) ≥ ‖(r u : EuclideanSpace ℝ (Fin d)) - (r v : EuclideanSpace ℝ (Fin d))‖^2 := by
      have := h_var u ( r v ) ; have := h_var v ( r u ) ; simp_all +decide [ inner_sub_left, inner_sub_right ] ;
      have := h_var u ( r v ) ( r v |>.2 ) ; have := h_var v ( r u ) ( r u |>.2 ) ; simp_all +decide [ real_inner_comm ] ;
      rw [ @norm_sub_sq ℝ ] ; norm_num [ real_inner_comm, real_inner_self_eq_norm_sq ] ; linarith [ h_var v ( r u ) ( r u |>.2 ) ] ;
    nlinarith [ norm_nonneg ( u - v ), norm_nonneg ( ( r u : EuclideanSpace ℝ ( Fin d ) ) - ( r v : EuclideanSpace ℝ ( Fin d ) ) ), abs_le.mp ( abs_real_inner_le_norm ( u - v ) ( ( r u : EuclideanSpace ℝ ( Fin d ) ) - ( r v : EuclideanSpace ℝ ( Fin d ) ) ) ) ];
  refine' ⟨ fun u => r u, _, _, _ ⟩;
  · rw [ Metric.continuous_iff ];
    exact fun u ε hε => ⟨ ε, hε, fun v hv => lt_of_le_of_lt ( h_lip _ _ ) hv ⟩;
  · exact fun u => r u |>.2;
  · intro x hx; specialize hr x; specialize h_var x ⟨ x, hx ⟩ ; simp_all +decide [ inner_self_eq_norm_sq_to_K ] ;
    exact Eq.symm ( sub_eq_zero.mp hr )

/-- A nonempty compact convex set contained in a set with FPP also has FPP
(via the nearest-point retraction). -/
lemma hasFPP_of_subset {d : ℕ} {K T : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) (hK_nonempty : K.Nonempty)
    (hKT : K ⊆ T) (hT : HasFPP T) : HasFPP K := by
  obtain ⟨r, hr_cont, hr_mem, hr_id⟩ :=
    exists_continuous_retraction hK_compact.isClosed hK_convex hK_nonempty
  refine HasFPP.of_retract hKT (fun b => ⟨r (b : EuclideanSpace ℝ (Fin d)), hr_mem _⟩) ?_ ?_ hT
  · exact (hr_cont.comp continuous_subtype_val).subtype_mk _
  · intro x
    exact hr_id (x : EuclideanSpace ℝ (Fin d)) x.2

/-- The standard simplex inside `EuclideanSpace ℝ (Fin n)`. -/
def euclSimplex (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- The "corner" simplex inside `EuclideanSpace ℝ (Fin d)`:
`{x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}`. -/
def cornerSimplex (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-
The standard simplex is closed.
-/
lemma euclSimplex_isClosed (n : ℕ) : IsClosed (euclSimplex n) := by
  unfold euclSimplex;
  simp +decide only [setOf_and, setOf_forall];
  refine' IsClosed.inter ( isClosed_iInter fun i => isClosed_le continuous_const <| _ ) ( isClosed_eq _ _ ); all_goals fun_prop

/-
The standard simplex is compact.
-/
lemma euclSimplex_isCompact (n : ℕ) : IsCompact (euclSimplex n) := by
  refine' Metric.isCompact_iff_isClosed_bounded.mpr ⟨ euclSimplex_isClosed n, _ ⟩;
  refine' isBounded_iff_forall_norm_le.mpr ⟨ 1, _ ⟩;
  simp +decide [ EuclideanSpace.norm_eq, euclSimplex ];
  exact fun x hx₁ hx₂ => hx₂ ▸ Finset.sum_le_sum fun i _ => pow_le_of_le_one ( hx₁ i ) ( hx₂ ▸ Finset.single_le_sum ( fun a _ => hx₁ a ) ( Finset.mem_univ i ) ) ( by norm_num )

/-
The standard simplex is nonempty (for `n ≥ 1`).
-/
lemma euclSimplex_nonempty {n : ℕ} (hn : 0 < n) : (euclSimplex n).Nonempty := by
  refine' ⟨ EuclideanSpace.single ⟨ 0, hn ⟩ 1, _, _ ⟩ <;> norm_num;
  exact fun i => by split_ifs <;> norm_num;

/-
If every continuous self-map (as a `ContinuousOn`/`MapsTo` pair) of `s` has a fixed
point, then `s` has the fixed point property.
-/
lemma hasFPP_of_continuousOn {V : Type*} [TopologicalSpace V] {s : Set V}
    (h : ∀ f : V → V, ContinuousOn f s → MapsTo f s s → ∃ x ∈ s, f x = x) : HasFPP s := by
  intro g hg;
  convert h ( fun x => if hx : x ∈ s then g ⟨ x, hx ⟩ else x ) _ _ using 1;
  any_goals intro x; exact Classical.propDecidable _;
  · grind;
  · rw [ continuousOn_iff_continuous_restrict ];
    convert continuous_subtype_val.comp hg using 1;
    grind;
  · intro x hx; aesop;

/-- `HasFPP` for the standard simplex in `Fin n → ℝ`, from the Sperner core. -/
lemma stdSimplex_hasFPP {n : ℕ} (hn : 0 < n) : HasFPP (stdSimplex ℝ (Fin n)) :=
  hasFPP_of_continuousOn (fun f hf hmaps => Sperner.simplex_brouwer hn f hf hmaps)

/-
The continuous-linear equivalence `EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ)` maps the
Euclidean simplex onto the standard simplex.
-/
lemma image_equiv_euclSimplex (n : ℕ) :
    (EuclideanSpace.equiv (Fin n) ℝ) '' euclSimplex n = stdSimplex ℝ (Fin n) := by
  aesop

/-- **Brouwer for the standard simplex**, transferred from `Sperner.simplex_brouwer`. -/
lemma euclSimplex_hasFPP {n : ℕ} (hn : 0 < n) : HasFPP (euclSimplex n) := by
  have e : (euclSimplex n) ≃ₜ (stdSimplex ℝ (Fin n)) :=
    ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.image (euclSimplex n)).trans
      (Homeomorph.setCongr (image_equiv_euclSimplex n))
  exact (stdSimplex_hasFPP hn).congr e.symm

/-
The corner simplex has the fixed point property (transferred from `euclSimplex (d+1)`).
-/
lemma cornerSimplex_hasFPP (d : ℕ) : HasFPP (cornerSimplex d) := by
  convert euclSimplex_hasFPP ( Nat.succ_pos d ) |> HasFPP.congr ( ?_ ) using 1;
  -- Define the map $\phi : \text{euclSimplex } (d+1) \to \text{cornerSimplex } d$ by dropping the last coordinate.
  set phi : (EuclideanSpace ℝ (Fin (d + 1))) → (EuclideanSpace ℝ (Fin d)) := fun a => (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => a (i.castSucc));
  -- To prove the homeomorphism, we show that $\phi$ is continuous, bijective, and has a continuous inverse.
  have h_cont : Continuous (fun a : {a : EuclideanSpace ℝ (Fin (d + 1)) | a ∈ euclSimplex (d + 1)} => ⟨phi a, by
    constructor;
    · exact fun i => a.2.1 _;
    · have := a.2.2; simp_all +decide [ Fin.sum_univ_castSucc ] ;
      exact this ▸ le_add_of_nonneg_right ( a.2.1 _ )⟩ : {a : EuclideanSpace ℝ (Fin (d + 1)) | a ∈ euclSimplex (d + 1)} → {a : EuclideanSpace ℝ (Fin d) | a ∈ cornerSimplex d}) := by
    refine' Continuous.subtype_mk _ _;
    refine' Continuous.comp _ _; all_goals fun_prop
  generalize_proofs at *;
  -- Define the inverse map $\psi : \text{cornerSimplex } d \to \text{euclSimplex } (d+1)$ by adding a last coordinate that is $1 - \sum_{i=0}^{d-1} y_i$.
  set psi : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin (d + 1))) := fun y => (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm (Fin.snoc (fun i => y i) (1 - ∑ i, y i));
  -- Show that $\psi$ is continuous.
  have h_cont_psi : Continuous (fun y : {a : EuclideanSpace ℝ (Fin d) | a ∈ cornerSimplex d} => ⟨psi y, by
    simp +zetaDelta at *;
    constructor <;> norm_num [ Fin.sum_univ_castSucc ];
    intro i; refine' Fin.lastCases _ _ i <;> simp +decide [ * ] ;
    · exact y.2.2;
    · exact fun i => y.2.1 i⟩ : {a : EuclideanSpace ℝ (Fin d) | a ∈ cornerSimplex d} → {a : EuclideanSpace ℝ (Fin (d + 1)) | a ∈ euclSimplex (d + 1)}) := by
    refine' Continuous.subtype_mk _ _;
    refine' Continuous.comp _ _;
    · fun_prop;
    · refine' continuous_pi_iff.mpr _;
      intro i; induction i using Fin.lastCases <;> simp +decide [ *, Fin.snoc ] ;
      · fun_prop;
      · fun_prop
  generalize_proofs at *;
  fapply Homeomorph.mk;
  refine' ⟨ fun a => ⟨ phi a, by
    exact? ⟩, fun b => ⟨ psi b, by
    exact? ⟩, fun a => _, fun b => _ ⟩
  all_goals generalize_proofs at *;
  · ext i; simp [phi, psi];
    refine' Fin.lastCases _ _ i <;> simp +decide [ Fin.snoc ];
    have := a.2.2; simp_all +decide [ Fin.sum_univ_castSucc ] ;
    linarith;
  · ext i; simp [phi, psi];
  · exact h_cont;
  · exact h_cont_psi

/-
Any nonempty compact set `K` is contained in some set with the fixed point property.
-/
lemma exists_container {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty) :
    ∃ T : Set (EuclideanSpace ℝ (Fin d)), K ⊆ T ∧ HasFPP T := by
  revert hK_compact hK_nonempty K;
  intro K hK_compact hK_nonempty
  obtain ⟨M, hM⟩ : ∃ M ≥ 0, ∀ x ∈ K, ∀ i, abs (x i) ≤ M := by
    obtain ⟨ M, hM ⟩ := hK_compact.isBounded.exists_pos_norm_le;
    simp_all +decide [ EuclideanSpace.norm_eq ];
    exact ⟨ M, hM.1.le, fun x hx i => le_trans ( Real.abs_le_sqrt <| Finset.single_le_sum ( fun a _ => sq_nonneg <| x.ofLp a ) <| Finset.mem_univ i ) ( hM.2 x hx ) ⟩;
  -- Set `a := 2 * (d : ℝ) * M + 1`, so `a > 0` (since `d, M ≥ 0`), in particular `a ≠ 0`. Set the constant vector `b := (EuclideanSpace.equiv (Fin d) ℝ).symm (fun _ => -M)`, whose every coordinate is `-M`.
  set a := 2 * (d : ℝ) * M + 1 with ha
  have ha_pos : 0 < a := by
    exact add_pos_of_nonneg_of_pos ( mul_nonneg ( mul_nonneg zero_le_two ( Nat.cast_nonneg _ ) ) hM.1 ) zero_lt_one
  set b : EuclideanSpace ℝ (Fin d) := (EuclideanSpace.equiv (Fin d) ℝ).symm (fun _ => -M) with hb;
  -- Define the homeomorphism `e := (Homeomorph.smulOfNeZero a (by positivity : a ≠ 0)).trans (Homeomorph.addLeft b)`, so `e z = b + a • z`, with coordinates `(e z) i = -M + a * z i`.
  set e : EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d) := (Homeomorph.smulOfNeZero a (by positivity : a ≠ 0)).trans (Homeomorph.addLeft b) with he;
  refine' ⟨ e '' cornerSimplex d, _, _ ⟩;
  · intro x hx; use ( EuclideanSpace.equiv ( Fin d ) ℝ ).symm ( fun i => ( x i + M ) / a ) ; simp_all +decide [ div_eq_inv_mul ] ;
    refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
    · exact fun i => mul_nonneg ( inv_nonneg.2 ha_pos.le ) ( by linarith [ abs_le.mp ( hM.2 x hx i ) ] );
    · refine' le_trans ( Finset.sum_le_sum fun i _ => show ( 2 * d * M + 1 ) ⁻¹ * ( x.ofLp i + M ) ≤ ( 2 * d * M + 1 ) ⁻¹ * ( M + M ) from mul_le_mul_of_nonneg_left ( by linarith [ abs_le.mp ( hM.2 x hx i ) ] ) ( by positivity ) ) _ ; norm_num [ ← Finset.mul_sum _ _ _, ha_pos.ne' ];
      rw [ inv_mul_le_iff₀ ] <;> nlinarith [ show ( d : ℝ ) * M ≥ 0 by exact mul_nonneg ( Nat.cast_nonneg _ ) hM.1 ];
    · ext i; simp +decide [ mul_assoc, mul_left_comm ] ;
      grind;
  · convert HasFPP.congr ( Homeomorph.image e ( cornerSimplex d ) ) ( cornerSimplex_hasFPP d ) using 1

/-- Every nonempty compact convex set has the fixed point property. -/
lemma convexCompact_hasFPP {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) (hK_nonempty : K.Nonempty) :
    HasFPP K := by
  obtain ⟨T, hKT, hT⟩ := exists_container hK_compact hK_nonempty
  exact hasFPP_of_subset hK_compact hK_convex hK_nonempty hKT hT

end BrouwerProof

open Set Function BrouwerProof in
lemma brouwer_fixed_point {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (_hK_compact : IsCompact K) (_hK_convex : Convex ℝ K)
    (_hK_nonempty : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (_hf_cont : ContinuousOn f K) (_hf_maps : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  exact fixed_of_hasFPP
    (convexCompact_hasFPP _hK_compact _hK_convex _hK_nonempty) _hf_cont _hf_maps

-- Trust check: must report only `propext`, `Classical.choice`, `Quot.sound`.
#print axioms brouwer_fixed_point

end LogicalInduction
