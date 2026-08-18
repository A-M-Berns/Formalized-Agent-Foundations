import FactoredSpaces.PerfectMap

/-!
# Worked examples: non-vacuity witnesses and convention regression tests

Nothing here is a paper node.  The file exists for two reasons.

1. **Non-vacuity.** The library's §4 and §5.2 vocabulary is otherwise never instantiated,
   so a reader cannot tell from the artifact alone that `Disintegrates`, `history`,
   `StructIndep`, `Factorizes`, `IsFactoredSpaceModel`, `FactorizesOverDAG` and
   `Digraph.DSeparated` have inhabitants and non-inhabitants — i.e. that the definitions
   are neither empty nor trivially true.  The paper's two-coin example and its "every
   distribution has a one-factor model" remark are checked here against the Lean
   definitions, and each of the paper's three *factorizes* predicates is also refuted on a
   concrete object: `not_isFactoredSpaceModel_const` (Definition 4.4, a constant
   observation variable against a non-degenerate law), `not_factorizes_diag`
   (Definition 4.3) and `not_factorizesOverDAG_diag` (§5.2, eq. (2)), the last two on the
   perfectly-correlated two-coin law `Pdiag`.  §5.2's `StrictlyBefore` and
   `StructIndepGiven` are exhibited on concrete DAGs with a matching negative instance
   (`structIndepGiven_collider` against `not_structIndepGiven_nodesVar`), and
   `IsPerfectMapDAG` is inhabited twice over, which discharges the vacuity risk on the
   hypothesis of Proposition 5.8(1): by the edgeless one-node `isPerfectMapDAG_G₁_Q`, and —
   so that neither side of Definition 5.7(1)'s equivalence is idle — by
   `isPerfectMapDAG_G₂_Pedge` on the DAG `0 → 1` carrying a law whose two coordinates are
   genuinely dependent (`not_dSeparated_G₂`, `not_condIndepVar_Pedge`).

2. **Convention regression.** d-separation is the one load-bearing definition that the
   paper does not supply (`dd:dsep`, errata E8); the collider and endpoint conventions
   chosen in `DSeparation.lean` are pinned below by concrete examples on the collider DAG
   `0 → 2 ← 1`, so that a later edit to `Walk.IsColliderAt` or `Walk.Active` that silently
   flips a convention breaks the build.
-/

universe u

namespace FactoredSpaces
namespace Examples

/-! ### The paper's two-coin example (§4)

`I = {0, 1}`, `Ω₀ = Ω₁ = Bool`, and `C` the diagonal event "the two coins agree". -/

/-- The two-factor space of the paper's running example: `I = Fin 2`, `Ω_i = Bool`. -/
abbrev Coins : Fin 2 → Type := fun _ => Bool

/-- The diagonal event `C = {00, 11}`: the two coins agree. -/
def diag : Set (Pt Coins) := {ω | ω 0 = ω 1}

/-- The whole index set disintegrates every event (a trivial positive instance of
Definition 4.5). -/
lemma disintegrates_univ_diag : Disintegrates (Finset.univ : Finset (Fin 2)) diag :=
  disintegrates_univ _

/-- A single coordinate does **not** disintegrate the diagonal: Definition 4.5 is not
vacuously satisfied.  Splicing `00` and `11` along `{0}` gives `01 ∉ C`. -/
lemma not_disintegrates_singleton_diag : ¬ Disintegrates ({0} : Finset (Fin 2)) diag := by
  rw [disintegrates_iff_splice]
  intro h
  have := h (fun _ => false) (by simp [diag]) (fun _ => true) (by simp [diag])
  simp [diag, Finset.piecewise] at this

/-- Definition 4.6 computes to something non-degenerate: the history of the coordinate
variable `U₀` is exactly `{0}`. -/
lemma history_bg_zero : history (bg (Ω := Coins) 0) (Set.univ : Set (Pt Coins)) = {0} := by
  refine Finset.Subset.antisymm (history_bg_subset 0 _ (disintegrates_univ_set _)) ?_
  intro i hi
  rw [Finset.mem_singleton] at hi
  subst hi
  rw [mem_history_iff_exists_ne]
  exact ⟨fun _ => false, fun j => if j = 0 then true else false, fun j hj => by simp [hj],
    by simp [bg]⟩

/-- Definition 4.10 has inhabitants: the two coordinate variables are structurally
independent. -/
lemma structIndep_bg_zero_one : StructIndep (bg (Ω := Coins) 0) (bg (Ω := Coins) 1) := by
  have h1 : history (bg (Ω := Coins) 1) (Set.univ : Set (Pt Coins)) ⊆ {1} :=
    history_bg_subset 1 _ (disintegrates_univ_set _)
  refine Finset.disjoint_left.2 fun a ha hb => ?_
  rw [history_bg_zero, Finset.mem_singleton] at ha
  have := h1 hb
  rw [ha, Finset.mem_singleton] at this
  exact absurd this (by decide)

/-- Definition 4.10 is not vacuously true: a non-constant variable is not structurally
independent of itself. -/
lemma not_structIndep_bg_self : ¬ StructIndep (bg (Ω := Coins) 0) (bg (Ω := Coins) 0) := by
  intro h
  have h0 : (0 : Fin 2) ∈ history (bg (Ω := Coins) 0) (Set.univ : Set (Pt Coins)) := by
    rw [history_bg_zero]; exact Finset.mem_singleton_self 0
  exact (Finset.disjoint_left.1 h h0) h0

/-! ### The trivial one-factor model (remark after Definition 4.4)

Every distribution on a finite observation space has a factored space model, namely the
one-factor space `Ω = Obs` with the identity observation variable. -/

/-- **Every distribution has a factored space model.**  Take `I = Unit`, `Ω_() = Obs` and
`O ω = ω ()`; the model distribution is `P` itself, which factorizes over a one-element
index set.  This is the paper's remark after Definition 4.4, and it witnesses that
`IsFactoredSpaceModel` is inhabited for every `P`. -/
lemma isFactoredSpaceModel_single (Obs : Type u) [Fintype Obs] (P : Distr Obs) :
    IsFactoredSpaceModel (Ω := fun _ : Unit => Obs) (fun ω => ω ()) P := by
  refine ⟨Distr.prod (fun _ => P), factorizes_prod _, fun o => ?_⟩
  have hset : fiber (fun ω : Pt (fun _ : Unit => Obs) => ω ()) o = {fun _ => o} := by
    ext ω
    constructor
    · intro h
      funext i
      cases i
      exact h
    · rintro rfl
      rfl
  rw [hset, Distr.prob_singleton, Distr.prod_mass]
  simp

/-- **A constant observation variable is not a model of a non-degenerate law.**  On the
two-coin space the observation `O ≡ true` has empty fibre over `false`, so no factorizing
`P^Ω` can give `false` the mass `1/2` that the uniform law on `Bool` does.  Together with
`isFactoredSpaceModel_single` this shows Definition 4.4 is neither empty nor trivially
true. -/
lemma not_isFactoredSpaceModel_const :
    ¬ IsFactoredSpaceModel (Ω := Coins) (fun _ => true) (Distr.uniform : Distr Bool) := by
  rintro ⟨PΩ, -, h⟩
  have hf : fiber (fun _ : Pt Coins => true) false = (∅ : Set (Pt Coins)) := by
    ext ω; simp [fiber]
  have h0 := h false
  rw [hf, Distr.prob_empty] at h0
  have hu : (Distr.uniform : Distr Bool).mass false = (2 : ℝ)⁻¹ := by
    show ((Fintype.card Bool : ℝ))⁻¹ = _
    norm_num
  rw [hu] at h0
  norm_num at h0

/-! ### The diagonal law factorizes over nothing

`Pdiag` is the law of the paper's two coins when they are *perfectly correlated*: each of
`00` and `11` has probability `1/2`.  It refutes Definition 4.3 on `Ω = Coins` and eq. (2)
on the edgeless two-node DAG, so neither predicate is trivially true. -/

/-- The **diagonal law** on the two-coin space: the two coins always agree, each of `00`
and `11` carrying probability `1/2`. -/
noncomputable def Pdiag : Distr (Pt Coins) :=
  (Distr.uniform : Distr Bool).map (fun b => (fun _ => b : Pt Coins))

private lemma unif_mass (b : Bool) : (Distr.uniform : Distr Bool).mass b = (2 : ℝ)⁻¹ := by
  show ((Fintype.card Bool : ℝ))⁻¹ = _
  norm_num

private lemma Pdiag_mass (x : Pt Coins) :
    Pdiag.mass x = if x 0 = x 1 then (2 : ℝ)⁻¹ else 0 := by
  rw [Pdiag, Distr.map_mass]
  by_cases h : x 0 = x 1
  · have hset : (fun b => (fun _ => b : Pt Coins)) ⁻¹' {x} = {x 0} := by
      ext c
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hc; exact congrFun hc 0
      · rintro rfl
        funext v
        fin_cases v
        · rfl
        · exact h
    rw [hset, Distr.prob_singleton, unif_mass, if_pos h]
  · have hset : (fun b => (fun _ => b : Pt Coins)) ⁻¹' {x} = (∅ : Set Bool) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hc
      exact h ((congrFun hc 0).symm.trans (congrFun hc 1))
    rw [hset, Distr.prob_empty, if_neg h]

private lemma Pdiag_const (b : Bool) : Pdiag.mass (fun _ => b) = (2 : ℝ)⁻¹ := by
  rw [Pdiag_mass]; exact if_pos rfl

private lemma Pdiag_of_ne {x : Pt Coins} (h : x 0 ≠ x 1) : Pdiag.mass x = 0 := by
  rw [Pdiag_mass]; exact if_neg h

/-- The point `01` of the two-coin space. -/
private def coinFT : Pt Coins := fun i => if i = 0 then false else true

/-- The point `10` of the two-coin space. -/
private def coinTF : Pt Coins := fun i => if i = 0 then true else false

private lemma coinFT_zero : coinFT 0 = false := by simp [coinFT]
private lemma coinFT_one : coinFT 1 = true := by simp [coinFT]
private lemma coinTF_zero : coinTF 0 = true := by simp [coinTF]
private lemma coinTF_one : coinTF 1 = false := by simp [coinTF]

private lemma Pdiag_margAt (i : Fin 2) (b : Bool) : (Pdiag.margAt i).mass b = (2 : ℝ)⁻¹ := by
  show (Pdiag.map (bg i)).mass b = _
  rw [Distr.map_mass, Pdiag, Distr.map_prob]
  have hset : (fun c => (fun _ => c : Pt Coins)) ⁻¹' (bg i ⁻¹' {b}) = {b} := by
    ext c; simp [bg]
  rw [hset, Distr.prob_singleton, unif_mass]

/-- **Definition 4.3 is not trivially true**: the diagonal law does not factorize.  Both
marginals are uniform, so factorization would force `P(01) = 1/4`, but `P(01) = 0`. -/
lemma not_factorizes_diag : ¬ Factorizes Pdiag := by
  intro h
  have hx := h coinFT
  rw [Pdiag_of_ne (by rw [coinFT_zero, coinFT_one]; decide), Fin.prod_univ_two,
    Pdiag_margAt, Pdiag_margAt] at hx
  norm_num at hx

/-- The edgeless DAG on two nodes. -/
def G₀ : Digraph (Fin 2) := ⟨fun _ _ => False⟩

instance : DecidableRel G₀.Adj := fun _ _ => inferInstanceAs (Decidable False)

/-- `G₀` is acyclic. -/
lemma G₀_acyclic : G₀.IsAcyclic := by
  intro v h
  cases h with
  | single h => exact h
  | tail _ h => exact h

private lemma parentConfig_G₀ (v : Fin 2) (x y : Pt Coins) :
    parentConfig G₀ Coins x v = parentConfig G₀ Coins y v := by
  funext i
  exact ((Digraph.mem_parents G₀).mp i.2).elim

/-- **Eq. (2) is not trivially true**: the diagonal law does not factorize over the
edgeless two-node DAG.  With no parents every CPD is a fixed distribution `A`, `B` on
`Bool`, and `A(t)B(t) = A(f)B(f) = 1/2` with `A(t)B(f) = A(f)B(t) = 0` is contradictory. -/
lemma not_factorizesOverDAG_diag : ¬ FactorizesOverDAG G₀ Coins Pdiag := by
  rintro ⟨φ, hφ⟩
  set A : Bool → ℝ := fun b => (φ 0 (parentConfig G₀ Coins (fun _ => true) 0)).mass b with hA
  set B : Bool → ℝ := fun b => (φ 1 (parentConfig G₀ Coins (fun _ => true) 1)).mass b with hB
  have key : ∀ x : Pt Coins, Pdiag.mass x = A (x 0) * B (x 1) := by
    intro x
    rw [hφ x, Fin.prod_univ_two, hA, hB,
      parentConfig_G₀ 0 x (fun _ => true), parentConfig_G₀ 1 x (fun _ => true)]
  have h1 : A true * B true = (2 : ℝ)⁻¹ := by
    have := key (fun _ => true); rw [Pdiag_const] at this; exact this.symm
  have h2 : A false * B false = (2 : ℝ)⁻¹ := by
    have := key (fun _ => false); rw [Pdiag_const] at this; exact this.symm
  have h3 : A false * B true = 0 := by
    have := key coinFT
    rw [Pdiag_of_ne (by rw [coinFT_zero, coinFT_one]; decide), coinFT_zero, coinFT_one] at this
    exact this.symm
  have h4 : A true * B false = 0 := by
    have := key coinTF
    rw [Pdiag_of_ne (by rw [coinTF_zero, coinTF_one]; decide), coinTF_zero, coinTF_one] at this
    exact this.symm
  have hcontr : (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ = 0 :=
    calc (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ = (A true * B true) * (A false * B false) := by rw [h1, h2]
      _ = (A true * B false) * (A false * B true) := by ring
      _ = 0 := by rw [h3, h4]; ring
  norm_num at hcontr

/-! ### d-separation conventions on the collider DAG `0 → 2 ← 1`

`DSeparation.lean` fixes two conventions the paper leaves implicit (`dd:dsep`, errata E8):
a collider is *opened* by conditioning on it (or on a descendant), and the endpoints of a
trail count as non-colliders (so a vertex is never d-separated from itself unless it is in
the conditioning set).  Both are pinned here. -/

/-- The collider DAG `0 → 2 ← 1` on `Fin 3`. -/
def collider : Digraph (Fin 3) := ⟨fun a b => (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2)⟩

instance : DecidableRel collider.Adj :=
  fun a b => inferInstanceAs (Decidable ((a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2)))

private lemma collider_adj_rank {a b : Fin 3} (h : collider.Adj a b) :
    (if a = 2 then 1 else 0) < (if b = 2 then 1 else 0) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private lemma collider_ancestor_rank {a b : Fin 3} (h : collider.IsAncestor a b) :
    (if a = 2 then 1 else 0) < (if b = 2 then 1 else 0) := by
  induction h with
  | single hab => exact collider_adj_rank hab
  | tail _ hbc ih => exact ih.trans (collider_adj_rank hbc)

lemma collider_isAcyclic : collider.IsAcyclic :=
  fun _ h => absurd (collider_ancestor_rank h) (lt_irrefl _)

/-- The trail `0 — 2 — 1` through the collider. -/
def colliderTrail : collider.Trail 0 1 where
  verts := [0, 2, 1]
  chain := by simp [List.isChain_cons, Digraph.Skel, collider]
  head := rfl
  last := rfl
  nodup := by decide

@[simp]
private lemma colliderTrail_verts : colliderTrail.toWalk.verts = [0, 2, 1] := rfl

/- **Positions versus vertices.**  `Walk.IsColliderAt` is indexed by *position along the
trail*, not by vertex name, and `colliderTrail.verts = [0, 2, 1]`: position `0` is vertex
`0`, position `1` is the collider `2`, and position `2` is vertex `1`.  The three pins
below are named for the **vertex** they are about, so their numeral arguments deliberately
differ from the numerals in their names. -/

/-- Vertex `2` (trail position `1`) is a collider on `colliderTrail`. -/
private lemma colliderTrail_isColliderAt_vertex_two : colliderTrail.toWalk.IsColliderAt 1 :=
  ⟨0, 2, 1, rfl, rfl, rfl, by norm_num, by simp [collider], by simp [collider]⟩

/-- Vertex `0` (trail position `0`) is not a collider: it is an endpoint. -/
private lemma colliderTrail_not_isColliderAt_vertex_zero :
    ¬ colliderTrail.toWalk.IsColliderAt 0 := by
  rintro ⟨a, b, c, -, -, -, h, -⟩
  exact absurd h (lt_irrefl 0)

/-- Vertex `1` (trail position `2`) is not a collider: it is the other endpoint. -/
private lemma colliderTrail_not_isColliderAt_vertex_one :
    ¬ colliderTrail.toWalk.IsColliderAt 2 := by
  rintro ⟨a, b, c, -, -, h, -⟩
  simp at h

private lemma colliderTrail_active : colliderTrail.Active ({2} : Finset (Fin 3)) := by
  intro k v hk
  match k with
  | 0 =>
    have hv : v = 0 := by simpa using hk.symm
    subst hv
    exact ⟨fun h => absurd h colliderTrail_not_isColliderAt_vertex_zero, fun _ => by decide⟩
  | 1 =>
    have hv : v = 2 := by simpa using hk.symm
    subst hv
    exact ⟨fun _ => Or.inl (by decide), fun h => absurd colliderTrail_isColliderAt_vertex_two h⟩
  | 2 =>
    have hv : v = 1 := by simpa using hk.symm
    subst hv
    exact ⟨fun h => absurd h colliderTrail_not_isColliderAt_vertex_one, fun _ => by decide⟩
  | (n + 3) => simp at hk

/-- **Collider convention.** Conditioning on a collider *opens* the trail through it, so
the two parents of a collider are not d-separated given the collider. -/
lemma not_dSeparated_given_collider : ¬ collider.DSeparated {0} {1} {2} :=
  fun h => h 0 (by decide) 1 (by decide) colliderTrail colliderTrail_active

/-- The same trail is blocked when nothing is conditioned on: the collider `2` is not in
`Z` and has no descendant in `Z`. -/
lemma not_colliderTrail_active_empty : ¬ colliderTrail.Active (∅ : Finset (Fin 3)) := by
  intro h
  rcases (h 1 2 rfl).1 colliderTrail_isColliderAt_vertex_two with h1 | ⟨z, hz, -⟩
  · simp at h1
  · simp at hz

/-- **The collider blocks when unconditioned.**  With `Z = ∅` the parents of a collider
*are* d-separated — the counterpart of `not_dSeparated_given_collider`. -/
lemma dSeparated_parents_of_collider : collider.DSeparated {0} {1} ∅ := by
  have hpa : collider.parents 0 = ∅ := by decide
  have h := Digraph.dSeparated_singleton_parents (G := collider) collider_isAcyclic 0 {1}
    (by
      intro u hu
      rw [Finset.mem_singleton] at hu
      subst hu
      exact ⟨by decide, fun hanc => absurd (collider_ancestor_rank hanc) (by decide)⟩)
  rwa [hpa] at h

/-- **Endpoint convention** (`Trail.nil_active_iff`), concretely: the zero-edge trail at
`0` is active exactly when `0` is outside the conditioning set, because endpoints count as
non-colliders. -/
lemma nil_active_zero : (Digraph.Trail.nil (G := collider) 0).Active {1} :=
  (Digraph.Trail.nil_active_iff 0 {1}).2 (by decide)

lemma not_nil_active_zero : ¬ (Digraph.Trail.nil (G := collider) 0).Active {0} :=
  fun h => absurd ((Digraph.Trail.nil_active_iff 0 {0}).1 h) (by decide)

/-- Consequently a vertex is never d-separated from itself given a set missing it — the
step the paper's own proof of Proposition 5.8 relies on. -/
lemma not_dSeparated_self_zero : ¬ collider.DSeparated {0} {0} ∅ :=
  Digraph.not_dSeparated_self (Finset.mem_singleton_self 0) (Finset.mem_singleton_self 0)
    (Finset.notMem_empty 0)

/-- **Adjacent vertices are never d-separated** by a conditioning set avoiding them: the
one-edge trail `0 — 2` has no collider, and neither of its two vertices is in `Z`
(`Digraph.not_dSeparated_of_skel`). -/
lemma not_dSeparated_adj : ¬ collider.DSeparated {0} {2} {1} :=
  Digraph.not_dSeparated_of_skel (V₁ := {0}) (V₂ := {2}) (V₃ := {1}) (s := 0) (t := 2)
    (by decide) (by decide) (by decide) (Or.inl (Or.inl ⟨rfl, rfl⟩)) (by decide) (by decide)

/-- **Endpoint convention, discriminating pin.**  The same one-edge trail `0 — 2` of
`not_dSeparated_adj`, but conditioning on its *endpoint* `2`: here `0` and `2` **are**
d-separated given `{2}`, because endpoints count as non-collider trail vertices and so
block when they lie in the conditioning set (`dd:dsep`).  Under the alternative convention
— only interior vertices are tested — the trail `0 — 2` would stay active and this would be
false.  Together with `not_dSeparated_self_zero` this pins the convention from both sides;
flipping it in `DSeparation.lean` breaks one of the two. -/
lemma dSeparated_given_endpoint : collider.DSeparated {0} {2} {2} := by
  rw [Digraph.dSeparated_iff_disjoint_zClosureSet collider_isAcyclic, Set.disjoint_right]
  intro a ha _
  obtain ⟨t, ht, htZ, -⟩ := Digraph.exists_of_mem_zClosureSet ha
  exact htZ ht

/-! ### Propositions 5.5 and 5.6 have content on `collider`

The edge `0 → 2` of `collider` produces a genuine strict "before" and a genuine
structural *dependence* in the constructed factored space model `M^{collider}`.
-/

/-- Two-element value space at each node of `collider`; supplies `Nontrivial`, the standing
assumption of Propositions 5.5 and 5.6. -/
abbrev ColliderVal : Fin 3 → Type := fun _ => Bool

/-- Definition 4.10's conditional form is inhabited on a concrete DAG: with nothing
conditioned on, the two parents `0` and `1` of the collider `2` are structurally
independent in `M^{collider}` (Proposition 5.5 applied to
`dSeparated_parents_of_collider`).  Together with `not_structIndepGiven_nodesVar` this
shows `StructIndepGiven` is neither empty nor trivially true. -/
lemma structIndepGiven_collider :
    StructIndepGiven (nodesVar (Val := ColliderVal) collider_isAcyclic {0})
      (nodesVar collider_isAcyclic {1}) (nodesVar collider_isAcyclic ∅) :=
  (dSeparated_iff_structIndepGiven (Val := ColliderVal) collider_isAcyclic {0} {1} ∅).mp
    dSeparated_parents_of_collider

/-- Proposition 5.5 has content: the node variables at the adjacent nodes `0` and `2` are
structurally *dependent* given `X_1`, so the iff is not vacuously "always independent". -/
lemma not_structIndepGiven_nodesVar :
    ¬ StructIndepGiven (nodesVar (Val := ColliderVal) collider_isAcyclic {0})
      (nodesVar collider_isAcyclic {2}) (nodesVar collider_isAcyclic {1}) := fun h =>
  not_dSeparated_adj
    ((dSeparated_iff_structIndepGiven (Val := ColliderVal) collider_isAcyclic {0} {2} {1}).mpr h)

/-- Proposition 5.6 has content: the edge `0 → 2` gives a genuine strict
`<_{Ω^collider}` between the two node variables. -/
lemma strictlyBefore_nodeVar :
    StrictlyBefore (nodeVar (Val := ColliderVal) collider_isAcyclic 0)
      (nodeVar collider_isAcyclic 2) :=
  (isAncestor_iff_strictlyBefore (Val := ColliderVal) collider_isAcyclic (by decide)).mp
    (Relation.TransGen.single (Or.inl ⟨rfl, rfl⟩))

/-! ### A DAG that is a perfect map

`G₁` is the edgeless DAG on one node with a uniform distribution on `Bool`.  It inhabits
Definition 5.7's `IsPerfectMapDAG`, and hence the hypothesis of Proposition 5.8(1), whose
conclusion then produces an actual `IsPerfectMapFSM`.
-/

/-- The one-node edgeless DAG. -/
def G₁ : Digraph Unit := ⟨fun _ _ => False⟩

instance : DecidableRel G₁.Adj := fun _ _ => inferInstanceAs (Decidable False)

/-- The value space of `G₁`: `Bool` at its single node. -/
abbrev UVal : Unit → Type := fun _ => Bool

/-- `G₁` is acyclic. -/
lemma G₁_acyclic : G₁.IsAcyclic := by
  intro v h
  induction h with
  | single h => exact h
  | tail _ h _ => exact h

/-- The uniform distribution on the observation space of `G₁`. -/
noncomputable def Q : Distr (Pt UVal) := Distr.uniform

private lemma Q_pos (c : Pt UVal) : 0 < Q.mass c := Distr.uniform_strictlyPositive c

/-- A `Finset Unit` is empty or everything. -/
private lemma unit_finset_cases (S : Finset Unit) : S = ∅ ∨ S = Finset.univ := by
  rcases S.eq_empty_or_nonempty with h | ⟨u, hu⟩
  · exact Or.inl h
  · exact Or.inr (Finset.eq_univ_iff_forall.mpr fun x => by rw [Subsingleton.elim x u]; exact hu)

/-- The empty subfamily has a single fiber, all of `Ω`. -/
private lemma fiber_proj_empty (x : PtOn UVal (∅ : Finset Unit)) :
    fiber (proj (∅ : Finset Unit)) x = Set.univ := by
  ext ω
  simp only [Set.mem_univ, iff_true]
  show proj (∅ : Finset Unit) ω = x
  funext i
  exact absurd i.2 (Finset.notMem_empty _)

/-- The full subfamily has singleton fibers. -/
private lemma fiber_proj_univ (c : Pt UVal) :
    fiber (proj (Finset.univ : Finset Unit)) (proj Finset.univ c) = {c} := by
  ext ω
  constructor
  · intro h
    exact funext fun i => congrFun h ⟨i, Finset.mem_univ i⟩
  · rintro rfl
    rfl

private lemma prob_inter_singleton_mem {A : Set (Pt UVal)} (c : Pt UVal) (h : c ∈ A) :
    Q.prob (A ∩ {c}) = Q.mass c := by
  rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr h), Distr.prob_singleton]

private lemma prob_inter_singleton_not {A : Set (Pt UVal)} (c : Pt UVal) (h : c ∉ A) :
    Q.prob (A ∩ {c}) = 0 := by
  rw [Set.inter_singleton_eq_empty.mpr h, Distr.prob_empty]

/-- Conditioning on a single point makes every pair of events independent. -/
private lemma condIndep_singleton (A B : Set (Pt UVal)) (c : Pt UVal) : CondIndep Q A B {c} := by
  show Q.prob (A ∩ {c}) * Q.prob (B ∩ {c}) = Q.prob (A ∩ B ∩ {c}) * Q.prob {c}
  rw [Distr.prob_singleton]
  by_cases hA : c ∈ A
  · by_cases hB : c ∈ B
    · rw [prob_inter_singleton_mem c hA, prob_inter_singleton_mem c hB,
        prob_inter_singleton_mem c (Set.mem_inter hA hB)]
    · rw [prob_inter_singleton_mem c hA, prob_inter_singleton_not c hB,
        prob_inter_singleton_not c (fun h => hB (Set.mem_of_mem_inter_right h))]
      ring
  · rw [prob_inter_singleton_not c hA,
      prob_inter_singleton_not c (fun h => hA (Set.mem_of_mem_inter_left h))]
    ring

private lemma condIndep_univ_left (B C : Set (Pt UVal)) : CondIndep Q Set.univ B C := by
  show Q.prob (Set.univ ∩ C) * Q.prob (B ∩ C) = Q.prob (Set.univ ∩ B ∩ C) * Q.prob C
  rw [Set.univ_inter, Set.univ_inter]
  ring

private lemma condIndep_univ_right (A C : Set (Pt UVal)) : CondIndep Q A Set.univ C :=
  (condIndep_univ_left A C).symm

/-- In `G₁` a trail is blocked as soon as its source lies in the conditioning set (the
general `Digraph.dSeparated_of_subset_left`, specialized). -/
private lemma dSeparated_of_mem (V₁ V₂ V₃ : Finset Unit) (h : ∀ s ∈ V₁, s ∈ V₃) :
    G₁.DSeparated V₁ V₂ V₃ :=
  Digraph.dSeparated_of_subset_left h

/-- Definition 5.7 is inhabited: the edgeless one-node DAG is a perfect map of the uniform
distribution.  This is the hypothesis of Proposition 5.8(1). -/
lemma isPerfectMapDAG_G₁_Q : IsPerfectMapDAG G₁ Q := by
  intro V₁ V₂ V₃
  rcases unit_finset_cases V₃ with h3 | h3
  · subst h3
    rcases unit_finset_cases V₁ with h1 | h1
    · subst h1
      constructor
      · intro _ x y z
        -- Definition 6.1's events are set-builders (it is stated over an arbitrary sample
        -- space); `fiber` is the same set, so the ascription is definitional.
        show CondIndep Q (fiber (proj ∅) x) (fiber (proj V₂) y) (fiber (proj ∅) z)
        rw [fiber_proj_empty x]
        exact condIndep_univ_left _ _
      · intro _
        exact dSeparated_of_mem _ _ _ (fun s hs => absurd hs (Finset.notMem_empty s))
    · rcases unit_finset_cases V₂ with h2 | h2
      · subst h1; subst h2
        constructor
        · intro _ x y z
          show CondIndep Q (fiber (proj Finset.univ) x) (fiber (proj ∅) y) (fiber (proj ∅) z)
          rw [fiber_proj_empty y]
          exact condIndep_univ_right _ _
        · intro _ s hs t ht
          exact absurd ht (Finset.notMem_empty t)
      · subst h1; subst h2
        constructor
        · intro hd
          exact absurd hd (Digraph.not_dSeparated_self (V₁ := Finset.univ) (V₂ := Finset.univ)
            (V₃ := ∅) (v := ()) (Finset.mem_univ _) (Finset.mem_univ _) (Finset.notMem_empty _))
        · intro hci
          exfalso
          have hcf : ({(fun _ : Unit => false)} ∩ {(fun _ : Unit => true)} : Set (Pt UVal)) = ∅ := by
            rw [Set.singleton_inter_eq_empty]
            intro h
            exact Bool.false_ne_true (congrFun (Set.mem_singleton_iff.mp h) ())
          have h : CondIndep Q (fiber (proj Finset.univ) (proj Finset.univ (fun _ : Unit => false)))
              (fiber (proj Finset.univ) (proj Finset.univ (fun _ : Unit => true)))
              (fiber (proj (∅ : Finset Unit)) (proj (∅ : Finset Unit) (fun _ : Unit => false))) :=
            hci (proj Finset.univ (fun _ : Unit => false))
              (proj Finset.univ (fun _ : Unit => true))
              (proj (∅ : Finset Unit) (fun _ : Unit => false))
          rw [fiber_proj_univ, fiber_proj_univ, fiber_proj_empty] at h
          have h' : Q.prob ({(fun _ : Unit => false)} ∩ Set.univ) *
              Q.prob ({(fun _ : Unit => true)} ∩ Set.univ)
              = Q.prob (({(fun _ : Unit => false)} ∩ {(fun _ : Unit => true)}) ∩ Set.univ)
                * Q.prob Set.univ := h
          rw [Set.inter_univ, Set.inter_univ, Set.inter_univ, Distr.prob_singleton,
            Distr.prob_singleton, hcf, Distr.prob_empty, zero_mul] at h'
          exact (mul_pos (Q_pos _) (Q_pos _)).ne' h'
  · subst h3
    constructor
    · intro _ x y z
      obtain ⟨c, hc⟩ : ∃ c : Pt UVal, z = proj Finset.univ c :=
        ⟨fun i => z ⟨i, Finset.mem_univ i⟩, rfl⟩
      subst hc
      show CondIndep Q (fiber (proj V₁) x) (fiber (proj V₂) y)
        (fiber (proj Finset.univ) (proj Finset.univ c))
      rw [fiber_proj_univ]
      exact condIndep_singleton _ _ _
    · intro _
      exact dSeparated_of_mem _ _ _ (fun s _ => Finset.mem_univ s)

/-- Proposition 5.8(1) is not vacuous: its hypothesis is satisfied by `G₁`, so its
conclusion produces an actual factored space model that is a perfect map of `Q`. -/
example : ∃ (I : Type) (Ω : I → Type) (_ : Fintype I) (_ : DecidableEq I)
    (_ : ∀ i, Fintype (Ω i)) (X : ∀ v, Pt Ω → UVal v), IsPerfectMapFSM X Q :=
  exists_isPerfectMapFSM_of_exists_isPerfectMapDAG (V := Unit) (Val := UVal) (P := Q)
    ⟨G₁, G₁_acyclic, isPerfectMapDAG_G₁_Q⟩

/-! ### A perfect map with an edge

`G₁` above is edgeless, so its perfect-map property says nothing about the d-separation
side of Definition 5.7(1).  `G₂` is the two-node DAG `0 → 1` and `Pedge` makes its two
coordinates agree with probability `3/4`; `isPerfectMapDAG_G₂_Pedge` is therefore an
inhabitant of Definition 5.7(1) in which both sides of the equivalence have content
(`not_dSeparated_G₂` and `not_condIndepVar_Pedge` are the two negative instances).
-/

/-- The two-node DAG with a single edge `0 → 1`. -/
def G₂ : Digraph (Fin 2) := ⟨fun u v => u = 0 ∧ v = 1⟩

instance G₂_decidableAdj : DecidableRel G₂.Adj :=
  fun u v => inferInstanceAs (Decidable (u = 0 ∧ v = 1))

/-- `G₂` really has an edge — the point of this witness. -/
lemma G₂_adj_zero_one : G₂.Adj 0 1 := ⟨rfl, rfl⟩

private lemma G₂_adj_rank {a b : Fin 2} (h : G₂.Adj a b) :
    (if a = 1 then 1 else 0) < (if b = 1 then 1 else 0) := by
  obtain ⟨rfl, rfl⟩ := h
  decide

private lemma G₂_ancestor_rank {a b : Fin 2} (h : G₂.IsAncestor a b) :
    (if a = 1 then 1 else 0) < (if b = 1 then 1 else 0) := by
  induction h with
  | single hab => exact G₂_adj_rank hab
  | tail _ hbc ih => exact ih.trans (G₂_adj_rank hbc)

/-- `G₂` is acyclic. -/
lemma G₂_acyclic : G₂.IsAcyclic :=
  fun _ h => absurd (G₂_ancestor_rank h) (lt_irrefl _)

/-- Distinct nodes of `G₂` are always skeleton-adjacent. -/
private lemma G₂_skel {s t : Fin 2} (h : s ≠ t) : G₂.Skel s t := by
  have key : ∀ s t : Fin 2, s ≠ t → ((s = 0 ∧ t = 1) ∨ (t = 0 ∧ s = 1)) := by decide
  exact key s t h

private lemma fin2_eq_or {s t : Fin 2} (h : s ≠ t) (a : Fin 2) : a = s ∨ a = t := by
  revert h
  revert s t a
  decide

private lemma fin2_pair {s t : Fin 2} (h : s ≠ t) : (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  have key : ∀ a b : Fin 2, a ≠ b → ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) := by decide
  exact key s t h

private def coinEquiv : Pt Coins ≃ (Bool × Bool) where
  toFun x := (x 0, x 1)
  invFun p := ![p.1, p.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

private lemma sum_pt (f : Pt Coins → ℝ) :
    ∑ x : Pt Coins, f x
      = f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [← Equiv.sum_comp coinEquiv.symm f, Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  rw [Fintype.sum_bool, Fintype.sum_bool]
  show f ![true, true] + f ![true, false] + (f ![false, true] + f ![false, false]) = _
  ring

/-- `X₁ = X₀` with probability `3/4`: a strictly positive law on the two coins with uniform
marginals whose coordinates are dependent. -/
noncomputable def Pedge : Distr (Pt Coins) where
  mass x := if x 0 = x 1 then 3 / 8 else 1 / 8
  nonneg x := by split_ifs <;> norm_num
  sum_eq_one := by rw [sum_pt]; norm_num

private lemma Pedge_mass (x : Pt Coins) :
    Pedge.mass x = if x 0 = x 1 then 3 / 8 else 1 / 8 := rfl

private lemma Pedge_pos : Pedge.StrictlyPositive := by
  intro x
  rw [Pedge_mass]
  split_ifs <;> norm_num

private lemma Pedge_prob (A : Set (Pt Coins)) :
    Pedge.prob A = A.indicator Pedge.mass ![false, false]
      + A.indicator Pedge.mass ![false, true]
      + A.indicator Pedge.mass ![true, false]
      + A.indicator Pedge.mass ![true, true] :=
  sum_pt _

private lemma fiber_proj_singleton (i : Fin 2) (ω₀ : Pt Coins) :
    fiber (proj ({i} : Finset (Fin 2))) (proj {i} ω₀) = {ω : Pt Coins | ω i = ω₀ i} := by
  ext ω
  constructor
  · intro h
    exact congrFun (show proj ({i} : Finset (Fin 2)) ω = proj {i} ω₀ from h)
      ⟨i, Finset.mem_singleton_self i⟩
  · intro h
    show proj ({i} : Finset (Fin 2)) ω = proj {i} ω₀
    exact proj_eq_iff.mpr fun j hj => by
      rw [Finset.mem_singleton] at hj; exact hj ▸ h

private lemma fiber_proj_empty_coins (z : PtOn Coins (∅ : Finset (Fin 2))) :
    fiber (proj (∅ : Finset (Fin 2))) z = Set.univ := by
  ext ω
  simp only [Set.mem_univ, iff_true]
  show proj (∅ : Finset (Fin 2)) ω = z
  funext i
  exact absurd i.2 (Finset.notMem_empty _)

/-- **The two coins of `Pedge` are dependent.**  `P(X₀ = 1)·P(X₁ = 1) = 1/4 ≠ 3/8 =
P(X₀ = X₁ = 1)`, so the conditional-independence side of `isPerfectMapDAG_G₂_Pedge` is not
vacuously true. -/
lemma not_condIndepVar_Pedge :
    ¬ CondIndepVar Pedge (proj ({0} : Finset (Fin 2))) (proj ({1} : Finset (Fin 2)))
        (proj (∅ : Finset (Fin 2))) := by
  intro h
  have key : CondIndep Pedge (fiber (proj {0}) (proj {0} (![true, true] : Pt Coins)))
      (fiber (proj {1}) (proj {1} (![true, true] : Pt Coins)))
      (fiber (proj (∅ : Finset (Fin 2))) (proj (∅ : Finset (Fin 2)) (![true, true] : Pt Coins))) :=
    h _ _ _
  rw [fiber_proj_singleton, fiber_proj_singleton, fiber_proj_empty_coins] at key
  have key' : Pedge.prob ({ω : Pt Coins | ω 0 = (![true, true] : Pt Coins) 0} ∩ Set.univ)
      * Pedge.prob ({ω : Pt Coins | ω 1 = (![true, true] : Pt Coins) 1} ∩ Set.univ)
      = Pedge.prob (({ω : Pt Coins | ω 0 = (![true, true] : Pt Coins) 0}
          ∩ {ω : Pt Coins | ω 1 = (![true, true] : Pt Coins) 1}) ∩ Set.univ)
        * Pedge.prob (Set.univ : Set (Pt Coins)) := key
  rw [Set.inter_univ, Set.inter_univ, Set.inter_univ, Pedge_prob, Pedge_prob, Pedge_prob,
    Pedge_prob] at key'
  norm_num [Set.indicator_apply, Pedge_mass] at key'

/-- On `G₂` both sides of Definition 5.7(1) collapse to `V₁ ⊆ V₃ ∨ V₂ ⊆ V₃`: the graph
side.  `G₂` has no collider, so a trail is active given `V₃` exactly when neither of its
vertices lies in `V₃`. -/
private lemma dSeparated_G₂_iff (V₁ V₂ V₃ : Finset (Fin 2)) :
    G₂.DSeparated V₁ V₂ V₃ ↔ V₁ ⊆ V₃ ∨ V₂ ⊆ V₃ := by
  constructor
  · intro hd
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs, hs3⟩ := Finset.not_subset.mp hcon.1
    obtain ⟨t, ht, ht3⟩ := Finset.not_subset.mp hcon.2
    by_cases hst : s = t
    · subst hst
      exact Digraph.not_dSeparated_self hs ht hs3 hd
    · exact Digraph.not_dSeparated_of_skel hs ht hst (G₂_skel hst) hs3 ht3 hd
  · rintro (h | h)
    · exact Digraph.dSeparated_of_subset_left h
    · exact Digraph.dSeparated_of_subset_right h

/-- The probability side of the same collapse: `Pedge` is strictly positive with dependent
coordinates, so a conditional independence among the coordinate projections holds exactly
when one side is already determined by the conditioning family. -/
private lemma condIndepVar_Pedge_iff (V₁ V₂ V₃ : Finset (Fin 2)) :
    CondIndepVar Pedge (proj V₁) (proj V₂) (proj V₃) ↔ V₁ ⊆ V₃ ∨ V₂ ⊆ V₃ := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs, hs3⟩ := Finset.not_subset.mp hcon.1
    obtain ⟨t, ht, ht3⟩ := Finset.not_subset.mp hcon.2
    have hst : CondIndepVar Pedge (proj ({s} : Finset (Fin 2)))
        (proj ({t} : Finset (Fin 2))) (proj V₃) :=
      CondIndepVar.of_proj_subset (Finset.singleton_subset_iff.mpr hs)
        (Finset.singleton_subset_iff.mpr ht) h
    by_cases hsteq : s = t
    · subst hsteq
      haveI : Nontrivial (Coins s) := inferInstanceAs (Nontrivial Bool)
      exact not_condIndepVar_proj_self Pedge_pos hs3 hst
    · have hV₃ : V₃ = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro a ha
        rcases fin2_eq_or hsteq a with rfl | rfl
        · exact hs3 ha
        · exact ht3 ha
      subst hV₃
      rcases fin2_pair hsteq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact not_condIndepVar_Pedge hst
      · exact not_condIndepVar_Pedge hst.symm
  · rintro (h | h)
    · exact condIndepVar_proj_of_subset_left h _
    · exact condIndepVar_proj_of_subset_right h _

/-- **Definition 5.7(1) is inhabited by a DAG with an edge.**  `G₂ = (0 → 1)` is a perfect
map of `Pedge`, whose two coordinates are genuinely dependent.  Unlike
`isPerfectMapDAG_G₁_Q` — where the graph is edgeless and the law a product — the
equivalence here has content on both sides: see `not_dSeparated_G₂` and
`not_condIndepVar_Pedge`. -/
lemma isPerfectMapDAG_G₂_Pedge : IsPerfectMapDAG G₂ Pedge := fun V₁ V₂ V₃ =>
  (dSeparated_G₂_iff V₁ V₂ V₃).trans (condIndepVar_Pedge_iff V₁ V₂ V₃).symm

/-- The equivalence of `isPerfectMapDAG_G₂_Pedge` is not vacuously "everything is
d-separated": the two endpoints of the edge are not d-separated given nothing. -/
lemma not_dSeparated_G₂ : ¬ G₂.DSeparated {0} {1} ∅ := by
  rw [dSeparated_G₂_iff]
  simp

/-- …nor vacuously "nothing is d-separated": conditioning on an endpoint separates. -/
lemma dSeparated_G₂_given_endpoint : G₂.DSeparated {0} {1} {0} := by
  rw [dSeparated_G₂_iff]
  simp

/-- Proposition 5.8(1) applied to a DAG with an edge: the factored space model it produces
is a perfect map of `Pedge`. -/
example : ∃ (I : Type) (Ω : I → Type) (_ : Fintype I) (_ : DecidableEq I)
    (_ : ∀ i, Fintype (Ω i)) (X : ∀ v, Pt Ω → Coins v), IsPerfectMapFSM X Pedge :=
  exists_isPerfectMapFSM_of_exists_isPerfectMapDAG (V := Fin 2) (Val := Coins) (P := Pedge)
    ⟨G₂, G₂_acyclic, isPerfectMapDAG_G₂_Pedge⟩

end Examples
end FactoredSpaces
