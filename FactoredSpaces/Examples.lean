import FactoredSpaces.PerfectMap

/-!
# Worked examples: non-vacuity witnesses and convention regression tests

Nothing here is a paper node.  The file exists for two reasons.

1. **Non-vacuity.** The library's §4 and §5.2 vocabulary is otherwise never instantiated,
   so a reader cannot tell from the artifact alone that `Disintegrates`, `history`,
   `StructIndep`, `IsFactoredSpaceModel` and `Digraph.DSeparated` have inhabitants and
   non-inhabitants — i.e. that the definitions are neither empty nor trivially true.
   The paper's two-coin example and its "every distribution has a one-factor model"
   remark are checked here against the Lean definitions, and §5.2's `IsPerfectMapDAG`,
   `StrictlyBefore` and `StructIndepGiven` are exhibited on concrete DAGs, each with a
   matching negative instance (`structIndepGiven_collider` against
   `not_structIndepGiven_nodesVar`) — including a DAG that *is* a perfect map, which
   discharges the vacuity risk on the hypothesis of Proposition 5.8(1).

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

private lemma colliderTrail_isColliderAt_one : colliderTrail.toWalk.IsColliderAt 1 :=
  ⟨0, 2, 1, rfl, rfl, rfl, by norm_num, by simp [collider], by simp [collider]⟩

private lemma colliderTrail_not_isColliderAt_zero :
    ¬ colliderTrail.toWalk.IsColliderAt 0 := by
  rintro ⟨a, b, c, -, -, -, h, -⟩
  exact absurd h (lt_irrefl 0)

private lemma colliderTrail_not_isColliderAt_two :
    ¬ colliderTrail.toWalk.IsColliderAt 2 := by
  rintro ⟨a, b, c, -, -, h, -⟩
  simp at h

private lemma colliderTrail_active : colliderTrail.Active ({2} : Finset (Fin 3)) := by
  intro k v hk
  match k with
  | 0 =>
    have hv : v = 0 := by simpa using hk.symm
    subst hv
    exact ⟨fun h => absurd h colliderTrail_not_isColliderAt_zero, fun _ => by decide⟩
  | 1 =>
    have hv : v = 2 := by simpa using hk.symm
    subst hv
    exact ⟨fun _ => Or.inl (by decide), fun h => absurd colliderTrail_isColliderAt_one h⟩
  | 2 =>
    have hv : v = 1 := by simpa using hk.symm
    subst hv
    exact ⟨fun h => absurd h colliderTrail_not_isColliderAt_two, fun _ => by decide⟩
  | (n + 3) => simp at hk

/-- **Collider convention.** Conditioning on a collider *opens* the trail through it, so
the two parents of a collider are not d-separated given the collider. -/
lemma not_dSeparated_given_collider : ¬ collider.DSeparated {0} {1} {2} :=
  fun h => h 0 (by decide) 1 (by decide) colliderTrail colliderTrail_active

/-- The same trail is blocked when nothing is conditioned on: the collider `2` is not in
`Z` and has no descendant in `Z`. -/
lemma not_colliderTrail_active_empty : ¬ colliderTrail.Active (∅ : Finset (Fin 3)) := by
  intro h
  rcases (h 1 2 rfl).1 colliderTrail_isColliderAt_one with h1 | ⟨z, hz, -⟩
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

/-- The one-edge trail `0 — 2`. -/
def edgeTrail : collider.Trail 0 2 where
  verts := [0, 2]
  chain := by simp [List.isChain_cons, Digraph.Skel, collider]
  head := rfl
  last := rfl
  nodup := by decide

@[simp]
private lemma edgeTrail_verts : edgeTrail.toWalk.verts = [0, 2] := rfl

/-- **Adjacent vertices are never d-separated** by a conditioning set avoiding them: the
one-edge trail has no collider and no non-collider in `Z`. -/
lemma not_dSeparated_adj : ¬ collider.DSeparated {0} {2} {1} := by
  refine fun h => h 0 (by decide) 2 (by decide) edgeTrail ?_
  have hnc : ∀ j, ¬ edgeTrail.toWalk.IsColliderAt j := by
    rintro (_ | _ | j) ⟨a, b, c, -, -, h3, hj, -⟩
    · exact absurd hj (lt_irrefl 0)
    · simp at h3
    · simp at h3
  intro k v hv
  refine ⟨fun hc => absurd hc (hnc k), fun _ => ?_⟩
  match k with
  | 0 =>
    have : v = 0 := by simpa using hv.symm
    subst this
    decide
  | 1 =>
    have : v = 2 := by simpa using hv.symm
    subst this
    decide
  | (n + 2) => simp at hv

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

/-- In `G₁` a trail is blocked as soon as its source lies in the conditioning set. -/
private lemma dSeparated_of_mem (V₁ V₂ V₃ : Finset Unit) (h : ∀ s ∈ V₁, s ∈ V₃) :
    G₁.DSeparated V₁ V₂ V₃ := by
  intro s hs t ht p hact
  have hhead := p.head
  have h0 : p.toWalk.verts[0]? = some s := by
    show p.verts[0]? = some s
    cases hv : p.verts with
    | nil => rw [hv] at hhead; simp at hhead
    | cons a l => rw [hv] at hhead; exact List.getElem?_cons_zero.trans hhead
  have hnc : ¬ p.toWalk.IsColliderAt 0 := by
    rintro ⟨a, b, c, -, -, -, hk, -, -⟩
    exact absurd hk (lt_irrefl 0)
  exact (hact 0 s h0).2 hnc (h s hs)

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

end Examples
end FactoredSpaces
