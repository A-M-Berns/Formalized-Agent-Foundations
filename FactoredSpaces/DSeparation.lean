import FactoredSpaces.BayesNet
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

/-!
# d-separation (§5.2, `dd:dsep`)

The paper uses d-separation (Koller–Friedman) without defining it.  A *trail* between
`s` and `t` in `G` is a sequence of distinct vertices, consecutive ones joined by an edge
in either direction; a vertex of the trail is a *collider* if both incident trail edges
point into it (`v_{k-1} → v_k ← v_{k+1}`), otherwise a *non-collider* — the endpoints, having
at most one incident trail edge, are non-colliders.  A trail is *active* given `Z` if every
collider on it is in `Z` or has a descendant in `Z`, and no non-collider is in `Z`; `V₁`
and `V₂` are *d-separated* given `V₃` if no trail from a member of `V₁` to a member of
`V₂` is active given `V₃`.

The endpoint convention matters and is fixed here (`dd:dsep`): endpoints count as
non-collider trail vertices, so the zero-edge trail `v — v` is blocked iff `v ∈ Z`, and
`V₁ ∩ V₂ ⊄ V₃` is never d-separated.  This is the reading the paper's own proof of
Proposition 5.8 uses ("the path from `v₂` to itself has zero edges and can only be blocked
by itself"), and the only reading under which Proposition 5.5 holds for arbitrary
`V₁, V₂, V₃`: under the alternative convention — only interior trail vertices are tested —
a vertex would be d-separated from itself given a set missing it, while `X_v` is never
structurally independent of itself (see `notes/paper-errata.md`, E8).

Both conventions are pinned by regression examples in `FactoredSpaces/Examples.lean`, over
the collider `0 → 2 ← 1`: conditioning on the collider opens the trail, conditioning on
nothing blocks it, and a vertex is never d-separated from itself given a set missing it.
Flipping either convention here breaks that file.
-/

universe u

namespace Digraph

variable {V : Type u} (G : Digraph V)

/-- The skeleton: `u — v` iff `u → v` or `v → u`. -/
def Skel (u v : V) : Prop := G.Adj u v ∨ G.Adj v u

/-- A trail from `s` to `t`: distinct vertices `v₀ = s, …, v_n = t`, consecutive ones
adjacent in the skeleton.  (Zero-edge trails `[s]` are trails from `s` to `s`.) -/
structure Trail (s t : V) where
  verts : List V
  chain : verts.IsChain G.Skel
  head : verts.head? = some s
  last : verts.getLast? = some t
  nodup : verts.Nodup

/-- A walk: the same without distinctness (used only in proofs; d-separation is defined
through trails). -/
structure Walk (s t : V) where
  verts : List V
  chain : verts.IsChain G.Skel
  head : verts.head? = some s
  last : verts.getLast? = some t

variable {G}

/-- The trail vertex at position `k` is a collider: `v_{k-1} → v_k ← v_{k+1}`. -/
def Walk.IsColliderAt {s t : V} (p : G.Walk s t) (k : ℕ) : Prop :=
  ∃ a b c, p.verts[k - 1]? = some a ∧ p.verts[k]? = some b ∧ p.verts[k + 1]? = some c ∧
    0 < k ∧ G.Adj a b ∧ G.Adj c b

/-- A walk is active given `Z`: every collider is in `Z` or has a descendant in `Z`, and no
non-collider (endpoints included) is in `Z`. -/
def Walk.Active {s t : V} (p : G.Walk s t) (Z : Finset V) : Prop :=
  ∀ k v, p.verts[k]? = some v →
    (p.IsColliderAt k → v ∈ Z ∨ ∃ z ∈ Z, G.IsAncestor v z) ∧ (¬ p.IsColliderAt k → v ∉ Z)

variable (G) in
/-- The condition `Walk.Active` imposes at a collider, named: `v` is in `Z` or has a
descendant in `Z`.  (Definitionally the disjunct above; the graph-theoretic development of
`ConditionalHistory.lean` and `ActiveTrails.lean` reasons about it as a predicate.) -/
def ColliderOK (Z : Finset V) (v : V) : Prop :=
  v ∈ Z ∨ ∃ z ∈ Z, G.IsAncestor v z

/-- Every trail is a walk. -/
def Trail.toWalk {s t : V} (p : G.Trail s t) : G.Walk s t := ⟨p.verts, p.chain, p.head, p.last⟩

/-- A trail is active given `Z` if it is active as a walk. -/
def Trail.Active {s t : V} (p : G.Trail s t) (Z : Finset V) : Prop := p.toWalk.Active Z

variable (G) in
/-- **d-separation.** `V₁` and `V₂` are d-separated given `V₃` in `G` if no trail from a
vertex of `V₁` to a vertex of `V₂` is active given `V₃` (`dd:dsep`). -/
def DSeparated (V₁ V₂ V₃ : Finset V) : Prop :=
  ∀ s ∈ V₁, ∀ t ∈ V₂, ∀ p : G.Trail s t, ¬ p.Active V₃

/-- The zero-edge trail at `s`. -/
def Trail.nil (s : V) : G.Trail s s := ⟨[s], List.isChain_singleton s, rfl, rfl, List.nodup_singleton s⟩

/-- The zero-edge trail is active given `Z` iff `s ∉ Z` (endpoints are non-colliders). -/
lemma Trail.nil_active_iff (s : V) (Z : Finset V) : (Trail.nil (G := G) s).Active Z ↔ s ∉ Z := by
  have hnc : ∀ k, ¬ (Trail.nil (G := G) s).toWalk.IsColliderAt k := by
    rintro k ⟨a, b, c, -, -, hc, -⟩
    simp [Trail.nil, Trail.toWalk] at hc
  constructor
  · intro h
    exact (h 0 s rfl).2 (hnc 0)
  · intro hs k v hv
    refine ⟨fun hcol => absurd hcol (hnc k), fun _ => ?_⟩
    rcases k with _ | k
    · simp only [Trail.nil, Trail.toWalk, List.getElem?_cons_zero, Option.some.injEq] at hv
      exact hv ▸ hs
    · simp [Trail.nil, Trail.toWalk] at hv

/-- A vertex is never d-separated from itself given a set not containing it. -/
lemma not_dSeparated_self {V₁ V₂ V₃ : Finset V} {v : V} (h₁ : v ∈ V₁) (h₂ : v ∈ V₂)
    (h₃ : v ∉ V₃) : ¬ G.DSeparated V₁ V₂ V₃ := fun h =>
  h v h₁ v h₂ (Trail.nil v) ((Trail.nil_active_iff v V₃).2 h₃)

/-- **Conditioning on all of `V₁` d-separates it from everything.**  A trail out of
`s ∈ V₁` has `s` at position `0`, an endpoint and hence a non-collider, so `s ∈ V₃` blocks
it. -/
lemma dSeparated_of_subset_left {V₁ V₂ V₃ : Finset V} (h : V₁ ⊆ V₃) :
    G.DSeparated V₁ V₂ V₃ := by
  intro s hs t _ p hact
  have hhead := p.head
  have h0 : p.toWalk.verts[0]? = some s := by
    show p.verts[0]? = some s
    cases hv : p.verts with
    | nil => rw [hv] at hhead; simp at hhead
    | cons a l => rw [hv] at hhead; exact List.getElem?_cons_zero.trans hhead
  have hnc : ¬ p.toWalk.IsColliderAt 0 := by
    rintro ⟨a, b, c, -, -, -, hk, -, -⟩
    exact absurd hk (lt_irrefl 0)
  exact (hact 0 s h0).2 hnc (h hs)

/-- The mirror of `dSeparated_of_subset_left`, blocking at the last trail vertex. -/
lemma dSeparated_of_subset_right {V₁ V₂ V₃ : Finset V} (h : V₂ ⊆ V₃) :
    G.DSeparated V₁ V₂ V₃ := by
  intro s _ t ht p hact
  have hlast := p.last
  have hn : p.toWalk.verts[p.verts.length - 1]? = some t := by
    show p.verts[p.verts.length - 1]? = some t
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  have hnc : ¬ p.toWalk.IsColliderAt (p.verts.length - 1) := by
    rintro ⟨a, b, c, -, -, hc, hk, -, -⟩
    rw [show p.verts.length - 1 + 1 = p.verts.length by omega] at hc
    rw [show p.toWalk.verts = p.verts from rfl,
      List.getElem?_eq_none (le_refl p.verts.length)] at hc
    simp at hc
  exact (hact _ t hn).2 hnc (h ht)

/-- The one-edge trail `s — t` along a skeleton edge between distinct vertices. -/
def Trail.pair {s t : V} (h : G.Skel s t) (hne : s ≠ t) : G.Trail s t where
  verts := [s, t]
  chain := by simpa using h
  head := rfl
  last := rfl
  nodup := by simp [hne]

private lemma Trail.pair_verts {s t : V} (h : G.Skel s t) (hne : s ≠ t) :
    (Trail.pair h hne).toWalk.verts = [s, t] := rfl

private lemma Trail.pair_not_isColliderAt {s t : V} (h : G.Skel s t) (hne : s ≠ t) (k : ℕ) :
    ¬ (Trail.pair h hne).toWalk.IsColliderAt k := by
  rintro ⟨a, b, c, -, -, hc, hk, -, -⟩
  rw [Trail.pair_verts] at hc
  rcases Nat.lt_or_ge (k + 1) 2 with hlt | hge
  · omega
  · rw [List.getElem?_eq_none (by simpa using hge)] at hc
    simp at hc

/-- The one-edge trail is active given `Z` as soon as neither endpoint is in `Z`: it has no
collider, and its only vertices are its two endpoints. -/
lemma Trail.pair_active {s t : V} (h : G.Skel s t) (hne : s ≠ t) {Z : Finset V}
    (hs : s ∉ Z) (ht : t ∉ Z) : (Trail.pair h hne).Active Z := by
  intro k v hv
  refine ⟨fun hcol => absurd hcol (Trail.pair_not_isColliderAt h hne k), fun _ => ?_⟩
  rw [Trail.pair_verts] at hv
  match k with
  | 0 =>
    have : v = s := by simpa using hv.symm
    exact this ▸ hs
  | 1 =>
    have : v = t := by simpa using hv.symm
    exact this ▸ ht
  | (n + 2) => simp at hv

/-- **Adjacent vertices outside the conditioning set are never d-separated.**  If `s ∈ V₁`
and `t ∈ V₂` are distinct, joined by an edge in either direction, and neither is in `V₃`,
then the one-edge trail between them is active. -/
lemma not_dSeparated_of_skel {V₁ V₂ V₃ : Finset V} {s t : V} (hs : s ∈ V₁) (ht : t ∈ V₂)
    (hne : s ≠ t) (hadj : G.Skel s t) (hs3 : s ∉ V₃) (ht3 : t ∉ V₃) :
    ¬ G.DSeparated V₁ V₂ V₃ := fun h =>
  h s hs t ht (Trail.pair hadj hne) (Trail.pair_active hadj hne hs3 ht3)

/-- d-separation of sets is d-separation of their members pairwise. -/
lemma dSeparated_iff_forall_singleton (V₁ V₂ V₃ : Finset V) :
    G.DSeparated V₁ V₂ V₃ ↔ ∀ s ∈ V₁, ∀ t ∈ V₂, G.DSeparated {s} {t} V₃ := by
  constructor
  · intro h s hs t ht s' hs' t' ht' p
    simp only [Finset.mem_singleton] at hs' ht'
    subst hs'; subst ht'
    exact h _ hs _ ht p
  · intro h s hs t ht p
    exact h s hs t ht s (Finset.mem_singleton_self s) t (Finset.mem_singleton_self t) p

end Digraph
