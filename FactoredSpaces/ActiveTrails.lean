import FactoredSpaces.ConditionalHistory

/-!
# Active trails and the `Z`-closure criterion

The graph-theoretic half of the direct proof of Proposition 5.5
(`notes/dsep-sizing/memo-2026-08-17.md`, Theorem 3): for vertices `s, t`,
`S_Z(s) ∩ S_Z(t) ≠ ∅` iff there is an active trail between `s` and `t` given `Z`.  The
easy direction decomposes an active trail at its colliders into forks; the hard direction
builds an active *walk* from a witness of the intersection and shortens it to a trail.
-/

universe u

namespace Digraph

variable {V : Type u} [Fintype V] [DecidableEq V] {G : Digraph V}

/-- An active walk between `s` and `t` shortens to an active trail: d-separation may
equivalently be defined through walks. -/
lemma exists_active_trail_of_active_walk (hG : G.IsAcyclic) {s t : V} {Z : Finset V}
    (p : G.Walk s t) (hp : p.Active Z) : ∃ q : G.Trail s t, q.Active Z := by
  sorry

/-- **Active trail ⟹ the closures meet** (memo, Theorem 3, easy direction). -/
lemma zClosure_inter_nonempty_of_active_trail (hG : G.IsAcyclic) {s t : V} {Z : Finset V}
    (p : G.Trail s t) (hp : p.Active Z) : (G.zClosure Z s ∩ G.zClosure Z t).Nonempty := by
  sorry

/-- **The closures meet ⟹ an active trail exists** (memo, Theorem 3, hard direction). -/
lemma exists_active_trail_of_zClosure_inter_nonempty (hG : G.IsAcyclic) {s t : V} {Z : Finset V}
    (h : (G.zClosure Z s ∩ G.zClosure Z t).Nonempty) : ∃ p : G.Trail s t, p.Active Z := by
  sorry

/-- **`Z`-closure criterion for d-separation**: `V₁` and `V₂` are d-separated given `V₃`
iff `S_{V₃}(V₁) ∩ S_{V₃}(V₂) = ∅` (memo, Theorem 3, set form). -/
lemma dSeparated_iff_disjoint_zClosureSet (hG : G.IsAcyclic) (V₁ V₂ V₃ : Finset V) :
    G.DSeparated V₁ V₂ V₃ ↔ Disjoint (G.zClosureSet V₃ V₁) (G.zClosureSet V₃ V₂) := by
  sorry

end Digraph
