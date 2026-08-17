import FactoredSpaces.DSeparation

/-!
# Conditional histories in the factored space of a DAG

The closed form behind the direct proof of Proposition 5.5
(`notes/dsep-sizing/memo-2026-08-17.md`, Theorem 1).  For a DAG `G`, a conditioning set
`Z ⊆ V` with value `z`, and a node `s`:

* `A_Z(v)` (`unblockedAnc`) — the vertices reaching `v` by a directed path whose
  non-terminal vertices avoid `Z` (so `v ∈ A_Z(v)`);
* a set `S ⊆ V` is `Z`-closed if `A_Z(w) ∩ S ≠ ∅ ⟹ A_Z(w) ⊆ S` for every `w ∈ Z`, and
  `S_Z(s)` (`zClosure`) is the least `Z`-closed set containing `A_Z(s)` (`∅` if `s ∈ Z`);
* `I^z` (`zConsistent z`) — the indices `(u, y) ∈ I` whose parent configuration `y` agrees
  with `z` on `pa(u) ∩ Z`.

Then `H(X_A | X_Z = z) = I^z ∩ I_{S_Z(A)}` (`mem_history_nodesVar_iff`): the vertex set
does not depend on `z`, so structural independence of `X_{V₁}, X_{V₂}` given `X_{V₃}` is
`S_Z(V₁) ∩ S_Z(V₂) = ∅` (`structIndepGiven_nodesVar_iff_disjoint_zClosure`).  All of this
needs `|Val_v| ≥ 2` for every `v`.
-/

universe u

namespace Digraph

variable {V : Type u} [DecidableEq V] (G : Digraph V)

/-- `A_Z(v)`: vertices `u` with a directed path `u = u₀ → ⋯ → u_k = v` (`k ≥ 0`) whose
vertices `u₀, …, u_{k−1}` avoid `Z`. -/
def unblockedAnc (Z : Finset V) (v : V) : Set V :=
  {u | Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ Z) u v}

/-- `S` is `Z`-closed: whenever `A_Z(w)` meets `S` for some `w ∈ Z`, all of `A_Z(w) ⊆ S`. -/
def IsZClosed (Z : Finset V) (S : Set V) : Prop :=
  ∀ w ∈ Z, (G.unblockedAnc Z w ∩ S).Nonempty → G.unblockedAnc Z w ⊆ S

/-- `S_Z(s)`: the least `Z`-closed set containing `A_Z(s)` for `s ∉ Z`, and `∅` for `s ∈ Z`. -/
def zClosure (Z : Finset V) (s : V) : Set V :=
  if s ∈ Z then ∅ else ⋂₀ {S | G.IsZClosed Z S ∧ G.unblockedAnc Z s ⊆ S}

/-- `S_Z(A) = ⋃_{a∈A} S_Z(a)`. -/
def zClosureSet (Z A : Finset V) : Set V := ⋃ a ∈ A, G.zClosure Z a

variable {G}

omit [DecidableEq V] in
lemma mem_unblockedAnc_self (Z : Finset V) (v : V) : v ∈ G.unblockedAnc Z v :=
  Relation.ReflTransGen.refl

lemma unblockedAnc_subset_zClosure {Z : Finset V} {s : V} (hs : s ∉ Z) :
    G.unblockedAnc Z s ⊆ G.zClosure Z s := by
  sorry

lemma isZClosed_zClosure (Z : Finset V) (s : V) : G.IsZClosed Z (G.zClosure Z s) := by
  sorry

lemma zClosure_subset {Z : Finset V} {s : V} {S : Set V} (hS : G.IsZClosed Z S)
    (hs : G.unblockedAnc Z s ⊆ S) : G.zClosure Z s ⊆ S := by
  sorry

/-- The induction principle for `S_Z(s)`: it is generated from `A_Z(s)` by repeatedly
adjoining `A_Z(w)` for `w ∈ Z` whenever `A_Z(w)` meets what has been built. -/
lemma zClosure_induction {Z : Finset V} {s : V} (hs : s ∉ Z) {P : V → Prop}
    (base : ∀ u ∈ G.unblockedAnc Z s, P u)
    (step : ∀ w ∈ Z, ∀ u ∈ G.unblockedAnc Z w, (∃ m ∈ G.unblockedAnc Z w, P m) → P u) :
    ∀ u ∈ G.zClosure Z s, P u := by
  sorry

end Digraph

namespace FactoredSpaces

variable {V : Type u} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val : V → Type u} [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)]

/-- `I^z`: the indices `(u, y)` whose parent configuration `y` agrees with `z` on
`pa(u) ∩ Z`. -/
def zConsistent (G : Digraph V) [DecidableRel G.Adj] (Val : V → Type u) {Z : Finset V}
    (z : PtOn Val Z) : Set (bnIndex G Val) :=
  {i | ∀ p : G.parents i.1, ∀ hp : p.1 ∈ Z, i.2 p = z ⟨p.1, hp⟩}

/-- **Realization**: every joint value `x` with `x_Z = z` is attained on the event
`{X_Z = z}` (by the constant tables `ω_{(v,·)} ≡ x_v`). -/
lemma exists_mem_fiber_nodesVar (hG : G.IsAcyclic) (Z : Finset V) (x : Pt Val) :
    ∃ ω ∈ fiber (nodesVar (Val := Val) hG Z) (proj Z x), jointVar hG ω = x := by
  sorry

/-- **The conditional history of a family of node variables**, in closed form:
`H(X_A | X_Z = z) = I^z ∩ I_{S_Z(A)}` (memo, Theorem 1). -/
lemma mem_history_nodesVar_iff [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic)
    (A Z : Finset V) (z : PtOn Val Z) (i : bnIndex G Val) :
    i ∈ history (nodesVar (Val := Val) hG A) (fiber (nodesVar hG Z) z) ↔
      i ∈ zConsistent G Val z ∧ i.1 ∈ G.zClosureSet Z A := by
  sorry

/-- **Structural independence of node families is a vertex-set criterion**:
`X_{V₁} ⊥ X_{V₂} | X_{V₃}` in `M^G` iff `S_{V₃}(V₁) ∩ S_{V₃}(V₂) = ∅` (memo, Corollary 2). -/
lemma structIndepGiven_nodesVar_iff_disjoint_zClosure [∀ v, Nontrivial (Val v)]
    (hG : G.IsAcyclic) (V₁ V₂ V₃ : Finset V) :
    StructIndepGiven (nodesVar (Val := Val) hG V₁) (nodesVar hG V₂) (nodesVar hG V₃) ↔
      Disjoint (G.zClosureSet V₃ V₁) (G.zClosureSet V₃ V₂) := by
  sorry

end FactoredSpaces
