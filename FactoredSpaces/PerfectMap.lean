import FactoredSpaces.Separation

/-!
# Perfect maps (§5.2.3, Definition 5.7, Proposition 5.8)

A DAG is a perfect map of a distribution `P` on its joint value space if its
d-separations are exactly the conditional independences of `P` among the node
projections; a factored space model is a perfect map of `P` with regard to a family of
variables if it is a model of `P` and its structural independences among the family are
exactly the conditional independences of `P` among the corresponding projections.
Factored space models are more expressive than DAGs (Proposition 5.8).
-/

namespace FactoredSpaces

universe u

section DAG

variable {V : Type u} [Fintype V] [DecidableEq V] {Val : V → Type u} [∀ v, Fintype (Val v)]

/-- **Perfect map (DAG).** `G` (with value space `Val = ×_v Val_v`) is a perfect map of a
distribution `P` on `Val` if for all sets of nodes `V₁, V₂, V₃ ⊆ V`, `V₁` and `V₂` are
d-separated given `V₃` in `G` iff `X_{V₁}` and `X_{V₂}` are independent given `X_{V₃}` in
`P` — the `X_S` being the coordinate projections of the observation space `Val`, which is
the paper's `Val(X̄) = Obs`.

Paper node: Definition 5.7 (§5.2). -/
def IsPerfectMapDAG (G : Digraph V) (P : Dist (Pt Val)) : Prop :=
  ∀ V₁ V₂ V₃ : Finset V,
    G.DSeparated V₁ V₂ V₃ ↔ CondIndepVar P (proj V₁) (proj V₂) (proj V₃)

end DAG

section FSM

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type u} [∀ i, Fintype (Ω i)]
variable {W : Type u} [Fintype W] [DecidableEq W] {Val : W → Type u} [∀ w, Fintype (Val w)]

/-- The subfamily `X_S = (X_w)_{w∈S}` of a family of variables `X = (X_w)_{w∈W}` on `Ω`. -/
def famVar (X : ∀ w : W, Pt Ω → Val w) (S : Finset W) : Pt Ω → PtOn Val S :=
  fun ω w => X w ω

/-- The joint variable `(X_w)_{w∈W} : Ω → ×_w Val_w` of a family — the observation variable
of the model `(Ω, X)`. -/
def famJoint (X : ∀ w : W, Pt Ω → Val w) : Pt Ω → Pt Val := fun ω w => X w ω

/-- **Perfect map (factored space model).** The model `M = (Ω, X)`, `X = (X_w)_{w∈W}` a
family of variables on `Ω` with joint value space `Val = ×_w Val_w`, is a perfect map of a
distribution `P` on `Val` with regard to `X` if `M` is a factored space model of `P` and
for all `W₁, W₂, W₃ ⊆ W`, `X_{W₁}` and `X_{W₂}` are independent given `X_{W₃}` in `P` (as
projections of `Val`) iff they are structurally independent given `X_{W₃}` in `Ω`.
(The paper types the family as `X_w : Ω → Obs`; read `Obs = ×_w Val(X_w)` and `O` as the
joint variable, which is how Proposition 5.8 uses it — see `notes/paper-errata.md`.)

Paper node: Definition 5.7 (§5.2). -/
def IsPerfectMapFSM (X : ∀ w : W, Pt Ω → Val w) (P : Dist (Pt Val)) : Prop :=
  IsFactoredSpaceModel (famJoint X) P ∧
    ∀ W₁ W₂ W₃ : Finset W,
      CondIndepVar P (proj W₁) (proj W₂) (proj W₃) ↔
        StructIndepGiven (famVar X W₁) (famVar X W₂) (famVar X W₃)

end FSM

section Expressiveness

variable {V : Type u} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val : V → Type u} [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)]

/-- **Perfect maps of graphs and factored spaces (1)**, concretely: if `G` is a perfect map
of `P` then `M^G` is a perfect map of `P` with regard to `(X_v)_{v∈V}`.

Paper node: Proposition 5.8 (§5.2). -/
theorem isPerfectMapFSM_nodeVar_of_isPerfectMapDAG [∀ v, Nontrivial (Val v)]
    (hG : G.IsAcyclic) {P : Dist (Pt Val)} (h : IsPerfectMapDAG G P) :
    IsPerfectMapFSM (nodeVar (Val := Val) hG) P := by
  sorry

/-- **Perfect maps of graphs and factored spaces (1).** If some DAG `G` with nodes `V` is a
perfect map of `P`, then some factored space model `M = (Ω, X)` with `X = (X_v)_{v∈V}` is a
perfect map of `P` with regard to `X`.

Paper node: Proposition 5.8 (§5.2). -/
theorem exists_isPerfectMapFSM_of_exists_isPerfectMapDAG [∀ v, Nontrivial (Val v)]
    {P : Dist (Pt Val)}
    (h : ∃ (G : Digraph V) (_ : DecidableRel G.Adj), G.IsAcyclic ∧ IsPerfectMapDAG G P) :
    ∃ (I : Type u) (Ω : I → Type u) (_ : Fintype I) (_ : DecidableEq I)
      (_ : ∀ i, Fintype (Ω i)) (X : ∀ v, Pt Ω → Val v), IsPerfectMapFSM X P := by
  sorry

end Expressiveness

/-- **Perfect maps of graphs and factored spaces (2).** There is a distribution `P` on an
observation space `×_v Val_v` (every `Val_v` with at least two elements) with a factored
space model that is a perfect map of `P` with regard to `(X_v)_v`, but no DAG with nodes
`V` that is a perfect map of `P`.  The paper's witness: `Ω = Ω₁ = {0, 1, 2}`,
`X₁ = U₁`, `X₂ = [U₁ > 0]`, so `X₂ ⊥ X₂ | X₁` holds in `P` and structurally, while no
graph d-separates `v₂` from itself given `v₁`.

Paper node: Proposition 5.8 (§5.2). -/
theorem exists_isPerfectMapFSM_not_exists_isPerfectMapDAG :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (Val : V → Type) (_ : ∀ v, Fintype (Val v))
      (_ : ∀ v, Nontrivial (Val v)) (P : Dist (Pt Val)),
      (∃ (I : Type) (Ω : I → Type) (_ : Fintype I) (_ : DecidableEq I) (_ : ∀ i, Fintype (Ω i))
        (X : ∀ v, Pt Ω → Val v), IsPerfectMapFSM X P) ∧
      ∀ G : Digraph V, G.IsAcyclic → ¬ IsPerfectMapDAG G P := by
  sorry

end FactoredSpaces
