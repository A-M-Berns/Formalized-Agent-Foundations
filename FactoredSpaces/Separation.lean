import FactoredSpaces.ActiveTrails

/-!
# d-separation is structural independence in `M^G` (Proposition 5.5)

The paper proves Proposition 5.5 by citing the soundness and completeness of d-separation
(Koller–Friedman) and applying Lemma 5.3 and Theorem 6.2, remarking that a direct proof
is possible.  We take the direct route (`notes/dsep-sizing/memo-2026-08-17.md`): a
closed-form description of the conditional histories `H(X_A | X_Z = z)` in `M^G`
(`ConditionalHistory.lean`) and a purely graph-theoretic equivalence between the resulting
vertex-set criterion and the existence of an active trail (`ActiveTrails.lean`).  Nothing
probabilistic is used, and no external theorem is cited.
-/

namespace FactoredSpaces

universe u w

variable {V : Type u} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val : V → Type w} [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)]

/-- **d-separation.** For sets of nodes `V₁, V₂, V₃ ⊆ V`: `V₁` and `V₂` are d-separated
given `V₃` in `G` iff `X_{V₁}` and `X_{V₂}` are structurally independent given `X_{V₃}` in
`M^G`.  Needs every `Val_v` to have at least two elements (the paper's standing
assumption; a one-element `Val_v` makes `v` invisible to the histories).

Applying this to a concrete DAG, supply the value family explicitly — `… (Val := Val) …` —
rather than leaving it to be inferred from the expected type: with `Val` a metavariable the
unifier compares the `Fintype`/`DecidableEq` instances of `Pt (bnFactor G Val)` by
evaluating them, and exceeds the heartbeat limit.  `FactoredSpaces/Examples.lean` shows the
working idiom.

Paper node: Proposition 5.5 (§5.2). -/
theorem dSeparated_iff_structIndepGiven [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic)
    (V₁ V₂ V₃ : Finset V) :
    G.DSeparated V₁ V₂ V₃ ↔
      StructIndepGiven (nodesVar (Val := Val) hG V₁) (nodesVar hG V₂) (nodesVar hG V₃) := by
  rw [Digraph.dSeparated_iff_disjoint_zClosureSet hG,
    structIndepGiven_nodesVar_iff_disjoint_zClosure hG]

end FactoredSpaces
