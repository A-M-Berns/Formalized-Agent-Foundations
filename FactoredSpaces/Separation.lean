import FactoredSpaces.ActiveTrails

/-!
# d-separation and ancestry in `M^G` (Propositions 5.5, 5.6)

The paper proves Proposition 5.5 by citing the soundness and completeness of d-separation
(Koller–Friedman) and applying Lemma 5.3 and Theorem 6.2, remarking that a direct proof
is possible.  We take the direct route (`notes/dsep-sizing/memo-2026-08-17.md`): a
closed-form description of the conditional histories `H(X_A | X_Z = z)` in `M^G`
(`ConditionalHistory.lean`) and a purely graph-theoretic equivalence between the resulting
vertex-set criterion and the existence of an active trail (`ActiveTrails.lean`).  Nothing
probabilistic is used, and no external theorem is cited.

Proposition 5.6 is proved here too, because it is the `Z = ∅`, `A = {v}` case of the same
closed form: `H(X_v) = I^∅ ∩ I_{S_∅({v})}`, and `S_∅({v})` is the set of
ancestors-or-self of `v`.  Stating it in `BayesNet.lean` would mean re-proving that case by
hand.
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

/-! ## Proposition 5.6: the ancestor relation

The history of a single node variable, unconditioned, is the `Z = ∅`, `A = {v}` instance of
`mem_history_nodesVar_iff`: with nothing conditioned on, every index is `z`-consistent and
`S_∅(v)` is `A_∅(v)`, the set of ancestors-or-self of `v`. -/

/-- The history of a node variable: `H(X_v) = ⋃_{u ∈ an(v) ∪ {v}} I_u` (the identity the
proof of Proposition 5.6 starts from), stated as a membership criterion. -/
lemma mem_history_nodeVar_iff [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic) (v : V)
    (i : bnIndex G Val) :
    i ∈ history (nodeVar (Val := Val) hG v) (Set.univ : Set (Pt (bnFactor G Val))) ↔
      i.1 = v ∨ G.IsAncestor i.1 v := by
  classical
  obtain ⟨z⟩ : Nonempty (PtOn Val (∅ : Finset V)) := ⟨fun i => absurd i.2 (Finset.notMem_empty _)⟩
  have hC : fiber (nodesVar (Val := Val) hG ∅) z = Set.univ := by
    ext ω
    simp only [Set.mem_univ, iff_true]
    exact (mem_fiber_nodesVar_iff hG).mpr fun w => absurd w.2 (Finset.notMem_empty _)
  have hd1 : DerivedOn (Set.univ : Set (Pt (bnFactor G Val)))
      (nodesVar (Val := Val) hG {v}) (nodeVar hG v) :=
    ⟨fun y => y ⟨v, Finset.mem_singleton_self v⟩, fun _ _ => rfl⟩
  constructor
  · intro h
    have h2 := history_mono_of_derived hd1 h
    rw [← hC] at h2
    obtain ⟨-, hmem⟩ := (mem_history_nodesVar_iff hG {v} ∅ z i).mp h2
    obtain ⟨a, ha, -, hia⟩ := G.exists_of_mem_zClosureSet hmem
    rw [Finset.mem_singleton] at ha
    subst ha
    have hsub : G.zClosure ∅ a ⊆ {u | Relation.ReflTransGen G.Adj u a} :=
      Digraph.zClosure_subset (fun w hw => absurd hw (Finset.notMem_empty w))
        (fun u hu => hu.mono fun _ _ h => h.1)
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp (hsub hia) with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  · intro h
    rw [← hC]
    refine mem_history_nodeVar_of_unblockedAnc hG (Finset.notMem_empty v)
      (fun p hp => absurd hp (Finset.notMem_empty _)) ?_
    rcases h with h | h
    · exact h ▸ Digraph.mem_unblockedAnc_self _ _
    · exact (Relation.reflTransGen_iff_eq_or_transGen.mpr (Or.inr h)).mono
        fun a b hab => ⟨hab, Finset.notMem_empty a⟩

/-- **Ancestor relation.** For distinct nodes `v₁ ≠ v₂`: `v₁` is an ancestor of `v₂` in `G`
iff `X_{v₁} <_{Ω^G} X_{v₂}`.  Needs every `Val_v` to have at least two elements (the
paper's standing assumption on `Val`; with a one-element `Val_v` the node `v` carries no
randomness and drops out of every history).

Applying this to a concrete DAG, supply the value family explicitly — `… (Val := Val) …` —
rather than leaving it to be inferred from the expected type: with `Val` a metavariable the
unifier compares the `Fintype`/`DecidableEq` instances of `Pt (bnFactor G Val)` by
evaluating them, and exceeds the heartbeat limit.  `FactoredSpaces/Examples.lean` shows the
working idiom.

Paper node: Proposition 5.6 (§5.2). -/
theorem isAncestor_iff_strictlyBefore [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic)
    {v₁ v₂ : V} (hne : v₁ ≠ v₂) :
    G.IsAncestor v₁ v₂ ↔ StrictlyBefore (nodeVar (Val := Val) hG v₁) (nodeVar hG v₂) := by
  constructor
  · intro h
    have hsub : history (nodeVar (Val := Val) hG v₁) (Set.univ : Set (Pt (bnFactor G Val)))
        ⊆ history (nodeVar (Val := Val) hG v₂) Set.univ := by
      intro i hi
      rw [mem_history_nodeVar_iff] at hi ⊢
      rcases hi with h1 | h1
      · exact Or.inr (by rw [h1]; exact h)
      · exact Or.inr (h1.trans h)
    refine (Finset.ssubset_iff_of_subset hsub).mpr ?_
    obtain ⟨c⟩ : Nonempty (ParentVals G Val v₂) := inferInstance
    refine ⟨⟨v₂, c⟩, (mem_history_nodeVar_iff hG v₂ _).mpr (Or.inl rfl), ?_⟩
    rw [mem_history_nodeVar_iff]
    rintro (h1 | h1)
    · exact hne h1.symm
    · exact hG v₁ (h.trans h1)
  · intro h
    obtain ⟨c⟩ : Nonempty (ParentVals G Val v₁) := inferInstance
    have hmem : (⟨v₁, c⟩ : bnIndex G Val) ∈
        history (nodeVar (Val := Val) hG v₂) (Set.univ : Set (Pt (bnFactor G Val))) :=
      subset_of_ssubset h ((mem_history_nodeVar_iff hG v₁ _).mpr (Or.inl rfl))
    rcases (mem_history_nodeVar_iff hG v₂ _).mp hmem with h1 | h1
    · exact absurd h1 hne
    · exact h1

end FactoredSpaces
