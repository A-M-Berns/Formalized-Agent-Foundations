import FactoredSpaces.MainTheorem
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma

/-!
# From Bayesian networks to factored space models (§5.2, Appendix B.2)

A DAG `G = (V, E, Val)` (a `Digraph V` that is acyclic, with a value type `Val v` per
node), the factored space `Ω^G` indexed by `I = ⋃_v I_v`, `I_v = {(v, x_pa(v))}`, the
node variables `X_v(ω) = ω_{(v, X_pa(v)(ω))}` (well-founded recursion along the DAG), the
observation variable `X = (X_v)_v`, factorization of a distribution over `G`
(`dd:cpd`), the map `τ` (Lemma 5.3), Lemma B.2 and the factorization property
(Proposition 5.4).  The ancestor relation (Proposition 5.6) is proved in
`FactoredSpaces/Separation.lean`, as a corollary of the closed-form conditional history.
-/

universe u w

/-! ## DAGs (generic vocabulary, in the root `Digraph` namespace) -/

namespace Digraph

section

variable {V : Type u} (G : Digraph V)

/-- `G` is acyclic: no vertex reaches itself along a nonempty directed path. -/
def IsAcyclic : Prop := ∀ v, ¬ Relation.TransGen G.Adj v v

/-- `u` is an ancestor of `v`: there is a nonempty directed path `u → ⋯ → v`.  The paper's
`an(v)` is `{u | G.IsAncestor u v}`. -/
def IsAncestor (u v : V) : Prop := Relation.TransGen G.Adj u v

/-- On a finite acyclic digraph the edge relation is well-founded (`u ≺ v` iff `u → v`),
which is what defines the node variables recursively. -/
lemma IsAcyclic.wf [Finite V] {G : Digraph V} (h : G.IsAcyclic) : WellFounded G.Adj := by
  haveI : IsTrans V (Relation.TransGen G.Adj) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  haveI : Std.Irrefl (Relation.TransGen G.Adj) := ⟨h⟩
  exact Subrelation.wf (fun hxy => Relation.TransGen.single hxy)
    (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen G.Adj))

/-- The parents `pa(v) = {u | u → v}` of a vertex. -/
def parents [Fintype V] [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter fun u => G.Adj u v

lemma mem_parents [Fintype V] [DecidableRel G.Adj] {u v : V} : u ∈ G.parents v ↔ G.Adj u v := by
  simp [parents]

end

/-! ### Consequences of acyclicity

The one-line facts every file of §5.2 uses: an edge has distinct endpoints, is not
reversible, and its head is not an ancestor-or-self of its tail. -/

section Acyclic

variable {V : Type u} {G : Digraph V}

/-- An edge of an acyclic digraph has distinct endpoints. -/
lemma IsAcyclic.ne_of_adj (hG : G.IsAcyclic) {u v : V} (h : G.Adj u v) : u ≠ v := by
  rintro rfl
  exact hG u (Relation.TransGen.single h)

/-- An edge of an acyclic digraph has no reverse edge. -/
lemma IsAcyclic.not_adj_symm (hG : G.IsAcyclic) {a b : V} (h : G.Adj a b) : ¬ G.Adj b a :=
  fun h' => hG a ((Relation.TransGen.single h).trans (Relation.TransGen.single h'))

/-- The head of an edge is neither the tail nor an ancestor of the tail. -/
lemma IsAcyclic.not_ancestor_of_adj (hG : G.IsAcyclic) {u v : V} (h : G.Adj u v) :
    ¬ (v = u ∨ G.IsAncestor v u) := by
  rintro (rfl | hvu)
  · exact hG _ (Relation.TransGen.single h)
  · exact hG v (hvu.trans (Relation.TransGen.single h))

end Acyclic

/-! ### Parents, depth and ancestral closure

`depth` is strictly increasing along edges, so it is a topological order on an acyclic
`G`; ancestrally closed sets are the sets the chain rule of
`FactoredSpaces.prob_agreeOn_eq_prod` recurses on, by removing a node of maximal depth. -/

section Depth

variable {V : Type u} [Fintype V] {G : Digraph V} [DecidableRel G.Adj]

/-- No vertex of an acyclic digraph is one of its own parents. -/
lemma notMem_parents_self (hG : G.IsAcyclic) (v : V) : v ∉ G.parents v := fun h =>
  hG v (Relation.TransGen.single ((mem_parents G).mp h))

/-- The depth of a node: `0` at the sources, one more than the deepest parent elsewhere.
`depth_lt` makes it a topological order on an acyclic `G`. -/
noncomputable def depth (hG : G.IsAcyclic) : V → ℕ :=
  hG.wf.fix fun v ih => (G.parents v).attach.sup fun u => ih u.1 ((mem_parents G).mp u.2) + 1

lemma depth_eq (hG : G.IsAcyclic) (v : V) :
    depth hG v = (G.parents v).attach.sup fun u => depth hG u.1 + 1 := by
  conv_lhs => rw [depth]
  rw [WellFounded.fix_eq]
  rfl

lemma depth_lt (hG : G.IsAcyclic) {u v : V} (h : G.Adj u v) : depth hG u < depth hG v := by
  rw [depth_eq hG v]
  exact lt_of_lt_of_le (Nat.lt_succ_self _)
    (Finset.le_sup (f := fun w : {w // w ∈ G.parents v} => depth hG w.1 + 1)
      (Finset.mem_attach _ ⟨u, (mem_parents G).mpr h⟩))

lemma depth_lt_of_isAncestor (hG : G.IsAcyclic) {u v : V} (h : G.IsAncestor u v) :
    depth hG u < depth hG v := by
  induction h with
  | single h => exact depth_lt hG h
  | tail _ h ih => exact ih.trans (depth_lt hG h)

variable (G) in
/-- A set of nodes is *ancestrally closed* if it contains the parents of each of its
members.  `Finset.univ` is, and removing a node of maximal depth preserves it, which is
the recursion the chain rule of `FactoredSpaces.prob_agreeOn_eq_prod` runs on. -/
def AncClosed (S : Finset V) : Prop :=
  ∀ v ∈ S, G.parents v ⊆ S

end Depth

end Digraph

namespace FactoredSpaces

/-! ## Families of variables

A factored space model observes `Ω` through a *family* `X = (X_w)_{w∈W}` of variables;
`famVar` is the subfamily `X_S` and `famJoint` the joint variable `(X_w)_{w∈W}`.  The node
variables of a DAG (below) are the case `W = V`, and `nodesVar`/`jointVar` are literally
`famVar`/`famJoint` applied to them, so Proposition 5.5 and Definition 5.7 speak about the
same functions. -/

section Family

variable {I : Type*} {Ω : I → Type*} {W : Type*} {Val : W → Type*}

/-- The subfamily `X_S = (X_w)_{w∈S}` of a family of variables `X = (X_w)_{w∈W}` on `Ω`. -/
def famVar (X : ∀ w : W, Pt Ω → Val w) (S : Finset W) : Pt Ω → PtOn Val S :=
  fun ω w => X w ω

/-- The joint variable `(X_w)_{w∈W} : Ω → ×_w Val_w` of a family — the observation variable
of the model `(Ω, X)`. -/
def famJoint (X : ∀ w : W, Pt Ω → Val w) : Pt Ω → Pt Val := fun ω w => X w ω

end Family

/-! ## The factored space of a DAG -/

section Construction

variable {V : Type u} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
  (Val : V → Type w) [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)]

/-- The paper's `Val_{pa(v)}`: assignments of values to the parents of `v`.  (`PtOn Val
(G.parents v)` — the joint value space `Val = ×_v Val_v` is itself the point type
`Pt Val`, so the §4 projection vocabulary applies to it.) -/
abbrev ParentVals (v : V) : Type max u w := PtOn Val (G.parents v)

/-- The parent configuration `x_pa(v)` of a joint value `x ∈ Val`. -/
def parentConfig (x : Pt Val) (v : V) : ParentVals G Val v := proj (G.parents v) x

/-- The index set `I = ⋃_{v∈V} I_v` with `I_v = {(v, x_pa(v)) | x_pa(v) ∈ Val_pa(v)}`. -/
abbrev bnIndex : Type max u w := Σ v : V, ParentVals G Val v

/-- The factors `Ω^G_{(v, x_pa(v))} = Val_v`; the factored space constructed from `G` is
`Pt (bnFactor G Val)`. -/
abbrev bnFactor : bnIndex G Val → Type w := fun i => Val i.1

variable {G Val}

/-- **The node variables** `X_v : Ω^G → Val_v`, defined recursively along the DAG by
`X_v(ω) = ω_{(v, X_pa(v)(ω))}` (eq. (4) of §5.2); `nodeVar_apply` is the unfolding. -/
noncomputable def nodeVar (hG : G.IsAcyclic) : ∀ v : V, Pt (bnFactor G Val) → Val v :=
  hG.wf.fix fun v ih ω => ω ⟨v, fun u => ih u.1 ((Digraph.mem_parents G).mp u.2) ω⟩

omit [DecidableEq V] [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
lemma nodeVar_apply (hG : G.IsAcyclic) (v : V) (ω : Pt (bnFactor G Val)) :
    nodeVar hG v ω = ω ⟨v, fun u => nodeVar hG u.1 ω⟩ := by
  show hG.wf.fix (C := fun v => Pt (bnFactor G Val) → Val v)
      (fun v ih ω => ω ⟨v, fun u => ih u.1 ((Digraph.mem_parents G).mp u.2) ω⟩) v ω = _
  rw [WellFounded.fix_eq]
  rfl

/-- The joint node variable `X = (X_v)_{v∈V} : Ω^G → Val`, the observation variable `O` of
the factored space model `M^G = (Ω^G, X)` constructed from `G` (§5.2) — the family
`(X_v)_{v∈V}` read as one variable. -/
noncomputable def jointVar (hG : G.IsAcyclic) : Pt (bnFactor G Val) → Pt Val :=
  famJoint (nodeVar hG)

/-- The family `X_S = (X_v)_{v∈S}` for a set of nodes `S ⊆ V`. -/
noncomputable def nodesVar (hG : G.IsAcyclic) (S : Finset V) : Pt (bnFactor G Val) → PtOn Val S :=
  famVar (nodeVar hG) S

/-! ### Reading off the node variables

`X_v(ω)` is a single table lookup, at the index `(v, X_pa(v)(ω))` that the joint value
`X(ω)` realizes at `v` (`nodeVar_eq_idxAt`).  Everything downstream constructs points of
`Ω^G` by prescribing those lookups, so this is the API the whole of §5.2 reads `nodeVar`
through; the evaluation principle is `nodeVar_eq_of_diag`. -/

variable (G Val) in
/-- The index `(v, x_pa(v))` that a joint value `x` realizes at `v`. -/
def idxAt (x : Pt Val) (v : V) : bnIndex G Val := ⟨v, parentConfig G Val x v⟩

omit [DecidableEq V] [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
@[simp] lemma idxAt_fst (x : Pt Val) (v : V) : (idxAt G Val x v).1 = v := rfl

omit [DecidableEq V] [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
/-- Two lookups at the same node with equal parent configurations agree.  (Stated
separately because rewriting the index of a dependent lookup `ω i` fails the motive
check.) -/
lemma table_congr (ω : Pt (bnFactor G Val)) {q : V} {c d : ParentVals G Val q} (h : c = d) :
    ω ⟨q, c⟩ = ω ⟨q, d⟩ := by cases h; rfl

omit [DecidableEq V] [(v : V) → Fintype (Val v)] [(v : V) → DecidableEq (Val v)] in
/-- If the parent configuration seen at `v` is `c`, then `X_v` reads off the factor
`(v, c)`. -/
lemma nodeVar_eq_coord (hG : G.IsAcyclic) (v : V) (ω : Pt (bnFactor G Val))
    (c : ParentVals G Val v) (hc : parentConfig G Val (jointVar hG ω) v = c) :
    nodeVar hG v ω = ω ⟨v, c⟩ := by
  rw [nodeVar_apply, show (fun u : ↥(G.parents v) => nodeVar hG (u : V) ω) = c from hc]

omit [DecidableEq V] [(v : V) → Fintype (Val v)] [(v : V) → DecidableEq (Val v)] in
/-- `X_v(ω) = ω_{(v, X_pa(v)(ω))}`: the index consulted at `v` is the one realized by the
joint value `X(ω)`. -/
lemma nodeVar_eq_idxAt (hG : G.IsAcyclic) (v : V) (ω : Pt (bnFactor G Val)) :
    nodeVar hG v ω = ω (idxAt G Val (jointVar hG ω) v) :=
  nodeVar_eq_coord hG v ω _ rfl

omit [DecidableEq V] [(v : V) → Fintype (Val v)] [(v : V) → DecidableEq (Val v)] in
/-- A node whose table is constant takes that constant value. -/
lemma nodeVar_eq_of_const (hG : G.IsAcyclic) {ω : Pt (bnFactor G Val)} {q : V} {c : Val q}
    (h : ∀ y : ParentVals G Val q, ω ⟨q, y⟩ = c) : nodeVar hG q ω = c := by
  rw [nodeVar_eq_idxAt]; exact h _

omit [DecidableEq V] [(v : V) → Fintype (Val v)] [(v : V) → DecidableEq (Val v)] in
/-- **The evaluation principle.**  If `ω` returns `x_q` at every index realized by `x`,
then `X(ω) = x`. -/
lemma nodeVar_eq_of_diag (hG : G.IsAcyclic) {x : Pt Val} {ω : Pt (bnFactor G Val)}
    (h : ∀ q, ω (idxAt G Val x q) = x q) (q : V) : nodeVar hG q ω = x q := by
  induction q using hG.wf.induction with
  | _ q ih =>
    have hc : parentConfig G Val (jointVar hG ω) q = parentConfig G Val x q :=
      funext fun p => ih p.1 ((Digraph.mem_parents G).mp p.2)
    rw [nodeVar_eq_idxAt]
    exact (table_congr ω hc).trans (h q)

omit [DecidableEq V] [(v : V) → Fintype (Val v)] [(v : V) → DecidableEq (Val v)] in
lemma jointVar_eq_of_diag (hG : G.IsAcyclic) {x : Pt Val} {ω : Pt (bnFactor G Val)}
    (h : ∀ q, ω (idxAt G Val x q) = x q) : jointVar hG ω = x :=
  funext (nodeVar_eq_of_diag hG h)

omit [DecidableEq V] [(v : V) → Fintype (Val v)] [(v : V) → DecidableEq (Val v)] in
/-- The set identity behind Lemma B.2: `{X = x} = {ω | ∀ v, ω_{(v, x_pa(v))} = x_v}`. -/
lemma jointVar_eq_iff (hG : G.IsAcyclic) (ω : Pt (bnFactor G Val)) (x : Pt Val) :
    jointVar hG ω = x ↔ ∀ v, ω (idxAt G Val x v) = x v := by
  refine ⟨fun hj v => ?_, jointVar_eq_of_diag hG⟩
  have hc : parentConfig G Val x v = parentConfig G Val (jointVar hG ω) v := by rw [hj]
  exact (table_congr ω hc).trans ((nodeVar_eq_idxAt hG v ω).symm.trans (congrFun hj v))

variable (G Val) in
/-- The "constant table" `ω_x`, with every factor of `I_v` holding `x_v`; it satisfies
`X(ω_x) = x`. -/
def constTable (x : Pt Val) : Pt (bnFactor G Val) := fun i => x i.1

omit [DecidableEq V] [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
@[simp] lemma constTable_apply (x : Pt Val) (i : bnIndex G Val) :
    constTable G Val x i = x i.1 := rfl

omit [DecidableEq V] [(v : V) → Fintype (Val v)] [(v : V) → DecidableEq (Val v)] in
lemma jointVar_constTable (hG : G.IsAcyclic) (x : Pt Val) :
    jointVar hG (constTable G Val x) = x :=
  jointVar_eq_of_diag hG fun _ => rfl

/-! ### Private helpers -/

omit [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
/-- Every parent configuration is realized by a joint value. -/
private lemma exists_parentConfig (x₀ : Pt Val) (v : V) (y : ParentVals G Val v) :
    ∃ x : Pt Val, parentConfig G Val x v = y := by
  classical
  refine ⟨fun u => if h : u ∈ G.parents v then y ⟨u, h⟩ else x₀ u, ?_⟩
  funext u
  show (if h : (u : V) ∈ G.parents v then y ⟨u, h⟩ else x₀ u) = y u
  rw [dif_pos u.2]

omit [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
/-- Every parent configuration is realized by a joint value with a prescribed value at the
node itself (the node is not one of its own parents). -/
private lemma exists_parentConfig_val (hG : G.IsAcyclic) (x₀ : Pt Val) (v : V)
    (y : ParentVals G Val v) (a : Val v) :
    ∃ x : Pt Val, parentConfig G Val x v = y ∧ x v = a := by
  classical
  obtain ⟨x, hx⟩ := exists_parentConfig x₀ v y
  refine ⟨Function.update x v a, ?_, Function.update_self v a x⟩
  funext u
  have hu : (u : V) ≠ v := by
    intro h
    have hmem := u.2
    rw [h] at hmem
    exact Digraph.notMem_parents_self hG v hmem
  show Function.update x v a (u : V) = y u
  rw [Function.update_of_ne hu]
  exact congrFun hx u

omit [DecidableEq V] [(v : V) → Fintype (Val v)] [(v : V) → DecidableEq (Val v)] in
/-- `X_v` depends only on the factors `I_u` for `u` an ancestor of `v` or `v` itself. -/
private lemma nodeVar_congr (hG : G.IsAcyclic) (ω ω' : Pt (bnFactor G Val)) (v : V) :
    (∀ i : bnIndex G Val, (i.1 = v ∨ G.IsAncestor i.1 v) → ω i = ω' i) →
      nodeVar hG v ω = nodeVar hG v ω' := by
  induction v using hG.wf.induction with
  | _ v ih =>
    intro h
    rw [nodeVar_apply, nodeVar_apply]
    have key : (fun u : ↥(G.parents v) => nodeVar hG (u : V) ω)
        = fun u : ↥(G.parents v) => nodeVar hG (u : V) ω' := by
      funext u
      have hadj : G.Adj (u : V) v := (Digraph.mem_parents G).mp u.2
      refine ih (u : V) hadj (fun i hi => h i ?_)
      rcases hi with hi | hi
      · exact Or.inr (by rw [hi]; exact Relation.TransGen.single hadj)
      · exact Or.inr (hi.trans (Relation.TransGen.single hadj))
    rw [key]
    exact h ⟨v, _⟩ (Or.inl rfl)

omit [(v : V) → Fintype (Val v)] in
/-- Changing a factor of `I_v` does not change the parent configuration seen at `v`. -/
private lemma parentConfig_jointVar_update (hG : G.IsAcyclic) (v : V)
    (ω : Pt (bnFactor G Val)) (i : bnIndex G Val) (hi : i.1 = v) (b : bnFactor G Val i) :
    parentConfig G Val (jointVar hG (Function.update ω i b)) v
      = parentConfig G Val (jointVar hG ω) v := by
  classical
  funext u
  show nodeVar hG (u : V) (Function.update ω i b) = nodeVar hG (u : V) ω
  refine nodeVar_congr hG _ _ (u : V) fun j hj => ?_
  have hne : j ≠ i := by
    intro hji
    rw [hji, hi] at hj
    exact hG.not_ancestor_of_adj ((Digraph.mem_parents G).mp u.2) hj
  exact Function.update_of_ne hne _ _

/-! ## Factorization over a DAG (`dd:cpd`) -/

/-- A family of conditional probability distributions: for every node `v` and parent
configuration `x_pa(v)`, a distribution `P(· | x_pa(v))` on `Val_v`. -/
abbrev CPD : Type max u w := ∀ v : V, ParentVals G Val v → Distr (Val v)

variable (G Val) in
/-- **`P` factorizes over `G`** (§5.2, eq. (2)): `P(x) = ∏_v P(x_v | x_pa(v))` for all
`x ∈ Val`, where the factors `P(· | x_pa(v))` are conditional probability distributions
— one per node and parent configuration — as in Koller–Friedman's definition, which the
paper follows (`dd:cpd`; the CPD at a parent configuration of probability zero is not
determined by `P`, see `KNOWLEDGE.md`). -/
def FactorizesOverDAG (P : Distr (Pt Val)) : Prop :=
  ∃ φ : CPD (G := G) (Val := Val), ∀ x : Pt Val,
    P.mass x = ∏ v, (φ v (parentConfig G Val x v)).mass (x v)

variable (G Val) in
/-- The set `Δ^*(G)` of distributions on `Val` that factorize over `G` (Lemma 5.3). -/
def dagFactorizing : Set (Distr (Pt Val)) := {P | FactorizesOverDAG G Val P}

omit [∀ v, DecidableEq (Val v)] in
lemma mem_dagFactorizing {P : Distr (Pt Val)} :
    P ∈ dagFactorizing G Val ↔ FactorizesOverDAG G Val P := Iff.rfl

/-- The conditional probabilities `P(x_v | x_pa(v))` of a strictly positive `P` as a CPD
family — the factors the paper's eq. (2) and Lemma 5.3 write. -/
noncomputable def condCPD (P : Distr (Pt Val)) (hP : P.StrictlyPositive) : CPD (G := G) (Val := Val) :=
  fun v y =>
    { mass := fun a => P.condProb {x | x v = a} {x | parentConfig G Val x v = y}
      nonneg := fun _ => by
        unfold Distr.condProb
        exact div_nonneg (P.prob_nonneg _) (P.prob_nonneg _)
      sum_eq_one := by
        classical
        obtain ⟨x₀⟩ := P.nonempty_carrier
        obtain ⟨x, hx⟩ := exists_parentConfig x₀ v y
        have hCpos : 0 < P.prob {x | parentConfig G Val x v = y} := by
          rw [P.prob_pos_iff]
          exact ⟨x, hx, hP x⟩
        have hsum : ∑ a : Val v, P.prob ({x | x v = a} ∩ {x | parentConfig G Val x v = y})
            = P.prob {x | parentConfig G Val x v = y} := by
          simp only [Distr.prob]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          have hpt : ∀ a : Val v,
              ({x' : Pt Val | x' v = a} ∩ {x' | parentConfig G Val x' v = y}).indicator
                  P.mass x
                = if x v = a then
                    ({x' : Pt Val | parentConfig G Val x' v = y}).indicator P.mass x else 0 := by
            intro a
            by_cases h1 : x v = a <;>
              by_cases h2 : x ∈ ({x' : Pt Val | parentConfig G Val x' v = y} : Set (Pt Val)) <;>
                simp [h1, h2]
          rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_ite_eq]
          simp
        simp only [Distr.condProb, div_eq_mul_inv, ← Finset.sum_mul, hsum]
        exact mul_inv_cancel₀ hCpos.ne' }

/-! ## Lemma B.2 and the map `τ` (Lemma 5.3) -/

/-- **`P^Ω(X = x) = ∏_v P^Ω(U_{(v, x_pa(v))} = x_v)`** for `P^Ω` factorizing over `Ω^G`.

Paper node: Lemma B.2 (§B.2). -/
theorem prob_jointVar_fiber (hG : G.IsAcyclic) {PΩ : Distr (Pt (bnFactor G Val))}
    (hP : Factorizes PΩ) (x : Pt Val) :
    PΩ.prob (fiber (jointVar hG) x) =
      ∏ v, (PΩ.margAt ⟨v, parentConfig G Val x v⟩).mass (x v) := by
  classical
  have hPΩ : PΩ = Distr.prod (fun i => PΩ.margAt i) := hP.eq_prod_margAt
  set κ : V → bnIndex G Val := fun v => ⟨v, parentConfig G Val x v⟩ with hκ
  have hinj : Set.InjOn κ (Finset.univ : Finset V) := fun a _ b _ hab => congrArg Sigma.fst hab
  have hset : fiber (jointVar hG) x
      = {ω : Pt (bnFactor G Val) | ∀ i ∈ Finset.image κ Finset.univ, ω i = constTable G Val x i} := by
    ext ω
    show jointVar hG ω = x ↔ _
    rw [jointVar_eq_iff hG ω x]
    simp only [Set.mem_setOf_eq, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro h i ⟨v, rfl⟩
      exact h v
    · intro h v
      exact h (κ v) ⟨v, rfl⟩
  calc PΩ.prob (fiber (jointVar hG) x)
      = (Distr.prod (fun i => PΩ.margAt i)).prob
          {ω : Pt (bnFactor G Val) |
            ∀ i ∈ Finset.image κ Finset.univ, ω i = constTable G Val x i} := by
        rw [hset]; conv_lhs => rw [hPΩ]
    _ = ∏ i ∈ Finset.image κ Finset.univ, (PΩ.margAt i).mass (constTable G Val x i) :=
        Distr.prob_prod_agree_on _ _ _
    _ = ∏ v, (PΩ.margAt (κ v)).mass (constTable G Val x (κ v)) := Finset.prod_image hinj
    _ = ∏ v, (PΩ.margAt ⟨v, parentConfig G Val x v⟩).mass (x v) := rfl

/-- The map `τ : Δ^⊗(Ω^G) → Δ^*(G)`, `τ(P^Ω)(x) = P^Ω(X = x)` (Lemma 5.3). -/
noncomputable def tau (hG : G.IsAcyclic) (PΩ : Distr (Pt (bnFactor G Val))) : Distr (Pt Val) :=
  PΩ.map (jointVar hG)

lemma tau_mass (hG : G.IsAcyclic) (PΩ : Distr (Pt (bnFactor G Val))) (x : Pt Val) :
    (tau hG PΩ).mass x = PΩ.prob (fiber (jointVar hG) x) := rfl

/-- The paper's `τ⁻¹`, from a CPD family: `τ⁻¹(P)(ω) = ∏_{(v, x_pa(v)) ∈ I} P(ω_{v,x_pa(v)} |
x_pa(v))`, i.e. the product over `I` of the CPDs. -/
noncomputable def tauInv (φ : CPD (G := G) (Val := Val)) : Distr (Pt (bnFactor G Val)) :=
  Distr.prod fun i => φ i.1 i.2

/-- **`τ⁻¹` lands in `Δ^⊗(Ω^G)`** (Lemma 5.3, first claim for `τ⁻¹`): the distribution
`τ⁻¹(φ)` built from a CPD family is a product over `I`, hence factorizes over `Ω^G`.

Paper node: Lemma 5.3 (§5.2). -/
theorem factorizes_tauInv (φ : CPD (G := G) (Val := Val)) : Factorizes (tauInv φ) :=
  factorizes_prod _

/-- **`τ` maps `Δ^⊗(Ω^G)` into `Δ^*(G)`** (Lemma 5.3, first claim).

Paper node: Lemma 5.3 (§5.2). -/
theorem factorizesOverDAG_tau (hG : G.IsAcyclic) {PΩ : Distr (Pt (bnFactor G Val))}
    (hP : Factorizes PΩ) : FactorizesOverDAG G Val (tau hG PΩ) :=
  ⟨fun v y => PΩ.margAt ⟨v, y⟩, fun x => by
    rw [tau_mass]; exact prob_jointVar_fiber hG hP x⟩

/-- **`τ⁻¹` is a right inverse of `τ`**: for `P ∈ Δ^*(G)` with CPD family `φ`,
`τ(τ⁻¹(P)) = P` (Lemma 5.3, surjectivity).

Paper node: Lemma 5.3 (§5.2). -/
theorem tau_tauInv (hG : G.IsAcyclic) {P : Distr (Pt Val)} (φ : CPD (G := G) (Val := Val))
    (hφ : ∀ x : Pt Val, P.mass x = ∏ v, (φ v (parentConfig G Val x v)).mass (x v)) :
    tau hG (tauInv φ) = P := by
  ext x
  rw [tau_mass, prob_jointVar_fiber hG (factorizes_tauInv φ) x, hφ x]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [show (tauInv φ).margAt ⟨v, parentConfig G Val x v⟩
      = φ v (parentConfig G Val x v) from Distr.margAt_prod _ _]

/-- `τ` preserves strict positivity. -/
lemma tau_strictlyPositive (hG : G.IsAcyclic) {PΩ : Distr (Pt (bnFactor G Val))}
    (hpos : PΩ.StrictlyPositive) : (tau hG PΩ).StrictlyPositive := by
  intro x
  rw [tau_mass, PΩ.prob_pos_iff]
  exact ⟨constTable G Val x, jointVar_constTable hG x, hpos _⟩

/-- The conditional probabilities of `τ(P^Ω)` are the marginals of `P^Ω` on the
corresponding factors — the computation behind the inverse formula of Lemma 5.3. -/
private lemma condProb_tau_eq (hG : G.IsAcyclic) {PΩ : Distr (Pt (bnFactor G Val))}
    (hP : Factorizes PΩ) (hpos : PΩ.StrictlyPositive) (v : V) (y : ParentVals G Val v)
    (a : Val v) :
    (tau hG PΩ).condProb {x : Pt Val | x v = a} {x | parentConfig G Val x v = y}
      = (PΩ.margAt ⟨v, y⟩).mass a := by
  classical
  have hPΩ : PΩ = Distr.prod (fun i => PΩ.margAt i) := hP.eq_prod_margAt
  set E : Set (Pt (bnFactor G Val)) :=
    {ω | parentConfig G Val (jointVar hG ω) v = y} with hEdef
  have hcoord : ∀ ω ∈ E, nodeVar hG v ω = ω ⟨v, y⟩ := fun ω hω =>
    nodeVar_eq_coord hG v ω y hω
  have hAE : jointVar hG ⁻¹' ({x : Pt Val | x v = a} ∩ {x | parentConfig G Val x v = y})
      = E ∩ {ω | ω ⟨v, y⟩ = a} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [← hcoord ω h2]
      exact h1
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      rw [show jointVar hG ω v = nodeVar hG v ω from rfl, hcoord ω h2]
      exact h1
  have hinv : ∀ (ω : Pt (bnFactor G Val)) (b : bnFactor G Val ⟨v, y⟩), ω ∈ E →
      Function.update ω ⟨v, y⟩ b ∈ E := by
    intro ω b hω
    show parentConfig G Val (jointVar hG (Function.update ω ⟨v, y⟩ b)) v = y
    rw [parentConfig_jointVar_update hG v ω ⟨v, y⟩ rfl b]
    exact hω
  have hEpos : 0 < PΩ.prob E := by
    obtain ⟨x₀⟩ := (tau hG PΩ).nonempty_carrier
    obtain ⟨x, hx⟩ := exists_parentConfig x₀ v y
    rw [PΩ.prob_pos_iff]
    refine ⟨constTable G Val x, ?_, hpos _⟩
    show parentConfig G Val (jointVar hG (constTable G Val x)) v = y
    rw [jointVar_constTable hG x]
    exact hx
  have h1 : (tau hG PΩ).prob ({x : Pt Val | x v = a} ∩ {x | parentConfig G Val x v = y})
      = PΩ.prob (E ∩ {ω | ω ⟨v, y⟩ = a}) := by
    show (PΩ.map (jointVar hG)).prob _ = _
    rw [Distr.map_prob, hAE]
  have h2 : (tau hG PΩ).prob {x : Pt Val | parentConfig G Val x v = y} = PΩ.prob E := by
    show (PΩ.map (jointVar hG)).prob _ = _
    rw [Distr.map_prob]
    rfl
  have hkey : (Distr.prod (fun i => PΩ.margAt i)).prob (E ∩ {ω | ω ⟨v, y⟩ = a})
      = (PΩ.margAt ⟨v, y⟩).mass a * (Distr.prod (fun i => PΩ.margAt i)).prob E :=
    Distr.prob_prod_inter_bg (fun i => PΩ.margAt i) ⟨v, y⟩ a hinv
  rw [← hPΩ] at hkey
  rw [Distr.condProb, h1, h2, hkey, mul_div_assoc, div_self hEpos.ne', mul_one]

/-- `τ` on the strictly positive members of `Δ^⊗(Ω^G)`, landing in the strictly positive
members of `Δ^*(G)`. -/
noncomputable def tauPos (hG : G.IsAcyclic) :
    {PΩ : Distr (Pt (bnFactor G Val)) // PΩ ∈ factorizing (bnFactor G Val) ∧ PΩ.StrictlyPositive} →
      {P : Distr (Pt Val) // P ∈ dagFactorizing G Val ∧ P.StrictlyPositive} :=
  fun PΩ => ⟨tau hG PΩ.1, factorizesOverDAG_tau hG PΩ.2.1, tau_strictlyPositive hG PΩ.2.2⟩

/-- **The inverse formula of Lemma 5.3**: for strictly positive factorizing `P^Ω`,
`τ⁻¹(τ(P^Ω))(ω) = ∏_{(v, x_pa(v)) ∈ I} τ(P^Ω)(ω_{v,x_pa(v)} | x_pa(v)) = P^Ω(ω)`, with the
factors the genuine conditional probabilities of `τ(P^Ω)`.

Paper node: Lemma 5.3 (§5.2). -/
theorem tauInv_condCPD_tau (hG : G.IsAcyclic) {PΩ : Distr (Pt (bnFactor G Val))}
    (hP : Factorizes PΩ) (hpos : PΩ.StrictlyPositive) :
    tauInv (condCPD (tau hG PΩ) (tau_strictlyPositive hG hpos)) = PΩ := by
  have hφ : (fun i : bnIndex G Val =>
      condCPD (tau hG PΩ) (tau_strictlyPositive hG hpos) i.1 i.2)
      = fun i => PΩ.margAt i := by
    funext i
    ext a
    exact condProb_tau_eq hG hP hpos i.1 i.2 a
  rw [show tauInv (condCPD (tau hG PΩ) (tau_strictlyPositive hG hpos))
      = Distr.prod (fun i : bnIndex G Val =>
          condCPD (tau hG PΩ) (tau_strictlyPositive hG hpos) i.1 i.2) from rfl, hφ]
  exact hP.eq_prod_margAt.symm

private lemma tauInv_condCPD_congr {P Q : Distr (Pt Val)} (hP : P.StrictlyPositive)
    (hQ : Q.StrictlyPositive) (h : P = Q) :
    tauInv (condCPD (G := G) P hP) = tauInv (condCPD (G := G) Q hQ) := by
  subst h; rfl

/-- **`τ` is a bijection between the strictly positive members of `Δ^⊗(Ω^G)` and of
`Δ^*(G)`** (Lemma 5.3, bijectivity — in its true form).

The paper claims `τ` is bijective on all of `Δ^⊗(Ω^G)`, which fails: two factorizing
`P^Ω` that differ only in a factor `(v, y)` whose parent configuration `y` has
probability zero under `X_pa(v)` have the same `τ`-image (a chain `a → b` with
`P^Ω(X_a = 0) = 1` and any two distributions on the `(b, 1)` factor).  The paper's own
proof of `τ⁻¹ ∘ τ = id` divides by `P^Ω(X_pa(v) = x_pa(v))`, which is exactly the
positivity assumed here.  See `notes/paper-errata.md`.

Paper node: Lemma 5.3 (§5.2). -/
theorem tauPos_bijective (hG : G.IsAcyclic) : Function.Bijective (tauPos (G := G) (Val := Val) hG) := by
  constructor
  · rintro ⟨P₁, hf₁, hp₁⟩ ⟨P₂, hf₂, hp₂⟩ h
    have hEq : tau hG P₁ = tau hG P₂ := congrArg Subtype.val h
    refine Subtype.ext (show P₁ = P₂ from ?_)
    rw [← tauInv_condCPD_tau hG hf₁ hp₁, ← tauInv_condCPD_tau hG hf₂ hp₂]
    exact tauInv_condCPD_congr _ _ hEq
  · rintro ⟨P, hfac, hpos⟩
    obtain ⟨φ, hφ⟩ := hfac
    obtain ⟨x₀⟩ := P.nonempty_carrier
    have hφpos : ∀ (v : V) (y : ParentVals G Val v) (a : Val v), 0 < (φ v y).mass a := by
      intro v y a
      obtain ⟨x, hx1, hx2⟩ := exists_parentConfig_val hG x₀ v y a
      rcases lt_or_eq_of_le ((φ v y).nonneg a) with hlt | heq
      · exact hlt
      · exfalso
        refine absurd (hφ x) (ne_of_gt ?_)
        rw [Finset.prod_eq_zero (Finset.mem_univ v)
          (show (φ v (parentConfig G Val x v)).mass (x v) = 0 by rw [hx1, hx2, ← heq])]
        exact hpos x
    have hprodpos : (tauInv (G := G) φ).StrictlyPositive := by
      intro ω
      rw [show (tauInv (G := G) φ).mass ω = ∏ i, (φ i.1 i.2).mass (ω i) from rfl]
      exact Finset.prod_pos fun i _ => hφpos i.1 i.2 (ω i)
    exact ⟨⟨tauInv φ, factorizes_tauInv φ, hprodpos⟩, Subtype.ext (tau_tauInv hG φ hφ)⟩

/-! ## Proposition 5.4: the factorization property -/

/-- **Factorization property.** `P` factorizes over `G` iff `M^G = (Ω^G, X)` is a factored
space model of `P`.

Paper node: Proposition 5.4 (§5.2). -/
theorem factorizesOverDAG_iff_isFactoredSpaceModel (hG : G.IsAcyclic) (P : Distr (Pt Val)) :
    FactorizesOverDAG G Val P ↔ IsFactoredSpaceModel (jointVar hG) P := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨tauInv φ, factorizes_tauInv φ, fun o => ?_⟩
    rw [← tau_mass hG (tauInv φ) o, tau_tauInv hG φ hφ]
  · rintro ⟨PΩ, hfac, hprob⟩
    have hEq : tau hG PΩ = P := by
      ext o
      rw [tau_mass]
      exact hprob o
    rw [← hEq]
    exact factorizesOverDAG_tau hG hfac

end Construction

end FactoredSpaces
