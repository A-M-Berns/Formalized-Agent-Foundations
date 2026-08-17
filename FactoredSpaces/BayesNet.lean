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
(`dd:cpd`), the map `τ` (Lemma 5.3), Lemma B.2, the factorization property
(Proposition 5.4) and the ancestor relation (Proposition 5.6).
-/

universe u

/-! ## DAGs (generic vocabulary, in the root `Digraph` namespace) -/

namespace Digraph

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

end Digraph

namespace FactoredSpaces

/-! ## Auxiliary facts about distributions and histories

Generic statements used below that are not part of the paper's §5.2 vocabulary; they are
private to this file (`Dist`-level product identities and one reformulation of `history`).
-/

section Aux

universe uI vΩ

variable {S : Type uI} [Fintype S]

/-- A finite type carrying a distribution is nonempty (its masses sum to `1`). -/
private lemma dist_nonempty (P : Dist S) : Nonempty S := by
  by_contra hS
  rw [not_nonempty_iff] at hS
  have h := P.sum_eq_one
  rw [Finset.univ_eq_empty, Finset.sum_empty] at h
  exact zero_ne_one h

variable {I : Type uI} [DecidableEq I] [Fintype I] {Ω : I → Type vΩ} [∀ i, Fintype (Ω i)]

/-- Under a product distribution, the probability that `ω` agrees with a fixed point `f`
on a finite set `S` of coordinates is the product of the corresponding masses. -/
private lemma prob_prod_agree_on (p : ∀ i, Dist (Ω i)) (S : Finset I) (f : Pt Ω) :
    (Dist.prod p).prob {ω | ∀ i ∈ S, ω i = f i} = ∏ i ∈ S, (p i).mass (f i) := by
  classical
  have hset : Finset.univ.filter (fun ω : Pt Ω => ω ∈ {ω : Pt Ω | ∀ i ∈ S, ω i = f i})
      = Fintype.piFinset (fun j => if j ∈ S then ({f j} : Finset (Ω j)) else Finset.univ) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases hj : j ∈ S
      · simp [hj, h j hj]
      · simp [hj]
    · intro h j hj
      have := h j
      simpa [hj] using this
  rw [Dist.prob_eq_sum_filter, hset]
  simp only [Dist.prod_mass]
  rw [← Finset.prod_univ_sum]
  have hsum : ∀ j : I, (∑ b ∈ (if j ∈ S then ({f j} : Finset (Ω j)) else Finset.univ),
      (p j).mass b) = if j ∈ S then (p j).mass (f j) else 1 := by
    intro j
    by_cases hj : j ∈ S
    · simp [hj]
    · simp [hj, (p j).sum_eq_one]
  simp only [hsum]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- Under a product distribution, an event invariant under changing the `i`-th coordinate
is independent of that coordinate. -/
private lemma prob_prod_inter_bg (p : ∀ i, Dist (Ω i)) (i : I) (a : Ω i) {E : Set (Pt Ω)}
    (hE : ∀ (ω : Pt Ω) (b : Ω i), ω ∈ E → Function.update ω i b ∈ E) :
    (Dist.prod p).prob (E ∩ {ω | ω i = a}) = (p i).mass a * (Dist.prod p).prob E := by
  classical
  have hupd : ∀ (ω : Pt Ω) (b : Ω i),
      ∏ j ∈ Finset.univ.erase i, (p j).mass (Function.update ω i b j)
        = ∏ j ∈ Finset.univ.erase i, (p j).mass (ω j) := fun ω b =>
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj) b ω]
  have hmass : ∀ ω : Pt Ω, (Dist.prod p).mass ω
      = (p i).mass (ω i) * ∏ j ∈ Finset.univ.erase i, (p j).mass (ω j) := fun ω =>
    (Finset.mul_prod_erase Finset.univ (fun j => (p j).mass (ω j)) (Finset.mem_univ i)).symm
  have hmem : ∀ (ω : Pt Ω) (b : Ω i), Function.update ω i b ∈ E ↔ ω ∈ E := by
    intro ω b
    refine ⟨fun h => ?_, fun h => hE ω b h⟩
    have := hE _ (ω i) h
    rwa [Function.update_idem, Function.update_eq_self] at this
  have hGsum : ∀ b : Ω i,
      (∑ ω ∈ Finset.univ.filter (fun ω : Pt Ω => ω ∈ E ∧ ω i = b),
        ∏ j ∈ Finset.univ.erase i, (p j).mass (ω j))
      = ∑ ω ∈ Finset.univ.filter (fun ω : Pt Ω => ω ∈ E ∧ ω i = a),
        ∏ j ∈ Finset.univ.erase i, (p j).mass (ω j) := by
    intro b
    refine Finset.sum_nbij' (fun ω => Function.update ω i a) (fun ω => Function.update ω i b)
      ?_ ?_ ?_ ?_ ?_
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact ⟨(hmem ω a).mpr hω.1, Function.update_self _ _ _⟩
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact ⟨(hmem ω b).mpr hω.1, Function.update_self _ _ _⟩
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      rw [Function.update_idem, ← hω.2, Function.update_eq_self]
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      rw [Function.update_idem, ← hω.2, Function.update_eq_self]
    · intro ω _
      exact (hupd ω a).symm
  have hkey : ∀ b : Ω i,
      (∑ ω ∈ Finset.univ.filter (fun ω : Pt Ω => ω ∈ E ∧ ω i = b), (Dist.prod p).mass ω)
      = (p i).mass b * ∑ ω ∈ Finset.univ.filter (fun ω : Pt Ω => ω ∈ E ∧ ω i = a),
          ∏ j ∈ Finset.univ.erase i, (p j).mass (ω j) := by
    intro b
    rw [← hGsum b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω hω => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    rw [hmass ω, hω.2]
  have hLHS : (Dist.prod p).prob (E ∩ {ω | ω i = a})
      = ∑ ω ∈ Finset.univ.filter (fun ω : Pt Ω => ω ∈ E ∧ ω i = a), (Dist.prod p).mass ω := by
    rw [Dist.prob_eq_sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ω
    simp [Set.mem_inter_iff]
  have hRHS : (Dist.prod p).prob E
      = ∑ b : Ω i, ∑ ω ∈ Finset.univ.filter (fun ω : Pt Ω => ω ∈ E ∧ ω i = b),
          (Dist.prod p).mass ω := by
    rw [Dist.prob_eq_sum_filter,
      ← Finset.sum_fiberwise (Finset.univ.filter (fun ω : Pt Ω => ω ∈ E)) (fun ω : Pt Ω => ω i)
        (Dist.prod p).mass]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    rw [Finset.filter_filter]
  rw [hLHS, hRHS, hkey a]
  simp only [hkey]
  rw [← Finset.sum_mul, (p i).sum_eq_one, one_mul]

variable {α : Type*}

/-- A factor lies in the (unconditional) history of `X` exactly when `X` is sensitive to
it: two points agreeing off `i` with different `X`-values exist.  (Both directions of
`exists_ne_of_mem_history`, which gives the weaker conclusion `a i ≠ b i`.) -/
private lemma mem_history_iff_exists_ne [Nonempty α] (X : Pt Ω → α) (i : I) :
    i ∈ history X (Set.univ : Set (Pt Ω)) ↔
      ∃ a b : Pt Ω, (∀ j, j ≠ i → a j = b j) ∧ X a ≠ X b := by
  classical
  constructor
  · intro hi
    by_contra hcon
    push Not at hcon
    have hgen : Generates (Finset.univ.erase i) X (Set.univ : Set (Pt Ω)) := by
      rw [generates_iff]
      refine ⟨disintegrates_univ_set _, fun a _ b _ hab => ?_⟩
      exact hcon a b fun j hj => hab j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    exact (Finset.mem_erase.mp (history_subset_of_generates hgen hi)).1 rfl
  · rintro ⟨a, b, hab, hne⟩
    by_contra hi
    have hsub : history X (Set.univ : Set (Pt Ω)) ⊆ Finset.univ.erase i := fun j hj =>
      Finset.mem_erase.mpr ⟨fun h => hi (h ▸ hj), Finset.mem_univ j⟩
    have hgen : Generates (Finset.univ.erase i) X (Set.univ : Set (Pt Ω)) :=
      (generates_iff_history_subset (disintegrates_univ_set _)).mpr hsub
    rw [generates_iff] at hgen
    exact hne (hgen.2 a (Set.mem_univ _) b (Set.mem_univ _) fun j hj =>
      hab j (Finset.mem_erase.mp hj).1)

end Aux

/-! ## The factored space of a DAG -/

section Construction

variable {V : Type u} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
  (Val : V → Type u) [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)]

/-- The paper's `Val_{pa(v)}`: assignments of values to the parents of `v`.  (`PtOn Val
(G.parents v)` — the joint value space `Val = ×_v Val_v` is itself the point type
`Pt Val`, so the §4 projection vocabulary applies to it.) -/
abbrev ParentVals (v : V) : Type u := PtOn Val (G.parents v)

/-- The parent configuration `x_pa(v)` of a joint value `x ∈ Val`. -/
def parentConfig (x : Pt Val) (v : V) : ParentVals G Val v := proj (G.parents v) x

/-- The index set `I = ⋃_{v∈V} I_v` with `I_v = {(v, x_pa(v)) | x_pa(v) ∈ Val_pa(v)}`. -/
abbrev bnIndex : Type u := Σ v : V, ParentVals G Val v

/-- The factors `Ω^G_{(v, x_pa(v))} = Val_v`; the factored space constructed from `G` is
`Pt (bnFactor G Val)`. -/
abbrev bnFactor : bnIndex G Val → Type u := fun i => Val i.1

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
the factored space model `M^G = (Ω^G, X)` constructed from `G` (§5.2). -/
noncomputable def jointVar (hG : G.IsAcyclic) : Pt (bnFactor G Val) → Pt Val :=
  fun ω v => nodeVar hG v ω

/-- The family `X_S = (X_v)_{v∈S}` for a set of nodes `S ⊆ V`. -/
noncomputable def nodesVar (hG : G.IsAcyclic) (S : Finset V) : Pt (bnFactor G Val) → PtOn Val S :=
  fun ω v => nodeVar hG v ω

omit [DecidableEq V] [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
lemma nodesVar_eq_proj_comp (hG : G.IsAcyclic) (S : Finset V) :
    nodesVar (Val := Val) hG S = proj S ∘ jointVar hG := rfl

/-! ### Reading off the node variables (private) -/

omit [DecidableEq V] in
/-- A vertex is not its own parent. -/
private lemma not_mem_parents_self (hG : G.IsAcyclic) (v : V) : v ∉ G.parents v := fun h =>
  hG v (Relation.TransGen.single ((Digraph.mem_parents G).mp h))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The head of an edge is neither the tail nor an ancestor of the tail. -/
private lemma not_ancestor_of_adj (hG : G.IsAcyclic) {u v : V} (h : G.Adj u v) :
    ¬ (v = u ∨ G.IsAncestor v u) := by
  rintro (rfl | hvu)
  · exact hG _ (Relation.TransGen.single h)
  · exact hG v (hvu.trans (Relation.TransGen.single h))

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
    exact not_mem_parents_self hG v hmem
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

omit [DecidableEq V] [(v : V) → Fintype (Val v)] [(v : V) → DecidableEq (Val v)] in
/-- The set identity behind Lemma B.2: `{X = x} = {ω | ∀ v, ω_{(v, x_pa(v))} = x_v}`. -/
private lemma jointVar_eq_iff (hG : G.IsAcyclic) (ω : Pt (bnFactor G Val)) (x : Pt Val) :
    jointVar hG ω = x ↔ ∀ v, ω ⟨v, parentConfig G Val x v⟩ = x v := by
  constructor
  · intro hj v
    have h1 : ∀ u, nodeVar hG u ω = x u := fun u => congrFun hj u
    have h2 : (fun u : ↥(G.parents v) => nodeVar hG (u : V) ω) = parentConfig G Val x v := by
      funext u; exact h1 u
    rw [← h2, ← nodeVar_apply hG v ω]
    exact h1 v
  · intro h
    funext v
    show nodeVar hG v ω = x v
    induction v using hG.wf.induction with
    | _ v ih =>
      rw [nodeVar_apply]
      have h2 : (fun u : ↥(G.parents v) => nodeVar hG (u : V) ω) = parentConfig G Val x v := by
        funext u
        exact ih (u : V) ((Digraph.mem_parents G).mp u.2)
      rw [h2]
      exact h v

omit [DecidableEq V] [(v : V) → Fintype (Val v)] [(v : V) → DecidableEq (Val v)] in
/-- If the parent configuration seen at `v` is `c`, then `X_v` reads off the factor
`(v, c)`. -/
private lemma nodeVar_eq_coord (hG : G.IsAcyclic) (v : V) (ω : Pt (bnFactor G Val))
    (c : ParentVals G Val v) (hc : parentConfig G Val (jointVar hG ω) v = c) :
    nodeVar hG v ω = ω ⟨v, c⟩ := by
  rw [nodeVar_apply, show (fun u : ↥(G.parents v) => nodeVar hG (u : V) ω) = c from hc]

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
    exact not_ancestor_of_adj hG ((Digraph.mem_parents G).mp u.2) hj
  exact Function.update_of_ne hne _ _

omit [(v : V) → Fintype (Val v)] in
/-- Overwriting the factor `(v, c)` that `X_v` reads sets the value of `X_v`. -/
private lemma nodeVar_update_eq (hG : G.IsAcyclic) (v : V) (ω : Pt (bnFactor G Val))
    (c : ParentVals G Val v) (hc : parentConfig G Val (jointVar hG ω) v = c) (b : Val v) :
    nodeVar hG v (Function.update ω ⟨v, c⟩ b) = b := by
  classical
  have h := parentConfig_jointVar_update hG v ω ⟨v, c⟩ rfl b
  rw [hc] at h
  rw [nodeVar_eq_coord hG v _ c h, Function.update_self]

variable (G Val) in
/-- The "constant table" `ω_x`, with every factor of `I_v` holding `x_v`; it satisfies
`X(ω_x) = x`. -/
private def constTable (x : Pt Val) : Pt (bnFactor G Val) := fun i => x i.1

omit [DecidableEq V] [(v : V) → Fintype (Val v)] [(v : V) → DecidableEq (Val v)] in
private lemma jointVar_constTable (hG : G.IsAcyclic) (x : Pt Val) :
    jointVar hG (constTable G Val x) = x :=
  (jointVar_eq_iff hG _ x).mpr fun _ => rfl

/-! ## Factorization over a DAG (`dd:cpd`) -/

/-- A family of conditional probability distributions: for every node `v` and parent
configuration `x_pa(v)`, a distribution `P(· | x_pa(v))` on `Val_v`. -/
abbrev CPD : Type u := ∀ v : V, ParentVals G Val v → Dist (Val v)

variable (G Val) in
/-- **`P` factorizes over `G`** (§5.2, eq. (4)): `P(x) = ∏_v P(x_v | x_pa(v))` for all
`x ∈ Val`, where the factors `P(· | x_pa(v))` are conditional probability distributions
— one per node and parent configuration — as in Koller–Friedman's definition, which the
paper follows (`dd:cpd`; the CPD at a parent configuration of probability zero is not
determined by `P`, see `KNOWLEDGE.md`). -/
def FactorizesOverDAG (P : Dist (Pt Val)) : Prop :=
  ∃ φ : CPD (G := G) (Val := Val), ∀ x : Pt Val,
    P.mass x = ∏ v, (φ v (parentConfig G Val x v)).mass (x v)

variable (G Val) in
/-- The set `Δ^*(G)` of distributions on `Val` that factorize over `G` (Lemma 5.3). -/
def dagFactorizing : Set (Dist (Pt Val)) := {P | FactorizesOverDAG G Val P}

/-- The conditional probabilities `P(x_v | x_pa(v))` of a strictly positive `P` as a CPD
family — the factors the paper's eq. (4) and Lemma 5.3 write. -/
noncomputable def condCPD (P : Dist (Pt Val)) (hP : P.StrictlyPositive) : CPD (G := G) (Val := Val) :=
  fun v y =>
    { mass := fun a => P.condProb {x | x v = a} {x | parentConfig G Val x v = y}
      nonneg := fun _ => by
        unfold Dist.condProb
        exact div_nonneg (P.prob_nonneg _) (P.prob_nonneg _)
      sum_eq_one := by
        classical
        obtain ⟨x₀⟩ := dist_nonempty P
        obtain ⟨x, hx⟩ := exists_parentConfig x₀ v y
        have hCpos : 0 < P.prob {x | parentConfig G Val x v = y} := by
          rw [P.prob_pos_iff]
          exact ⟨x, hx, hP x⟩
        have hsum : ∑ a : Val v, P.prob ({x | x v = a} ∩ {x | parentConfig G Val x v = y})
            = P.prob {x | parentConfig G Val x v = y} := by
          simp only [Dist.prob]
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
        simp only [Dist.condProb, div_eq_mul_inv, ← Finset.sum_mul, hsum]
        exact mul_inv_cancel₀ hCpos.ne' }

/-! ## Lemma B.2 and the map `τ` (Lemma 5.3) -/

/-- **`P^Ω(X = x) = ∏_v P^Ω(U_{(v, x_pa(v))} = x_v)`** for `P^Ω` factorizing over `Ω^G`.

Paper node: Lemma B.2 (§B.2). -/
theorem prob_jointVar_fiber (hG : G.IsAcyclic) {PΩ : Dist (Pt (bnFactor G Val))}
    (hP : Factorizes PΩ) (x : Pt Val) :
    PΩ.prob (fiber (jointVar hG) x) =
      ∏ v, (PΩ.margAt ⟨v, parentConfig G Val x v⟩).mass (x v) := by
  classical
  have hPΩ : PΩ = Dist.prod (fun i => PΩ.margAt i) := hP.eq_prod_margAt
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
      = (Dist.prod (fun i => PΩ.margAt i)).prob
          {ω : Pt (bnFactor G Val) |
            ∀ i ∈ Finset.image κ Finset.univ, ω i = constTable G Val x i} := by
        rw [hset]; conv_lhs => rw [hPΩ]
    _ = ∏ i ∈ Finset.image κ Finset.univ, (PΩ.margAt i).mass (constTable G Val x i) :=
        prob_prod_agree_on _ _ _
    _ = ∏ v, (PΩ.margAt (κ v)).mass (constTable G Val x (κ v)) := Finset.prod_image hinj
    _ = ∏ v, (PΩ.margAt ⟨v, parentConfig G Val x v⟩).mass (x v) := rfl

/-- The map `τ : Δ^F(Ω^G) → Δ^*(G)`, `τ(P^Ω)(x) = P^Ω(X = x)` (Lemma 5.3). -/
noncomputable def tau (hG : G.IsAcyclic) (PΩ : Dist (Pt (bnFactor G Val))) : Dist (Pt Val) :=
  PΩ.map (jointVar hG)

lemma tau_mass (hG : G.IsAcyclic) (PΩ : Dist (Pt (bnFactor G Val))) (x : Pt Val) :
    (tau hG PΩ).mass x = PΩ.prob (fiber (jointVar hG) x) := rfl

/-- The paper's `τ⁻¹`, from a CPD family: `τ⁻¹(P)(ω) = ∏_{(v, x_pa(v)) ∈ I} P(ω_{v,x_pa(v)} |
x_pa(v))`, i.e. the product over `I` of the CPDs. -/
noncomputable def tauInv (φ : CPD (G := G) (Val := Val)) : Dist (Pt (bnFactor G Val)) :=
  Dist.prod fun i => φ i.1 i.2

lemma factorizes_tauInv (φ : CPD (G := G) (Val := Val)) : Factorizes (tauInv φ) :=
  factorizes_prod _

/-- **`τ` maps `Δ^F(Ω^G)` into `Δ^*(G)`** (Lemma 5.3, first claim).

Paper node: Lemma 5.3 (§5.2). -/
theorem factorizesOverDAG_tau (hG : G.IsAcyclic) {PΩ : Dist (Pt (bnFactor G Val))}
    (hP : Factorizes PΩ) : FactorizesOverDAG G Val (tau hG PΩ) :=
  ⟨fun v y => PΩ.margAt ⟨v, y⟩, fun x => by
    rw [tau_mass]; exact prob_jointVar_fiber hG hP x⟩

/-- **`τ⁻¹` is a right inverse of `τ`**: for `P ∈ Δ^*(G)` with CPD family `φ`,
`τ(τ⁻¹(P)) = P` (Lemma 5.3, surjectivity).

Paper node: Lemma 5.3 (§5.2). -/
theorem tau_tauInv (hG : G.IsAcyclic) {P : Dist (Pt Val)} (φ : CPD (G := G) (Val := Val))
    (hφ : ∀ x : Pt Val, P.mass x = ∏ v, (φ v (parentConfig G Val x v)).mass (x v)) :
    tau hG (tauInv φ) = P := by
  ext x
  rw [tau_mass, prob_jointVar_fiber hG (factorizes_tauInv φ) x, hφ x]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [show (tauInv φ).margAt ⟨v, parentConfig G Val x v⟩
      = φ v (parentConfig G Val x v) from Dist.margAt_prod _ _]

/-- `τ` preserves strict positivity. -/
lemma tau_strictlyPositive (hG : G.IsAcyclic) {PΩ : Dist (Pt (bnFactor G Val))}
    (_hP : Factorizes PΩ) (hpos : PΩ.StrictlyPositive) : (tau hG PΩ).StrictlyPositive := by
  intro x
  rw [tau_mass, PΩ.prob_pos_iff]
  exact ⟨constTable G Val x, jointVar_constTable hG x, hpos _⟩

/-- `τ⁻¹` of the conditional probabilities of a strictly positive `P` is strictly positive.

Acyclicity is needed (and is implicit in the paper, which only ever considers DAGs): with
a self-loop at `v` the event `{X_v = a} ∩ {X_pa(v) = y}` is empty for `a ≠ y_v`, and the
corresponding conditional probability vanishes. -/
lemma tauInv_condCPD_strictlyPositive (hG : G.IsAcyclic) (P : Dist (Pt Val))
    (hpos : P.StrictlyPositive) :
    (tauInv (condCPD (G := G) P hpos)).StrictlyPositive := by
  classical
  intro ω
  obtain ⟨x₀⟩ := dist_nonempty P
  rw [show (tauInv (condCPD (G := G) P hpos)).mass ω
      = ∏ i, (condCPD (G := G) P hpos i.1 i.2).mass (ω i) from rfl]
  refine Finset.prod_pos fun i _ => ?_
  show 0 < P.condProb {x | x i.1 = ω i} {x | parentConfig G Val x i.1 = i.2}
  obtain ⟨x, hx1, hx2⟩ := exists_parentConfig_val hG x₀ i.1 i.2 (ω i)
  rw [Dist.condProb]
  refine div_pos ?_ ?_
  · rw [P.prob_pos_iff]
    exact ⟨x, ⟨hx2, hx1⟩, hpos x⟩
  · rw [P.prob_pos_iff]
    exact ⟨x, hx1, hpos x⟩

/-- The conditional probabilities of `τ(P^Ω)` are the marginals of `P^Ω` on the
corresponding factors — the computation behind the inverse formula of Lemma 5.3. -/
private lemma condProb_tau_eq (hG : G.IsAcyclic) {PΩ : Dist (Pt (bnFactor G Val))}
    (hP : Factorizes PΩ) (hpos : PΩ.StrictlyPositive) (v : V) (y : ParentVals G Val v)
    (a : Val v) :
    (tau hG PΩ).condProb {x : Pt Val | x v = a} {x | parentConfig G Val x v = y}
      = (PΩ.margAt ⟨v, y⟩).mass a := by
  classical
  have hPΩ : PΩ = Dist.prod (fun i => PΩ.margAt i) := hP.eq_prod_margAt
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
    obtain ⟨x₀⟩ := dist_nonempty (tau hG PΩ)
    obtain ⟨x, hx⟩ := exists_parentConfig x₀ v y
    rw [PΩ.prob_pos_iff]
    refine ⟨constTable G Val x, ?_, hpos _⟩
    show parentConfig G Val (jointVar hG (constTable G Val x)) v = y
    rw [jointVar_constTable hG x]
    exact hx
  have h1 : (tau hG PΩ).prob ({x : Pt Val | x v = a} ∩ {x | parentConfig G Val x v = y})
      = PΩ.prob (E ∩ {ω | ω ⟨v, y⟩ = a}) := by
    show (PΩ.map (jointVar hG)).prob _ = _
    rw [Dist.map_prob, hAE]
  have h2 : (tau hG PΩ).prob {x : Pt Val | parentConfig G Val x v = y} = PΩ.prob E := by
    show (PΩ.map (jointVar hG)).prob _ = _
    rw [Dist.map_prob]
    rfl
  have hkey : (Dist.prod (fun i => PΩ.margAt i)).prob (E ∩ {ω | ω ⟨v, y⟩ = a})
      = (PΩ.margAt ⟨v, y⟩).mass a * (Dist.prod (fun i => PΩ.margAt i)).prob E :=
    prob_prod_inter_bg (fun i => PΩ.margAt i) ⟨v, y⟩ a hinv
  rw [← hPΩ] at hkey
  rw [Dist.condProb, h1, h2, hkey, mul_div_assoc, div_self hEpos.ne', mul_one]

/-- `τ` on the strictly positive factorizing distributions, landing in the strictly positive
members of `Δ^*(G)`. -/
noncomputable def tauPos (hG : G.IsAcyclic) :
    {PΩ : Dist (Pt (bnFactor G Val)) // Factorizes PΩ ∧ PΩ.StrictlyPositive} →
      {P : Dist (Pt Val) // FactorizesOverDAG G Val P ∧ P.StrictlyPositive} :=
  fun PΩ => ⟨tau hG PΩ.1, factorizesOverDAG_tau hG PΩ.2.1, tau_strictlyPositive hG PΩ.2.1 PΩ.2.2⟩

/-- **The inverse formula of Lemma 5.3**: for strictly positive factorizing `P^Ω`,
`τ⁻¹(τ(P^Ω))(ω) = ∏_{(v, x_pa(v)) ∈ I} τ(P^Ω)(ω_{v,x_pa(v)} | x_pa(v)) = P^Ω(ω)`, with the
factors the genuine conditional probabilities of `τ(P^Ω)`.

Paper node: Lemma 5.3 (§5.2). -/
theorem tauInv_condCPD_tau (hG : G.IsAcyclic) {PΩ : Dist (Pt (bnFactor G Val))}
    (hP : Factorizes PΩ) (hpos : PΩ.StrictlyPositive) :
    tauInv (condCPD (tau hG PΩ) (tau_strictlyPositive hG hP hpos)) = PΩ := by
  have hφ : (fun i : bnIndex G Val =>
      condCPD (tau hG PΩ) (tau_strictlyPositive hG hP hpos) i.1 i.2)
      = fun i => PΩ.margAt i := by
    funext i
    ext a
    exact condProb_tau_eq hG hP hpos i.1 i.2 a
  rw [show tauInv (condCPD (tau hG PΩ) (tau_strictlyPositive hG hP hpos))
      = Dist.prod (fun i : bnIndex G Val =>
          condCPD (tau hG PΩ) (tau_strictlyPositive hG hP hpos) i.1 i.2) from rfl, hφ]
  exact hP.eq_prod_margAt.symm

private lemma tauInv_condCPD_congr {P Q : Dist (Pt Val)} (hP : P.StrictlyPositive)
    (hQ : Q.StrictlyPositive) (h : P = Q) :
    tauInv (condCPD (G := G) P hP) = tauInv (condCPD (G := G) Q hQ) := by
  subst h; rfl

/-- **`τ` is a bijection between the strictly positive members of `Δ^F(Ω^G)` and of
`Δ^*(G)`** (Lemma 5.3, bijectivity — in its true form).

The paper claims `τ` is bijective on all of `Δ^F(Ω^G)`, which fails: two factorizing
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
    obtain ⟨x₀⟩ := dist_nonempty P
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
theorem factorizesOverDAG_iff_isFactoredSpaceModel (hG : G.IsAcyclic) (P : Dist (Pt Val)) :
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

/-! ## Proposition 5.6: the ancestor relation -/

/-- The history of `X_v` is contained in `⋃_{u ∈ an(v) ∪ {v}} I_u` (`nodeVar_congr`
packaged through Lemma 4.7). -/
private lemma history_nodeVar_subset [∀ v, Nonempty (Val v)] (hG : G.IsAcyclic) (v : V)
    {i : bnIndex G Val}
    (hi : i ∈ history (nodeVar (Val := Val) hG v) (Set.univ : Set (Pt (bnFactor G Val)))) :
    i.1 = v ∨ G.IsAncestor i.1 v := by
  classical
  have hgen : Generates
      (Finset.univ.filter fun j : bnIndex G Val => j.1 = v ∨ G.IsAncestor j.1 v)
      (nodeVar (Val := Val) hG v) (Set.univ : Set (Pt (bnFactor G Val))) := by
    rw [generates_iff]
    refine ⟨disintegrates_univ_set _, fun a _ b _ hab => ?_⟩
    exact nodeVar_congr hG a b v fun j hj =>
      hab j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  exact (Finset.mem_filter.mp (history_subset_of_generates hgen hi)).2

/-- Every factor of `I_v` lies in the history of `X_v`. -/
private lemma mem_history_nodeVar_self [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic) (v : V)
    (c : ParentVals G Val v) :
    (⟨v, c⟩ : bnIndex G Val) ∈
      history (nodeVar (Val := Val) hG v) (Set.univ : Set (Pt (bnFactor G Val))) := by
  classical
  obtain ⟨x, hx⟩ := exists_parentConfig (fun u => Classical.arbitrary (Val u)) v c
  obtain ⟨s, hs⟩ := exists_ne (x v)
  have hc : parentConfig G Val (jointVar hG (constTable G Val x)) v = c := by
    rw [jointVar_constTable hG x]; exact hx
  refine (mem_history_iff_exists_ne _ _).mpr
    ⟨constTable G Val x, Function.update (constTable G Val x) ⟨v, c⟩ s, ?_, ?_⟩
  · intro j hj
    exact (Function.update_of_ne (β := bnFactor G Val) hj s _).symm
  · rw [nodeVar_update_eq hG v (constTable G Val x) c hc s,
      nodeVar_eq_coord hG v (constTable G Val x) c hc]
    exact fun h => hs h.symm

/-- The history of `X_w` is contained in that of `X_v` whenever `w → v`. -/
private lemma history_nodeVar_mono_adj [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic) {w v : V}
    (hadj : G.Adj w v) :
    history (nodeVar (Val := Val) hG w) (Set.univ : Set (Pt (bnFactor G Val)))
      ⊆ history (nodeVar (Val := Val) hG v) Set.univ := by
  classical
  intro i hi
  obtain ⟨ω, ω', hoff, hne⟩ := (mem_history_iff_exists_ne _ _).mp hi
  have hiv : i.1 ≠ v := by
    intro h
    exact not_ancestor_of_adj hG hadj (by rw [← h]; exact history_nodeVar_subset hG w hi)
  set d : ParentVals G Val v := parentConfig G Val (jointVar hG ω) v with hd
  set d' : ParentVals G Val v := parentConfig G Val (jointVar hG ω') v with hd'
  have hdd : d ≠ d' := fun h => hne (congrFun h ⟨w, (Digraph.mem_parents G).mpr hadj⟩)
  have hidx : (⟨v, d⟩ : bnIndex G Val) ≠ ⟨v, d'⟩ := by
    simp only [ne_eq, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact hdd
  have hiv1 : i ≠ (⟨v, d⟩ : bnIndex G Val) := fun h => hiv (by rw [h])
  have hiv2 : i ≠ (⟨v, d'⟩ : bnIndex G Val) := fun h => hiv (by rw [h])
  obtain ⟨α, β, hαβ⟩ := exists_pair_ne (Val v)
  set upd : Pt (bnFactor G Val) → Pt (bnFactor G Val) :=
    fun σ => Function.update (Function.update σ ⟨v, d⟩ α) ⟨v, d'⟩ β with hupd
  have hpc : ∀ σ : Pt (bnFactor G Val),
      parentConfig G Val (jointVar hG (upd σ)) v = parentConfig G Val (jointVar hG σ) v := by
    intro σ
    rw [hupd]
    rw [parentConfig_jointVar_update hG v _ ⟨v, d'⟩ rfl β,
      parentConfig_jointVar_update hG v σ ⟨v, d⟩ rfl α]
  have hval : ∀ (σ : Pt (bnFactor G Val)) (c : ParentVals G Val v),
      parentConfig G Val (jointVar hG σ) v = c → (upd σ) ⟨v, c⟩ = nodeVar hG v (upd σ) := by
    intro σ c hσ
    rw [nodeVar_eq_coord hG v (upd σ) c (by rw [hpc σ]; exact hσ)]
  refine (mem_history_iff_exists_ne _ _).mpr ⟨upd ω, upd ω', fun j hj => ?_, ?_⟩
  · by_cases h1 : j = (⟨v, d'⟩ : bnIndex G Val)
    · subst h1
      rw [hupd]
      simp only [Function.update_self]
    · by_cases h2 : j = (⟨v, d⟩ : bnIndex G Val)
      · subst h2
        rw [hupd]
        simp only [Function.update_of_ne h1, Function.update_self]
      · rw [hupd]
        simp only [Function.update_of_ne h1, Function.update_of_ne h2]
        exact hoff j hj
  · rw [← hval ω d hd.symm, ← hval ω' d' hd'.symm, hupd]
    simp only [Function.update_of_ne hidx, Function.update_self]
    exact hαβ

/-- The history of `X_u` is contained in that of `X_v` whenever `u` is an ancestor of `v`. -/
private lemma history_nodeVar_mono_ancestor [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic)
    {u v : V} (h : G.IsAncestor u v) :
    history (nodeVar (Val := Val) hG u) (Set.univ : Set (Pt (bnFactor G Val)))
      ⊆ history (nodeVar (Val := Val) hG v) Set.univ := by
  induction h with
  | single hadj => exact history_nodeVar_mono_adj hG hadj
  | tail _ hbc ih => exact ih.trans (history_nodeVar_mono_adj hG hbc)

/-- The history of a node variable: `H(X_v) = ⋃_{u ∈ an(v) ∪ {v}} I_u` (the identity the
proof of Proposition 5.6 starts from), stated as a membership criterion. -/
lemma mem_history_nodeVar_iff [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic) (v : V)
    (i : bnIndex G Val) :
    i ∈ history (nodeVar (Val := Val) hG v) (Set.univ : Set (Pt (bnFactor G Val))) ↔
      i.1 = v ∨ G.IsAncestor i.1 v := by
  constructor
  · exact fun hi => history_nodeVar_subset hG v hi
  · obtain ⟨u, c⟩ := i
    rintro (h | h)
    · subst h
      exact mem_history_nodeVar_self hG u c
    · exact history_nodeVar_mono_ancestor hG h (mem_history_nodeVar_self hG u c)

/-- **Ancestor relation.** For distinct nodes `v₁ ≠ v₂`: `v₁` is an ancestor of `v₂` in `G`
iff `X_{v₁} <_{Ω^G} X_{v₂}`.  Needs every `Val_v` to have at least two elements (the
paper's standing assumption on `Val`; with a one-element `Val_v` the node `v` carries no
randomness and drops out of every history).

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

end Construction

end FactoredSpaces
