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
  sorry

/-- The parents `pa(v) = {u | u → v}` of a vertex. -/
def parents [Fintype V] [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter fun u => G.Adj u v

lemma mem_parents [Fintype V] [DecidableRel G.Adj] {u v : V} : u ∈ G.parents v ↔ G.Adj u v := by
  simp [parents]

end Digraph

namespace FactoredSpaces

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

lemma nodeVar_apply (hG : G.IsAcyclic) (v : V) (ω : Pt (bnFactor G Val)) :
    nodeVar hG v ω = ω ⟨v, fun u => nodeVar hG u.1 ω⟩ := by
  sorry

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
      sum_eq_one := by sorry }

/-! ## Lemma B.2 and the map `τ` (Lemma 5.3) -/

/-- **`P^Ω(X = x) = ∏_v P^Ω(U_{(v, x_pa(v))} = x_v)`** for `P^Ω` factorizing over `Ω^G`.

Paper node: Lemma B.2 (§B.2). -/
theorem prob_jointVar_fiber (hG : G.IsAcyclic) {PΩ : Dist (Pt (bnFactor G Val))}
    (hP : Factorizes PΩ) (x : Pt Val) :
    PΩ.prob (fiber (jointVar hG) x) =
      ∏ v, (PΩ.margAt ⟨v, parentConfig G Val x v⟩).mass (x v) := by
  sorry

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
    (hP : Factorizes PΩ) : FactorizesOverDAG G Val (tau hG PΩ) := by
  sorry

/-- **`τ⁻¹` is a right inverse of `τ`**: for `P ∈ Δ^*(G)` with CPD family `φ`,
`τ(τ⁻¹(P)) = P` (Lemma 5.3, surjectivity).

Paper node: Lemma 5.3 (§5.2). -/
theorem tau_tauInv (hG : G.IsAcyclic) {P : Dist (Pt Val)} (φ : CPD (G := G) (Val := Val))
    (hφ : ∀ x : Pt Val, P.mass x = ∏ v, (φ v (parentConfig G Val x v)).mass (x v)) :
    tau hG (tauInv φ) = P := by
  sorry

/-- `τ` preserves strict positivity. -/
lemma tau_strictlyPositive (hG : G.IsAcyclic) {PΩ : Dist (Pt (bnFactor G Val))}
    (hP : Factorizes PΩ) (hpos : PΩ.StrictlyPositive) : (tau hG PΩ).StrictlyPositive := by
  sorry

/-- `τ⁻¹` of the conditional probabilities of a strictly positive `P` is strictly positive. -/
lemma tauInv_condCPD_strictlyPositive (P : Dist (Pt Val)) (hpos : P.StrictlyPositive) :
    (tauInv (condCPD (G := G) P hpos)).StrictlyPositive := by
  sorry

/-- `τ` on the strictly positive factorizing distributions, landing in the strictly positive
members of `Δ^*(G)`. -/
noncomputable def tauPos (hG : G.IsAcyclic) :
    {PΩ : Dist (Pt (bnFactor G Val)) // Factorizes PΩ ∧ PΩ.StrictlyPositive} →
      {P : Dist (Pt Val) // FactorizesOverDAG G Val P ∧ P.StrictlyPositive} :=
  fun PΩ => ⟨tau hG PΩ.1, factorizesOverDAG_tau hG PΩ.2.1, tau_strictlyPositive hG PΩ.2.1 PΩ.2.2⟩

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
  sorry

/-- **The inverse formula of Lemma 5.3**: for strictly positive factorizing `P^Ω`,
`τ⁻¹(τ(P^Ω))(ω) = ∏_{(v, x_pa(v)) ∈ I} τ(P^Ω)(ω_{v,x_pa(v)} | x_pa(v)) = P^Ω(ω)`, with the
factors the genuine conditional probabilities of `τ(P^Ω)`.

Paper node: Lemma 5.3 (§5.2). -/
theorem tauInv_condCPD_tau (hG : G.IsAcyclic) {PΩ : Dist (Pt (bnFactor G Val))}
    (hP : Factorizes PΩ) (hpos : PΩ.StrictlyPositive) :
    tauInv (condCPD (tau hG PΩ) (tau_strictlyPositive hG hP hpos)) = PΩ := by
  sorry

/-! ## Proposition 5.4: the factorization property -/

/-- **Factorization property.** `P` factorizes over `G` iff `M^G = (Ω^G, X)` is a factored
space model of `P`.

Paper node: Proposition 5.4 (§5.2). -/
theorem factorizesOverDAG_iff_isFactoredSpaceModel (hG : G.IsAcyclic) (P : Dist (Pt Val)) :
    FactorizesOverDAG G Val P ↔ IsFactoredSpaceModel (jointVar hG) P := by
  sorry

/-! ## Proposition 5.6: the ancestor relation -/

/-- The history of a node variable: `H(X_v) = ⋃_{u ∈ an(v) ∪ {v}} I_u` (the identity the
proof of Proposition 5.6 starts from), stated as a membership criterion. -/
lemma mem_history_nodeVar_iff [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic) (v : V)
    (i : bnIndex G Val) :
    i ∈ history (nodeVar (Val := Val) hG v) (Set.univ : Set (Pt (bnFactor G Val))) ↔
      i.1 = v ∨ G.IsAncestor i.1 v := by
  sorry

/-- **Ancestor relation.** For distinct nodes `v₁ ≠ v₂`: `v₁` is an ancestor of `v₂` in `G`
iff `X_{v₁} <_{Ω^G} X_{v₂}`.  Needs every `Val_v` to have at least two elements (the
paper's standing assumption on `Val`; with a one-element `Val_v` the node `v` carries no
randomness and drops out of every history).

Paper node: Proposition 5.6 (§5.2). -/
theorem isAncestor_iff_strictlyBefore [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic)
    {v₁ v₂ : V} (hne : v₁ ≠ v₂) :
    G.IsAncestor v₁ v₂ ↔ StrictlyBefore (nodeVar (Val := Val) hG v₁) (nodeVar hG v₂) := by
  sorry

end Construction

end FactoredSpaces
