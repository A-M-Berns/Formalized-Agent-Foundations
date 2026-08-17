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

Every point of `Ω^G` constructed here — for the relevance half of the determination
lemma and for the block-connectivity lemma alike — is one table, `propTable`, modified at
one or two indices by `Function.update`: node `q` returns the "good" value `x q` unless
`q` lies in a designated set `D` of unblocked descendants and a live parent of `q`
deviates from `x`, in which case it returns `bad q ≠ x q`.  Its two evaluation principles
are `nodeVar_eq_of_diag` (all-good: `X(ω) = x`) and `nodeVar_ne_of_prop` (badness
propagates along `D` from a source).  Keeping the dependent index `(v, y : Val_pa(v))`
out of every rewrite is what `table_congr` is for.
-/

universe u w

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
lemma mem_unblockedAnc_iff {Z : Finset V} {u v : V} :
    u ∈ G.unblockedAnc Z v ↔
      Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ Z) u v := Iff.rfl

omit [DecidableEq V] in
lemma mem_unblockedAnc_self (Z : Finset V) (v : V) : v ∈ G.unblockedAnc Z v :=
  Relation.ReflTransGen.refl

omit [DecidableEq V] in
/-- `A_Z` is transitive: an unblocked path into `u` extends along an unblocked path
`u ⇝ w`. -/
lemma unblockedAnc_subset_of_mem {Z : Finset V} {u w : V} (h : u ∈ G.unblockedAnc Z w) :
    G.unblockedAnc Z u ⊆ G.unblockedAnc Z w :=
  fun _ ha => ha.trans h

omit [DecidableEq V] in
/-- Only the terminal vertex of an unblocked path may lie in `Z`. -/
lemma not_mem_of_mem_unblockedAnc {Z : Finset V} {u v : V} (h : u ∈ G.unblockedAnc Z v)
    (hne : u ≠ v) : u ∉ Z := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, -⟩
  · exact absurd rfl hne
  · exact hc.2

omit [DecidableEq V] in
/-- A non-`Z` parent of `v` is an unblocked ancestor of `v`. -/
lemma mem_unblockedAnc_of_adj {Z : Finset V} {p v : V} (hp : p ∉ Z) (hadj : G.Adj p v) :
    p ∈ G.unblockedAnc Z v :=
  Relation.ReflTransGen.single ⟨hadj, hp⟩

omit [DecidableEq V] in
/-- `A_Z(p) ⊆ A_Z(v)` for a non-`Z` parent `p` of `v`. -/
lemma unblockedAnc_subset_of_adj {Z : Finset V} {p v : V} (hp : p ∉ Z) (hadj : G.Adj p v) :
    G.unblockedAnc Z p ⊆ G.unblockedAnc Z v :=
  G.unblockedAnc_subset_of_mem (G.mem_unblockedAnc_of_adj hp hadj)

omit [DecidableEq V] in
lemma isZClosed_iUnion {Z : Finset V} {ι : Sort*} {S : ι → Set V}
    (hS : ∀ j, G.IsZClosed Z (S j)) : G.IsZClosed Z (⋃ j, S j) := by
  intro w hw hne a ha
  obtain ⟨m, hmT, hmS⟩ := hne
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmS
  exact Set.mem_iUnion.mpr ⟨j, hS j w hw ⟨m, hmT, hj⟩ ha⟩

omit [DecidableEq V] in
lemma isZClosed_empty (Z : Finset V) : G.IsZClosed Z (∅ : Set V) := by
  rintro w _ ⟨m, -, hm⟩
  exact absurd hm (Set.notMem_empty m)

lemma zClosure_subset {Z : Finset V} {s : V} {S : Set V} (hS : G.IsZClosed Z S)
    (hs : G.unblockedAnc Z s ⊆ S) : G.zClosure Z s ⊆ S := by
  unfold Digraph.zClosure
  split
  · exact Set.empty_subset S
  · exact Set.sInter_subset_of_mem ⟨hS, hs⟩

lemma unblockedAnc_subset_zClosure {Z : Finset V} {s : V} (hs : s ∉ Z) :
    G.unblockedAnc Z s ⊆ G.zClosure Z s := by
  unfold Digraph.zClosure
  rw [if_neg hs]
  intro a ha S hS
  exact hS.2 ha

lemma isZClosed_zClosure (Z : Finset V) (s : V) : G.IsZClosed Z (G.zClosure Z s) := by
  unfold Digraph.zClosure
  split
  · exact G.isZClosed_empty Z
  · intro w hw hne a ha S hS
    exact hS.1 w hw ⟨hne.choose, hne.choose_spec.1, hne.choose_spec.2 S hS⟩ ha

/-- The induction principle for `S_Z(s)`: it is generated from `A_Z(s)` by repeatedly
adjoining `A_Z(w)` for `w ∈ Z` whenever `A_Z(w)` meets what has been built.  (No `s ∉ Z`
hypothesis is needed: for `s ∈ Z` the closure is empty and the conclusion is vacuous.) -/
lemma zClosure_induction {Z : Finset V} {s : V} {P : V → Prop}
    (base : ∀ u ∈ G.unblockedAnc Z s, P u)
    (step : ∀ w ∈ Z, ∀ u ∈ G.unblockedAnc Z w, (∃ m ∈ G.unblockedAnc Z w, P m) → P u) :
    ∀ u ∈ G.zClosure Z s, P u :=
  G.zClosure_subset (S := {u | P u}) (fun w hw hne u hu => step w hw u hu hne) base

/-- `S_Z(s)` is closed under unblocked ancestors: if `u ∈ S_Z(s)` then `A_Z(u) ⊆ S_Z(s)`. -/
lemma unblockedAnc_subset_zClosure_of_mem {Z : Finset V} {s : V} (hs : s ∉ Z) :
    ∀ u ∈ G.zClosure Z s, G.unblockedAnc Z u ⊆ G.zClosure Z s := by
  refine G.zClosure_induction (P := fun u => G.unblockedAnc Z u ⊆ G.zClosure Z s)
    (fun u hu => ?_) (fun w hw u hu hex => ?_)
  · exact (G.unblockedAnc_subset_of_mem hu).trans (G.unblockedAnc_subset_zClosure hs)
  · obtain ⟨m, hm, hmP⟩ := hex
    have hmem : m ∈ G.zClosure Z s := hmP (G.mem_unblockedAnc_self Z m)
    have : G.unblockedAnc Z w ⊆ G.zClosure Z s :=
      G.isZClosed_zClosure Z s w hw ⟨m, hm, hmem⟩
    exact (G.unblockedAnc_subset_of_mem hu).trans this

lemma zClosure_eq_empty {Z : Finset V} {s : V} (hs : s ∈ Z) : G.zClosure Z s = ∅ := by
  simp [zClosure, hs]

/-! ### `Z`-closure and the collider condition

`ColliderOK Z u` (`DSeparation.lean`) is exactly what makes `A_Z(u)` behave like an
`A_Z(w)` for `w ∈ Z` against a `Z`-closed set. -/

omit [DecidableEq V] in
/-- From an ancestor in `Z`: some `d ∈ Z` is reachable by a directed path whose
non-terminal vertices avoid `Z`. -/
lemma exists_mem_reflTransGen_of_isAncestor {Z : Finset V} {z : V} (hz : z ∈ Z) {u : V}
    (h : G.IsAncestor u z) : u ∉ Z →
      ∃ d ∈ Z, Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ Z) u d := by
  refine Relation.TransGen.head_induction_on
    (motive := fun a _ => a ∉ Z →
      ∃ d ∈ Z, Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ Z) a d) h ?_ ?_
  · intro a h' hu
    exact ⟨z, hz, Relation.ReflTransGen.single ⟨h', hu⟩⟩
  · intro a c h' _ ihc hu
    by_cases hc : c ∈ Z
    · exact ⟨c, hc, Relation.ReflTransGen.single ⟨h', hu⟩⟩
    · obtain ⟨d, hd, hpath⟩ := ihc hc
      exact ⟨d, hd, Relation.ReflTransGen.head ⟨h', hu⟩ hpath⟩

omit [DecidableEq V] in
/-- A vertex satisfying the collider condition has its `A_Z` inside that of some `z`-node. -/
lemma exists_zNode {Z : Finset V} {u : V} (h : G.ColliderOK Z u) :
    ∃ d ∈ Z, G.unblockedAnc Z u ⊆ G.unblockedAnc Z d := by
  by_cases hu : u ∈ Z
  · exact ⟨u, hu, subset_rfl⟩
  rcases h with hz | ⟨z, hz, hanc⟩
  · exact absurd hz hu
  · obtain ⟨d, hd, hp⟩ := exists_mem_reflTransGen_of_isAncestor hz hanc hu
    exact ⟨d, hd, unblockedAnc_subset_of_mem hp⟩

omit [DecidableEq V] in
/-- A `Z`-closed set that meets `A_Z(u)` for a vertex `u` satisfying the collider condition
contains all of `A_Z(u)`. -/
lemma unblockedAnc_subset_of_colliderOK {Z : Finset V} {S : Set V} (hS : G.IsZClosed Z S)
    {u : V} (hc : G.ColliderOK Z u) (hne : (G.unblockedAnc Z u ∩ S).Nonempty) :
    G.unblockedAnc Z u ⊆ S := by
  obtain ⟨d, hd, hsub⟩ := exists_zNode hc
  obtain ⟨m, hm1, hm2⟩ := hne
  exact hsub.trans (hS d hd ⟨m, hsub hm1, hm2⟩)

variable (G) in
/-- `{q | v ⇝ q by an unblocked path}`: the set the table constructions propagate along.
`u ∈ A_Z(v)` iff `v ∈ unblockedDesc Z u` (`mem_unblockedDesc_iff_mem_unblockedAnc`). -/
def unblockedDesc (Z : Finset V) (v : V) : Set V :=
  {q | Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ Z) v q}

omit [DecidableEq V] in
lemma mem_unblockedDesc_iff_mem_unblockedAnc {Z : Finset V} {u v : V} :
    v ∈ G.unblockedDesc Z u ↔ u ∈ G.unblockedAnc Z v := Iff.rfl

omit [DecidableEq V] in
lemma mem_unblockedDesc_self (Z : Finset V) (v : V) : v ∈ G.unblockedDesc Z v :=
  Relation.ReflTransGen.refl

omit [DecidableEq V] in
/-- Every unblocked descendant other than the source is reached through a live parent. -/
lemma unblockedDesc_step {Z : Finset V} {v q : V} (hq : q ∈ G.unblockedDesc Z v) (hqv : q ≠ v) :
    ∃ p : V, p ∈ G.unblockedDesc Z v ∧ p ∉ Z ∧ G.Adj p q := by
  rcases Relation.ReflTransGen.cases_tail hq with h | ⟨p, hvp, hadj, hpZ⟩
  · exact absurd h hqv
  · exact ⟨p, hvp, hpZ, hadj⟩

omit [DecidableEq V] in
/-- No unblocked path runs from `v` back to a parent of `v`: a parent of `v` is never an
unblocked descendant of `v`. -/
lemma IsAcyclic.not_mem_unblockedDesc_of_adj (hG : G.IsAcyclic) {Z : Finset V} {p v : V}
    (hadj : G.Adj p v) : p ∉ G.unblockedDesc Z v :=
  fun h => hG v (Relation.TransGen.tail' (h.mono fun _ _ hab => hab.1) hadj)

/-! ### `S_Z(A)` -/

lemma isZClosed_zClosureSet (Z A : Finset V) : G.IsZClosed Z (G.zClosureSet Z A) := by
  refine G.isZClosed_iUnion fun a => ?_
  exact G.isZClosed_iUnion fun _ => G.isZClosed_zClosure Z a

lemma mem_zClosureSet_of_mem_unblockedAnc {Z A : Finset V} {a u : V} (ha : a ∈ A) (haZ : a ∉ Z)
    (hu : u ∈ G.unblockedAnc Z a) : u ∈ G.zClosureSet Z A :=
  Set.mem_biUnion ha (G.unblockedAnc_subset_zClosure haZ hu)

lemma mem_zClosureSet_self {Z A : Finset V} {a : V} (ha : a ∈ A) (haZ : a ∉ Z) :
    a ∈ G.zClosureSet Z A :=
  G.mem_zClosureSet_of_mem_unblockedAnc ha haZ (G.mem_unblockedAnc_self Z a)

lemma exists_of_mem_zClosureSet {Z A : Finset V} {u : V} (hu : u ∈ G.zClosureSet Z A) :
    ∃ a ∈ A, a ∉ Z ∧ u ∈ G.zClosure Z a := by
  obtain ⟨a, ha, hua⟩ := Set.mem_iUnion₂.mp hu
  refine ⟨a, ha, ?_, hua⟩
  intro h
  simp only [Digraph.zClosure, if_pos h, Set.mem_empty_iff_false] at hua

/-- `S_Z(A)` is closed under unblocked ancestors of its members. -/
lemma unblockedAnc_subset_zClosureSet {Z A : Finset V} {u : V} (hu : u ∈ G.zClosureSet Z A) :
    G.unblockedAnc Z u ⊆ G.zClosureSet Z A := by
  obtain ⟨a, ha, haZ, hua⟩ := G.exists_of_mem_zClosureSet hu
  exact fun b hb =>
    Set.mem_biUnion ha (G.unblockedAnc_subset_zClosure_of_mem haZ u hua hb)

/-- `S_Z(A)` is closed under live (non-`Z`) parents. -/
lemma zClosureSet_liveParent {Z A : Finset V} {v p : V} (hv : v ∈ G.zClosureSet Z A)
    (hp : p ∉ Z) (hadj : G.Adj p v) : p ∈ G.zClosureSet Z A :=
  G.unblockedAnc_subset_zClosureSet hv (G.mem_unblockedAnc_of_adj hp hadj)

/-! ### `A_Z` with `Z = pa(v)`

The instance of the closure vocabulary the local Markov property runs on. -/

section Parents

variable [Fintype V] [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- With `Z = pa(v)` every edge into `v` is blocked at once, so `A_Z(v) = {v}`. -/
lemma unblockedAnc_parents_self (v : V) :
    G.unblockedAnc (G.parents v) v = {v} := by
  ext u
  constructor
  · intro hu
    rcases Relation.ReflTransGen.cases_tail hu with h | ⟨c, _, hc⟩
    · exact h ▸ rfl
    · exact absurd ((mem_parents G).mpr hc.1) hc.2
  · rintro rfl
    exact mem_unblockedAnc_self _ _

omit [DecidableEq V] in
/-- With `Z = pa(v)` no `A_Z(w)` for `w ∈ Z` contains `v`: that would close a cycle. -/
lemma notMem_unblockedAnc_of_mem_parents (hG : G.IsAcyclic) {v w : V}
    (hw : w ∈ G.parents v) : v ∉ G.unblockedAnc (G.parents v) w := fun hv =>
  hG v (Relation.TransGen.tail' (Relation.ReflTransGen.mono (fun _ _ hab => hab.1) hv)
    ((mem_parents G).mp hw))

end Parents

end Digraph

namespace FactoredSpaces

-- The ambient data `(V, G, Val)` is fixed for the whole development; most helper lemmas
-- use only part of the instance bundle, so the unused-section-variable linter would
-- otherwise demand an `omit` line on nearly every declaration.
set_option linter.unusedSectionVars false


variable {V : Type u} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val : V → Type w} [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)]

/-- `I^z`: the indices `(u, y)` whose parent configuration `y` agrees with `z` on
`pa(u) ∩ Z`. -/
def zConsistent (G : Digraph V) [DecidableRel G.Adj] (Val : V → Type w) {Z : Finset V}
    (z : PtOn Val Z) : Set (bnIndex G Val) :=
  {i | ∀ p : G.parents i.1, ∀ hp : p.1 ∈ Z, i.2 p = z ⟨p.1, hp⟩}

/-! ### The conditioning event -/

lemma mem_fiber_nodesVar_iff (hG : G.IsAcyclic) {Z : Finset V} {z : PtOn Val Z}
    {ω : Pt (bnFactor G Val)} :
    ω ∈ fiber (nodesVar (Val := Val) hG Z) z ↔ ∀ v : Z, nodeVar hG v.1 ω = z v :=
  ⟨fun h v => congrFun h v, fun h => funext h⟩

variable (Val) in
/-- `x` agrees with `z` on `Z`. -/
def ZCompat {Z : Finset V} (z : PtOn Val Z) (x : Pt Val) : Prop := ∀ v : Z, x v.1 = z v

lemma zCompat_jointVar (hG : G.IsAcyclic) {Z : Finset V} {z : PtOn Val Z}
    {ω : Pt (bnFactor G Val)} (hω : ω ∈ fiber (nodesVar (Val := Val) hG Z) z) :
    ZCompat Val z (jointVar hG ω) :=
  (mem_fiber_nodesVar_iff hG).mp hω

lemma mem_fiber_of_zCompat (hG : G.IsAcyclic) {Z : Finset V} {z : PtOn Val Z}
    {ω : Pt (bnFactor G Val)} (h : ZCompat Val z (jointVar hG ω)) :
    ω ∈ fiber (nodesVar (Val := Val) hG Z) z :=
  (mem_fiber_nodesVar_iff hG).mpr h

/-! ### `z`-consistent indices -/

lemma mem_zConsistent_iff {Z : Finset V} {z : PtOn Val Z} {i : bnIndex G Val} :
    i ∈ zConsistent G Val z ↔ ∀ p : G.parents i.1, ∀ hp : p.1 ∈ Z, i.2 p = z ⟨p.1, hp⟩ :=
  Iff.rfl

/-- Every index realized by a `z`-compatible joint value is `z`-consistent (L2). -/
lemma zConsistent_idxAt {Z : Finset V} {z : PtOn Val Z} {x : Pt Val} (hx : ZCompat Val z x)
    (v : V) : idxAt G Val x v ∈ zConsistent G Val z :=
  fun p hp => hx ⟨p.1, hp⟩

/-- Conversely, every `z`-consistent index is realized by a `z`-compatible joint value. -/
lemma exists_zCompat_idxAt [∀ v, Nonempty (Val v)] {Z : Finset V} {z : PtOn Val Z}
    {i : bnIndex G Val} (hi : i ∈ zConsistent G Val z) :
    ∃ x : Pt Val, ZCompat Val z x ∧ idxAt G Val x i.1 = i := by
  classical
  refine ⟨fun q => if h : G.Adj q i.1 then i.2 ⟨q, (Digraph.mem_parents G).mpr h⟩ else
      if hz : q ∈ Z then z ⟨q, hz⟩ else Classical.arbitrary (Val q), fun v => ?_, ?_⟩
  · by_cases h : G.Adj v.1 i.1
    · simp only [dif_pos h]
      exact hi ⟨v.1, (Digraph.mem_parents G).mpr h⟩ v.2
    · simp only [dif_neg h, dif_pos v.2]
  · refine congrArg (Sigma.mk i.1) (funext fun p => ?_)
    have h : G.Adj p.1 i.1 := (Digraph.mem_parents G).mp p.2
    show (if h : G.Adj p.1 i.1 then i.2 ⟨p.1, (Digraph.mem_parents G).mpr h⟩ else _) = i.2 p
    rw [dif_pos h]

lemma exists_zCompat [∀ v, Nonempty (Val v)] {Z : Finset V} (z : PtOn Val Z) :
    ∃ x : Pt Val, ZCompat Val z x := by
  classical
  exact ⟨fun q => if h : q ∈ Z then z ⟨q, h⟩ else Classical.arbitrary (Val q),
    fun v => by simp only [dif_pos v.2]⟩

/-- The block of a node is never empty: some `z`-consistent index sits at every `v`. -/
lemma exists_mem_zConsistent [∀ v, Nonempty (Val v)] {Z : Finset V} (z : PtOn Val Z) (v : V) :
    ∃ i : bnIndex G Val, i ∈ zConsistent G Val z ∧ i.1 = v := by
  obtain ⟨x, hx⟩ := exists_zCompat (Val := Val) z
  exact ⟨idxAt G Val x v, zConsistent_idxAt hx v, rfl⟩

/-! ### The candidate history `I^z ∩ I_S` -/

variable (G Val) in
/-- `I^z ∩ I_S`: the `z`-consistent indices sitting at nodes of `S`. -/
noncomputable def zcIdx {Z : Finset V} (z : PtOn Val Z) (S : Set V) : Finset (bnIndex G Val) := by
  classical
  exact Finset.univ.filter fun i => i ∈ zConsistent G Val z ∧ i.1 ∈ S

lemma mem_zcIdx_iff {Z : Finset V} {z : PtOn Val Z} {S : Set V} {i : bnIndex G Val} :
    i ∈ zcIdx G Val z S ↔ i ∈ zConsistent G Val z ∧ i.1 ∈ S := by
  classical
  simp [zcIdx]

/-! ### The table-construction API (`propTable`) -/

variable (G Val) in
/-- **The reusable table construction.**  Node `q` outputs the "good" value `x q`, except
that a node of `D` whose consulted configuration deviates from `x` at a live parent
(a parent in `D ∖ Z`) outputs the "bad" value `bad q`.  Every construction below is this
table modified at one or two indices by `Function.update`. -/
noncomputable def propTable (Z : Finset V) (x bad : Pt Val) (D : Set V) :
    Pt (bnFactor G Val) := by
  classical
  exact fun i =>
    if i.1 ∈ D ∧ ∃ p : G.parents i.1, p.1 ∈ D ∧ p.1 ∉ Z ∧ i.2 p ≠ x p.1 then bad i.1 else x i.1

lemma propTable_of_good {Z : Finset V} {x bad : Pt Val} {D : Set V} {q : V}
    {y : ParentVals G Val q} (h : ∀ p : G.parents q, p.1 ∈ D → p.1 ∉ Z → y p = x p.1) :
    propTable G Val Z x bad D ⟨q, y⟩ = x q := by
  classical
  refine if_neg ?_
  rintro ⟨-, p, hpD, hpZ, hne⟩
  exact hne (h p hpD hpZ)

lemma propTable_of_not_mem {Z : Finset V} {x bad : Pt Val} {D : Set V} {q : V}
    (hq : q ∉ D) (y : ParentVals G Val q) : propTable G Val Z x bad D ⟨q, y⟩ = x q := by
  classical
  exact if_neg fun h => hq h.1

lemma propTable_of_bad {Z : Finset V} {x bad : Pt Val} {D : Set V} {q : V}
    {y : ParentVals G Val q} (hq : q ∈ D) (p : G.parents q) (hpD : p.1 ∈ D) (hpZ : p.1 ∉ Z)
    (hne : y p ≠ x p.1) : propTable G Val Z x bad D ⟨q, y⟩ = bad q := by
  classical
  exact if_pos ⟨hq, p, hpD, hpZ, hne⟩

/-- **Bad propagation.**  If every node of `D` other than the source `d` returns a bad
value once a live parent deviates, and `X_d(ω)` already deviates, then `X_q(ω)` deviates
for every `q ∈ D`. -/
lemma nodeVar_ne_of_prop (hG : G.IsAcyclic) {Z : Finset V} {x bad : Pt Val} {D : Set V}
    {ω : Pt (bnFactor G Val)} {d : V} (hbad : ∀ q, bad q ≠ x q)
    (htab : ∀ q ∈ D, q ≠ d → ∀ y : ParentVals G Val q,
      (∃ p : G.parents q, p.1 ∈ D ∧ p.1 ∉ Z ∧ y p ≠ x p.1) → ω ⟨q, y⟩ = bad q)
    (hd : nodeVar hG d ω ≠ x d)
    (hstep : ∀ q ∈ D, q ≠ d → ∃ p : V, p ∈ D ∧ p ∉ Z ∧ G.Adj p q) :
    ∀ q ∈ D, nodeVar hG q ω ≠ x q := by
  intro q
  induction q using hG.wf.induction with
  | _ q ih =>
    intro hqD
    by_cases hqd : q = d
    · subst hqd; exact hd
    · obtain ⟨p, hpD, hpZ, hadj⟩ := hstep q hqD hqd
      have hp : nodeVar hG p ω ≠ x p := ih p hadj hpD
      have htq := htab q hqD hqd (parentConfig G Val (jointVar hG ω) q)
        ⟨⟨p, (Digraph.mem_parents G).mpr hadj⟩, hpD, hpZ, hp⟩
      have heq : nodeVar hG q ω = bad q := by rw [nodeVar_eq_idxAt]; exact htq
      rw [heq]; exact hbad q

/-- Two indices at the same node with different parent configurations are distinct. -/
lemma idx_ne_of_config_ne {q : V} {c d : ParentVals G Val q} (h : c ≠ d) :
    (⟨q, c⟩ : bnIndex G Val) ≠ ⟨q, d⟩ := by
  intro he
  rw [Sigma.mk.injEq] at he
  exact h (eq_of_heq he.2)

/-- Two indices at different nodes are distinct. -/
lemma idx_ne_of_node_ne {q r : V} {c : ParentVals G Val q} {d : ParentVals G Val r}
    (h : q ≠ r) : (⟨q, c⟩ : bnIndex G Val) ≠ ⟨r, d⟩ := fun he => h (congrArg Sigma.fst he)

/-! ### (L5) All-or-nothing on a block -/

/-- **(L5a) The adjacent step.**  Let `u → v` be an edge with `u ∉ Z`, and let `w ∈ Z` be
reachable from `v` by an unblocked path.  Then no set disintegrating `C` separates the two
indices a single `z`-compatible joint value `x` realizes at `u` and at `v`.

The witnesses are the all-good table `α = propTable x bad D` on the unblocked descendants
`D` of `v`; the doubly-updated `β`, which flips `u`'s entry to `bad u` (so `v` consults a
*different* entry, still good) and spoils `v`'s entry at the old configuration; and the
mixed point `μ`, which keeps `u`'s good entry — so `v` does consult the spoiled entry —
and whose badness then propagates along `D` and breaks `X_w = z_w`. -/
lemma mem_iff_mem_adj [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic) {Z : Finset V}
    {z : PtOn Val Z} {J : Finset (bnIndex G Val)}
    (hJ : Disintegrates J (fiber (nodesVar (Val := Val) hG Z) z))
    {x : Pt Val} (hx : ZCompat Val z x) {u v w : V}
    (hadj : G.Adj u v) (huZ : u ∉ Z) (hwZ : w ∈ Z) (hvw : w ∈ G.unblockedDesc Z v) :
    idxAt G Val x u ∈ J ↔ idxAt G Val x v ∈ J := by
  classical
  have hbadex : ∀ q : V, ∃ c : Val q, c ≠ x q := fun q => exists_ne (x q)
  choose bad hbad using hbadex
  have huv : u ≠ v := hG.ne_of_adj hadj
  have huD : u ∉ G.unblockedDesc Z v := hG.not_mem_unblockedDesc_of_adj hadj
  have hvD : v ∈ G.unblockedDesc Z v := G.mem_unblockedDesc_self Z v
  have hpar_v : ∀ p : G.parents v, p.1 ∉ G.unblockedDesc Z v := fun p =>
    hG.not_mem_unblockedDesc_of_adj ((Digraph.mem_parents G).mp p.2)
  have hik : (idxAt G Val x u : bnIndex G Val) ≠ idxAt G Val x v := idx_ne_of_node_ne huv
  obtain ⟨α, hα⟩ : ∃ a : Pt (bnFactor G Val),
      a = propTable G Val Z x bad (G.unblockedDesc Z v) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ b : Pt (bnFactor G Val), b =
      Function.update (Function.update α (idxAt G Val x u) (bad u)) (idxAt G Val x v) (bad v) :=
    ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ m : Pt (bnFactor G Val),
      m = Function.update α (idxAt G Val x v) (bad v) := ⟨_, rfl⟩
  -- the all-good point `α`
  have hαdiag : ∀ q, α (idxAt G Val x q) = x q := by
    intro q; rw [hα]; exact propTable_of_good (fun _ _ _ => rfl)
  have hαC : α ∈ fiber (nodesVar (Val := Val) hG Z) z :=
    mem_fiber_of_zCompat hG (by rw [jointVar_eq_of_diag hG hαdiag]; exact hx)
  -- the second point `β`
  have hβk : β (idxAt G Val x v) = bad v := by rw [hβ]; exact Function.update_self _ _ _
  have hβi : β (idxAt G Val x u) = bad u := by
    rw [hβ, Function.update_of_ne hik]; exact Function.update_self _ _ _
  have hβoff : ∀ j, j ≠ idxAt G Val x u → j ≠ idxAt G Val x v → β j = α j := by
    intro j h1 h2
    rw [hβ, Function.update_of_ne h2, Function.update_of_ne h1]
  have hβgood : ∀ q, nodeVar hG q β = Function.update x u (bad u) q := by
    refine nodeVar_eq_of_diag hG fun q => ?_
    by_cases hqu : q = u
    · subst hqu
      have hcfg : parentConfig G Val (Function.update x q (bad q)) q = parentConfig G Val x q :=
        funext fun p =>
          Function.update_of_ne (hG.ne_of_adj ((Digraph.mem_parents G).mp p.2)) _ _
      exact ((table_congr β hcfg).trans hβi).trans (Function.update_self q (bad q) x).symm
    · have h2 : (⟨q, parentConfig G Val (Function.update x u (bad u)) q⟩ : bnIndex G Val)
          ≠ idxAt G Val x u := idx_ne_of_node_ne hqu
      by_cases hqv : q = v
      · subst hqv
        have hu : u ∈ G.parents q := (Digraph.mem_parents G).mpr hadj
        have hcfgne :
            parentConfig G Val (Function.update x u (bad u)) q ≠ parentConfig G Val x q := by
          intro h
          exact hbad u ((Function.update_self u (bad u) x).symm.trans (congrFun h ⟨u, hu⟩))
        have h1 : (⟨q, parentConfig G Val (Function.update x u (bad u)) q⟩ : bnIndex G Val)
            ≠ idxAt G Val x q := idx_ne_of_config_ne hcfgne
        have hg : α (idxAt G Val (Function.update x u (bad u)) q) = x q := by
          rw [hα]; exact propTable_of_good (fun p hpD _ => absurd hpD (hpar_v p))
        exact ((hβoff _ h2 h1).trans hg).trans (Function.update_of_ne hqu (bad u) x).symm
      · have h1 : (⟨q, parentConfig G Val (Function.update x u (bad u)) q⟩ : bnIndex G Val)
            ≠ idxAt G Val x v := idx_ne_of_node_ne hqv
        have hg : α (idxAt G Val (Function.update x u (bad u)) q) = x q := by
          rw [hα]
          refine propTable_of_good (fun p hpD _ => ?_)
          by_cases hpu : p.1 = u
          · exact absurd (hpu ▸ hpD) huD
          · exact Function.update_of_ne hpu _ _
        exact ((hβoff _ h2 h1).trans hg).trans (Function.update_of_ne hqu (bad u) x).symm
  have hβC : β ∈ fiber (nodesVar (Val := Val) hG Z) z := by
    refine mem_fiber_of_zCompat hG fun w' => ?_
    have hne : w'.1 ≠ u := fun h => huZ (h ▸ w'.2)
    show nodeVar hG w'.1 β = z w'
    rw [hβgood w'.1, Function.update_of_ne hne]
    exact hx w'
  -- the mixed point `μ`
  have hμoff : ∀ q, q ∉ G.unblockedDesc Z v → ∀ y : ParentVals G Val q, μ ⟨q, y⟩ = x q := by
    intro q hq y
    have hqv : q ≠ v := by rintro rfl; exact hq hvD
    have h1 : (⟨q, y⟩ : bnIndex G Val) ≠ idxAt G Val x v := idx_ne_of_node_ne hqv
    rw [hμ, Function.update_of_ne h1, hα]
    exact propTable_of_not_mem hq y
  have hμconst : ∀ q, q ∉ G.unblockedDesc Z v → nodeVar hG q μ = x q := fun q hq =>
    nodeVar_eq_of_const hG (hμoff q hq)
  have hμv : nodeVar hG v μ = bad v := by
    have hcfg : parentConfig G Val (jointVar hG μ) v = parentConfig G Val x v :=
      funext fun p => hμconst p.1 (hpar_v p)
    have h1 : nodeVar hG v μ = μ (idxAt G Val x v) :=
      (nodeVar_eq_idxAt hG v μ).trans (table_congr μ hcfg)
    rw [h1, hμ, Function.update_self]
  have hμbad : ∀ q ∈ G.unblockedDesc Z v, nodeVar hG q μ ≠ x q := by
    refine nodeVar_ne_of_prop hG (Z := Z) (ω := μ) (d := v) hbad ?_ ?_ ?_
    · rintro q hqD hqv y ⟨p, hpD, hpZ, hne⟩
      have h1 : (⟨q, y⟩ : bnIndex G Val) ≠ idxAt G Val x v := idx_ne_of_node_ne hqv
      rw [hμ, Function.update_of_ne h1, hα]
      exact propTable_of_bad hqD p hpD hpZ hne
    · rw [hμv]; exact hbad v
    · exact fun q hqD hqv => G.unblockedDesc_step hqD hqv
  have hμC : μ ∉ fiber (nodesVar (Val := Val) hG Z) z := fun h =>
    hμbad w hvw (((mem_fiber_nodesVar_iff hG).mp h ⟨w, hwZ⟩).trans (hx ⟨w, hwZ⟩).symm)
  refine mem_iff_mem_of_mix hJ hαC hβC (fun j h1 h2 => (hβoff j h1 h2).symm) ?_
  rw [hβk, ← hμ]
  exact hμC

/-! ### Determination and disintegration for `Z`-closed vertex sets -/

/-- **(L3⇐) Determination.**  Two members of `C` that agree on `I^z ∩ I_S` agree at every
node of `S`, provided `S` is closed under live (non-`Z`) parents. -/
lemma nodeVar_eq_of_agree_on_zcIdx (hG : G.IsAcyclic) {Z : Finset V} {z : PtOn Val Z}
    {S : Set V} (hS : ∀ v ∈ S, ∀ p : V, p ∉ Z → G.Adj p v → p ∈ S)
    {ω ω' : Pt (bnFactor G Val)} (hω : ω ∈ fiber (nodesVar (Val := Val) hG Z) z)
    (hω' : ω' ∈ fiber (nodesVar (Val := Val) hG Z) z)
    (hagree : ∀ i ∈ zcIdx G Val z S, ω i = ω' i) :
    ∀ v ∈ S, nodeVar hG v ω = nodeVar hG v ω' := by
  intro v
  induction v using hG.wf.induction with
  | _ v ih =>
    intro hv
    have hc : parentConfig G Val (jointVar hG ω) v = parentConfig G Val (jointVar hG ω') v := by
      funext p
      have hadj : G.Adj p.1 v := (Digraph.mem_parents G).mp p.2
      show nodeVar hG p.1 ω = nodeVar hG p.1 ω'
      by_cases hpZ : p.1 ∈ Z
      · rw [(mem_fiber_nodesVar_iff hG).mp hω ⟨p.1, hpZ⟩,
          (mem_fiber_nodesVar_iff hG).mp hω' ⟨p.1, hpZ⟩]
      · exact ih p.1 hadj (hS v hv p.1 hpZ hadj)
    have hjmem : idxAt G Val (jointVar hG ω) v ∈ zcIdx G Val z S :=
      mem_zcIdx_iff.mpr ⟨zConsistent_idxAt (zCompat_jointVar hG hω) v, hv⟩
    rw [nodeVar_eq_idxAt hG v ω, nodeVar_eq_idxAt hG v ω']
    exact (hagree _ hjmem).trans (table_congr ω' hc)

/-- **(L4) Blocks disintegrate.**  If `S` is `Z`-closed then `I^z ∩ I_S` disintegrates `C`. -/
lemma disintegrates_zcIdx (hG : G.IsAcyclic) {Z : Finset V} {z : PtOn Val Z} {S : Set V}
    (hS : G.IsZClosed Z S) :
    Disintegrates (zcIdx G Val z S) (fiber (nodesVar (Val := Val) hG Z) z) := by
  classical
  refine (disintegrates_iff_splice _ _).mpr fun ω hω ω' hω' => ?_
  set K : Finset (bnIndex G Val) := zcIdx G Val z S
  set σ : Pt (bnFactor G Val) := K.piecewise ω ω'
  have main : ∀ v : V,
      ((G.unblockedAnc Z v ⊆ S) → nodeVar hG v σ = nodeVar hG v ω) ∧
      ((∀ a ∈ G.unblockedAnc Z v, a ∉ S) → nodeVar hG v σ = nodeVar hG v ω') := by
    intro v
    induction v using hG.wf.induction with
    | _ v ih =>
      have hZpar : ∀ p : V, G.Adj p v → ∀ hp : p ∈ Z, nodeVar hG p σ = z ⟨p, hp⟩ := by
        intro p hadj hp
        by_cases hnep : (G.unblockedAnc Z p ∩ S).Nonempty
        · rw [(ih p hadj).1 (hS p hp hnep)]
          exact (mem_fiber_nodesVar_iff hG).mp hω ⟨p, hp⟩
        · rw [(ih p hadj).2 fun a ha haS => hnep ⟨a, ha, haS⟩]
          exact (mem_fiber_nodesVar_iff hG).mp hω' ⟨p, hp⟩
      constructor
      · intro hsub
        have hc : parentConfig G Val (jointVar hG σ) v = parentConfig G Val (jointVar hG ω) v := by
          funext p
          have hadj : G.Adj p.1 v := (Digraph.mem_parents G).mp p.2
          show nodeVar hG p.1 σ = nodeVar hG p.1 ω
          by_cases hpZ : p.1 ∈ Z
          · rw [hZpar p.1 hadj hpZ]
            exact ((mem_fiber_nodesVar_iff hG).mp hω ⟨p.1, hpZ⟩).symm
          · exact (ih p.1 hadj).1 fun a ha =>
              hsub (G.unblockedAnc_subset_of_adj hpZ hadj ha)
        have hjmem : idxAt G Val (jointVar hG ω) v ∈ K :=
          mem_zcIdx_iff.mpr ⟨zConsistent_idxAt (zCompat_jointVar hG hω) v,
            hsub (G.mem_unblockedAnc_self Z v)⟩
        rw [nodeVar_eq_idxAt hG v σ, nodeVar_eq_idxAt hG v ω]
        refine (table_congr σ hc).trans ?_
        show K.piecewise ω ω' (idxAt G Val (jointVar hG ω) v) = _
        exact K.piecewise_eq_of_mem ω ω' hjmem
      · intro hall
        have hc : parentConfig G Val (jointVar hG σ) v = parentConfig G Val (jointVar hG ω') v := by
          funext p
          have hadj : G.Adj p.1 v := (Digraph.mem_parents G).mp p.2
          show nodeVar hG p.1 σ = nodeVar hG p.1 ω'
          by_cases hpZ : p.1 ∈ Z
          · rw [hZpar p.1 hadj hpZ]
            exact ((mem_fiber_nodesVar_iff hG).mp hω' ⟨p.1, hpZ⟩).symm
          · exact (ih p.1 hadj).2 fun a ha =>
              hall a (G.unblockedAnc_subset_of_adj hpZ hadj ha)
        have hjmem : idxAt G Val (jointVar hG ω') v ∉ K := fun h =>
          hall v (G.mem_unblockedAnc_self Z v) (mem_zcIdx_iff.mp h).2
        rw [nodeVar_eq_idxAt hG v σ, nodeVar_eq_idxAt hG v ω']
        refine (table_congr σ hc).trans ?_
        show K.piecewise ω ω' (idxAt G Val (jointVar hG ω') v) = _
        exact K.piecewise_eq_of_notMem ω ω' hjmem
  refine (mem_fiber_nodesVar_iff hG).mpr fun w => ?_
  by_cases hnew : (G.unblockedAnc Z w.1 ∩ S).Nonempty
  · rw [(main w.1).1 (hS w.1 w.2 hnew)]
    exact (mem_fiber_nodesVar_iff hG).mp hω w
  · rw [(main w.1).2 fun a ha haS => hnew ⟨a, ha, haS⟩]
    exact (mem_fiber_nodesVar_iff hG).mp hω' w

/-- The easy half of Theorem 1: `H(X_A | z) ⊆ I^z ∩ I_{S_Z(A)}`. -/
lemma history_nodesVar_subset [∀ v, Nonempty (Val v)] (hG : G.IsAcyclic)
    {Z : Finset V} (z : PtOn Val Z) (A : Finset V) :
    history (nodesVar (Val := Val) hG A) (fiber (nodesVar hG Z) z)
      ⊆ zcIdx G Val z (G.zClosureSet Z A) := by
  haveI : ∀ v, Nonempty (Val v) := fun v => inferInstance
  refine history_subset_of_generates ?_
  rw [generates_iff]
  refine ⟨disintegrates_zcIdx hG (G.isZClosed_zClosureSet Z A), fun ω hω ω' hω' hagree => ?_⟩
  funext a
  show nodeVar hG a.1 ω = nodeVar hG a.1 ω'
  by_cases haZ : a.1 ∈ Z
  · rw [(mem_fiber_nodesVar_iff hG).mp hω ⟨a.1, haZ⟩,
      (mem_fiber_nodesVar_iff hG).mp hω' ⟨a.1, haZ⟩]
  · exact nodeVar_eq_of_agree_on_zcIdx hG
      (fun v hv p hpZ hadj => G.zClosureSet_liveParent hv hpZ hadj) hω hω' hagree a.1
      (G.mem_zClosureSet_self a.2 haZ)

/-! ### (L3⇒) Relevance of `z`-consistent indices at unblocked ancestors -/

/-- **(L3⇒) Relevance.**  For `s ∉ Z` and a `z`-consistent index `i` sitting at an
unblocked ancestor of `s`, two members of `C` differing only at `i` disagree at `X_s`. -/
lemma exists_sep_pair_of_unblockedAnc [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic)
    {Z : Finset V} {z : PtOn Val Z} {s : V} (hs : s ∉ Z) {i : bnIndex G Val}
    (hi : i ∈ zConsistent G Val z) (hmem : i.1 ∈ G.unblockedAnc Z s) :
    ∃ ω ω' : Pt (bnFactor G Val),
      ω ∈ fiber (nodesVar (Val := Val) hG Z) z ∧ ω' ∈ fiber (nodesVar hG Z) z ∧
      (∀ j, j ≠ i → ω j = ω' j) ∧ nodeVar hG s ω ≠ nodeVar hG s ω' := by
  classical
  obtain ⟨u, cfg⟩ := i
  -- Step 0: the source of the unblocked path avoids `Z`.
  have huZ : u ∉ Z := by
    rcases Relation.ReflTransGen.cases_head hmem with h | ⟨b, hb, -⟩
    · exact fun hz => hs (h ▸ hz)
    · exact hb.2
  -- Step 1: a `z`-compatible joint value realizing the index.
  obtain ⟨x, hx, hidx⟩ := exists_zCompat_idxAt (Val := Val) hi
  have hidx2 : parentConfig G Val x u = cfg := by
    have h : (⟨u, parentConfig G Val x u⟩ : bnIndex G Val) = ⟨u, cfg⟩ := hidx
    simpa using h
  -- Step 2: a pointwise-different "bad" joint value.
  have hbadex : ∀ q : V, ∃ c : Val q, c ≠ x q := fun q => exists_ne (x q)
  choose bad hbad using hbadex
  -- Step 3: the live set.
  obtain ⟨D, hD⟩ : ∃ S : Set V, S = {q | q ∈ G.unblockedDesc Z u ∧ q ∉ Z} := ⟨_, rfl⟩
  have hmemD : ∀ q : V, q ∈ D ↔ (q ∈ G.unblockedDesc Z u ∧ q ∉ Z) := by
    intro q; rw [hD]; exact Iff.rfl
  have huD : u ∈ D := (hmemD u).mpr ⟨G.mem_unblockedDesc_self Z u, huZ⟩
  -- Step 4: the two points.
  obtain ⟨ω, hω⟩ : ∃ w : Pt (bnFactor G Val), w = propTable G Val Z x bad D := ⟨_, rfl⟩
  obtain ⟨ω', hω'⟩ : ∃ w : Pt (bnFactor G Val),
      w = Function.update ω (⟨u, cfg⟩ : bnIndex G Val) (bad u) := ⟨_, rfl⟩
  -- Step 5: `ω` realizes `x`, hence lies in the conditioning event.
  have hdiag : ∀ q, ω (idxAt G Val x q) = x q := by
    intro q; rw [hω]; exact propTable_of_good (fun _ _ _ => rfl)
  have hjoint : jointVar hG ω = x := jointVar_eq_of_diag hG hdiag
  have hωC : ω ∈ fiber (nodesVar (Val := Val) hG Z) z :=
    mem_fiber_of_zCompat hG (by rw [hjoint]; exact hx)
  -- Step 6: off `D`, the updated table is constantly good, so `X_q(ω') = x_q`.
  have hoff : ∀ q, q ∉ D → nodeVar hG q ω' = x q := by
    intro q hq
    refine nodeVar_eq_of_const hG (fun y => ?_)
    have hqi : (⟨q, y⟩ : bnIndex G Val) ≠ ⟨u, cfg⟩ := by
      intro h
      exact hq (by rw [show q = u from congrArg Sigma.fst h]; exact huD)
    rw [hω', Function.update_of_ne hqi, hω]
    exact propTable_of_not_mem hq y
  have hω'C : ω' ∈ fiber (nodesVar (Val := Val) hG Z) z := by
    refine mem_fiber_of_zCompat hG (fun v => ?_)
    have hvD : v.1 ∉ D := fun h => ((hmemD v.1).mp h).2 v.2
    show nodeVar hG v.1 ω' = z v
    rw [hoff v.1 hvD]
    exact hx v
  -- Step 7: on `D`, the updated table propagates the bad value.
  have hbadD : ∀ q ∈ D, nodeVar hG q ω' ≠ x q := by
    refine nodeVar_ne_of_prop hG (Z := Z) (ω := ω') (d := u) hbad ?_ ?_ ?_
    · rintro q hqD hqu y ⟨p, hpD, hpZ, hne⟩
      have hqi : (⟨q, y⟩ : bnIndex G Val) ≠ ⟨u, cfg⟩ := fun h =>
        hqu (show q = u from congrArg Sigma.fst h)
      rw [hω', Function.update_of_ne hqi, hω]
      exact propTable_of_bad hqD p hpD hpZ hne
    · have hpar : parentConfig G Val (jointVar hG ω') u = cfg := by
        refine Eq.trans (funext fun p => ?_) hidx2
        have hadj : G.Adj p.1 u := (Digraph.mem_parents G).mp p.2
        exact hoff p.1 fun h => hG.not_mem_unblockedDesc_of_adj hadj ((hmemD p.1).mp h).1
      have h1 : nodeVar hG u ω' = ω' ⟨u, cfg⟩ :=
        (nodeVar_eq_idxAt hG u ω').trans (table_congr ω' hpar)
      rw [h1, hω', Function.update_self]
      exact hbad u
    · intro q hqD hqu
      obtain ⟨p, hpdesc, hpZ, hadj⟩ := G.unblockedDesc_step ((hmemD q).mp hqD).1 hqu
      exact ⟨p, (hmemD p).mpr ⟨hpdesc, hpZ⟩, hpZ, hadj⟩
  -- Steps 8 and 9.
  have hsD : s ∈ D := (hmemD s).mpr ⟨hmem, hs⟩
  refine ⟨ω, ω', hωC, hω'C, fun j hj => ?_, ?_⟩
  · rw [hω']; exact (Function.update_of_ne hj _ _).symm
  · rw [nodeVar_eq_of_diag hG hdiag s]
    exact (hbadD s hsD).symm

/-- Consequently `I^z ∩ I_{A_Z(s)} ⊆ H(X_s | z)` for `s ∉ Z`. -/
lemma mem_history_nodeVar_of_unblockedAnc [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic)
    {Z : Finset V} {z : PtOn Val Z} {s : V} (hs : s ∉ Z) {i : bnIndex G Val}
    (hi : i ∈ zConsistent G Val z) (hmem : i.1 ∈ G.unblockedAnc Z s) :
    i ∈ history (nodeVar (Val := Val) hG s) (fiber (nodesVar hG Z) z) := by
  obtain ⟨ω, ω', hωC, hω'C, hagree, hne⟩ := exists_sep_pair_of_unblockedAnc hG hs hi hmem
  exact mem_history_of_sep hωC hω'C hagree hne

/-- **(L5b) Same node.**  All `z`-consistent indices at one node of a block lie on the
same side of any set disintegrating `C`.  Induction on the topological order: two
configurations that differ at all differ at a live parent, and the adjacent step moves
both to that parent. -/
lemma mem_iff_mem_same [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic) {Z : Finset V}
    {z : PtOn Val Z} {J : Finset (bnIndex G Val)}
    (hJ : Disintegrates J (fiber (nodesVar (Val := Val) hG Z) z)) {w : V} (hwZ : w ∈ Z) :
    ∀ v : V, w ∈ G.unblockedDesc Z v → ∀ x x' : Pt Val, ZCompat Val z x → ZCompat Val z x' →
      (idxAt G Val x v ∈ J ↔ idxAt G Val x' v ∈ J) := by
  intro v
  induction v using hG.wf.induction with
  | _ v ih =>
    intro hvw x x' hx hx'
    by_cases hcfg : parentConfig G Val x v = parentConfig G Val x' v
    · rw [show idxAt G Val x v = idxAt G Val x' v from congrArg (Sigma.mk v) hcfg]
    · obtain ⟨p, hp⟩ : ∃ p : G.parents v, x p.1 ≠ x' p.1 := by
        by_contra h
        push Not at h
        exact hcfg (funext h)
      have hadj : G.Adj p.1 v := (Digraph.mem_parents G).mp p.2
      have hpZ : p.1 ∉ Z := fun hz => hp ((hx ⟨p.1, hz⟩).trans (hx' ⟨p.1, hz⟩).symm)
      have hpw : w ∈ G.unblockedDesc Z p.1 := Relation.ReflTransGen.head ⟨hadj, hpZ⟩ hvw
      exact ((mem_iff_mem_adj hG hJ hx hadj hpZ hwZ hvw).symm.trans
        (ih p.1 hadj hpw x x' hx hx')).trans (mem_iff_mem_adj hG hJ hx' hadj hpZ hwZ hvw)

/-- **(L5c) Along an unblocked path.**  Iterating the adjacent step carries the index of a
fixed `z`-compatible joint value from `v` to the `Z`-node `w` at the end of the path. -/
lemma mem_iff_mem_path [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic) {Z : Finset V}
    {z : PtOn Val Z} {J : Finset (bnIndex G Val)}
    (hJ : Disintegrates J (fiber (nodesVar (Val := Val) hG Z) z))
    {x : Pt Val} (hx : ZCompat Val z x) {w : V} (hwZ : w ∈ Z) {v : V}
    (hvw : w ∈ G.unblockedDesc Z v) : idxAt G Val x v ∈ J ↔ idxAt G Val x w ∈ J := by
  have hvw' : Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ Z) v w := hvw
  clear hvw
  induction hvw' using Relation.ReflTransGen.head_induction_on with
  | refl => exact Iff.rfl
  | head h' h ih => exact (mem_iff_mem_adj hG hJ hx h'.1 h'.2 hwZ h).trans ih

/-- **(L5) All-or-nothing on a block.**  Any two `z`-consistent indices sitting at
unblocked ancestors of the same `w ∈ Z` lie on the same side of every set disintegrating
`C`: a disintegrating set contains all of `I^z ∩ I_{A_Z(w)}` or none of it. -/
lemma mem_iff_mem_of_unblockedAnc [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic) {Z : Finset V}
    {z : PtOn Val Z} {J : Finset (bnIndex G Val)}
    (hJ : Disintegrates J (fiber (nodesVar (Val := Val) hG Z) z)) {w : V} (hwZ : w ∈ Z)
    {i k : bnIndex G Val} (hi : i ∈ zConsistent G Val z) (hk : k ∈ zConsistent G Val z)
    (hiw : i.1 ∈ G.unblockedAnc Z w) (hkw : k.1 ∈ G.unblockedAnc Z w) : i ∈ J ↔ k ∈ J := by
  obtain ⟨x, hx, hxi⟩ := exists_zCompat_idxAt (Val := Val) hi
  obtain ⟨x', hx', hxk⟩ := exists_zCompat_idxAt (Val := Val) hk
  have e1 : (i ∈ J) ↔ (idxAt G Val x i.1 ∈ J) := by rw [hxi]
  have e2 : (k ∈ J) ↔ (idxAt G Val x' k.1 ∈ J) := by rw [hxk]
  refine e1.trans (((mem_iff_mem_path hG hJ hx hwZ hiw).trans ?_).trans e2.symm)
  exact (mem_iff_mem_same hG hJ hwZ w (G.mem_unblockedDesc_self Z w) x x' hx hx').trans
    (mem_iff_mem_path hG hJ hx' hwZ hkw).symm

/-! ### (L6) Assembly -/

/-- The hard half of Theorem 1: every `z`-consistent index at a node of `S_Z(a)` lies in
`H(X_A | z)` for `a ∈ A ∖ Z`.  The base case is (L3⇒); the closure step is (L5), applied
to the history itself (which disintegrates `C` by `generates_history`). -/
lemma mem_history_of_mem_zClosure [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic)
    {Z : Finset V} (z : PtOn Val Z) {A : Finset V} {a : V} (haA : a ∈ A) (haZ : a ∉ Z) :
    ∀ u ∈ G.zClosure Z a, ∀ i : bnIndex G Val, i ∈ zConsistent G Val z → i.1 = u →
      i ∈ history (nodesVar (Val := Val) hG A) (fiber (nodesVar hG Z) z) := by
  haveI : ∀ v, Nonempty (Val v) := fun v => inferInstance
  refine G.zClosure_induction (P := fun u => ∀ i : bnIndex G Val,
    i ∈ zConsistent G Val z → i.1 = u →
      i ∈ history (nodesVar (Val := Val) hG A) (fiber (nodesVar hG Z) z)) ?_ ?_
  · intro u hu i hi hiu
    have hderiv : DerivedOn (fiber (nodesVar (Val := Val) hG Z) z)
        (nodesVar (Val := Val) hG A) (nodeVar hG a) :=
      ⟨fun y => y ⟨a, haA⟩, fun _ _ => rfl⟩
    refine history_mono_of_derived hderiv ?_
    exact mem_history_nodeVar_of_unblockedAnc hG haZ hi (by rw [hiu]; exact hu)
  · rintro w hw u hu ⟨m, hm, hmP⟩ i hi hiu
    obtain ⟨i₀, hi₀z, hi₀m⟩ := exists_mem_zConsistent (G := G) (Val := Val) z m
    have hJ := (generates_history (nodesVar (Val := Val) hG A)
      (fiber (nodesVar (Val := Val) hG Z) z)).2
    refine (mem_iff_mem_of_unblockedAnc hG hJ hw hi hi₀z (by rw [hiu]; exact hu)
      (by rw [hi₀m]; exact hm)).mpr (hmP i₀ hi₀z hi₀m)

/-- **Realization**: every joint value `x` with `x_Z = z` is attained on the event
`{X_Z = z}` (by the constant tables `ω_{(v,·)} ≡ x_v`). -/
lemma exists_mem_fiber_nodesVar (hG : G.IsAcyclic) (Z : Finset V) (x : Pt Val) :
    ∃ ω ∈ fiber (nodesVar (Val := Val) hG Z) (proj Z x), jointVar hG ω = x :=
  ⟨constTable G Val x,
    (mem_fiber_nodesVar_iff hG).mpr fun v => congrFun (jointVar_constTable hG x) v.1,
    jointVar_constTable hG x⟩

/-- **The conditional history of a family of node variables**, in closed form:
`H(X_A | X_Z = z) = I^z ∩ I_{S_Z(A)}` (memo, Theorem 1). -/
lemma mem_history_nodesVar_iff [∀ v, Nontrivial (Val v)] (hG : G.IsAcyclic)
    (A Z : Finset V) (z : PtOn Val Z) (i : bnIndex G Val) :
    i ∈ history (nodesVar (Val := Val) hG A) (fiber (nodesVar hG Z) z) ↔
      i ∈ zConsistent G Val z ∧ i.1 ∈ G.zClosureSet Z A := by
  constructor
  · intro h
    exact mem_zcIdx_iff.mp (history_nodesVar_subset hG z A h)
  · rintro ⟨hiz, hiS⟩
    obtain ⟨a, haA, haZ, hia⟩ := G.exists_of_mem_zClosureSet hiS
    exact mem_history_of_mem_zClosure hG z haA haZ i.1 hia i hiz rfl

/-- **Structural independence of node families is a vertex-set criterion**:
`X_{V₁} ⊥ X_{V₂} | X_{V₃}` in `M^G` iff `S_{V₃}(V₁) ∩ S_{V₃}(V₂) = ∅` (memo, Corollary 2). -/
lemma structIndepGiven_nodesVar_iff_disjoint_zClosure [∀ v, Nontrivial (Val v)]
    (hG : G.IsAcyclic) (V₁ V₂ V₃ : Finset V) :
    StructIndepGiven (nodesVar (Val := Val) hG V₁) (nodesVar hG V₂) (nodesVar hG V₃) ↔
      Disjoint (G.zClosureSet V₃ V₁) (G.zClosureSet V₃ V₂) := by
  haveI : ∀ v, Nonempty (Val v) := fun v => inferInstance
  constructor
  · intro h
    rw [Set.disjoint_left]
    intro v hv1 hv2
    obtain ⟨i, hiz, hiv⟩ :=
      exists_mem_zConsistent (G := G) (Val := Val) (Classical.arbitrary (PtOn Val V₃)) v
    refine Finset.disjoint_left.mp (h (Classical.arbitrary (PtOn Val V₃)))
      ((mem_history_nodesVar_iff hG V₁ V₃ _ i).mpr ⟨hiz, by rw [hiv]; exact hv1⟩)
      ((mem_history_nodesVar_iff hG V₂ V₃ _ i).mpr ⟨hiz, by rw [hiv]; exact hv2⟩)
  · intro hdisj z
    rw [Finset.disjoint_left]
    intro i h1 h2
    exact Set.disjoint_left.mp hdisj ((mem_history_nodesVar_iff hG V₁ V₃ z i).mp h1).2
      ((mem_history_nodesVar_iff hG V₂ V₃ z i).mp h2).2

end FactoredSpaces
