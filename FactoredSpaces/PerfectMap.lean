import FactoredSpaces.Separation

/-!
# Perfect maps (§5.2.3, Definition 5.7, Proposition 5.8)

A DAG is a perfect map of a distribution `P` on its joint value space if its
d-separations are exactly the conditional independences of `P` among the node
projections; a factored space model is a perfect map of `P` with regard to a family of
variables if it is a model of `P` and its structural independences among the family are
exactly the conditional independences of `P` among the corresponding projections.
Factored space models are more expressive than DAGs (Proposition 5.8).

Proposition 5.8(1) also needs a step the paper's proof omits (`notes/paper-errata.md`,
E7): a perfect map `G` of `P` makes `P` *factorize* over `G`, which is what makes `M^G` a
factored space *model* of `P` (Proposition 5.4).  That is the standard "I-map implies
factorization" theorem (Koller–Friedman, Theorem 3.1), proved here as
`factorizesOverDAG_of_isIMapDAG` from the local Markov d-separations
(`Digraph.dSeparated_singleton_parents`, `ActiveTrails.lean`) and the chain rule along the
DAG's depth order (`Digraph.depth`, `Digraph.AncClosed`, `BayesNet.lean`).
-/

universe u w

namespace FactoredSpaces

section DAG

variable {V : Type u} [Fintype V] [DecidableEq V] {Val : V → Type w} [∀ v, Fintype (Val v)]

/-- **Perfect map (DAG).** `G` (with value space `Val = ×_v Val_v`) is a perfect map of a
distribution `P` on `Val` if for all sets of nodes `V₁, V₂, V₃ ⊆ V`, `V₁` and `V₂` are
d-separated given `V₃` in `G` iff `X_{V₁}` and `X_{V₂}` are independent given `X_{V₃}` in
`P` — the `X_S` being the coordinate projections of the observation space `Val`, which is
the paper's `Val(X̄) = Obs`.  The quantification is over *arbitrary* (possibly overlapping)
`V₁, V₂, V₃`, as the paper writes it — strictly stronger than the Koller–Friedman perfect map
(pairwise disjoint triples) the paper cites; Proposition 5.8(2) depends on this
(`notes/paper-errata.md`, E17).

The paper takes `G` to be a DAG throughout; acyclicity is not part of this definition but
travels as a separate hypothesis `hG : G.IsAcyclic` on the Proposition 5.8 statements, so
that the definition itself reads against Definition 5.7 as printed.

Paper node: Definition 5.7 (§5.2). -/
def IsPerfectMapDAG (G : Digraph V) (P : Distr (Pt Val)) : Prop :=
  ∀ V₁ V₂ V₃ : Finset V,
    G.DSeparated V₁ V₂ V₃ ↔ CondIndepVar P (proj V₁) (proj V₂) (proj V₃)

end DAG

section FSM

variable {I : Type*} [DecidableEq I] [Fintype I] {Ω : I → Type*} [∀ i, Fintype (Ω i)]
variable {W : Type*} [Fintype W] [DecidableEq W] {Val : W → Type*} [∀ w, Fintype (Val w)]

/-- **Perfect map (factored space model).** The model `M = (Ω, X)`, `X = (X_w)_{w∈W}` a
family of variables on `Ω` with joint value space `Val = ×_w Val_w`, is a perfect map of a
distribution `P` on `Val` with regard to `X` if `M` is a factored space model of `P` and
for all `W₁, W₂, W₃ ⊆ W`, `X_{W₁}` and `X_{W₂}` are independent given `X_{W₃}` in `P` (as
projections of `Val`) iff they are structurally independent given `X_{W₃}` in `Ω`.
(The paper types the family as `X_w : Ω → Obs`; read `Obs = ×_w Val(X_w)` and `O` as the
joint variable, which is how Proposition 5.8 uses it — see `notes/paper-errata.md`.)

Paper node: Definition 5.7 (§5.2). -/
def IsPerfectMapFSM (X : ∀ w : W, Pt Ω → Val w) (P : Distr (Pt Val)) : Prop :=
  IsFactoredSpaceModel (famJoint X) P ∧
    ∀ W₁ W₂ W₃ : Finset W,
      CondIndepVar P (proj W₁) (proj W₂) (proj W₃) ↔
        StructIndepGiven (famVar X W₁) (famVar X W₂) (famVar X W₃)

end FSM

section Expressiveness

variable {V : Type u} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val : V → Type w} [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)]

/-! ## From an I-map to a factorization (Koller–Friedman Theorem 3.1)

Definition 5.7(1) makes a perfect map `G` of `P` in particular an *I-map* of `P` — every
d-separation of `G` is a conditional independence of `P` — and Proposition 5.8(1) needs
`M^G` to be a factored space *model* of `P`, i.e. (Proposition 5.4) `P` to factorize over
`G`.  The paper's proof omits that step (`notes/paper-errata.md`, E7); it is supplied here
by the standard argument: the chain rule along the DAG's depth order, with each conditional
collapsed onto the parents by the local Markov d-separations. -/

/-- `G` is an **I-map** of `P`: every d-separation of `G` is a conditional independence of
`P`.  This is the direction of Definition 5.7(1) that the factorization theorem uses. -/
def IsIMapDAG (G : Digraph V) (P : Distr (Pt Val)) : Prop :=
  ∀ V₁ V₂ V₃ : Finset V, G.DSeparated V₁ V₂ V₃ → CondIndepVar P (proj V₁) (proj V₂) (proj V₃)

omit [DecidableRel G.Adj] [∀ v, DecidableEq (Val v)] in
lemma IsPerfectMapDAG.isIMapDAG {P : Distr (Pt Val)} (h : IsPerfectMapDAG G P) :
    IsIMapDAG G P := fun V₁ V₂ V₃ hd => (h V₁ V₂ V₃).mp hd

/-- The event `{y | y_S = x_S}` that a joint value agrees with `x` on `S` — the fibre of
`U_S` through `x`, and the shape every event in the chain rule has. -/
def agreeOn (S : Finset V) (x : Pt Val) : Set (Pt Val) := fiber (proj S) (proj S x)

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
lemma mem_agreeOn {S : Finset V} {x y : Pt Val} : y ∈ agreeOn S x ↔ ∀ i ∈ S, y i = x i :=
  proj_eq_iff

omit [Fintype V] [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
lemma agreeOn_inter (S T : Finset V) (x : Pt Val) :
    agreeOn S x ∩ agreeOn T x = agreeOn (S ∪ T) x := by
  ext y
  simp only [Set.mem_inter_iff, mem_agreeOn, Finset.mem_union]
  refine ⟨fun hy i hi => hi.elim (hy.1 i) (hy.2 i), fun hy => ?_⟩
  exact ⟨fun i hi => hy i (Or.inl hi), fun i hi => hy i (Or.inr hi)⟩

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
lemma agreeOn_mono {S T : Finset V} (h : S ⊆ T) (x : Pt Val) : agreeOn T x ⊆ agreeOn S x :=
  fun _ hy => mem_agreeOn.mpr fun i hi => mem_agreeOn.mp hy i (h hi)

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
lemma agreeOn_empty (x : Pt Val) : agreeOn (∅ : Finset V) x = Set.univ := by
  ext y; simp [mem_agreeOn]

omit [DecidableEq V] [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
lemma agreeOn_univ (x : Pt Val) : agreeOn (Finset.univ : Finset V) x = {x} := by
  ext y
  simp only [mem_agreeOn, Finset.mem_univ, forall_const, Set.mem_singleton_iff]
  exact ⟨funext, fun h i => by rw [h]⟩

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (Val v)] [∀ v, DecidableEq (Val v)] in
lemma agreeOn_singleton (v : V) (x : Pt Val) :
    agreeOn ({v} : Finset V) x = (fun y : Pt Val => y v) ⁻¹' {x v} := by
  ext y; simp [mem_agreeOn]

/-- The conditional probability distribution of `x_v` given a parent configuration under
`P`, made total by falling back on the uniform distribution at parent configurations of
probability zero — where `P` determines nothing (`dd:cpd`).  This is the CPD family
witnessing `FactorizesOverDAG` in `factorizesOverDAG_of_isIMapDAG`. -/
noncomputable def cpdOfDist (P : Distr (Pt Val)) (v : V)
    (y : ParentVals G Val v) : Distr (Val v) :=
  letI : Nonempty (Val v) := ⟨(Classical.choice P.nonempty_carrier) v⟩
  if h : 0 < P.prob (fiber (proj (G.parents v)) y) then
    (condDist P _ h).map fun x => x v
  else Distr.uniform

omit [∀ v, DecidableEq (Val v)] in
lemma cpdOfDist_mass_of_pos {P : Distr (Pt Val)} {v : V} (x : Pt Val)
    (h : 0 < P.prob (agreeOn (G.parents v) x)) :
    (cpdOfDist P v (parentConfig G Val x v)).mass (x v) =
      P.prob (agreeOn ({v} ∪ G.parents v) x) / P.prob (agreeOn (G.parents v) x) := by
  have he : cpdOfDist P v (parentConfig G Val x v)
      = (condDist P (agreeOn (G.parents v) x) h).map fun y => y v := dif_pos h
  rw [he, Distr.map_mass, condDist_prob, ← agreeOn_singleton, agreeOn_inter]

omit [∀ v, DecidableEq (Val v)] in
/-- **The chain rule along the DAG.**  For an I-map `G` of `P` and an ancestrally closed
set `S` of nodes, the probability that a joint value agrees with `x` on `S` is the product
over `S` of the conditional probabilities of `x_v` given `x_pa(v)`.

The induction removes a node `v ∈ S` of maximal depth: its parents lie in `S \ {v}` and
every other member of `S \ {v}` is a non-descendant of `v`, so the local Markov
d-separation `{v} ⊥ (S \ {v}) \ pa(v) | pa(v)` collapses the conditional on `S \ {v}` onto
one on `pa(v)`.  Parent configurations of probability zero need no separate treatment: the
whole prefix then has probability zero and the corresponding factor is zero. -/
lemma prob_agreeOn_eq_prod (hG : G.IsAcyclic) {P : Distr (Pt Val)}
    (h : IsIMapDAG G P) (x : Pt Val) :
    ∀ S : Finset V, G.AncClosed S →
      P.prob (agreeOn S x) = ∏ v ∈ S, (cpdOfDist P v (parentConfig G Val x v)).mass (x v) := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp [agreeOn_empty, Distr.prob_univ]
    obtain ⟨v, hvS, hvmax⟩ := S.exists_max_image (Digraph.depth hG) hne
    have hpaT : G.parents v ⊆ S.erase v := by
      intro u hu
      refine Finset.mem_erase.mpr ⟨?_, hS v hvS hu⟩
      rintro rfl
      exact Digraph.notMem_parents_self hG u hu
    have hTanc : G.AncClosed (S.erase v) := by
      intro u huT w hw
      have huS : u ∈ S := (Finset.mem_erase.mp huT).2
      refine Finset.mem_erase.mpr ⟨?_, hS u huS hw⟩
      rintro rfl
      exact absurd (hvmax u huS) (not_le.mpr (Digraph.depth_lt hG ((Digraph.mem_parents G).mp hw)))
    have hIH := ih (S.erase v) (Finset.erase_ssubset hvS) hTanc
    -- the local Markov independence, at the values of `x`
    have hsep := Digraph.dSeparated_singleton_parents hG v (S.erase v \ G.parents v) (by
      intro u hu
      obtain ⟨huT, -⟩ := Finset.mem_sdiff.mp hu
      have huS : u ∈ S := (Finset.mem_erase.mp huT).2
      refine ⟨(Finset.mem_erase.mp huT).1, fun hanc => ?_⟩
      exact absurd (hvmax u huS) (not_le.mpr (Digraph.depth_lt_of_isAncestor hG hanc)))
    have hRT : S.erase v \ G.parents v ∪ G.parents v = S.erase v :=
      Finset.sdiff_union_of_subset hpaT
    have hSeq : ({v} ∪ (S.erase v \ G.parents v)) ∪ G.parents v = S := by
      rw [Finset.union_assoc, hRT, ← Finset.insert_eq, Finset.insert_erase hvS]
    have hkey : P.prob (agreeOn ({v} ∪ G.parents v) x) * P.prob (agreeOn (S.erase v) x) =
        P.prob (agreeOn S x) * P.prob (agreeOn (G.parents v) x) := by
      have hci : P.prob (agreeOn ({v} : Finset V) x ∩ agreeOn (G.parents v) x) *
          P.prob (agreeOn (S.erase v \ G.parents v) x ∩ agreeOn (G.parents v) x) =
          P.prob (agreeOn ({v} : Finset V) x ∩ agreeOn (S.erase v \ G.parents v) x ∩
            agreeOn (G.parents v) x) * P.prob (agreeOn (G.parents v) x) :=
        h {v} (S.erase v \ G.parents v) (G.parents v) hsep _ _ _
      rwa [agreeOn_inter, agreeOn_inter, agreeOn_inter, agreeOn_inter, hRT, hSeq] at hci
    by_cases hpos : 0 < P.prob (agreeOn (S.erase v) x)
    · have hpapos : 0 < P.prob (agreeOn (G.parents v) x) :=
        lt_of_lt_of_le hpos (P.prob_mono (agreeOn_mono hpaT x))
      rw [← Finset.mul_prod_erase S _ hvS, ← hIH, cpdOfDist_mass_of_pos x hpapos]
      field_simp
      linarith [hkey]
    · rw [not_lt] at hpos
      have hz : P.prob (agreeOn (S.erase v) x) = 0 :=
        le_antisymm hpos (P.prob_nonneg _)
      rw [← Finset.mul_prod_erase S _ hvS, ← hIH, hz, mul_zero]
      exact P.prob_eq_zero_of_subset (agreeOn_mono (Finset.erase_subset v S) x) hz

omit [∀ v, DecidableEq (Val v)] in
/-- **I-map implies factorization** (Koller–Friedman, Theorem 3.1): if every d-separation
of the acyclic `G` is a conditional independence of `P`, then `P` factorizes over `G`.

This is the step Proposition 5.8(1) needs and the paper's proof omits
(`notes/paper-errata.md`, E7). -/
lemma factorizesOverDAG_of_isIMapDAG (hG : G.IsAcyclic)
    {P : Distr (Pt Val)} (h : IsIMapDAG G P) : FactorizesOverDAG G Val P := by
  refine ⟨fun v y => cpdOfDist P v y, fun x => ?_⟩
  have hx := prob_agreeOn_eq_prod hG h x Finset.univ fun v _ => Finset.subset_univ _
  rwa [agreeOn_univ, Distr.prob_singleton] at hx

/-- **Perfect maps of graphs and factored spaces (1)**, concretely: if `G` is a perfect map
of `P` then `M^G` is a perfect map of `P` with regard to `(X_v)_{v∈V}`.

Paper node: Proposition 5.8 (§5.2). -/
theorem isPerfectMapFSM_nodeVar_of_isPerfectMapDAG [∀ v, Nontrivial (Val v)]
    (hG : G.IsAcyclic) {P : Distr (Pt Val)} (h : IsPerfectMapDAG G P) :
    IsPerfectMapFSM (nodeVar (Val := Val) hG) P := by
  refine ⟨?_, fun W₁ W₂ W₃ => ?_⟩
  · exact (factorizesOverDAG_iff_isFactoredSpaceModel hG P).mp
      (factorizesOverDAG_of_isIMapDAG hG h.isIMapDAG)
  · exact (h W₁ W₂ W₃).symm.trans (dSeparated_iff_structIndepGiven hG W₁ W₂ W₃)

omit [∀ v, DecidableEq (Val v)] in
/-- **Perfect maps of graphs and factored spaces (1).** If some DAG `G` with nodes `V` is a
perfect map of `P`, then some factored space model `M = (Ω, X)` with `X = (X_v)_{v∈V}` is a
perfect map of `P` with regard to `X`.

Paper node: Proposition 5.8 (§5.2). -/
theorem exists_isPerfectMapFSM_of_exists_isPerfectMapDAG [∀ v, Nontrivial (Val v)]
    {P : Distr (Pt Val)}
    (h : ∃ G : Digraph V, G.IsAcyclic ∧ IsPerfectMapDAG G P) :
    ∃ (I : Type max u w) (Ω : I → Type w) (_ : Fintype I) (_ : DecidableEq I)
      (_ : ∀ i, Fintype (Ω i)) (X : ∀ v, Pt Ω → Val v), IsPerfectMapFSM X P := by
  classical
  obtain ⟨G, hG, hpm⟩ := h
  exact ⟨bnIndex G Val, bnFactor G Val, inferInstance, inferInstance, inferInstance,
    nodeVar hG, isPerfectMapFSM_nodeVar_of_isPerfectMapDAG (Val := Val) hG hpm⟩

end Expressiveness

/-! ## Two general lemmas used by the counterexample

An empty history is constancy, and conditional independence of the coordinate projections
under the law of a family's joint variable is conditional independence of the subfamilies
upstairs.  Both are general facts about §4's vocabulary; they are stated here because the
counterexample of Proposition 5.8(2) is the first place they are needed. -/

/-- **A history is empty exactly when the variable is constant.** `H(X | C) = ∅` iff `X`
takes the same value at all points of `C`: the empty index set disintegrates every event,
so it generates `X` given `C` precisely when `X` is constant on `C`. -/
lemma history_eq_empty_iff {I : Type*} [DecidableEq I] [Fintype I] {Ω : I → Type*}
    {α : Type*} [Nonempty α] (X : Pt Ω → α) (C : Set (Pt Ω)) :
    history X C = ∅ ↔ ∀ a ∈ C, ∀ b ∈ C, X a = X b := by
  constructor
  · intro h a ha b hb
    have hgen : Generates (∅ : Finset I) X C :=
      (generates_iff_history_subset (disintegrates_empty C)).mpr (by simp [h])
    exact ((generates_iff _ _ _).mp hgen).2 a ha b hb (by simp)
  · intro h
    rw [← Finset.subset_empty]
    exact history_subset_of_generates
      ((generates_iff _ _ _).mpr ⟨disintegrates_empty C, fun a ha b hb _ => h a ha b hb⟩)

/-- **Conditional independence transfers along the joint variable of a family.**
Independence of the projections `π_{W_k}` under the law `P^Ω ∘ X⁻¹` of the joint variable
is independence of the subfamilies `X_{W_k}` under `P^Ω`, because `π_W ∘ X = X_W`: the two
sides are literally the same identity between probabilities of the same events. -/
lemma condIndepVar_map_famJoint {I : Type*} [DecidableEq I] [Fintype I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] {W : Type*} [Fintype W] [DecidableEq W] {Val : W → Type*}
    [∀ w, Fintype (Val w)] (X : ∀ w : W, Pt Ω → Val w) (Q : Distr (Pt Ω))
    (W₁ W₂ W₃ : Finset W) :
    CondIndepVar (Q.map (famJoint X)) (proj W₁) (proj W₂) (proj W₃) ↔
      CondIndepVar Q (famVar X W₁) (famVar X W₂) (famVar X W₃) := by
  -- Definition 6.1 is stated over an arbitrary sample space, so its events are written as
  -- set-builders rather than as `fiber`s; both sides here are still `rfl`.
  have key : ∀ (S : Finset W) (x : PtOn Val S),
      famJoint X ⁻¹' {t | proj S t = x} = {t | famVar X S t = x} := fun _ _ => rfl
  refine forall_congr' fun x => forall_congr' fun y => forall_congr' fun z => ?_
  simp only [CondIndep, Distr.map_prob, Set.preimage_inter, key]

/-! ## Conditional-independence tools for checking a perfect map

Verifying `IsPerfectMapDAG G P` means deciding `CondIndepVar P (proj V₁) (proj V₂) (proj V₃)`
for *arbitrary, possibly overlapping* `V₁, V₂, V₃` (Definition 5.7 as printed; errata E17).
These are the general facts that make that tractable: a family already determined by the
conditioning family is independent of everything (`condIndepVar_proj_of_subset_left`), a
conditional independence of families restricts to subfamilies
(`CondIndepVar.of_proj_subset`), and — the reason the overlapping quantification is not
idle — a non-degenerate coordinate is never independent of *itself* given a family that
omits it (`not_condIndepVar_proj_self`).  They belong with §6.1's vocabulary in
`Probability.lean`; they are stated here because `Examples.lean` is the first consumer.
-/

section CondIndepTools

variable {I : Type*} [DecidableEq I] [Fintype I] {Ω : I → Type*} [∀ i, Fintype (Ω i)]

/-- If the conditioning event is contained in `A`, then `A` is conditionally independent of
everything given it. -/
lemma CondIndep.of_subset_left {P : Distr (Pt Ω)} {A B C : Set (Pt Ω)} (h : C ⊆ A) :
    CondIndep P A B C := by
  have h1 : A ∩ C = C := Set.inter_eq_right.mpr h
  have h2 : A ∩ B ∩ C = B ∩ C := by
    ext ω
    simp only [Set.mem_inter_iff]
    exact ⟨fun hh => ⟨hh.1.2, hh.2⟩, fun hh => ⟨⟨h hh.2, hh.1⟩, hh.2⟩⟩
  show P.prob (A ∩ C) * P.prob (B ∩ C) = P.prob (A ∩ B ∩ C) * P.prob C
  rw [h1, h2]
  ring

/-- If `A` is disjoint from the conditioning event, it is conditionally independent of
everything given it (both sides vanish). -/
lemma CondIndep.of_disjoint_left {P : Distr (Pt Ω)} {A B C : Set (Pt Ω)} (h : Disjoint A C) :
    CondIndep P A B C := by
  have h1 : A ∩ C = ∅ := Set.disjoint_iff_inter_eq_empty.mp h
  have h2 : A ∩ B ∩ C = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ω hω
    have hmem : ω ∈ A ∩ C := ⟨hω.1.1, hω.2⟩
    rw [h1] at hmem
    simp at hmem
  show P.prob (A ∩ C) * P.prob (B ∩ C) = P.prob (A ∩ B ∩ C) * P.prob C
  rw [h1, h2, P.prob_empty]
  ring

/-- Conditional independence of variables is symmetric. -/
lemma CondIndepVar.symm {α β γ : Type*} {P : Distr (Pt Ω)} {X : Pt Ω → α} {Y : Pt Ω → β}
    {Z : Pt Ω → γ} (h : CondIndepVar P X Y Z) : CondIndepVar P Y X Z :=
  fun y x z => (h x y z).symm

omit [DecidableEq I] [Fintype I] [∀ i, Fintype (Ω i)] in
/-- A fibre of `U_J` either sits inside a given fibre of `U_{J'}` (`J' ⊆ J`) or misses it. -/
lemma fiber_proj_subset_or_disjoint {J' J : Finset I} (h : J' ⊆ J) (x : PtOn Ω J')
    (z : PtOn Ω J) :
    fiber (proj J) z ⊆ fiber (proj J') x ∨
      Disjoint (fiber (proj J') x) (fiber (proj J) z) := by
  by_cases hx : Finset.restrict₂ h z = x
  · refine Or.inl fun ω hω => ?_
    show proj J' ω = x
    rw [← hx]
    show (fun i : J' => ω i) = Finset.restrict₂ h z
    funext i
    exact congrFun (show proj J ω = z from hω) ⟨i, h i.2⟩
  · refine Or.inr (Set.disjoint_left.2 fun ω hω hω' => hx ?_)
    have hz : proj J ω = z := hω'
    have hx' : proj J' ω = x := hω
    rw [← hz, ← hx']
    rfl

/-- **A conditioned-on family is independent of everything.**  If `J₁ ⊆ J₃` then `U_{J₁}` is
conditionally independent of any variable given `U_{J₃}`, because each fibre of `U_{J₃}`
either lies inside or misses each fibre of `U_{J₁}`. -/
lemma condIndepVar_proj_of_subset_left {P : Distr (Pt Ω)} {J₁ J₃ : Finset I} (h : J₁ ⊆ J₃)
    {β : Type*} (Y : Pt Ω → β) : CondIndepVar P (proj J₁) Y (proj J₃) := by
  intro x _ z
  rcases fiber_proj_subset_or_disjoint h x z with hsub | hdisj
  · exact CondIndep.of_subset_left hsub
  · exact CondIndep.of_disjoint_left hdisj

/-- The right-hand form of `condIndepVar_proj_of_subset_left`. -/
lemma condIndepVar_proj_of_subset_right {P : Distr (Pt Ω)} {J₂ J₃ : Finset I} (h : J₂ ⊆ J₃)
    {α : Type*} (X : Pt Ω → α) : CondIndepVar P X (proj J₂) (proj J₃) :=
  (condIndepVar_proj_of_subset_left h X).symm

/-- **Shrinking both sides of a conditional independence of families**: two applications of
Lemma C.14 (`CondIndepEventVar.of_proj_subset`), with a symmetry between them. -/
lemma CondIndepVar.of_proj_subset {P : Distr (Pt Ω)} {J₁' J₁ J₂' J₂ : Finset I} {γ : Type*}
    {Z : Pt Ω → γ} (h₁ : J₁' ⊆ J₁) (h₂ : J₂' ⊆ J₂)
    (h : CondIndepVar P (proj J₁) (proj J₂) Z) : CondIndepVar P (proj J₁') (proj J₂') Z := by
  intro x y z
  have s1 : ∀ x₁ : PtOn Ω J₁,
      CondIndepEventVar P (fiber (proj J₁) x₁) (proj J₂') (fiber Z z) :=
    fun x₁ => CondIndepEventVar.of_proj_subset h₂ (fun y₂ => h x₁ y₂ z)
  have s2 : CondIndepEventVar P (fiber (proj J₂') y) (proj J₁') (fiber Z z) :=
    CondIndepEventVar.of_proj_subset h₁ (fun x₁ => (s1 x₁ y).symm)
  exact (s2 x).symm

/-- **A non-degenerate coordinate is never conditionally independent of itself.**  Under a
strictly positive `P`, with `i ∉ J` and `Ω_i` nontrivial, `U_i ⊥ U_i | U_J` fails: two
distinct fibres of `U_i` both meet the conditioning fibre in positive probability but are
disjoint from each other.  This is what makes the *overlapping* triples of Definition 5.7
(errata E17) real content, and it discharges every `V₁ ∩ V₂ ⊄ V₃` case uniformly. -/
lemma not_condIndepVar_proj_self {P : Distr (Pt Ω)} (hP : P.StrictlyPositive) {i : I}
    {J : Finset I} (hi : i ∉ J) [Nontrivial (Ω i)] :
    ¬ CondIndepVar P (proj ({i} : Finset I)) (proj ({i} : Finset I)) (proj J) := by
  intro h
  obtain ⟨ω⟩ := P.nonempty_carrier
  obtain ⟨b, hb⟩ := exists_ne (ω i)
  set ω' : Pt Ω := Function.update ω i b with hω'def
  have hω'i : ω' i = b := Function.update_self (β := Ω) i b ω
  have hω'ne : ∀ j : I, j ≠ i → ω' j = ω j := fun j hj => Function.update_of_ne hj b ω
  set A := fiber (proj ({i} : Finset I)) (proj {i} ω) with hA
  set B := fiber (proj ({i} : Finset I)) (proj {i} ω') with hB
  set C := fiber (proj J) (proj J ω) with hC
  have key := h (proj {i} ω) (proj {i} ω') (proj J ω)
  have hAB : A ∩ B = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    have e1 : proj ({i} : Finset I) x = proj {i} ω := hx1
    have e2 : proj ({i} : Finset I) x = proj {i} ω' := hx2
    have : ω i = ω' i :=
      congrFun (e1.symm.trans e2) ⟨i, Finset.mem_singleton_self i⟩
    rw [hω'i] at this
    exact hb this.symm
  have hABC : A ∩ B ∩ C = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hmem : x ∈ A ∩ B := hx.1
    rw [hAB] at hmem
    simp at hmem
  have hωAC : ω ∈ A ∩ C := ⟨rfl, rfl⟩
  have hω'BC : ω' ∈ B ∩ C := by
    refine ⟨rfl, ?_⟩
    show proj J ω' = proj J ω
    exact proj_eq_iff.mpr fun j hj => hω'ne j (fun hji => hi (hji ▸ hj))
  have hpos1 : 0 < P.prob (A ∩ C) := (P.prob_pos_iff _).2 ⟨ω, hωAC, hP ω⟩
  have hpos2 : 0 < P.prob (B ∩ C) := (P.prob_pos_iff _).2 ⟨ω', hω'BC, hP ω'⟩
  have hkey : P.prob (A ∩ C) * P.prob (B ∩ C) = P.prob (A ∩ B ∩ C) * P.prob C := key
  rw [hABC, P.prob_empty, zero_mul] at hkey
  exact (mul_pos hpos1 hpos2).ne' hkey

end CondIndepTools

/-! ## The counterexample of Proposition 5.8(2) -/

namespace Prop58Witness

/-- Value spaces of the paper's counterexample.  The node type is `Bool`: `false` is the
paper's `v₁` and `true` is `v₂`.  The paper's `X₁ = U₁` takes values in `Ω₁ = {0, 1, 2}`
and `X₂ = [U₁ > 0]` takes Boolean values, so `Val(X_{v₁}) = Fin 3` and `Val(X_{v₂}) = Bool`;
both have at least two elements, as Proposition 5.8 requires. -/
abbrev Val : Bool → Type
  | false => Fin 3
  | true => Bool

instance instFintypeVal : ∀ b : Bool, Fintype (Val b)
  | false => inferInstanceAs (Fintype (Fin 3))
  | true => inferInstanceAs (Fintype Bool)

instance instNontrivialVal : ∀ b : Bool, Nontrivial (Val b)
  | false => inferInstanceAs (Nontrivial (Fin 3))
  | true => inferInstanceAs (Nontrivial Bool)

/-- The factored space of the counterexample: a single factor `Ω = Ω₁ = {0, 1, 2}`. -/
abbrev Om : Unit → Type := fun _ => Fin 3

/-- The paper's family `X = (X₁, X₂)` on `Ω`: `X₁ = U₁` and `X₂ = [U₁ > 0]`. -/
def X : ∀ b : Bool, Pt Om → Val b
  | false => fun ω => ω ()
  | true => fun ω => decide (0 < ω ())

/-- The point of `Ω` whose single coordinate is `n`. -/
def om (n : Fin 3) : Pt Om := fun _ => n

@[simp] lemma om_apply (n : Fin 3) : om n () = n := rfl

/-- A point of `Ω` is determined by its single coordinate. -/
lemma pt_ext {a b : Pt Om} (h : a () = b ()) : a = b := by
  funext i
  cases i
  exact h

/-- The uniform distribution on the single factor, as a distribution on `Ω`. -/
noncomputable def PO : Distr (Pt Om) :=
  Distr.prod (fun _ : Unit => (Distr.uniform : Distr (Fin 3)))

lemma factorizes_PO : Factorizes PO := factorizes_prod _

/-- `P^Ω` has full support, so every nonempty event has positive probability. -/
lemma prob_PO_pos {A : Set (Pt Om)} (h : A.Nonempty) : 0 < PO.prob A := by
  obtain ⟨ω, hω⟩ := h
  rw [Distr.prob_pos_iff]
  exact ⟨ω, hω, (Distr.prod_mass_pos_iff _ ω).mpr fun _ => Distr.uniform_strictlyPositive _⟩

/-- The distribution `P` of the counterexample: the law of `X` under the uniform
distribution on `Ω`. -/
noncomputable def P : Distr (Pt Val) := PO.map (famJoint X)

/-- Two points agree under `X_S` exactly when they agree in the coordinates `S` selects:
the value of `U₁` when `v₁ ∈ S`, its positivity when `v₂ ∈ S`. -/
lemma famVar_eq_iff (S : Finset Bool) (a b : Pt Om) :
    famVar X S a = famVar X S b ↔
      ((false ∈ S) → a () = b ()) ∧ ((true ∈ S) → decide (0 < a ()) = decide (0 < b ())) := by
  constructor
  · intro h
    exact ⟨fun hf => congrFun h ⟨false, hf⟩, fun ht => congrFun h ⟨true, ht⟩⟩
  · rintro ⟨h1, h2⟩
    funext w
    obtain ⟨w, hw⟩ := w
    cases w
    · exact h1 hw
    · exact h2 hw

lemma famVar_empty_eq (a b : Pt Om) : famVar X ∅ a = famVar X ∅ b :=
  (famVar_eq_iff ∅ a b).mpr ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩

lemma famVar_ne_of_mem_false {S : Finset Bool} (hS : false ∈ S) {m n : Fin 3} (h : m ≠ n) :
    famVar X S (om m) ≠ famVar X S (om n) :=
  fun heq => h (((famVar_eq_iff S _ _).mp heq).1 hS)

lemma famVar_ne_of_mem_true {S : Finset Bool} (hS : true ∈ S) {m n : Fin 3}
    (h : decide (0 < m) ≠ decide (0 < n)) :
    famVar X S (om m) ≠ famVar X S (om n) :=
  fun heq => h (((famVar_eq_iff S _ _).mp heq).2 hS)

/-- No nonempty subfamily is constant: `X_S` already separates `0` from `1`. -/
lemma famVar_zero_ne_one {S : Finset Bool} (hS : S.Nonempty) :
    famVar X S (om 0) ≠ famVar X S (om 1) := by
  obtain ⟨w, hw⟩ := hS
  cases w
  · exact famVar_ne_of_mem_false hw (by decide)
  · exact famVar_ne_of_mem_true hw (by decide)

lemma pos_of_famVar_eq_one {S : Finset Bool} (hS : S.Nonempty) {ω : Pt Om}
    (h : famVar X S ω = famVar X S (om 1)) : 0 < ω () := by
  obtain ⟨w, hw⟩ := hS
  rw [famVar_eq_iff] at h
  cases w
  · have h' : ω () = (1 : Fin 3) := h.1 hw
    rw [h']
    decide
  · have hone : decide (0 < om (1 : Fin 3) ()) = true := by decide
    have h' := h.2 hw
    rw [hone] at h'
    exact of_decide_eq_true h'

lemma not_pos_of_famVar_eq_zero {S : Finset Bool} (hS : S.Nonempty) {ω : Pt Om}
    (h : famVar X S ω = famVar X S (om 0)) : ¬ (0 < ω ()) := by
  obtain ⟨w, hw⟩ := hS
  rw [famVar_eq_iff] at h
  cases w
  · have h' : ω () = (0 : Fin 3) := h.1 hw
    rw [h']
    decide
  · have hzero : decide (0 < om (0 : Fin 3) ()) = false := by decide
    have h' := h.2 hw
    rw [hzero] at h'
    exact of_decide_eq_false h'

/-- **Independence pattern of the counterexample.**  `X_{W₁} ⊥ X_{W₂} | X_{W₃}` holds
exactly in these cases.  If `v₁ ∈ W₃` the conditioning event is a single point of `Ω`, so
everything is independent given it; if only `v₂ ∈ W₃` the conditioning event still fixes
`[U₁ > 0]`, and `X_{W_k}` is constant on it exactly when `v₁ ∉ W_k` — this is the paper's
nontrivial `X₂ ⊥ X₂ | X₁` together with `X₁ ⊥̸ X₁ | X₂`; with `W₃ = ∅` only the empty
subfamilies are independent (`X₁ ⊥̸ X₁`, `X₁ ⊥̸ X₂`, `X₂ ⊥̸ X₂`). -/
def ind (W₁ W₂ W₃ : Finset Bool) : Prop :=
  if false ∈ W₃ then True
  else if true ∈ W₃ then (false ∉ W₁ ∨ false ∉ W₂)
  else (W₁ = ∅ ∨ W₂ = ∅)

lemma ind_of_mem_false {W₁ W₂ W₃ : Finset Bool} (h : false ∈ W₃) : ind W₁ W₂ W₃ := by
  simp only [ind, if_pos h]

lemma ind_iff_of_mem_true {W₁ W₂ W₃ : Finset Bool} (h1 : false ∉ W₃) (h2 : true ∈ W₃) :
    ind W₁ W₂ W₃ ↔ (false ∉ W₁ ∨ false ∉ W₂) := by
  simp only [ind, if_neg h1, if_pos h2]

lemma ind_iff_of_notMem {W₁ W₂ W₃ : Finset Bool} (h1 : false ∉ W₃) (h2 : true ∉ W₃) :
    ind W₁ W₂ W₃ ↔ (W₁ = ∅ ∨ W₂ = ∅) := by
  simp only [ind, if_neg h1, if_neg h2]

lemma eq_empty_of_notMem {S : Finset Bool} (h1 : false ∉ S) (h2 : true ∉ S) : S = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr fun w => by cases w <;> assumption

/-- Disjointness of two subsets of the one-element index set is triviality of one of
them. -/
private lemma disjoint_unit_iff (s t : Finset Unit) : Disjoint s t ↔ s = ∅ ∨ t = ∅ := by
  constructor
  · intro h
    by_cases hs : s = ∅
    · exact Or.inl hs
    · refine Or.inr ?_
      by_contra ht
      obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr ht
      cases u
      cases v
      exact Finset.disjoint_left.mp h hu hv
  · rintro (rfl | rfl)
    · exact disjoint_bot_left
    · exact disjoint_bot_right

/-- Structural independence in the witness, unfolded: with a single factor, disjointness
of the two conditional histories says that one of `X_{W₁}`, `X_{W₂}` is constant on each
fibre of `X_{W₃}`. -/
lemma structIndepGiven_iff_forall (W₁ W₂ W₃ : Finset Bool) :
    StructIndepGiven (famVar X W₁) (famVar X W₂) (famVar X W₃) ↔
      ∀ z : PtOn Val W₃,
        (∀ a ∈ fiber (famVar X W₃) z, ∀ b ∈ fiber (famVar X W₃) z,
            famVar X W₁ a = famVar X W₁ b) ∨
        (∀ a ∈ fiber (famVar X W₃) z, ∀ b ∈ fiber (famVar X W₃) z,
            famVar X W₂ a = famVar X W₂ b) := by
  refine forall_congr' fun z => ?_
  rw [disjoint_unit_iff, history_eq_empty_iff, history_eq_empty_iff]

/-- Points of a fibre of `X_{W₃}` agree under `X_{W₃}`. -/
lemma famVar_eq_of_mem_fiber {W₃ : Finset Bool} {z : PtOn Val W₃} {a b : Pt Om}
    (ha : a ∈ fiber (famVar X W₃) z) (hb : b ∈ fiber (famVar X W₃) z) :
    famVar X W₃ a = famVar X W₃ b := by
  have ha' : famVar X W₃ a = z := ha
  have hb' : famVar X W₃ b = z := hb
  rw [ha', hb']

/-- **Step 2: the structural independences of the witness are exactly `ind`.**  These are
the paper's tables of independencies and dependencies: `H(X₁) = H(X₂) = H(X₁ | X₂) = {1}`
and `H(X₂ | X₁) = ∅`. -/
lemma structIndepGiven_iff_ind (W₁ W₂ W₃ : Finset Bool) :
    StructIndepGiven (famVar X W₁) (famVar X W₂) (famVar X W₃) ↔ ind W₁ W₂ W₃ := by
  rw [structIndepGiven_iff_forall]
  by_cases hf : false ∈ W₃
  · -- conditioning on `U₁` leaves a single point: everything is constant
    refine iff_of_true (fun z => Or.inl fun a ha b hb => ?_) (ind_of_mem_false hf)
    have hab := famVar_eq_of_mem_fiber ha hb
    rw [pt_ext (((famVar_eq_iff _ _ _).mp hab).1 hf)]
  by_cases ht : true ∈ W₃
  · rw [ind_iff_of_mem_true hf ht]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      -- `om 1` and `om 2` lie in the same fibre of `X_{W₃}` but differ under `U₁`
      have hmem : om 2 ∈ fiber (famVar X W₃) (famVar X W₃ (om 1)) :=
        (famVar_eq_iff _ _ _).mpr ⟨fun h' => absurd h' hf, fun _ => by decide⟩
      rcases h (famVar X W₃ (om 1)) with h | h
      · exact famVar_ne_of_mem_false hc1 (by decide)
          (h (om 1) rfl (om 2) hmem)
      · exact famVar_ne_of_mem_false hc2 (by decide)
          (h (om 1) rfl (om 2) hmem)
    · intro h z
      have hconst : ∀ (S : Finset Bool), false ∉ S →
          ∀ a ∈ fiber (famVar X W₃) z, ∀ b ∈ fiber (famVar X W₃) z,
            famVar X S a = famVar X S b := by
        intro S hS a ha b hb
        exact (famVar_eq_iff _ _ _).mpr
          ⟨fun h' => absurd h' hS,
           fun _ => ((famVar_eq_iff _ _ _).mp (famVar_eq_of_mem_fiber ha hb)).2 ht⟩
      exact h.imp (hconst W₁) (hconst W₂)
  · -- `W₃ = ∅`: the fibre is all of `Ω`
    rw [ind_iff_of_notMem hf ht, eq_empty_of_notMem hf ht]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      rcases h (famVar X (∅ : Finset Bool) (om 0)) with h | h
      · exact famVar_zero_ne_one hc1
          (h (om 0) rfl (om 1) (famVar_empty_eq _ _))
      · exact famVar_zero_ne_one hc2
          (h (om 0) rfl (om 1) (famVar_empty_eq _ _))
    · rintro (rfl | rfl) z
      · exact Or.inl fun a _ b _ => famVar_empty_eq a b
      · exact Or.inr fun a _ b _ => famVar_empty_eq a b

/-- The failure of conditional independence is witnessed by a pair of events of positive
probability whose intersection with the conditioning event is empty. -/
lemma not_condIndep {A B C : Set (Pt Om)} (hAC : (A ∩ C).Nonempty) (hBC : (B ∩ C).Nonempty)
    (hABC : A ∩ B ∩ C = ∅) : ¬ CondIndep PO A B C := by
  intro h
  have h' : PO.prob (A ∩ C) * PO.prob (B ∩ C) = PO.prob (A ∩ B ∩ C) * PO.prob C := h
  rw [hABC, Distr.prob_empty, zero_mul] at h'
  exact (mul_pos (prob_PO_pos hAC) (prob_PO_pos hBC)).ne' h'

/-- **Step 3: the probabilistic conditional independences of `P^Ω` are exactly `ind`.**

The ⟸ direction is soundness of structural independence (Theorem 6.2); the ⟹ direction
exhibits, in each failing case, two events of positive probability with empty
intersection. -/
lemma condIndepVar_PO_iff_ind (W₁ W₂ W₃ : Finset Bool) :
    CondIndepVar PO (famVar X W₁) (famVar X W₂) (famVar X W₃) ↔ ind W₁ W₂ W₃ := by
  refine ⟨fun h => ?_, fun h => condIndepVar_of_structIndepGiven
    ((structIndepGiven_iff_ind W₁ W₂ W₃).mpr h) PO factorizes_PO⟩
  by_contra hc
  by_cases hf : false ∈ W₃
  · exact hc (ind_of_mem_false hf)
  by_cases ht : true ∈ W₃
  · rw [ind_iff_of_mem_true hf ht] at hc
    push Not at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hmem : famVar X W₃ (om 2) = famVar X W₃ (om 1) :=
      (famVar_eq_iff _ _ _).mpr ⟨fun h' => absurd h' hf, fun _ => by decide⟩
    refine not_condIndep (A := fiber (famVar X W₁) (famVar X W₁ (om 1)))
      (B := fiber (famVar X W₂) (famVar X W₂ (om 2)))
      (C := fiber (famVar X W₃) (famVar X W₃ (om 1)))
      ⟨om 1, rfl, rfl⟩ ⟨om 2, rfl, hmem⟩ ?_ (h _ _ _)
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ω ⟨⟨hA, hB⟩, -⟩
    have e1 : ω () = (1 : Fin 3) := ((famVar_eq_iff _ _ _).mp hA).1 hc1
    have e2 : ω () = (2 : Fin 3) := ((famVar_eq_iff _ _ _).mp hB).1 hc2
    rw [e1] at e2
    exact absurd e2 (by decide)
  · rw [ind_iff_of_notMem hf ht] at hc
    push Not at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hW₃ : W₃ = ∅ := eq_empty_of_notMem hf ht
    subst hW₃
    refine not_condIndep (A := fiber (famVar X W₁) (famVar X W₁ (om 1)))
      (B := fiber (famVar X W₂) (famVar X W₂ (om 0)))
      (C := fiber (famVar X (∅ : Finset Bool)) (famVar X (∅ : Finset Bool) (om 0)))
      ⟨om 1, rfl, famVar_empty_eq _ _⟩ ⟨om 0, rfl, rfl⟩ ?_ (h _ _ _)
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ω ⟨⟨hA, hB⟩, -⟩
    exact not_pos_of_famVar_eq_zero hc2 hB
      (pos_of_famVar_eq_one hc1 hA)

/-- The conditional independences of `P` among the coordinate projections of the
observation space are exactly `ind`. -/
lemma condIndepVar_P_iff_ind (W₁ W₂ W₃ : Finset Bool) :
    CondIndepVar P (proj W₁) (proj W₂) (proj W₃) ↔ ind W₁ W₂ W₃ := by
  show CondIndepVar (PO.map (famJoint X)) (proj W₁) (proj W₂) (proj W₃) ↔ _
  rw [condIndepVar_map_famJoint, condIndepVar_PO_iff_ind]

/-- `(Ω, X)` is a perfect map of `P` with regard to `X`. -/
lemma isPerfectMapFSM_X : IsPerfectMapFSM X P := by
  refine ⟨⟨PO, factorizes_PO, fun o => rfl⟩, fun W₁ W₂ W₃ => ?_⟩
  rw [condIndepVar_P_iff_ind, structIndepGiven_iff_ind]

/-- No DAG on `{v₁, v₂}` is a perfect map of `P`: `X₂ ⊥ X₂ | X₁` holds in `P`, but `v₂`
is never d-separated from itself given a set not containing it. -/
lemma not_isPerfectMapDAG (G : Digraph Bool) : ¬ IsPerfectMapDAG G P := by
  intro h
  have hind : ind {true} {true} {false} := ind_of_mem_false (by simp)
  exact Digraph.not_dSeparated_self (V₁ := {true}) (V₂ := {true}) (V₃ := {false}) (v := true)
    (by simp) (by simp) (by simp)
    ((h {true} {true} {false}).mpr ((condIndepVar_P_iff_ind _ _ _).mpr hind))

end Prop58Witness

/-- **Perfect maps of graphs and factored spaces (2).** There is a distribution `P` on an
observation space `×_v Val_v` (every `Val_v` with at least two elements) with a factored
space model that is a perfect map of `P` with regard to `(X_v)_v`, but no DAG with nodes
`V` that is a perfect map of `P`.  The paper's witness: `Ω = Ω₁ = {0, 1, 2}`,
`X₁ = U₁`, `X₂ = [U₁ > 0]`, so `X₂ ⊥ X₂ | X₁` holds in `P` and structurally, while no
graph d-separates `v₂` from itself given `v₁`.

The acyclicity hypothesis on the right-hand side is stated only to match the paper: the
witness lemma `Prop58Witness.not_isPerfectMapDAG` proves the stronger statement that *no*
digraph on `V` — acyclic or not — is a perfect map of `P`, since a vertex is never
d-separated from itself given a set not containing it.

Paper node: Proposition 5.8 (§5.2). -/
theorem exists_isPerfectMapFSM_not_exists_isPerfectMapDAG :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (Val : V → Type) (_ : ∀ v, Fintype (Val v))
      (_ : ∀ v, Nontrivial (Val v)) (P : Distr (Pt Val)),
      (∃ (I : Type) (Ω : I → Type) (_ : Fintype I) (_ : DecidableEq I) (_ : ∀ i, Fintype (Ω i))
        (X : ∀ v, Pt Ω → Val v), IsPerfectMapFSM X P) ∧
      ∀ G : Digraph V, G.IsAcyclic → ¬ IsPerfectMapDAG G P :=
  ⟨Bool, inferInstance, inferInstance, Prop58Witness.Val, Prop58Witness.instFintypeVal,
    Prop58Witness.instNontrivialVal, Prop58Witness.P,
    ⟨Unit, Prop58Witness.Om, inferInstance, inferInstance, fun _ => inferInstance,
      Prop58Witness.X, Prop58Witness.isPerfectMapFSM_X⟩,
    fun G _ => Prop58Witness.not_isPerfectMapDAG G⟩

end FactoredSpaces
