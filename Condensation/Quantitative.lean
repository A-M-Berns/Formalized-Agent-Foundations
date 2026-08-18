import Condensation.Amalgamation
import Condensation.Perfect

/-!
# Condensation §5 — comparison of latent variable models

This file is §5.2–§5.3 of Eisenstat, *Condensation: A Theory of Concepts*:

* **Lemma 5.4** — the quantitative variant of Lemma 4.14, in both the exact form (5.6) and
  the inequality form (5.5).  Proved.
* **Definition 5.5** — the polar `F°` of a subfamily `F ⊆ P⁺I` (`polar`), with the two
  facts §5 uses: `polar F` is upward-closed and `polar` is antitone.
* **Definition 5.6** — the intersection tree (`ITree`, `ITree.label`,
  `ITree.intersections`), and **Proposition 5.7** — existence and uniqueness of the
  extension of a leaf labeling by members of an intersection-closed collection `M` to a
  labeling `ℓ : V → M` of every vertex satisfying (5.10).
* **Theorem 5.8** — the general comparison theorem, in both the inequality form (5.13) and
  the exact form (5.14).
* **Corollary 5.9** ((5.21), (5.22)) and **Corollary 5.10** ((5.24), (5.25)).

## Modeling decisions

`dd:tree` — Definition 5.6's directed binary tree `(V, E, ℓ)` is rendered as an inductive
binary tree `ITree`, with the label of an internal vertex *computed* as the meet of its
children's labels (`ITree.label`).  Note the paper's direction convention: its "parents" of
a vertex `u` are what the inductive presentation calls the *children* of `u`, and the
"ancestors" of `v` are the vertices of the subtree above `v`.  Because `ITree` is an
inductive type, it ranges over exactly the **finite** trees: this is a *disclosed reading*
of Definition 5.6, not a neutral change of presentation, since the definition as printed
carries no finiteness or well-foundedness clause (`notes/paper-errata.md` entry 17).  The
reading is licensed by Theorem 5.8, whose conclusion (5.14) is a finite sum over the leaves
and internal vertices of the tree — an infinite or non-well-founded tree makes that sum
meaningless, so the finite reading is the only one under which the paper's own theorem has
content.  Read that way, a directed rooted binary tree in which every vertex has a unique
directed path to the root *is* an inductive binary tree, and the `(V, E, ℓ)` presentation
would import graph theory for no content.  Proposition 5.7 is then the statement that an
arbitrary labeling of *all* the vertices (rendered as a fully-decorated tree `LTree`) which
restricts to the given leaf labeling, satisfies (5.10) everywhere and lands in `M`
everywhere (`LTree.LabelsIn`) is the computed one — existence and uniqueness of a function
`ℓ : V → M`, exactly as printed.  Definition 5.6's family of intersections (5.11) is a
`List`, not a `Finset`: the paper explicitly warns that the same intersection may occur
more than once.

`dd:interaction` — Theorem 5.8's `I (Z_{L(v)} ; Z_{R(v)} ; Y_⊇A | Z_{I(v)})` is
`Condensation.condInteractionInfo` from `Condensation/Probability.lean`.

`dd:pplus` — subfamilies of `P⁺I` are `Set (PPlus I)`, so the polar, upward-closure and
the intersection algebra of §5 are plain set algebra; `Set (PPlus I)` is a
`SemilatticeInf` (indeed a complete lattice) with `⊓ = ∩`, which is what `ITree.label`
ranges over.

Finiteness — Lemma 5.4's raw variables carry `ShannonInformation.FiniteEntropyOf`, the
paper's own hypothesis; the `dd:finite-range` narrowing was retired on 2026-08-17.  Every
statement quantifying over a model or an amalgamation gets it from the structure.

## Definition 4.12's amalgamation is the ambient data

Theorem 5.8 and Corollaries 5.9–5.10 are stated about an **amalgamation**
`Am : LatentAmalgamation L₁ L₂` (Definition 4.12, `Condensation/Amalgamation.lean`) of two
latent variable models for one random variable model `M`.  `L₁` supplies the paper's `Y`
family, `L₂` supplies its `Z` family, and `Am.Λ₀` is the single probability space on which
the paper reads all three of `X`, `Y` and `Z` — the paper's "when we write random variables
`X`, `Y`, or `Z`, we will mean their pullbacks to `Λ₀` under the appropriate maps".  The
two latent variable models `Am.lat₁`, `Am.lat₂` derived from the structure have `Am.Λ₀` as
their underlying probability space *definitionally*, so the §5 statements are written in
Definition 3.3/3.4's own vocabulary and nothing is re-spelled locally: `Y_⊇A` is
`Am.lat₁.jointAbove A.toFinset`, `Z_G` is `Am.lat₂.jointOn G`, `X_B` is
`Am.lat₁.pullbackJoint B.toFinset`, `ϱ_Y(B)` is `Am.lat₁.reconScore B.toFinset`, and
Definition 4.8's ordered Markov condition on the `Z` family is `RVModel.OrderedMarkov
Am.rv₂` (`Condensation/Perfect.lean`).  Definition 3.2's two contribution conditions are
fields of the structure, so they are hypotheses of nothing here.  The section preamble
before Theorem 5.8 says which of them the proof of (5.13) actually uses and why the
`Am.comm` field is what reconciles `Am.π₁` with `Am.π₂`.

## Status

Statements are complete, match the paper as printed, and quantify over Definition 4.12's
`LatentAmalgamation` throughout.  **No proof in this file is `sorry` as of M2**: Lemma 5.4
in both forms, Definition 5.5's polar facts, Definition 5.6 and Proposition 5.7 in full,
Theorem 5.8's (5.13) and (5.14), Corollary 5.9's (5.21) and (5.22), and Corollary 5.10's
(5.24) and (5.25) are all proved, as is the structural bridge `ITree.label_eq_polar` (the
root label of Theorem 5.8's tree *is* the polar `G`, which is what puts `Z_G` on the left
of (5.13)/(5.14)).

All five §5 endpoints are inventoried in `AxiomAudit.lean` and axiom-clean, including
`condEntropy_jointAbove_le_reconScore_of_orderedMarkov` (5.22): it consumes Proposition
4.10 (`RVModel.orderedMarkov_iff`, `Condensation/Perfect.lean`), whose proof was completed
in the same milestone.

The general machinery M2 needed is generic and does not belong to §5, so it lives upstream:
the `AEFunctionOf` congruences and the three conditional-entropy comparison lemmas in
`Condensation/Probability.lean`, `above_mono` and the union companion of
`RVModel.functionOf_jointOn_mono` in `Condensation/Model.lean`, and the `Λ₀`-pinned
finiteness helper `LatentAmalgamation.finiteEntropyOf'` in `Condensation/Amalgamation.lean`.
-/

universe u v w u₀ u₁ v₁ u₂ v₂

namespace Condensation

open MeasureTheory ProbabilityTheory

/-! ## Lemma 5.4

The paper's own proof of (5.6) is "a straightforward if unenlightening calculation"; over
the vendored substrate it is two applications of `condMutualInfo_eq'` and `ring`, once the
arguments of the interaction information have been rotated into the order those rewrites
produce.  The rotation needs the symmetry of `condInteractionInfo` in all three of its
first arguments, which is proved here.  (`Condensation/Probability.lean` proves the
corresponding symmetries for the *unconditional* `interactionInfo`, Definition 2.3's
carrier; the conditional form is used only by §5, so its symmetries live here.) -/

section Lemma54

variable {Ω S T₁ T₂ V : Type*}
  [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T₁] [MeasurableSpace T₂]
  [MeasurableSpace V]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T₁] [MeasurableSingletonClass T₂]
  [MeasurableSingletonClass V]
  [Countable S] [Countable T₁] [Countable T₂] [Countable V]
  {X : Ω → S} {Y₁ : Ω → T₁} {Y₂ : Ω → T₂} {C : Ω → V}
  {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
  [ShannonInformation.FiniteEntropyOf X μ] [ShannonInformation.FiniteEntropyOf Y₁ μ]
  [ShannonInformation.FiniteEntropyOf Y₂ μ] [ShannonInformation.FiniteEntropyOf C μ]

/-- Conditioning on `(Y₁, Y₂, C)` and on `(Y₂, Y₁, C)` gives the same conditional entropy:
the two conditioning variables differ by an injective relabelling of the range. -/
lemma condEntropy_pair_rotate (hX : Measurable X) (hY₁ : Measurable Y₁)
    (hY₂ : Measurable Y₂) (hC : Measurable C) :
    H[X | ⟨Y₁, ⟨Y₂, C⟩⟩ ; μ] = H[X | ⟨Y₂, ⟨Y₁, C⟩⟩ ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  haveI : ShannonInformation.FiniteEntropyOf (⟨Y₁, C⟩ : Ω → T₁ × V) μ :=
    ShannonInformation.finiteEntropyOf_pair (μ := μ) hY₁ hC
  haveI : ShannonInformation.FiniteEntropyOf (⟨Y₂, ⟨Y₁, C⟩⟩ : Ω → T₂ × T₁ × V) μ :=
    ShannonInformation.finiteEntropyOf_pair (μ := μ) hY₂ (hY₁.prodMk hC)
  exact ShannonInformation.condEntropy_of_injective' μ hX (hY₂.prodMk (hY₁.prodMk hC))
    (fun p : T₂ × T₁ × V ↦ (p.2.1, p.1, p.2.2))
    (by rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h; simp_all)
    (hY₁.prodMk (hY₂.prodMk hC))

omit [MeasurableSingletonClass T₂] [MeasurableSingletonClass V] [Countable T₂] [Countable V]
  [ShannonInformation.FiniteEntropyOf X μ] [ShannonInformation.FiniteEntropyOf Y₁ μ] in
/-- `I (X; Y; Z | C)` is symmetric in `X` and `Y`.  Like its unconditional companion
`interactionInfo_comm`, this needs no finiteness at all. -/
lemma condInteractionInfo_comm (hX : Measurable X) (hY₁ : Measurable Y₁)
    (Y₂ : Ω → T₂) (C : Ω → V) (μ : Measure Ω) :
    condInteractionInfo X Y₁ Y₂ C μ = condInteractionInfo Y₁ X Y₂ C μ := by
  rw [condInteractionInfo, condInteractionInfo, condMutualInfo_comm hX hY₁,
    condMutualInfo_comm hX hY₁]

/-- `I (X; Y; Z | C)` is symmetric in `Y` and `Z`.  With `condInteractionInfo_comm` this
generates the full symmetric group on the three arguments, which is what lets Lemma 5.4 be
stated with the paper's argument order `I (Y₁; Y₂; X | C)` and proved in the order the
chain rules produce. -/
lemma condInteractionInfo_swap (hX : Measurable X) (hY₁ : Measurable Y₁)
    (hY₂ : Measurable Y₂) (hC : Measurable C) :
    condInteractionInfo X Y₁ Y₂ C μ = condInteractionInfo X Y₂ Y₁ C μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [condInteractionInfo]
  haveI : ShannonInformation.FiniteEntropyOf (⟨Y₂, C⟩ : Ω → T₂ × V) μ :=
    ShannonInformation.finiteEntropyOf_pair (μ := μ) hY₂ hC
  haveI : ShannonInformation.FiniteEntropyOf (⟨Y₁, C⟩ : Ω → T₁ × V) μ :=
    ShannonInformation.finiteEntropyOf_pair (μ := μ) hY₁ hC
  rw [condInteractionInfo, condInteractionInfo,
    ShannonInformation.condMutualInfo_eq' hX hY₁ hC μ,
    ShannonInformation.condMutualInfo_eq' (Z := ⟨Y₂, C⟩) hX hY₁ (hY₂.prodMk hC) μ,
    ShannonInformation.condMutualInfo_eq' hX hY₂ hC μ,
    ShannonInformation.condMutualInfo_eq' (Z := ⟨Y₁, C⟩) hX hY₂ (hY₁.prodMk hC) μ,
    condEntropy_pair_rotate hX hY₁ hY₂ hC]
  ring

/-- The cyclic rotation `I (Y₁; Y₂; X | C) = I (X; Y₁; Y₂ | C)`. -/
lemma condInteractionInfo_rotate (hX : Measurable X) (hY₁ : Measurable Y₁)
    (hY₂ : Measurable Y₂) (hC : Measurable C) :
    condInteractionInfo Y₁ Y₂ X C μ = condInteractionInfo X Y₁ Y₂ C μ := by
  rw [condInteractionInfo_comm hY₁ hY₂ X C μ,
    condInteractionInfo_swap hY₂ hY₁ hX hC,
    condInteractionInfo_comm hY₂ hX Y₁ C μ,
    condInteractionInfo_swap hX hY₂ hY₁ hC]

/-- **Lemma 5.4**, equation (5.6) — the exact statement

`H (X | C) = H (X | Y₁, C) + H (X | Y₂, C) − H (X | Y₁, Y₂, C) + I (Y₁; Y₂; X | C)`.

The paper's triple `(Y₁, Y₂, C)` is the right-nested pair `⟨Y₁, ⟨Y₂, C⟩⟩`, which is the
grouping the vendored chain rules produce.

Paper node: `Lemma 5.4` -/
theorem condEntropy_eq_of_pair (hX : Measurable X) (hY₁ : Measurable Y₁)
    (hY₂ : Measurable Y₂) (hC : Measurable C) :
    H[X | C ; μ] = H[X | ⟨Y₁, C⟩ ; μ] + H[X | ⟨Y₂, C⟩ ; μ] - H[X | ⟨Y₁, ⟨Y₂, C⟩⟩ ; μ]
      + condInteractionInfo Y₁ Y₂ X C μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [condInteractionInfo]
  haveI : ShannonInformation.FiniteEntropyOf (⟨Y₂, C⟩ : Ω → T₂ × V) μ :=
    ShannonInformation.finiteEntropyOf_pair (μ := μ) hY₂ hC
  rw [condInteractionInfo_rotate hX hY₁ hY₂ hC, condInteractionInfo,
    ShannonInformation.condMutualInfo_eq' hX hY₁ hC μ,
    ShannonInformation.condMutualInfo_eq' (Z := ⟨Y₂, C⟩) hX hY₁ (hY₂.prodMk hC) μ]
  ring

/-- **Lemma 5.4**, equation (5.5) — the inequality form

`H (X | C) ≤ H (X | Y₁, C) + H (X | Y₂, C) + I (Y₁; Y₂ | C)`,

deduced from (5.6) exactly as the paper's (5.8) does it: drop `−H (X | Y₁, Y₂, C)` and
`−I (Y₁; Y₂ | X, C)` by nonnegativity.

Paper node: `Lemma 5.4` -/
theorem condEntropy_le_of_pair (hX : Measurable X) (hY₁ : Measurable Y₁)
    (hY₂ : Measurable Y₂) (hC : Measurable C) :
    H[X | C ; μ] ≤ H[X | ⟨Y₁, C⟩ ; μ] + H[X | ⟨Y₂, C⟩ ; μ] + I[Y₁ : Y₂ | C ; μ] := by
  have h := condEntropy_eq_of_pair (μ := μ) hX hY₁ hY₂ hC
  rw [condInteractionInfo] at h
  have h1 : (0 : ℝ) ≤ H[X | ⟨Y₁, ⟨Y₂, C⟩⟩ ; μ] := condEntropy_nonneg _ _ _
  have h2 : (0 : ℝ) ≤ I[Y₁ : Y₂ | ⟨X, C⟩ ; μ] :=
    ShannonInformation.condMutualInfo_nonneg hY₁ hY₂
  linarith

end Lemma54

/-! ## Definition 5.5 — the polar -/

section Polar

variable {I : Type*}

/-- **Definition 5.5** — the **polar** of a subfamily `F` of a nonempty power set `P⁺I`:

`F° = {B ∈ P⁺I : ∀ A ∈ F. A ∩ B ≠ ∅}`,  equation (5.9).

The nonempty intersection is spelled "some index of `A` lies in `B`", exactly as `contrib`
spells it in `Condensation/Model.lean`, so that no `DecidableEq I` is needed;
`mem_polar_iff` gives back the paper's literal `A ∩ B ≠ ∅`.

Paper node: `Definition 5.5` -/
def polar (F : Set (PPlus I)) : Set (PPlus I) := {B | ∀ A ∈ F, ∃ i ∈ A.toFinset, i ∈ B}

@[simp] lemma mem_polar {F : Set (PPlus I)} {B : PPlus I} :
    B ∈ polar F ↔ ∀ A ∈ F, ∃ i ∈ A.toFinset, i ∈ B := Iff.rfl

/-- `polar` is literally the paper's `{B : ∀ A ∈ F. A ∩ B ≠ ∅}` of (5.9). -/
lemma mem_polar_iff [DecidableEq I] {F : Set (PPlus I)} {B : PPlus I} :
    B ∈ polar F ↔ ∀ A ∈ F, (A.toFinset ∩ B.toFinset).Nonempty := by
  simp [polar, Finset.Nonempty, Finset.mem_inter]

/-- The polar of any family is **upward-closed**.  This is what puts the labels of Theorem
5.8's intersection tree in the lattice of upward-closed subsets of `P⁺I`. -/
lemma isUpperSet_polar (F : Set (PPlus I)) : IsUpperSet (polar F) := by
  rintro B C hBC hB A hA
  obtain ⟨i, hiA, hiB⟩ := hB A hA
  exact ⟨i, hiA, hBC hiB⟩

/-- Taking polars is **antitone**: a larger family has a smaller polar.  This is the
"we can make `G` better approximate `{C : C ⊇ A}` by picking a larger `F`" of the
discussion preceding Theorem 5.8. -/
lemma polar_antitone : Antitone (polar (I := I)) := by
  intro F F' h B hB A hA
  exact hB A (h hA)

/-- The polar of a singleton is the contributing family `{C : B ∩ C ≠ ∅}` of (3.5) — the
identity that makes the leaf labels of Theorem 5.8's tree `contrib`s. -/
@[simp] lemma polar_singleton (A : PPlus I) : polar {A} = contrib A.toFinset := by
  ext B; simp [contrib]

/-- The polar is the intersection of the contributing families of its members. -/
lemma polar_eq_iInter (F : Set (PPlus I)) :
    polar F = ⋂ A ∈ F, contrib A.toFinset := by
  ext B; simp [contrib]

@[simp] lemma polar_empty : polar (∅ : Set (PPlus I)) = Set.univ := by
  ext B; simp

end Polar

/-! ### Definition 5.6: the tree and its labels -/

/-- Definition 5.6(1)'s directed binary tree: every vertex either has no parents (a *leaf*)
or exactly two parents (an *internal* vertex), and there is one vertex, the root, to which
every vertex has a unique directed path.  Read the paper's "parents of `u`" as the
constructor arguments `l`, `r` of `node l r`.

Being inductive, `ITree` ranges over exactly the **finite** trees.  That is a disclosed
reading of Definition 5.6, which as printed carries no finiteness or well-foundedness
clause (`notes/paper-errata.md` entry 17); it is licensed by Theorem 5.8, whose conclusion
(5.14) is a finite sum over the leaves and internal vertices of the tree, and so has
content only for a finite tree.

Paper node: `Definition 5.6` -/
inductive ITree (α : Type*) where
  | leaf (a : α) : ITree α
  | node (l r : ITree α) : ITree α
  deriving Repr

namespace ITree

variable {α : Type*}

/-- Definition 5.6(2)–(3): the label of the root vertex, computed from the tree.  Equation
(5.10), `ℓ(u) = ℓ(v) ⊓ ℓ(w)` for `u` internal with parents `v`, `w`, holds by definition.

Paper node: `Definition 5.6` -/
def label [SemilatticeInf α] : ITree α → α
  | leaf a => a
  | node l r => l.label ⊓ r.label

@[simp] lemma label_leaf [SemilatticeInf α] (a : α) : (leaf a).label = a := rfl

@[simp] lemma label_node [SemilatticeInf α] (l r : ITree α) :
    (node l r).label = l.label ⊓ r.label := rfl

/-- The labels of the leaves, in left-to-right order.  A `List`, not a `Finset`: the same
label may decorate several leaves. -/
def leaves : ITree α → List α
  | leaf a => [a]
  | node l r => l.leaves ++ r.leaves

@[simp] lemma leaves_leaf (a : α) : (leaf a).leaves = [a] := rfl

@[simp] lemma leaves_node (l r : ITree α) : (node l r).leaves = l.leaves ++ r.leaves := rfl

@[simp] lemma leaves_ne_nil (t : ITree α) : t.leaves ≠ [] := by
  induction t with
  | leaf a => simp
  | node l r ihl _ => simp [ihl]

/-- All vertices of the tree, presented as the subtrees they root; the root comes first. -/
def subtrees : ITree α → List (ITree α)
  | leaf a => [leaf a]
  | node l r => node l r :: (l.subtrees ++ r.subtrees)

@[simp] lemma subtrees_leaf (a : α) : (leaf a).subtrees = [leaf a] := rfl

@[simp] lemma subtrees_node (l r : ITree α) :
    (node l r).subtrees = node l r :: (l.subtrees ++ r.subtrees) := rfl

@[simp] lemma mem_subtrees_self (t : ITree α) : t ∈ t.subtrees := by
  cases t with
  | leaf a => simp
  | node l r => simp

/-- Definition 5.6's **family of intersections** (5.11): one entry `(ℓ(v), ℓ(w), ℓ(u))` for
each internal vertex `u` with parents `v`, `w`.  A `List`, not a `Finset`, because the
paper warns that the same intersection may appear more than once in the family.

Paper node: `Definition 5.6` -/
def intersections [SemilatticeInf α] : ITree α → List (α × α × α)
  | leaf _ => []
  | node l r => (l.label, r.label, l.label ⊓ r.label) :: (l.intersections ++ r.intersections)

@[simp] lemma intersections_leaf [SemilatticeInf α] (a : α) :
    (leaf a).intersections = [] := rfl

@[simp] lemma intersections_node [SemilatticeInf α] (l r : ITree α) :
    (node l r).intersections =
      (l.label, r.label, (node l r).label) :: (l.intersections ++ r.intersections) := rfl

/-! ### Proposition 5.7's description of the labels -/

/-- Folding `⊓` into a running accumulator factors the accumulator out. -/
private lemma foldr_inf_top [SemilatticeInf α] [OrderTop α] (L : List α) (x : α) :
    L.foldr (· ⊓ ·) x = L.foldr (· ⊓ ·) ⊤ ⊓ x := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, inf_assoc]

/-- Proposition 5.7's description of the extension: the label of a vertex is the meet of
the labels of the leaves which are its ancestors.  Read at each subtree — that is, at each
vertex — this is exactly the paper's clause.

Paper node: `Proposition 5.7` -/
theorem label_eq_leaves_foldr [SemilatticeInf α] [OrderTop α] (t : ITree α) :
    t.label = t.leaves.foldr (· ⊓ ·) ⊤ := by
  induction t with
  | leaf a => simp
  | node l r ihl ihr =>
    rw [label_node, leaves_node, List.foldr_append, foldr_inf_top, ihl, ihr]

/-! ### Definition 5.6: "on an intersection-closed collection `M`" -/

/-- `t` is an intersection tree **on `M`** (Definition 5.6): all its leaf labels lie in
`M`.  When `M` is closed under `⊓` this puts *every* vertex's label in `M`
(`ITree.label_mem_of_labelsIn`), which is what the definition asks for.

Paper node: `Definition 5.6` -/
def LabelsIn (M : Set α) (t : ITree α) : Prop := ∀ a ∈ t.leaves, a ∈ M

@[simp] lemma labelsIn_leaf {M : Set α} (a : α) : (leaf a).LabelsIn M ↔ a ∈ M := by
  simp [LabelsIn]

@[simp] lemma labelsIn_node {M : Set α} (l r : ITree α) :
    (node l r).LabelsIn M ↔ l.LabelsIn M ∧ r.LabelsIn M := by
  simp only [LabelsIn, leaves_node, List.mem_append]
  constructor
  · exact fun h => ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  · rintro ⟨hl, hr⟩ a (ha | ha)
    · exact hl a ha
    · exact hr a ha

/-- If `M` is closed under `⊓` and the leaf labels lie in `M`, then the label of *every*
vertex lies in `M`.  This is the content of Definition 5.6's "intersection tree on an
intersection-closed collection `M`"; the node carrier for that clause is `ITree.LabelsIn`,
and this is the fact that makes carrying it on the leaves alone equivalent. -/
lemma label_mem_of_labelsIn [SemilatticeInf α] {M : Set α}
    (hM : ∀ a ∈ M, ∀ b ∈ M, a ⊓ b ∈ M) (t : ITree α) (h : t.LabelsIn M) :
    ∀ s ∈ t.subtrees, s.label ∈ M := by
  induction t with
  | leaf a =>
    intro s hs
    rw [subtrees_leaf, List.mem_singleton] at hs
    subst hs
    simpa using h
  | node l r ihl ihr =>
    rw [labelsIn_node] at h
    intro s hs
    rw [subtrees_node, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · rw [label_node]
      exact hM _ (ihl h.1 l (mem_subtrees_self l)) _ (ihr h.2 r (mem_subtrees_self r))
    · exact ihl h.1 s hs
    · exact ihr h.2 s hs

/-- What (5.11)'s entries look like: for every internal vertex, the two children's labels
lie in `M` and the vertex's own label is their meet.  This is `label_mem_of_labelsIn` read
along `intersections`, and it is what lets Corollary 5.9's second form (5.22) feed each
entry of the family of intersections to Proposition 4.10, whose hypothesis is that the two
families are upward-closed. -/
lemma intersections_spec [SemilatticeInf α] {M : Set α}
    (hM : ∀ a ∈ M, ∀ b ∈ M, a ⊓ b ∈ M) (t : ITree α) (h : t.LabelsIn M) :
    ∀ p ∈ t.intersections, p.1 ∈ M ∧ p.2.1 ∈ M ∧ p.2.2 = p.1 ⊓ p.2.1 := by
  induction t with
  | leaf a => simp
  | node l r ihl ihr =>
    rw [labelsIn_node] at h
    intro p hp
    rw [intersections_node, List.mem_cons, List.mem_append] at hp
    rcases hp with rfl | hp | hp
    · exact ⟨label_mem_of_labelsIn hM l h.1 l (mem_subtrees_self l),
        label_mem_of_labelsIn hM r h.2 r (mem_subtrees_self r), rfl⟩
    · exact ihl h.1 p hp
    · exact ihr h.2 p hp

end ITree

/-! ### Proposition 5.7 -/

/-- A binary tree carrying a label at **every** vertex: an arbitrary candidate for the
function `ℓ : V → M` of Definition 5.6(2), before (5.10) is imposed. -/
inductive LTree (α : Type*) where
  | leaf (a : α) : LTree α
  | node (a : α) (l r : LTree α) : LTree α
  deriving Repr

namespace LTree

variable {α : Type*}

/-- The label the candidate `ℓ` assigns to the root vertex. -/
def rootLabel : LTree α → α
  | leaf a => a
  | node a _ _ => a

@[simp] lemma rootLabel_leaf (a : α) : (leaf a).rootLabel = a := rfl

@[simp] lemma rootLabel_node (a : α) (l r : LTree α) : (node a l r).rootLabel = a := rfl

/-- Forget the internal labels: the underlying directed binary tree `(V, E)` together with
the leaf labelling `ℓ̃` of Proposition 5.7. -/
def erase : LTree α → ITree α
  | leaf a => .leaf a
  | node _ l r => .node l.erase r.erase

@[simp] lemma erase_leaf (a : α) : (leaf a).erase = .leaf a := rfl

@[simp] lemma erase_node (a : α) (l r : LTree α) :
    (node a l r).erase = .node l.erase r.erase := rfl

/-- Definition 5.6(3): equation (5.10) holds at every internal vertex. -/
def IsIntersectionTree [SemilatticeInf α] : LTree α → Prop
  | leaf _ => True
  | node a l r => a = l.rootLabel ⊓ r.rootLabel ∧ l.IsIntersectionTree ∧ r.IsIntersectionTree

@[simp] lemma isIntersectionTree_leaf [SemilatticeInf α] (a : α) :
    (leaf a).IsIntersectionTree := trivial

@[simp] lemma isIntersectionTree_node [SemilatticeInf α] (a : α) (l r : LTree α) :
    (node a l r).IsIntersectionTree ↔
      a = l.rootLabel ⊓ r.rootLabel ∧ l.IsIntersectionTree ∧ r.IsIntersectionTree :=
  Iff.rfl

/-- Definition 5.6(2) at the level of a candidate labelling: `ℓ` takes **every** vertex
into the intersection-closed collection `M`, i.e. `ℓ` is a function `V → M`.  This is the
`LTree` counterpart of `ITree.LabelsIn`, which carries the same condition on the leaves
alone; `ITree.label_mem_of_labelsIn` is what makes the two agree on the canonical
decoration (`ITree.labelsIn_decorate`). -/
def LabelsIn (M : Set α) : LTree α → Prop
  | leaf a => a ∈ M
  | node a l r => a ∈ M ∧ l.LabelsIn M ∧ r.LabelsIn M

@[simp] lemma labelsIn_leaf {M : Set α} (a : α) : (leaf a).LabelsIn M ↔ a ∈ M := Iff.rfl

@[simp] lemma labelsIn_node {M : Set α} (a : α) (l r : LTree α) :
    (node a l r).LabelsIn M ↔ a ∈ M ∧ l.LabelsIn M ∧ r.LabelsIn M := Iff.rfl

end LTree

namespace ITree

variable {α : Type*}

/-- The canonical labelling whose existence and uniqueness is Proposition 5.7: label every
vertex by the meet of the labels of the leaves which are its ancestors, i.e. by
`ITree.label` of the subtree it roots.  Not itself a printed node — Proposition 5.7's
carriers are `existsUnique_intersectionTree`, `eq_decorate_of_isIntersectionTree` and
`ITree.label_eq_leaves_foldr`. -/
def decorate [SemilatticeInf α] : ITree α → LTree α
  | leaf a => .leaf a
  | node l r => .node (l.label ⊓ r.label) l.decorate r.decorate

@[simp] lemma decorate_leaf [SemilatticeInf α] (a : α) : (leaf a).decorate = .leaf a := rfl

@[simp] lemma decorate_node [SemilatticeInf α] (l r : ITree α) :
    (node l r).decorate = .node (node l r).label l.decorate r.decorate := rfl

@[simp] lemma decorate_erase [SemilatticeInf α] (t : ITree α) : t.decorate.erase = t := by
  induction t with
  | leaf a => rfl
  | node l r ihl ihr => rw [decorate_node, LTree.erase_node, ihl, ihr]

@[simp] lemma rootLabel_decorate [SemilatticeInf α] (t : ITree α) :
    t.decorate.rootLabel = t.label := by
  cases t with
  | leaf a => rfl
  | node l r => rfl

lemma isIntersectionTree_decorate [SemilatticeInf α] (t : ITree α) :
    t.decorate.IsIntersectionTree := by
  induction t with
  | leaf a => trivial
  | node l r ihl ihr =>
    refine ⟨?_, ihl, ihr⟩
    rw [rootLabel_decorate, rootLabel_decorate]

/-- The canonical decoration of a tree whose *leaf* labels lie in an intersection-closed
`M` labels **every** vertex by a member of `M`.  This is `ITree.label_mem_of_labelsIn` read
along `decorate`, and it is the existence half of Proposition 5.7's "a function
`ℓ : V → M`". -/
lemma labelsIn_decorate [SemilatticeInf α] {M : Set α}
    (hM : ∀ a ∈ M, ∀ b ∈ M, a ⊓ b ∈ M) (t : ITree α) (h : t.LabelsIn M) :
    t.decorate.LabelsIn M := by
  induction t with
  | leaf a => simpa using h
  | node l r ihl ihr =>
    have h' := h
    rw [labelsIn_node] at h'
    exact ⟨label_mem_of_labelsIn hM (node l r) h _ (mem_subtrees_self _), ihl h'.1, ihr h'.2⟩

end ITree

/-- The uniqueness half of Proposition 5.7, in the form the induction wants: a labelling
of every vertex satisfying (5.10) everywhere *is* the canonical one. -/
lemma LTree.eq_decorate_erase {α : Type*} [SemilatticeInf α] {d : LTree α}
    (hd : d.IsIntersectionTree) : d = d.erase.decorate := by
  induction d with
  | leaf a => rfl
  | node a l r ihl ihr =>
    obtain ⟨ha, hl, hr⟩ := hd
    have hl' := ihl hl
    have hr' := ihr hr
    have hla : l.rootLabel = l.erase.label := by rw [hl']; simp
    have hra : r.rootLabel = r.erase.label := by rw [hr']; simp
    rw [LTree.erase_node, ITree.decorate_node, ITree.label_node, ha, hla, hra, ← hl', ← hr']

/-- **Proposition 5.7**, uniqueness: an extension of the leaf labelling `ℓ̃` to a labelling
`ℓ` of every vertex satisfying (5.10) is *the* canonical one, which assigns to each
internal vertex the meet of the labels of the leaves which are its ancestors.

Paper node: `Proposition 5.7` -/
theorem eq_decorate_of_isIntersectionTree {α : Type*} [SemilatticeInf α] {t : ITree α}
    {d : LTree α} (herase : d.erase = t) (hd : d.IsIntersectionTree) : d = t.decorate := by
  subst herase
  exact LTree.eq_decorate_erase hd

/-- The `M`-free machinery form of Proposition 5.7: over the *ambient* lattice `α`, the
labelling of every vertex which restricts to the given leaf labelling and satisfies (5.10)
exists and is unique.  Proposition 5.7's actual claim is the `M`-version
(`existsUnique_intersectionTree`), whose uniqueness half is read off from this one — the
extra "every label lies in `M`" conjunct only narrows the candidate set, and any candidate
is already `t.decorate` by `eq_decorate_of_isIntersectionTree`. -/
lemma existsUnique_intersectionTree_ambient {α : Type*} [SemilatticeInf α] (t : ITree α) :
    ∃! d : LTree α, d.erase = t ∧ d.IsIntersectionTree :=
  ⟨t.decorate, ⟨t.decorate_erase, t.isIntersectionTree_decorate⟩,
    fun _ hd => eq_decorate_of_isIntersectionTree hd.1 hd.2⟩

/-- **Proposition 5.7**: given a directed binary tree `(V, E)`, an intersection-closed
collection of sets `M` (`hM`), and a labelling `ℓ̃` of the leaves of `V` **by members of
`M`** (`ht`) — the tree together with `ℓ̃` being an `ITree` with `ITree.LabelsIn M` — there
is a unique extension of `ℓ̃` to a function **`ℓ : V → M`** making `(V, E, ℓ)` an
intersection tree.  `LTree.LabelsIn M` is the "`ℓ` is a function `V → M`" clause of
Definition 5.6(2), so the conjunction is exactly the paper's conclusion.  See
`ITree.label_eq_leaves_foldr` for the paper's description of that extension, and
`existsUnique_intersectionTree_ambient` for the `M`-free form the uniqueness half comes
from.

Paper node: `Proposition 5.7` -/
theorem existsUnique_intersectionTree {α : Type*} [SemilatticeInf α] {M : Set α}
    (hM : ∀ a ∈ M, ∀ b ∈ M, a ⊓ b ∈ M) (t : ITree α) (ht : t.LabelsIn M) :
    ∃! d : LTree α, d.erase = t ∧ d.IsIntersectionTree ∧ d.LabelsIn M :=
  ⟨t.decorate,
    ⟨t.decorate_erase, t.isIntersectionTree_decorate, ITree.labelsIn_decorate hM t ht⟩,
    fun _ hd => eq_decorate_of_isIntersectionTree hd.1 hd.2.1⟩

/-! ### An intersection-closed collection of sets -/

/-- The upward-closed subsets of a preorder form an intersection-closed collection of sets,
in the sense of Definition 5.6. -/
lemma isUpperSet_inf_closed {β : Type*} [Preorder β] :
    ∀ s ∈ {s : Set β | IsUpperSet s}, ∀ t ∈ {s : Set β | IsUpperSet s},
      s ⊓ t ∈ {s : Set β | IsUpperSet s} := by
  intro s hs t ht
  simp only [Set.mem_setOf_eq] at hs ht ⊢
  exact hs.inter ht

/-! ### Regression examples -/

example :
    (ITree.node (.leaf ({true} : Set Bool)) (.leaf ({true, false} : Set Bool))).label
      = ({true} : Set Bool) := by
  ext b
  simp only [ITree.label_node, ITree.label_leaf, Set.inf_eq_inter, Set.mem_inter_iff,
    Set.mem_singleton_iff, Set.mem_insert_iff]
  tauto

/-- A three-leaf tree has two internal vertices, hence two entries in its family of
intersections — one per internal vertex, as (5.11) prescribes. -/
example (a b c : Set Bool) :
    (ITree.node (.leaf a) (ITree.node (.leaf b) (.leaf c))).intersections.length = 2 := rfl

example (a b c : Set Bool) :
    (ITree.node (.leaf a) (ITree.node (.leaf b) (.leaf c))).leaves = [a, b, c] := rfl

example (a b c : Set Bool) :
    (ITree.node (.leaf a) (ITree.node (.leaf b) (.leaf c))).subtrees.length = 5 := rfl

/-- The root label of Theorem 5.8's intersection tree is the polar `G = F°`.  This is why
(5.13) and (5.14) have `Z_G` on the left: the root's label is the meet of all the leaf
labels, and the meet of `{C : B ∩ C ≠ ∅}` over `B ∈ F` is exactly `F°` (`polar_eq_iInter`). -/
lemma ITree.label_eq_polar {I : Type*} [Finite I] {F : Set (PPlus I)}
    {T : ITree (Set (PPlus I))}
    (hleaves : (T.leaves : Multiset (Set (PPlus I)))
      = (famFinset F).val.map fun B => contrib B.toFinset) :
    T.label = polar F := by
  rw [ITree.label_eq_leaves_foldr, ← Multiset.coe_fold_r, ← Multiset.inf, hleaves,
    ← Finset.inf_def, Finset.inf_set_eq_iInter, polar_eq_iInter]
  simp

/-! ## Theorem 5.8, Corollary 5.9, Corollary 5.10

### Definition 4.12's amalgamation is the ambient data

Everything below is stated about an amalgamation `Am : LatentAmalgamation L₁ L₂`
(Definition 4.12) of two latent variable models for one random variable model `M`: `L₁`
supplies the paper's `Y` family, `L₂` supplies its `Z` family, and `Am.Λ₀` is the single
probability space on which the paper reads all three of `X`, `Y` and `Z` — "when we write
random variables `X`, `Y`, or `Z`, we will mean their pullbacks to `Λ₀` under the
appropriate maps".  Nothing has to be re-spelled locally, because the two latent variable
models `Am.lat₁` and `Am.lat₂` derived from the structure have `Am.Λ₀` as their underlying
probability space *definitionally*:

* `Y_⊇A` is `Am.lat₁.jointAbove A.toFinset` and `Z_G` is `Am.lat₂.jointOn G`, Definition
  3.4's joint variables of those two models;
* `X_B` is `Am.lat₁.pullbackJoint B.toFinset`, the pullback of `M.joint B.toFinset` along
  `Am.π₁` (`dd:pullback`);
* `ϱ_Y(B) = H (Y_⊇B | X_B)` is `Am.lat₁.reconScore B.toFinset`, Definition 3.3's
  reconstruction score itself;
* Definition 4.8's ordered Markov condition on the `Z` family is
  `RVModel.OrderedMarkov Am.rv₂` (`Condensation/Perfect.lean`).

Definition 3.2's two contribution conditions are *fields* of `LatentAmalgamation`
(`Am.contributes₁`, `Am.contributes₂`), so no statement below carries them as hypotheses.
The `Z`-side one is the one the proof actually uses, at (5.18), where `X_B` has to be
recognised as almost everywhere a function of `Z_{∩B}`; the `Y`-side one is part of the
data of an amalgamation, not something (5.13) needs.  Note that `Am.contributes₂` is
phrased through `Am.π₂` while `X_B` here is pulled back along `Am.π₁`; the two maps agree
almost everywhere by the field `Am.comm`, which is exactly the role that field exists to
play, so nothing is lost.

Nor is any generality lost by quantifying over an amalgamation rather than over three bare
families of variables on a common space carrying the two contribution conditions: such
families *are* an amalgamation, of `M = (Λ₀, X)` by `L₁ = (Λ₀, Y, id)` and
`L₂ = (Λ₀, Z, id)` with identity morphisms. -/

section Comparison

variable {I : Type w} [Finite I] {M : RVModel.{u, v, w} I}
  {L₁ : LatentModel.{u, v, w, u₁, v₁} M} {L₂ : LatentModel.{u, v, w, u₂, v₂} M}
  (Am : LatentAmalgamation.{u, v, w, u₀, u₁, v₁, u₂, v₂} L₁ L₂)

/-! ### The induction of (5.15)–(5.16)

The proof of (5.14) is an induction over the tree, done here for an arbitrary variable `X`
on `Λ₀` — the paper's `Y_⊇A` plays no role in it beyond being *some* variable, and keeping
it abstract is what makes the induction hypothesis usable.  Each step is Lemma 5.4
(`condEntropy_eq_of_pair`) at `C = Z_{ℓ(v)}`, `Y₁ = Z_{ℓ(s)}`, `Y₂ = Z_{ℓ(t)}`, followed by
three identifications of conditioning variables, which are the two lemmas below.  Note that
the tree's upper-set hypothesis is *not* used for (5.14): it is Corollary 5.9's (5.22) that
needs it.

`X` is spelled `Am.Λ₀ → S` rather than `Am.lat₁.Λ → S` throughout, so that the finiteness
instances all sit at one spelling of the sample space — see
`LatentAmalgamation.finiteEntropyOf'` for why that matters. -/

section Induction

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  {X : Am.Λ₀ → S} (hX : Measurable X)
  (hfX : ShannonInformation.FiniteEntropyOf X Am.P₀)

include hX hfX

/-- Conditioning on `(Z_F, Z_G)` with `G ⊆ F` is conditioning on `Z_F`, because `Z_G` is
then a coordinate projection of `Z_F`.  This is the step
`H (Y_⊇A | Z_{ℓ(s)}, Z_{ℓ(v)}) = H (Y_⊇A | Z_{ℓ(s)})` of (5.16), where
`ℓ(v) = ℓ(s) ⊓ ℓ(t) ⊆ ℓ(s)`. -/
private lemma condEntropy_jointOn_pair_of_subset {F G : Set (PPlus I)} (h : G ⊆ F) :
    H[X | ⟨Am.lat₂.jointOn F, Am.lat₂.jointOn G⟩ ; Am.P₀]
      = H[X | Am.lat₂.jointOn F ; Am.P₀] :=
  condEntropy_congr_of_aeFunctionOf (hfX := hfX)
    (hfW := Am.finiteEntropyOf' ((Am.lat₂.L.measurable_jointOn F).prodMk
      (Am.lat₂.L.measurable_jointOn G)))
    (hfV := Am.finiteEntropyOf' (Am.lat₂.L.measurable_jointOn F))
    hX
    ((Am.lat₂.L.measurable_jointOn F).prodMk (Am.lat₂.L.measurable_jointOn G))
    (Am.lat₂.L.measurable_jointOn F)
    (AEFunctionOf.of_functionOf (functionOf_comp (f := Prod.fst) measurable_fst))
    (aeFunctionOf_self.prodMk (Am.lat₂.L.aeFunctionOf_jointOn_mono h _))

/-- Conditioning on `(Z_F, Z_G, Z_K)` with `K ⊆ F ∪ G` is conditioning on `Z_{F ∪ G}`: the
triple and the joint over the union are a.e. functions of each other
(`RVModel.functionOf_jointOn_union` one way, `RVModel.functionOf_jointOn_mono` the other).
This is the step `H (Y_⊇A | Z_{ℓ(s)}, Z_{ℓ(t)}, Z_{ℓ(v)}) = H (Y_⊇A | Z_{ℓ(s) ∪ ℓ(t)})`
of (5.16). -/
private lemma condEntropy_jointOn_triple {F G K : Set (PPlus I)} (hK : K ⊆ F ∪ G) :
    H[X | ⟨Am.lat₂.jointOn F, ⟨Am.lat₂.jointOn G, Am.lat₂.jointOn K⟩⟩ ; Am.P₀]
      = H[X | Am.lat₂.jointOn (F ∪ G) ; Am.P₀] := by
  refine condEntropy_congr_of_aeFunctionOf (hfX := hfX)
    (hfW := Am.finiteEntropyOf' ((Am.lat₂.L.measurable_jointOn F).prodMk
      ((Am.lat₂.L.measurable_jointOn G).prodMk (Am.lat₂.L.measurable_jointOn K))))
    (hfV := Am.finiteEntropyOf' (Am.lat₂.L.measurable_jointOn (F ∪ G)))
    hX
    ((Am.lat₂.L.measurable_jointOn F).prodMk
      ((Am.lat₂.L.measurable_jointOn G).prodMk (Am.lat₂.L.measurable_jointOn K)))
    (Am.lat₂.L.measurable_jointOn (F ∪ G)) ?_ ?_
  · exact AEFunctionOf.trans
      (AEFunctionOf.of_functionOf
        ⟨fun p => (p.1, p.2.1), measurable_fst.prodMk (measurable_fst.comp measurable_snd),
          fun _ => rfl⟩)
      (AEFunctionOf.of_functionOf (Am.lat₂.L.functionOf_jointOn_union F G))
  · exact (Am.lat₂.L.aeFunctionOf_jointOn_mono Set.subset_union_left _).prodMk
      ((Am.lat₂.L.aeFunctionOf_jointOn_mono Set.subset_union_right _).prodMk
        (Am.lat₂.L.aeFunctionOf_jointOn_mono hK _))

/-- **Equation (5.15)** at every vertex, which is the induction (5.16) proves: the tree form
of (5.14), with the root label in place of the polar and an arbitrary `X` in place of
`Y_⊇A`.  A leaf is (5.15) read at a leaf, where both sides are `H (X | Z_{ℓ(v)})`; an
internal vertex is Lemma 5.4 plus the two identifications above. -/
private lemma condEntropy_eq_tree (T : ITree (Set (PPlus I))) :
    H[X | Am.lat₂.jointOn T.label ; Am.P₀]
      = (T.leaves.map fun s => H[X | Am.lat₂.jointOn s ; Am.P₀]).sum
        - (T.intersections.map fun p =>
            H[X | Am.lat₂.jointOn (p.1 ∪ p.2.1) ; Am.P₀]).sum
        + (T.intersections.map fun p =>
            condInteractionInfo (Am.lat₂.jointOn p.1) (Am.lat₂.jointOn p.2.1) X
              (Am.lat₂.jointOn p.2.2) Am.P₀).sum := by
  haveI := hfX
  induction T with
  | leaf a =>
    simp only [ITree.leaves_leaf, ITree.intersections_leaf, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, sub_zero]
    rfl
  | node l r ihl ihr =>
    haveI := Am.finiteEntropyOf' (Am.lat₂.L.measurable_jointOn l.label)
    haveI := Am.finiteEntropyOf' (Am.lat₂.L.measurable_jointOn r.label)
    haveI := Am.finiteEntropyOf' (Am.lat₂.L.measurable_jointOn (ITree.node l r).label)
    have key : H[X | Am.lat₂.jointOn (ITree.node l r).label ; Am.P₀]
        = H[X | ⟨Am.lat₂.jointOn l.label, Am.lat₂.jointOn (ITree.node l r).label⟩ ; Am.P₀]
          + H[X | ⟨Am.lat₂.jointOn r.label, Am.lat₂.jointOn (ITree.node l r).label⟩ ; Am.P₀]
          - H[X | ⟨Am.lat₂.jointOn l.label, ⟨Am.lat₂.jointOn r.label,
                Am.lat₂.jointOn (ITree.node l r).label⟩⟩ ; Am.P₀]
          + condInteractionInfo (Am.lat₂.jointOn l.label) (Am.lat₂.jointOn r.label) X
              (Am.lat₂.jointOn (ITree.node l r).label) Am.P₀ :=
      condEntropy_eq_of_pair (μ := Am.P₀) hX
        (Am.lat₂.L.measurable_jointOn l.label) (Am.lat₂.L.measurable_jointOn r.label)
        (Am.lat₂.L.measurable_jointOn (ITree.node l r).label)
    have e1 : H[X | ⟨Am.lat₂.jointOn l.label, Am.lat₂.jointOn (ITree.node l r).label⟩ ; Am.P₀]
        = H[X | Am.lat₂.jointOn l.label ; Am.P₀] :=
      condEntropy_jointOn_pair_of_subset Am hX hfX inf_le_left
    have e2 : H[X | ⟨Am.lat₂.jointOn r.label, Am.lat₂.jointOn (ITree.node l r).label⟩ ; Am.P₀]
        = H[X | Am.lat₂.jointOn r.label ; Am.P₀] :=
      condEntropy_jointOn_pair_of_subset Am hX hfX inf_le_right
    have e3 : H[X | ⟨Am.lat₂.jointOn l.label,
          ⟨Am.lat₂.jointOn r.label, Am.lat₂.jointOn (ITree.node l r).label⟩⟩ ; Am.P₀]
        = H[X | Am.lat₂.jointOn (l.label ∪ r.label) ; Am.P₀] :=
      condEntropy_jointOn_triple Am hX hfX (inf_le_left.trans Set.subset_union_left)
    rw [e1, e2, e3] at key
    simp only [ITree.leaves_node, ITree.intersections_node, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons]
    rw [key, ihl, ihr]
    ring

/-- `condEntropy_eq_tree` with the root label named separately, so that Theorem 5.8 can
substitute `ITree.label_eq_polar` without rewriting under the dependent type of the
conditioning variable. -/
private lemma condEntropy_eq_tree' (T : ITree (Set (PPlus I))) {G : Set (PPlus I)}
    (hG : T.label = G) :
    H[X | Am.lat₂.jointOn G ; Am.P₀]
      = (T.leaves.map fun s => H[X | Am.lat₂.jointOn s ; Am.P₀]).sum
        - (T.intersections.map fun p =>
            H[X | Am.lat₂.jointOn (p.1 ∪ p.2.1) ; Am.P₀]).sum
        + (T.intersections.map fun p =>
            condInteractionInfo (Am.lat₂.jointOn p.1) (Am.lat₂.jointOn p.2.1) X
              (Am.lat₂.jointOn p.2.2) Am.P₀).sum := by
  subst hG
  exact condEntropy_eq_tree Am hX hfX T

omit [Countable S] [MeasurableSingletonClass S] hX hfX in
/-- **Equation (5.17)**: the leaf sum of (5.14) is the sum over `F`, reindexed along
Theorem 5.8's bijection between the leaves of `T` and `(Z_{∩B})_{B ∈ F}`.  The multiset
hypothesis is exactly what makes this a `Finset` sum. -/
private lemma sum_leaves_eq (T : ITree (Set (PPlus I))) (F : Set (PPlus I))
    (hleaves : (T.leaves : Multiset (Set (PPlus I)))
      = (famFinset F).val.map fun B => contrib B.toFinset) :
    (T.leaves.map fun s => H[X | Am.lat₂.jointOn s ; Am.P₀]).sum
      = ∑ B ∈ famFinset F, H[X | Am.lat₂.jointOn (contrib B.toFinset) ; Am.P₀] := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, hleaves, Multiset.map_map, Finset.sum]
  rfl

omit [Countable S] [MeasurableSingletonClass S] hX hfX in
/-- **Equation (5.20)**: `I (Z_F; Z_G; X | Z_K) ≤ I (Z_F; Z_G | Z_K)`, because the
subtracted term `I (Z_F; Z_G | X, Z_K)` is nonnegative. -/
private lemma condInteractionInfo_jointOn_le (F G K : Set (PPlus I)) :
    condInteractionInfo (Am.lat₂.jointOn F) (Am.lat₂.jointOn G) X (Am.lat₂.jointOn K) Am.P₀
      ≤ I[Am.lat₂.jointOn F : Am.lat₂.jointOn G | Am.lat₂.jointOn K ; Am.P₀] := by
  haveI : ShannonInformation.FiniteEntropyOf (Am.lat₂.jointOn F) Am.P₀ :=
    Am.lat₂.L.finiteEntropy_jointOn F
  haveI : ShannonInformation.FiniteEntropyOf (Am.lat₂.jointOn G) Am.P₀ :=
    Am.lat₂.L.finiteEntropy_jointOn G
  haveI : IsProbabilityMeasure (α := Am.lat₂.Λ) Am.P₀ := Am.probP₀
  have h : (0 : ℝ) ≤ I[Am.lat₂.jointOn F : Am.lat₂.jointOn G | ⟨X, Am.lat₂.jointOn K⟩ ;
      Am.P₀] :=
    ShannonInformation.condMutualInfo_nonneg
      (Am.lat₂.L.measurable_jointOn F) (Am.lat₂.L.measurable_jointOn G)
  rw [condInteractionInfo]
  linarith

end Induction

/-! ### The `Z`-side contribution condition, at (5.18) -/

/-- **Equation (5.18)'s hypothesis**: `X_B` is almost everywhere a function of `Z_{∩B}`.

This is Definition 3.2's contribution condition for `L̃₂` (the field
`LatentAmalgamation.contributes₂`), assembled coordinatewise over `i ∈ B` and read through
`LatentAmalgamation.comm`: the field is phrased with `π̃₂` while `X_B` is pulled back along
`π̃₁`, and the two agree almost everywhere.  Theorem 5.8 uses the `Z`-side condition without
listing it as a hypothesis; the licence is Definition 4.12 (see the section preamble and
`Condensation/notes/paper-errata.md`). -/
private lemma aeFunctionOf_pullbackJoint (B : PPlus I) :
    AEFunctionOf (Am.lat₂.jointOn (contrib B.toFinset))
      (Am.lat₁.pullbackJoint B.toFinset) Am.P₀ := by
  have hcontrib : ∀ i : I, i ∈ B.toFinset →
      AEFunctionOf (Am.lat₂.jointOn (contrib B.toFinset)) (M.X i ∘ Am.π₁) Am.P₀ := by
    intro i hi
    refine AEFunctionOf.trans
      (Am.lat₂.L.aeFunctionOf_jointOn_mono (contribIdx_subset_contrib hi) _) ?_
    refine AEFunctionOf.congr_right (Am.contributes₂ i) ?_
    filter_upwards [Am.comm] with l hl
    exact congrArg (M.X i) hl
  exact AEFunctionOf.pi fun i : B.toFinset => hcontrib i.1 i.2

/-- **Equation (5.18)**: `H (Y_⊇A | Z_{∩B}) ≤ H (Y_⊇A | X_B)`. -/
private lemma condEntropy_jointContrib_le_pullbackJoint {S : Type*} [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S] {X : Am.Λ₀ → S} (hX : Measurable X)
    (hfX : ShannonInformation.FiniteEntropyOf X Am.P₀) (B : PPlus I) :
    H[X | Am.lat₂.jointOn (contrib B.toFinset) ; Am.P₀]
      ≤ H[X | Am.lat₁.pullbackJoint B.toFinset ; Am.P₀] :=
  condEntropy_le_condEntropy_of_aeFunctionOf (hfX := hfX)
    (hfW := Am.finiteEntropyOf' (Am.lat₂.L.measurable_jointOn (contrib B.toFinset)))
    (hfV := Am.finiteEntropyOf' (Am.lat₁.measurable_pullbackJoint B.toFinset))
    hX (Am.lat₂.L.measurable_jointOn (contrib B.toFinset))
    (Am.lat₁.measurable_pullbackJoint B.toFinset)
    (aeFunctionOf_pullbackJoint Am B)

/-! ### The tree hypothesis

Theorem 5.8 asks for an intersection tree `T` on the lattice of upward-closed subsets of
`P⁺I` "such that `ℓ` restricts to a bijection between the leaves of `T` and the set of sets
`{C ∈ P⁺I : B ∩ C ≠ ∅}` ranging over `B ∈ F`".  That is rendered as the multiset equation

`(T.leaves : Multiset _) = (famFinset F).val.map (fun B => contrib B.toFinset)`,

which says exactly that the leaf labels, *with multiplicity*, are the family
`(contrib B)_{B ∈ F}`.  Because `contrib` is injective on `P⁺I` (`contrib_injective`) the
right-hand multiset is duplicate-free, so this is a bijection and not merely a surjection —
and it is the form the sums of (5.13)/(5.14) actually consume.  The separate hypothesis
that the tree is on the lattice of upward-closed sets (`T.LabelsIn {s | IsUpperSet s}`) is
Definition 5.6's "on an intersection-closed collection `M`"; it is *implied* by the
multiset equation together with `isUpperSet_contrib`, and is carried anyway because it is
part of the printed statement. -/

set_option linter.unusedVariables false in
/-- **Theorem 5.8** (comparison of latent variable models), equation (5.13):

`H (Y_⊇A | Z_G) ≤ [∑_{B ∈ F} H (Y_⊇A | X_B)] + [∑_{v ∈ N} I (Z_{L(v)}; Z_{R(v)} | Z_{I(v)})]`

with `G = F°` the polar.  The sum over the tree's internal vertices `N` is the sum over
`T.intersections`, Definition 5.6's family of intersections (5.11): one entry
`(ℓ(v), ℓ(w), ℓ(u))` per internal vertex `u` with parents `v, w`, as a `List` because the
paper warns that the same intersection may occur more than once.

Paper node: `Theorem 5.8` -/
theorem condEntropy_jointAbove_le
    (A : PPlus I) (F : Set (PPlus I)) (T : ITree (Set (PPlus I)))
    (hupper : T.LabelsIn {s | IsUpperSet s})
    (hleaves : (T.leaves : Multiset (Set (PPlus I)))
      = (famFinset F).val.map fun B => contrib B.toFinset) :
    H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (polar F) ; Am.P₀]
      ≤ (∑ B ∈ famFinset F,
            H[Am.lat₁.jointAbove A.toFinset | Am.lat₁.pullbackJoint B.toFinset ; Am.P₀])
        + (T.intersections.map fun p =>
            I[Am.lat₂.jointOn p.1 : Am.lat₂.jointOn p.2.1 | Am.lat₂.jointOn p.2.2 ;
              Am.P₀]).sum := by
  have hX : Measurable (Am.lat₁.jointAbove A.toFinset) :=
    Am.lat₁.L.measurable_jointOn (above A.toFinset)
  have hfX := Am.finiteEntropyOf' hX
  -- (5.14).
  have heq : H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (polar F) ; Am.P₀]
      = (T.leaves.map fun s =>
            H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn s ; Am.P₀]).sum
        - (T.intersections.map fun p =>
            H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (p.1 ∪ p.2.1) ; Am.P₀]).sum
        + (T.intersections.map fun p =>
            condInteractionInfo (Am.lat₂.jointOn p.1) (Am.lat₂.jointOn p.2.1)
              (Am.lat₁.jointAbove A.toFinset) (Am.lat₂.jointOn p.2.2) Am.P₀).sum :=
    condEntropy_eq_tree' Am hX hfX T (ITree.label_eq_polar hleaves)
  -- (5.17): the leaf sum is the sum over `F`.
  have h517 : (T.leaves.map fun s =>
        H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn s ; Am.P₀]).sum
      = ∑ B ∈ famFinset F,
          H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (contrib B.toFinset) ; Am.P₀] :=
    sum_leaves_eq Am T F hleaves
  -- (5.18): each leaf term is bounded by the corresponding `H (Y_⊇A | X_B)`.
  have h518 : ∀ B ∈ famFinset F,
      H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (contrib B.toFinset) ; Am.P₀]
        ≤ H[Am.lat₁.jointAbove A.toFinset | Am.lat₁.pullbackJoint B.toFinset ; Am.P₀] := by
    intro B _
    exact condEntropy_jointContrib_le_pullbackJoint Am hX hfX B
  -- (5.19): the subtracted sum is nonnegative.
  have h519 : (0 : ℝ) ≤ (T.intersections.map fun p =>
      H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (p.1 ∪ p.2.1) ; Am.P₀]).sum := by
    refine List.sum_nonneg ?_
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, _, rfl⟩ := hx
    exact condEntropy_nonneg _ _ _
  -- (5.20): each interaction information is bounded by the conditional mutual information.
  have h520 : (T.intersections.map fun p =>
        condInteractionInfo (Am.lat₂.jointOn p.1) (Am.lat₂.jointOn p.2.1)
          (Am.lat₁.jointAbove A.toFinset) (Am.lat₂.jointOn p.2.2) Am.P₀).sum
      ≤ (T.intersections.map fun p =>
          I[Am.lat₂.jointOn p.1 : Am.lat₂.jointOn p.2.1 | Am.lat₂.jointOn p.2.2 ;
            Am.P₀]).sum :=
    List.sum_le_sum fun p _ => condInteractionInfo_jointOn_le Am p.1 p.2.1 p.2.2
  have hsum := Finset.sum_le_sum h518
  linarith

set_option linter.unusedVariables false in
/-- **Theorem 5.8**, equation (5.14) — the exact statement:

`H (Y_⊇A | Z_G) = [∑_{v ∈ L} H (Y_⊇A | Z_{I(v)})] − [∑_{v ∈ N} H (Y_⊇A | Z_{L(v) ∪ R(v)})]`
`                 + [∑_{v ∈ N} I (Z_{L(v)}; Z_{R(v)}; Y_⊇A | Z_{I(v)})]`.

The leaf sum ranges over `T.leaves` (the labels `I(v)` at the leaves `v ∈ L`) and the two
internal sums over `T.intersections`.

`hupper` is carried because it is part of the printed statement, but the induction of
(5.15)–(5.16) never consults it: nothing in the exact form depends on the labels being
upward-closed.  It is Corollary 5.9's second form (5.22) that needs it, to feed each entry
of the family of intersections to Proposition 4.10.  The same is true of (5.13).

Paper node: `Theorem 5.8` -/
theorem condEntropy_jointAbove_eq
    (A : PPlus I) (F : Set (PPlus I)) (T : ITree (Set (PPlus I)))
    (hupper : T.LabelsIn {s | IsUpperSet s})
    (hleaves : (T.leaves : Multiset (Set (PPlus I)))
      = (famFinset F).val.map fun B => contrib B.toFinset) :
    H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (polar F) ; Am.P₀]
      = (T.leaves.map fun s =>
            H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn s ; Am.P₀]).sum
        - (T.intersections.map fun p =>
            H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (p.1 ∪ p.2.1) ; Am.P₀]).sum
        + (T.intersections.map fun p =>
            condInteractionInfo (Am.lat₂.jointOn p.1) (Am.lat₂.jointOn p.2.1)
              (Am.lat₁.jointAbove A.toFinset) (Am.lat₂.jointOn p.2.2) Am.P₀).sum := by
  have hX : Measurable (Am.lat₁.jointAbove A.toFinset) :=
    Am.lat₁.L.measurable_jointOn (above A.toFinset)
  exact condEntropy_eq_tree' Am hX (Am.finiteEntropyOf' hX) T
    (ITree.label_eq_polar hleaves)

/-- **Equation (5.23)**: `H (Y_⊇A | X_B) ≤ H (Y_⊇B | X_B) = ϱ_Y(B)` whenever `B ⊆ A`.
The inequality is data processing for the conditioned variable — `above A ⊆ above B`, so
`Y_⊇A` is a coordinate projection of `Y_⊇B` — and the equality is `LatentModel.reconScore`
unfolded. -/
private lemma condEntropy_jointAbove_le_reconScore_term {A B : PPlus I} (hBA : B ≤ A) :
    H[Am.lat₁.jointAbove A.toFinset | Am.lat₁.pullbackJoint B.toFinset ; Am.P₀]
      ≤ Am.lat₁.reconScore B.toFinset := by
  haveI : IsProbabilityMeasure (α := Am.lat₁.Λ) Am.P₀ := Am.probP₀
  exact condEntropy_le_of_aeFunctionOf
    (hfX := Am.finiteEntropyOf' (Am.lat₁.L.measurable_jointOn (above B.toFinset)))
    (hfV := Am.finiteEntropyOf' (Am.lat₁.L.measurable_jointOn (above A.toFinset)))
    (hfW := Am.finiteEntropyOf' (Am.lat₁.measurable_pullbackJoint B.toFinset))
    (Am.lat₁.L.measurable_jointOn (above B.toFinset))
    (Am.lat₁.L.measurable_jointOn (above A.toFinset))
    (Am.lat₁.measurable_pullbackJoint B.toFinset)
    (Am.lat₁.L.aeFunctionOf_jointOn_mono (above_mono hBA) _)

/-- **Corollary 5.9**, equation (5.21): when every `B ∈ F` is a subset of `A`, the leaf
terms of (5.13) are bounded by the reconstruction scores `ϱ_Y(B)` of Definition 3.3.

Paper node: `Corollary 5.9` -/
theorem condEntropy_jointAbove_le_reconScore
    (A : PPlus I) (F : Set (PPlus I)) (hFA : ∀ B ∈ F, B ≤ A)
    (T : ITree (Set (PPlus I))) (hupper : T.LabelsIn {s | IsUpperSet s})
    (hleaves : (T.leaves : Multiset (Set (PPlus I)))
      = (famFinset F).val.map fun B => contrib B.toFinset) :
    H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (polar F) ; Am.P₀]
      ≤ (∑ B ∈ famFinset F, Am.lat₁.reconScore B.toFinset)
        + (T.intersections.map fun p =>
            I[Am.lat₂.jointOn p.1 : Am.lat₂.jointOn p.2.1 | Am.lat₂.jointOn p.2.2 ;
              Am.P₀]).sum := by
  have h513 := condEntropy_jointAbove_le Am A F T hupper hleaves
  have h523 : ∀ B ∈ famFinset F,
      H[Am.lat₁.jointAbove A.toFinset | Am.lat₁.pullbackJoint B.toFinset ; Am.P₀]
        ≤ Am.lat₁.reconScore B.toFinset := fun B hB =>
    condEntropy_jointAbove_le_reconScore_term Am (hFA B (mem_famFinset.mp hB))
  have hsum := Finset.sum_le_sum h523
  linarith

/-- **Corollary 5.9**, equation (5.22): if in addition the `Z` family satisfies Definition
4.8's ordered Markov condition, the internal terms vanish (Proposition 4.10) and only the
reconstruction scores remain.

Paper node: `Corollary 5.9` -/
theorem condEntropy_jointAbove_le_reconScore_of_orderedMarkov
    (hmarkov : Am.rv₂.OrderedMarkov)
    (A : PPlus I) (F : Set (PPlus I)) (hFA : ∀ B ∈ F, B ≤ A)
    (T : ITree (Set (PPlus I))) (hupper : T.LabelsIn {s | IsUpperSet s})
    (hleaves : (T.leaves : Multiset (Set (PPlus I)))
      = (famFinset F).val.map fun B => contrib B.toFinset) :
    H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (polar F) ; Am.P₀]
      ≤ ∑ B ∈ famFinset F, Am.lat₁.reconScore B.toFinset := by
  have h521 := condEntropy_jointAbove_le_reconScore Am A F hFA T hupper hleaves
  have hspec := ITree.intersections_spec isUpperSet_inf_closed T hupper
  have hzero : (T.intersections.map fun p =>
      I[Am.lat₂.jointOn p.1 : Am.lat₂.jointOn p.2.1 | Am.lat₂.jointOn p.2.2 ;
        Am.P₀]).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q₁, q₂, q₃⟩ := p
    obtain ⟨hq₁, hq₂, hq₃⟩ := hspec _ hp
    simp only at hq₁ hq₂ hq₃
    subst hq₃
    haveI := Am.finiteEntropyOf' (Am.lat₂.L.measurable_jointOn q₁)
    haveI := Am.finiteEntropyOf' (Am.lat₂.L.measurable_jointOn q₂)
    haveI := Am.finiteEntropyOf' (Am.lat₂.L.measurable_jointOn (q₁ ⊓ q₂))
    refine (ShannonInformation.condMutualInfo_eq_zero (μ := Am.P₀)
      (Am.lat₂.L.measurable_jointOn q₁) (Am.lat₂.L.measurable_jointOn q₂)
      (Am.lat₂.L.measurable_jointOn (q₁ ⊓ q₂))).mpr ?_
    exact (Am.rv₂.orderedMarkov_iff).mp hmarkov q₁ q₂ hq₁ hq₂
  rw [hzero] at h521
  linarith

/-- The `k`-element subsets of `A`, Corollary 5.10's family `F`. -/
def kSubsets (A : PPlus I) (k : ℕ) : Set (PPlus I) :=
  {C | C ≤ A ∧ C.toFinset.card = k}

omit [Finite I] in
/-- **Corollary 5.10**, equation (5.24): the polar of the family of `k`-element subsets of
`A` is the family of sets containing all but at most `k − 1` elements of `A`.

Two things the printed statement leaves open, resolved here (see
`Condensation/notes/paper-errata.md`).  First, (5.24) is printed with `n − 1`, but the
parameter is `k`; this is the paper's typo.  Second, `k` is used in the hypothesis one
sentence before it is bound, and the degenerate values are unaddressed.  `k = 0` is
**excluded** (`1 ≤ k`), because the identity is false there.  With `k = 0` the paper's `F`
would be `{∅}`, which is not a subfamily of `P⁺I` at all, so in this rendering
`kSubsets A 0 = ∅` — no member of `P⁺I` has cardinality `0` — and the left-hand side is
`polar ∅ = P⁺I` (`polar_empty`).  The right-hand side, on the other hand, is **not** empty:
`k - 1` is truncated subtraction on `ℕ`, so at `k = 0` it reads `0`, and the condition
`(A \ C).card ≤ 0` says `A ⊆ C`.  The right-hand side is therefore the upward cone
`{C : A ⊆ C}` (`above A.toFinset`), and the two sides differ as soon as some `C ∈ P⁺I`
fails to contain `A` — for instance any `C = {i}` with `A` not a subset of `{i}`.  (They do
coincide in the degenerate case where every member of `P⁺I` contains `A`, so the failure is
general rather than universal.)  `k > |A|` is **allowed**: then `F = ∅` again and the
left-hand side is `P⁺I`, but now `k - 1 ≥ |A|` bounds `(A \ C).card ≤ |A|` for every `C`,
so the right-hand side is `P⁺I` too and (5.24) holds.  Note that (5.25) is vacuous in that
case, since an `ITree` always has at least one leaf and so no tree can satisfy the
bijection hypothesis with `F = ∅`.

`DecidableEq I` appears only to write the `Finset` difference `A \ C`; it is classical
data, not a restriction on `I`.  The `omit [Finite I] in` above this docstring is
deliberate, and is the one place in §5 where the section binder is dropped: (5.24) is pure
`Finset` combinatorics and holds for an arbitrary `I`, so carrying the unused instance
would both weaken the statement and draw the `unusedSectionVars` linter.

Paper node: `Corollary 5.10` -/
theorem polar_kSubsets [DecidableEq I] (A : PPlus I) {k : ℕ} (hk : 1 ≤ k) :
    polar (kSubsets A k) = {C : PPlus I | (A.toFinset \ C.toFinset).card ≤ k - 1} := by
  ext C
  simp only [Set.mem_setOf_eq, polar]
  constructor
  · intro hC
    by_contra hlt
    push Not at hlt
    have hk' : k ≤ (A.toFinset \ C.toFinset).card := by omega
    obtain ⟨D, hDsub, hDcard⟩ := Finset.exists_subset_card_eq hk'
    have hDne : D.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hiD, hiC⟩ := hC ⟨D, hDne⟩ ⟨by
      intro j hj
      exact (Finset.mem_sdiff.mp (hDsub hj)).1, hDcard⟩
    exact (Finset.mem_sdiff.mp (hDsub hiD)).2 hiC
  · intro hC D hD
    by_contra hne
    push Not at hne
    have hsub : D.toFinset ⊆ A.toFinset \ C.toFinset := by
      intro j hj
      exact Finset.mem_sdiff.mpr ⟨hD.1 hj, fun hjC => hne j hj hjC⟩
    have := Finset.card_le_card hsub
    rw [hD.2] at this
    omega

/-- The `k`-element subsets of `A` number `|A| choose k`.

Stated for `1 ≤ k`, which is where `kSubsets A k` really *is* `Finset.powersetCard k A`
transported along `PPlus.toFinset`: the transport needs each member to be nonempty, which
is what `1 ≤ k` supplies.  At `k = 0` the two sides differ — the left is `0` (no member of
`P⁺I` is empty) and the right is `1` — and (5.25) handles that case separately, by
observing that its tree hypothesis is unsatisfiable there. -/
private lemma card_famFinset_kSubsets (A : PPlus I) {k : ℕ} (hk : 1 ≤ k) :
    (famFinset (kSubsets A k)).card = A.toFinset.card.choose k := by
  rw [← Finset.card_powersetCard k A.toFinset]
  refine Finset.card_bij (fun C _ => C.toFinset) ?_ ?_ ?_
  · intro C hC
    rw [mem_famFinset] at hC
    exact Finset.mem_powersetCard.mpr ⟨hC.1, hC.2⟩
  · intro C₁ _ C₂ _ h
    exact PPlus.toFinset_injective h
  · intro D hD
    rw [Finset.mem_powersetCard] at hD
    have hne : D.Nonempty := Finset.card_pos.mp (by omega)
    exact ⟨⟨D, hne⟩, by rw [mem_famFinset]; exact ⟨hD.1, hD.2⟩, rfl⟩

/-- **Corollary 5.10**, equation (5.25): with `F` the `k`-element subsets of `A` and
`ϱ_Y(C) ≤ α` for every `C` of cardinality `k`, the leaf sum of (5.21) is at most
`(|A| choose k) · α`.

Unlike `polar_kSubsets` (5.24), this statement carries **no** `1 ≤ k` hypothesis, and that
is deliberate: at `k = 0` the family `kSubsets A 0` is empty, so `hleaves` would force
`T.leaves` to be the empty multiset, which no `ITree` satisfies (`ITree.leaves_ne_nil` — a
tree always has at least one leaf).  The tree hypothesis is thus unsatisfiable at `k = 0`,
(5.25) holds vacuously there, and `1 ≤ k` would be dead weight.  In `polar_kSubsets` there
is no tree to make the degenerate case vacuous and `1 ≤ k` is load-bearing: see that
statement's docstring for what goes wrong at `k = 0`.

Paper node: `Corollary 5.10` -/
theorem condEntropy_jointAbove_le_choose
    {k : ℕ} {α : ℝ}
    (hϱ : ∀ C : PPlus I, C.toFinset.card = k → Am.lat₁.reconScore C.toFinset ≤ α)
    (A : PPlus I) (T : ITree (Set (PPlus I))) (hupper : T.LabelsIn {s | IsUpperSet s})
    (hleaves : (T.leaves : Multiset (Set (PPlus I)))
      = (famFinset (kSubsets A k)).val.map fun B => contrib B.toFinset) :
    H[Am.lat₁.jointAbove A.toFinset | Am.lat₂.jointOn (polar (kSubsets A k)) ; Am.P₀]
      ≤ (A.toFinset.card.choose k : ℝ) * α
        + (T.intersections.map fun p =>
            I[Am.lat₂.jointOn p.1 : Am.lat₂.jointOn p.2.1 | Am.lat₂.jointOn p.2.2 ;
              Am.P₀]).sum := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- The tree hypothesis is unsatisfiable at `k = 0`: `kSubsets A 0` is empty, so
    -- `hleaves` would make `T` leafless, which no `ITree` is.
    exfalso
    have hempty : famFinset (kSubsets A 0) = (∅ : Finset (PPlus I)) := by
      ext B
      simp only [mem_famFinset, Finset.notMem_empty, iff_false, kSubsets, Set.mem_setOf_eq,
        not_and]
      intro _
      exact fun hcard =>
        absurd (Finset.card_eq_zero.mp hcard) (Finset.nonempty_iff_ne_empty.mp B.nonempty)
    rw [hempty, Finset.empty_val, Multiset.map_zero] at hleaves
    simp only [Multiset.coe_eq_zero] at hleaves
    exact ITree.leaves_ne_nil T hleaves
  have h521 := condEntropy_jointAbove_le_reconScore Am A (kSubsets A k)
    (fun B hB => hB.1) T hupper hleaves
  have h1 : ∀ B ∈ famFinset (kSubsets A k), Am.lat₁.reconScore B.toFinset ≤ α := by
    intro B hB
    rw [mem_famFinset] at hB
    exact hϱ B hB.2
  have hb : ∑ B ∈ famFinset (kSubsets A k), Am.lat₁.reconScore B.toFinset
      ≤ (A.toFinset.card.choose k : ℝ) * α := by
    calc ∑ B ∈ famFinset (kSubsets A k), Am.lat₁.reconScore B.toFinset
        ≤ (famFinset (kSubsets A k)).card • α := Finset.sum_le_card_nsmul _ _ _ h1
      _ = ((famFinset (kSubsets A k)).card : ℝ) * α := by rw [nsmul_eq_mul]
      _ = (A.toFinset.card.choose k : ℝ) * α := by rw [card_famFinset_kSubsets A hk]
  linarith

end Comparison

/-! ## Regression examples

`Condensation/Examples.lean` is deliberately **not** imported here: it is the terminal
non-vacuity file of the library, imported by the aggregator and by nothing else, and
importing it from a §5 file would invert that dependency.  The concrete checks below are
therefore combinatorial (the tree examples live with `ITree` above); the entropy-side
witnesses for `interactionInfo` belong in `Examples.lean` and are that file's owner's to
add. -/

section Regression

/-- Definition 5.5 on a concrete family.  Over `Bool`, the polar of `{{true}, {false}}` is
the family of sets containing both indices — the singleton `{{true, false}} ⊆ P⁺Bool`. -/
example (C : PPlus Bool) :
    C ∈ polar ({PPlus.single true, PPlus.single false} : Set (PPlus Bool))
      ↔ (true ∈ C ∧ false ∈ C) := by
  simp only [mem_polar, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨by simpa using h _ (Or.inl rfl), by simpa using h _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ A (rfl | rfl)
    · exact ⟨true, by simp, h1⟩
    · exact ⟨false, by simp, h2⟩

/-- The polar of a singleton family is the contributing family of (3.5). -/
example (A : PPlus Bool) : polar {A} = contrib A.toFinset := polar_singleton A

/-- A two-leaf intersection tree whose leaves are the contributing families of `{true}` and
`{false}` has the polar of `{{true}, {false}}` as its root label — Theorem 5.8's `Z_G`. -/
example :
    (ITree.node (.leaf (contrib ({true} : Finset Bool)))
        (.leaf (contrib ({false} : Finset Bool)))).label
      = polar ({PPlus.single true, PPlus.single false} : Set (PPlus Bool)) := by
  rw [ITree.label_node, ITree.label_leaf, ITree.label_leaf, polar_eq_iInter]
  ext C
  simp [contrib]

end Regression

end Condensation
