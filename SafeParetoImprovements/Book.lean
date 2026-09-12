import SafeParetoImprovements.Assumptions
import SafeParetoImprovements.Reduction
import SafeParetoImprovements.Representatives
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Consistency of Assumptions 1 and 2: the book representatives (§4.4.3)

Every result of the form "under Assumptions 1 and 2, …" is vacuous unless some
representatives satisfy both.  §4.4.3 argues informally that such representatives
exist — "we would need to specify in more detail what the set of games looks like" to
make it formal — and the repository standard requires the hypotheses of a headline
theorem to be shown satisfiable.  This file supplies the construction (`dd:book`).

**The book.**  Fix, for each isomorphism class of games over the universe, one
representative (`rep`, by `Quotient.out`) and, for each game, one isomorphism onto the
representative of its class (`chosenIso`, by `Classical.choice`).  A *book* assigns to
each class a random outcome of the representative — the "page" — on a sample space `Ω`.
The book representatives play a game `Γ` by fully reducing it (`Game.reduce`), reading
the page of the reduced game's class, and translating back through the chosen
isomorphism.

* **Assumption 1** holds because removing a strictly dominated action does not change
  the full reduction (`Game.reduce_erase`, i.e. path independence), so the same page is
  read through the same translation — the two plays are literally equal — and the
  dominated action is not in the reduced game, so it is never played.
* **Assumption 2** holds because two fully reduced isomorphic games are their own
  reductions and lie in the same class, so both read the same page; the composite of
  the two translations is an isomorphism along which they correspond.

Both hold at **every** sample point, hence for every certainty filter — the strong,
solver-wise reading of the assumptions, not just the paper's "for every game, with
certainty".

**The pages are a parameter.**  The construction takes any page family; the
deterministic book (`Book.const`) proves joint satisfiability outright, and books with
prescribed page distributions are what Proposition 16 and the strictness clause of
Proposition 6 need — `Book.prescribed` is one, pinning the page of a single class to a
chosen outcome (`Book.prescribed_play`).  `Book.toRepresentatives` packages a book with a
probability measure whose page fibers are measurable into a `Representatives` model, and
`exists_representatives_satisfiesA1_satisfiesA2` states §4.4.3's consistency claim at that
level rather than only for a bare play family.

The representative of a class need not itself be reduced; nothing here needs it.
-/

namespace SafeParetoImprovements

open Filter
open scoped SetRel

universe u v w

variable {N : Type u} {𝒜 : N → Type v}

/-! ### Isomorphism classes of games -/

lemma Game.Isomorphic.refl (Γ : Game N 𝒜) : Γ.Isomorphic Γ := ⟨GameIso.refl Γ⟩

lemma Game.Isomorphic.trans {Γ Γ' Γ'' : Game N 𝒜} (h : Γ.Isomorphic Γ') (h' : Γ'.Isomorphic Γ'') :
    Γ.Isomorphic Γ'' :=
  ⟨h.some.trans h'.some⟩

section classes

lemma Game.Isomorphic.symm {Γ Γ' : Game N 𝒜} (h : Γ.Isomorphic Γ') : Γ'.Isomorphic Γ :=
  ⟨h.some.symm⟩

/-- Isomorphism of games is an equivalence relation (given `dd:iso`'s bijective,
positive-affine reading; with `λᵢ = 0` allowed it would not be symmetric). -/
def isoSetoid (N : Type u) (𝒜 : N → Type v) : Setoid (Game N 𝒜) where
  r := Game.Isomorphic
  iseqv := ⟨Game.Isomorphic.refl, Game.Isomorphic.symm, Game.Isomorphic.trans⟩

/-- The isomorphism classes of games over the universe: the pages of the book. -/
abbrev IsoClass (N : Type u) (𝒜 : N → Type v) :=
  Quotient (isoSetoid N 𝒜)

/-- The class of a game. -/
def Game.cls (Γ : Game N 𝒜) : IsoClass N 𝒜 := Quotient.mk (isoSetoid N 𝒜) Γ

lemma Game.cls_eq_of_isomorphic {Γ Γ' : Game N 𝒜} (h : Γ.Isomorphic Γ') : Γ.cls = Γ'.cls :=
  Quotient.sound h

/-- The chosen representative of a class. -/
noncomputable def IsoClass.rep (q : IsoClass N 𝒜) : Game N 𝒜 := Quotient.out q

lemma Game.isomorphic_rep (Γ : Game N 𝒜) : Γ.Isomorphic Γ.cls.rep :=
  (Quotient.mk_out (s := isoSetoid N 𝒜) Γ).symm

/-- The chosen isomorphism from a game onto the representative of a class it belongs to.
The class is an explicit argument with a proof, so that "its own class" is the instance
`chosenIso Γ Γ.cls rfl` and any other presentation of the class can be substituted. -/
noncomputable def Game.chosenIso (Γ : Game N 𝒜) (q : IsoClass N 𝒜) (h : Γ.cls = q) :
    GameIso Γ q.rep :=
  Classical.choice (h ▸ Γ.isomorphic_rep)

end classes

/-! ### The book and its play -/

variable [Fintype N] [DecidableEq N] [∀ i, DecidableEq (𝒜 i)]

/-- A **book** (§4.4.3): for each isomorphism class, a random outcome of the class's
representative game — the page the representatives consult. -/
structure Book (N : Type u) (𝒜 : N → Type v) (Ω : Type w) where
  /-- The page for a class, at a sample point. -/
  page : IsoClass N 𝒜 → Ω → (∀ i, 𝒜 i)
  /-- The page is an outcome of the representative. -/
  page_mem : ∀ q ω, page q ω ∈ q.rep.profiles

namespace Book

variable {Ω : Type w} (B : Book N 𝒜 Ω)

/-- How the book representatives play a game `G` *that is already fully reduced*: read
the page of its class and translate back through the chosen isomorphism. -/
noncomputable def playReduced (G : Game N 𝒜) (ω : Ω) : ∀ i, 𝒜 i :=
  (G.chosenIso G.cls rfl).symm.map (B.page G.cls ω)

omit [Fintype N] [DecidableEq N] [∀ i, DecidableEq (𝒜 i)] in
lemma playReduced_mem (G : Game N 𝒜) (ω : Ω) : B.playReduced G ω ∈ G.profiles :=
  (G.chosenIso G.cls rfl).symm.map_mem (B.page_mem _ ω)

omit [Fintype N] [DecidableEq N] [∀ i, DecidableEq (𝒜 i)] in
/-- Reading the page through *any* presentation of the class gives the same play. -/
lemma chosenIso_symm_map_page (G : Game N 𝒜) (q : IsoClass N 𝒜) (h : G.cls = q) (ω : Ω) :
    (G.chosenIso q h).symm.map (B.page q ω) = B.playReduced G ω := by
  subst h; rfl

/-- The book representatives as a play family: fully reduce, then play as the book
says. -/
noncomputable def toPlay : Play N 𝒜 Ω where
  play Γ ω := B.playReduced Γ.reduce ω
  mem Γ ω := Γ.reduce_isSubsetGameOf.profiles_subset (B.playReduced_mem _ ω)

@[simp] lemma toPlay_play (Γ : Game N 𝒜) (ω : Ω) :
    B.toPlay.play Γ ω = B.playReduced Γ.reduce ω := rfl

/-- **The book representatives satisfy Assumption 1**, at every sample point and hence
for every certainty filter. -/
lemma satisfiesA1 (L : Filter Ω) : B.toPlay.SatisfiesA1 L := by
  intro Γ i ã h
  refine Eventually.of_forall fun ω => ?_
  refine ⟨B.toPlay.mem Γ ω, ?_, ?_⟩
  · -- the dominated action is not in the reduced game, so it is not played
    intro heq
    have hmem : B.playReduced Γ.reduce ω ∈ Γ.reduce.profiles := B.playReduced_mem _ ω
    have hsub : Γ.reduce.IsSubsetGameOf (Γ.erase i ã h.erase_nonempty) := by
      rw [← Γ.reduce_erase h]; exact Game.reduce_isSubsetGameOf _
    have : ã ∈ (Γ.erase i ã h.erase_nonempty).S i := hsub i (heq ▸ hmem i)
    rw [Game.erase_S_self] at this
    exact (Finset.mem_erase.1 this).1 rfl
  · -- removing it does not change the reduction, hence not the play
    simp only [toPlay_play, Γ.reduce_erase h]

/-- **The book representatives satisfy Assumption 2**, at every sample point and hence
for every certainty filter: two fully reduced isomorphic games read the same page, and
the composite of their translations is the witnessing isomorphism. -/
lemma satisfiesA2 (L : Filter Ω) : B.toPlay.SatisfiesA2 L := by
  intro Γ Γ' hΓ hΓ' hiso
  have hq : Γ'.cls = Γ.cls := (Game.cls_eq_of_isomorphic hiso).symm
  -- translations onto the common representative
  let φ : GameIso Γ Γ.cls.rep := Γ.chosenIso Γ.cls rfl
  let φ' : GameIso Γ' Γ.cls.rep := Γ'.chosenIso Γ.cls hq
  refine ⟨φ.trans φ'.symm, Eventually.of_forall fun ω => ?_⟩
  refine ⟨B.toPlay.mem Γ ω, ?_⟩
  simp only [toPlay_play, Game.reduce_of_reduced hΓ, Game.reduce_of_reduced hΓ',
    GameIso.trans_map]
  rw [← B.chosenIso_symm_map_page Γ' Γ.cls hq ω]
  show φ'.symm.map (B.page Γ.cls ω) = φ'.symm.map (φ.map (φ.symm.map (B.page Γ.cls ω)))
  rw [φ.map_symm_map (B.page_mem _ ω)]

/-- The deterministic book: each page is a fixed outcome of the representative. -/
noncomputable def const (Ω : Type w) : Book N 𝒜 Ω where
  page q _ := (q.rep.profiles_nonempty).choose
  page_mem q _ := (q.rep.profiles_nonempty).choose_spec

/-- The **prescribed book** for one target class: the page of the class of the reduced
game `T` is a chosen outcome `a` of `T`, translated onto the class representative; every
other class gets an arbitrary outcome.  This is the "book with a prescribed page
distribution" that Proposition 16 and the strictness clause of Proposition 6 need
(R1-F15). -/
noncomputable def prescribed (T : Game N 𝒜) {a : ∀ i, 𝒜 i} (ha : a ∈ T.profiles)
    (Ω : Type w) : Book N 𝒜 Ω where
  page q _ := open Classical in
    if h : T.cls = q then (T.chosenIso q h).map a else (q.rep.profiles_nonempty).choose
  page_mem q _ := by
    classical
    by_cases h : T.cls = q
    · rw [dif_pos h]; exact (T.chosenIso q h).map_mem ha
    · rw [dif_neg h]; exact (q.rep.profiles_nonempty).choose_spec

/-- The prescribed book plays `a` in every game whose full reduction is `T`. -/
lemma prescribed_play (T : Game N 𝒜) {a : ∀ i, 𝒜 i} (ha : a ∈ T.profiles) (Ω : Type w)
    (Γ : Game N 𝒜) (hΓ : Γ.reduce = T) (ω : Ω) :
    (prescribed T ha Ω).toPlay.play Γ ω = a := by
  classical
  rw [toPlay_play, hΓ, playReduced, prescribed]
  dsimp only
  rw [dif_pos rfl]
  exact GameIso.symm_map_map _ ha

/-! ### Books as probabilistic representatives -/

section representatives

open MeasureTheory

variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- If every page's fibers are measurable, so are the play's fibers. -/
lemma measurableSet_fiber (hB : ∀ q a, MeasurableSet {ω | B.page q ω = a})
    (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) : MeasurableSet {ω | B.toPlay.play Γ ω = a} := by
  by_cases ha : a ∈ Γ.reduce.profiles
  · have : {ω | B.toPlay.play Γ ω = a} =
        {ω | B.page Γ.reduce.cls ω = (Γ.reduce.chosenIso Γ.reduce.cls rfl).map a} := by
      ext ω
      simp only [Set.mem_setOf_eq, toPlay_play, playReduced]
      constructor
      · rintro rfl
        rw [GameIso.map_symm_map _ (B.page_mem _ ω)]
      · intro h
        rw [h, GameIso.symm_map_map _ ha]
    rw [this]; exact hB _ _
  · have : {ω | B.toPlay.play Γ ω = a} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro rfl
      exact ha (B.playReduced_mem _ ω)
    rw [this]; exact MeasurableSet.empty

/-- A book with measurable pages, as a `Representatives` model on `(Ω, μ)`. -/
noncomputable def toRepresentatives (hB : ∀ q a, MeasurableSet {ω | B.page q ω = a}) :
    Representatives.{u, v, w} N 𝒜 where
  Ω := Ω
  μ := μ
  toPlay := B.toPlay
  measurableSet_fiber := B.measurableSet_fiber hB

end representatives

end Book

/-- **Assumptions 1 and 2 are jointly satisfiable** (§4.4.3, made formal): over any
universe and any sample space there is a play family satisfying both, for every
certainty filter.  The witness is the deterministic book. -/
lemma exists_play_satisfiesA1_satisfiesA2 (Ω : Type w) :
    ∃ X : Play N 𝒜 Ω, ∀ L : Filter Ω, X.SatisfiesA1 L ∧ X.SatisfiesA2 L :=
  ⟨(Book.const Ω).toPlay, fun L => ⟨(Book.const Ω).satisfiesA1 L, (Book.const Ω).satisfiesA2 L⟩⟩

/-- **Assumptions 1 and 2 are jointly satisfiable by *representatives*** — a probability
space with measurable outcome fibers, which is what §3 models the representatives as — and
not merely by a bare play family (R1-F14).  The witness is the deterministic book on a
one-point probability space; its pages are constant, hence its fibers measurable, and the
assumptions hold at every sample point and so at the model's own certainty filter. -/
lemma exists_representatives_satisfiesA1_satisfiesA2 :
    ∃ R : Representatives.{u, v, 0} N 𝒜,
      R.toPlay.SatisfiesA1 R.certainty ∧ R.toPlay.SatisfiesA2 R.certainty :=
  ⟨(Book.const Unit).toRepresentatives (μ := MeasureTheory.Measure.dirac ())
      (fun _ _ => trivial),
    (Book.const Unit).satisfiesA1 _, (Book.const Unit).satisfiesA2 _⟩

end SafeParetoImprovements
