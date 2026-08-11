module

public import ProvabilityLogic.LabelledGentzen.Search
public import ProvabilityLogic.LabelledGentzen.Kripke

/-!
Completeness of the proof search `search0` for `ProvableLabelledGentzen`: whenever `search0 R Γ Δ = none`,
a finite Kripke countermodel of the labelled sequent `R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset`
exists (`LabelledGentzen.exists_countermodel_of_search0_eq_none`).
-/

@[expose]
public section

open scoped Formula

namespace LabelledGentzen

variable {α : Type u} [DecidableEq α]

namespace LabelledSequent

/-! ### The countermodel determined by a saturated open leaf -/

variable {S S₀ : LabelledSequent α} {x y : Label} {A B : Formula α}

/-- Every boxed succedent formula of `S` has a relational successor refuting its body:
the Hintikka-style condition supplied to the countermodel construction by the failed
proof search. -/
def BoxSucWitnessed (S : LabelledSequent α) : Prop :=
  ∀ x A, (x ∶ □A) ∈ S.suc → ∃ y, (x, y) ∈ S.rel ∧ (y ∶ A) ∈ S.suc

instance : Nonempty {z : Label // z ∈ insert (0 : Label) S.labels} :=
  ⟨⟨0, Finset.mem_insert_self 0 _⟩⟩

/-- The finite Kripke model determined by a labelled sequent `S`: the worlds are the
labels of `S` (plus a fallback root `0`), the relation is given by the relational atoms
and the valuation by the atomic antecedent members. -/
def countermodel (S : LabelledSequent α) : Model {z : Label // z ∈ insert (0 : Label) S.labels} α where
  Rel' u w := (u.1, w.1) ∈ S.rel
  Val' u a := (u.1 ∶ (#a : Formula α)) ∈ S.ant

omit [DecidableEq α] in
lemma countermodel_isFiniteGL (hsat : S.Saturated) : S.countermodel.IsFiniteGL where
  finite := inferInstance
  trans u v w huv hvw := hsat.rel_trans u.1 v.1 w.1 huv hvw
  irrefl u := hsat.not_irref u.1

omit [DecidableEq α] in
/-- Truth lemma for `countermodel`: on a saturated sequent all of whose boxed succedent
formulas are witnessed, antecedent members are forced and succedent members are refuted
at their labels. -/
lemma countermodel_truthlemma (hsat : S.Saturated) (hbox : S.BoxSucWitnessed)
  {A : Formula α} {w : S.countermodel.World} :
  ((w.1 ∶ A) ∈ S.ant → w ⊩ A) ∧ ((w.1 ∶ A) ∈ S.suc → ¬w ⊩ A) := by
  induction A generalizing w with
  | atom a =>
    constructor;
    · exact fun h => h;
    · intro h hf;
      exact hsat.not_axm _ hf h;
  | bot =>
    constructor;
    · intro h;
      exact absurd h (hsat.not_bot w.1);
    · intro _ hf;
      exact hf;
  | imp A B ihA ihB =>
    constructor;
    · intro h hA;
      rcases hsat.imp_ant _ _ _ h with hs | hb;
      · exact absurd hA (ihA.2 hs);
      · exact ihB.1 hb;
    · intro h hf;
      obtain ⟨hA, hB⟩ := hsat.imp_suc _ _ _ h;
      exact ihB.2 hB (hf (ihA.1 hA));
  | box A ih =>
    constructor;
    · intro h u Rwu;
      exact ih.1 (hsat.box_ant _ _ _ Rwu h);
    · intro h hf;
      obtain ⟨y, hRy, hyA⟩ := hbox _ _ h;
      have hy : y ∈ insert (0 : Label) S.labels :=
        Finset.mem_insert_of_mem (mem_labels_of_mem_suc (lf := y ∶ A) hyA);
      exact (ih (w := ⟨y, hy⟩)).2 hyA (hf ⟨y, hy⟩ hRy);

/-- The label assignment interpreting each label of `S` as its own world. -/
def countermodelAssignment (S : LabelledSequent α) : Label → S.countermodel.World :=
  fun z => if h : z ∈ insert (0 : Label) S.labels then ⟨z, h⟩ else ⟨0, Finset.mem_insert_self 0 _⟩

omit [DecidableEq α] in
lemma countermodelAssignment_val {z : Label} (h : z ∈ S.labels) :
  (S.countermodelAssignment z).1 = z := by
  simp only [countermodelAssignment];
  rw [dif_pos (Finset.mem_insert_of_mem h)];

omit [DecidableEq α] in
/-- `countermodel` refutes, under `countermodelAssignment`, every labelled sequent that
`S` extends componentwise. -/
lemma not_validate_countermodel (hsat : S.Saturated) (hbox : S.BoxSucWitnessed)
  (hrel : S₀.rel ⊆ S.rel) (hant : S₀.ant ⊆ S.ant) (hsuc : S₀.suc ⊆ S.suc) :
  ¬S.countermodel ⊧ˡ[S.countermodelAssignment] S₀ := by
  intro hval;
  have hvrel : ∀ p ∈ S₀.rel, S.countermodelAssignment p.1 ≺ S.countermodelAssignment p.2 := by
    intro p hp;
    have hp' : p ∈ S.rel := hrel hp;
    show (_, _) ∈ S.rel;
    rw [countermodelAssignment_val (fst_mem_labels_of_mem_rel hp'),
      countermodelAssignment_val (snd_mem_labels_of_mem_rel hp')];
    exact hp';
  have hvant : ∀ lf ∈ S₀.ant, S.countermodelAssignment lf.label ⊩ lf.formula := by
    intro lf hlf;
    apply countermodel_truthlemma hsat hbox (A := lf.formula)
      (w := S.countermodelAssignment lf.label) |>.1;
    rw [countermodelAssignment_val (mem_labels_of_mem_ant (hant hlf))];
    exact hant hlf;
  obtain ⟨lf, hlf, hforce⟩ := hval hvrel hvant;
  apply countermodel_truthlemma hsat hbox (A := lf.formula)
    (w := S.countermodelAssignment lf.label) |>.2 ?_ hforce;
  rw [countermodelAssignment_val (mem_labels_of_mem_suc (hsuc hlf))];
  exact hsuc hlf;

/-! ### The soundness invariant of the `processed` bookkeeping -/

/-- Soundness invariant of the `processed` set threaded through `search`/`searchLeaves`:
every recorded pair `(x ∶ □A)` has a witness label `y` with `(x, y) ∈ S.rel` and
`y ∶ A ∈ S.suc`. -/
def ProcessedWitnessed (P : Finset (LabelledFormula α)) (S : LabelledSequent α) : Prop :=
  ∀ x A, (x ∶ □A) ∈ P → ∃ y, (x, y) ∈ S.rel ∧ (y ∶ A) ∈ S.suc

variable {P : Finset (LabelledFormula α)} {S' : LabelledSequent α}

omit [DecidableEq α] in
-- `ProcessedWitnessed` is preserved because the search only ever grows `rel` and `suc`.
lemma ProcessedWitnessed.mono (h : ProcessedWitnessed P S)
  (hrel : S.rel ⊆ S'.rel) (hsuc : S.suc ⊆ S'.suc) : ProcessedWitnessed P S' := by
  intro x A hxA;
  obtain ⟨y, h1, h2⟩ := h x A hxA;
  exact ⟨y, hrel h1, hsuc h2⟩;

omit [DecidableEq α] in
lemma ProcessedWitnessed.empty : ProcessedWitnessed (∅ : Finset (LabelledFormula α)) S := by
  intro x A hxA;
  exact absurd hxA (Finset.notMem_empty _);

/-! ### Abandoned leaves of the proof search -/

/-- An *abandoned leaf* of the proof search over `S₀`: a saturated sequent extending `S₀`
componentwise on which neither `loopTarget?` nor `lobTarget?` fires, together with a
`processed` set witnessed in it. -/
inductive HasFailingLeaf (S₀ : LabelledSequent α) : Prop where
  | intro
      (Rl : List LabelRel)
      (Γl Δl : List (LabelledFormula α))
      (P : Finset (LabelledFormula α))
      (sat : (LabelledSequent.ofLists (Rl, Γl, Δl)).Saturated)
      (noLoop : loopTarget? Rl Γl Δl = none)
      (noLob : lobTarget? P Rl Γl Δl = none)
      (wit : ProcessedWitnessed P (LabelledSequent.ofLists (Rl, Γl, Δl)))
      (hrel : S₀.rel ⊆ Rl.toFinset)
      (hant : S₀.ant ⊆ Γl.toFinset)
      (hsuc : S₀.suc ⊆ Δl.toFinset)

lemma HasFailingLeaf.mono (h : S'.HasFailingLeaf)
  (hrel : S.rel ⊆ S'.rel) (hant : S.ant ⊆ S'.ant) (hsuc : S.suc ⊆ S'.suc) :
  S.HasFailingLeaf := by
  obtain ⟨Rl, Γl, Δl, P, sat, noLoop, noLob, wit, hrel', hant', hsuc'⟩ := h;
  exact ⟨Rl, Γl, Δl, P, sat, noLoop, noLob, wit,
    hrel.trans hrel', hant.trans hant', hsuc.trans hsuc'⟩;

/-- On an abandoned leaf every boxed succedent formula is witnessed. -/
lemma HasFailingLeaf.boxSucWitnessed
  {Rl : List LabelRel} {Γl Δl : List (LabelledFormula α)}
  {P : Finset (LabelledFormula α)}
  (sat : (LabelledSequent.ofLists (Rl, Γl, Δl)).Saturated)
  (noLoop : loopTarget? Rl Γl Δl = none)
  (noLob : lobTarget? P Rl Γl Δl = none)
  (wit : ProcessedWitnessed P (LabelledSequent.ofLists (Rl, Γl, Δl))) :
  (LabelledSequent.ofLists (Rl, Γl, Δl)).BoxSucWitnessed := by
  intro x A hxA;
  -- The three disjuncts of `lobTarget?_none`: witnessed by the recorded `processed` pair,
  -- or contradicted by saturation (`not_axm`), or by `loopTarget?_none`.
  rcases lobTarget?_none noLob hxA with hP | hΓ | ⟨w, hwR, hwΓ⟩;
  · exact wit x A hP;
  · exact absurd hxA (sat.not_axm _ hΓ);
  · exact absurd hwΓ (loopTarget?_none noLoop hxA hwR);

/-- An abandoned leaf yields a finite Kripke countermodel of `S₀`. -/
theorem exists_countermodel_of_hasFailingLeaf (h : S₀.HasFailingLeaf) :
  ∃ (κ : Type) (_ : Nonempty κ) (M : Model κ α) (_ : M.IsFiniteGL) (L : M.LabelMap),
    ¬M ⊧ˡ[L] S₀ := by
  obtain ⟨Rl, Γl, Δl, P, sat, noLoop, noLob, wit, hrel, hant, hsuc⟩ := h;
  set S : LabelledSequent α := LabelledSequent.ofLists (Rl, Γl, Δl);
  use {z : Label // z ∈ insert (0 : Label) S.labels}, inferInstance, S.countermodel,
    countermodel_isFiniteGL sat, S.countermodelAssignment;
  exact not_validate_countermodel sat (HasFailingLeaf.boxSucWitnessed sat noLoop noLob wit)
    hrel hant hsuc;

end LabelledSequent


/-! ### Extraction of an abandoned leaf from a failing search -/

open LabelledSequent in
/-- Auxiliary simultaneous statement for `search_eq_none_hasFailingLeaf` and
`searchLeaves_eq_none_hasFailingLeaf`. -/
theorem hasFailingLeaf_of_eq_none_aux (n : ℕ) :
  (∀ (P : Finset (LabelledFormula α)) (m : ℕ)
    (leaves : List (List LabelRel × List (LabelledFormula α) × List (LabelledFormula α)))
    (hbound : ∀ L ∈ leaves, (LabelledSequent.ofLists L).lobMeasure P ≤ m),
    m ≤ n → searchLeaves P m leaves hbound = none →
    (∀ L ∈ leaves, (LabelledSequent.ofLists L).Saturated) →
    (∀ L ∈ leaves, ProcessedWitnessed P (LabelledSequent.ofLists L)) →
    ∃ L ∈ leaves, (LabelledSequent.ofLists L).HasFailingLeaf) ∧
  (∀ (P : Finset (LabelledFormula α)) (R : List LabelRel) (Γ Δ : List (LabelledFormula α)),
    (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).lobMeasure P ≤ n → search P R Γ Δ = none →
    ProcessedWitnessed P (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset) →
    (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).HasFailingLeaf) := by
  -- Strong induction on a bound `n` of the `lobMeasure`: the list recursion of
  -- `searchLeaves` is handled by an inner structural induction below, and each `R□^Löb`
  -- step strictly decreases the measure (`lobMeasure_lob_lt`), so its child `search` call
  -- falls under the outer induction hypothesis `ih`.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have SL : ∀ (P : Finset (LabelledFormula α)) (m : ℕ)
    (leaves : List (List LabelRel × List (LabelledFormula α) × List (LabelledFormula α)))
    (hbound : ∀ L ∈ leaves, (LabelledSequent.ofLists L).lobMeasure P ≤ m),
    m ≤ n → searchLeaves P m leaves hbound = none →
    (∀ L ∈ leaves, (LabelledSequent.ofLists L).Saturated) →
    (∀ L ∈ leaves, ProcessedWitnessed P (LabelledSequent.ofLists L)) →
    ∃ L ∈ leaves, (LabelledSequent.ofLists L).HasFailingLeaf := by
    intro P m leaves;
    induction leaves with
    | nil =>
      intro hbound hmn h hsat hwit;
      rw [searchLeaves] at h;
      simp at h;
    | cons hd rest ihrest =>
      obtain ⟨Rl, Γl, Δl⟩ := hd;
      intro hbound hmn h hsat hwit;
      rw [searchLeaves] at h;
      split at h;
      -- `loopTarget?` fires: the head leaf is closed by `loop`; the failure comes from `rest`.
      · rename_i w x A h₁;
        rcases hrest : searchLeaves P m rest
            (fun L hL => hbound L (List.mem_cons_of_mem _ hL)) with _ | ps;
        · obtain ⟨L, hL, hfail⟩ := ihrest _ hmn hrest
            (fun L hL => hsat L (List.mem_cons_of_mem _ hL))
            (fun L hL => hwit L (List.mem_cons_of_mem _ hL));
          exact ⟨L, List.mem_cons_of_mem _ hL, hfail⟩;
        · rw [hrest] at h;
          simp at h;
      · rename_i h₁;
        split at h;
        -- `lobTarget?` fires: recurse into the `R□^Löb` child or into `rest`.
        · rename_i x A h₂;
          have hΔ : (x ∶ □A) ∈ Δl.toFinset := (lobTarget?_some h₂).1;
          have hP : (x ∶ □A) ∉ P := (lobTarget?_some h₂).2.1;
          have hΓ : (x ∶ □A) ∉ Γl.toFinset := (lobTarget?_some h₂).2.2.1;
          have hpred : ∀ w, (w, x) ∈ Rl.toFinset → (w ∶ □A) ∉ Γl.toFinset :=
            (lobTarget?_some h₂).2.2.2;
          rcases hrest : searchLeaves P m rest
              (fun L hL => hbound L (List.mem_cons_of_mem _ hL)) with _ | ps;
          -- `rest` already fails.
          · obtain ⟨L, hL, hfail⟩ := ihrest _ hmn hrest
              (fun L hL => hsat L (List.mem_cons_of_mem _ hL))
              (fun L hL => hwit L (List.mem_cons_of_mem _ hL));
            exact ⟨L, List.mem_cons_of_mem _ hL, hfail⟩;
          -- `rest` succeeds: the failure must come from the `R□^Löb` child.
          · set y : Label := (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset).freshLabel with hy;
            have hyfresh : y ∉ (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset).labels := by
              rw [hy];
              exact LabelledSequent.freshLabel_notMem;
            rcases hchild : search (insert (x ∶ □A) P)
                (((Rl.filter (fun p => p.2 = x)).map Prod.fst).map (fun w => (w, y)) ++ (x, y) :: Rl)
                ((y ∶ □A) :: Γl) ((y ∶ A) :: Δl) with _ | π;
            · -- the child fails: extract its abandoned leaf and transfer it to the head leaf.
              have hrelEq :
                ((((Rl.filter (fun p => p.2 = x)).map Prod.fst).map (fun w => (w, y)) ++
                  (x, y) :: Rl)).toFinset =
                insert (x, y)
                  ((Rl.toFinset.filter (fun p => p.2 = x)).image (fun p => (p.1, y)) ∪ Rl.toFinset) := by
                ext p;
                simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.mem_map,
                  List.mem_filter, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
                  Finset.mem_filter, decide_eq_true_eq];
                grind;
              have hlt :
                ((((Rl.filter (fun p => p.2 = x)).map Prod.fst).map (fun w => (w, y)) ++
                  (x, y) :: Rl).toFinset ⸴
                  ((y ∶ □A) :: Γl).toFinset ⟹ˡ ((y ∶ A) :: Δl).toFinset).lobMeasure
                  (insert (x ∶ □A) P) < m := by
                apply lt_of_lt_of_le ?_ (hbound (Rl, Γl, Δl) (by simp));
                rw [List.toFinset_cons, List.toFinset_cons, hrelEq];
                exact LabelledSequent.lobMeasure_lob_lt hΔ hP hΓ hpred hyfresh;
              have hwit' :
                ProcessedWitnessed (insert (x ∶ □A) P)
                  ((((Rl.filter (fun p => p.2 = x)).map Prod.fst).map (fun w => (w, y)) ++
                    (x, y) :: Rl).toFinset ⸴
                    ((y ∶ □A) :: Γl).toFinset ⟹ˡ ((y ∶ A) :: Δl).toFinset) := by
                intro z B hzB;
                rcases Finset.mem_insert.mp hzB with heqz | hzB;
                · obtain ⟨rfl, hBA⟩ := LabelledFormula.mk.injEq _ _ _ _ ▸ heqz;
                  obtain rfl : B = A := by grind;
                  exact ⟨y, by grind [List.mem_toFinset], by grind [List.mem_toFinset]⟩;
                · obtain ⟨y', h1, h2⟩ := hwit (Rl, Γl, Δl) List.mem_cons_self z B hzB;
                  exact ⟨y', by grind [List.mem_toFinset], by grind [List.mem_toFinset]⟩;
              have hm1 : 1 ≤ m := by omega;
              have hfail := (ih (m - 1) (by omega)).2 (insert (x ∶ □A) P) _ _ _
                (by omega) hchild hwit';
              refine ⟨(Rl, Γl, Δl), List.mem_cons_self, hfail.mono ?_ ?_ ?_⟩;
              · intro p hp;
                grind [List.mem_toFinset];
              · intro lf hlf;
                grind [List.mem_toFinset];
              · intro lf hlf;
                grind [List.mem_toFinset];
            · -- both the child and `rest` succeed: contradicts `h`.
              rw [hrest] at h;
              dsimp only at h;
              rw [hchild] at h;
              simp at h;
        -- neither finder fires: the head leaf itself is abandoned.
        · rename_i h₂;
          exact ⟨(Rl, Γl, Δl), List.mem_cons_self,
            ⟨Rl, Γl, Δl, P, hsat _ List.mem_cons_self, h₁, h₂, hwit _ List.mem_cons_self,
              subset_rfl, subset_rfl, subset_rfl⟩⟩;
  refine ⟨SL, ?_⟩;
  intro P R Γ Δ hm h hwit;
  rw [search] at h;
  split at h;
  · simp at h;
  · rename_i leaves hsat hlab hsf hmono k heq₀;
    rcases hrest : searchLeaves P ((R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).lobMeasure P) leaves
        (fun L hL => LabelledSequent.lobMeasure_le (hlab L hL) (hsf L hL)
          (hmono L hL).1 (hmono L hL).2.1) with _ | ps;
    · obtain ⟨L, hL, hfail⟩ := SL P _ leaves _ hm hrest hsat
        (fun L hL => hwit.mono (hmono L hL).1 (hmono L hL).2.2);
      exact hfail.mono (hmono L hL).1 (hmono L hL).2.1 (hmono L hL).2.2;
    · rw [hrest] at h;
      simp at h;

open LabelledSequent in
/-- A failing run of `search` abandons some saturated leaf (extending the input sequent
componentwise) on which neither `loopTarget?` nor `lobTarget?` fires. -/
theorem search_eq_none_hasFailingLeaf
  {P : Finset (LabelledFormula α)} {R : List LabelRel} {Γ Δ : List (LabelledFormula α)}
  (h : search P R Γ Δ = none)
  (hwit : ProcessedWitnessed P (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset)) :
  (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).HasFailingLeaf :=
  (hasFailingLeaf_of_eq_none_aux ((R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).lobMeasure P)).2
    P R Γ Δ le_rfl h hwit


/-! ### Completeness of `search0`: countermodel extraction and decidability -/

open LabelledSequent in
/-- **Completeness of the proof search**: if `search0 R Γ Δ = none`, there is a finite
Kripke countermodel of the labelled sequent `R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset`. -/
theorem exists_countermodel_of_search0_eq_none
  {R : List LabelRel} {Γ Δ : List (LabelledFormula α)}
  (h : search0 R Γ Δ = none) :
  ∃ (κ : Type) (_ : Nonempty κ) (M : Model κ α) (_ : M.IsFiniteGL) (L : M.LabelMap),
    ¬M ⊧ˡ[L] (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset) :=
  exists_countermodel_of_hasFailingLeaf
    (search_eq_none_hasFailingLeaf h ProcessedWitnessed.empty)

open LabelledSequent in
/-- The proof search is complete: `search0` succeeds exactly on the provable sequents
(of list-represented components). -/
theorem isSome_search0_iff_provableLabelledGentzen
  {R : List LabelRel} {Γ Δ : List (LabelledFormula α)} :
  (search0 R Γ Δ).isSome ↔ ⊢ˡ (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset) := by
  constructor;
  · intro h;
    exact ⟨(search0 R Γ Δ).get h⟩;
  · intro hprov;
    rcases hs : search0 R Γ Δ with _ | π;
    · exfalso;
      obtain ⟨κ, _, M, _, L, hM⟩ := exists_countermodel_of_search0_eq_none hs;
      exact hM (ProvableLabelledGentzen.Kripke.soundness hprov M L);
    · simp;

/-- `ProvableLabelledGentzen` of a labelled sequent given by list-represented components is
decidable, by running the proof search `search0`. -/
instance decidable_provableLabelledGentzen_ofLists
  (R : List LabelRel) (Γ Δ : List (LabelledFormula α)) :
  Decidable (⊢ˡ (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset)) :=
  decidable_of_iff _ isSome_search0_iff_provableLabelledGentzen

/-- `ProvableLabelledGentzen` of a single labelled formula is decidable. -/
instance decidable_provableLabelledGentzen_singleton (x : Label) (A : Formula α) :
  Decidable (⊢ˡ (∅ ⸴ ∅ ⟹ˡ {x ∶ A})) :=
  decidable_of_iff (⊢ˡ (([] : List LabelRel).toFinset ⸴
    ([] : List (LabelledFormula α)).toFinset ⟹ˡ [x ∶ A].toFinset)) (by simp)

end LabelledGentzen

end
