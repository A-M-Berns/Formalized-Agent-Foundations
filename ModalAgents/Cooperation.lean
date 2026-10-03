/-
  Cooperation analysis for modal agents (Barasz, §3-4).

  `outcome X Y` is the GL formula corresponding to the paper's
  `ψ_{[X(Y)]}` (§4, Thm 4.7). `outcome_fixed_point` is the GL-level
  fixed-point equation. The arithmetical lifts of `Cooperates` and
  `ProvablyDefects` (§4, Thm 4.1) live in `ModalAgents/Arithmetic.lean`: this
  file deliberately imports no first-order layer, because Foundation's global
  `□`/`∼` notations would otherwise capture the parse of the modal ones here.
-/

import ModalAgents.FixedPoint

open LogicGL Formula

/-- Substitute atom 0 ↦ `β`, atoms 1,…,m ↦ `refs 0,…,refs (m-1)`;
atoms > m unchanged. -/
abbrev substFull (β : Formula ℕ) {m : ℕ} (refs : Fin m → Formula ℕ) : Formula.Substitution ℕ ℕ :=
  fun k => match k with
    | 0 => β
    | j + 1 => if h : j < m then refs ⟨j, h⟩ else .atom (j + 1)

/-- For `k ≠ 0`, `substFull β refs k` is modalized in atom 0 whenever each
`refs j` omits atom 0. -/
lemma substFull_modalized_step {m : ℕ} (β : Formula ℕ)
    (refs : Fin m → Formula ℕ) (hrefs : ∀ j, 0 ∉ (refs j).atoms)
    {k : ℕ} (hk : k ≠ 0) : Modalized 0 (substFull β refs k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  show Modalized 0 (if h : k < m then refs ⟨k, h⟩ else .atom (k+1))
  by_cases hk' : k < m
  · rw [dite_eq_left hk']
    exact modalized_of_notMem_atoms (hrefs ⟨k, hk'⟩)
  · rw [dite_eq_right hk']
    show k+1 ≠ 0
    exact Nat.succ_ne_zero k

/-- `X.formula⟦substFull β refs⟧` is modalized in atom 0 whenever each
`refs i` omits atom 0. -/
lemma modalized_substFull (X : ModalAgent) (β : Formula ℕ)
    (refs : Fin X.arity → Formula ℕ) (hrefs : ∀ i, 0 ∉ (refs i).atoms) :
    Modalized 0 (X.formula⟦substFull β refs⟧) :=
  modalized_subst (fun _ hk => substFull_modalized_step β refs hrefs hk)
    (X.modalized 0 (Nat.zero_le _))

/-! ## Outcomes -/

/-- GL formula corresponding to the paper's `ψ_{[X(Y)]}` (Barasz, §4). -/
noncomputable def outcome (X Y : ModalAgent) : Formula ℕ :=
  glFixedPoint 0
    (X.formula⟦substFull
      (Y.formula⟦substFull (.atom 0)
        (fun j : Fin Y.arity => outcome X (Y.references j))⟧)
      (fun i : Fin X.arity => outcome Y (X.references i))⟧)
termination_by X.rank + Y.rank
decreasing_by
  all_goals first
    | (have h := ModalAgent.rank_ref_lt Y j; omega)
    | (have h := ModalAgent.rank_ref_lt X i; omega)

/-- Two-level operator. `F_of X Y (.atom 0)` is the formula whose
GL fixed point is `outcome X Y`. -/
noncomputable def F_of (X Y : ModalAgent) (p : Formula ℕ) : Formula ℕ :=
  X.formula⟦substFull
    (Y.formula⟦substFull p (fun j : Fin Y.arity => outcome X (Y.references j))⟧)
    (fun i : Fin X.arity => outcome Y (X.references i))⟧

/-- Bridge between the recursive definition of `outcome` and `F_of`. -/
lemma outcome_unfold (X Y : ModalAgent) :
    outcome X Y = glFixedPoint 0 (F_of X Y (.atom 0)) := by
  rw [outcome]; rfl

/-- Atom 0 doesn't appear in `outcome X Y`. -/
lemma outcome_atoms_notMem (X Y : ModalAgent) : 0 ∉ (outcome X Y).atoms := by
  intro hmem
  rw [outcome_unfold] at hmem
  have hMod : Modalized 0 (F_of X Y (.atom 0)) :=
    modalized_substFull X _ _ (fun i => outcome_atoms_notMem Y (X.references i))
  exact (glFixedPoint_atoms hMod 0 hmem).2 rfl
termination_by X.rank + Y.rank
decreasing_by have h := ModalAgent.rank_ref_lt X i; omega

/-- `F_of X Y p` is modalized in atom 0 for any `p`: X.formula's atom-0
occurrences are already under boxes, and the outer references omit atom 0. -/
lemma F_of_modalized (X Y : ModalAgent) (p : Formula ℕ) : Modalized 0 (F_of X Y p) :=
  modalized_substFull X _ _ (fun _ => outcome_atoms_notMem _ _)

/-! ## Substitution lemmas -/

/-- Substitutions compose: `(φ⟦s₁⟧)⟦s₂⟧ = φ⟦fun a => (s₁ a)⟦s₂⟧⟧`. -/
lemma Formula.subst_subst (s₁ s₂ : Formula.Substitution ℕ ℕ) :
    ∀ φ : Formula ℕ, (φ⟦s₁⟧)⟦s₂⟧ = φ⟦fun a => (s₁ a)⟦s₂⟧⟧
  | .atom _ => rfl
  | .bot => rfl
  | .imp φ ψ => by
    show (φ⟦s₁⟧)⟦s₂⟧ 🡒 (ψ⟦s₁⟧)⟦s₂⟧ = φ⟦fun a => (s₁ a)⟦s₂⟧⟧ 🡒 ψ⟦fun a => (s₁ a)⟦s₂⟧⟧
    rw [Formula.subst_subst s₁ s₂ φ, Formula.subst_subst s₁ s₂ ψ]
  | .box φ => by
    show □((φ⟦s₁⟧)⟦s₂⟧) = □(φ⟦fun a => (s₁ a)⟦s₂⟧⟧)
    rw [Formula.subst_subst s₁ s₂ φ]

/-- Substitution composition: `substFull β refs` post-composed with
`diag 0 χ` equals `substFull (β⟦diag 0 χ⟧) refs`, provided each `refs j`
doesn't mention atom 0. -/
lemma substFull_comp_diag_of_notMem (β χ : Formula ℕ) {m : ℕ}
    (refs : Fin m → Formula ℕ) (hrefs : ∀ j, 0 ∉ (refs j).atoms) :
    (fun a => (substFull β refs a)⟦diag 0 χ⟧) = substFull (β⟦diag 0 χ⟧) refs := by
  funext k
  match k with
  | 0 => rfl
  | j+1 =>
    show (if h : j < m then refs ⟨j, h⟩ else .atom (j+1))⟦diag 0 χ⟧
       = if h : j < m then refs ⟨j, h⟩ else .atom (j+1)
    by_cases h : j < m
    · rw [dite_eq_left h]
      exact subst_diag_of_notMem_atoms (hrefs ⟨j, h⟩)
    · rw [dite_eq_right h]
      show diag 0 χ (j+1) = .atom (j+1)
      simp [diag, Formula.Substitution.single]

/-- Substitution identity: `F_of X Y (.atom 0)` with atom 0 instantiated
to `ψ` equals `F_of X Y ψ`. -/
lemma F_of_subst (X Y : ModalAgent) (ψ : Formula ℕ) :
    (F_of X Y (.atom 0))⟦diag 0 ψ⟧ = F_of X Y ψ := by
  unfold F_of
  rw [Formula.subst_subst,
      substFull_comp_diag_of_notMem _ _ _ (fun _ => outcome_atoms_notMem _ _),
      Formula.subst_subst,
      substFull_comp_diag_of_notMem _ _ _ (fun _ => outcome_atoms_notMem _ _)]
  rfl

/-- For zero-reference substitutions, changing the atom-0 replacement is the
only nontrivial substitution case. -/
lemma substFull_zero_congr (φ β γ : Formula ℕ) (refs : Fin 0 → Formula ℕ)
    (h : (β 🡘 γ) ∈ (LogicGL : Logic ℕ)) :
    (φ⟦substFull β refs⟧ 🡘 φ⟦substFull γ refs⟧) ∈ (LogicGL : Logic ℕ) := by
  apply subst_congr
  intro a
  cases a with
  | zero => exact h
  | succ k =>
    show ((if hk : k < 0 then refs ⟨k, hk⟩ else .atom (k + 1)) 🡘
      (if hk : k < 0 then refs ⟨k, hk⟩ else .atom (k + 1))) ∈ (LogicGL : Logic ℕ)
    exact GL.iff_refl

/-! ## Fixed-point equations -/

/-- Two-level fixed-point equation for `outcome`. -/
lemma outcome_twoLevel (X Y : ModalAgent) :
    (outcome X Y 🡘 F_of X Y (outcome X Y)) ∈ (LogicGL : Logic ℕ) := by
  have h := glFixedPoint_spec (F_of_modalized X Y (.atom 0))
  rw [← outcome_unfold, F_of_subst] at h
  exact h

/-- GL-level form of the modal-agent fixed-point equation: `outcome X Y` is
the fixed point `ψ_{[X(Y)]}` of `X`'s modal formula applied to `Y`'s outcomes.

Paper node: Theorem 4.7 (§4). -/
theorem outcome_fixed_point (X Y : ModalAgent) :
    (outcome X Y 🡘
      X.formula⟦substFull (outcome Y X)
        (fun j : Fin X.arity => outcome Y (X.references j))⟧) ∈ (LogicGL : Logic ℕ) := by
  set K := X.formula⟦substFull (outcome Y X)
    (fun i : Fin X.arity => outcome Y (X.references i))⟧
  have hYX' : (outcome Y X 🡘
      Y.formula⟦substFull K (fun j : Fin Y.arity => outcome X (Y.references j))⟧) ∈
        (LogicGL : Logic ℕ) :=
    outcome_twoLevel Y X
  have hKfp : (K 🡘 F_of X Y K) ∈ (LogicGL : Logic ℕ) := by
    unfold F_of
    apply subst_congr
    intro a
    match a with
    | 0 => exact hYX'
    | _+1 => exact GL.iff_refl
  have hMod := F_of_modalized X Y (.atom 0)
  have hα' : (outcome X Y 🡘 (F_of X Y (.atom 0))⟦diag 0 (outcome X Y)⟧) ∈ (LogicGL : Logic ℕ) := by
    rw [F_of_subst]; exact outcome_twoLevel X Y
  have hKfp' : (K 🡘 (F_of X Y (.atom 0))⟦diag 0 K⟧) ∈ (LogicGL : Logic ℕ) := by
    rw [F_of_subst]; exact hKfp
  exact glFixedPoint_uniqueness hMod hα' hKfp'

/-! ## Concrete-agent formula reductions -/

@[simp] lemma cooperateBot_formula_substFull
    (β : Formula ℕ) {m : ℕ} (refs : Fin m → Formula ℕ) :
    cooperateBot.formula⟦substFull β refs⟧ = (⊤ : Formula ℕ) := rfl

@[simp] lemma defectBot_formula_substFull
    (β : Formula ℕ) {m : ℕ} (refs : Fin m → Formula ℕ) :
    defectBot.formula⟦substFull β refs⟧ = (⊥ : Formula ℕ) := rfl

@[simp] lemma fairBot_formula_substFull
    (β : Formula ℕ) {m : ℕ} (refs : Fin m → Formula ℕ) :
    fairBot.formula⟦substFull β refs⟧ = □β := rfl

@[simp] lemma prudentBot_formula_substFull
    (β : Formula ℕ) {m : ℕ} (refs : Fin m → Formula ℕ) :
    prudentBot.formula⟦substFull β refs⟧ = □β ⋏ □(∼□⊥ 🡒 ∼(substFull β refs 1)) := rfl

/-! ## Cooperation predicates -/

/-- X cooperates with Y: GL proves the outcome formula. -/
def Cooperates (X Y : ModalAgent) : Prop := outcome X Y ∈ (LogicGL : Logic ℕ)

/-- X defects against Y, rendered as: GL does not prove the outcome formula.

This is strictly weaker than `ProvablyDefects` below, which is the paper's notion —
`ProvablyDefects.defects` is the one-way implication, and there is no converse.
Where the strong form is available it is stated and used instead
(`defectBot_provably_defects`); this predicate remains the endpoint form in exactly
the three places where the strong form is *not available in `GL` at all*, for a
reason that is itself proved here:

* `fairBot_vs_defectBot` — `outcome fairBot defectBot` is GL-equivalent to `□⊥`
  (`outcome_fairBot_defectBot`), so the strong form is `GL ⊢ ∼□⊥`, i.e. `GL`
  proving its own consistency;
* `prudentBot_vs_defectBot` — likewise GL-equivalent to `□⊥`
  (`outcome_prudentBot_defectBot`);
* `prudentBot_vs_cooperateBot` — GL-equivalent to `□□⊥`
  (`outcome_prudentBot_cooperateBot`), so the strong form is `GL ⊢ ∼□□⊥`,
  i.e. `GL` proving `Con(PA+1)`.

`unprovable_neg_box_bot` and `unprovable_neg_box_box_bot` show `GL` proves neither,
and `fairBot_not_provably_defects_defectBot`,
`prudentBot_not_provably_defects_defectBot` and
`prudentBot_not_provably_defects_cooperateBot` land the consequence: on those three
endpoints the weak form is forced, not a shortcut. This tracks the paper exactly,
which states them as `PA+1 ⊢ [FB(DB)=D]`, `PA+1 ⊢ [PB(DB)=D]` and
`PA+2 ⊢ [PB(CB)=D]` — one and two reflection steps above the `PA` that `GL` models.
See the modeling boundary in `ModalAgents/README.md`. -/
def Defects (X Y : ModalAgent) : Prop := outcome X Y ∉ (LogicGL : Logic ℕ)

/-- X provably defects against Y: GL proves the outcome formula *false*. This is the
paper's notion of defection (`PA ⊢ [X(Y)=D]`), and unlike `Defects` it is a positive
`GL` claim, so it lifts to arithmetic through `ProvablyDefects.arithmeticLift`. -/
def ProvablyDefects (X Y : ModalAgent) : Prop := (∼(outcome X Y)) ∈ (LogicGL : Logic ℕ)

/-- Provable defection implies defection, by consistency of `GL`. The converse fails,
and for the three endpoints listed at `Defects` it fails unavoidably. -/
lemma ProvablyDefects.defects {X Y : ModalAgent} (h : ProvablyDefects X Y) :
    Defects X Y := fun hc => GL.bot_not_mem (GL.mdp h hc)

/-! ## Cooperation theorems -/

/-- `outcome defectBot Y ↔ ⊥` for every Y. -/
lemma outcome_defectBot (Y : ModalAgent) :
    (outcome defectBot Y 🡘 ⊥) ∈ (LogicGL : Logic ℕ) := by
  have h := outcome_fixed_point defectBot Y
  simpa [defectBot_formula_substFull] using h

/-- `outcome cooperateBot Y ↔ ⊤` for every Y. -/
lemma outcome_cooperateBot (Y : ModalAgent) :
    (outcome cooperateBot Y 🡘 ⊤) ∈ (LogicGL : Logic ℕ) := by
  have h := outcome_fixed_point cooperateBot Y
  simpa [cooperateBot_formula_substFull] using h

/-- `outcome fairBot Y ↔ □(outcome Y fairBot)` for every Y. -/
lemma outcome_fairBot (Y : ModalAgent) :
    (outcome fairBot Y 🡘 □(outcome Y fairBot)) ∈ (LogicGL : Logic ℕ) := by
  have h := outcome_fixed_point fairBot Y
  simpa [fairBot_formula_substFull] using h

/-- `outcome prudentBot Y ↔ □(outcome Y prudentBot) ⋏ □(∼□⊥ 🡒 ∼(outcome Y defectBot))`
for every Y. -/
lemma outcome_prudentBot (Y : ModalAgent) :
    (outcome prudentBot Y 🡘
      (□(outcome Y prudentBot) ⋏ □(∼□⊥ 🡒 ∼(outcome Y defectBot)))) ∈ (LogicGL : Logic ℕ) := by
  have h := outcome_fixed_point prudentBot Y
  rw [prudentBot_formula_substFull] at h
  have e : substFull (outcome Y prudentBot)
      (fun j : Fin prudentBot.arity => outcome Y (prudentBot.references j)) 1 =
      outcome Y defectBot := rfl
  rw [e] at h
  exact h

/-- DefectBot *provably* defects against every opponent — the paper's own
`PA ⊢ [DB(X)=D]`, at full strength, since `outcome defectBot Y` is GL-equivalent to
`⊥`. Barasz states this as §2 prose in an unnumbered remark, so it carries no
paper-node annotation. -/
lemma defectBot_provably_defects (Y : ModalAgent) : ProvablyDefects defectBot Y :=
  GL.and_elim_left (outcome_defectBot Y)

/-- DefectBot defects against every opponent — the weak form, for uniformity with the
other defection endpoints. `defectBot_provably_defects` is the strong form. -/
lemma defectBot_defects (Y : ModalAgent) : Defects defectBot Y :=
  (defectBot_provably_defects Y).defects

/-- CooperateBot cooperates with every opponent. Barasz states this as §2 prose
(`PA ⊢ [CB(X)=C]`, in an unnumbered remark), so it carries no paper-node
annotation. -/
lemma cooperateBot_cooperates (Y : ModalAgent) : Cooperates cooperateBot Y :=
  GL.mdp (GL.and_elim_right (outcome_cooperateBot Y)) GL.top

/-! ## Concrete cooperation: rank 0 -/

/-- FairBot cooperates with itself, by the Löbian circle.

Paper node: Theorem 3.1 (§3). -/
theorem fairBot_vs_fairBot : Cooperates fairBot fairBot := by
  have hα := outcome_fairBot fairBot
  have h : (outcome fairBot fairBot ⋏ outcome fairBot fairBot) ∈ (LogicGL : Logic ℕ) :=
    lobian_circle (GL.and_elim_right hα) (GL.and_elim_right hα)
  exact GL.and_elim_left h

/-- **FairBot is unexploitable.** Barasz asserts this in §3 "by inspection"
(presuming `PA` sound, FairBot never cooperates with an opponent that defects against
it), in unnumbered prose, so this carries no paper-node annotation.

The statement is the same shape as `prudentBot_unexploitable`: "`Y` exploits FairBot" is
`Cooperates fairBot Y ∧ Defects Y fairBot`, so unexploitability is the implication
below.  As there, the paper's appeal to soundness of `PA` is discharged here by `GL`'s
admissible unnecessitation rule `□φ / φ`, so the conclusion lands at `Cooperates` —
arithmetically liftable — with no soundness side-hypothesis. -/
lemma fairBot_unexploitable (Y : ModalAgent) :
    Cooperates fairBot Y → Cooperates Y fairBot := by
  intro h
  have hα := outcome_fairBot Y
  exact unnecessitation (GL.mdp (GL.and_elim_left hα) h)

/-- FairBot and CooperateBot mutually cooperate. Barasz notes this only as §3
prose ("FairBot wastes utility by cooperating even with CooperateBot"), so it
carries no paper-node annotation. -/
lemma fairBot_vs_cooperateBot :
    Cooperates fairBot cooperateBot ∧ Cooperates cooperateBot fairBot := by
  have hα := outcome_fairBot cooperateBot
  have h_cb := cooperateBot_cooperates fairBot
  exact ⟨GL.mdp (GL.and_elim_right hα) (GL.nec h_cb), cooperateBot_cooperates fairBot⟩

/-- GL-level form: a rank-0 modal agent that cooperates with FairBot also
cooperates with CooperateBot.

Paper node: Theorem 4.10 (§4). -/
theorem rank0_fairBot_implies_cooperateBot (X : ModalAgent) (h_rank : X.rank = 0) :
    Cooperates X fairBot → Cooperates X cooperateBot := by
  intro hXF
  have h_arity := ModalAgent.arity_eq_zero_of_rank_eq_zero h_rank
  cases X with
  | mk φ n refs mod =>
    simp [ModalAgent.arity] at h_arity
    subst n
    let X : ModalAgent := ModalAgent.mk φ 0 refs mod
    change Cooperates X cooperateBot
    change Cooperates X fairBot at hXF
    have hXFB_fp := outcome_fixed_point X fairBot
    have hFBX := outcome_fairBot X
    have h_to_box : (φ⟦substFull (outcome fairBot X)
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧ 🡘
        φ⟦substFull (□(outcome X fairBot))
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧) ∈ (LogicGL : Logic ℕ) :=
      substFull_zero_congr φ (outcome fairBot X) (□(outcome X fairBot))
        (fun j : Fin 0 => outcome fairBot (X.references j)) hFBX
    have h_phi_box : (φ⟦substFull (□(outcome X fairBot))
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧) ∈ (LogicGL : Logic ℕ) :=
      GL.iff_mp h_to_box (GL.iff_mp hXFB_fp hXF)
    have h_box_top : (□(outcome X fairBot) 🡘 (⊤ : Formula ℕ)) ∈ (LogicGL : Logic ℕ) :=
      GL.and_intro (GL.imp_of_mem GL.top) (GL.imp_of_mem (GL.nec hXF))
    have h_to_top : (φ⟦substFull (□(outcome X fairBot))
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧ 🡘
        φ⟦substFull (⊤ : Formula ℕ)
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧) ∈ (LogicGL : Logic ℕ) :=
      substFull_zero_congr φ (□(outcome X fairBot)) (⊤ : Formula ℕ)
        (fun j : Fin 0 => outcome fairBot (X.references j)) h_box_top
    have h_phi_top : (φ⟦substFull (⊤ : Formula ℕ)
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧) ∈ (LogicGL : Logic ℕ) :=
      GL.iff_mp h_to_top h_phi_box
    have hCBX := outcome_cooperateBot X
    have h_to_cb : (φ⟦substFull (outcome cooperateBot X)
          (fun j : Fin 0 => outcome cooperateBot (X.references j))⟧ 🡘
        φ⟦substFull (⊤ : Formula ℕ)
          (fun j : Fin 0 => outcome cooperateBot (X.references j))⟧) ∈ (LogicGL : Logic ℕ) :=
      substFull_zero_congr φ (outcome cooperateBot X) (⊤ : Formula ℕ)
        (fun j : Fin 0 => outcome cooperateBot (X.references j)) hCBX
    have hXCB_fp := outcome_fixed_point X cooperateBot
    have h_rhs_cb : (φ⟦substFull (outcome cooperateBot X)
          (fun j : Fin 0 => outcome cooperateBot (X.references j))⟧) ∈ (LogicGL : Logic ℕ) := by
      -- the two zero-reference substitutions of `⊤` coincide (no reference is ever read)
      have e : (φ⟦substFull (⊤ : Formula ℕ)
            (fun j : Fin 0 => outcome fairBot (X.references j))⟧) =
          φ⟦substFull (⊤ : Formula ℕ)
            (fun j : Fin 0 => outcome cooperateBot (X.references j))⟧ := by
        congr 1
      exact GL.iff_mpr h_to_cb (e ▸ h_phi_top)
    exact GL.iff_mpr hXCB_fp h_rhs_cb

/-- FairBot and DefectBot mutually defect. Barasz states FairBot's
unexploitability as §3 prose ("by inspection"), so this carries no paper-node
annotation.

DefectBot's half is at the paper's strength (`defectBot_provably_defects`). FairBot's
half is `Defects`, and it cannot be strengthened: `outcome fairBot defectBot` is
GL-equivalent to `□⊥` (`outcome_fairBot_defectBot`), so provable defection would be
`GL ⊢ ∼□⊥` — see `fairBot_not_provably_defects_defectBot`. The paper accordingly
states this one in `PA+1`. -/
lemma fairBot_vs_defectBot :
    Defects fairBot defectBot ∧ Defects defectBot fairBot := by
  have hα := outcome_fairBot defectBot
  have hβ := outcome_defectBot fairBot
  refine ⟨?_, defectBot_defects fairBot⟩
  intro ha
  have h_box : (□(outcome defectBot fairBot)) ∈ (LogicGL : Logic ℕ) :=
    GL.mdp (GL.and_elim_left hα) ha
  have h_imp : (outcome defectBot fairBot 🡒 ⊥) ∈ (LogicGL : Logic ℕ) := GL.and_elim_left hβ
  exact unprovable_box_bot (GL.mdp (GL.box_imp h_imp) h_box)

/-- **PrudentBot is unexploitable** — the first conjunct of the node below, and the
only one that quantifies over all opponents.

"`Y` exploits PrudentBot" is `Cooperates prudentBot Y ∧ Defects Y prudentBot`: the
sucker's payoff, PrudentBot cooperating into a defection. Its negation, for every `Y`,
is the implication stated here, since `Defects Y prudentBot` is
`outcome Y prudentBot ∉ LogicGL` and its classical negation is
`Cooperates Y prudentBot`.

The argument is the paper's, in modal form: PrudentBot cooperates only given a *proof*
that its opponent cooperates back, and the paper cashes that proof out by soundness of
`PA`. Here the corresponding step is `GL`'s unnecessitation rule `□φ / φ`, which is
admissible in `GL` (`unnecessitation`, by a root extension of a refuting finite model).
So the conclusion needs no soundness side-assumption and lands at full strength —
`Cooperates`, hence liftable by `Cooperates.arithmeticLift` — rather than at the
weakened `¬ Defects`.

Paper node: Theorem 3.2 (§3). -/
theorem prudentBot_unexploitable (Y : ModalAgent) :
    Cooperates prudentBot Y → Cooperates Y prudentBot := by
  intro h
  have hα := outcome_prudentBot Y
  exact unnecessitation (GL.and_elim_left (GL.mdp (GL.and_elim_left hα) h))

/-- PrudentBot and FairBot mutually cooperate — the "mutually cooperates …
with FairBot" conjunct of the node below.

Paper node: Theorem 3.2 (§3). -/
theorem prudentBot_vs_fairBot :
    Cooperates prudentBot fairBot ∧ Cooperates fairBot prudentBot := by
  have hα := outcome_prudentBot fairBot
  have hFBvsPB := outcome_fairBot prudentBot
  have hFBvsDB := outcome_fairBot defectBot
  have hDBvsFB := outcome_defectBot fairBot
  have h_FBvsDB_to_boxbot : (outcome fairBot defectBot 🡒 □(⊥ : Formula ℕ)) ∈ (LogicGL : Logic ℕ) :=
    GL.imp_trans (GL.and_elim_left hFBvsDB) (GL.box_imp (GL.and_elim_left hDBvsFB))
  have h_consist : (□(∼□(⊥ : Formula ℕ) 🡒 ∼(outcome fairBot defectBot))) ∈ (LogicGL : Logic ℕ) :=
    GL.nec (GL.contra h_FBvsDB_to_boxbot)
  have h : (outcome prudentBot fairBot ⋏ outcome fairBot prudentBot) ∈ (LogicGL : Logic ℕ) :=
    lobian_circle (GL.and_elim_right hFBvsPB)
      (GL.imp_trans (GL.and_intro_imp GL.imp_id (GL.imp_of_mem h_consist)) (GL.and_elim_right hα))
  exact ⟨GL.and_elim_left h, GL.and_elim_right h⟩

/-- PrudentBot and DefectBot mutually defect. This is the "in particular,
`PA+1 ⊢ [PB(DB)=D]`" step *inside* the proof of Barasz §3, Thm 3.2, not one of
that theorem's four conjuncts, so it carries no paper-node annotation.

DefectBot's half is at the paper's strength (`defectBot_provably_defects`).
PrudentBot's half is `Defects` and cannot be strengthened: `outcome prudentBot
defectBot` is GL-equivalent to `□⊥` (`outcome_prudentBot_defectBot`), so provable
defection would be `GL ⊢ ∼□⊥` — see `prudentBot_not_provably_defects_defectBot`.
That is why the paper's own statement of this step is in `PA+1`. -/
lemma prudentBot_vs_defectBot :
    Defects prudentBot defectBot ∧ Defects defectBot prudentBot := by
  have hα := outcome_prudentBot defectBot
  have hβ := outcome_defectBot prudentBot
  refine ⟨?_, defectBot_defects prudentBot⟩
  intro ha
  have h_box : (□(outcome defectBot prudentBot)) ∈ (LogicGL : Logic ℕ) :=
    GL.and_elim_left (GL.mdp (GL.and_elim_left hα) ha)
  have h_imp : (outcome defectBot prudentBot 🡒 ⊥) ∈ (LogicGL : Logic ℕ) := GL.and_elim_left hβ
  exact unprovable_box_bot (GL.mdp (GL.box_imp h_imp) h_box)

/-- PrudentBot defects against CooperateBot; CooperateBot cooperates
with PrudentBot. The first component is the "defects against CooperateBot"
conjunct of the node below.

**Disclosed weakening, and its cause.** That conjunct is `PA+2 ⊢ [PB(CB)=D]` in the
paper — provable defection. Here it is `Defects`, i.e. `GL ⊬ outcome`. The gap is not
a shortcut: `outcome prudentBot cooperateBot` is GL-equivalent to `□□⊥`
(`outcome_prudentBot_cooperateBot`), so provable defection would be `GL ⊢ ∼□□⊥`, i.e.
`GL` proving `Con(PA+1)`, which it does not
(`prudentBot_not_provably_defects_cooperateBot`). `PA+2` is exactly the strength the
paper needs and `GL` lacks. The cooperation component is at full strength and lifts
through `Cooperates.arithmeticLift`. The node's remaining conjuncts are carried by
`prudentBot_unexploitable`, `prudentBot_vs_prudentBot` and `prudentBot_vs_fairBot`.

Paper node: Theorem 3.2 (§3). -/
theorem prudentBot_vs_cooperateBot :
    Defects prudentBot cooperateBot ∧ Cooperates cooperateBot prudentBot := by
  have hα := outcome_prudentBot cooperateBot
  refine ⟨?_, cooperateBot_cooperates prudentBot⟩
  intro ha
  have h_right : (□(∼□(⊥ : Formula ℕ) 🡒 ∼(outcome cooperateBot defectBot))) ∈ (LogicGL : Logic ℕ) :=
    GL.and_elim_right (GL.mdp (GL.and_elim_left hα) ha)
  have h_cbdb := cooperateBot_cooperates defectBot
  have h_flip : (□(outcome cooperateBot defectBot 🡒 □(⊥ : Formula ℕ))) ∈ (LogicGL : Logic ℕ) :=
    GL.mdp (GL.box_imp GL.elimContra) h_right
  have h_boxbox : (□(□(⊥ : Formula ℕ))) ∈ (LogicGL : Logic ℕ) :=
    GL.mdp (GL.mdp GL.axiomK h_flip) (GL.nec h_cbdb)
  exact unprovable_box_box_bot h_boxbox

/-- PrudentBot cooperates with itself — the "mutually cooperates with itself"
conjunct of the node below.

Paper node: Theorem 3.2 (§3). -/
theorem prudentBot_vs_prudentBot : Cooperates prudentBot prudentBot := by
  have hα := outcome_prudentBot prudentBot
  have hg := outcome_prudentBot defectBot
  have hβ := outcome_defectBot prudentBot
  have h_g_to_boxbot : (outcome prudentBot defectBot 🡒 □(⊥ : Formula ℕ)) ∈ (LogicGL : Logic ℕ) :=
    GL.imp_trans (GL.imp_trans (GL.and_elim_left hg) GL.and_left)
      (GL.box_imp (GL.and_elim_left hβ))
  have h_consist : (□(∼□(⊥ : Formula ℕ) 🡒 ∼(outcome prudentBot defectBot))) ∈ (LogicGL : Logic ℕ) :=
    GL.nec (GL.contra h_g_to_boxbot)
  have h₁ : (□(outcome prudentBot prudentBot) 🡒
      (□(outcome prudentBot prudentBot) ⋏
        □(∼□(⊥ : Formula ℕ) 🡒 ∼(outcome prudentBot defectBot)))) ∈ (LogicGL : Logic ℕ) :=
    GL.and_intro_imp GL.imp_id (GL.imp_of_mem h_consist)
  exact lob_rule (GL.imp_trans h₁ (GL.and_elim_right hα))

/-! ## The defection boundary

`defectBot_provably_defects` gives defection at the paper's strength. The three
remaining defection endpoints cannot: each of their outcome formulas is GL-equivalent
to an iterated `□⊥`, so the strong form asks `GL` for a consistency statement, and by
Gödel's second incompleteness theorem it has none. The equivalences below make that
exact, and the three `¬ ProvablyDefects` results are the consequence.

The reflection depth matches the paper step for step: `□⊥` here is `PA+1` there
(`PA+1 ⊢ [FB(DB)=D]`, `PA+1 ⊢ [PB(DB)=D]`) and `□□⊥` is `PA+2`
(`PA+2 ⊢ [PB(CB)=D]`). PrudentBot's own definition already reads its opponent's
behaviour against DefectBot under `∼□⊥ 🡒 ·` for precisely this reason — the paper's
remark after Theorem 3.2 is that the extra reflection step is load-bearing. -/

/-- Against DefectBot, FairBot's outcome is GL-equivalent to `□⊥`: FairBot cooperates
exactly when it can prove DefectBot's (refutable) cooperation. -/
lemma outcome_fairBot_defectBot :
    (outcome fairBot defectBot 🡘 □(⊥ : Formula ℕ)) ∈ (LogicGL : Logic ℕ) :=
  GL.iff_trans (outcome_fairBot defectBot) (GL.box_iff (outcome_defectBot fairBot))

/-- Against DefectBot, PrudentBot's outcome is GL-equivalent to `□⊥` as well: `□⊥`
already gives both of PrudentBot's conjuncts. -/
lemma outcome_prudentBot_defectBot :
    (outcome prudentBot defectBot 🡘 □(⊥ : Formula ℕ)) ∈ (LogicGL : Logic ℕ) := by
  have hα := outcome_prudentBot defectBot
  have hβ := outcome_defectBot prudentBot
  exact GL.and_intro
    (GL.imp_trans (GL.imp_trans (GL.and_elim_left hα) GL.and_left)
      (GL.box_imp (GL.and_elim_left hβ)))
    (GL.imp_trans (GL.and_intro_imp GL.box_of_boxBot GL.box_of_boxBot) (GL.and_elim_right hα))

/-- `A 🡒 (∼A 🡒 B)`: a formula and its negation yield anything. -/
private lemma GL.imp_neg_imp {A B : Formula ℕ} : (A 🡒 (∼A 🡒 B)) ∈ (LogicGL : Logic ℕ) := by
  apply GL.of_provable
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hA : {∼A, A} ⊢ʰ[GL] A := DeducibleHilbert.ofContext (by grind)
  have hnA : {∼A, A} ⊢ʰ[GL] A 🡒 ⊥ := DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.efq) (DeducibleHilbert.mdp hnA hA)

/-- Against CooperateBot, PrudentBot's outcome is GL-equivalent to `□□⊥`: the first
conjunct is outright provable, and the second — PrudentBot's `PA+1` check that
CooperateBot defects against DefectBot — is what costs the second box. -/
lemma outcome_prudentBot_cooperateBot :
    (outcome prudentBot cooperateBot 🡘 □(□(⊥ : Formula ℕ))) ∈ (LogicGL : Logic ℕ) := by
  have hα := outcome_prudentBot cooperateBot
  have hcbdb := cooperateBot_cooperates defectBot
  have hcbpb := cooperateBot_cooperates prudentBot
  refine GL.and_intro ?_ ?_
  · -- `outcome 🡒 □(∼□⊥ 🡒 ∼X) 🡒 □(X 🡒 □⊥) 🡒 □□⊥`, the last step because `□X` is a theorem
    refine GL.imp_trans (GL.imp_trans (GL.imp_trans (GL.and_elim_left hα) GL.and_right)
      (GL.box_imp GL.elimContra)) ?_
    exact GL.under_mdp GL.axiomK (GL.imp_of_mem (GL.nec hcbdb))
  · exact GL.imp_trans
      (GL.and_intro_imp (GL.imp_of_mem (GL.nec hcbpb)) (GL.box_imp GL.imp_neg_imp))
      (GL.and_elim_right hα)

/-- FairBot's defection against DefectBot is **not** available at the paper's
strength: `GL ⊢ ∼(outcome fairBot defectBot)` is `GL ⊢ ∼□⊥`, which is `GL` proving
its own consistency. Hence `fairBot_vs_defectBot` states the weak `Defects` by
necessity, not by convenience. -/
lemma fairBot_not_provably_defects_defectBot : ¬ ProvablyDefects fairBot defectBot :=
  fun h => unprovable_neg_box_bot
    (GL.imp_trans (GL.and_elim_right outcome_fairBot_defectBot) h)

/-- PrudentBot's defection against DefectBot is not available at the paper's strength,
for the same reason as `fairBot_not_provably_defects_defectBot`: it too reduces to
`GL ⊢ ∼□⊥`. The paper states this conjunct in `PA+1`. -/
lemma prudentBot_not_provably_defects_defectBot :
    ¬ ProvablyDefects prudentBot defectBot :=
  fun h => unprovable_neg_box_bot
    (GL.imp_trans (GL.and_elim_right outcome_prudentBot_defectBot) h)

/-- PrudentBot's defection against CooperateBot — Theorem 3.2's last conjunct — is not
available at the paper's strength either: it reduces to `GL ⊢ ∼□□⊥`, i.e. `GL` proving
`Con(PA+1)`. The paper states this conjunct in `PA+2`. -/
lemma prudentBot_not_provably_defects_cooperateBot :
    ¬ ProvablyDefects prudentBot cooperateBot :=
  fun h => unprovable_neg_box_box_bot
    (GL.imp_trans (GL.and_elim_right outcome_prudentBot_cooperateBot) h)
