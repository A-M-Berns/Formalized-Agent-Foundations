import CartesianFrames.Subagent
import Mathlib.Data.Set.Basic

/-!
# Additive and multiplicative subagents

§2.4 of the paper from Definition 18 through Theorem 24, with the equivalence
proofs of Appendix A (Claims 41–44).  Per the settled convention, the paper's
first-presented definitions are primary: committing (Definition 18) owns `◁₊`,
externalizing (Definition 19) owns `◁ₓ`; the currying definitions (20, 21) are
named variants with the equivalences proved as Claims 41–44 and packaged as
Claim 22.

The committing and externalizing definitions render the paper's "there exist sets
X, Y, Z" as existentials over `Type u` (`dd:universe`).  A priori this bounds the
witnesses' size; it is without loss of generality *by Claims 41–44*, whose currying
witnesses are built from `D`'s own carriers, which live in `u`.

**Paper erratum (Claim 43).** The printed proof chooses "some `b ∈ B` (it does not
matter which)" when defining `h₃`, silently assuming `Agent(D)` is nonempty.  The
Lean proof splits on that hypothesis: the paper's construction handles the nonempty
case verbatim, and when `Agent(D)` is empty the equivalence `D ≃ (X × Y, Z, •)`
forces `X × Y` empty, so every adjointness and homotopy obligation below is vacuous
and a degenerate `M` works.  The claim is true as stated.
-/

universe u

namespace CartesianFrames

namespace Frame

open CategoryTheory

variable {W : Type u}

/-! ## The four definitions (Definitions 18–21) -/

/-- Definition 18, the committing definition of additive subagent — the primary
rendering of `C ◁₊ D`: both frames present over a common environment `Z`, with
`C`'s agent a subset of `D`'s.

Paper node: Definition 18 (§2.4). -/
def AddSubagent (C D : Frame W) : Prop :=
  ∃ (Y Z : Type u) (X : Set Y) (f : Y → Z → W),
    (C ≃ᵇ { Agent := X, Env := Z, outcome := fun x z => f x.val z }) ∧
    (D ≃ᵇ { Agent := Y, Env := Z, outcome := f })

@[inherit_doc] scoped infixl:50 " ◁₊ " => AddSubagent

/-- Definition 19, the externalizing definition of multiplicative subagent — the
primary rendering of `C ◁ₓ D`: a three-place outcome function, with the middle
factor on `C`'s environment side and on `D`'s agent side.

Paper node: Definition 19 (§2.4). -/
def MultSubagent (C D : Frame W) : Prop :=
  ∃ (X Y Z : Type u) (f : X → Y → Z → W),
    (C ≃ᵇ { Agent := X, Env := Y × Z, outcome := fun x p => f x p.1 p.2 }) ∧
    (D ≃ᵇ { Agent := X × Y, Env := Z, outcome := fun p z => f p.1 p.2 z })

@[inherit_doc] scoped infixl:50 " ◁ₓ " => MultSubagent

/-- Definition 20, the currying definition of additive subagent: `C ≃ᵇ D°(M)` for
a frame `M` over `D`'s agent with a one-element environment.

Paper node: Definition 20 (§2.4). -/
def AddSubagentCurry (C D : Frame W) : Prop :=
  ∃ (M : Frame D.Agent) (_ : Unique M.Env), C ≃ᵇ D.curry.obj M

/-- Definition 21, the currying definition of multiplicative subagent:
`C ≃ᵇ D°(M)` for a frame `M` over `D`'s agent whose image is all of `D`'s agent.

Paper node: Definition 21 (§2.4). -/
def MultSubagentCurry (C D : Frame W) : Prop :=
  ∃ M : Frame D.Agent, M.image = Set.univ ∧ (C ≃ᵇ D.curry.obj M)

/-! ## Internal machinery

Four supporting constructions, each isolated because more than one of the claims
below needs it: transfer of carrier nonemptiness across `≃ᵇ` (the empty corner of
Claim 43), the `M ≃ ⊥_{Image M}` step the paper takes in one line inside Claim 42,
transport of a curried frame along a homotopy equivalence of its base, and the
reassociation `(E°(M))°(N) ≅ E°(N ∘ M)` (both used by the transitivity halves of
Claim 23). -/

private lemma nonempty_agent_of_biextEquiv {C D : Frame W} (h : C ≃ᵇ D)
    (hC : Nonempty C.Agent) : Nonempty D.Agent := by
  obtain ⟨i⟩ := h
  obtain ⟨a⟩ := hC
  exact ⟨(i.hom.agent (Quotient.mk C.agentSetoid a) : Quotient D.agentSetoid).out⟩

private lemma nonempty_env_of_biextEquiv {C D : Frame W} (h : C ≃ᵇ D)
    (hD : Nonempty D.Env) : Nonempty C.Env := by
  obtain ⟨i⟩ := h
  obtain ⟨e⟩ := hD
  exact ⟨(i.hom.env (Quotient.mk D.envSetoid e) : Quotient C.envSetoid).out⟩

/-- A frame with a one-element environment is biextensionally equivalent to the
`⊥` frame on its image — the paper's "since `|Env(M)| = 1`, we have `M ≃ ⊥_X`"
inside the proof of Claim 42. -/
private lemma biextEquiv_botOf_image {A : Type u} (M : Frame A) [Unique M.Env] :
    M ≃ᵇ botOf M.image := by
  classical
  have hval : ∀ s : (M.image : Set A), ∃ a : M.Agent, M.outcome a default = s.val := by
    intro s
    obtain ⟨a, e, he⟩ := s.property
    exact ⟨a, (congrArg (M.outcome a) (Subsingleton.elim _ e)).trans he⟩
  choose pick hpick using hval
  refine biextEquiv_iff_homotopyEquiv.mpr
    ⟨{ agent := fun a => ⟨M.outcome a default, ⟨a, default, rfl⟩⟩
       env := fun _ => default
       adjoint := fun _ _ => rfl },
     { agent := pick
       env := fun _ => PUnit.unit
       adjoint := fun s e =>
         (hpick s).symm.trans (congrArg (M.outcome (pick s)) (Subsingleton.elim _ e)) },
     ?_, fun s _ => (hpick s).symm⟩
  intro a e
  rw [Subsingleton.elim e (default : M.Env)]
  exact (hpick ⟨M.outcome a default, ⟨a, default, rfl⟩⟩).symm

/-- Transport of a curried frame along a homotopy-equivalence pair of its base:
`D°(Z) ≃ᵇ D'°(σ°(Z))`.  `mapWorlds` keeps the environment carrier, so a `Unique`
environment survives the transport. -/
private lemma biextEquiv_curry_transport {D D' : Frame W} (σ : D ⟶ D') (τ : D' ⟶ D)
    (hστ : Homotopic (σ ≫ τ) (𝟙 D)) (Z : Frame D.Agent) :
    D.curry.obj Z ≃ᵇ D'.curry.obj ((mapWorlds σ.agent).obj Z) :=
  biextEquiv_iff_homotopyEquiv.mpr
    ⟨{ agent := fun a => a
       env := fun p => (p.1, σ.env p.2)
       adjoint := fun a p => σ.adjoint (Z.outcome a p.1) p.2 },
     { agent := fun a => a
       env := fun p => (p.1, τ.env p.2)
       adjoint := fun a p =>
         (τ.adjoint (σ.agent (Z.outcome a p.1)) p.2).trans (hστ (Z.outcome a p.1) p.2).symm },
     fun _ _ => rfl, fun _ _ => rfl⟩

/-- Currying twice is currying once along the composite: `(E°(M))°(N)` differs from
`E°(N ∘ M)` only by reassociating the environment triple. -/
private def curryCurryIso (E : Frame W) (M : Frame E.Agent) (N : Frame M.Agent) :
    (E.curry.obj M).curry.obj N ≅
      E.curry.obj { Agent := N.Agent, Env := N.Env × M.Env,
                    outcome := fun a p => M.outcome (N.outcome a p.1) p.2 } where
  hom :=
    { agent := fun a => a
      env := fun q => (q.1.1, (q.1.2, q.2))
      adjoint := fun _ _ => rfl }
  inv :=
    { agent := fun a => a
      env := fun p => ((p.1, p.2.1), p.2.2)
      adjoint := fun _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- A product of one-element types is a one-element type.  Mathlib has the
`Inhabited` and `Subsingleton` product instances but no `Unique` one. -/
@[reducible] private def uniqueProd {α β : Type u} (ha : Unique α) (hb : Unique β) :
    Unique (α × β) :=
  letI := ha
  letI := hb
  Unique.mk' _

/-- If a frame `N` over `Agent(E)` has an image meeting every row-equivalence class
of `Agent(E)`, it can be patched to a frame with image literally all of `Agent(E)`
without changing `E°(N)` up to biextensional equivalence.  This is what makes
`◁ₓ` transitive: transporting the inner frame along a homotopy equivalence of bases
only preserves the image up to rows. -/
private lemma exists_image_univ_curry {E : Frame W} (N : Frame E.Agent)
    (hN : ∀ c : E.Agent, ∃ (a : N.Agent) (p : N.Env),
      ∀ e : E.Env, E.outcome (N.outcome a p) e = E.outcome c e) :
    ∃ N' : Frame E.Agent, N'.image = Set.univ ∧ (E.curry.obj N ≃ᵇ E.curry.obj N') := by
  classical
  by_cases hE : Nonempty E.Agent
  · choose pa pe hpe using hN
    refine ⟨{ Agent := N.Agent, Env := N.Env × E.Agent,
              outcome := fun a p =>
                if (a, p.1) = (pa p.2, pe p.2) then p.2 else N.outcome a p.1 }, ?_, ?_⟩
    · exact Set.eq_univ_of_forall fun c => ⟨pa c, (pe c, c), if_pos rfl⟩
    · have key : ∀ (a : N.Agent) (p : N.Env × E.Agent) (e : E.Env),
          E.outcome (if (a, p.1) = (pa p.2, pe p.2) then p.2 else N.outcome a p.1) e
            = E.outcome (N.outcome a p.1) e := by
        intro a p e
        by_cases hc : (a, p.1) = (pa p.2, pe p.2)
        · rw [if_pos hc]
          have h1 : a = pa p.2 := congrArg Prod.fst hc
          have h2 : p.1 = pe p.2 := congrArg Prod.snd hc
          rw [h1, h2]
          exact (hpe p.2 e).symm
        · rw [if_neg hc]
      exact biextEquiv_iff_homotopyEquiv.mpr
        ⟨{ agent := fun a => a
           env := fun q => (q.1.1, q.2)
           adjoint := fun a q => (key a q.1 q.2).symm },
         { agent := fun a => a
           env := fun p => ((p.1, hE.some), p.2)
           adjoint := fun a p => key a (p.1, hE.some) p.2 },
         fun _ _ => rfl, fun _ _ => rfl⟩
  · exact ⟨N, Set.eq_univ_of_forall fun c => absurd ⟨c⟩ hE, BiextEquiv.refl _⟩

/-! ## The equivalence of the two pairs of definitions (Claims 41–44, 22) -/

/-- The committing definition of additive subagent implies the currying definition.

Paper node: Claim 41 (App. A). -/
theorem AddSubagent.addSubagentCurry {C D : Frame W} (h : C ◁₊ D) :
    AddSubagentCurry C D := by
  obtain ⟨Y, Z, X, f, hC, hD⟩ := h
  obtain ⟨g0, g1, hg01, hg10⟩ := biextEquiv_iff_homotopyEquiv.mp hD
  refine ⟨{ Agent := X, Env := PUnit, outcome := fun x _ => g1.agent x.val },
    ⟨⟨PUnit.unit⟩, fun _ => rfl⟩, ?_⟩
  refine hC.trans (biextEquiv_iff_homotopyEquiv.mpr
    ⟨{ agent := fun x => x
       env := fun p => g1.env p.2
       adjoint := fun x p => g1.adjoint x.val p.2 },
     { agent := fun x => x
       env := fun z => (PUnit.unit, g0.env z)
       adjoint := fun x z =>
         (g1.adjoint x.val (g0.env z)).symm.trans (hg10.symm x.val z) },
     fun _ _ => rfl, fun _ _ => rfl⟩)

/-- The currying definition of additive subagent implies the committing definition.

Paper node: Claim 42 (App. A). -/
theorem AddSubagentCurry.addSubagent {C D : Frame W} (h : AddSubagentCurry C D) :
    C ◁₊ D := by
  obtain ⟨M, hu, hM⟩ := h
  haveI := hu
  refine ⟨D.Agent, D.Env, M.image, D.outcome, ?_, BiextEquiv.refl D⟩
  refine hM.trans ((BiextEquiv.curryObj D (biextEquiv_botOf_image M)).trans
    (biextEquiv_of_nonempty_iso ⟨?_⟩))
  exact
    { hom :=
        { agent := fun x => x
          env := fun z => (PUnit.unit, z)
          adjoint := fun _ _ => rfl }
      inv :=
        { agent := fun x => x
          env := fun p => p.2
          adjoint := fun _ _ => rfl }
      hom_inv_id := rfl
      inv_hom_id := rfl }

/-- The externalizing definition of multiplicative subagent implies the currying
definition.

Paper node: Claim 43 (App. A). -/
theorem MultSubagent.multSubagentCurry {C D : Frame W} (h : C ◁ₓ D) :
    MultSubagentCurry C D := by
  classical
  obtain ⟨X, Y, Z, f, hC, hD⟩ := h
  obtain ⟨g0, g1, hg01, hg10⟩ := biextEquiv_iff_homotopyEquiv.mp hD
  by_cases hB : Nonempty D.Agent
  · -- The paper's construction, verbatim.
    refine ⟨{ Agent := X, Env := Y × D.Agent,
              outcome := fun x p =>
                if g0.agent p.2 = (x, p.1) then p.2 else g1.agent (x, p.1) }, ?_, ?_⟩
    · exact Set.eq_univ_of_forall fun b =>
        ⟨(g0.agent b).1, ((g0.agent b).2, b), if_pos rfl⟩
    · have key : ∀ (x : X) (p : Y × D.Agent) (e : D.Env),
          D.outcome (if g0.agent p.2 = (x, p.1) then p.2 else g1.agent (x, p.1)) e
            = D.outcome (g1.agent (x, p.1)) e := by
        intro x p e
        by_cases hc : g0.agent p.2 = (x, p.1)
        · rw [if_pos hc, ← hc]
          exact hg01 p.2 e
        · rw [if_neg hc]
      exact hC.trans (biextEquiv_iff_homotopyEquiv.mpr
        ⟨{ agent := fun x => x
           env := fun q => (q.1.1, g1.env q.2)
           adjoint := fun x q =>
             (g1.adjoint (x, q.1.1) q.2).trans (key x q.1 q.2).symm },
         { agent := fun x => x
           env := fun p => ((p.1, hB.some), g0.env p.2)
           adjoint := fun x p =>
             ((key x (p.1, hB.some) (g0.env p.2)).trans
               (g1.adjoint (x, p.1) (g0.env p.2)).symm).trans (hg10.symm (x, p.1) p.2) },
         fun _ _ => rfl, fun _ _ => rfl⟩)
  · -- The corner the paper's "some `b ∈ B`" skips: `Agent(D)` empty forces `X × Y`
    -- empty, so every obligation below is vacuous.
    have hXY : IsEmpty (X × Y) := by
      constructor
      intro p
      exact hB (nonempty_agent_of_biextEquiv hD.symm ⟨p⟩)
    have hDA : IsEmpty D.Agent := not_nonempty_iff.mp hB
    have hZD : Nonempty Z → Nonempty D.Env := fun hz => nonempty_env_of_biextEquiv hD hz
    refine ⟨{ Agent := X, Env := Y × Z,
              outcome := fun x p => (hXY.false (x, p.1)).elim }, ?_, ?_⟩
    · exact Set.eq_univ_of_forall fun b => (hDA.false b).elim
    · exact hC.trans (biextEquiv_iff_homotopyEquiv.mpr
        ⟨{ agent := fun x => x
           env := fun q => q.1
           adjoint := fun x q => (hXY.false (x, q.1.1)).elim },
         { agent := fun x => x
           env := fun p => (p, (hZD ⟨p.2⟩).some)
           adjoint := fun x p => (hXY.false (x, p.1)).elim },
         fun x p => (hXY.false (x, p.1)).elim,
         fun x q => (hXY.false (x, q.1.1)).elim⟩)

/-- The currying definition of multiplicative subagent implies the externalizing
definition.

Paper node: Claim 44 (App. A). -/
theorem MultSubagentCurry.multSubagent {C D : Frame W} (h : MultSubagentCurry C D) :
    C ◁ₓ D := by
  classical
  obtain ⟨M, himg, hM⟩ := h
  have hsurj : ∀ b : D.Agent, ∃ p : M.Agent × M.Env, M.outcome p.1 p.2 = b := by
    intro b
    have hb : b ∈ M.image := by rw [himg]; trivial
    obtain ⟨a, e, he⟩ := hb
    exact ⟨(a, e), he⟩
  choose pre hpre using hsurj
  refine ⟨M.Agent, M.Env, D.Env, fun x y z => D.outcome (M.outcome x y) z, hM, ?_⟩
  exact biextEquiv_iff_homotopyEquiv.mpr
    ⟨{ agent := pre
       env := fun z => z
       adjoint := fun b z => congrArg (fun a => D.outcome a z) (hpre b).symm },
     { agent := fun p => M.outcome p.1 p.2
       env := fun z => z
       adjoint := fun _ _ => rfl },
     fun b z => congrArg (fun a => D.outcome a z) (hpre b).symm,
     fun p z => congrArg (fun a => D.outcome a z) (hpre (M.outcome p.1 p.2)).symm⟩

/-- The currying definition of additive subagent is equivalent to the committing
definition — the additive half of Claim 22.

Paper node: Claim 22 (§2.4). -/
theorem addSubagent_iff_addSubagentCurry {C D : Frame W} :
    C ◁₊ D ↔ AddSubagentCurry C D :=
  ⟨AddSubagent.addSubagentCurry, AddSubagentCurry.addSubagent⟩

/-- The currying definition of multiplicative subagent is equivalent to the
externalizing definition — the multiplicative half of Claim 22.

Paper node: Claim 22 (§2.4). -/
theorem multSubagent_iff_multSubagentCurry {C D : Frame W} :
    C ◁ₓ D ↔ MultSubagentCurry C D :=
  ⟨MultSubagent.multSubagentCurry, MultSubagentCurry.multSubagent⟩

/-! ## Basic properties (Claim 23) -/

/-- Additive subagents are subagents — Claim 23(1), additive half.

Paper node: Claim 23 (§2.4). -/
theorem AddSubagent.subagent {C D : Frame W} (h : C ◁₊ D) : C ◁ D := by
  obtain ⟨M, _, hM⟩ := h.addSubagentCurry
  exact SubagentCurry.subagent ⟨M, hM⟩

/-- Multiplicative subagents are subagents — Claim 23(1), multiplicative half.

Paper node: Claim 23 (§2.4). -/
theorem MultSubagent.subagent {C D : Frame W} (h : C ◁ₓ D) : C ◁ D := by
  obtain ⟨M, _, hM⟩ := h.multSubagentCurry
  exact SubagentCurry.subagent ⟨M, hM⟩

/-- `◁₊` respects biextensional equivalence on both sides — Claim 23(2).

Paper node: Claim 23 (§2.4). -/
theorem AddSubagent.congr {C C' D D' : Frame W} (h : C ◁₊ D) (hC : C ≃ᵇ C')
    (hD : D ≃ᵇ D') : C' ◁₊ D' := by
  obtain ⟨Y, Z, X, f, h₀, h₁⟩ := h
  exact ⟨Y, Z, X, f, hC.symm.trans h₀, hD.symm.trans h₁⟩

/-- `◁ₓ` respects biextensional equivalence on both sides — Claim 23(2).

Paper node: Claim 23 (§2.4). -/
theorem MultSubagent.congr {C C' D D' : Frame W} (h : C ◁ₓ D) (hC : C ≃ᵇ C')
    (hD : D ≃ᵇ D') : C' ◁ₓ D' := by
  obtain ⟨X, Y, Z, f, h₀, h₁⟩ := h
  exact ⟨X, Y, Z, f, hC.symm.trans h₀, hD.symm.trans h₁⟩

/-- `◁₊` is reflexive — Claim 23(3).

Paper node: Claim 23 (§2.4). -/
theorem AddSubagent.refl (C : Frame W) : C ◁₊ C := by
  refine ⟨C.Agent, C.Env, Set.univ, C.outcome, biextEquiv_of_nonempty_iso ⟨?_⟩,
    BiextEquiv.refl C⟩
  exact
    { hom :=
        { agent := fun a => ⟨a, Set.mem_univ a⟩
          env := fun e => e
          adjoint := fun _ _ => rfl }
      inv :=
        { agent := fun s => s.val
          env := fun e => e
          adjoint := fun _ _ => rfl }
      hom_inv_id := rfl
      inv_hom_id := rfl }

/-- `◁ₓ` is reflexive — Claim 23(3).

Paper node: Claim 23 (§2.4). -/
theorem MultSubagent.refl (C : Frame W) : C ◁ₓ C := by
  refine ⟨C.Agent, PUnit, C.Env, fun a _ e => C.outcome a e,
    biextEquiv_of_nonempty_iso ⟨?_⟩, biextEquiv_of_nonempty_iso ⟨?_⟩⟩
  · exact
      { hom :=
          { agent := fun a => a
            env := fun p => p.2
            adjoint := fun _ _ => rfl }
        inv :=
          { agent := fun a => a
            env := fun e => (PUnit.unit, e)
            adjoint := fun _ _ => rfl }
        hom_inv_id := rfl
        inv_hom_id := rfl }
  · exact
      { hom :=
          { agent := fun a => (a, PUnit.unit)
            env := fun e => e
            adjoint := fun _ _ => rfl }
        inv :=
          { agent := fun p => p.1
            env := fun e => e
            adjoint := fun _ _ => rfl }
        hom_inv_id := rfl
        inv_hom_id := rfl }

/-- `◁₊` is transitive — Claim 23(3).

Paper node: Claim 23 (§2.4). -/
theorem AddSubagent.trans {C D E : Frame W} (h₀ : C ◁₊ D) (h₁ : D ◁₊ E) : C ◁₊ E := by
  obtain ⟨M₁, u₁, hC⟩ := h₀.addSubagentCurry
  obtain ⟨M₂, u₂, hD⟩ := h₁.addSubagentCurry
  obtain ⟨σ, τ, hστ, hτσ⟩ := biextEquiv_iff_homotopyEquiv.mp hD
  refine addSubagent_iff_addSubagentCurry.mpr
    ⟨{ Agent := M₁.Agent, Env := M₁.Env × M₂.Env,
       outcome := fun a p => M₂.outcome (σ.agent (M₁.outcome a p.1)) p.2 },
     uniqueProd u₁ u₂, ?_⟩
  exact (hC.trans (biextEquiv_curry_transport σ τ hστ M₁)).trans
    (biextEquiv_of_nonempty_iso ⟨curryCurryIso E M₂ ((mapWorlds σ.agent).obj M₁)⟩)

/-- `◁ₓ` is transitive — Claim 23(3).

Paper node: Claim 23 (§2.4). -/
theorem MultSubagent.trans {C D E : Frame W} (h₀ : C ◁ₓ D) (h₁ : D ◁ₓ E) : C ◁ₓ E := by
  classical
  obtain ⟨M₁, hi₁, hC⟩ := h₀.multSubagentCurry
  obtain ⟨M₂, hi₂, hD⟩ := h₁.multSubagentCurry
  obtain ⟨σ, τ, hστ, hτσ⟩ := biextEquiv_iff_homotopyEquiv.mp hD
  have hCM : C ≃ᵇ E.curry.obj
      { Agent := M₁.Agent, Env := M₁.Env × M₂.Env,
        outcome := fun a p => M₂.outcome (σ.agent (M₁.outcome a p.1)) p.2 } :=
    (hC.trans (biextEquiv_curry_transport σ τ hστ M₁)).trans
      (biextEquiv_of_nonempty_iso ⟨curryCurryIso E M₂ ((mapWorlds σ.agent).obj M₁)⟩)
  -- The transported inner frame need only meet every row-class of `Agent(E)`;
  -- `exists_image_univ_curry` patches it up to a literally full image.
  have hhit : ∀ c : E.Agent, ∃ (a : M₁.Agent) (p : M₁.Env × M₂.Env),
      ∀ e : E.Env,
        E.outcome (M₂.outcome (σ.agent (M₁.outcome a p.1)) p.2) e = E.outcome c e := by
    intro c
    have hc : c ∈ M₂.image := by rw [hi₂]; trivial
    obtain ⟨a₂, f₂, hf₂⟩ := hc
    have hd : τ.agent a₂ ∈ M₁.image := by rw [hi₁]; trivial
    obtain ⟨a₁, f₁, hf₁⟩ := hd
    refine ⟨a₁, (f₁, f₂), fun e => ?_⟩
    rw [hf₁, ← hf₂]
    exact (hτσ a₂ (f₂, e)).symm
  obtain ⟨M₃, himg, hEq⟩ := exists_image_univ_curry
    ({ Agent := M₁.Agent, Env := M₁.Env × M₂.Env,
       outcome := fun a p => M₂.outcome (σ.agent (M₁.outcome a p.1)) p.2 } : Frame E.Agent)
    hhit
  exact multSubagent_iff_multSubagentCurry.mpr ⟨M₃, himg, hCM.trans hEq⟩

/-! ## The Decomposition Theorem (Theorem 24) -/

/-- The Decomposition Theorem: `C₀ ◁ C₁` iff the subagency factors as a
multiplicative subagency followed by an additive one.

Paper node: Theorem 24 (§2.4). -/
theorem subagent_iff_exists_multSubagent_addSubagent {C₀ C₁ : Frame W} :
    C₀ ◁ C₁ ↔ ∃ C₂, (C₀ ◁ₓ C₂) ∧ (C₂ ◁₊ C₁) := by
  constructor
  · intro h
    obtain ⟨D, hD⟩ := subagent_iff_subagentCurry.mp h
    refine ⟨{ Agent := D.image, Env := C₁.Env,
              outcome := fun a e => C₁.outcome a.val e }, ?_, ?_⟩
    · refine multSubagent_iff_multSubagentCurry.mpr
        ⟨{ Agent := D.Agent, Env := D.Env,
           outcome := fun a e => ⟨D.outcome a e, ⟨a, e, rfl⟩⟩ }, ?_, hD⟩
      refine Set.eq_univ_of_forall fun s => ?_
      obtain ⟨a, e, he⟩ := s.property
      exact ⟨a, e, Subtype.ext he⟩
    · exact ⟨C₁.Agent, C₁.Env, D.image, C₁.outcome, BiextEquiv.refl _, BiextEquiv.refl _⟩
  · rintro ⟨C₂, hx, ha⟩
    exact hx.subagent.trans ha.subagent

section RegressionExamples

/- Client-side exercises of the endpoints above (endpoint-usability rule). -/

example {C D : Frame W} (h : C ◁₊ D) : C ◁ D := h.subagent

example {C D : Frame W} (h : C ◁ₓ D) (h' : D ◁ₓ C) : C ◁ₓ C := h.trans h'

example {C₀ C₁ : Frame W} (h : C₀ ◁ C₁) : ∃ C₂, (C₀ ◁ C₂) ∧ (C₂ ◁ C₁) := by
  obtain ⟨C₂, hx, ha⟩ := subagent_iff_exists_multSubagent_addSubagent.mp h
  exact ⟨C₂, hx.subagent, ha.subagent⟩

example {C D : Frame W} (h : C ◁₊ D) : ∃ (M : Frame D.Agent) (_ : Unique M.Env),
    C ≃ᵇ D.curry.obj M :=
  addSubagent_iff_addSubagentCurry.mp h

example (C : Frame W) : (C ◁₊ C) ∧ (C ◁ₓ C) := ⟨AddSubagent.refl C, MultSubagent.refl C⟩

end RegressionExamples

end Frame

end CartesianFrames
