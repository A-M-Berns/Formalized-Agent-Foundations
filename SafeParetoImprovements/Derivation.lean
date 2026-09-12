import SafeParetoImprovements.Assumptions
import SafeParetoImprovements.Reduction

/-!
# Derivations from Assumptions 1 and 2, and the SPI decision problem (§4.6, Definition 5)

Definition 5 does not ask whether `Γs` *is* an SPI on `Γ` under Assumptions 1 and 2; it
asks whether that can be **shown** using only the allowed moves: a single application of
Assumption 1, a single application of Assumption 1 in reverse (via Lemma 2.2, symmetry),
or a single application of Assumption 2, in a chain of subset games of `Γ` whose
composite correspondence is Pareto-improving.  That is a syntactic notion, and it is what
Theorem 9's complexity claims and Appendix D's structure lemmas (19–22) are about
(`dd:derivation`).

* `Step Γ₀ Γ Γ' Φ` — one allowed move between two subset games of the root `Γ₀`, with the
  correspondence it records.  The isomorphism move records the *chosen* isomorphism.
* `Deriv Γ₀ Γ Γ' Φ` — a chain of moves with composite `Φ`.

What a derivation establishes is deliberately **not** "`Γ ∼_Φ Γ'` under the assumptions":
Assumption 2 supplies *some* isomorphism, not the recorded one, so that statement is
false.  What is true, and what the paper uses:

* **Structure (Lemma 21, Lemma 22):** every derivation from `Γ` to `Γ'` relates each
  outcome of `reduce Γ` to its image under an isomorphism `reduce Γ ≅ reduce Γ'`
  (`Deriv.exists_iso`), and conversely every such isomorphism is realized by a derivation
  in normal form — eliminations, one isomorphism, reverse eliminations
  (`Deriv.normal`).  The composite of the normal form is exactly the graph of the
  isomorphism on `reduce Γ` (`normalRel`).
* **Certificate form** (the "conciser way to state" the consequence of Lemma 21, corrected
  per erratum D9): a Pareto-improving derivation from `Γ₀` to `Γs` exists iff there is a
  Pareto-improving isomorphism `reduce Γ₀ ≅ reduce Γs` (`exists_paretoImproving_deriv_iff`).
  This is the object Theorem 9's membership algorithm and Proposition 10's search enumerate.
* **Soundness** (`isSPI_of_deriv`): a Pareto-improving derivation from `Γ₀` to `Γs`
  makes `Γs` an SPI on `Γ₀` under every play family satisfying Assumptions 1 and 2 — via
  the structure theorem, Assumption 1 along the eliminations, Assumption 2 and Lemma 4 at
  the isomorphism, and Theorem 3.

Completeness (every SPI valid under the assumptions has a derivation) is neither claimed
by the paper nor true, and is not stated.
-/

namespace SafeParetoImprovements

open Filter
open scoped SetRel

universe u v w

variable {N : Type u} {𝒜 : N → Type v}

/-- The partial identity on the outcomes of `G`: `a ~ b` iff `a ∈ A_G` and `b = a`.  The
composite of Assumption 1's correspondences along an elimination chain ending at `G`, in
either direction. -/
def Game.partialId (G : Game N 𝒜) : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i) :=
  {p | p.1 ∈ G.profiles ∧ p.2 = p.1}

@[simp] lemma Game.mem_partialId (G : Game N 𝒜) (a b : ∀ i, 𝒜 i) :
    a ~[G.partialId] b ↔ a ∈ G.profiles ∧ b = a := Iff.rfl

namespace GameIso

variable {G₁ G₂ H₁ H₂ : Game N 𝒜}

/-- Transport an isomorphism along equalities of its endpoints. -/
def cast (e : G₁ = G₂) (e' : H₁ = H₂) (φ : GameIso G₁ H₁) : GameIso G₂ H₂ := e ▸ e' ▸ φ

@[simp] lemma cast_map (e : G₁ = G₂) (e' : H₁ = H₂) (φ : GameIso G₁ H₁) :
    (φ.cast e e').map = φ.map := by
  subst e; subst e'; rfl

end GameIso

section derivation

variable [DecidableEq N] [∀ i, DecidableEq (𝒜 i)]

namespace Game

/-- One move of Definition 5, between subset games of the root `Γ₀`: Assumption 1
(`elim`), Assumption 1 in reverse via Lemma 2.2 (`unelim`), or Assumption 2 between fully
reduced games (`iso`, recording the chosen isomorphism).

Paper node: `Definition 5` -/
inductive Step (Γ₀ : Game N 𝒜) : Game N 𝒜 → Game N 𝒜 → SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i) → Prop
  | elim {Γ : Game N 𝒜} {i : N} {ã : 𝒜 i} (hsub : Γ.IsSubsetGameOf Γ₀)
      (h : Γ.IsStrictlyDominated i ã) :
      Step Γ₀ Γ (Γ.erase i ã h.erase_nonempty) (Γ.elimRel i ã)
  | unelim {Γ : Game N 𝒜} {i : N} {ã : 𝒜 i} (hsub : Γ.IsSubsetGameOf Γ₀)
      (h : Γ.IsStrictlyDominated i ã) :
      Step Γ₀ (Γ.erase i ã h.erase_nonempty) Γ (Γ.elimRel i ã).inv
  | iso {Γ Γ' : Game N 𝒜} (hsub : Γ.IsSubsetGameOf Γ₀) (hsub' : Γ'.IsSubsetGameOf Γ₀)
      (hΓ : Γ.Reduced) (hΓ' : Γ'.Reduced) (φ : GameIso Γ Γ') : Step Γ₀ Γ Γ' φ.rel

/-- A chain of moves of Definition 5 from `Γ` to `Γ'` inside the root `Γ₀`, with its
composite correspondence (the paper's `Φₖ ∘ ⋯ ∘ Φ₁`, in Mathlib's diagrammatic order).
The empty chain records the paper's typed identity `id_A`, the partial identity on the
game's outcomes.

Paper node: `Definition 5` -/
inductive Deriv (Γ₀ : Game N 𝒜) : Game N 𝒜 → Game N 𝒜 → SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i) → Prop
  | refl {Γ : Game N 𝒜} (hsub : Γ.IsSubsetGameOf Γ₀) : Deriv Γ₀ Γ Γ Γ.partialId
  | step {Γ Γ' Γ'' : Game N 𝒜} {Φ Ψ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)}
      (s : Step Γ₀ Γ Γ' Φ) (d : Deriv Γ₀ Γ' Γ'' Ψ) : Deriv Γ₀ Γ Γ'' (Φ ○ Ψ)

namespace Step

variable {Γ₀ Γ Γ' : Game N 𝒜} {Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)}

lemma isSubsetGameOf_left (s : Step Γ₀ Γ Γ' Φ) : Γ.IsSubsetGameOf Γ₀ := by
  cases s with
  | elim hsub _ => exact hsub
  | unelim hsub h => exact (Game.erase_isSubsetGameOf _ _ _ _).trans hsub
  | iso hsub _ _ _ _ => exact hsub

lemma isSubsetGameOf_right (s : Step Γ₀ Γ Γ' Φ) : Γ'.IsSubsetGameOf Γ₀ := by
  cases s with
  | elim hsub h => exact (Game.erase_isSubsetGameOf _ _ _ _).trans hsub
  | unelim hsub _ => exact hsub
  | iso _ hsub' _ _ _ => exact hsub'

/-- A move relates only outcomes of its source to outcomes of its target. -/
lemma mem_of_rel (s : Step Γ₀ Γ Γ' Φ) {a b : ∀ i, 𝒜 i} (h : a ~[Φ] b) :
    a ∈ Γ.profiles ∧ b ∈ Γ'.profiles := by
  cases s with
  | @elim Γ i ã hsub hd =>
    obtain ⟨ha, hne, hb⟩ := (Game.mem_elimRel _ _ _ _ _).1 h
    subst hb
    refine ⟨ha, fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; rw [Game.erase_S_self]; exact Finset.mem_erase.2 ⟨hne, ha _⟩
    · rw [Game.erase_S_of_ne _ _ _ _ hj]; exact ha j
  | @unelim Γ i ã hsub hd =>
    obtain ⟨hb, hne, ha⟩ := (Game.mem_elimRel _ _ _ _ _).1 (SetRel.mem_inv.1 h)
    subst ha
    refine ⟨fun j => ?_, hb⟩
    by_cases hj : j = i
    · subst hj; rw [Game.erase_S_self]; exact Finset.mem_erase.2 ⟨hne, hb _⟩
    · rw [Game.erase_S_of_ne _ _ _ _ hj]; exact hb j
  | iso _ _ _ _ φ =>
    obtain ⟨ha, hb⟩ := (φ.mem_rel _ _).1 h
    subst hb
    exact ⟨ha, φ.map_mem ha⟩

end Step

namespace Deriv

variable {Γ₀ Γ Γ' Γ'' : Game N 𝒜} {Φ Ψ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)}

lemma isSubsetGameOf_left (d : Deriv Γ₀ Γ Γ' Φ) : Γ.IsSubsetGameOf Γ₀ := by
  cases d with
  | refl hsub => exact hsub
  | step s _ => exact s.isSubsetGameOf_left

lemma isSubsetGameOf_right (d : Deriv Γ₀ Γ Γ' Φ) : Γ'.IsSubsetGameOf Γ₀ := by
  induction d with
  | refl hsub => exact hsub
  | step _ _ ih => exact ih

/-- A derivation relates only outcomes of its source to outcomes of its target. -/
lemma mem_of_rel (d : Deriv Γ₀ Γ Γ' Φ) {a b : ∀ i, 𝒜 i} (h : a ~[Φ] b) :
    a ∈ Γ.profiles ∧ b ∈ Γ'.profiles := by
  induction d generalizing a b with
  | refl _ =>
    obtain ⟨ha, hb⟩ := (Game.mem_partialId _ _ _).1 h
    subst hb
    exact ⟨ha, ha⟩
  | step s _ ih =>
    obtain ⟨c, hac, hcb⟩ := h
    exact ⟨(s.mem_of_rel hac).1, (ih hcb).2⟩

lemma comp_partialId (d : Deriv Γ₀ Γ Γ' Φ) : Φ ○ Γ'.partialId = Φ := by
  ext ⟨a, b⟩
  simp only [SetRel.mem_comp, Game.mem_partialId]
  constructor
  · rintro ⟨c, hac, -, rfl⟩; exact hac
  · intro h; exact ⟨b, h, (d.mem_of_rel h).2, rfl⟩

lemma partialId_comp (d : Deriv Γ₀ Γ Γ' Φ) : Γ.partialId ○ Φ = Φ := by
  ext ⟨a, b⟩
  simp only [SetRel.mem_comp, Game.mem_partialId]
  constructor
  · rintro ⟨c, ⟨-, rfl⟩, h⟩; exact h
  · intro h; exact ⟨a, ⟨(d.mem_of_rel h).1, rfl⟩, h⟩

/-- Derivations concatenate. -/
lemma trans (d : Deriv Γ₀ Γ Γ' Φ) (d' : Deriv Γ₀ Γ' Γ'' Ψ) : Deriv Γ₀ Γ Γ'' (Φ ○ Ψ) := by
  induction d with
  | refl _ => rw [d'.partialId_comp]; exact d'
  | step s _ ih => rw [SetRel.comp_assoc]; exact step s (ih d')

lemma _root_.SafeParetoImprovements.Game.Step.comp_partialId {Γ Γ' : Game N 𝒜}
    (s : Step Γ₀ Γ Γ' Φ) : Φ ○ Γ'.partialId = Φ := by
  ext ⟨a, b⟩
  simp only [SetRel.mem_comp, Game.mem_partialId]
  constructor
  · rintro ⟨c, hac, -, rfl⟩; exact hac
  · intro h; exact ⟨b, h, (s.mem_of_rel h).2, rfl⟩

lemma single {Γ Γ' : Game N 𝒜} (s : Step Γ₀ Γ Γ' Φ) : Deriv Γ₀ Γ Γ' Φ :=
  s.comp_partialId ▸ step s (refl s.isSubsetGameOf_right)

/-! ### Elimination chains as derivations -/

lemma partialId_comp_elimRel (G : Game N 𝒜) {i : N} {ã : 𝒜 i} (h : G.IsStrictlyDominated i ã) :
    G.partialId ○ G.elimRel i ã = (G.erase i ã h.erase_nonempty).partialId := by
  ext ⟨a, b⟩
  simp only [SetRel.mem_comp, Game.mem_partialId, Game.mem_elimRel]
  constructor
  · rintro ⟨c, ⟨ha, rfl⟩, -, hne, rfl⟩
    refine ⟨fun j => ?_, rfl⟩
    by_cases hj : j = i
    · subst hj; rw [Game.erase_S_self]; exact Finset.mem_erase.2 ⟨hne, ha j⟩
    · rw [Game.erase_S_of_ne _ _ _ _ hj]; exact ha j
  · rintro ⟨ha, hba⟩
    rw [hba]
    have hsub := G.erase_isSubsetGameOf i ã h.erase_nonempty
    refine ⟨a, ⟨hsub.profiles_subset ha, rfl⟩, hsub.profiles_subset ha, ?_, rfl⟩
    have := ha i
    rw [Game.erase_S_self] at this
    exact (Finset.mem_erase.1 this).1

lemma elimRel_inv_comp_partialId (G : Game N 𝒜) {i : N} {ã : 𝒜 i}
    (h : G.IsStrictlyDominated i ã) :
    (G.elimRel i ã).inv ○ G.partialId = (G.erase i ã h.erase_nonempty).partialId := by
  ext ⟨a, b⟩
  simp only [SetRel.mem_comp, SetRel.mem_inv, Game.mem_partialId, Game.mem_elimRel]
  constructor
  · rintro ⟨c, ⟨hc, hne, rfl⟩, -, rfl⟩
    refine ⟨fun j => ?_, rfl⟩
    by_cases hj : j = i
    · subst hj; rw [Game.erase_S_self]; exact Finset.mem_erase.2 ⟨hne, hc j⟩
    · rw [Game.erase_S_of_ne _ _ _ _ hj]; exact hc j
  · rintro ⟨ha, hba⟩
    rw [hba]
    have hsub := G.erase_isSubsetGameOf i ã h.erase_nonempty
    refine ⟨a, ⟨hsub.profiles_subset ha, ?_, rfl⟩, hsub.profiles_subset ha, rfl⟩
    have := ha i
    rw [Game.erase_S_self] at this
    exact (Finset.mem_erase.1 this).1

/-- An elimination chain `Γ →* G` inside `Γ₀` is a derivation whose composite is the
partial identity on `G`'s outcomes. -/
lemma ofElimStar (hsub : Γ.IsSubsetGameOf Γ₀) {G : Game N 𝒜} (h : Γ.ElimStar G) :
    Deriv Γ₀ Γ G G.partialId := by
  induction h with
  | refl => exact refl hsub
  | tail _ hstep ih =>
    obtain ⟨i, ã, hã, rfl⟩ := hstep
    rw [← partialId_comp_elimRel _ hã]
    exact ih.trans (single (Step.elim ih.isSubsetGameOf_right hã))

/-- The reverse of an elimination chain `Γ →* G` is a derivation from `G` back to `Γ`, by
Assumption 1 in reverse, with composite the partial identity on `G`'s outcomes. -/
lemma ofElimStar_rev (hsub : Γ.IsSubsetGameOf Γ₀) {G : Game N 𝒜} (h : Γ.ElimStar G) :
    Deriv Γ₀ G Γ G.partialId := by
  induction h with
  | refl => exact refl hsub
  | tail _ hstep ih =>
    obtain ⟨i, ã, hã, rfl⟩ := hstep
    rw [← elimRel_inv_comp_partialId _ hã]
    exact (single (Step.unelim ih.isSubsetGameOf_left hã)).trans ih


/-! ### The structure of derivations (Lemmas 21 and 22) -/

section structure_theorem

variable [Fintype N]

/-- **Lemma 21 / Lemma 22, structural form**: every derivation from `Γ` to `Γ'` relates
each outcome of `reduce Γ` to its image under some isomorphism `reduce Γ ≅ reduce Γ'`.
Eliminations and reverse eliminations act as the identity on the outcomes of the full
reduction (they never remove one, by path independence), and isomorphism moves compose.

Paper node: `Lemma 21` -/
theorem exists_iso (d : Deriv Γ₀ Γ Γ' Φ) :
    ∃ ψ : GameIso Γ.reduce Γ'.reduce, ∀ a ∈ Γ.reduce.profiles, a ~[Φ] ψ.map a := by
  induction d with
  | @refl Γ hsub =>
    exact ⟨GameIso.refl _, fun a ha => ⟨Γ.reduce_isSubsetGameOf.profiles_subset ha, rfl⟩⟩
  | @step Γ Γ' Γ'' Φ Ψ s _ ih =>
    obtain ⟨ψ', hψ'⟩ := ih
    cases s with
    | @elim Γ i ã hsub hd =>
      have e := Γ.reduce_erase hd
      refine ⟨ψ'.cast e rfl, fun a ha => ⟨a, ?_, ?_⟩⟩
      · refine ⟨Γ.reduce_isSubsetGameOf.profiles_subset ha, ?_, rfl⟩
        intro hai
        dsimp only at hai
        have hmem : a i ∈ (Γ.erase i ã hd.erase_nonempty).S i :=
          (e ▸ (Γ.erase i ã hd.erase_nonempty).reduce_isSubsetGameOf) i (ha i)
        rw [Game.erase_S_self, hai] at hmem
        exact (Finset.mem_erase.1 hmem).1 rfl
      · rw [GameIso.cast_map]
        exact hψ' a (by rw [e]; exact ha)
    | @unelim _ i ã hsub hd =>
      have e := Game.reduce_erase Γ' hd
      refine ⟨ψ'.cast e.symm rfl, fun a ha => ⟨a, ?_, ?_⟩⟩
      · refine SetRel.mem_inv.2 ⟨Γ'.reduce_isSubsetGameOf.profiles_subset (e ▸ ha), ?_, rfl⟩
        intro hai
        dsimp only at hai
        have hmem : a i ∈ (Γ'.erase i ã hd.erase_nonempty).S i :=
          (Γ'.erase i ã hd.erase_nonempty).reduce_isSubsetGameOf i (ha i)
        rw [Game.erase_S_self, hai] at hmem
        exact (Finset.mem_erase.1 hmem).1 rfl
      · rw [GameIso.cast_map]
        exact hψ' a (e ▸ ha)
    | @iso Γ Γ' hsub hsub' hΓ hΓ' φ =>
      refine ⟨(φ.cast (Γ.reduce_of_reduced hΓ).symm (Γ'.reduce_of_reduced hΓ').symm).trans ψ',
        fun a ha => ?_⟩
      have ha' : a ∈ Γ.profiles := by rw [Γ.reduce_of_reduced hΓ] at ha; exact ha
      refine ⟨φ.map a, ⟨ha', rfl⟩, ?_⟩
      rw [GameIso.trans_map, GameIso.cast_map]
      exact hψ' _ (by rw [Γ'.reduce_of_reduced hΓ']; exact φ.map_mem ha')

/-- The composite of a normal-form derivation: the graph of `ψ` on the outcomes of
`reduce Γ`. -/
def normalRel (ψ : GameIso Γ.reduce Γ'.reduce) : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i) :=
  {p | p.1 ∈ Γ.reduce.profiles ∧ p.2 = ψ.map p.1}

@[simp] lemma mem_normalRel (ψ : GameIso Γ.reduce Γ'.reduce) (a b : ∀ i, 𝒜 i) :
    a ~[normalRel ψ] b ↔ a ∈ Γ.reduce.profiles ∧ b = ψ.map a := Iff.rfl

/-- **Lemma 21, normal form**: every isomorphism `reduce Γ ≅ reduce Γ'` is realized by a
derivation of the shape *eliminations, one isomorphism move, reverse eliminations*, whose
composite is exactly `normalRel ψ`.  With `exists_iso`, this is the paper's reorganization
of an arbitrary chain into that shape.

Paper node: `Lemma 21` -/
theorem normal (hsub : Γ.IsSubsetGameOf Γ₀) (hsub' : Γ'.IsSubsetGameOf Γ₀)
    (ψ : GameIso Γ.reduce Γ'.reduce) : Deriv Γ₀ Γ Γ' (normalRel ψ) := by
  have d₁ : Deriv Γ₀ Γ Γ.reduce Γ.reduce.partialId := ofElimStar hsub (Γ.elimStar_reduce)
  have d₂ : Deriv Γ₀ Γ.reduce Γ'.reduce ψ.rel :=
    single (Step.iso (Γ.reduce_isSubsetGameOf.trans hsub) (Γ'.reduce_isSubsetGameOf.trans hsub')
      (Γ.reduce_reduced) (Γ'.reduce_reduced) ψ)
  have d₃ : Deriv Γ₀ Γ'.reduce Γ' Γ'.reduce.partialId := ofElimStar_rev hsub' (Γ'.elimStar_reduce)
  have d := d₁.trans (d₂.trans d₃)
  have e : Γ.reduce.partialId ○ (ψ.rel ○ Γ'.reduce.partialId) = normalRel ψ := by
    ext ⟨a, b⟩
    simp only [SetRel.mem_comp, Game.mem_partialId, GameIso.mem_rel, mem_normalRel]
    constructor
    · rintro ⟨c, ⟨ha, rfl⟩, e, ⟨-, rfl⟩, -, rfl⟩; exact ⟨ha, rfl⟩
    · rintro ⟨ha, rfl⟩; exact ⟨a, ⟨ha, rfl⟩, ψ.map a, ⟨ha, rfl⟩, ψ.map_mem ha, rfl⟩
  rw [← e]; exact d

end structure_theorem

end Deriv

/-! ### Definition 5 and its certificate form -/

section decision

variable [Fintype N]

/-- A correspondence is **Pareto-improving for the base game** `Γ₀` (Definition 5, item 3):
`u(aˢ) ≥ u(a)` under `Γ₀`'s payoffs whenever `aˢ ∈ Φ(a)`. -/
def ParetoImprovingFor (Γ₀ : Game N 𝒜) (Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)) : Prop :=
  ∀ a b, a ~[Φ] b → Γ₀.u a ≤ Γ₀.u b

/-- **The certificate form of Definition 5** (the "conciser way to state" the consequence of
Lemma 21, with erratum D9 corrected): a Pareto-improving derivation from `Γ₀` to its subset
game `Γs` exists iff there is a Pareto-improving isomorphism from the full reduction of
`Γ₀` onto the full reduction of `Γs`.  The right-hand side is what Theorem 9's membership
algorithm guesses and Proposition 10's search enumerates.

Paper node: `Lemma 22` -/
theorem exists_paretoImproving_deriv_iff (Γ₀ Γs : Game N 𝒜) (hsub : Γs.IsSubsetGameOf Γ₀) :
    (∃ Φ, Deriv Γ₀ Γ₀ Γs Φ ∧ ParetoImprovingFor Γ₀ Φ) ↔
      ∃ ψ : GameIso Γ₀.reduce Γs.reduce, ψ.ParetoImproving := by
  constructor
  · rintro ⟨Φ, d, hΦ⟩
    obtain ⟨ψ, hψ⟩ := d.exists_iso
    refine ⟨ψ, fun a ha => ?_⟩
    rw [Game.reduce_u]
    exact hΦ a _ (hψ a ha)
  · rintro ⟨ψ, hψ⟩
    refine ⟨_, Deriv.normal (Game.IsSubsetGameOf.refl Γ₀) hsub ψ, fun a b hab => ?_⟩
    obtain ⟨ha, rfl⟩ := (Deriv.mem_normalRel ψ a b).1 hab
    have := hψ a ha
    rwa [Game.reduce_u] at this

/-- **The SPI decision problem** (Definition 5): does `Γ` have a subset game `Γs` such that
(1) the full reductions of `Γs` and `Γ` are not equal (in the paper's sense of equality,
`Game.EqOn`), (2) some chain of single applications of Assumption 1, Assumption 1 in
reverse, or Assumption 2 leads from `Γ` to `Γs`, and (3) its composite is
Pareto-improving under `Γ`'s payoffs?

Paper node: `Definition 5` -/
def SPIDecision (Γ : Game N 𝒜) : Prop :=
  ∃ Γs : Game N 𝒜, Γs.IsSubsetGameOf Γ ∧ ¬ Γs.reduce.EqOn Γ.reduce ∧
    ∃ Φ, Deriv Γ Γ Γs Φ ∧ ParetoImprovingFor Γ Φ

/-- **The strict SPI decision problem** (Definition 5, item 4): additionally some player `i`
and some outcome `a` surviving iterated elimination have `uᵢ(Φ(a)) > uᵢ(a)`.

Paper node: `Definition 5` -/
def StrictSPIDecision (Γ : Game N 𝒜) : Prop :=
  ∃ Γs : Game N 𝒜, Γs.IsSubsetGameOf Γ ∧ ¬ Γs.reduce.EqOn Γ.reduce ∧
    ∃ Φ, Deriv Γ Γ Γs Φ ∧ ParetoImprovingFor Γ Φ ∧
      ∃ i, ∃ a ∈ Γ.reduce.profiles, ∀ b, a ~[Φ] b → Γ.u a i < Γ.u b i

/-- **The unilateral SPI decision problem** (Definition 5, item 5): additionally `Γs` is a
unilateral subset game of `Γ` (Definition 2).

Paper node: `Definition 5` -/
def UnilateralSPIDecision (Γ : Game N 𝒜) : Prop :=
  ∃ Γs : Game N 𝒜, Γs.IsSubsetGameOf Γ ∧ ¬ Γs.reduce.EqOn Γ.reduce ∧
    (∃ Φ, Deriv Γ Γ Γs Φ ∧ ParetoImprovingFor Γ Φ) ∧ Γ.Unilateral Γs

end decision

end Game

/-! ### Soundness of derivations -/

section soundness

variable {Ω : Type w} {X : Play N 𝒜 Ω} {L : Filter Ω}

/-- Under Assumption 1 the representatives play a game as they play any game obtained
from it by iterated elimination, in particular its full reduction. -/
lemma Play.SatisfiesA1.play_elimStar (hA1 : X.SatisfiesA1 L) {Γ G : Game N 𝒜}
    (h : Γ.ElimStar G) : ∀ᶠ ω in L, X.play G ω = X.play Γ ω := by
  induction h with
  | refl => exact Eventually.of_forall fun _ => rfl
  | tail _ hstep ih =>
    obtain ⟨i, ã, hã, rfl⟩ := hstep
    filter_upwards [ih, hA1.play_erase _ hã] with ω h₁ h₂
    rw [h₂, h₁]

lemma Play.SatisfiesA1.play_reduce [Fintype N] (hA1 : X.SatisfiesA1 L) (Γ : Game N 𝒜) :
    ∀ᶠ ω in L, X.play Γ.reduce ω = X.play Γ ω :=
  hA1.play_elimStar Γ.elimStar_reduce

/-- **Soundness of Definition 5's derivations**: if a Pareto-improving derivation leads
from `Γ₀` to its subset game `Γs`, then `Γs` is an SPI on `Γ₀` under every play family
satisfying Assumptions 1 and 2.  (Structure theorem, then Assumption 1 along the
reductions, Assumption 2 with Lemma 4 at the isomorphism, Theorem 3.) -/
lemma Play.isSPI_of_deriv [Fintype N] [∀ i, Nonempty (𝒜 i)] (hA1 : X.SatisfiesA1 L)
    (hA2 : X.SatisfiesA2 L)
    {Γ₀ Γs : Game N 𝒜} (hsub : Γs.IsSubsetGameOf Γ₀)
    {Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)} (d : Game.Deriv Γ₀ Γ₀ Γs Φ)
    (hΦ : Game.ParetoImprovingFor Γ₀ Φ) : X.IsSPI L Γ₀ Γs := by
  obtain ⟨ψ, hψ⟩ := (Game.exists_paretoImproving_deriv_iff Γ₀ Γs hsub).1 ⟨Φ, d, hΦ⟩
  obtain ⟨ψ', hψ', hc⟩ := Play.exists_paretoImproving_corresponds_of_assumption2 hA2
    Γ₀.reduce_reduced Γs.reduce_reduced ψ hψ
  refine ⟨hsub, ?_⟩
  filter_upwards [hA1.play_reduce Γ₀, hA1.play_reduce Γs, hc] with ω h₀ hs hω
  obtain ⟨hmem, hmap⟩ := (ψ'.mem_rel _ _).1 hω
  rw [← h₀, ← hs, hmap]
  have := hψ' _ hmem
  rwa [Game.reduce_u] at this

end soundness

end derivation

end SafeParetoImprovements
