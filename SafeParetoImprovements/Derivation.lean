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
  isomorphism on `reduce Γ` (`normalRel`).  The paper-facing form of Lemma 21 is
  `Deriv.exists_normalForm`, which exhibits the three phases explicitly: the two
  elimination-only chains `Γ →* reduce Γ` and `Γ' →* reduce Γ'` (`ElimStar`, not
  arbitrary `Step`s), the single Assumption 2 move between two fully reduced games, and
  the composite identity.  Lemma 22 is `exists_paretoImproving_normalForm`: the
  Pareto-improving case needs no reverse elimination and ends at `reduce Γs`.

  Two things the rendering deliberately does not claim.  (i) The printed **length bound**
  `m ≤ k` on the reorganized chain is not rendered, and is false as printed (erratum
  D14): for the one-player game with actions `{0,1,2}` and `u(a) = a`, the chain that
  eliminates `0` consists of two games, while any normal-form chain must reach both full
  reductions, insert the isomorphism move and come back, which takes five.  (ii) The
  normal form has the *same endpoints* and a composite that is **contained in** the
  original one on the outcomes of `reduce Γ` — for each such outcome `a`, the original
  composite relates `a` to `ψ.map a`, not necessarily only to it; it is not the original
  composite (which may relate outcomes killed by the reduction).  A chain with restricted move kinds *is* expressible
  in a `Prop`-valued system — the earlier claim that "the same chain reorganized is not
  expressible" was over-broad; what is genuinely not expressible is a statement about a
  *given* chain being permuted, since `Deriv` records no list of moves.
* **Certificate form** (the "conciser way to state" the consequence of Lemma 21, corrected
  per erratum D9): a Pareto-improving derivation from `Γ₀` to `Γs` exists iff there is a
  Pareto-improving isomorphism `reduce Γ₀ ≅ reduce Γs` (`exists_paretoImproving_deriv_iff`).
  This is the object Theorem 9's membership algorithm and Proposition 10's search enumerate.
* **Soundness** (`isSPI_of_deriv`): a Pareto-improving derivation from `Γ₀` to `Γs`
  makes `Γs` an SPI on `Γ₀` under every play family satisfying Assumptions 1 and 2 — via
  the certificate form `exists_paretoImproving_deriv_iff`, Assumption 1 along the
  reductions (`SatisfiesA1.play_reduce`), Assumption 2 with Lemma 4 at the isomorphism
  (`exists_paretoImproving_corresponds_of_assumption2`), and then the definition of
  `Play.IsSPI` directly.  Theorem 3 is *not* used: the correspondence is produced
  explicitly, so no appeal to the characterization is needed.

Completeness (every SPI valid under the assumptions has a derivation) is neither claimed
by the paper nor true, and is not stated.
-/

namespace SafeParetoImprovements

open Filter
open scoped SetRel

universe u v w

variable {N : Type u} {𝒜 : N → Type v}

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

/-- The isomorphism extracted from a derivation: every derivation from `Γ` to `Γ'`
relates each outcome of `reduce Γ` to its image under some isomorphism
`reduce Γ ≅ reduce Γ'`.  Eliminations and reverse eliminations act as the identity on the
outcomes of the full reduction (they never remove one, by path independence), and
isomorphism moves compose.

This is the analytic half of Lemma 21; the paper-facing statement is
`exists_normalForm`.  Note that neither records the printed length bound `m ≤ k` on the
reorganized chain, which is false as printed (erratum D14, see the module docstring). -/
lemma exists_iso (d : Deriv Γ₀ Γ Γ' Φ) :
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

/-- The composite of the three phases of a normal-form derivation — the elimination chain
into `reduce Γ`, the isomorphism move, the reverse elimination chain out of `reduce Γ'` —
is exactly `normalRel ψ`. -/
lemma partialId_comp_rel_comp_partialId (ψ : GameIso Γ.reduce Γ'.reduce) :
    Γ.reduce.partialId ○ (ψ.rel ○ Γ'.reduce.partialId) = normalRel ψ := by
  ext ⟨a, b⟩
  simp only [SetRel.mem_comp, Game.mem_partialId, GameIso.mem_rel, mem_normalRel]
  constructor
  · rintro ⟨c, ⟨ha, rfl⟩, e, ⟨-, rfl⟩, -, rfl⟩; exact ⟨ha, rfl⟩
  · rintro ⟨ha, rfl⟩; exact ⟨a, ⟨ha, rfl⟩, ψ.map a, ⟨ha, rfl⟩, ψ.map_mem ha, rfl⟩

/-- Every isomorphism `reduce Γ ≅ reduce Γ'` is realized by a derivation of the shape
*eliminations, one isomorphism move, reverse eliminations*, whose composite is exactly
`normalRel ψ`.  This is the synthetic half of Lemma 21; the paper-facing statement is
`exists_normalForm`. -/
lemma normal (hsub : Γ.IsSubsetGameOf Γ₀) (hsub' : Γ'.IsSubsetGameOf Γ₀)
    (ψ : GameIso Γ.reduce Γ'.reduce) : Deriv Γ₀ Γ Γ' (normalRel ψ) := by
  have d₁ : Deriv Γ₀ Γ Γ.reduce Γ.reduce.partialId := ofElimStar hsub (Γ.elimStar_reduce)
  have d₂ : Deriv Γ₀ Γ.reduce Γ'.reduce ψ.rel :=
    single (Step.iso (Γ.reduce_isSubsetGameOf.trans hsub) (Γ'.reduce_isSubsetGameOf.trans hsub')
      (Γ.reduce_reduced) (Γ'.reduce_reduced) ψ)
  have d₃ : Deriv Γ₀ Γ'.reduce Γ' Γ'.reduce.partialId := ofElimStar_rev hsub' (Γ'.elimStar_reduce)
  have d := d₁.trans (d₂.trans d₃)
  rw [← partialId_comp_rel_comp_partialId ψ]; exact d

/-- **Lemma 21**: any derivation from `Γ` to `Γ'` inside `Γ₀` can be replaced by one in
normal form with the same endpoints — *eliminations by Assumption 1, then one application
of Assumption 2 between two fully reduced games, then reverse eliminations* — whose
composite is **contained in** the original derivation's on the outcomes of `reduce Γ`.
The statement exhibits every component: the isomorphism `ψ : reduce Γ ≅ reduce Γ'`, the
two elimination-only chains (`ElimStar`, so no Assumption 2 move hides in them) into the
two full reductions, which are reduced, the *single Assumption 2 move*
`Step Γ₀ Γ.reduce Γ'.reduce ψ.rel` between those two fully reduced games, the composite
identity of the three phases, and the resulting derivation.

Two qualifications, both recorded in the module docstring.  The printed length bound
`m ≤ k` is **not** rendered, and is false as printed (erratum D14).  And the last
conjunct is one-directional: on each outcome `a` of `reduce Γ` the *original* composite
`Φ` relates `a` to the normal form's image `ψ.map a` — the normal form is contained in
`Φ` there — not that the two relate `a` to exactly the same outcomes, and nothing is
claimed off `reduce Γ`, where the original composite may relate outcomes that the
reduction kills.

Paper node: `Lemma 21` -/
theorem exists_normalForm (d : Deriv Γ₀ Γ Γ' Φ) :
    ∃ ψ : GameIso Γ.reduce Γ'.reduce,
      Γ.ElimStar Γ.reduce ∧ Γ'.ElimStar Γ'.reduce ∧
        Γ.reduce.Reduced ∧ Γ'.reduce.Reduced ∧
        Step Γ₀ Γ.reduce Γ'.reduce ψ.rel ∧
        Γ.reduce.partialId ○ (ψ.rel ○ Γ'.reduce.partialId) = normalRel ψ ∧
        Deriv Γ₀ Γ Γ' (normalRel ψ) ∧ ∀ a ∈ Γ.reduce.profiles, a ~[Φ] ψ.map a := by
  obtain ⟨ψ, hψ⟩ := d.exists_iso
  exact ⟨ψ, Γ.elimStar_reduce, Γ'.elimStar_reduce, Γ.reduce_reduced, Γ'.reduce_reduced,
    Step.iso (Γ.reduce_isSubsetGameOf.trans d.isSubsetGameOf_left)
      (Γ'.reduce_isSubsetGameOf.trans d.isSubsetGameOf_right)
      Γ.reduce_reduced Γ'.reduce_reduced ψ,
    partialId_comp_rel_comp_partialId ψ, normal d.isSubsetGameOf_left d.isSubsetGameOf_right ψ,
    hψ⟩

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
algorithm guesses and Proposition 10's search enumerates.  The paper-facing form of
Lemma 22 — the explicit symmetry-free chain — is `exists_paretoImproving_normalForm`. -/
lemma exists_paretoImproving_deriv_iff (Γ₀ Γs : Game N 𝒜) (hsub : Γs.IsSubsetGameOf Γ₀) :
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

/-- **Lemma 22**: a Pareto-improving derivation from `Γ₀` to a subset game `Γs` can be
replaced by a chain that uses **no reverse elimination**: eliminate `Γ₀` down to its full
reduction (`ElimStar`, so Assumption 1 only), then a single Assumption 2 move onto
`reduce Γs`.  The statement exhibits the isomorphism `ψ : reduce Γ₀ ≅ reduce Γs`, its
Pareto-improvingness, the forward elimination chain, the single `Step.iso`, the composite
identity `id_{reduce Γ₀} ∘ ψ = ψ`, the resulting derivation, and the fact that its
composite is Pareto-improving for `Γ₀`.

As in the paper, the chain ends at `reduce Γs` rather than at `Γs` itself; that is what
lets the reverse eliminations be dropped.

Paper node: `Lemma 22` -/
theorem exists_paretoImproving_normalForm {Γ₀ Γs : Game N 𝒜} (hsub : Γs.IsSubsetGameOf Γ₀)
    {Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)} (d : Deriv Γ₀ Γ₀ Γs Φ)
    (hΦ : ParetoImprovingFor Γ₀ Φ) :
    ∃ ψ : GameIso Γ₀.reduce Γs.reduce, ψ.ParetoImproving ∧
      Γ₀.ElimStar Γ₀.reduce ∧ Step Γ₀ Γ₀.reduce Γs.reduce ψ.rel ∧
        Γ₀.reduce.partialId ○ ψ.rel = ψ.rel ∧
        Deriv Γ₀ Γ₀ Γs.reduce ψ.rel ∧ ParetoImprovingFor Γ₀ ψ.rel := by
  obtain ⟨ψ, hψ⟩ := (exists_paretoImproving_deriv_iff Γ₀ Γs hsub).1 ⟨Φ, d, hΦ⟩
  have hstep : Step Γ₀ Γ₀.reduce Γs.reduce ψ.rel :=
    Step.iso Γ₀.reduce_isSubsetGameOf (Γs.reduce_isSubsetGameOf.trans hsub)
      Γ₀.reduce_reduced Γs.reduce_reduced ψ
  have hcomp : Γ₀.reduce.partialId ○ ψ.rel = ψ.rel := by
    ext ⟨a, b⟩
    simp only [SetRel.mem_comp, Game.mem_partialId, GameIso.mem_rel]
    constructor
    · rintro ⟨c, ⟨-, rfl⟩, h⟩; exact h
    · rintro ⟨ha, rfl⟩; exact ⟨a, ⟨ha, rfl⟩, ha, rfl⟩
  have hPI : ParetoImprovingFor Γ₀ ψ.rel := by
    intro a b hab
    obtain ⟨ha, hb⟩ := hab
    dsimp only at ha hb
    subst hb
    have := hψ a ha
    rwa [Game.reduce_u] at this
  refine ⟨ψ, hψ, Γ₀.elimStar_reduce, hstep, hcomp, ?_, hPI⟩
  rw [← hcomp]
  exact (Deriv.ofElimStar (Game.IsSubsetGameOf.refl Γ₀) Γ₀.elimStar_reduce).trans
    (Deriv.single hstep)

/-! ### Definition 5 as printed, and why its non-triviality clause is empty (erratum D13)

Definition 5's item 1 asks that "the two resulting games are not equal".  A subset game
may assign *different utilities* to the outcomes it keeps ("a subset game may assign
different utilities to outcomes than the original game", §2), so shifting every payoff of
`reduce Γ` by `+1` produces a subset game whose full reduction is not equal to `reduce Γ`
while the identity action map is an isomorphism between them, and is Pareto-improving
with equality.  The clause is therefore satisfied by every game with at least one player,
and the printed decision problems are constant-true.  The defect is the paper's, not the
rendering's (the adjudication of R1-F18 confirmed the witness against the printed text);
Appendix D's converse argument calls the identity action map *trivial*, which is what the
intended clause is about.

The predicates below render the printed clause verbatim, and
`spiDecisionPrinted_of_nonempty` / `unilateralSPIDecisionPrinted_of_reduced` are the
erratum's witnesses.  `SPIDecision`, `StrictSPIDecision` and `UnilateralSPIDecision`
further below are the repaired predicates that the rest of the development uses. -/

/-- **The SPI decision problem, exactly as printed** (Definition 5): does `Γ` have a
subset game `Γs` such that (1) the full reductions of `Γs` and `Γ` are not equal (in the
paper's sense of equality, `Game.EqOn`), (2) some chain of single applications of
Assumption 1, Assumption 1 in reverse, or Assumption 2 leads from `Γ` to `Γs`, and (3) its
composite is Pareto-improving under `Γ`'s payoffs?

This predicate is **constant-true** (`spiDecisionPrinted_of_nonempty`); erratum D13.  It
is kept because it is what the paper prints; `SPIDecision` is the repaired predicate.

Paper node: `Definition 5` -/
def SPIDecisionPrinted (Γ : Game N 𝒜) : Prop :=
  ∃ Γs : Game N 𝒜, Γs.IsSubsetGameOf Γ ∧ ¬ Γs.reduce.EqOn Γ.reduce ∧
    ∃ Φ, Deriv Γ Γ Γs Φ ∧ ParetoImprovingFor Γ Φ

/-- **The strict SPI decision problem, exactly as printed** (Definition 5, item 4):
additionally some player `i` and some outcome `a` surviving iterated elimination have
`uᵢ(Φ(a)) > uᵢ(a)`.  Non-triviality is the printed clause, which is empty (erratum D13);
`StrictSPIDecision` is the repaired predicate.

Paper node: `Definition 5` -/
def StrictSPIDecisionPrinted (Γ : Game N 𝒜) : Prop :=
  ∃ Γs : Game N 𝒜, Γs.IsSubsetGameOf Γ ∧ ¬ Γs.reduce.EqOn Γ.reduce ∧
    ∃ Φ, Deriv Γ Γ Γs Φ ∧ ParetoImprovingFor Γ Φ ∧
      ∃ i, ∃ a ∈ Γ.reduce.profiles, ∀ b, a ~[Φ] b → Γ.u a i < Γ.u b i

/-- **The unilateral SPI decision problem, exactly as printed** (Definition 5, item 5):
additionally `Γs` is a unilateral subset game of `Γ` (Definition 2).  Constant-true on
fully reduced games (`unilateralSPIDecisionPrinted_of_reduced`); erratum D13.
`UnilateralSPIDecision` is the repaired predicate.

Paper node: `Definition 5` -/
def UnilateralSPIDecisionPrinted (Γ : Game N 𝒜) : Prop :=
  ∃ Γs : Game N 𝒜, Γs.IsSubsetGameOf Γ ∧ ¬ Γs.reduce.EqOn Γ.reduce ∧
    (∃ Φ, Deriv Γ Γ Γs Φ ∧ ParetoImprovingFor Γ Φ) ∧ Γ.Unilateral Γs

/-! #### The erratum's witnesses -/

/-- The subset game on `reduce Γ`'s action sets whose payoffs are `Γ`'s raised by one.
A legal subset game (payoffs of a subset game are unconstrained), fully reduced, and not
`EqOn` `reduce Γ`; the witness for erratum D13. -/
noncomputable def shiftReduce (Γ : Game N 𝒜) : Game N 𝒜 :=
  ⟨Γ.reduce.S, Γ.reduce.nonempty, fun a i => Γ.u a i + 1⟩

lemma shiftReduce_reduced (Γ : Game N 𝒜) : Γ.shiftReduce.Reduced := by
  rintro i a ⟨a', ha'⟩
  rw [Game.strictlyDominates_iff] at ha'
  refine Γ.reduce_reduced i a ⟨a', ?_⟩
  rw [Game.strictlyDominates_iff]
  refine ⟨ha'.1, ha'.2.1, fun b hb => ?_⟩
  have := ha'.2.2 b hb
  simp only [shiftReduce, Game.reduce_u] at *
  linarith

/-- The identity is an isomorphism `reduce Γ ≅ shiftReduce Γ` (`λ = 1`, `c = −1`). -/
noncomputable def shiftReduceIso (Γ : Game N 𝒜) : GameIso Γ.reduce Γ.shiftReduce where
  toFun _ := id
  bijOn _ := Set.bijOn_id _
  scale _ := 1
  scale_pos _ := one_pos
  shift _ := -1
  affine a ha i := by simp [shiftReduce, Game.reduce_u]

/-- **Erratum D13, first witness**: every game with at least one player is a "yes"
instance of the printed SPI decision problem, so `SPIDecisionPrinted` carries no
information.  The witness shifts every payoff of `reduce Γ` by `+1`. -/
lemma spiDecisionPrinted_of_nonempty [Nonempty N] (Γ : Game N 𝒜) : Γ.SPIDecisionPrinted := by
  refine ⟨Γ.shiftReduce, Γ.reduce_isSubsetGameOf, ?_, ?_⟩
  · rw [Game.reduce_of_reduced (shiftReduce_reduced Γ)]
    rintro ⟨-, h2⟩
    obtain ⟨a, ha⟩ := Γ.reduce.profiles_nonempty
    obtain ⟨i⟩ := ‹Nonempty N›
    have := h2 a ha i
    simp only [shiftReduce, Game.reduce_u] at this
    linarith
  · refine (exists_paretoImproving_deriv_iff Γ Γ.shiftReduce Γ.reduce_isSubsetGameOf).2 ?_
    refine ⟨(Γ.shiftReduceIso).cast rfl (Game.reduce_of_reduced (shiftReduce_reduced Γ)).symm, ?_⟩
    intro a _ i
    rw [GameIso.cast_map]
    exact le_rfl

/-- `Γ` with player `i`'s payoff raised by one: a *unilateral* subset game of `Γ`. -/
def bumpPayoff (Γ : Game N 𝒜) (i : N) : Game N 𝒜 :=
  ⟨Γ.S, Γ.nonempty, fun a j => if j = i then Γ.u a j + 1 else Γ.u a j⟩

omit [∀ i, DecidableEq (𝒜 i)] [Fintype N] in
lemma bumpPayoff_reduced {Γ : Game N 𝒜} (h : Γ.Reduced) (i : N) : (Γ.bumpPayoff i).Reduced := by
  rintro j a ⟨a', ha'⟩
  rw [Game.strictlyDominates_iff] at ha'
  refine h j a ⟨a', ?_⟩
  rw [Game.strictlyDominates_iff]
  refine ⟨ha'.1, ha'.2.1, fun b hb => ?_⟩
  have := ha'.2.2 b hb
  simp only [bumpPayoff] at this
  split at this <;> linarith

/-- The identity is an isomorphism `Γ ≅ bumpPayoff Γ i`. -/
def bumpPayoffIso (Γ : Game N 𝒜) (i : N) : GameIso Γ (Γ.bumpPayoff i) where
  toFun _ := id
  bijOn _ := Set.bijOn_id _
  scale _ := 1
  scale_pos _ := one_pos
  shift j := if j = i then -1 else 0
  affine a ha j := by by_cases hj : j = i <;> simp [bumpPayoff, hj]

/-- **Erratum D13, second witness**: every fully reduced game is a "yes" instance of the
printed unilateral SPI decision problem, by raising exactly one player's payoff. -/
lemma unilateralSPIDecisionPrinted_of_reduced {Γ : Game N 𝒜} (h : Γ.Reduced) (i : N) :
    Γ.UnilateralSPIDecisionPrinted := by
  have hsub : (Γ.bumpPayoff i).IsSubsetGameOf Γ := fun _ => Finset.Subset.refl _
  refine ⟨Γ.bumpPayoff i, hsub, ?_, ?_, hsub, i, fun j hj => ⟨rfl, fun a _ => by
    simp [bumpPayoff, hj]⟩⟩
  · rw [Game.reduce_of_reduced (bumpPayoff_reduced h i), Game.reduce_of_reduced h]
    rintro ⟨-, h2⟩
    obtain ⟨a, ha⟩ := Γ.profiles_nonempty
    have := h2 a ha i
    simp only [bumpPayoff, if_true] at this
    linarith
  · refine (exists_paretoImproving_deriv_iff Γ (Γ.bumpPayoff i) hsub).2 ?_
    refine ⟨((Γ.bumpPayoffIso i).cast (Game.reduce_of_reduced h).symm
      (Game.reduce_of_reduced (bumpPayoff_reduced h i)).symm), ?_⟩
    intro a _ j
    rw [GameIso.cast_map]
    exact le_rfl

/-! #### Definition 5 with the non-triviality clause repaired

`dd:nontrivial` — non-triviality reads "**the reduced action sets differ**",
`Γs.reduce.S ≠ Γ.reduce.S`: the representatives are told to play a different set of
actions.  This is the reading Appendix D's hardness argument uses when it calls the
identity action map trivial (extraction l. 2710), and it is insensitive to the payoff
relabelling that empties the printed clause.  Ruled by Anson, 2026-09-12 (erratum D13);
see `notes/paper-errata.md`.

The repaired predicates are not constant: `not_spiDecision_of_card_le_one` gives a "no"
instance, and the Demand Game is a "yes" instance of all three
(`Examples.demandGame_spiDecision`, `Examples.demandGame_strictSPIDecision`, and — for the
unilateral variant — `Examples.complicatedTemptation_unilateralSPIDecision`).

Note that the payoff-shift witnesses above (`shiftReduce`, `bumpPayoff`) do **not** serve
the repaired predicates: they leave `reduce.S` unchanged and therefore fail the repaired
non-triviality clause by construction.  They are exactly the erratum-D13 counterexamples
and serve only the printed predicates. -/

/-- **The SPI decision problem** (Definition 5, non-triviality repaired per erratum D13):
does `Γ` have a subset game `Γs` such that (1) the reduced action sets differ,
`Γs.reduce.S ≠ Γ.reduce.S`, (2) some chain of single applications of Assumption 1,
Assumption 1 in reverse, or Assumption 2 leads from `Γ` to `Γs`, and (3) its composite is
Pareto-improving under `Γ`'s payoffs?

Soundness: `Play.isSPI_of_deriv` turns items (2)–(3) into `Play.IsSPI` under Assumptions
1 and 2.  The Demand Game is a "yes" instance (`Examples.demandGame_spiDecision`); a game
in which every player has one action is a "no" instance
(`not_spiDecision_of_card_le_one`).

Paper node: `Definition 5` -/
def SPIDecision (Γ : Game N 𝒜) : Prop :=
  ∃ Γs : Game N 𝒜, Γs.IsSubsetGameOf Γ ∧ Γs.reduce.S ≠ Γ.reduce.S ∧
    ∃ Φ, Deriv Γ Γ Γs Φ ∧ ParetoImprovingFor Γ Φ

/-- **The strict SPI decision problem** (Definition 5, item 4; non-triviality repaired per
erratum D13): additionally some player `i` and some outcome `a` surviving iterated
elimination have `uᵢ(Φ(a)) > uᵢ(a)`.

**Side condition.**  The paper notes that this matches the strict clause of Definition 1
only because "the definition of the strict SPI problem assumes that all outcomes `a` that
survive iterated elimination occur with positive probability" (extraction l. 1214–1216).
That assumption is not part of the predicate — it is a hypothesis on the *representatives*
— so it appears as an explicit hypothesis of the soundness result
`Play.isStrictSPI_of_deriv`, in the form `∀ a ∈ Γ.reduce.profiles, ∃ᶠ ω in L,
X.play Γ ω = a`.  Without it a "yes" instance need not give a strict SPI.  It is
satisfiable jointly with Assumptions 1 and 2
(`exists_play_satisfiesA1_satisfiesA2_hits`), though not over a one-point sample space.

The Demand Game is a "yes" instance (`Examples.demandGame_strictSPIDecision`).

Paper node: `Definition 5` -/
def StrictSPIDecision (Γ : Game N 𝒜) : Prop :=
  ∃ Γs : Game N 𝒜, Γs.IsSubsetGameOf Γ ∧ Γs.reduce.S ≠ Γ.reduce.S ∧
    ∃ Φ, Deriv Γ Γ Γs Φ ∧ ParetoImprovingFor Γ Φ ∧
      ∃ i, ∃ a ∈ Γ.reduce.profiles, ∀ b, a ~[Φ] b → Γ.u a i < Γ.u b i

/-- **The unilateral SPI decision problem** (Definition 5, item 5; non-triviality repaired
per erratum D13): additionally `Γs` is a unilateral subset game of `Γ` (Definition 2).

Soundness: `Play.isUnilateralSPI_of_deriv`.  The Complicated Temptation Game is a "yes"
instance (`Examples.complicatedTemptation_unilateralSPIDecision`).

Paper node: `Definition 5` -/
def UnilateralSPIDecision (Γ : Game N 𝒜) : Prop :=
  ∃ Γs : Game N 𝒜, Γs.IsSubsetGameOf Γ ∧ Γs.reduce.S ≠ Γ.reduce.S ∧
    (∃ Φ, Deriv Γ Γ Γs Φ ∧ ParetoImprovingFor Γ Φ) ∧ Γ.Unilateral Γs

/-- A game in which every player has at most one action is a **"no" instance** of the
repaired SPI decision problem: every subset game has the same (single) action sets, so no
subset game can pass the repaired non-triviality clause.  The matching "yes" instance is
`Examples.demandGame_spiDecision`; together the two show the repaired predicate is not
constant in either direction.  (The payoff-shift witnesses above are *not* the "yes" half:
they fail the repaired clause, being exactly the erratum-D13 counterexamples.) -/
lemma not_spiDecision_of_card_le_one {Γ : Game N 𝒜} (h : ∀ i, (Γ.S i).card ≤ 1) :
    ¬ Γ.SPIDecision := by
  have hred : ∀ G : Game N 𝒜, (∀ i, (G.S i).card ≤ 1) → G.Reduced := by
    intro G hG i a hd
    obtain ⟨b, hb⟩ := hd.erase_nonempty
    have hab := Finset.mem_erase.1 hb
    have : ¬ (G.S i).card ≤ 1 :=
      not_le.2 (Finset.one_lt_card.2 ⟨b, hab.2, a, hd.mem, hab.1⟩)
    exact this (hG i)
  rintro ⟨Γs, hsub, hne, -⟩
  refine hne ?_
  have hSeq : Γs.S = Γ.S := by
    funext i
    exact Finset.eq_of_subset_of_card_le (hsub i) ((h i).trans (Finset.one_le_card.2 (Γs.nonempty i)))
  have hs : ∀ i, (Γs.S i).card ≤ 1 := fun i => by rw [hSeq]; exact h i
  rw [Game.reduce_of_reduced (hred Γs hs), Game.reduce_of_reduced (hred Γ h), hSeq]

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
satisfying Assumptions 1 and 2.

*Provenance of the proof*: the certificate form of Definition 5
(`Game.exists_paretoImproving_deriv_iff`) turns the derivation into a Pareto-improving
isomorphism of the two full reductions; Assumption 1 identifies the play of each game with
the play of its reduction (`SatisfiesA1.play_reduce`); Assumption 2 with Lemma 4 supplies a
correspondence along *some* isomorphism, still Pareto-improving
(`Play.exists_paretoImproving_corresponds_of_assumption2`); and `Play.IsSPI` is then
discharged from its definition.  Theorem 3 is not used.

The subset-game clause of Definition 5 is not a separate hypothesis: the derivation
supplies it (`d.isSubsetGameOf_right`). -/
lemma Play.isSPI_of_deriv [Fintype N] (hA1 : X.SatisfiesA1 L)
    (hA2 : X.SatisfiesA2 L)
    {Γ₀ Γs : Game N 𝒜}
    {Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)} (d : Game.Deriv Γ₀ Γ₀ Γs Φ)
    (hΦ : Game.ParetoImprovingFor Γ₀ Φ) : X.IsSPI L Γ₀ Γs := by
  haveI : ∀ i, Nonempty (𝒜 i) := Γ₀.nonempty_universe
  have hsub : Γs.IsSubsetGameOf Γ₀ := d.isSubsetGameOf_right
  obtain ⟨ψ, hψ⟩ := (Game.exists_paretoImproving_deriv_iff Γ₀ Γs hsub).1 ⟨Φ, d, hΦ⟩
  obtain ⟨ψ', hψ', hc⟩ := Play.exists_paretoImproving_corresponds_of_assumption2 hA2
    Γ₀.reduce_reduced Γs.reduce_reduced ψ hψ
  refine ⟨hsub, ?_⟩
  filter_upwards [hA1.play_reduce Γ₀, hA1.play_reduce Γs, hc] with ω h₀ hs hω
  obtain ⟨hmem, hmap⟩ := (ψ'.mem_rel _ _).1 hω
  rw [← h₀, ← hs, hmap]
  have := hψ' _ hmem
  rwa [Game.reduce_u] at this

/-- **Soundness for the unilateral variant** (Definition 5, item 5): a Pareto-improving
derivation onto a *unilateral* subset game makes that game a unilateral SPI, under every
play family satisfying Assumptions 1 and 2. -/
lemma Play.isUnilateralSPI_of_deriv [Fintype N] (hA1 : X.SatisfiesA1 L)
    (hA2 : X.SatisfiesA2 L) {Γ₀ Γs : Game N 𝒜} (huni : Γ₀.Unilateral Γs)
    {Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)} (d : Game.Deriv Γ₀ Γ₀ Γs Φ)
    (hΦ : Game.ParetoImprovingFor Γ₀ Φ) : X.IsUnilateralSPI L Γ₀ Γs :=
  ⟨huni, Play.isSPI_of_deriv hA1 hA2 d hΦ⟩

/-- **Soundness for the strict variant** (Definition 5, item 4): a Pareto-improving
derivation whose composite is *strictly* improving for player `i` at some surviving
outcome `a` makes `Γs` a strict SPI — provided the paper's side condition holds, that
every outcome surviving iterated elimination is played with positive probability
(extraction l. 1214–1216).  The side condition is what carries strictness from one
outcome of `reduce Γ₀` to a positive-probability event; without it the strict clause of
Definition 1 can fail at a "yes" instance.

Note that the recorded `Φ` does not have to be the correspondence Assumption 2 supplies:
strictness transfers to whichever isomorphism it supplies by Lemma 4 (the strict form).

The side condition is not vacuous, but it does rule out the one-point sample space as soon
as the reduction has two outcomes: the witness is the page-varying book
(`exists_play_satisfiesA1_satisfiesA2_hits`), and
`Examples.demandGame_isStrictSPI_of_deriv_witnessed` exhibits every hypothesis of this
lemma holding at once (R2-F18). -/
lemma Play.isStrictSPI_of_deriv [Fintype N] (hA1 : X.SatisfiesA1 L)
    (hA2 : X.SatisfiesA2 L) {Γ₀ Γs : Game N 𝒜}
    {Φ : SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i)} (d : Game.Deriv Γ₀ Γ₀ Γs Φ)
    (hΦ : Game.ParetoImprovingFor Γ₀ Φ)
    (hpos : ∀ a ∈ Γ₀.reduce.profiles, ∃ᶠ ω in L, X.play Γ₀ ω = a)
    {i : N} {a : ∀ i, 𝒜 i} (ha : a ∈ Γ₀.reduce.profiles)
    (hstrict : ∀ b, a ~[Φ] b → Γ₀.u a i < Γ₀.u b i) : X.IsStrictSPI L Γ₀ Γs := by
  haveI : ∀ i, Nonempty (𝒜 i) := Γ₀.nonempty_universe
  have hsub : Γs.IsSubsetGameOf Γ₀ := d.isSubsetGameOf_right
  refine ⟨Play.isSPI_of_deriv hA1 hA2 d hΦ, ?_⟩
  obtain ⟨ψ₀, hψ₀⟩ := (Game.exists_paretoImproving_deriv_iff Γ₀ Γs hsub).1 ⟨Φ, d, hΦ⟩
  obtain ⟨ψ, hψ⟩ := d.exists_iso
  have hPI : ψ.ParetoImproving := GameIso.paretoImproving_of_paretoImproving ψ₀ ψ hψ₀
  have hlt : Γ₀.reduce.u a < Γ₀.reduce.u (ψ.map a) := by
    rw [Pi.lt_def]
    refine ⟨hPI a ha, i, ?_⟩
    simpa only [Game.reduce_u] using hstrict _ (hψ a ha)
  obtain ⟨ψ', hψ'PI, hc⟩ := Play.exists_paretoImproving_corresponds_of_assumption2 hA2
    Γ₀.reduce_reduced Γs.reduce_reduced ψ hPI
  obtain ⟨-, a', ha', hlt'⟩ :=
    GameIso.strictlyParetoImproving_of_strictlyParetoImproving ψ ψ' ⟨hPI, a, ha, hlt⟩
  obtain ⟨-, j, hj⟩ := Pi.lt_def.1 hlt'
  refine ⟨j, ?_⟩
  have hev : ∀ᶠ ω in L, X.play Γ₀.reduce ω = X.play Γ₀ ω ∧
      (X.play Γs.reduce ω = X.play Γs ω ∧ X.play Γ₀.reduce ω ~[ψ'.rel] X.play Γs.reduce ω) :=
    (hA1.play_reduce Γ₀).and ((hA1.play_reduce Γs).and hc)
  refine ((hpos a' ha').and_eventually hev).mono ?_
  rintro ω ⟨hω, h₀, hs, hrel⟩
  have hmap : X.play Γs.reduce ω = ψ'.map (X.play Γ₀.reduce ω) := ((ψ'.mem_rel _ _).1 hrel).2
  have hA : X.play Γ₀.reduce ω = a' := by rw [h₀, hω]
  have hB : X.play Γs ω = ψ'.map a' := by rw [← hs, hmap, hA]
  rw [hω, hB]
  simpa only [Game.reduce_u] using hj

end soundness

end derivation

end SafeParetoImprovements
