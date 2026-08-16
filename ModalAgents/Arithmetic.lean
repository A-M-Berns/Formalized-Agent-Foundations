/-
  The arithmetic layer (Barasz, §1 and §4).

  The rest of this development works inside `GL`; this file is where `GL` statements
  become statements about a formal system extending `PA`, which is the level at which
  the paper states §4.

  Main results:
  - `lob_theorem`                       : Löb's Theorem (§1, Thm 1.1)
  - `arithmetic_modal_substitution`     : modal substitution congruence (§4, Lemma 4.5)
  - `arithmetic_fixedPoint_uniqueness`  : uniqueness of arithmetic fixed points
                                          (§4, Cor 4.4)
-/

import ModalAgents.FixedPoint
import ProvabilityLogic.ProvabilityLogic.GL.Basic
import Foundation.FirstOrder.Incompleteness.Löb

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

/-! ## Löb's Theorem (Barasz, §1) -/

open LO.FirstOrder LO.FirstOrder.Arithmetic in
/-- **Löb's Theorem.** For a formal system `T` including Peano Arithmetic, writing
`Bootstrapping.provabilityPred T σ` for the arithmetized "there is a `T`-proof of `σ`"
in a fixed Gödel numbering (available because `T` is `Δ₁`-definable): if `T` proves
`□σ 🡒 σ` then `T` proves `σ`.

This is a citation, not a reproof: it is Foundation's
`LO.FirstOrder.Arithmetic.löb_theorem`, which is stated there slightly more generally,
for every `Δ₁` theory extending `𝗜𝚺₁`. The hypothesis is specialized to `𝗣𝗔 ⪯ T` here
to match the paper's "a formal system which includes Peano Arithmetic" verbatim.

Löb's Theorem is what the whole paper runs on; its `GL`-side counterpart, used
throughout this development, is `lob_rule` in `ModalAgents/GL.lean`.

Paper node: Theorem 1.1 (§1). -/
theorem lob_theorem {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔 ⪯ T] {σ : ArithmeticSentence}
    (h : T ⊢ Bootstrapping.provabilityPred T σ 🡒 σ) : T ⊢ σ :=
  haveI : (𝗜𝚺₁ : ArithmeticTheory) ⪯ T :=
    Entailment.WeakerThan.trans (𝓣 := (𝗣𝗔 : ArithmeticTheory)) inferInstance inferInstance
  LO.FirstOrder.Arithmetic.löb_theorem h

/-! ## Reading a modal formula arithmetically

The upstream `ProvabilityLogic` package supplies the realization machinery: a
`Realization ℕ 𝔅` names a closed arithmetic formula for each propositional atom, and
`Formula.interpret` reads a modal formula as an arithmetic sentence, sending `□` to the
provability predicate `𝔅`. That is exactly the paper's `φ(ψ₁,…,ψₙ)`. The wrapper below
runs it on *Foundation's* modal formulas — the ones this development's `GL` results are
about — through the `GlFixedPointBridge` translation.

Beware the two syntaxes: the upstream package builds `⋏`, `∼` and `🡘` as abbreviations
over `🡒`/`⊥`, whereas Foundation's first-order `Sentence` has them as constructors, so
an interpreted conjunction is *not* syntactically a `Sentence`-level conjunction. It is
of course provably equivalent to one; the `pAnd`/`pIff`/`pBoxdot` abbreviations below
name the shapes that actually come out, so that statements about them are `rfl` rather
than a normalization fight. -/

section Interpretation

open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction

variable {L : FirstOrder.Language} [L.ReferenceableBy L]
  {T₀ T : FirstOrder.Theory L} {𝔅 : Provability T₀ T}

/-- The paper's `φ(ψ₁,…,ψₙ)`: the arithmetic sentence a modal formula denotes once each
atom `i` is read as the closed formula `f i` and `□` as the provability predicate. -/
def arithInterp (f : _root_.Realization ℕ 𝔅) (φ : Modal.Formula ℕ) :
    FirstOrder.Sentence L :=
  _root_.Formula.interpret f (GlFixedPointBridge.toSeq φ)

@[simp] lemma arithInterp_atom (f : _root_.Realization ℕ 𝔅) (a : ℕ) :
    arithInterp f (.atom a) = f.val a := rfl

@[simp] lemma arithInterp_imp (f : _root_.Realization ℕ 𝔅) (A B : Modal.Formula ℕ) :
    arithInterp f (A 🡒 B) = (arithInterp f A 🡒 arithInterp f B) := rfl

@[simp] lemma arithInterp_box (f : _root_.Realization ℕ 𝔅) (A : Modal.Formula ℕ) :
    arithInterp f (□A) = 𝔅 (arithInterp f A) := rfl

/-- Rebind one atom of a realization. -/
def _root_.Realization.update (f : _root_.Realization ℕ 𝔅) (p : ℕ)
    (σ : FirstOrder.Sentence L) : _root_.Realization ℕ 𝔅 :=
  ⟨fun a => if a = p then σ else f.val a⟩

@[simp] lemma Realization.update_val (f : _root_.Realization ℕ 𝔅) (p : ℕ)
    (σ : FirstOrder.Sentence L) (a : ℕ) :
    (f.update p σ).val a = if a = p then σ else f.val a := rfl

/-- Realizations agreeing on the atoms of `φ` interpret `φ` identically. -/
lemma arithInterp_congr_atoms {f₁ f₂ : _root_.Realization ℕ 𝔅} {φ : Modal.Formula ℕ}
    (h : ∀ a ∈ φ.atoms, f₁.val a = f₂.val a) : arithInterp f₁ φ = arithInterp f₂ φ :=
  _root_.Formula.interpret_congr_atoms
    (by rw [GlFixedPointBridge.atoms_toSeq]; exact h)

/-- Substituting for atom `p` in the modal formula is rebinding atom `p` in the
realization: the syntactic `diag` and the semantic `update` agree. -/
lemma arithInterp_subst_diag (f : _root_.Realization ℕ 𝔅) (p : ℕ)
    (φ χ : Modal.Formula ℕ) :
    arithInterp f (φ⟦diag p χ⟧) = arithInterp (f.update p (arithInterp f χ)) φ := by
  show _root_.Formula.interpret f (GlFixedPointBridge.toSeq (φ⟦diag p χ⟧)) = _
  rw [GlFixedPointBridge.toSeq_diag, _root_.Formula.interpret_subst]
  congr 1
  refine congrArg _root_.Realization.mk (funext fun a => ?_)
  by_cases h : a = p
  · simp [h, _root_.Formula.Substitution.single, arithInterp]
  · simp [h, _root_.Formula.Substitution.single, _root_.Formula.interpret]

/-- The interpreted shape of a modal conjunction. -/
abbrev pAnd (a b : FirstOrder.Sentence L) : FirstOrder.Sentence L := (a 🡒 (b 🡒 ⊥)) 🡒 ⊥

/-- The interpreted shape of a modal biconditional. -/
abbrev pIff (a b : FirstOrder.Sentence L) : FirstOrder.Sentence L :=
  pAnd (a 🡒 b) (b 🡒 a)

/-- The interpreted shape of `⊡a`, the paper's `□⁺a`. -/
abbrev pBoxdot (𝔅 : Provability T₀ T) (a : FirstOrder.Sentence L) : FirstOrder.Sentence L :=
  pAnd a (𝔅 a)

@[simp] lemma arithInterp_and (f : _root_.Realization ℕ 𝔅) (A B : Modal.Formula ℕ) :
    arithInterp f (A ⋏ B) = pAnd (arithInterp f A) (arithInterp f B) := rfl

@[simp] lemma arithInterp_iff (f : _root_.Realization ℕ 𝔅) (A B : Modal.Formula ℕ) :
    arithInterp f (A 🡘 B) = pIff (arithInterp f A) (arithInterp f B) := rfl

@[simp] lemma arithInterp_boxdot (f : _root_.Realization ℕ 𝔅) (A : Modal.Formula ℕ) :
    arithInterp f (⊡A) = pBoxdot 𝔅 (arithInterp f A) := rfl

end Interpretation

/-! ## Lemma 4.5 (Barasz, §4): modal substitution

The paper's proof is "Lindström's Lemma 8, applied `n` times, then arithmetic
soundness". Once the realization machinery is in place the direct induction is shorter,
and — this is the point — it lands in the right theory. The upstream package's
`Formula.interpret_iff_congr` is the same induction with hypotheses *and* conclusion in
the provability predicate's **base** theory `T₀` (`𝗜𝚺₁` for a standard provability
predicate). The paper's Lemma 4.5 has both in `PA`, which is the **object** theory `T`,
and the `T₀` form does not imply it: a `T`-provable equivalence of the `ψᵢ` is not a
`T₀`-provable one. So the statement below is proved here rather than cited; the `□` step
is `𝔅.ext`, which is exactly where the base theory reappears and is discharged. -/

section Substitution

open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction

variable {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
  {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T] {𝔅 : Provability T₀ T} [𝔅.HBL]

/-- **Modal substitution.** If `φ` is a modal formula and the arithmetic formulas
`ψᵢ`, `ψᵢ'` naming its atoms satisfy `PA ⊢ ψᵢ 🡘 ψᵢ'` for each `i`, then
`PA ⊢ φ(ψ₁,…,ψₙ) 🡘 φ(ψ₁',…,ψₙ')`.

`f₁`, `f₂` are the two families of closed arithmetic formulas, and the object theory `T`
plays the paper's `PA` — both in the hypotheses and in the conclusion, as printed.

Not to be confused with `subst_congr` (`ModalAgents/FixedPoint.lean`), which is the
`GL`-level congruence and states nothing about arithmetic.

Paper node: Lemma 4.5 (§4). -/
theorem arithmetic_modal_substitution {f₁ f₂ : _root_.Realization ℕ 𝔅}
    (h : ∀ a, T ⊢ f₁.val a 🡘 f₂.val a) (φ : Modal.Formula ℕ) :
    T ⊢ arithInterp f₁ φ 🡘 arithInterp f₂ φ := by
  induction φ with
  | hatom a => exact h a
  | hfalsum => cl_prover
  | himp A B ihA ihB =>
    rw [arithInterp_imp, arithInterp_imp]; cl_prover [ihA, ihB]
  | hbox A ih =>
    rw [arithInterp_box, arithInterp_box]
    exact Entailment.WeakerThan.pbl (𝔅.ext ih)

end Substitution

/-! ## Corollary 4.4 (Barasz, §4): uniqueness of arithmetic fixed points -/

section ArithmeticUniqueness

open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction

variable {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
  {T U : FirstOrder.Theory L} [FirstOrder.ProvabilityAbstraction.Diagonalization T]
  [T ⪯ U] {𝔅 : Provability T U} [𝔅.HBL]

/-- An atom at or beyond `φ.freshAtom` does not occur in `φ`. -/
private lemma notMem_atoms_of_freshAtom_le {φ : Modal.Formula ℕ} {k : ℕ}
    (h : φ.freshAtom ≤ k) : k ∉ φ.atoms := by
  intro hk
  have hle := LO.Modal.Formula.le_max_atoms_of_mem_atoms hk
  have hlt := LO.Modal.Formula.le_max_atoms_freshAtom (φ := φ) ⟨k, hk⟩
  omega

/-- **Uniqueness of arithmetic fixed points.** If the modal formula `φ` is modalized in
`p` and the closed arithmetic formulas `ψ`, `ψ'` both satisfy the fixed-point equation
`PA ⊢ ψ 🡘 φ(·, ψ₁,…,ψₙ)`, then `PA ⊢ ψ 🡘 ψ'`.

The realization `f` carries the paper's side formulas `ψ₁,…,ψₙ`, and `f.update p ψ`
substitutes `ψ` for the diagonal variable — so `arithInterp (f.update p ψ) φ` is the
paper's `φ(ψ,ψ₁,…,ψₙ)`.

This is the paper's own proof: arithmetic soundness of `GL` (Theorem 4.1) applied to the
internal form of Theorem 4.3, followed by "`PA ⊢ φ̃` implies `PA ⊢ □⁺φ̃`", which is the
first Hilbert–Bernays–Löb condition.

Paper node: Corollary 4.4 (§4). -/
theorem arithmetic_fixedPoint_uniqueness {p : ℕ} {φ : Modal.Formula ℕ}
    (hmod : Modalized p φ) (f : _root_.Realization ℕ 𝔅)
    {ψ ψ' : FirstOrder.Sentence L}
    (hfix : U ⊢ ψ 🡘 arithInterp (f.update p ψ) φ)
    (hfix' : U ⊢ ψ' 🡘 arithInterp (f.update p ψ') φ) :
    U ⊢ ψ 🡘 ψ' := by
  have h₁ : U ⊢ pIff ψ (arithInterp (f.update p ψ) φ) := by cl_prover [hfix]
  have h₂ : U ⊢ pIff ψ' (arithInterp (f.update p ψ') φ) := by cl_prover [hfix']
  suffices h : U ⊢ pIff ψ ψ' by cl_prover [h]
  -- Name the two fixed points by fresh atoms, and read the internal Theorem 4.3
  -- through the realization that sends them to `ψ` and `ψ'`.
  set q : ℕ := φ.freshAtom + p + 1 with hqdef
  set q' : ℕ := φ.freshAtom + p + 2 with hq'def
  have hq : q ∉ φ.atoms := notMem_atoms_of_freshAtom_le (by omega)
  have hq' : q' ∉ φ.atoms := notMem_atoms_of_freshAtom_le (by omega)
  have hpq : q ≠ p := by omega
  have hpq' : q' ≠ p := by omega
  have hqq' : q ≠ q' := by omega
  set g : _root_.Realization ℕ 𝔅 := (f.update q ψ).update q' ψ' with hgdef
  have hgq : arithInterp g (.atom q) = ψ := by
    simp [hgdef, _root_.Realization.update, hqq']
  have hgq' : arithInterp g (.atom q') = ψ' := by
    simp [hgdef, _root_.Realization.update]
  have key (χ : Modal.Formula ℕ) (σ : FirstOrder.Sentence L)
      (hχ : arithInterp g χ = σ) :
      arithInterp g (φ⟦diag p χ⟧) = arithInterp (f.update p σ) φ := by
    rw [arithInterp_subst_diag, hχ]
    refine arithInterp_congr_atoms fun a ha => ?_
    by_cases hap : a = p
    · simp [hap, _root_.Realization.update]
    · have hne : a ≠ q := fun h => hq (h ▸ ha)
      have hne' : a ≠ q' := fun h => hq' (h ▸ ha)
      simp [hap, hne, hne', hgdef, _root_.Realization.update]
  have hA := key (.atom q) ψ hgq
  have hA' := key (.atom q') ψ' hgq'
  have hsound : U ⊢ arithInterp g
      (⊡((Modal.Formula.atom q) 🡘 φ⟦diag p (.atom q)⟧) ⋏
        ⊡((Modal.Formula.atom q') 🡘 φ⟦diag p (.atom q')⟧) 🡒
        ((Modal.Formula.atom q) 🡘 (Modal.Formula.atom q'))) :=
    _root_.LogicGL.arithmetical_soundness' (f := g)
      (GlFixedPointBridge.mem_logicGL_of_provable
        (glFixedPoint_uniqueness_internal hmod (.atom q) (.atom q')))
  rw [arithInterp_imp, arithInterp_and, arithInterp_boxdot, arithInterp_boxdot,
    arithInterp_iff, arithInterp_iff, arithInterp_iff, hgq, hgq', hA, hA'] at hsound
  have hb₁ : U ⊢ 𝔅 (pIff ψ (arithInterp (f.update p ψ) φ)) :=
    Entailment.WeakerThan.pbl (𝔅.D1 h₁)
  have hb₂ : U ⊢ 𝔅 (pIff ψ' (arithInterp (f.update p ψ') φ)) :=
    Entailment.WeakerThan.pbl (𝔅.D1 h₂)
  have hand : ∀ a b : FirstOrder.Sentence L, U ⊢ a → U ⊢ b → U ⊢ pAnd a b := by
    intro a b ha hb; cl_prover [ha, hb]
  exact hsound ⨀ hand _ _ (hand _ _ h₁ hb₁) (hand _ _ h₂ hb₂)

end ArithmeticUniqueness
