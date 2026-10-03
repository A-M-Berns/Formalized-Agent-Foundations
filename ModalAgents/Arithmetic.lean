/-
  The arithmetic layer (Barasz, §1 and §4).

  The rest of this development works inside `GL`; this file is where `GL` statements
  become statements about a formal system extending `PA`, which is the level at which
  the paper states §4.

  Main results:
  - `lob_theorem`                       : Löb's Theorem (§1, Thm 1.1)
  - `Cooperates.arithmeticLift`,
    `ProvablyDefects.arithmeticLift`    : the arithmetical lift of GL-provable
                                          cooperation / defection (§4, Thm 4.1)
  - `arithmetic_modal_substitution`     : modal substitution congruence (§4, Lemma 4.5)
  - `arithmetic_fixedPoint_uniqueness`  : uniqueness of arithmetic fixed points
                                          (§4, Cor 4.4)
-/

import ModalAgents.Behavioral
import ProvabilityLogic.ProvabilityLogic.GL.Basic
import Foundation.FirstOrder.Incompleteness.Löb

open FFL FFL.Entailment
open LogicGL

/-! ## Löb's Theorem (Barasz, §1) -/

open FFL.FirstOrder FFL.FirstOrder.Arithmetic in
/-- **Löb's Theorem.** For a formal system `T` including Peano Arithmetic, writing
`Bootstrapping.provabilityPred T σ` for the arithmetized "there is a `T`-proof of `σ`"
in a fixed Gödel numbering (available because `T` is `Δ₁`-definable): if `T` proves
`□σ 🡒 σ` then `T` proves `σ`.

This is a citation, not a reproof: it is Foundation's
`FFL.FirstOrder.Arithmetic.löb_theorem`, which is stated there slightly more generally,
for every `Δ₁` theory extending `𝗜𝚺₁`. The hypothesis is specialized to `𝗣𝗔 ⪯ T` here
to match the paper's "a formal system which includes Peano Arithmetic" verbatim.

Löb's Theorem is what the whole paper runs on; its `GL`-side counterpart, used
throughout this development, is `lob_rule` in `ModalAgents/GL.lean`.

Paper node: Theorem 1.1 (§1). -/
theorem lob_theorem {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔 ⪯ T] {σ : ArithmeticSentence}
    (h : T ⊢ Bootstrapping.provabilityPred T σ 🡒 σ) : T ⊢ σ :=
  haveI : (𝗜𝚺₁ : ArithmeticTheory) ⪯ T :=
    Entailment.WeakerThan.trans (𝓣 := (𝗣𝗔 : ArithmeticTheory)) inferInstance inferInstance
  FFL.FirstOrder.Arithmetic.löb_theorem h

/-! ## Reading a modal formula arithmetically

The `ProvabilityLogic` package supplies the realization machinery: a
`Realization ℕ L` names a closed formula of `L` for each propositional atom, and
`Formula.interpret f 𝔅` reads a modal formula as a sentence, sending `□` to the
provability predicate `𝔅`. That is exactly the paper's `φ(ψ₁,…,ψₙ)`, and it is used
here directly on the formulas this development's `GL` results are about.

Beware the two syntaxes: the modal `⋏`, `∼` and `🡘` are abbreviations over `🡒`/`⊥`,
whereas Foundation's first-order `Sentence` has them as constructors, so an interpreted
conjunction is *not* syntactically a `Sentence`-level conjunction. It is of course
provably equivalent to one; the `pAnd`/`pIff`/`pBoxdot` abbreviations below name the
shapes that actually come out, so that statements about them are `rfl` rather than a
normalization fight. -/

section Interpretation

open FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction

variable {L : FirstOrder.Language}

/-- Rebind one atom of a realization. -/
def _root_.Realization.update (f : _root_.Realization ℕ L) (p : ℕ)
    (σ : FirstOrder.Sentence L) : _root_.Realization ℕ L :=
  ⟨fun a => if a = p then σ else f.val a⟩

@[simp] lemma Realization.update_val (f : _root_.Realization ℕ L) (p : ℕ)
    (σ : FirstOrder.Sentence L) (a : ℕ) :
    (f.update p σ).val a = if a = p then σ else f.val a := rfl

variable [L.ReferenceableBy L] {T₀ T : FirstOrder.Theory L} {𝔅 : Provability T₀ T}

@[simp] lemma interpret_atom (f : _root_.Realization ℕ L) (a : ℕ) :
    (_root_.Formula.atom a).interpret f 𝔅 = f.val a := rfl

@[simp] lemma interpret_imp (f : _root_.Realization ℕ L) (A B : _root_.Formula ℕ) :
    (A 🡒 B).interpret f 𝔅 = ((A.interpret f 𝔅 🡒 B.interpret f 𝔅) : FirstOrder.Sentence L) := rfl

@[simp] lemma interpret_box (f : _root_.Realization ℕ L) (A : _root_.Formula ℕ) :
    (□A).interpret f 𝔅 = 𝔅 (A.interpret f 𝔅) := rfl

/-- Substituting for atom `p` in the modal formula is rebinding atom `p` in the
realization: the syntactic `diag` and the semantic `update` agree. -/
lemma interpret_subst_diag (f : _root_.Realization ℕ L) (p : ℕ)
    (φ χ : _root_.Formula ℕ) :
    (φ⟦diag p χ⟧).interpret f 𝔅 = φ.interpret (f.update p (χ.interpret f 𝔅)) 𝔅 := by
  rw [_root_.Formula.interpret_subst]
  congr 1
  refine congrArg _root_.Realization.mk (funext fun a => ?_)
  by_cases h : a = p
  · simp [h, diag, _root_.Formula.Substitution.single]
  · simp [h, diag, _root_.Formula.Substitution.single]

/-- The interpreted shape of a modal conjunction. -/
abbrev pAnd (a b : FirstOrder.Sentence L) : FirstOrder.Sentence L :=
  (a 🡒 (b 🡒 (⊥ : FirstOrder.Sentence L))) 🡒 (⊥ : FirstOrder.Sentence L)

/-- The interpreted shape of a modal biconditional. -/
abbrev pIff (a b : FirstOrder.Sentence L) : FirstOrder.Sentence L :=
  pAnd ((a 🡒 b : FirstOrder.Sentence L)) ((b 🡒 a : FirstOrder.Sentence L))

/-- The interpreted shape of `⊡a`, the paper's `□⁺a`. -/
abbrev pBoxdot (𝔅 : Provability T₀ T) (a : FirstOrder.Sentence L) : FirstOrder.Sentence L :=
  pAnd a (𝔅 a)

@[simp] lemma interpret_and (f : _root_.Realization ℕ L) (A B : _root_.Formula ℕ) :
    (A ⋏ B).interpret f 𝔅 = pAnd (A.interpret f 𝔅) (B.interpret f 𝔅) := rfl

@[simp] lemma interpret_iff (f : _root_.Realization ℕ L) (A B : _root_.Formula ℕ) :
    (A 🡘 B).interpret f 𝔅 = pIff (A.interpret f 𝔅) (B.interpret f 𝔅) := rfl

@[simp] lemma interpret_boxdot (f : _root_.Realization ℕ L) (A : _root_.Formula ℕ) :
    (⊡A).interpret f 𝔅 = pBoxdot 𝔅 (A.interpret f 𝔅) := rfl

end Interpretation

/-! ## Lemma 4.5 (Barasz, §4): modal substitution

The paper's proof is "Lindström's Lemma 8, applied `n` times, then arithmetic
soundness". Once the realization machinery is in place the direct induction is shorter,
and — this is the point — it lands in the right theory. The package's
`Formula.interpret_iff_congr` is the same induction with hypotheses *and* conclusion in
the provability predicate's **base** theory `T₀` (`𝗜𝚺₁` for a standard provability
predicate). The paper's Lemma 4.5 has both in `PA`, which is the **object** theory `T`,
and the `T₀` form does not imply it: a `T`-provable equivalence of the `ψᵢ` is not a
`T₀`-provable one. So the statement below is proved here rather than cited; the `□` step
is `𝔅.ext`, which is exactly where the base theory reappears and is discharged. -/

section Substitution

open FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction

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
theorem arithmetic_modal_substitution {f₁ f₂ : _root_.Realization ℕ L}
    (h : ∀ a, T ⊢ f₁.val a 🡘 f₂.val a) (φ : _root_.Formula ℕ) :
    T ⊢ φ.interpret f₁ 𝔅 🡘 φ.interpret f₂ 𝔅 := by
  induction φ with
  | atom a => exact h a
  | bot => dsimp [_root_.Formula.interpret]; cl_prover
  | imp A B ihA ihB =>
    rw [interpret_imp, interpret_imp]; cl_prover [ihA, ihB]
  | box A ih =>
    rw [interpret_box, interpret_box]
    exact Entailment.WeakerThan.pbl (𝔅.ext ih)

end Substitution

/-! ## Corollary 4.4 (Barasz, §4): uniqueness of arithmetic fixed points -/

section ArithmeticUniqueness

open FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction

variable {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
  {T U : FirstOrder.Theory L} [FirstOrder.ProvabilityAbstraction.Diagonalization T]
  [T ⪯ U] {𝔅 : Provability T U} [𝔅.HBL]

/-- **Uniqueness of arithmetic fixed points.** If the modal formula `φ` is modalized in
`p` and the closed arithmetic formulas `ψ`, `ψ'` both satisfy the fixed-point equation
`PA ⊢ ψ 🡘 φ(·, ψ₁,…,ψₙ)`, then `PA ⊢ ψ 🡘 ψ'`.

The realization `f` carries the paper's side formulas `ψ₁,…,ψₙ`, and `f.update p ψ`
substitutes `ψ` for the diagonal variable — so `φ.interpret (f.update p ψ) 𝔅` is the
paper's `φ(ψ,ψ₁,…,ψₙ)`.

This is the paper's own proof: arithmetic soundness of `GL` (Theorem 4.1) applied to the
internal form of Theorem 4.3, followed by "`PA ⊢ φ̃` implies `PA ⊢ □⁺φ̃`", which is the
first Hilbert–Bernays–Löb condition.

Paper node: Corollary 4.4 (§4). -/
theorem arithmetic_fixedPoint_uniqueness {p : ℕ} {φ : _root_.Formula ℕ}
    (hmod : Modalized p φ) (f : _root_.Realization ℕ L)
    {ψ ψ' : FirstOrder.Sentence L}
    (hfix : U ⊢ ψ 🡘 φ.interpret (f.update p ψ) 𝔅)
    (hfix' : U ⊢ ψ' 🡘 φ.interpret (f.update p ψ') 𝔅) :
    U ⊢ ψ 🡘 ψ' := by
  have h₁ : U ⊢ pIff ψ (φ.interpret (f.update p ψ) 𝔅) := by cl_prover [hfix]
  have h₂ : U ⊢ pIff ψ' (φ.interpret (f.update p ψ') 𝔅) := by cl_prover [hfix']
  suffices h : U ⊢ pIff ψ ψ' by cl_prover [h]
  -- Name the two fixed points by fresh atoms, and read the internal Theorem 4.3
  -- through the realization that sends them to `ψ` and `ψ'`.
  set q : ℕ := φ.atoms.sup id + p + 1 with hqdef
  set q' : ℕ := φ.atoms.sup id + p + 2 with hq'def
  have hq : q ∉ φ.atoms := notMem_atoms_of_sup_lt (by omega)
  have hq' : q' ∉ φ.atoms := notMem_atoms_of_sup_lt (by omega)
  have hpq : q ≠ p := by omega
  have hpq' : q' ≠ p := by omega
  have hqq' : q ≠ q' := by omega
  set g : _root_.Realization ℕ L := (f.update q ψ).update q' ψ' with hgdef
  have hgq : (_root_.Formula.atom q).interpret g 𝔅 = ψ := by
    simp [hgdef, _root_.Realization.update, hqq']
  have hgq' : (_root_.Formula.atom q').interpret g 𝔅 = ψ' := by
    simp [hgdef, _root_.Realization.update]
  have key (χ : _root_.Formula ℕ) (σ : FirstOrder.Sentence L)
      (hχ : χ.interpret g 𝔅 = σ) :
      (φ⟦diag p χ⟧).interpret g 𝔅 = φ.interpret (f.update p σ) 𝔅 := by
    rw [interpret_subst_diag, hχ]
    refine _root_.Formula.interpret_congr_atoms fun a ha => ?_
    by_cases hap : a = p
    · simp [hap, _root_.Realization.update]
    · have hne : a ≠ q := fun h => hq (h ▸ ha)
      have hne' : a ≠ q' := fun h => hq' (h ▸ ha)
      simp [hap, hne, hne', hgdef, _root_.Realization.update]
  have hA := key (.atom q) ψ hgq
  have hA' := key (.atom q') ψ' hgq'
  have hsound : U ⊢ ((⊡((_root_.Formula.atom q) 🡘 φ⟦diag p (.atom q)⟧) ⋏
        ⊡((_root_.Formula.atom q') 🡘 φ⟦diag p (.atom q')⟧)) 🡒
        ((_root_.Formula.atom q) 🡘 (_root_.Formula.atom q'))).interpret g 𝔅 :=
    LogicGL.arithmetical_soundness' (f := g)
      (glFixedPoint_uniqueness_internal hmod (.atom q) (.atom q'))
  rw [interpret_imp, interpret_and, interpret_boxdot, interpret_boxdot,
    interpret_iff, interpret_iff, interpret_iff, hgq, hgq', hA, hA'] at hsound
  have hb₁ : U ⊢ 𝔅 (pIff ψ (φ.interpret (f.update p ψ) 𝔅)) :=
    Entailment.WeakerThan.pbl (𝔅.D1 h₁)
  have hb₂ : U ⊢ 𝔅 (pIff ψ' (φ.interpret (f.update p ψ') 𝔅)) :=
    Entailment.WeakerThan.pbl (𝔅.D1 h₂)
  have hand : ∀ a b : FirstOrder.Sentence L, U ⊢ a → U ⊢ b → U ⊢ pAnd a b := by
    intro a b ha hb; cl_prover [ha, hb]
  exact hsound ⨀ hand _ _ (hand _ _ h₁ hb₁) (hand _ _ h₂ hb₂)

end ArithmeticUniqueness

/-! ## Arithmetical lift (Barasz, §4, Thm 4.1) -/

open FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction in
/-- Lift GL-provable cooperation through an arithmetical realization: the outcome
formula, read as an arithmetic sentence by `Formula.interpret` with `□` sent to the
provability predicate `𝔅`, is a theorem of `U`. The realization and the interpretation
are the `ProvabilityLogic` package's own, applied directly to `outcome X Y`.

Paper node: Theorem 4.1 (§4). -/
theorem Cooperates.arithmeticLift {X Y : ModalAgent} (h : Cooperates X Y)
    {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
    {T U : FirstOrder.Theory L} [Diagonalization T]
    [T ⪯ U] {𝔅 : Provability T U} [𝔅.HBL]
    {f : _root_.Realization ℕ L} :
    U ⊢ (outcome X Y).interpret f 𝔅 :=
  LogicGL.arithmetical_soundness' h

open FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction in
/-- Lift GL-provable *defection* through an arithmetical realization, by the same
soundness theorem. This is the payoff of stating defection as `ProvablyDefects` rather
than `Defects`: a negative claim that `GL` actually proves is still a `GL` theorem, so
it lifts, whereas `Defects` — a metatheoretic non-provability — has no counterpart
here and could not have one.

Paper node: Theorem 4.1 (§4). -/
theorem ProvablyDefects.arithmeticLift {X Y : ModalAgent} (h : ProvablyDefects X Y)
    {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
    {T U : FirstOrder.Theory L} [Diagonalization T]
    [T ⪯ U] {𝔅 : Provability T U} [𝔅.HBL]
    {f : _root_.Realization ℕ L} :
    U ⊢ (∼(outcome X Y)).interpret f 𝔅 :=
  LogicGL.arithmetical_soundness' h

open FFL.FirstOrder in
/-- Example: the GL proof that FairBot cooperates with itself lifts to PA under any
realization, read through PA's standard provability predicate. -/
example (f : _root_.Realization ℕ ℒₒᵣ) : 𝗣𝗔 ⊢ f 𝗣𝗔 (outcome fairBot fairBot) :=
  Cooperates.arithmeticLift fairBot_vs_fairBot

open FFL.FirstOrder in
/-- Example: DefectBot's defection lifts to PA at the paper's strength — `PA` proves
the outcome formula false, not merely that it is unprovable. -/
example (Y : ModalAgent) (f : _root_.Realization ℕ ℒₒᵣ) : 𝗣𝗔 ⊢ f 𝗣𝗔 (∼(outcome defectBot Y)) :=
  ProvablyDefects.arithmeticLift (defectBot_provably_defects Y)
