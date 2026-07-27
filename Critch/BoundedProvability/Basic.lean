/-
  Bounded provability abstractions for Critch 2019, Definition 1.

  This file will contain the bounded provability predicate and bounded HBL
  assumptions used in the abstract proof of Theorems 1 and 2.
-/

import Critch.BoundedProvability.Asymp
import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic
import Foundation.FirstOrder.Incompleteness.RestrictedProvability
import Mathlib.Tactic.Ring

namespace LO

open LO.Entailment

namespace FirstOrder
namespace Critch

variable {L₀ L : Language}

/--
Bounded provability predicate family.

This mirrors Foundation's `Provability` structure, with the box indexed by a
meta-level proof bound. The `bew_def` field is the bounded D1 direction used to
turn an ordinary proof into some bounded proof.
-/
structure BoundedProvability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  bprov : Nat → Semisentence L₀ 1
  /-- Bounded D1: a proof in `T` has some bounded proof predicate in `T₀`. -/
  bew_def {σ : Sentence L} : T ⊢ σ → ∃ k, T₀ ⊢ (bprov k)/[⌜σ⌝]

namespace BoundedProvability

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

/-- Apply a bounded provability predicate at bound `k` to a sentence. -/
@[coe] def pr (𝔅 : BoundedProvability T₀ T) (k : Nat) (σ : Sentence L) :
    Sentence L₀ :=
  (𝔅.bprov k)/[⌜σ⌝]

/-- Coerce `𝔅` to its two-argument bounded-box operation. -/
instance : CoeFun (BoundedProvability T₀ T) (fun _ ↦ Nat → Sentence L → Sentence L₀) :=
  ⟨pr⟩

/-- Notation for the bounded box at meta-level bound `k`. -/
notation:90 𝔅 "[" k "]" σ => BoundedProvability.pr 𝔅 k σ

/-- Bounded D1 from the `BoundedProvability` structure. -/
lemma D1 {𝔅 : BoundedProvability T₀ T} {σ : Sentence L} :
    T ⊢ σ → ∃ k, T₀ ⊢ 𝔅 k σ :=
  𝔅.bew_def

/--
Critch §4, Property 1: bounded implication distribution.

The bound arithmetic is meta-level arithmetic on the indices of the bounded box.
-/
class BImpDistr (𝔅 : BoundedProvability T₀ T) where
  c : Nat
  impDistr {a b : Nat} {σ τ : Sentence L} :
    T₀ ⊢ 𝔅 a (σ 🡒 τ) 🡒 𝔅 b σ 🡒 𝔅 (a + b + c) τ

export BImpDistr (c impDistr)

/--
Critch §4, Property 2: bounded quantifier distribution.

The premise and conclusion are meta-level implications between provability
claims. The object-level universal is specialized at the meta-natural `k`, and
the resulting bound is computed externally as `C + 2 * N + lg k`.
-/
class BQuantDistr [L.Zero] [L.One] [L.Add] (𝔅 : BoundedProvability T₀ T) where
  C : Nat
  quantDistr {N k : Nat} {φ : Semisentence L 1} :
    T₀ ⊢ 𝔅 N (∀⁰ φ : Sentence L) →
      T₀ ⊢ 𝔅 (C + 2 * N + lg k) (φ/[.numeral k] : Sentence L)

export BQuantDistr (C quantDistr)

variable [L.ReferenceableBy L] {T₀ T : Theory L}

/--
Critch §4, Property 3: bounded necessitation.

The threshold is existential, matching the paper's use of a formula-dependent
proof bound without exposing a global proof-length oracle.
-/
class BNec (𝔅 : BoundedProvability T₀ T) where
  nec {σ : Sentence L} : T₀ ⊢ σ → ∃ k₀, ∀ k, k₀ ≤ k → T₀ ⊢ 𝔅 k σ

export BNec (nec)

/--
Critch §4, Property 4: bounded inner necessitation.

The field `expand` is Critch's proof-expansion function.
-/
class BInnerNec (𝔅 : BoundedProvability T₀ T) where
  expand : Nat → Nat
  innerNec {k : Nat} {σ : Sentence L} : T₀ ⊢ 𝔅 k σ 🡒 𝔅 (expand k) (𝔅 k σ)

export BInnerNec (expand innerNec)

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

/--
Bound monotonicity for bounded provability.

Critch uses this implicitly when replacing a bounded proof claim by the same
claim at a larger bound.
-/
class BMono (𝔅 : BoundedProvability T₀ T) where
  mono {a b : Nat} (h : a ≤ b) {σ : Sentence L} : T₀ ⊢ 𝔅 a σ 🡒 𝔅 b σ

export BMono (mono)

variable [L.ReferenceableBy L] [L.Zero] [L.One] [L.Add] {T₀ T : Theory L}

/--
Convenience bundle for the bounded derivability assumptions used in Critch §4.

The separate classes above remain the primary interface; this bundle is only for
theorems that need the full collection.
-/
class BHBL (𝔅 : BoundedProvability T₀ T) extends
    𝔅.BImpDistr, 𝔅.BQuantDistr, 𝔅.BNec, 𝔅.BInnerNec, 𝔅.BMono

end BoundedProvability

/-!
### Phase 0 probe: the internal-bound box (`bewBounded`)

Paper: Critch 2019, §3.1. The paper's `BBew[m, n, k] ∈ L_S(3)` says "`m` codes a proof of
the statement coded by `n`, and that proof uses at most `k` characters"; the bounded box is
`□ₖ(φ) := (∃m)(BBew[m, ⌜φ⌝, k])` with the bound `k` a *closed expression* — in particular
possibly a free object-level variable. Foundation's `Theory.RestrictedProvable` is the
meta-level-bound analogue (`e : ℕ` fixed outside the formula); the definitions below make
the bound an object-level variable, which is what the parametric diagonal argument needs.

**Size measure (standing scope decision 1 — a type-(c) modeling substitution).** The
paper measures proofs in "characters of written proof, with abbreviations". We substitute
the measure native to Foundation's arithmetized proofs: a proof `d` (a Gödel code of a
derivation) is *within bound `a`* iff `d < 2 ^ a` — i.e. the bound is on the *bit-length*
of the derivation code. This is exactly the measure of `Theory.RestrictedProvable`
(`∃ d < Exp.exp (numeral e), T.Proof d φ`), with `numeral e` generalized to a variable.
Chosen because (i) it is the measure Foundation already commits to, (ii) `Exp.exp` is
total and Σ₁-definable in `𝗜𝚺₁`, so the box stays Σ₁ with the bound free, and (iii) it
supports a provable — though *not additive* — combination algebra: `BewBounded.cut` below
shows the cost of combining two proofs is `2048 · (max bit-length) + O(1)`, the factor
`2048 = 2^11` coming from the 11 nested Cantor pairings of the 5-node derivation glue.
An additive algebra (paper Property 1's `a + b + c`) requires a node-count measure
(roadmap Phase 0 bullet 2, still open).
-/

section internalBox

open Arithmetic PeanoMinus ISigma0 ISigma1 Bootstrapping

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]
variable [L.Encodable] [L.LORDefinable]
variable (T : Theory L) [T.Δ₁]

/--
Meta-level (model-side) bounded provability with an object-level bound:
`BewBounded T a φ` iff some `T`-proof `d` of the formula coded by `φ` has `d < 2 ^ a`,
i.e. the derivation code's bit-length is at most `a`.

Paper correspondence: §3.1, the predicate `(∃m) BBew[m, n, k]` defining `□ₖ`, with
`n, k` object-level. Generalizes `Theory.RestrictedProvable`, whose bound is meta-level
(see `bewBounded_numeral_iff_restrictedProvable`).

Provenance: `Def`; measure choice is the type-(c) substitution documented in the section
header.
-/
def BewBounded (a φ : V) : Prop := ∃ d < Exp.exp a, T.Proof d φ

/--
The internal-bound box as a Σ₁ semisentence: variable 0 is the size bound, variable 1 the
formula code. `(bewBounded T).val/[k, ⌜σ⌝]` is the paper's `□ₖ(σ)` (§3.1) for the
bit-length measure.

TODO(pbl:phase-A): upgrade to `𝚫₁.Semisentence 2` (add the Π side, mirroring
`Theory.restrictedProvable`) and add the 3-ary `BBew` form if Phase A needs it.
-/
noncomputable def bewBounded : 𝚺₁.Semisentence 2 := .mkSigma
  “a φ. ∃ E, !expDef E a ∧ ∃ d < E, !T.proof.sigma d φ”

instance BewBounded.defined : 𝚺₁-Relation[V] (BewBounded T) via (bewBounded T) :=
  .mk fun v ↦ by simp [bewBounded, BewBounded]

instance BewBounded.definable : 𝚺₁-Relation[V] (BewBounded T) :=
  (BewBounded.defined T).to_definable

/-- Sanity bridge: at a standard numeral bound, the internal-bound box is definitionally
Foundation's meta-level `RestrictedProvable`. -/
lemma bewBounded_numeral_iff_restrictedProvable (e : ℕ) (φ : V) :
    BewBounded T (ORingStructure.numeral e : V) φ ↔ T.RestrictedProvable e φ :=
  Iff.rfl

/-- Bound monotonicity of the box (the paper uses this silently). -/
lemma BewBounded.mono {a b : V} (h : a ≤ b) {φ : V} :
    BewBounded T a φ → BewBounded T b φ := by
  rintro ⟨d, hd, hp⟩
  exact ⟨d, lt_of_lt_of_le hd (exp_monotone_le.mpr h), hp⟩

/-! #### Size algebra for the bit-length measure

Private helpers bounding Cantor-pair combinations under `Exp.exp`. Each pairing at
bit-level `u` lands within bit-level `2u + 2`; this factor-2-per-pairing is the precise
content of the roadmap's "pairing blowup breaks the additive bound algebra". -/

private lemma le_of_add_eq {u w v : V} (h : u + w = v) : u ≤ v := h ▸ le_self_add

private lemma le_exp_of_le {x u v : V} (hx : x ≤ Exp.exp u) (h : u ≤ v) :
    x ≤ Exp.exp v := le_trans hx (exp_monotone_le.mpr h)

private lemma le_exp_bump {x u : V} (w : V) {v : V} (hx : x ≤ Exp.exp u)
    (h : u + w = v) : x ≤ Exp.exp v := le_exp_of_le hx (le_of_add_eq h)

private lemma le_exp_congr {x u v : V} (hx : x ≤ Exp.exp u) (h : u = v) :
    x ≤ Exp.exp v := h ▸ hx

private lemma exp_add' (x y : V) : Exp.exp (x + y) = Exp.exp x * Exp.exp y :=
  exp_of_exponential ((exponential_exp x).add_mul (exponential_exp y))

private lemma add_exp_le {x y u : V} (hx : x ≤ Exp.exp u) (hy : y ≤ Exp.exp u) :
    x + y ≤ Exp.exp (u + 1) := by
  rw [exp_succ, two_mul]
  exact add_le_add hx hy

private lemma succ_le_exp {x u : V} (hx : x ≤ Exp.exp u) : x + 1 ≤ Exp.exp (u + 1) :=
  add_exp_le hx (one_le_exp u)

private lemma exp_two' : Exp.exp (2 : V) = 4 := by
  rw [show (2 : V) = 1 + 1 by norm_num, exp_succ, exp_one]; norm_num

private lemma exp_three' : Exp.exp (3 : V) = 8 := by
  rw [show (3 : V) = 2 + 1 by norm_num, exp_succ, exp_two']; norm_num

private lemma pair_le_exp {x y u : V} (hx : x ≤ Exp.exp u) (hy : y ≤ Exp.exp u) :
    ⟪x, y⟫ ≤ Exp.exp (2 * u + 2) := by
  have e : Exp.exp (2 * u + 2) =
      (Exp.exp u * Exp.exp u + Exp.exp u * Exp.exp u)
        + (Exp.exp u * Exp.exp u + Exp.exp u * Exp.exp u) := by
    rw [show (2 * u + 2 : V) = (u + u + 1) + 1 by ring, exp_succ, exp_succ, exp_add']
    ring
  have hxx : x ≤ Exp.exp u * Exp.exp u :=
    le_trans hx (le_mul_of_one_le_right (zero_le _) (one_le_exp u))
  have hyy : y ≤ Exp.exp u * Exp.exp u :=
    le_trans hy (le_mul_of_one_le_right (zero_le _) (one_le_exp u))
  rw [e]
  simp only [pair]
  split_ifs
  · exact le_trans
      (add_le_add (mul_le_mul hy hy (zero_le _) (zero_le _)) hxx) le_self_add
  · calc x * x + x + y
        ≤ (Exp.exp u * Exp.exp u + Exp.exp u * Exp.exp u) + (Exp.exp u * Exp.exp u) :=
          add_le_add (add_le_add (mul_le_mul hx hx (zero_le _) (zero_le _)) hxx) hyy
      _ ≤ _ := add_le_add le_rfl le_self_add

private lemma insert_le_add_exp (i s : V) : insert i s ≤ s + Exp.exp i := by
  rw [insert_eq, bitInsert]
  split_ifs
  · exact le_self_add
  · exact le_rfl

private lemma nat_cast_le_of_le {m n : ℕ} (h : m ≤ n) : ((m : ℕ) : V) ≤ ((n : ℕ) : V) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  push_cast
  exact le_self_add

/-! #### Quote commutation helpers (untyped codes of sentences) -/

private lemma quote_neg_sentence (φ : Sentence L) :
    (⌜(∼φ : Sentence L)⌝ : V) = Bootstrapping.neg L ⌜φ⌝ := by
  simp [Sentence.quote_eq]

private lemma quote_and_sentence (φ ψ : Sentence L) :
    (⌜(φ ⋏ ψ : Sentence L)⌝ : V) = (⌜φ⌝ : V) ^⋏ (⌜ψ⌝ : V) := by
  simp [Sentence.quote_eq]

private lemma quote_or_sentence (φ ψ : Sentence L) :
    (⌜(φ ⋎ ψ : Sentence L)⌝ : V) = (⌜φ⌝ : V) ^⋎ (⌜ψ⌝ : V) := by
  simp [Sentence.quote_eq]

/-! #### Toy bounded lemma (Phase 0 deliverable B) -/

/--
**Bounded cut for the internal-bound box** (the semantic core of the paper's Property 1,
Implication Distribution, §3.2 — meta-level shadow, not the internal `T₀`-provable form).

From an internal proof `d₁` of the disjunction `np ⋎ q` (the code of an implication
`¬np → q`) and an internal proof `d₂` of `¬np`, both of bit-length ≤ `P`, we *construct*
the 5-node derivation
`cut (wk d₁) (andIntro (wk d₂) axL)` proving `q`, and bound its code:
its bit-length is at most `2048·P + 10768`.

The two extra hypotheses bound the codes of `¬q` and of the conjunction `¬np ⋏ ¬q`
(the cut's auxiliary formulas) by `P`; they are *not* derivable from `d₁, d₂` because
`Bootstrapping.neg` can move a code arbitrarily. In the quoted instantiation
(`BewBounded.mp_meta`) they are standard-numeral constants.

**Probe finding (measure algebra).** The factor `2048 = 2^11` is exact bookkeeping: the
constructed derivation glue nests 11 Cantor pairings, and each pairing at bit-level `u`
lands at bit-level `2u + 2`. So the bit-length measure supports a *linear* combination
algebra `(P ↦ 2048·P + O(1))`, not the paper's *additive* one (`a + b + c`); standing
decision 1's planned node-count measure is what additivity requires.

Provenance: kind `P` (proved, constructive witness). Hypotheses: `h₁ h₂` internal proof
predicates (a); size bounds (a). No axioms beyond Foundation.
-/
lemma BewBounded.cut {np q d₁ d₂ P : V}
    (h₁ : T.Proof d₁ (np ^⋎ q)) (h₂ : T.Proof d₂ (Bootstrapping.neg L np))
    (hd₁ : d₁ ≤ Exp.exp P) (hd₂ : d₂ ≤ Exp.exp P)
    (hnq : Bootstrapping.neg L q ≤ P)
    (handF : Bootstrapping.neg L np ^⋏ Bootstrapping.neg L q ≤ P) :
    BewBounded T (2048 * P + 10768) q := by
  have h₁' : T.DerivationOf d₁ {np ^⋎ q} := h₁
  have h₂' : T.DerivationOf d₂ {Bootstrapping.neg L np} := h₂
  -- formula-hood
  have hor : IsFormula L (np ^⋎ q) := by simpa using h₁'.isFormulaSet
  have hnpq : IsFormula L np ∧ IsFormula L q := by simpa using hor
  have hnp_f : IsFormula L np := hnpq.1
  have hq_f : IsFormula L q := hnpq.2
  have hnnp_f : IsFormula L (Bootstrapping.neg L np) := hnp_f.neg
  have hnq_f : IsFormula L (Bootstrapping.neg L q) := hq_f.neg
  -- the derivation tree
  set sN : V := insert (Bootstrapping.neg L np ^⋏ Bootstrapping.neg L q) ({q} : V)
    with hsN_def
  set dq : V := Bootstrapping.axL (insert (Bootstrapping.neg L q) sN) q with hdq_def
  set dp : V := Bootstrapping.wkRule (insert (Bootstrapping.neg L np) sN) d₂ with hdp_def
  set dnA : V := Bootstrapping.andIntro sN (Bootstrapping.neg L np)
    (Bootstrapping.neg L q) dp dq with hdnA_def
  set dA : V := Bootstrapping.wkRule (insert (np ^⋎ q) ({q} : V)) d₁ with hdA_def
  set d₃ : V := Bootstrapping.cutRule ({q} : V) (np ^⋎ q) dA dnA with hd₃_def
  -- validity
  have hDdq : T.DerivationOf dq (insert (Bootstrapping.neg L q) sN) := by
    refine ⟨by rw [hdq_def]; exact fstIdx_axL _ _, ?_⟩
    rw [hdq_def]
    exact Theory.Derivation.axL (by simp [hsN_def, hnq_f, hnnp_f, hq_f])
      (by simp [hsN_def]) (by simp)
  have hDdp : T.DerivationOf dp (insert (Bootstrapping.neg L np) sN) := by
    refine ⟨by rw [hdp_def]; exact fstIdx_wkRule _ _, ?_⟩
    rw [hdp_def]
    exact Theory.Derivation.wkRule (by simp [hsN_def, hnnp_f, hnq_f, hq_f])
      (by intro x hx; rcases mem_singleton_iff.mp hx with rfl; simp) h₂'
  have hDdnA : T.DerivationOf dnA sN := by
    refine ⟨by rw [hdnA_def]; exact fstIdx_andIntro _ _ _ _ _, ?_⟩
    rw [hdnA_def]
    exact Theory.Derivation.andIntro (by simp [hsN_def]) hDdp hDdq
  have hDdA : T.DerivationOf dA (insert (np ^⋎ q) ({q} : V)) := by
    refine ⟨by rw [hdA_def]; exact fstIdx_wkRule _ _, ?_⟩
    rw [hdA_def]
    exact Theory.Derivation.wkRule (by simp [hor, hq_f])
      (by intro x hx; rcases mem_singleton_iff.mp hx with rfl; simp) h₁'
  have hnegA : Bootstrapping.neg L (np ^⋎ q)
      = Bootstrapping.neg L np ^⋏ Bootstrapping.neg L q :=
    neg_or hnp_f.isUFormula hq_f.isUFormula
  have hproof : T.Proof d₃ q := by
    refine ⟨by rw [hd₃_def]; exact fstIdx_cutRule _ _ _ _, ?_⟩
    rw [hd₃_def]
    exact Theory.Derivation.cutRule hDdA (by rw [hnegA, ← hsN_def]; exact hDdnA)
  -- sizes of the formula codes involved
  have hA_le : np ^⋎ q ≤ P := by
    have h1 : Exp.exp (np ^⋎ q) ≤ d₁ := by
      calc Exp.exp (np ^⋎ q) = ({np ^⋎ q} : V) := (singleton_def _).symm
        _ = fstIdx d₁ := h₁'.1.symm
        _ ≤ d₁ := fstIdx_le_self d₁
    exact exp_monotone_le.mp (le_trans h1 hd₁)
  have hnnp_le : Bootstrapping.neg L np ≤ P := by
    have h1 : Exp.exp (Bootstrapping.neg L np) ≤ d₂ := by
      calc Exp.exp (Bootstrapping.neg L np)
          = ({Bootstrapping.neg L np} : V) := (singleton_def _).symm
        _ = fstIdx d₂ := h₂'.1.symm
        _ ≤ d₂ := fstIdx_le_self d₂
    exact exp_monotone_le.mp (le_trans h1 hd₂)
  have hq_le : q ≤ P := by
    refine le_trans ?_ hA_le
    calc q ≤ ⟪np, q⟫ := le_pair_right np q
      _ ≤ ⟪(5 : V), np, q⟫ := le_pair_right _ _
      _ ≤ ⟪(5 : V), np, q⟫ + 1 := le_self_add
  -- sizes of the sequents
  have hs₀_le : ({q} : V) ≤ Exp.exp P := by
    rw [singleton_def]; exact exp_monotone_le.mpr hq_le
  have hsN_le : sN ≤ Exp.exp (P + 1) := by
    rw [hsN_def]
    exact le_trans (insert_le_add_exp _ _)
      (add_exp_le hs₀_le (exp_monotone_le.mpr handF))
  have hs₁_le : insert (Bootstrapping.neg L np) sN ≤ Exp.exp (P + 2) :=
    le_exp_congr (le_trans (insert_le_add_exp _ _)
      (add_exp_le hsN_le (le_exp_of_le (exp_monotone_le.mpr hnnp_le) le_self_add)))
      (by ring)
  have hs₂_le : insert (Bootstrapping.neg L q) sN ≤ Exp.exp (P + 2) :=
    le_exp_congr (le_trans (insert_le_add_exp _ _)
      (add_exp_le hsN_le (le_exp_of_le (exp_monotone_le.mpr hnq) le_self_add)))
      (by ring)
  have hsA_le : insert (np ^⋎ q) ({q} : V) ≤ Exp.exp (P + 1) :=
    le_trans (insert_le_add_exp _ _) (add_exp_le hs₀_le (exp_monotone_le.mpr hA_le))
  -- everything at the uniform base bit-level `P + 3`
  have atomE : ∀ x : V, x ≤ P → x ≤ Exp.exp (P + 3) := fun x hx =>
    le_exp_of_le (le_trans hx (le_of_lt (lt_exp P))) le_self_add
  have hq_E := atomE q hq_le
  have hnnp_E := atomE _ hnnp_le
  have hnq_E := atomE _ hnq
  have hA_E := atomE _ hA_le
  have hd₁_E : d₁ ≤ Exp.exp (P + 3) := le_exp_of_le hd₁ le_self_add
  have hd₂_E : d₂ ≤ Exp.exp (P + 3) := le_exp_of_le hd₂ le_self_add
  have h0_E : (0 : V) ≤ Exp.exp (P + 3) := zero_le _
  have h2_E : (2 : V) ≤ Exp.exp (P + 3) := by
    calc (2 : V) = Exp.exp (1 : V) := exp_one.symm
      _ ≤ _ := exp_monotone_le.mpr (le_of_add_eq (u := 1) (w := P + 2) (by ring))
  have h8_E : (8 : V) ≤ Exp.exp (P + 3) := by
    calc (8 : V) = Exp.exp (3 : V) := exp_three'.symm
      _ ≤ _ := exp_monotone_le.mpr (le_of_add_eq (u := 3) (w := P) (by ring))
  have h6_E : (6 : V) ≤ Exp.exp (P + 3) :=
    le_trans (le_of_add_eq (by norm_num : (6 : V) + 2 = 8)) h8_E
  have hs₀_E : ({q} : V) ≤ Exp.exp (P + 3) := le_exp_of_le hs₀_le le_self_add
  have hsN_E : sN ≤ Exp.exp (P + 3) := le_exp_of_le hsN_le (le_of_add_eq (w := 2) (by ring))
  have hs₁_E : insert (Bootstrapping.neg L np) sN ≤ Exp.exp (P + 3) :=
    le_exp_of_le hs₁_le (le_of_add_eq (w := 1) (by ring))
  have hs₂_E : insert (Bootstrapping.neg L q) sN ≤ Exp.exp (P + 3) :=
    le_exp_of_le hs₂_le (le_of_add_eq (w := 1) (by ring))
  have hsA_E : insert (np ^⋎ q) ({q} : V) ≤ Exp.exp (P + 3) :=
    le_exp_of_le hsA_le (le_of_add_eq (w := 2) (by ring))
  -- node bounds: each pairing doubles the bit-level (+2); leaves land at 4P+19,
  -- the andIntro node at 128P+671, the cut node at 2048P+10767
  have hdq_le : dq ≤ Exp.exp (4 * P + 19) := by
    have i1 : ⟪(0 : V), q⟫ ≤ Exp.exp (2 * P + 8) :=
      le_exp_congr (pair_le_exp h0_E hq_E) (by ring)
    have i2 : insert (Bootstrapping.neg L q) sN ≤ Exp.exp (2 * P + 8) :=
      le_exp_bump (P + 5) hs₂_E (by ring)
    have i3 : ⟪insert (Bootstrapping.neg L q) sN, ⟪(0 : V), q⟫⟫ ≤ Exp.exp (4 * P + 18) :=
      le_exp_congr (pair_le_exp i2 i1) (by ring)
    have i4 : ⟪insert (Bootstrapping.neg L q) sN, ⟪(0 : V), q⟫⟫ + 1
        ≤ Exp.exp (4 * P + 19) := le_exp_congr (succ_le_exp i3) (by ring)
    rw [hdq_def]
    simp only [Bootstrapping.axL]
    exact i4
  have hdp_le : dp ≤ Exp.exp (4 * P + 19) := by
    have i1 : ⟪(6 : V), d₂⟫ ≤ Exp.exp (2 * P + 8) :=
      le_exp_congr (pair_le_exp h6_E hd₂_E) (by ring)
    have i2 : insert (Bootstrapping.neg L np) sN ≤ Exp.exp (2 * P + 8) :=
      le_exp_bump (P + 5) hs₁_E (by ring)
    have i3 : ⟪insert (Bootstrapping.neg L np) sN, ⟪(6 : V), d₂⟫⟫ ≤ Exp.exp (4 * P + 18) :=
      le_exp_congr (pair_le_exp i2 i1) (by ring)
    have i4 : ⟪insert (Bootstrapping.neg L np) sN, ⟪(6 : V), d₂⟫⟫ + 1
        ≤ Exp.exp (4 * P + 19) := le_exp_congr (succ_le_exp i3) (by ring)
    rw [hdp_def]
    simp only [Bootstrapping.wkRule]
    exact i4
  have hdA_le : dA ≤ Exp.exp (4 * P + 19) := by
    have i1 : ⟪(6 : V), d₁⟫ ≤ Exp.exp (2 * P + 8) :=
      le_exp_congr (pair_le_exp h6_E hd₁_E) (by ring)
    have i2 : insert (np ^⋎ q) ({q} : V) ≤ Exp.exp (2 * P + 8) :=
      le_exp_bump (P + 5) hsA_E (by ring)
    have i3 : ⟪insert (np ^⋎ q) ({q} : V), ⟪(6 : V), d₁⟫⟫ ≤ Exp.exp (4 * P + 18) :=
      le_exp_congr (pair_le_exp i2 i1) (by ring)
    have i4 : ⟪insert (np ^⋎ q) ({q} : V), ⟪(6 : V), d₁⟫⟫ + 1
        ≤ Exp.exp (4 * P + 19) := le_exp_congr (succ_le_exp i3) (by ring)
    rw [hdA_def]
    simp only [Bootstrapping.wkRule]
    exact i4
  have hdnA_le : dnA ≤ Exp.exp (128 * P + 671) := by
    have j1 : ⟪dp, dq⟫ ≤ Exp.exp (8 * P + 40) :=
      le_exp_congr (pair_le_exp hdp_le hdq_le) (by ring)
    have j1' : Bootstrapping.neg L q ≤ Exp.exp (8 * P + 40) :=
      le_exp_bump (7 * P + 37) hnq_E (by ring)
    have j2 : ⟪Bootstrapping.neg L q, ⟪dp, dq⟫⟫ ≤ Exp.exp (16 * P + 82) :=
      le_exp_congr (pair_le_exp j1' j1) (by ring)
    have j2' : Bootstrapping.neg L np ≤ Exp.exp (16 * P + 82) :=
      le_exp_bump (15 * P + 79) hnnp_E (by ring)
    have j3 : ⟪Bootstrapping.neg L np, Bootstrapping.neg L q, dp, dq⟫
        ≤ Exp.exp (32 * P + 166) := le_exp_congr (pair_le_exp j2' j2) (by ring)
    have j3' : (2 : V) ≤ Exp.exp (32 * P + 166) :=
      le_exp_bump (31 * P + 163) h2_E (by ring)
    have j4 : ⟪(2 : V), Bootstrapping.neg L np, Bootstrapping.neg L q, dp, dq⟫
        ≤ Exp.exp (64 * P + 334) := le_exp_congr (pair_le_exp j3' j3) (by ring)
    have j4' : sN ≤ Exp.exp (64 * P + 334) :=
      le_exp_bump (63 * P + 331) hsN_E (by ring)
    have j5 : ⟪sN, (2 : V), Bootstrapping.neg L np, Bootstrapping.neg L q, dp, dq⟫
        ≤ Exp.exp (128 * P + 670) := le_exp_congr (pair_le_exp j4' j4) (by ring)
    have j6 : ⟪sN, (2 : V), Bootstrapping.neg L np, Bootstrapping.neg L q, dp, dq⟫ + 1
        ≤ Exp.exp (128 * P + 671) := le_exp_congr (succ_le_exp j5) (by ring)
    rw [hdnA_def]
    simp only [Bootstrapping.andIntro]
    exact j6
  have hd₃_le : d₃ ≤ Exp.exp (2048 * P + 10767) := by
    have c1' : dA ≤ Exp.exp (128 * P + 671) :=
      le_exp_bump (124 * P + 652) hdA_le (by ring)
    have c1 : ⟪dA, dnA⟫ ≤ Exp.exp (256 * P + 1344) :=
      le_exp_congr (pair_le_exp c1' hdnA_le) (by ring)
    have c2' : np ^⋎ q ≤ Exp.exp (256 * P + 1344) :=
      le_exp_bump (255 * P + 1341) hA_E (by ring)
    have c2 : ⟪np ^⋎ q, dA, dnA⟫ ≤ Exp.exp (512 * P + 2690) :=
      le_exp_congr (pair_le_exp c2' c1) (by ring)
    have c3' : (8 : V) ≤ Exp.exp (512 * P + 2690) :=
      le_exp_bump (511 * P + 2687) h8_E (by ring)
    have c3 : ⟪(8 : V), np ^⋎ q, dA, dnA⟫ ≤ Exp.exp (1024 * P + 5382) :=
      le_exp_congr (pair_le_exp c3' c2) (by ring)
    have c4' : ({q} : V) ≤ Exp.exp (1024 * P + 5382) :=
      le_exp_bump (1023 * P + 5379) hs₀_E (by ring)
    have c4 : ⟪({q} : V), (8 : V), np ^⋎ q, dA, dnA⟫ ≤ Exp.exp (2048 * P + 10766) :=
      le_exp_congr (pair_le_exp c4' c3) (by ring)
    have c5 : ⟪({q} : V), (8 : V), np ^⋎ q, dA, dnA⟫ + 1 ≤ Exp.exp (2048 * P + 10767) :=
      le_exp_congr (succ_le_exp c4) (by ring)
    rw [hd₃_def]
    simp only [Bootstrapping.cutRule]
    exact c5
  have hlt : d₃ < Exp.exp (2048 * P + 10768) := by
    have h1 : d₃ < Exp.exp (2048 * P + 10767 + 1) :=
      lt_of_le_of_lt hd₃_le (exp_monotone.mpr (lt_iff_succ_le.mpr le_rfl))
    rwa [show (2048 * P + 10767 + 1 : V) = 2048 * P + 10768 by ring] at h1
  exact ⟨d₃, hlt, hproof⟩

section metaWrapper

variable [L.DecidableEq] {T}

/-- The ℕ-key of the fixed data of `BewBounded.mp_meta`: the codes of the quoted proof of
`σ 🡒 τ` and of the two auxiliary cut formulas. -/
noncomputable def mpMetaKey {σ τ : Sentence L} (b : T ⊢! σ 🡒 τ) : ℕ :=
  (⌜b⌝ : ℕ) + (⌜(∼τ : Sentence L)⌝ : ℕ) + (⌜(σ ⋏ ∼τ : Sentence L)⌝ : ℕ)

/-- The additive constant of `BewBounded.mp_meta` — a first concrete value of the paper's
proof-expansion cost for the bit-length measure, depending only on the fixed proof `b`. -/
noncomputable def mpMetaBound {σ τ : Sentence L} (b : T ⊢! σ 🡒 τ) : ℕ :=
  2048 * mpMetaKey b + 10768

/--
**Toy bounded Mono (Phase 0 deliverable B, roadmap bullet 4).** From a fixed meta-level
proof `b : T ⊢! σ 🡒 τ`, the internal-bound box transfers along the implication:
`□ₐ⌜σ⌝ → □_{2048·a + c}⌜τ⌝` in every model `V ⊧ 𝗜𝚺₁`, with `c = mpMetaBound b` an
explicit standard constant. This is the meta-level shadow of the paper's Property 1
specialized to a fixed implication (§3.2); the internal (`T₀`-provable) form is Phase A.

Note the paper's shape is `□ₐφ → □_{a+c}ψ`; here the coefficient is `2048`, not `1` —
an honest artifact of the bit-length measure (see `BewBounded.cut`).

Provenance: kind `P`; hypothesis `b` meta-level derivation (a); `h` internal box (a);
constants derived in-proof (a). Measure substitution is type-(c), disclosed at
`bewBounded`.
-/
lemma BewBounded.mp_meta {σ τ : Sentence L} (b : T ⊢! σ 🡒 τ) (a : V)
    (h : BewBounded T a ⌜σ⌝) :
    BewBounded T (2048 * a + (mpMetaBound b : V)) ⌜τ⌝ := by
  obtain ⟨d, hd, hpf⟩ := h
  have hAq : (⌜(σ 🡒 τ : Sentence L)⌝ : V)
      = (⌜(∼σ : Sentence L)⌝ : V) ^⋎ (⌜τ⌝ : V) := by
    rw [show (σ 🡒 τ : Sentence L) = ∼σ ⋎ τ from Semiformula.imp_eq σ τ]
    exact quote_or_sentence _ _
  have hnegnp : Bootstrapping.neg L (⌜(∼σ : Sentence L)⌝ : V) = (⌜σ⌝ : V) := by
    rw [← quote_neg_sentence]
    congr 1
    exact Semiformula.neg_neg σ
  have h₁ : T.Proof (⌜b⌝ : V) ((⌜(∼σ : Sentence L)⌝ : V) ^⋎ (⌜τ⌝ : V)) := by
    have := proof_of_quote_proof (V := V) b
    rwa [hAq] at this
  have h₂ : T.Proof d (Bootstrapping.neg L (⌜(∼σ : Sentence L)⌝ : V)) := by
    rw [hnegnp]; exact hpf
  have hkey : ∀ n : ℕ, n ≤ mpMetaKey b → ((n : ℕ) : V) ≤ a + (mpMetaKey b : V) :=
    fun n hn => le_trans (nat_cast_le_of_le hn) le_add_self
  have hd₁ : (⌜b⌝ : V) ≤ Exp.exp (a + (mpMetaKey b : V)) := by
    rw [← coe_quote_proof_eq b]
    exact le_trans (hkey _ (by unfold mpMetaKey; omega)) (le_of_lt (lt_exp _))
  have hd₂ : d ≤ Exp.exp (a + (mpMetaKey b : V)) :=
    le_of_lt (lt_of_lt_of_le hd (exp_monotone_le.mpr le_self_add))
  have hnq : Bootstrapping.neg L (⌜τ⌝ : V) ≤ a + (mpMetaKey b : V) := by
    rw [← quote_neg_sentence, ← Sentence.coe_quote_eq_quote]
    exact hkey _ (by unfold mpMetaKey; omega)
  have handF : Bootstrapping.neg L (⌜(∼σ : Sentence L)⌝ : V)
      ^⋏ Bootstrapping.neg L (⌜τ⌝ : V) ≤ a + (mpMetaKey b : V) := by
    rw [hnegnp, ← quote_neg_sentence, ← quote_and_sentence,
      ← Sentence.coe_quote_eq_quote]
    exact hkey _ (by unfold mpMetaKey; omega)
  have hcut := BewBounded.cut T h₁ h₂ hd₁ hd₂ hnq handF
  rwa [show (2048 * (a + (mpMetaKey b : V)) + 10768 : V)
      = 2048 * a + (mpMetaBound b : V) from by
    unfold mpMetaBound; push_cast; ring] at hcut

end metaWrapper

end internalBox
end Critch
end FirstOrder
end LO
