/-
  Bounded provability interface for Critch 2019 (Phase A, interface-relative).

  The abstract bounded box `□ₖ` of §3.1 — a single two-variable semisentence whose
  bound slot is an object-level term — together with the interface properties the
  parametric bounded Löb proof consumes: Properties 1–2 (§3.2) and Definition 1
  with Properties 3–4 (§4). Nothing here is instantiated yet; grounding these
  classes for Foundation's proof encoding is Phase B (`Critch/Grounding/`).

  Measure abstraction (roadmap standing decision 1): the proof-size measure is
  never fixed here. Meta-level size enters only through `ProofMeasure`, and
  numeral cost only through the abstract `ν` of `BQuantDistr` (standing
  decision 4) — never a concrete `lg`. `lg` lives in `Asymp.lean` for the later
  asymptotic hypotheses.
-/

import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic
import Mathlib.Computability.Partrec

namespace LO

open LO.Entailment

namespace FirstOrder
namespace Critch

variable {L₀ L : Language}

/--
Meta-level bounded-proof judgment `⊢ₖ` for a theory `T`: `Pf k σ` reads "`σ` has a
`T`-proof of size at most `k`" in the (here unspecified) proof-size measure of the
chosen encoding. This is the abstract counterpart of the paper's "`S` proves `φ`
using at most `k` characters"; the measure substitution itself is roadmap standing
decision 1.

`sound`/`complete` say the judgment refines ordinary provability (every bounded
proof is a proof; every proof has some size); `mono` is monotonicity of the
measure, which the paper uses silently.

Paper node: §4 (the `⊢ₖ` judgment of Property 3).
-/
structure ProofMeasure (T : Theory L) where
  Pf : ℕ → Sentence L → Prop
  sound {k : ℕ} {σ : Sentence L} : Pf k σ → T ⊢ σ
  complete {σ : Sentence L} : T ⊢ σ → ∃ k, Pf k σ
  mono {k l : ℕ} {σ : Sentence L} : k ≤ l → Pf k σ → Pf l σ

/--
Bounded provability predicate with an **object-level** bound.

`bbew` is the two-variable semisentence `(∃m)(BBew[m, n, k])` of §3.1: variable `0`
is the size bound `k`, variable `1` the Gödel code `n` of the boxed sentence. The
bound slot accepts arbitrary object-level terms (see `prt`), so the box is a single
syntactic entity — which is what the parametric fixed-point formula of Theorem 1
requires (a meta-indexed family of boxes cannot express it).

`bbew₁` is §3.1's `Eval₁` extension of the box to formulas with one unbound
variable: for `φ ∈ L_S(1)` it is a two-variable semisentence — variable `0` the
bound, variable `1` the unbound argument `ℓ` of `φ` — standing for
`(∃m)(BBew[m, Eval₁(⌜φ⌝, ℓ), k])`. Its defining property (the `Eval₁`
specification) is the class `BEvalSpec`.

This structure is pure syntax: all proof-theoretic content lives in the property
classes below, mirroring how Foundation's `ProvabilityAbstraction` wraps its
1-ary `prov`.

Paper node: §3.1 (`BBew`, `□ₖ`, and the `Eval₁` extension).
-/
structure BoundedProvability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  bbew : Semisentence L₀ 2
  bbew₁ : Semisentence L 1 → Semisentence L₀ 2

namespace BoundedProvability

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

/-- The box `□ₜ(σ)` at an object-level bound term `t` (a "closed expression, such
as a free variable or a constant", §3.1). -/
def prt (𝔅 : BoundedProvability T₀ T) {n : ℕ} (t : Semiterm L₀ Empty n)
    (σ : Sentence L) : Semisentence L₀ n :=
  𝔅.bbew/[t, ⌜σ⌝]

/-- The box `□ₖ(σ)` at a standard numeral bound `k : ℕ`. -/
def pr [L₀.Zero] [L₀.One] [L₀.Add] (𝔅 : BoundedProvability T₀ T) (k : ℕ)
    (σ : Sentence L) : Sentence L₀ :=
  𝔅.prt (Semiterm.numeral k) σ

/--
Property 1 (Implication Distribution): **one** internal theorem with the bound
variables quantified inside the turnstile,

`⊢ (∀a)(∀b)(□ₐ(p → q) → (□_b(p) → □_{a+b+c}(q)))`,

for a fixed standard constant `c` (a `Const(S)`-style numeral). The bound
arithmetic `a + b + c` is object-level addition on the bound variables. The
meta-indexed family of numeral instances is strictly weaker (it cannot feed
Property 2's internally quantified premise), so it is not offered here.

Paper node: §3.2 (Property 1).
-/
class BImpDistr [L₀.Zero] [L₀.One] [L₀.Add] (𝔅 : BoundedProvability T₀ T) where
  c : ℕ
  impDistr (p q : Sentence L) :
    T₀ ⊢ “∀ a b, !𝔅.bbew a ⌜(p 🡒 q)⌝ → !𝔅.bbew b ⌜p⌝ → !𝔅.bbew (a + b + ↑c) ⌜q⌝”

/--
Property 2 (Quantifier Distribution): for `φ ∈ L_S(1)`,

`⊢ □_N((∀k)(φ[k]))  ⇒  ⊢ (∀k)(□_{C+2N+ν(k)}(φ[k]))`,

with `C` a fixed standard constant, `N` the (meta-level) size of the given proof,
and `ν` the **abstract numeral-cost function** of roadmap standing decision 4. The
paper instantiates `ν = lg` (§2.2, binary numerals); baking `lg` into the
interface would make it unsatisfiable for unary numerals, so the interface takes
`ν` abstract and the asymptotic hypotheses relating `ν` to `lg` live downstream
(`Asymp.lean`).

Since `ν(k)` must appear with `k` an object-level variable, it enters through its
graph formula `νGraph` in the paper's own §2.4 abuse-of-notation desugaring:
`□_{C+2N+ν(k)}(…)` officially reads `(∀y)(Γ_ν[k, y] → □_{C+2N+y}(…))`.
`νGraph_spec` is §2.4's representability condition tying `νGraph` to the
(computable) meta-level `ν`.

Paper node: §3.2 (Property 2), with §2.4 (representing computable functions).
-/
class BQuantDistr [L₀.Zero] [L₀.One] [L₀.Add] [L₀.Eq] (𝔅 : BoundedProvability T₀ T) where
  C : ℕ
  ν : ℕ → ℕ
  ν_computable : Computable ν
  νGraph : Semisentence L₀ 2
  νGraph_spec (k : ℕ) : T₀ ⊢ “∀ y, !νGraph ↑k y ↔ y = ↑(ν k)”
  quantDistr {N : ℕ} {φ : Semisentence L 1} :
    T₀ ⊢ 𝔅.pr N (∀⁰ φ : Sentence L) →
    T₀ ⊢ “∀ k y, !νGraph k y → !(𝔅.bbew₁ φ) (↑C + ↑(2 * N) + y) k”

/--
The `Eval₁` specification for the free-variable box `bbew₁`: substituting a
standard numeral for the unbound argument is (provably) the plain box of the
substituted sentence — the internalization of §3.1's
`Eval₁(⌜φ⌝, k) = ⌜φ(°k)⌝`, quantified over the object-level bound.

Paper node: §3.1 (the `Eval₁` specification).
-/
class BEvalSpec [L.Zero] [L.One] [L.Add] [L₀.Zero] [L₀.One] [L₀.Add]
    (𝔅 : BoundedProvability T₀ T) where
  eval_spec (φ : Semisentence L 1) (k : ℕ) :
    T₀ ⊢ “∀ a, !(𝔅.bbew₁ φ) a ↑k ↔ !𝔅.bbew a ⌜(φ/[(.numeral k : Semiterm L Empty 0)] : Sentence L)⌝”

/--
Internal bound monotonicity: `⊢ (∀a)(∀d)(□ₐ(σ) → □_{a+d}(σ))`. Not a numbered
property of the paper, but used silently whenever a bounded claim is weakened to a
larger bound; stated with an explicit additive slack `d` (rather than `≤`) to keep
the language assumptions to `Add`.

Paper node: implicit in §§3–4 (silent bound weakening).
-/
class BMono [L₀.Add] (𝔅 : BoundedProvability T₀ T) where
  mono (σ : Sentence L) :
    T₀ ⊢ “∀ a d, !𝔅.bbew a ⌜σ⌝ → !𝔅.bbew (a + d) ⌜σ⌝”

section sameLanguage

variable [L.ReferenceableBy L] {T₀ T : Theory L}

/--
Definition 1 (proof expansion function) together with the two properties that
define it: **one** computable `e : ℕ → ℕ` satisfying both

* Property 3 (Bounded Necessitation): `⊢ₖ φ  ⇒  ⊢_{e(k)} □ₖ(φ)` — note the
  bounded premise `⊢ₖ` and the `e(k)` bound on the *outer* proof; and
* Property 4 (Bounded Inner Necessitation): `⊢ □ₖ(φ) → □_{e(k)}(□ₖ(φ))`.

The meta-level judgments `⊢ₖ` are supplied by the `ProofMeasure`s `μ` (for `T`,
the premise side) and `μ₀` (for `T₀`, the conclusion side); in the paper both are
the character-count measure of the single system `S`. Keeping Properties 3 and 4
in one class is what makes `e` shared, as Definition 1 requires (Theorem 1
quantifies over that single `e`).

Paper node: §4 (Definition 1; Properties 3–4).
-/
class BExpansion [L.Zero] [L.One] [L.Add] (μ : ProofMeasure T) (μ₀ : ProofMeasure T₀)
    (𝔅 : BoundedProvability T₀ T) where
  e : ℕ → ℕ
  e_computable : Computable e
  nec {k : ℕ} {φ : Sentence L} : μ.Pf k φ → μ₀.Pf (e k) (𝔅.pr k φ)
  innerNec (k : ℕ) (φ : Sentence L) : T₀ ⊢ 𝔅.pr k φ 🡒 𝔅.pr (e k) (𝔅.pr k φ)

/-- Sanity: the interface recovers unbounded D1 — an ordinary `T`-theorem has
*some* bounded box provable in `T₀` (via `ProofMeasure.complete` and Property 3). -/
lemma exists_pr_of_provable [L.Zero] [L.One] [L.Add]
    {μ : ProofMeasure T} {μ₀ : ProofMeasure T₀} {𝔅 : BoundedProvability T₀ T}
    [BExpansion μ μ₀ 𝔅] {σ : Sentence L} (h : T ⊢ σ) :
    ∃ k, T₀ ⊢ 𝔅.pr k σ := by
  obtain ⟨k, hk⟩ := μ.complete h
  exact ⟨k, μ₀.sound (BExpansion.nec hk)⟩

/--
Convenience bundle of the full bounded-HBL interface for the parametric bounded
Löb theorem. The separate classes remain the primary interface; this bundle only
serves theorems needing the whole collection.

Paper node: §§3.2–4 (Properties 1–4, Definition 1, `Eval₁` specification).
-/
class BHBL [L.Zero] [L.One] [L.Add] [L.Eq] (μ : ProofMeasure T) (μ₀ : ProofMeasure T₀)
    (𝔅 : BoundedProvability T₀ T) extends
  𝔅.BImpDistr, 𝔅.BQuantDistr, 𝔅.BEvalSpec, 𝔅.BMono, BExpansion μ μ₀ 𝔅

end sameLanguage

end BoundedProvability

end Critch
end FirstOrder
end LO
