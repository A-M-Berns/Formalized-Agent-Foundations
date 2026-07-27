/-
  Bounded provability interface for Critch 2019 (Phase A, interface-relative).

  The abstract bounded box `□ₖ` of §3.1 — a single two-variable semisentence whose
  bound slot is an object-level term — together with the interface properties the
  proof of Theorem 1 (pp. 6–8) consumes: Properties 1–2 (§3.2) and Definition 1
  with Properties 3–4 (§4). Nothing here is instantiated yet; grounding these
  classes for Foundation's proof encoding is Phase B (`Critch/Grounding/`).

  Single-system reading (R2-F04): the paper works throughout in ONE proof system
  `S`, with one Gödel encoding and one size measure. An earlier draft generalized
  to a pair of theories `T₀`, `T` with separate measures `μ₀`, `μ`; Theorem 1's
  proof re-measures its own intermediate theorem in the same system (eq. 4.3 is
  obtained with `⊢_n`, combined internally, and the result at eq. 4.6 is fed to
  Bounded Necessitation *again*), a step unreachable at two-theory generality
  without a silent `T = T₀`, `μ = μ₀` specialization. That specialization is
  therefore the honest interface: a single `T` and a single `ProofMeasure`.

  Internal-quantifier forms (R2-F01/F02/F03/F10): every property that Theorem 1's
  proof applies to `L_S(1)` formulas under the internal `(∀k)` — Implication
  Distribution, Inner Necessitation, and bound monotonicity — is stated as ONE
  internal theorem over the free-variable box `bbew₁`. Per-numeral meta families
  are strictly weaker (no ω-rule recovers the internal universal) and are not
  offered.

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

variable {L : Language}

/--
Meta-level bounded-proof judgment `⊢ₖ` for a theory `T`: `Pf k σ` reads "`σ` has a
`T`-proof of size at most `k`" in the (here unspecified) proof-size measure of the
chosen encoding. This is the abstract counterpart of the paper's "`S` proves `φ`
using at most `k` characters"; the measure substitution itself is roadmap standing
decision 1.

`sound`/`complete` say the judgment refines ordinary provability (every bounded
proof is a proof; every proof has some size); `mono` is monotonicity of the
measure, which the paper uses silently.

Paper node: §2.1 (the `⊢ₙ` judgment; consumed by §4, Property 3).
-/
structure ProofMeasure (T : Theory L) where
  Pf : ℕ → Sentence L → Prop
  sound {k : ℕ} {σ : Sentence L} : Pf k σ → T ⊢ σ
  complete {σ : Sentence L} : T ⊢ σ → ∃ k, Pf k σ
  mono {k l : ℕ} {σ : Sentence L} : k ≤ l → Pf k σ → Pf l σ

/--
The arithmetic guard `↑m < k` as a one-free-variable formula: the boxed content
of `BQuantDistr.bddCompleteCmp`. Pure syntax; kept as a named definition so the
guard-completeness field quantifies over a fixed formula rather than a notation
occurrence.

Paper node: §4 (the restricted-quantifier guards `k > k̂` of eqs. 4.4–4.7,
officially `(∀k)(k > k̂ → …)` under the §2.4 conventions). -/
def ltGuard [L.Zero] [L.One] [L.Add] [L.LT] (m : ℕ) : Semisentence L 1 :=
  “k. ↑m < k”

/--
Bounded provability predicate with an **object-level** bound, in the single
system `S` of the paper (theory `T`, self-referential via `L.ReferenceableBy L`).

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

`bbewInner` is the two-variable (`Eval₂`) analogue needed to *box a box*: for
`φ ∈ L_S(1)` it is the three-variable semisentence standing for
`(∃m)(BBew[m, Eval₂(⌜□.(φ[·])⌝, a, k), z])` — variable `0` the outer bound `z`,
variable `1` the inner bound `a`, variable `2` the argument `k`. It exists
because Property 4's internal form (`BExpansion.innerNec`) boxes the formula
`□ₐ(φ[k])`, which has BOTH `a` and `k` unbound, so §3.1's one-variable `Eval₁`
route cannot express the outer box's code argument; the paper elides this under
its §2.4 abuse of notation. `bbewInner` is anchored per-numeral by
`BEvalSpec.eval_spec_inner`, exactly as `bbew₁` is by `eval_spec`.

This structure is pure syntax: all proof-theoretic content lives in the property
classes below, mirroring how Foundation's `ProvabilityAbstraction` wraps its
1-ary `prov`.

Paper node: §3.1 (`BBew`, `□ₖ`, and the `Eval₁` extension).
-/
structure BoundedProvability [L.ReferenceableBy L] (T : Theory L) where
  bbew : Semisentence L 2
  bbew₁ : Semisentence L 1 → Semisentence L 2
  bbewInner : Semisentence L 1 → Semisentence L 3

namespace BoundedProvability

variable [L.ReferenceableBy L] {T : Theory L}

/-- The box `□ₜ(σ)` at an object-level bound term `t` (a "closed expression, such
as a free variable or a constant", §3.1).

Paper node: §3.1 (`□ₖ` at a closed-expression bound). -/
def prt (𝔅 : BoundedProvability T) {n : ℕ} (t : Semiterm L Empty n)
    (σ : Sentence L) : Semisentence L n :=
  𝔅.bbew/[t, ⌜σ⌝]

/-- The box `□ₖ(σ)` at a standard numeral bound `k : ℕ`.

Paper node: §3.1 (`□ₖ` at a standard numeral bound). -/
def pr [L.Zero] [L.One] [L.Add] (𝔅 : BoundedProvability T) (k : ℕ)
    (σ : Sentence L) : Sentence L :=
  𝔅.prt (Semiterm.numeral k) σ

/--
Property 1 (Implication Distribution): **one** internal theorem, stated for the
free-variable box `bbew₁` with the parameter `k` and the bound variables `a`, `b`
all quantified inside the turnstile,

`⊢ (∀k)(∀a)(∀b)(□ₐ((φ → ψ)[k]) → (□_b(φ[k]) → □_{a+b+c}(ψ[k])))`,

for a fixed standard constant `c` (a `Const(S)`-style numeral). The bound
arithmetic `a + b + c` is object-level addition on the bound variables.

This is the form Theorem 1's proof consumes: both applications (p. 6) are to
`L_S(1)` formulas (`ψ[k] → G[⌜ψ⌝,k]`, then `G[⌜ψ⌝,k]` itself an implication)
under the internal `(∀k)` inherited from Quantifier Distribution. The paper's
"for any `p, q ∈ L_S`" covers open formulas, of which closed sentences are the
special case: a closed-sentence form is recoverable from this one via
`BEvalSpec.eval_spec` at any fixed numeral argument and a vacuous-variable
embedding, and is deliberately not offered as a parallel field (consolidation
discipline; derive it when a consumer exists).

Paper node: §3.2 (Property 1).
-/
class BImpDistr [L.Zero] [L.One] [L.Add] (𝔅 : BoundedProvability T) where
  c : ℕ
  impDistr (φ ψ : Semisentence L 1) :
    T ⊢ “∀ k a b, !(𝔅.bbew₁ (φ 🡒 ψ)) a k → !(𝔅.bbew₁ φ) b k → !(𝔅.bbew₁ ψ) (a + b + ↑c) k”

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

`νGraph_total` and `νGraph_func` make the graph an internally total function
(R2-F05). Totality is **not optional**: without it, `quantDistr`'s guarded
conclusion is vacuously satisfiable wherever the graph is empty at nonstandard
parameters — e.g. `νGraph ∧ Con_x(T)` satisfies `νGraph_spec` and `quantDistr`
while yielding no bounded box at all (were totality then provable, it would prove
`Con(T)`). The asymptotic comparison of `ν` against `lg` stays a downstream
`Asymp` obligation, deliberately outside this class.

`bddCompleteCmp` is bounded completeness for the numeral-comparison guards
(R3-F06): for each meta-level `m`,

`⊢ (∀k > m̄)(□_{c₂+ν(k)}(m̄ < k))`,

officially `(∀k)(∀y)(Γ_ν[k,y] → (m̄ < k → □_{c₂+y}(m̄ < k)))` — the box is over
the one-free-variable guard `ltGuard m` via `bbew₁`, and the bound is a fixed
constant `c₂` plus the numeral cost `ν(k)` routed through `νGraph` (standing
decision 4: never a baked-in `lg`; writing out the numeral `°k` is what the
verification of `m̄ < k` costs). The paper never states this property, but its
Theorem 1 proof spends it silently: the restricted universals of eqs. 4.4–4.7
are officially guarded implications, and recovering `(∀k > k₂)(□(ψ[k]))` from a
box of the guarded universal (Quantifier Distribution output
`□(k > k₂ → ψ[k])` at internal `k`) needs a uniformly bounded box of the guard
fact itself to feed Implication Distribution — no other interface field can
produce a box from nothing. The paper's own Property 2 proof sketch (p. 5)
exhibits exactly this cost shape: specializing an encoded proof at `°K` extends
it by `C + N + lg(K)` characters, a constant plus the numeral cost, which is
this field's `c₂ + ν(k)`. The order symbol this guard needs is why the class
assumes `[L.LT]`.

Paper node: §3.2 (Property 2), with §2.4 (representing computable functions)
and p. 5 (proof sketch: numeral-specialization cost, used silently in §4).
-/
class BQuantDistr [L.Zero] [L.One] [L.Add] [L.Eq] [L.LT] (𝔅 : BoundedProvability T) where
  C : ℕ
  ν : ℕ → ℕ
  ν_computable : Computable ν
  νGraph : Semisentence L 2
  νGraph_spec (k : ℕ) : T ⊢ “∀ y, !νGraph ↑k y ↔ y = ↑(ν k)”
  νGraph_total : T ⊢ “∀ k, ∃ y, !νGraph k y”
  νGraph_func : T ⊢ “∀ k y z, !νGraph k y → !νGraph k z → y = z”
  quantDistr {N : ℕ} {φ : Semisentence L 1} :
    T ⊢ 𝔅.pr N (∀⁰ φ : Sentence L) →
    T ⊢ “∀ k y, !νGraph k y → !(𝔅.bbew₁ φ) (↑C + ↑(2 * N) + y) k”
  c₂ : ℕ
  bddCompleteCmp (m : ℕ) :
    T ⊢ “∀ k y, !νGraph k y → ↑m < k → !(𝔅.bbew₁ (ltGuard m)) (↑c₂ + y) k”

/--
The `Eval` specifications for the free-variable boxes: substituting standard
numerals for the unbound arguments is (provably) the plain box of the substituted
sentence.

`eval_spec` internalizes §3.1's `Eval₁(⌜φ⌝, k) = ⌜φ(°k)⌝`, quantified over the
object-level bound; `eval_spec_inner` is the same anchor for `bbewInner`, whose
boxed content at numerals `(a, k)` is the sentence `(□ₐ(φ[k]))` itself a `bbew₁`
instance. Without these anchors the free-variable boxes would be unconstrained
formulas and every internal property vacuously satisfiable (the defect class of
R2-F05).

These per-numeral forms are deliberately NOT internalized to an internal `(∀k)`:
the right-hand code `⌜φ(°k)⌝` is a meta-level function of `k`, which is the whole
point of `bbew₁` (R2-F03). Re-deriving Theorem 1's proof skeleton (pp. 6–8)
against this interface shows no internal conversion is consumed: from Quantifier
Distribution onward every step stays in `bbew₁`/`bbewInner` form under the
internal `(∀k)`, and the endgame formulas (eqs. 4.6–4.7 combined to
`(∀k>k̂)(p[k])`) are box-free, so the boxes are never converted back under an
internal quantifier. The per-numeral forms remain as the semantic anchor and for
concrete-`k` specializations downstream (Theorem 2).

Paper node: §3.1 (the `Eval₁` specification).
-/
class BEvalSpec [L.Zero] [L.One] [L.Add] (𝔅 : BoundedProvability T) where
  eval_spec (φ : Semisentence L 1) (k : ℕ) :
    T ⊢ “∀ a, !(𝔅.bbew₁ φ) a ↑k ↔ !𝔅.bbew a ⌜(φ/[(.numeral k : Semiterm L Empty 0)] : Sentence L)⌝”
  eval_spec_inner (φ : Semisentence L 1) (a k : ℕ) :
    T ⊢ “∀ z, !(𝔅.bbewInner φ) z ↑a ↑k ↔
      !𝔅.bbew z ⌜((𝔅.bbew₁ φ)/[(.numeral a : Semiterm L Empty 0), (.numeral k : Semiterm L Empty 0)] : Sentence L)⌝”

/--
Internal bound monotonicity, in `bbew₁` form:
`⊢ (∀k)(∀a)(∀d)(□ₐ(φ[k]) → □_{a+d}(φ[k]))`. Not a numbered property of the
paper, but used silently whenever a bounded claim on `φ[k]` is weakened to a
larger bound under the internal `(∀k)` (eqs. 4.5–4.7); stated with an explicit
additive slack `d` (rather than `≤`) to keep the language assumptions to `Add`.
A closed-sentence form is recoverable via `BEvalSpec.eval_spec` when a consumer
exists.

Paper node: implicit in §§3–4 (silent bound weakening).
-/
class BMono [L.Add] (𝔅 : BoundedProvability T) where
  mono (φ : Semisentence L 1) :
    T ⊢ “∀ k a d, !(𝔅.bbew₁ φ) a k → !(𝔅.bbew₁ φ) (a + d) k”

/--
Definition 1 (proof expansion function) together with the two properties that
define it: **one** computable `e : ℕ → ℕ` satisfying both

* Property 3 (Bounded Necessitation): `⊢ₖ φ  ⇒  ⊢_{e(k)} □ₖ(φ)` — note the
  bounded premise `⊢ₖ` and the `e(k)` bound on the *outer* proof; and
* Property 4 (Bounded Inner Necessitation), in internal form (see below).

The meta-level judgment `⊢ₖ` is the single `ProofMeasure` `μ` of the system.
Property 3 stays a per-meta-numeral rule: Theorem 1's proof invokes it only at
meta-level proof sizes (`n` of eq. 4.3 and `N` of the final necessitation), never
under an internal quantifier. Keeping Properties 3 and 4 in one class is what
makes `e` shared, as Definition 1 requires (Theorem 1 quantifies over that
single `e`).

Property 4, by contrast, is consumed internally (p. 7: the specialization
`a := g(k)` producing eq. 4.5 happens inside the turnstile), so `innerNec` is
ONE internal theorem

`⊢ (∀k)(∀a)(∀z)(Γ_e[a, z] → (□ₐ(φ[k]) → □_z(□ₐ(φ[k]))))`,

where the object-level `e(a)` enters through the graph formula `eGraph` (§2.4
desugaring, mirroring `νGraph`), and the doubly-parametric boxed box
`□_z(□ₐ(φ[k]))` is `bbewInner` (see `BoundedProvability`). `eGraph_total` and
`eGraph_func` make the graph an internally total function — required for the
same non-vacuity reason as `νGraph_total` (R2-F05): a partial graph would let
`innerNec` hold vacuously at exactly the nonstandard parameters the internal
`(∀k)` ranges over.

Paper node: §4 (Definition 1; Properties 3–4).
-/
class BExpansion [L.Zero] [L.One] [L.Add] [L.Eq] (μ : ProofMeasure T)
    (𝔅 : BoundedProvability T) where
  e : ℕ → ℕ
  e_computable : Computable e
  eGraph : Semisentence L 2
  eGraph_spec (k : ℕ) : T ⊢ “∀ y, !eGraph ↑k y ↔ y = ↑(e k)”
  eGraph_total : T ⊢ “∀ k, ∃ y, !eGraph k y”
  eGraph_func : T ⊢ “∀ k y z, !eGraph k y → !eGraph k z → y = z”
  nec {k : ℕ} {φ : Sentence L} : μ.Pf k φ → μ.Pf (e k) (𝔅.pr k φ)
  innerNec (φ : Semisentence L 1) :
    T ⊢ “∀ k a z, !eGraph a z → !(𝔅.bbew₁ φ) a k → !(𝔅.bbewInner φ) z a k”

/-- Sanity: the interface recovers unbounded D1 — an ordinary `T`-theorem has
*some* bounded box provable in `T` (via `ProofMeasure.complete` and Property 3).

`μ` is an explicit argument: it occurs otherwise only inside the instance
argument's type, so leaving it implicit strands instance search on
`BExpansion ?μ 𝔅` and the lemma cannot be applied at all (R3-F07).

Paper node: §4 (Property 3 degenerates to Löb's derivability condition D1). -/
lemma exists_pr_of_provable [L.Zero] [L.One] [L.Add] [L.Eq]
    (μ : ProofMeasure T) {𝔅 : BoundedProvability T}
    [BExpansion μ 𝔅] {σ : Sentence L} (h : T ⊢ σ) :
    ∃ k, T ⊢ 𝔅.pr k σ := by
  obtain ⟨k, hk⟩ := μ.complete h
  exact ⟨k, μ.sound (BExpansion.nec hk)⟩

/-- R3-F07 regression check: the sanity lemma is applicable with the instance in
context (the round-3 form was stuck on `BExpansion ?μ 𝔅`). -/
example [L.Zero] [L.One] [L.Add] [L.Eq]
    {μ : ProofMeasure T} {𝔅 : BoundedProvability T}
    [BExpansion μ 𝔅] {σ : Sentence L} (h : T ⊢ σ) :
    ∃ k, T ⊢ 𝔅.pr k σ :=
  exists_pr_of_provable μ h

/--
Convenience bundle of the full bounded-HBL interface for the parametric bounded
Löb theorem. The separate classes remain the primary interface; this bundle only
serves theorems needing the whole collection.

Paper node: §§3.2–4 (Properties 1–4, Definition 1, `Eval₁` specification).
-/
class BHBL [L.Zero] [L.One] [L.Add] [L.Eq] [L.LT] (μ : ProofMeasure T)
    (𝔅 : BoundedProvability T) extends
  𝔅.BImpDistr, 𝔅.BQuantDistr, 𝔅.BEvalSpec, 𝔅.BMono, BExpansion μ 𝔅

end BoundedProvability

end Critch
end FirstOrder
end LO
