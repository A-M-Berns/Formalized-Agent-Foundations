import LogicalInduction.Framework.Foundations
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Rat.Encodable
import Foundation.Propositional.Boolean.Basic
import Complexitylib.Classes.P.Defs

/-!
# Criterion — expressible features, traders, and the Logical Induction Criterion

§3 of the paper: expressible features, worlds, deductive processes, trading strategies,
traders, exploitation, and both readings of the Logical Induction Criterion.

* `def:tf` → `EF`, a reified syntax (`dd:dsl`) with two semantics — `EF.denote` into `ℝ`,
  proved continuous by `continuous_denote`, which is what breaks the price/trade
  circularity the Brouwer step needs; and `EF.cost`, the syntactic size — together with
  `EF.rank`. `EFn n` is the rank-≤`n` subring of `History → ℝ`, the paper's commutative
  ring `𝓔ₙ`. The `var` / `letE` constructors are a disclosed, denotationally conservative
  extension for straight-line sharing, load-bearing for `cost`.
* `def:world` and propositional consistency (an unlabelled definition, tex:726) → `PCWorld`
  as a Foundation Boolean valuation, with `Holds`, `payout`, `ConsistentWith` and
  `ConsistentWithTheory`. `sentenceConjunction` / `sentenceDisjunction` and their `Holds`
  characterizations live here because both the emission layer (`RpnSplice`) and
  `Properties/LimitCoherence` need them.
* `def:dedproc` → `DeductiveProcess`, `ComputableDeductiveProcess` and the named
  `DeductiveProcessComputation`, with the bounded stage-search interface (`stageAtFuel`,
  `stageSearchUpTo`, `computedProcess`) that a clocked certificate checker consumes.
* `def:market` → `ComputableMarket` and the named `MarketComputation`, with the clocked
  exact-quote interface (`quoteAtFuel`, `exists_fuel_quoteAtFuel_list`) and the bounded
  rational feature evaluator `EF.denoteRatWithAtFuel` built on it.
* `def:tradestrat` → `Strategy n`, the paper's canonical `(feature, sentence)` encoding
  denoting `∑ eᵢ·(φᵢ − φᵢ*ⁿ)`; `def:trader` → `Trader`; `def:exploitation` →
  `Trader.Exploits`, plausible net worth bounded below and unbounded above.

## Serialization

`EF.serialize` is a flat postfix token stream of length `Θ(node count)`
(`serialize_length_le_cost`, `cost_le_serialize_length`), which is what makes poly-*size*
features admissible where a single `toNat` numeral would not be. `serializeTrades` flattens
a strategy, and the streaming stack machine `EF.streamStep` / `EF.streamReadFrom` decodes
it, giving `EF.serialize_injective` and `serializeTrades_injective`.

## The three metering layers of `def:ec`

Under `dd:fuel`: `EfficientlyComputableTok` (token emission), `EfficientlyComputableDigit`
(self-delimiting base-4 blocks, so poly digit length is poly *bit* size), and
`EfficientlyComputable` (Polish-notation sentence blocks, contracted by `unRpn` before
validation). Each layer removes a stated residual of the one above. The
structured-arithmetic escape grammar (`arithmeticVec2Code`, `negFormulaCode`, the
`parseStructured*` mutual block, `parseStructuredPaperPrime`, `parseRpn`, `unRpn`) lives
here beside the serializers because `clockedTrader` needs it; its lemma corpus is
`Framework/RpnSentence.lean`.

`def:ec` at the paper's own quantifier is `MachineEfficientTrader`: a `Complexity.FP`
function of the *unary* day (`unaryDay`, so machine-polynomial means day-polynomial)
emitting the strategy through
`strategyOfOutput = strategyOfTokens ∘ unRpn ∘ undigitize ∘ bitsToDigits`, introducing no
new parser. This is the class the construction enumerates and dominates.

## The criterion

`def:lic` → `IsLogicalInductor`, the fuel-certified compatibility reading the whole §4 tail
is conditioned on. `IsMachineLogicalInductor` (`Framework/MachineEfficiency.lean`) is the
paper's quantifier and implies it via `EfficientlyComputable.toMachine`.

Non-vacuity is witnessed here too: the paper's running example `exMaxDiff` with its
computed value, safe reciprocation landing in `(0,1]`, and `Trader.zero_not_exploits`,
which shows `Exploits` is refutable rather than vacuous.
-/

namespace LogicalInduction

/-! ## `def:tf` — Expressible Features

A reified DSL (`dd:dsl`) with two semantics. The *syntax* `EF` is the object that carries
`cost` (for efficient computability) and `rank` (dependence horizon); the *denotation*
`EF.denote` is the continuous ℝ-valued feature the paper's algebra lives on. -/

/-- `def:tf` (Expressible Feature), as syntax. Built from price features `pf φ n`,
rational constants, `+`, `×`, `max(·,·)`, and the safe reciprocation `max(1,·)⁻¹`.

The `var`/`letE` constructors are a **disclosed extension** of the paper's feature grammar:
straight-line sharing (evaluate once, reference many times). Denotationally conservative —
every `letE` term denotes the same function as its (possibly exponentially larger)
substitution-expanded form — but load-bearing for `cost`: sharing is what keeps deep
features (hysteresis chains, purchase counters) at polynomial *syntactic size*, which is
the quantity `def:ec`'s token-emission model meters. A free `var` denotes `0`, keeping all
raw syntax total. -/
inductive EF : Type where
  /-- The price feature `φ^{*n}`: the value of `φ` on day `n`. -/
  | price (φ : Sentence) (n : ℕ) : EF
  /-- A rational constant. -/
  | const (q : ℚ) : EF
  | add (a b : EF) : EF
  | mul (a b : EF) : EF
  | max (a b : EF) : EF
  /-- Safe reciprocation `max(1, a)⁻¹` — never divides by zero, stays in `(0, 1]`. -/
  | safeRecip (a : EF) : EF
  /-- De Bruijn reference used inside a shared `letE` expression. A free reference
  evaluates to zero, making all raw syntax total. -/
  | var (i : ℕ) : EF
  /-- Shared straight-line binding: evaluate `value` once, then evaluate `body` with that
  value available as variable `0` (and prior variables shifted by one). -/
  | letE (value body : EF) : EF
  deriving DecidableEq

namespace EF

/-- Continuous ℝ-valued semantics (`def:tf`). Feeds Brouwer via `continuous_denote`.
Noncomputable because safe reciprocation uses `ℝ`'s (noncomputable) inverse; efficient
computability is tracked syntactically by `cost`, not by running `denote`. -/
noncomputable def denoteWith : EF → List ℝ → History → ℝ
  | price φ n,   _, V => V n φ
  | const q,     _, _ => (q : ℝ)
  | add a b,     ρ, V => a.denoteWith ρ V + b.denoteWith ρ V
  | mul a b,     ρ, V => a.denoteWith ρ V * b.denoteWith ρ V
  | max a b,     ρ, V => Max.max (a.denoteWith ρ V) (b.denoteWith ρ V)
  | safeRecip a, ρ, V => (Max.max 1 (a.denoteWith ρ V))⁻¹
  | var i,       ρ, _ => ρ.getD i 0
  | letE x body, ρ, V => body.denoteWith (x.denoteWith ρ V :: ρ) V

/-- `def:tf`.  The feature's continuous ℝ-valued denotation: the closed-environment case
of `denoteWith`, evaluated against a whole price history. -/
noncomputable def denote (e : EF) (V : History) : ℝ := e.denoteWith [] V

@[simp] lemma denoteWith_price (φ : Sentence) (n : ℕ) (ρ : List ℝ) (V : History) :
    (price φ n).denoteWith ρ V = V n φ := rfl
@[simp] lemma denoteWith_const (q : ℚ) (ρ : List ℝ) (V : History) :
    (const q).denoteWith ρ V = (q : ℝ) := rfl
@[simp] lemma denoteWith_add (a b : EF) (ρ : List ℝ) (V : History) :
    (add a b).denoteWith ρ V = a.denoteWith ρ V + b.denoteWith ρ V := rfl
@[simp] lemma denoteWith_mul (a b : EF) (ρ : List ℝ) (V : History) :
    (mul a b).denoteWith ρ V = a.denoteWith ρ V * b.denoteWith ρ V := rfl
@[simp] lemma denoteWith_max (a b : EF) (ρ : List ℝ) (V : History) :
    (max a b).denoteWith ρ V = Max.max (a.denoteWith ρ V) (b.denoteWith ρ V) := rfl
@[simp] lemma denoteWith_safeRecip (a : EF) (ρ : List ℝ) (V : History) :
    (safeRecip a).denoteWith ρ V = (Max.max 1 (a.denoteWith ρ V))⁻¹ := rfl
@[simp] lemma denoteWith_var (i : ℕ) (ρ : List ℝ) (V : History) :
    (var i).denoteWith ρ V = ρ.getD i 0 := rfl
@[simp] lemma denoteWith_letE (x body : EF) (ρ : List ℝ) (V : History) :
    (letE x body).denoteWith ρ V = body.denoteWith (x.denoteWith ρ V :: ρ) V := rfl

/-- Exact rational evaluation of an expressible feature against a rational price table.
This is the executable semantics used when a computable-market certificate is available. -/
def denoteRatWith : EF → List ℚ → (ℕ → Sentence → ℚ) → ℚ
  | price φ n,   _, V => V n φ
  | const q,     _, _ => q
  | add a b,     ρ, V => a.denoteRatWith ρ V + b.denoteRatWith ρ V
  | mul a b,     ρ, V => a.denoteRatWith ρ V * b.denoteRatWith ρ V
  | max a b,     ρ, V => Max.max (a.denoteRatWith ρ V) (b.denoteRatWith ρ V)
  | safeRecip a, ρ, V => (Max.max 1 (a.denoteRatWith ρ V))⁻¹
  | var i,       ρ, _ => ρ.getD i 0
  | letE x body, ρ, V => body.denoteRatWith (x.denoteRatWith ρ V :: ρ) V

/-- The exact rational denotation against a rational price table: the closed-environment
case of `denoteRatWith`. -/
def denoteRat (e : EF) (V : ℕ → Sentence → ℚ) : ℚ := e.denoteRatWith [] V

/-- Rational and real feature semantics agree under pointwise-related variable
environments and price tables. -/
lemma denoteWith_eq_ratCast (e : EF) (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ n φ, P n φ = (Q n φ : ℝ)) :
    ∀ (ρR : List ℝ) (ρQ : List ℚ),
      (∀ i, ρR.getD i 0 = (ρQ.getD i 0 : ℝ)) →
      e.denoteWith ρR P = (e.denoteRatWith ρQ Q : ℝ) := by
  induction e with
  | price φ n => intro ρR ρQ hρ; simpa [denoteWith, denoteRatWith] using hQ n φ
  | const q => intro ρR ρQ hρ; rfl
  | add a b iha ihb => intro ρR ρQ hρ; simp [denoteWith, denoteRatWith, iha ρR ρQ hρ, ihb ρR ρQ hρ]
  | mul a b iha ihb => intro ρR ρQ hρ; simp [denoteWith, denoteRatWith, iha ρR ρQ hρ, ihb ρR ρQ hρ]
  | max a b iha ihb => intro ρR ρQ hρ; simp [denoteWith, denoteRatWith, iha ρR ρQ hρ, ihb ρR ρQ hρ]
  | safeRecip a iha => intro ρR ρQ hρ; simp [denoteWith, denoteRatWith, iha ρR ρQ hρ]
  | var i => intro ρR ρQ hρ; exact hρ i
  | letE x body ihx ihbody =>
      intro ρR ρQ hρ
      simp only [denoteWith, denoteRatWith]
      apply ihbody
      intro i
      cases i with
      | zero => simpa using ihx ρR ρQ hρ
      | succ i => simpa using hρ i

/-- Rational and real feature semantics agree when the real history is the coercion of the
rational price table. -/
lemma denote_eq_ratCast (e : EF) (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ n φ, P n φ = (Q n φ : ℝ)) :
    e.denote P = (e.denoteRat Q : ℝ) := by
  exact denoteWith_eq_ratCast e P Q hQ [] [] (by simp)

/-- Syntactic size of an expressible feature (`def:tf`): the structural node count. An
auxiliary complexity measure — a small feature is cheap to write down. (Efficient
computability itself is *not* defined via `cost`; it goes through the clocked interpreter,
see `EfficientlyComputable`. `cost` remains a convenient bound on description size.) -/
def cost : EF → ℕ
  | price _ _   => 1
  | const _     => 1
  | add a b     => a.cost + b.cost + 1
  | mul a b     => a.cost + b.cost + 1
  | max a b     => a.cost + b.cost + 1
  | safeRecip a => a.cost + 1
  | var _       => 1
  | letE x body => x.cost + body.cost + 1

/-- Rank = the latest day the feature inspects (`def:valfeature`); `EF_n` = rank ≤ `n`.
`const` inspects nothing (rank `0`); a binary node takes the `max` of its children. -/
def rankWith : EF → List ℕ → ℕ
  | price _ n,   _ => n
  | const _,     _ => 0
  | add a b,     ρ => Nat.max (a.rankWith ρ) (b.rankWith ρ)
  | mul a b,     ρ => Nat.max (a.rankWith ρ) (b.rankWith ρ)
  | max a b,     ρ => Nat.max (a.rankWith ρ) (b.rankWith ρ)
  | safeRecip a, ρ => a.rankWith ρ
  | var i,       ρ => ρ.getD i 0
  | letE x body, ρ => body.rankWith (x.rankWith ρ :: ρ)

/-- `def:valfeature`.  The latest day the feature inspects; a `const` and a free `var`
inspect nothing.  This is what `EFn` grades the feature algebra by. -/
def rank : EF → ℕ
  | price _ n   => n
  | const _     => 0
  | add a b     => Nat.max a.rank b.rank
  | mul a b     => Nat.max a.rank b.rank
  | max a b     => Nat.max a.rank b.rank
  | safeRecip a => a.rank
  | var _       => 0
  | letE x body => Nat.max x.rank body.rank

@[simp] lemma rank_price (φ : Sentence) (n : ℕ) : (price φ n).rank = n := rfl
@[simp] lemma rank_const (q : ℚ) : (const q).rank = 0 := rfl
@[simp] lemma rank_add (a b : EF) : (add a b).rank = Nat.max a.rank b.rank := rfl
@[simp] lemma rank_mul (a b : EF) : (mul a b).rank = Nat.max a.rank b.rank := rfl
@[simp] lemma rank_max (a b : EF) : (max a b).rank = Nat.max a.rank b.rank := rfl
@[simp] lemma rank_safeRecip (a : EF) : (safeRecip a).rank = a.rank := rfl
@[simp] lemma rank_var (i : ℕ) : (var i).rank = 0 := rfl
@[simp] lemma rank_letE (x body : EF) : (letE x body).rank = Nat.max x.rank body.rank := rfl

/-! ### `denote` is a ring map on the nose (all `rfl`), packaged for `simp`. -/

/-- A price feature denotes the market's own day-`n` price of its sentence. -/
@[simp] lemma denote_price (φ : Sentence) (n : ℕ) :
    (price φ n).denote = fun V => V n φ := rfl

@[simp] lemma denote_const (q : ℚ) :
    (const q).denote = fun _ => (q : ℝ) := rfl

@[simp] lemma denote_add (a b : EF) : (add a b).denote = a.denote + b.denote := by
  funext V; simp [denote, denoteWith, Pi.add_apply]

@[simp] lemma denote_mul (a b : EF) : (mul a b).denote = a.denote * b.denote := by
  funext V; simp [denote, denoteWith, Pi.mul_apply]

@[simp] lemma denote_max (a b : EF) (V : History) :
    (max a b).denote V = Max.max (a.denote V) (b.denote V) := rfl

@[simp] lemma denote_safeRecip (a : EF) (V : History) :
    (safeRecip a).denote V = (Max.max 1 (a.denote V))⁻¹ := rfl

/-! ### Continuity (`def:tf`), proved for the whole DSL — this is what breaks the
price/trade circularity the paper's fixed-point argument needs. Safe reciprocation is the
only nontrivial case: `max 1 x ≥ 1 > 0`, so the reciprocal is continuous with no removable
singularity. -/

private lemma continuous_env_getD (ρ : List (History → ℝ))
    (hρ : ∀ f ∈ ρ, Continuous f) (i : ℕ) :
    Continuous (fun V => (ρ.map (fun f => f V)).getD i 0) := by
  induction ρ generalizing i with
  | nil => simp; exact continuous_const
  | cons f ρ ih =>
      cases i with
      | zero => simpa using hρ f (by simp)
      | succ i =>
          simp only [List.map_cons, List.getD_cons_succ]
          exact ih (fun g hg => hρ g (by simp [hg])) i

lemma continuous_denoteWith (e : EF) : ∀ (ρ : List (History → ℝ)),
    (∀ f ∈ ρ, Continuous f) →
    Continuous (fun V => e.denoteWith (ρ.map (fun f => f V)) V) := by
  induction e with
  | price φ n => intro ρ hρ; exact (continuous_apply φ).comp (continuous_apply n)
  | const q => intro ρ hρ; exact continuous_const
  | add a b ha hb => intro ρ hρ; exact (ha ρ hρ).add (hb ρ hρ)
  | mul a b ha hb => intro ρ hρ; exact (ha ρ hρ).mul (hb ρ hρ)
  | max a b ha hb => intro ρ hρ; exact (ha ρ hρ).max (hb ρ hρ)
  | safeRecip a ha =>
      intro ρ hρ
      refine (continuous_const.max (ha ρ hρ)).inv₀ (fun V => ?_)
      have : (1 : ℝ) ≤ Max.max 1 (a.denoteWith (ρ.map (fun f => f V)) V) :=
        le_max_left _ _
      positivity
  | var i => intro ρ hρ; exact continuous_env_getD ρ hρ i
  | letE x body hx hbody =>
      intro ρ hρ
      simpa [denoteWith] using hbody
        ((fun V => x.denoteWith (ρ.map (fun f => f V)) V) :: ρ)
        (by
          intro f hf
          simp only [List.mem_cons] at hf
          rcases hf with rfl | hf
          · exact hx ρ hρ
          · exact hρ f hf)

lemma continuous_denote (e : EF) : Continuous e.denote := by
  exact continuous_denoteWith e [] (by simp)

/-! ### `EF_n` is a commutative ring (`def:tf`).

Features *are* functions (`def:valfeature`), so the ring structure lives on the semantic
side: `History → ℝ` is a commutative ring pointwise, and the rank-≤`n` expressible
features are a **subring** of it (closed under `+`, `×`, and — via `const (-1) * ·` —
negation). We keep the syntax `EF` as the DSL for `cost`; `EFn n` is the ring the paper's
algebra (`2 - φ*6`, etc.) actually takes place in. -/

/-- The set of rank-≤`n` expressible features, as a subring of the pointwise function
ring `History → ℝ`. -/
def ExpressibleRankLE (n : ℕ) : Subring (History → ℝ) where
  carrier := { f | ∃ e : EF, e.rank ≤ n ∧ e.denote = f }
  zero_mem' := ⟨const 0, by simp, by funext V; simp [denote, denoteWith]⟩
  one_mem' := ⟨const 1, by simp, by funext V; simp [denote, denoteWith]⟩
  add_mem' := by
    rintro f g ⟨ef, hf, rfl⟩ ⟨eg, hg, rfl⟩
    exact ⟨add ef eg, Nat.max_le.mpr ⟨hf, hg⟩, by simp⟩
  mul_mem' := by
    rintro f g ⟨ef, hf, rfl⟩ ⟨eg, hg, rfl⟩
    exact ⟨mul ef eg, Nat.max_le.mpr ⟨hf, hg⟩, by simp⟩
  neg_mem' := by
    rintro f ⟨ef, hf, rfl⟩
    refine ⟨mul (const (-1)) ef, by simpa using hf, ?_⟩
    funext V; simp [denote, denoteWith]

/-- `EF_n`: the rank-≤`n` expressible features. A commutative ring (`def:tf`). -/
abbrev EFn (n : ℕ) : Subring (History → ℝ) := ExpressibleRankLE n

/-- The required `CommRing EF_n` instance (`def:tf`), inherited from the ambient function
ring via the subring structure. -/
example (n : ℕ) : CommRing (EFn n) := inferInstance

/-- Every feature's denotation lives in the ring graded by its own rank. -/
lemma denote_mem_EFn (e : EF) : e.denote ∈ EFn e.rank := ⟨e, le_rfl, rfl⟩

/-- The rank grading is monotone, so a rank-`n` strategy may be built from lower-rank
pieces. -/
lemma EFn_mono {m n : ℕ} (h : m ≤ n) : EFn m ≤ EFn n := by
  rintro f ⟨e, he, rfl⟩
  exact ⟨e, he.trans h, rfl⟩

/-! ### Non-vacuity witnesses (`def:tf`).  Concrete features with computed denotations,
so the DSL is not an empty shell. -/

/-- Non-vacuity 1 — the paper's running example (`def:tf`): `max(0, φ*6 − ψ*7)`.
Subtraction is sugar for `add a (mul (const (-1)) b)`. -/
def exMaxDiff (φ ψ : Sentence) : EF :=
  max (const 0) (add (price φ 6) (mul (const (-1)) (price ψ 7)))

/-- Its rank is `7`, matching the paper. -/
example (φ ψ : Sentence) : (exMaxDiff φ ψ).rank = 7 := by
  simp [exMaxDiff]

/-- The paper's computed value: with `p₆(φ) = 0.5` and `p₇(ψ) = 0.2`, it returns `0.3`. -/
example (φ ψ : Sentence) (V : History) (h6 : V 6 φ = 0.5) (h7 : V 7 ψ = 0.2) :
    (exMaxDiff φ ψ).denote V = 0.3 := by
  simp only [exMaxDiff, denote_max, denote_add, denote_mul, denote_price, denote_const,
    Pi.add_apply, Pi.mul_apply, h6, h7]
  norm_num

/-- Non-vacuity 2 — safe reciprocation genuinely lands in `(0, 1]`, for *any* argument
feature and history: it never divides by zero. This is the property `max(1,·)⁻¹` exists
to guarantee. -/
example (a : EF) (V : History) :
    0 < (safeRecip a).denote V ∧ (safeRecip a).denote V ≤ 1 := by
  rw [denote_safeRecip]
  have h1 : (1 : ℝ) ≤ Max.max 1 (a.denote V) := le_max_left _ _
  constructor
  · positivity
  · rw [inv_le_one_iff₀]; right; exact h1

/-! ### `Encodable EF` — computable codes for expressible features.

Efficient computability (`def:ec`) requires talking about a machine that *outputs* a
trader's strategies, so those strategies must be encodable as naturals — with a
**computable** decoder (a classical `Countable`-derived encoding would not let a machine
recover the strategy). We build the encoding by hand (there is no `deriving Encodable`),
following Mathlib's own `Nat.Partrec.Code` template: a structural `toNat` and a
well-founded `ofNat`, each child encoded strictly smaller than its parent. -/

/-- Structural encoding of an expressible feature as a natural number, tag-then-payload via
`Nat.pair` only — **no multiplication**. This matters for `def:ec`: `Nat.pair` is a
`Nat.Partrec.Code` *primitive* (`Code.pair`, no `prec`), so a program that builds a
strategy's code from `n` is a tree of `const`/`pair`/`comp` whose clocked-interpreter fuel
is a clean `n + O(1)` — which is what makes responsive traders' efficient computability
provable (see `Computable.lean`). The encoding is a genuine computable bijection. -/
def toNat : EF → ℕ
  | const q     => Nat.pair 0 (Encodable.encode q)
  | price φ n   => Nat.pair 1 (Nat.pair (Encodable.encode φ) n)
  | add a b     => Nat.pair 2 (Nat.pair a.toNat b.toNat)
  | mul a b     => Nat.pair 3 (Nat.pair a.toNat b.toNat)
  | max a b     => Nat.pair 4 (Nat.pair a.toNat b.toNat)
  | safeRecip a => Nat.pair 5 a.toNat
  | var i       => Nat.pair 6 i
  | letE x body => Nat.pair 7 (Nat.pair x.toNat body.toNat)

/-- Fuel-clocked decoder inverting `EF.toNat`. Structural recursion on `fuel`; each child's
code is strictly smaller (tag `≥ 1` ⇒ `Nat.pair tag X > X`), so `fuel = m + 1` suffices. -/
def ofNatAux : ℕ → ℕ → Option EF
  | 0, _ => none
  | fuel + 1, m =>
    match m.unpair.1 with
    | 0 => (Encodable.decode m.unpair.2 : Option ℚ).map const
    | 1 => (Encodable.decode m.unpair.2.unpair.1 : Option Sentence).map
             (fun φ => price φ m.unpair.2.unpair.2)
    | 2 => (ofNatAux fuel m.unpair.2.unpair.1).bind
             (fun a => (ofNatAux fuel m.unpair.2.unpair.2).map (add a))
    | 3 => (ofNatAux fuel m.unpair.2.unpair.1).bind
             (fun a => (ofNatAux fuel m.unpair.2.unpair.2).map (mul a))
    | 4 => (ofNatAux fuel m.unpair.2.unpair.1).bind
             (fun a => (ofNatAux fuel m.unpair.2.unpair.2).map (max a))
    | 5 => (ofNatAux fuel m.unpair.2).map safeRecip
    | 6 => some (var m.unpair.2)
    | 7 => (ofNatAux fuel m.unpair.2.unpair.1).bind
             (fun x => (ofNatAux fuel m.unpair.2.unpair.2).map (letE x))
    | _ => none

/-- Decoder inverting `EF.toNat`, with fuel `m + 1` (always enough). -/
def ofNat (m : ℕ) : Option EF := ofNatAux (m + 1) m

/-- `Nat.pair t X > X` when the tag `t ≥ 1` — the strict decrease making children smaller. -/
private lemma lt_pair_tag (t X : ℕ) (ht : 0 < t) : X < Nat.pair t X :=
  lt_of_le_of_lt (Nat.right_le_pair 0 X) (Nat.pair_lt_pair_left X ht)

lemma ofNatAux_toNat : ∀ (fuel : ℕ) (e : EF), e.toNat < fuel → ofNatAux fuel e.toNat = some e := by
  intro fuel
  induction fuel with
  | zero => intro e he; omega
  | succ fuel ih =>
      intro e he
      cases e with
      | const q => simp [toNat, ofNatAux, Nat.unpair_pair]
      | price φ n => simp [toNat, ofNatAux, Nat.unpair_pair]
      | add a b =>
          simp only [toNat] at he ⊢
          have h1 := Nat.left_le_pair a.toNat b.toNat
          have h2 := Nat.right_le_pair a.toNat b.toNat
          have h3 := lt_pair_tag 2 (Nat.pair a.toNat b.toNat) (by norm_num)
          simp only [ofNatAux, Nat.unpair_pair, ih a (by omega), ih b (by omega),
            Option.bind_some, Option.map_some]
      | mul a b =>
          simp only [toNat] at he ⊢
          have h1 := Nat.left_le_pair a.toNat b.toNat
          have h2 := Nat.right_le_pair a.toNat b.toNat
          have h3 := lt_pair_tag 3 (Nat.pair a.toNat b.toNat) (by norm_num)
          simp only [ofNatAux, Nat.unpair_pair, ih a (by omega), ih b (by omega),
            Option.bind_some, Option.map_some]
      | max a b =>
          simp only [toNat] at he ⊢
          have h1 := Nat.left_le_pair a.toNat b.toNat
          have h2 := Nat.right_le_pair a.toNat b.toNat
          have h3 := lt_pair_tag 4 (Nat.pair a.toNat b.toNat) (by norm_num)
          simp only [ofNatAux, Nat.unpair_pair, ih a (by omega), ih b (by omega),
            Option.bind_some, Option.map_some]
      | safeRecip a =>
          simp only [toNat] at he ⊢
          have h3 := lt_pair_tag 5 a.toNat (by norm_num)
          simp only [ofNatAux, Nat.unpair_pair, ih a (by omega), Option.map_some]
      | var i => simp [toNat, ofNatAux, Nat.unpair_pair]
      | letE x body =>
          simp only [toNat] at he ⊢
          have h1 := Nat.left_le_pair x.toNat body.toNat
          have h2 := Nat.right_le_pair x.toNat body.toNat
          have h3 := lt_pair_tag 7 (Nat.pair x.toNat body.toNat) (by norm_num)
          simp only [ofNatAux, Nat.unpair_pair, ih x (by omega), ih body (by omega),
            Option.bind_some, Option.map_some]

lemma ofNat_toNat (e : EF) : ofNat e.toNat = some e :=
  ofNatAux_toNat _ e (Nat.lt_succ_self _)

instance : Encodable EF := ⟨toNat, ofNat, ofNat_toNat⟩

/-! ### `EF.serialize` — a **flat, poly-size** token stream for the feature.

`toNat` (above) is a faithful *bijective* code, but its **value blows up doubly-exponentially
in tree depth** (`Nat.pair`-nesting squares the magnitude per level), so a size-`n`, depth-`n`
feature has a `2^{2^n}`-value `toNat` — a `4ⁿ`-*bit* number. Under the clocked interpreter a
fixed program run for `poly n` fuel can only *output* a `poly n`-**value** natural (every
`evaln` clause fuel-guards its inputs, so intermediates stay `≤ fuel`; see
`EfficientlyComputableTok`), i.e. `O(log n)` bits. So an efficiency notion based on emitting
`toNat` as a single number would exclude features that are poly-*size* but deep, which the
paper's `def:ec` admits — an unfaithfulness in the class itself, not merely a proof
inconvenience.

`serialize` is the fix: a flat postfix (RPN) token stream whose **length is `Θ(node count)`**
(`serialize_length_le_cost`), so poly-*size* ⇔ poly-*length*, and whose individual tokens are
small (tags `0..5`, day indices, and the atomic sentence/constant codes). Efficient
computability (`EfficientlyComputableTok`) asks a program to emit this stream *one token at a
time* — polynomially many small tokens — which deep poly-size features admit. The stream is a
genuine encoding: `EF.serialize_injective` (via the streaming stack machine `EF.streamStep`)
shows it determines the feature. -/
/-- The flat postfix (RPN) token stream of a feature: tags `0..5`, `7`, `8` with their
small payloads (day indices and atomic sentence/constant codes).  Its length is
`Θ(node count)` (`serialize_length_le_cost`, `cost_le_serialize_length`), which is what
makes poly-*size* features admissible where a single `toNat` numeral would not be, and it
determines the feature (`EF.serialize_injective`). -/
def serialize : EF → List ℕ
  | price φ n   => [0, Encodable.encode φ, n]
  | const q     => [1, Encodable.encode q]
  | add a b     => a.serialize ++ b.serialize ++ [2]
  | mul a b     => a.serialize ++ b.serialize ++ [3]
  | max a b     => a.serialize ++ b.serialize ++ [4]
  | safeRecip a => a.serialize ++ [5]
  | var i       => [7, i]
  | letE x body => x.serialize ++ body.serialize ++ [8]

/-- `serialize`'s length is bounded by `3 · cost` — linear in the node count. Hence
poly-*size* (poly-`cost`) features have poly-*length* serializations, so
`EfficientlyComputableTok` admits them (unlike `toNat`, whose *value* is exponential).
Paper node: `def:ec` -/
lemma serialize_length_le_cost (e : EF) : (serialize e).length ≤ 3 * e.cost := by
  induction e with
  | price φ n => simp [serialize, cost]
  | const q => simp [serialize, cost]
  | add a b iha ihb => simp only [serialize, cost, List.length_append, List.length_cons,
      List.length_nil]; omega
  | mul a b iha ihb => simp only [serialize, cost, List.length_append, List.length_cons,
      List.length_nil]; omega
  | max a b iha ihb => simp only [serialize, cost, List.length_append, List.length_cons,
      List.length_nil]; omega
  | safeRecip a iha => simp only [serialize, cost, List.length_append, List.length_cons,
      List.length_nil]; omega
  | var i => simp [serialize, cost]
  | letE x body ihx ihbody => simp only [serialize, cost, List.length_append,
      List.length_cons, List.length_nil]; omega

/-- Converse calibration: the node count is bounded by the token count, so `cost` and the
serialized length agree up to the fixed factor `3`.  Together with `serialize_length_le_cost`
this reconciles the two cost vocabularies in play: `EF.cost` (the syntactic size the
strategy-level bounds are stated in) is an honest two-sided proxy for the token-stream length
that `def:ec`'s emission model actually meters.
Paper node: `def:ec` -/
lemma cost_le_serialize_length (e : EF) : e.cost ≤ (serialize e).length := by
  induction e with
  | price φ n => simp [serialize, cost]
  | const q => simp [serialize, cost]
  | add a b iha ihb => simp only [serialize, cost, List.length_append, List.length_cons,
      List.length_nil]; omega
  | mul a b iha ihb => simp only [serialize, cost, List.length_append, List.length_cons,
      List.length_nil]; omega
  | max a b iha ihb => simp only [serialize, cost, List.length_append, List.length_cons,
      List.length_nil]; omega
  | safeRecip a iha => simp only [serialize, cost, List.length_append, List.length_cons,
      List.length_nil]; omega
  | var i => simp [serialize, cost]
  | letE x body ihx ihbody => simp only [serialize, cost, List.length_append,
      List.length_cons, List.length_nil]; omega

end EF

/-! ## Flat serialization of strategies + unique decodability

A **strategy** is a `List (EF × Sentence)`; `serializeTrades` flattens it to a token stream
by concatenating each coefficient's `EF.serialize` followed by a trade-frame `[6, ⌜φ⌝]`.

One streaming stack machine decodes it. `EF.streamStep` consumes exactly one token per step,
carrying the parser control state explicitly, so a whole run is a single `List.foldl`
(`EF.streamReadFrom`). Tags `0..5` build features and push them; tag `6` reads a sentence
code and pops a coefficient to record a trade. Both `EF.serialize_injective` and
`serializeTrades_injective` come from its one roundtrip induction
(`EF.streamReadFrom_serialize_self`), so the token stream `EfficientlyComputableTok` emits
determines the strategy. This is also the form the concrete LIA compiler runs.

The state is `((mode, pendingSentence), (featureStack, trades))`. Mode `0` is ready; modes
`1,2` read a price's sentence/day; mode `3` reads a constant; mode `4` reads a trade
sentence; and mode `5` reads a variable index. -/

/-- Flatten a strategy to a token stream: each trade is its coefficient's `EF.serialize`
followed by the frame `[6, ⌜φ⌝]`. This is the object `EfficientlyComputableTok` requires a
program to emit token-by-token. -/
def serializeTrades : List (EF × Sentence) → List ℕ
  | [] => []
  | (e, φ) :: rest => e.serialize ++ (6 :: Encodable.encode φ :: serializeTrades rest)

/-- The streaming decoder's state: `((mode, pendingSentence), (featureStack, trades))`. -/
abbrev EF.StreamState :=
  (ℕ × Option Sentence) × (List EF × List (EF × Sentence))

/-- The decoder's start state: ready mode, nothing pending, empty stack and no trades. -/
def EF.streamInitial : EF.StreamState := ((0, none), ([], []))

/-- Consume exactly one token of the flat strategy serialization. -/
def EF.streamStep : Option EF.StreamState → ℕ → Option EF.StreamState
  | none, _ => none
  | some ((mode, pending), (efst, trades)), token =>
      if mode = 0 then
        if token = 0 then some ((1, none), (efst, trades))
        else if token = 1 then some ((3, none), (efst, trades))
        else if token = 2 then
          match efst with
          | b :: a :: rest => some ((0, none), (EF.add a b :: rest, trades))
          | _ => none
        else if token = 3 then
          match efst with
          | b :: a :: rest => some ((0, none), (EF.mul a b :: rest, trades))
          | _ => none
        else if token = 4 then
          match efst with
          | b :: a :: rest => some ((0, none), (EF.max a b :: rest, trades))
          | _ => none
        else if token = 5 then
          match efst with
          | a :: rest => some ((0, none), (EF.safeRecip a :: rest, trades))
          | [] => none
        else if token = 6 then some ((4, none), (efst, trades))
        else if token = 7 then some ((5, none), (efst, trades))
        else if token = 8 then
          match efst with
          | body :: x :: rest => some ((0, none), (EF.letE x body :: rest, trades))
          | _ => none
        else none
      else if mode = 1 then
        (Encodable.decode (α := Sentence) token).map fun φ =>
          ((2, some φ), (efst, trades))
      else if mode = 2 then
        pending.map fun φ => ((0, none), (EF.price φ token :: efst, trades))
      else if mode = 3 then
        (Encodable.decode (α := ℚ) token).map fun q =>
          ((0, none), (EF.const q :: efst, trades))
      else if mode = 4 then
        match efst, Encodable.decode (α := Sentence) token with
        | e :: rest, some φ => some ((0, none), (rest, trades ++ [(e, φ)]))
        | _, _ => none
      else if mode = 5 then
        some ((0, none), (EF.var token :: efst, trades))
      else none

/-- Run the streaming parser from an explicit state. -/
def EF.streamReadFrom (tokens : List ℕ) (state : Option EF.StreamState) :
    Option EF.StreamState :=
  tokens.foldl EF.streamStep state

@[simp] lemma EF.streamReadFrom_append (left right : List ℕ)
    (state : Option EF.StreamState) :
    EF.streamReadFrom (left ++ right) state =
      EF.streamReadFrom right (EF.streamReadFrom left state) := by
  simp [EF.streamReadFrom, List.foldl_append]

/-- Reading one canonical feature serialization pushes exactly that feature. -/
lemma EF.streamReadFrom_serialize_self (e : EF) (efst : List EF)
    (trades : List (EF × Sentence)) :
    EF.streamReadFrom e.serialize (some ((0, none), (efst, trades))) =
      some ((0, none), (e :: efst, trades)) := by
  induction e generalizing efst trades with
  | price φ n => simp [EF.serialize, EF.streamReadFrom, EF.streamStep, Encodable.encodek]
  | const q => simp [EF.serialize, EF.streamReadFrom, EF.streamStep, Encodable.encodek]
  | add a b iha ihb =>
      simp only [EF.serialize, List.append_assoc]
      rw [EF.streamReadFrom_append, iha, EF.streamReadFrom_append, ihb]
      simp [EF.streamReadFrom, EF.streamStep]
  | mul a b iha ihb =>
      simp only [EF.serialize, List.append_assoc]
      rw [EF.streamReadFrom_append, iha, EF.streamReadFrom_append, ihb]
      simp [EF.streamReadFrom, EF.streamStep]
  | max a b iha ihb =>
      simp only [EF.serialize, List.append_assoc]
      rw [EF.streamReadFrom_append, iha, EF.streamReadFrom_append, ihb]
      simp [EF.streamReadFrom, EF.streamStep]
  | safeRecip a iha =>
      simp only [EF.serialize]
      rw [EF.streamReadFrom_append, iha]
      simp [EF.streamReadFrom, EF.streamStep]
  | var i => simp [EF.serialize, EF.streamReadFrom, EF.streamStep]
  | letE x body ihx ihbody =>
      simp only [EF.serialize, List.append_assoc]
      rw [EF.streamReadFrom_append, ihx, EF.streamReadFrom_append, ihbody]
      simp [EF.streamReadFrom, EF.streamStep]

/-- **`EF.serialize` is injective** — the token stream determines the feature. -/
lemma EF.serialize_injective : Function.Injective EF.serialize := by
  intro a b h
  have ha := EF.streamReadFrom_serialize_self a [] []
  rw [h, EF.streamReadFrom_serialize_self b [] []] at ha
  simpa using ha.symm

/-- Reading a canonical strategy serialization records exactly its trades. -/
lemma EF.streamReadFrom_serializeTrades_self (l : List (EF × Sentence))
    (efst : List EF) (trades : List (EF × Sentence)) :
    EF.streamReadFrom (serializeTrades l)
      (some ((0, none), (efst, trades))) =
      some ((0, none), (efst, trades ++ l)) := by
  induction l generalizing efst trades with
  | nil => simp [serializeTrades, EF.streamReadFrom]
  | cons trade rest ih =>
      rcases trade with ⟨e, φ⟩
      change EF.streamReadFrom
        (e.serialize ++ ([6, Encodable.encode φ] ++ serializeTrades rest))
        (some ((0, none), (efst, trades))) = _
      rw [EF.streamReadFrom_append, EF.streamReadFrom_serialize_self,
        EF.streamReadFrom_append]
      have hframe : EF.streamReadFrom [6, Encodable.encode φ]
          (some ((0, none), (e :: efst, trades))) =
          some ((0, none), (efst, trades ++ [(e, φ)])) := by
        simp [EF.streamReadFrom, EF.streamStep, Encodable.encodek]
      rw [hframe, ih]
      simp [List.append_assoc]

/-- Decode a strategy with the one-token streaming machine: accept iff parsing ends ready
with an empty feature stack. -/
def deserializeTrades (toks : List ℕ) : Option (List (EF × Sentence)) :=
  match EF.streamReadFrom toks (some EF.streamInitial) with
  | some ((0, none), ([], l)) => some l
  | _ => none

lemma deserializeTrades_serializeTrades (l : List (EF × Sentence)) :
    deserializeTrades (serializeTrades l) = some l := by
  unfold deserializeTrades EF.streamInitial
  rw [EF.streamReadFrom_serializeTrades_self]
  rfl

/-- **`serializeTrades` is injective** — the token stream determines the strategy. -/
lemma serializeTrades_injective : Function.Injective serializeTrades := by
  intro a b h
  have ha := deserializeTrades_serializeTrades a
  rw [h, deserializeTrades_serializeTrades] at ha
  exact (Option.some.inj ha).symm

/-! ## `def:world` + Propositional Consistency

A world (`def:world`) is a truth assignment `Sentence → 𝔹`. The only worlds the criterion
quantifies over are the **propositionally consistent** ones (an unlabelled definition,
tex:726): those determined by
Boolean algebra from an assignment to prime sentences. Rather than re-derive Boolean
recursion over Foundation's connectives, we take a p.c. world to *be* a Foundation Boolean
model — an atom valuation `ℕ → Prop` read through `Formula.Boolean.val` — which is exactly
"determined by Boolean algebra from the atoms". Provenance `(b)`. -/

/-- A propositionally consistent world (`def:world` + p.c.): an assignment to the atoms,
whose truth value on a compound sentence is fixed by Foundation's classical Boolean
semantics. -/
def PCWorld : Type := LO.Propositional.Boolean.Valuation ℕ

namespace PCWorld

open Classical

/-- Whether `φ` is true in the p.c. world `v` (Foundation's Boolean evaluation). -/
def Holds (v : PCWorld) (φ : Sentence) : Prop :=
  LO.Propositional.Formula.Boolean.val v φ

/-- The truth value of `φ` in `v` as a real number in `{0, 1}` — the payout of a
`φ`-share in world `v`. Used to value a trader's holdings. -/
noncomputable def payout (v : PCWorld) (φ : Sentence) : ℝ :=
  if v.Holds φ then 1 else 0

/-- `v` is propositionally consistent **with** a finite set `D` (`v ∈ pcworlds(D)`): it
makes every sentence in `D` true. (Consistency itself is automatic — `v` is a Boolean
model.) -/
def ConsistentWith (v : PCWorld) (D : Finset Sentence) : Prop :=
  ∀ φ ∈ D, v.Holds φ

end PCWorld

/-! ### Finite conjunctions and disjunctions of sentences

Right-associated folds with the neutral element at the empty list.  They live here,
beside `PCWorld.Holds`, because both the syntactic emission layer (`Framework/RpnSplice`,
which builds variable-width disjunction blocks) and the semantic coherence development
(`Properties/LimitCoherence`) need them. -/

/-- Right-associated conjunction, with `⊤` as the empty conjunction. -/
def sentenceConjunction : List Sentence → Sentence
  | [] => ⊤
  | φ :: l => φ ⋏ sentenceConjunction l

/-- Right-associated disjunction, with `⊥` as the empty disjunction. -/
def sentenceDisjunction : List Sentence → Sentence
  | [] => ⊥
  | φ :: l => φ ⋎ sentenceDisjunction l

@[simp] lemma holds_sentenceConjunction (v : PCWorld) (l : List Sentence) :
    v.Holds (sentenceConjunction l) ↔ ∀ φ ∈ l, v.Holds φ := by
  induction l with
  | nil => simp [sentenceConjunction, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | cons φ l ih =>
      have hstep : v.Holds (sentenceConjunction (φ :: l)) ↔
          v.Holds φ ∧ v.Holds (sentenceConjunction l) := Iff.rfl
      simp [hstep, ih]

@[simp] lemma holds_sentenceDisjunction (v : PCWorld) (l : List Sentence) :
    v.Holds (sentenceDisjunction l) ↔ ∃ φ ∈ l, v.Holds φ := by
  induction l with
  | nil => simp [sentenceDisjunction, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | cons φ l ih =>
      have hstep : v.Holds (sentenceDisjunction (φ :: l)) ↔
          v.Holds φ ∨ v.Holds (sentenceDisjunction l) := Iff.rfl
      simp [hstep, ih]

/-! ## `def:dedproc` — Deductive Process -/

/-- `def:dedproc`. A nested sequence `D 0 ⊆ D 1 ⊆ ⋯` of finite sets of sentences,
interpreted as the theorems revealed by day `n`.

Computability is packaged separately below, so the bare order-theoretic object remains
convenient in semantic lemmas while logical-inductor instances carry the paper-required
certificate.
Paper node: `def:dedproc` -/
structure DeductiveProcess where
  /-- The sentences revealed by day `n`. -/
  D : ℕ → Finset Sentence
  /-- The revealed sets are nondecreasing. -/
  mono : ∀ n, D n ⊆ D (n + 1)

/-- Deductive processes are determined by their revealed sentence sets. -/
@[ext] protected lemma DeductiveProcess.ext {DP DQ : DeductiveProcess}
    (h : DP.D = DQ.D) : DP = DQ := by
  cases DP
  cases DQ
  cases h
  rfl

/-- Nestedness at arbitrary distance: `D m ⊆ D n` whenever `m ≤ n`. -/
lemma DeductiveProcess.mono_le (DP : DeductiveProcess) {m n : ℕ} (h : m ≤ n) :
    DP.D m ⊆ DP.D n := by
  show DP.D m ≤ DP.D n
  exact (monotone_nat_of_le_succ (fun i => show DP.D i ≤ DP.D (i + 1) from DP.mono i)) h

/-- Worlds consistent with every finite stage of the deductive process: the propositional
rendering of the paper's `cworlds(Θ)`.  This definition lives with the core world/process
types so quotation interfaces can use it without importing the later affine-coherence
development. -/
def PCWorld.ConsistentWithTheory (v : PCWorld) (DP : DeductiveProcess) : Prop :=
  ∀ n, v.ConsistentWith (DP.D n)

/-- A deductive process is computable in the paper's unary-time sense: one fixed partial
recursive program eventually emits the encoded finite set `D n`.  No polynomial runtime is
required. -/
def ComputableDeductiveProcess (DP : DeductiveProcess) : Prop :=
  ∃ code : Nat.Partrec.Code, ∀ n, Encodable.encode (DP.D n) ∈ code.eval n

/-- A named presentation of a computable deductive process.  This is equivalent to
`ComputableDeductiveProcess`, but keeps the program and its semantic specification
available to finite certificate checkers.
Paper node: `def:dedproc` -/
structure DeductiveProcessComputation (DP : DeductiveProcess) where
  code : Nat.Partrec.Code
  code_spec : ∀ n, Encodable.encode (DP.D n) ∈ code.eval n

lemma ComputableDeductiveProcess.nonemptyComputation
    {DP : DeductiveProcess} (h : ComputableDeductiveProcess DP) :
    Nonempty (DeductiveProcessComputation DP) := by
  obtain ⟨code, hcode⟩ := h
  exact ⟨⟨code, hcode⟩⟩

lemma DeductiveProcessComputation.toComputable
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) :
    ComputableDeductiveProcess DP :=
  ⟨c.code, c.code_spec⟩

/-- Any terminating clocked output of the certified deductive-process program is the
unique encoding of the claimed finite stage.  This is the soundness bridge used by a
bounded dovetailer. -/
lemma DeductiveProcessComputation.evaln_eq_stage
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP)
    {n fuel out : ℕ}
    (h : out ∈ Nat.Partrec.Code.evaln fuel c.code n) :
    out = Encodable.encode (DP.D n) := by
  exact Part.mem_unique (Nat.Partrec.Code.evaln_sound h) (c.code_spec n)

/-- Every certified deductive stage eventually appears at some finite clock. -/
lemma DeductiveProcessComputation.exists_evaln_stage
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    ∃ fuel, Encodable.encode (DP.D n) ∈
      Nat.Partrec.Code.evaln fuel c.code n :=
  Nat.Partrec.Code.evaln_complete.mp (c.code_spec n)

/-- Run the deductive-process program for exactly `fuel` interpreter steps and decode its
output as a finite sentence set.  `none` represents either timeout or malformed output. -/
def DeductiveProcessComputation.stageAtFuel
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP)
    (fuel n : ℕ) : Option (Finset Sentence) :=
  (Nat.Partrec.Code.evaln fuel c.code n).bind
    (Encodable.decode (α := Finset Sentence))

lemma DeductiveProcessComputation.stageAtFuel_sound
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP)
    {fuel n : ℕ} {stage : Finset Sentence}
    (h : c.stageAtFuel fuel n = some stage) :
    stage = DP.D n := by
  unfold stageAtFuel at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨out, hout, hdecode⟩ := h
  have houtEq := c.evaln_eq_stage hout
  subst out
  simpa using hdecode.symm

lemma DeductiveProcessComputation.stageAtFuel_complete
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    ∃ fuel, c.stageAtFuel fuel n = some (DP.D n) := by
  obtain ⟨fuel, hfuel⟩ := c.exists_evaln_stage n
  refine ⟨fuel, ?_⟩
  unfold stageAtFuel
  change Nat.Partrec.Code.evaln fuel c.code n =
    some (Encodable.encode (DP.D n)) at hfuel
  rw [hfuel]
  simp

/-- A decoded deductive stage, once available, remains available at every larger clock. -/
lemma DeductiveProcessComputation.stageAtFuel_mono
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP)
    {fuel fuel' n : ℕ} {stage : Finset Sentence}
    (hff : fuel ≤ fuel') (h : c.stageAtFuel fuel n = some stage) :
    c.stageAtFuel fuel' n = some stage := by
  unfold stageAtFuel at h ⊢
  rw [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨out, hout, hdecode⟩ := h
  exact ⟨out, Nat.Partrec.Code.evaln_mono hff hout, hdecode⟩

/-- Search the first `fuel` interpreter clocks for a decoded deductive stage.  This is a
literal bounded dovetail: it is total for each bound and retains the first successful
decode. -/
def DeductiveProcessComputation.stageSearchUpTo
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    ℕ → Option (Finset Sentence)
  | 0 => none
  | fuel + 1 =>
      match c.stageSearchUpTo n fuel with
      | some stage => some stage
      | none => c.stageAtFuel fuel n

/-- Every successful bounded stage search returns the certified semantic stage; malformed
outputs and timeouts can never manufacture a different finite theory. -/
lemma DeductiveProcessComputation.stageSearchUpTo_sound
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP)
    {n fuel : ℕ} {stage : Finset Sentence}
    (h : c.stageSearchUpTo n fuel = some stage) :
    stage = DP.D n := by
  induction fuel with
  | zero => simp [stageSearchUpTo] at h
  | succ fuel ih =>
      rw [stageSearchUpTo] at h
      cases hprev : c.stageSearchUpTo n fuel with
      | some prior =>
          simp only [hprev] at h
          cases h
          exact ih hprev
      | none =>
          simp only [hprev] at h
          exact c.stageAtFuel_sound h

/-- The bounded deductive-stage dovetail reaches the exact stage at a finite clock. -/
lemma DeductiveProcessComputation.exists_stageSearchUpTo
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    ∃ clock, c.stageSearchUpTo n clock = some (DP.D n) := by
  obtain ⟨fuel, hfuel⟩ := c.stageAtFuel_complete n
  cases hprev : c.stageSearchUpTo n fuel with
  | some stage =>
      have hstage := c.stageSearchUpTo_sound hprev
      subst stage
      exact ⟨fuel, hprev⟩
  | none =>
      refine ⟨fuel + 1, ?_⟩
      simp [stageSearchUpTo, hprev, hfuel]

/-- The least successful bound for the deductive-stage dovetail.  As with MarketMaker's
stopping index, the noncomputable minimum is used only to state totality; execution is the
bounded function `stageSearchUpTo`. -/
noncomputable def DeductiveProcessComputation.stageSearchClock
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) : ℕ :=
  Nat.find (c.exists_stageSearchUpTo n)

lemma DeductiveProcessComputation.stageSearch_clock
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    c.stageSearchUpTo n (c.stageSearchClock n) = some (DP.D n) :=
  Nat.find_spec (c.exists_stageSearchUpTo n)

/-- Exact finite stage decoded at the certified stopping clock. -/
noncomputable def DeductiveProcessComputation.computedStage
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    Finset Sentence :=
  (c.stageSearchUpTo n (c.stageSearchClock n)).get
    (by rw [c.stageSearch_clock n]; rfl)

lemma DeductiveProcessComputation.computedStage_eq
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) (n : ℕ) :
    c.computedStage n = DP.D n := by
  apply Option.some.inj
  calc
    some (c.computedStage n) =
        c.stageSearchUpTo n (c.stageSearchClock n) := by
      exact Option.some_get _
    _ = some (DP.D n) := c.stageSearch_clock n

/-- The deductive process reconstructed solely through the bounded stage-search interface.
Its monotonicity is transported from the certified semantic specification. -/
noncomputable def DeductiveProcessComputation.computedProcess
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) : DeductiveProcess where
  D := c.computedStage
  mono n := by
    rw [c.computedStage_eq n, c.computedStage_eq (n + 1)]
    exact DP.mono n

lemma DeductiveProcessComputation.computedProcess_eq
    {DP : DeductiveProcess} (c : DeductiveProcessComputation DP) :
    c.computedProcess = DP := by
  unfold computedProcess
  congr 1
  funext n
  exact c.computedStage_eq n

/-! ## `def:market` — computable markets and clocked evaluation -/

/-- A paper-faithful computable rational market certificate. `quote n ⌜φ⌝` is the exact
rational price of `φ` on day `n`, and one fixed partial-recursive program computes this
two-argument table (with its input paired into one natural). No polynomial runtime is
required of the market itself.

The extra values of `quote` on naturals that do not encode a sentence are harmless and make
the computational interface total. -/
def ComputableMarket (P : History) : Prop :=
  (∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) ∧
  ∃ (quote : ℕ → ℕ → ℚ) (code : Nat.Partrec.Code),
    (∀ n φ, P n φ = (quote n (Encodable.encode φ) : ℝ)) ∧
    ∀ z, Encodable.encode (quote z.unpair.1 z.unpair.2) ∈ code.eval z

/-- A named exact rational program presenting a computable market.  The existential
paper-facing predicate above is convenient in theorem statements; this structure is the
operational form consumed by finite clocked certificate checkers.
Paper node: `def:ec` -/
structure MarketComputation (P : History) where
  price_mem_Icc : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1
  quote : ℕ → ℕ → ℚ
  code : Nat.Partrec.Code
  quote_exact : ∀ n φ, P n φ = (quote n (Encodable.encode φ) : ℝ)
  code_spec : ∀ z, Encodable.encode (quote z.unpair.1 z.unpair.2) ∈ code.eval z

lemma ComputableMarket.nonemptyComputation
    {P : History} (h : ComputableMarket P) : Nonempty (MarketComputation P) := by
  obtain ⟨hrange, quote, code, hexact, hcode⟩ := h
  exact ⟨⟨hrange, quote, code, hexact, hcode⟩⟩

/-- Every computable market is a sequence of `[0,1]`-valued pricings. -/
lemma ComputableMarket.price_mem_Icc
    {P : History} (h : ComputableMarket P) (n : ℕ) (φ : Sentence) :
    0 ≤ P n φ ∧ P n φ ≤ 1 :=
  h.1 n φ

lemma MarketComputation.toComputable
    {P : History} (c : MarketComputation P) : ComputableMarket P :=
  ⟨c.price_mem_Icc, c.quote, c.code, c.quote_exact, c.code_spec⟩

/-- Any terminating clocked output of the certified market program is the unique exact
rational quote for that paired input. -/
lemma MarketComputation.evaln_eq_quote
    {P : History} (c : MarketComputation P) {z fuel out : ℕ}
    (h : out ∈ Nat.Partrec.Code.evaln fuel c.code z) :
    out = Encodable.encode (c.quote z.unpair.1 z.unpair.2) := by
  exact Part.mem_unique (Nat.Partrec.Code.evaln_sound h) (c.code_spec z)

/-- Decoded rational form of `MarketComputation.evaln_eq_quote`. -/
lemma MarketComputation.evaln_quote_eq
    {P : History} (c : MarketComputation P) {z fuel : ℕ} {q : ℚ}
    (h : Encodable.encode q ∈ Nat.Partrec.Code.evaln fuel c.code z) :
    q = c.quote z.unpair.1 z.unpair.2 := by
  exact Encodable.encode_injective (c.evaln_eq_quote h)

/-- Every exact rational market quote eventually appears at some finite clock. -/
lemma MarketComputation.exists_evaln_quote
    {P : History} (c : MarketComputation P) (z : ℕ) :
    ∃ fuel, Encodable.encode (c.quote z.unpair.1 z.unpair.2) ∈
      Nat.Partrec.Code.evaln fuel c.code z :=
  Nat.Partrec.Code.evaln_complete.mp (c.code_spec z)

/-- Run the market program for exactly `fuel` interpreter steps and decode its output as
an exact rational.  This is the executable quote source for historical maturity checks. -/
def MarketComputation.quoteAtFuel
    {P : History} (c : MarketComputation P)
    (fuel day : ℕ) (φ : Sentence) : Option ℚ :=
  (Nat.Partrec.Code.evaln fuel c.code
    (Nat.pair day (Encodable.encode φ))).bind (Encodable.decode (α := ℚ))

lemma MarketComputation.quoteAtFuel_sound
    {P : History} (c : MarketComputation P)
    {fuel day : ℕ} {φ : Sentence} {q : ℚ}
    (h : c.quoteAtFuel fuel day φ = some q) :
    q = c.quote day (Encodable.encode φ) := by
  unfold quoteAtFuel at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨out, hout, hdecode⟩ := h
  have houtEq := c.evaln_eq_quote hout
  simp only [Nat.unpair_pair] at houtEq
  subst out
  simpa using hdecode.symm

lemma MarketComputation.quoteAtFuel_complete
    {P : History} (c : MarketComputation P) (day : ℕ) (φ : Sentence) :
    ∃ fuel, c.quoteAtFuel fuel day φ =
      some (c.quote day (Encodable.encode φ)) := by
  let z := Nat.pair day (Encodable.encode φ)
  obtain ⟨fuel, hfuel⟩ := c.exists_evaln_quote z
  refine ⟨fuel, ?_⟩
  unfold quoteAtFuel
  change Nat.Partrec.Code.evaln fuel c.code z =
    some (Encodable.encode (c.quote z.unpair.1 z.unpair.2)) at hfuel
  simp only [z, Nat.unpair_pair] at hfuel
  rw [hfuel]
  simp

/-- A decoded market quote, once available, remains available at every larger clock. -/
lemma MarketComputation.quoteAtFuel_mono
    {P : History} (c : MarketComputation P)
    {fuel fuel' day : ℕ} {φ : Sentence} {q : ℚ}
    (hff : fuel ≤ fuel') (h : c.quoteAtFuel fuel day φ = some q) :
    c.quoteAtFuel fuel' day φ = some q := by
  unfold quoteAtFuel at h ⊢
  rw [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨out, hout, hdecode⟩ := h
  exact ⟨out, Nat.Partrec.Code.evaln_mono hff hout, hdecode⟩

/-- One finite clock simultaneously recovers every quote in a finite query list.  This is
the compactness step used to evaluate a whole finite strategy prefix at one fuel value. -/
lemma MarketComputation.exists_fuel_quoteAtFuel_list
    {P : History} (c : MarketComputation P)
    (queries : List (ℕ × Sentence)) :
    ∃ fuel, ∀ query ∈ queries,
      c.quoteAtFuel fuel query.1 query.2 =
        some (c.quote query.1 (Encodable.encode query.2)) := by
  induction queries with
  | nil => exact ⟨0, by simp⟩
  | cons head tail ih =>
      obtain ⟨headFuel, hhead⟩ := c.quoteAtFuel_complete head.1 head.2
      obtain ⟨tailFuel, htail⟩ := ih
      refine ⟨max headFuel tailFuel, ?_⟩
      intro query hquery
      simp only [List.mem_cons] at hquery
      rcases hquery with rfl | hquery
      · exact c.quoteAtFuel_mono (le_max_left _ _) hhead
      · exact c.quoteAtFuel_mono (le_max_right _ _) (htail query hquery)

namespace EF

/-- The finite market cells inspected by an expressible feature.  Duplicates are harmless:
the list is syntax-directed and therefore directly executable. -/
def priceQueries : EF → List (ℕ × Sentence)
  | price φ n => [(n, φ)]
  | const _ => []
  | add a b => a.priceQueries ++ b.priceQueries
  | mul a b => a.priceQueries ++ b.priceQueries
  | max a b => a.priceQueries ++ b.priceQueries
  | safeRecip a => a.priceQueries
  | var _ => []
  | letE value body => value.priceQueries ++ body.priceQueries

/-- Exact rational evaluation with a partial quote table.  At a price node it runs the
certified market program for `fuel` steps; timeout or malformed output propagates as `none`. -/
def denoteRatWithAtFuel {P : History} (market : MarketComputation P) (fuel : ℕ) :
    EF → List ℚ → Option ℚ
  | price φ n,   _ => market.quoteAtFuel fuel n φ
  | const q,     _ => some q
  | add a b,     ρ => do
      let qa ← a.denoteRatWithAtFuel market fuel ρ
      let qb ← b.denoteRatWithAtFuel market fuel ρ
      pure (qa + qb)
  | mul a b,     ρ => do
      let qa ← a.denoteRatWithAtFuel market fuel ρ
      let qb ← b.denoteRatWithAtFuel market fuel ρ
      pure (qa * qb)
  | max a b,     ρ => do
      let qa ← a.denoteRatWithAtFuel market fuel ρ
      let qb ← b.denoteRatWithAtFuel market fuel ρ
      pure (Max.max qa qb)
  | safeRecip a, ρ => do
      let qa ← a.denoteRatWithAtFuel market fuel ρ
      pure (Max.max 1 qa)⁻¹
  | var i,       ρ => some (ρ.getD i 0)
  | letE value body, ρ => do
      let q ← value.denoteRatWithAtFuel market fuel ρ
      body.denoteRatWithAtFuel market fuel (q :: ρ)

/-- Every successful bounded evaluation is semantically exact.  In particular, malformed
decoded outputs cannot make a finite certificate checker accept: quote soundness fixes each
price leaf, and the remaining computation is exact rational arithmetic. -/
lemma denoteRatWithAtFuel_sound
    {P : History} (market : MarketComputation P) (fuel : ℕ) (e : EF) (ρ : List ℚ)
    {q : ℚ} (h : e.denoteRatWithAtFuel market fuel ρ = some q) :
    q = e.denoteRatWith ρ
      (fun n φ => market.quote n (Encodable.encode φ)) := by
  induction e generalizing ρ q with
  | price φ n =>
      exact market.quoteAtFuel_sound h
  | const value =>
      simpa [denoteRatWithAtFuel, denoteRatWith] using h.symm
  | add a b iha ihb =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨qa, ha, qb, hb, rfl⟩ := h
      simp only [denoteRatWith]
      rw [iha ρ ha, ihb ρ hb]
  | mul a b iha ihb =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨qa, ha, qb, hb, rfl⟩ := h
      simp only [denoteRatWith]
      rw [iha ρ ha, ihb ρ hb]
  | max a b iha ihb =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨qa, ha, qb, hb, rfl⟩ := h
      simp only [denoteRatWith]
      rw [iha ρ ha, ihb ρ hb]
  | safeRecip a iha =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨qa, ha, rfl⟩ := h
      simp only [denoteRatWith]
      rw [iha ρ ha]
  | var i =>
      simpa [denoteRatWithAtFuel, denoteRatWith] using h.symm
  | letE value body ihvalue ihbody =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qvalue, hvalue, hbody⟩ := h
      have hv := ihvalue ρ hvalue
      have hb := ihbody (qvalue :: ρ) hbody
      simpa only [denoteRatWith, hv] using hb

/-- Successful bounded feature evaluation is monotone in the interpreter clock. -/
lemma denoteRatWithAtFuel_mono
    {P : History} (market : MarketComputation P) {fuel fuel' : ℕ} (e : EF)
    (ρ : List ℚ) {q : ℚ} (hff : fuel ≤ fuel')
    (h : e.denoteRatWithAtFuel market fuel ρ = some q) :
    e.denoteRatWithAtFuel market fuel' ρ = some q := by
  induction e generalizing ρ q with
  | price φ n => exact market.quoteAtFuel_mono hff h
  | const value => simpa [denoteRatWithAtFuel] using h
  | add a b iha ihb =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨qa, ha, qb, hb, hq⟩ := h
      exact ⟨qa, iha ρ ha, qb, ihb ρ hb, hq⟩
  | mul a b iha ihb =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨qa, ha, qb, hb, hq⟩ := h
      exact ⟨qa, iha ρ ha, qb, ihb ρ hb, hq⟩
  | max a b iha ihb =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨qa, ha, qb, hb, hq⟩ := h
      exact ⟨qa, iha ρ ha, qb, ihb ρ hb, hq⟩
  | safeRecip a iha =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨qa, ha, hq⟩ := h
      exact ⟨qa, iha ρ ha, hq⟩
  | var i => simpa [denoteRatWithAtFuel] using h
  | letE value body ihvalue ihbody =>
      simp only [denoteRatWithAtFuel, Option.bind_eq_bind] at h ⊢
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨qvalue, hvalue, hbody⟩ := h
      rw [ihvalue ρ hvalue]
      exact ihbody (qvalue :: ρ) hbody

/-- With every syntactically requested quote ready at the shared clock, bounded evaluation
returns exactly the total rational semantics. -/
lemma denoteRatWithAtFuel_complete
    {P : History} (market : MarketComputation P) (fuel : ℕ) (e : EF) (ρ : List ℚ)
    (hready : ∀ query ∈ e.priceQueries,
      market.quoteAtFuel fuel query.1 query.2 =
        some (market.quote query.1 (Encodable.encode query.2))) :
    e.denoteRatWithAtFuel market fuel ρ =
      some (e.denoteRatWith ρ
        (fun n φ => market.quote n (Encodable.encode φ))) := by
  induction e generalizing ρ with
  | price φ n => exact hready (n, φ) (by simp [priceQueries])
  | const q => rfl
  | add a b iha ihb =>
      have ha := iha ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inl hquery))
      have hb := ihb ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inr hquery))
      simp [denoteRatWithAtFuel, denoteRatWith, ha, hb]
  | mul a b iha ihb =>
      have ha := iha ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inl hquery))
      have hb := ihb ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inr hquery))
      simp [denoteRatWithAtFuel, denoteRatWith, ha, hb]
  | max a b iha ihb =>
      have ha := iha ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inl hquery))
      have hb := ihb ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inr hquery))
      simp [denoteRatWithAtFuel, denoteRatWith, ha, hb]
  | safeRecip a iha =>
      have ha := iha ρ (fun query hquery => hready query (by
        simpa only [priceQueries] using hquery))
      simp [denoteRatWithAtFuel, denoteRatWith, ha]
  | var i => rfl
  | letE value body ihvalue ihbody =>
      have hvalue := ihvalue ρ (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inl hquery))
      let q := value.denoteRatWith ρ
        (fun n φ => market.quote n (Encodable.encode φ))
      have hbody := ihbody (q :: ρ) (fun query hquery => hready query (by
        simp only [priceQueries, List.mem_append]
        exact Or.inr hquery))
      simpa [denoteRatWithAtFuel, denoteRatWith, hvalue, q] using hbody

/-- Every finite expressible feature eventually evaluates exactly under the certified
market program, at one shared clock for all of its price queries. -/
lemma exists_fuel_denoteRatWithAtFuel
    {P : History} (market : MarketComputation P) (e : EF) (ρ : List ℚ) :
    ∃ fuel, e.denoteRatWithAtFuel market fuel ρ =
      some (e.denoteRatWith ρ
        (fun n φ => market.quote n (Encodable.encode φ))) := by
  obtain ⟨fuel, hfuel⟩ := market.exists_fuel_quoteAtFuel_list e.priceQueries
  exact ⟨fuel, e.denoteRatWithAtFuel_complete market fuel ρ hfuel⟩

end EF

/-! ## `def:tradestrat`, `def:trader` — Trading strategies and traders

An `n`-strategy (`def:tradestrat`) is the paper's canonical encoding: a finite list of
`(coefficient, sentence)` pairs `(eᵢ, φᵢ)` with each `eᵢ` an expressible feature of rank
`≤ n`. It denotes `∑ᵢ eᵢ · (φᵢ − φᵢ*ⁿ)` — "buy `eᵢ(𝓥)` shares of `φᵢ` at the day-`n`
price", the cash term being determined by the pairs. -/

/-- `def:tradestrat`. A trading strategy for day `n`.
Paper node: `def:tradestrat` -/
structure Strategy (n : ℕ) where
  /-- The `(expressible-feature coefficient, sentence)` pairs `(eᵢ, φᵢ)`. -/
  trades : List (EF × Sentence)
  /-- Every coefficient has rank `≤ n` (the strategy sees only prices up to day `n`). -/
  rank_le : ∀ p ∈ trades, p.1.rank ≤ n

/-- Strategies are determined by their trade lists; rank certificates are proofs. -/
@[ext] protected lemma Strategy.ext {n : ℕ} {T U : Strategy n}
    (h : T.trades = U.trades) : T = U := by
  cases T
  cases U
  cases h
  rfl

namespace Strategy

/-- The value of an `n`-strategy against a history `𝓥`, as assessed by a world with payout
`w` (`w φ ∈ {0,1}`): `∑ᵢ eᵢ(𝓥) · (w φᵢ − 𝓥ₙ(φᵢ))`. Each summand is "shares bought times
(world payout − price paid at day `n`)". -/
noncomputable def value {n : ℕ} (T : Strategy n) (V : History) (w : Sentence → ℝ) : ℝ :=
  (T.trades.map (fun p => p.1.denote V * (w p.2 - V n p.2))).sum

/-- Syntactic size of a strategy, summing its coefficients' `EF.cost`. Feeds the
efficient-computability bound (`dd:fuel`). -/
def cost {n : ℕ} (T : Strategy n) : ℕ :=
  (T.trades.map (fun p => p.1.cost)).sum + T.trades.length + 1

/-- The same cost/length calibration at strategy level: a whole strategy's emitted token
stream is linearly bounded by its syntactic `cost`, so a poly-`cost` strategy sequence has
poly-length serializations — the quantity `EfficientlyComputableTok` meters.
Paper node: `def:ec` -/
lemma serializeTrades_length_le_cost {n : ℕ} (T : Strategy n) :
    (serializeTrades T.trades).length ≤ 3 * T.cost := by
  have key : ∀ l : List (EF × Sentence),
      (serializeTrades l).length ≤ 3 * ((l.map (fun p => p.1.cost)).sum + l.length) := by
    intro l
    induction l with
    | nil => simp [serializeTrades]
    | cons p rest ih =>
        have hser := EF.serialize_length_le_cost p.1
        simp only [serializeTrades, List.length_append, List.length_cons, List.map_cons,
          List.sum_cons]
        omega
  calc (serializeTrades T.trades).length
      ≤ 3 * ((T.trades.map (fun p => p.1.cost)).sum + T.trades.length) := key T.trades
    _ ≤ 3 * T.cost := by unfold cost; omega

end Strategy

/-- `def:trader`. A sequence of trading strategies, one per day.
Paper node: `def:trader` -/
structure Trader where
  /-- The strategy the trader plays on day `n`. -/
  strat : (n : ℕ) → Strategy n

/-- Traders are determined by their day-indexed strategies. -/
@[ext] protected lemma Trader.ext {T U : Trader} (h : T.strat = U.strat) : T = U := by
  cases T
  cases U
  cases h
  rfl

namespace Trader

/-- The trader's net worth after day `n`, assessed by the p.c. world `v`:
`∑_{i ≤ n} vᵢ(𝓥)` — the sum of its day-`i` strategy values, priced at each day `i`. -/
noncomputable def netWorth (Tr : Trader) (V : History) (v : PCWorld) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (Tr.strat i).value V v.payout

/-- The set of **plausible assessments** of `Tr`'s net worth against history `𝓥`: its net
worth on day `n`, as valued by any world propositionally consistent with `D n`, over all
`n` (`def:exploitation`). -/
def plausibleAssessments (Tr : Trader) (V : History) (DP : DeductiveProcess) : Set ℝ :=
  { x | ∃ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) ∧ x = Tr.netWorth V v n }

/-- `def:exploitation`. `Tr` **exploits** the history `𝓥` relative to `DP` if its plausible
assessments are bounded below but not bounded above — unbounded upside off bounded
downside. -/
def Exploits (Tr : Trader) (V : History) (DP : DeductiveProcess) : Prop :=
  BddBelow (Tr.plausibleAssessments V DP) ∧ ¬ BddAbove (Tr.plausibleAssessments V DP)

end Trader

/-! ## `def:ec`, `def:lic` — Efficient computability and the Logical Induction Criterion -/

/-- Fuel bound for the constant code: `Code.const K` on input `n` halts with output `K`
within `n + K + 1` steps of the clocked interpreter. (`comp` layers share fuel in `evaln`,
so the budget is just the input length `n` plus the `K` successor steps.) A reusable tool
for certifying that constant-strategy traders are efficiently computable. -/
lemma evaln_const_self : ∀ (K n : ℕ),
    K ∈ Nat.Partrec.Code.evaln (n + K + 1) (Nat.Partrec.Code.const K) n := by
  intro K
  induction K with
  | zero =>
      intro n
      show 0 ∈ Nat.Partrec.Code.evaln (n + 1) Nat.Partrec.Code.zero n
      simp [Nat.Partrec.Code.evaln]
  | succ K ih =>
      intro n
      have hxe : Nat.Partrec.Code.evaln (n + (K + 1) + 1) (Nat.Partrec.Code.const K) n
          = some K := Nat.Partrec.Code.evaln_mono (by omega) (ih n)
      show (K + 1) ∈ Nat.Partrec.Code.evaln (n + (K + 1) + 1)
        (Nat.Partrec.Code.comp .succ (Nat.Partrec.Code.const K)) n
      simp [Nat.Partrec.Code.evaln, hxe, Option.bind_eq_some_iff, Option.guard_eq_some']
      omega

/-! `def:ec` (`dd:fuel`) — **token-indexed emission, the poly-*size* model**. A trader is
**efficiently computable** if one program emits the length of the day-`n` strategy's flat
token stream and a second program emits that stream **one token at a time**.  Both programs
run under one polynomial clock.  The length emitter is load-bearing: a mere polynomial
*bound* on the extensional stream length would admit traders whose stopping length varies
uncomputably with `n`, and such a class could not be redundantly enumerated by the
construction's `TradingFirm`.

Emission is token-by-token rather than as one `Encodable.encode` numeral because of a hard
limit of the clocked interpreter, not as a stylistic choice: every `evaln` clause fuel-guards
its inputs (`guard (n ≤ k)` in `Mathlib.Computability.PartrecCode`), so a fixed program run
for `poly n` fuel can only *output* a value `≤ poly n` — `O(log n)` bits.

That claim is **proved**, not read off the source: `codeEvaln_result_le` with
`codeEvalBound_poly` (`Framework/Emission.lean`) bound a fixed code's output by an explicit
polynomial in the fuel; compose with the clock. Note it is *not* "output `≤ fuel`" — that is
false, and proved false (`evaln_output_can_exceed_fuel`, `Framework/Computable.lean`) — and
it does not follow from Mathlib's `evaln_bound`, which bounds the input only. A strategy
whose `Encodable.encode` is a large number (any poly-*size* but deep feature: its `toNat` value
is `2^{poly n}`) is therefore *unemittable as one number*, though the paper's poly-*size*
`def:ec` admits it. Emitting the `serializeTrades` stream token-by-token — polynomially many
`poly n`-value tokens (`serialize_length_le_cost` makes the stream length `Θ(size)`) — is the
faithful poly-*size* rendering, and it is what deep traders (`thm:con` hysteresis, `thm:nd`
purchase counters) need.

**Residual disclosure (type-`(c)`):** each token's *value* is generated by a clocked
program, so a traded sentence's atomic code `⌜φ⌝` must be `poly n`-value on day `n`. A trader
that always trades the same sentences pays a constant, absorbed into `a`; a trader whose
traded sentence varies with the day must carry a poly bound on `⌜φₙ⌝`. Two further layers
below remove the residual: `EfficientlyComputableDigit` meters token *bits* rather than
token values, and the Polish-notation layer replaces a sentence's single pair code by one
token per formula symbol, so that stream length tracks symbol count even for skewed
formulas. Their composite is the token-metered class `EfficientlyComputable`. -/

/-- Run a length program and then a token program under a shared clock.  The requested
length is clamped to the clock, so every index emits a polynomial-size stream even when its
length program returns a large paired numeral. -/
def clockedTokens (lengthCode tokenCode : Nat.Partrec.Code) (clock n : ℕ) : List ℕ :=
  match Nat.Partrec.Code.evaln clock lengthCode n with
  | none => []
  | some length => List.ofFn fun i : Fin (min length clock) =>
      (Nat.Partrec.Code.evaln clock tokenCode (Nat.pair n i)).getD 0

/-- Validate a serialized day-`n` strategy, including its rank discipline.  Malformed
streams denote the zero strategy. -/
def strategyOfTokens (n : ℕ) (tokens : List ℕ) : Strategy n :=
  match hdecode : deserializeTrades tokens with
  | none => ⟨[], by simp⟩
  | some trades =>
      if h : ∀ trade ∈ trades, trade.1.rank ≤ n then ⟨trades, h⟩ else ⟨[], by simp⟩

/-- The total trader denoted by two programs and a day-dependent clock. -/
def clockedTraderTok (lengthCode tokenCode : Nat.Partrec.Code) (clock : ℕ → ℕ) : Trader where
  strat n := strategyOfTokens n (clockedTokens lengthCode tokenCode (clock n) n)

/-- **The token-emission efficiency class** (`def:ec`, `dd:fuel`).  A trader is efficiently
computable at this layer when one program emits the length of the day-`n` strategy's flat
token stream and a second emits that stream one token at a time, both under a single
polynomial clock.  The residual this layer still carries — token *values* must be
polynomial in the day — is stated in the section block above and removed by
`EfficientlyComputableDigit`. -/
def EfficientlyComputableTok (Tr : Trader) : Prop :=
  ∃ (lengthCode tokenCode : Nat.Partrec.Code) (a k : ℕ),
    clockedTraderTok lengthCode tokenCode (fun n => a * (n + 1) ^ k + a) = Tr

/-! ### The digit layer (`dd:fuel` refinement)

`EfficientlyComputableTok` above emits the flat token stream one token per program call,
so each *token value* must be polynomial in the day — which excludes per-day rational
literals (`2^{-n}`) and deep/large sentence codes, though the paper's poly-*time* `def:ec`
admits them (the residual disclosed above). The digit layer removes that residual without
touching `serialize`/`cost`: every token is re-emitted as a **self-delimiting
base-4 digit block** (digits `0..3`, terminator `4`), so a `B`-bit token becomes `O(B)`
bounded-value digits. `EfficientlyComputableDigit` meters the digitized stream; poly
digit-stream length ⇔ poly *bit* size — the paper's accounting. -/

/-- Little-endian base-4 digits of `n` (empty for `0`). -/
def natDigits4 : ℕ → List ℕ
  | 0 => []
  | n + 1 => (n + 1) % 4 :: natDigits4 ((n + 1) / 4)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

/-- Every emitted digit is `< 4` (the terminator `4` never occurs inside a block). -/
lemma natDigits4_lt (n : ℕ) : ∀ d ∈ natDigits4 n, d < 4 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero => simp [natDigits4]
      | succ m =>
          rw [natDigits4]
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact Nat.mod_lt _ (by norm_num)
          · exact ih ((m + 1) / 4) (Nat.div_lt_self (Nat.succ_pos m) (by norm_num)) d hd

/-- One self-delimiting token block: the token's digits, then the terminator `4`. -/
def tokenBlock (t : ℕ) : List ℕ := natDigits4 t ++ [4]

/-- The digit stream of a token stream. -/
def digitize (ts : List ℕ) : List ℕ := ts.flatMap tokenBlock

lemma digitize_flatMap (l : List ℕ) (f : ℕ → List ℕ) :
    digitize (l.flatMap f) = l.flatMap fun x => digitize (f x) := by
  induction l with
  | nil => simp [digitize]
  | cons x rest ih =>
      simp only [digitize, List.flatMap_cons, List.flatMap_append] at ih ⊢
      rw [ih]

/-- Streaming inverse state step: `(finished tokens, block accumulator, place value)`.
Digits `< 4` accumulate little-endian; anything else closes the current block. -/
def undigitizeStep : List ℕ × ℕ × ℕ → ℕ → List ℕ × ℕ × ℕ
  | (out, acc, pow), d =>
      if d < 4 then (out, acc + d * pow, 4 * pow) else (out ++ [acc], 0, 1)

/-- Recover the token stream from a digit stream (complete blocks only). -/
def undigitize (ds : List ℕ) : List ℕ :=
  (ds.foldl undigitizeStep ([], 0, 1)).1

/-- Folding one digit list accumulates exactly its value at the current place. -/
lemma foldl_undigitizeStep_natDigits4 (n : ℕ) : ∀ (out : List ℕ) (acc pow : ℕ),
    List.foldl undigitizeStep (out, acc, pow) (natDigits4 n) =
      (out, acc + n * pow, 4 ^ (natDigits4 n).length * pow) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero => intro out acc pow; simp [natDigits4]
      | succ m =>
          intro out acc pow
          rw [natDigits4]
          simp only [List.foldl_cons, List.length_cons]
          rw [show undigitizeStep (out, acc, pow) ((m + 1) % 4) =
              (out, acc + (m + 1) % 4 * pow, 4 * pow) from
            if_pos (Nat.mod_lt _ (by norm_num)),
            ih ((m + 1) / 4) (Nat.div_lt_self (Nat.succ_pos m) (by norm_num))]
          simp only [Prod.mk.injEq]
          set r := (m + 1) % 4
          set q := (m + 1) / 4
          have h4 : r + 4 * q = m + 1 := Nat.mod_add_div (m + 1) 4
          exact ⟨trivial, by rw [← h4]; ring, by rw [pow_succ]; ring⟩

/-- Folding one complete token block appends exactly that token. -/
lemma foldl_undigitizeStep_tokenBlock (out : List ℕ) (t : ℕ) :
    List.foldl undigitizeStep (out, 0, 1) (tokenBlock t) = (out ++ [t], 0, 1) := by
  rw [tokenBlock, List.foldl_append, foldl_undigitizeStep_natDigits4]
  simp [undigitizeStep]

/-- **Digitization round-trips**: the digit stream determines the token stream.
Paper node: `def:ec` -/
lemma undigitize_digitize (ts : List ℕ) : undigitize (digitize ts) = ts := by
  suffices h : ∀ out, (List.foldl undigitizeStep (out, 0, 1) (digitize ts)).1 = out ++ ts by
    simpa [undigitize] using h []
  induction ts with
  | nil => intro out; simp [digitize]
  | cons t rest ih =>
      intro out
      rw [digitize, List.flatMap_cons, List.foldl_append,
        foldl_undigitizeStep_tokenBlock]
      rw [show (rest.flatMap tokenBlock) = digitize rest from rfl, ih]
      simp

/-- `digitize` is injective.
Paper node: `def:ec` -/
lemma digitize_injective : Function.Injective digitize := by
  intro a b h
  have := undigitize_digitize a
  rw [h, undigitize_digitize] at this
  exact this.symm

/-- The total trader denoted by two digit-emission programs and a day-dependent clock:
as `clockedTraderTok`, but the emitted stream is read through the digit layer. -/
def clockedTraderDigit (lengthCode tokenCode : Nat.Partrec.Code) (clock : ℕ → ℕ) : Trader where
  strat n :=
    strategyOfTokens n (undigitize (clockedTokens lengthCode tokenCode (clock n) n))

/-- `def:ec` (`dd:fuel`) — **digit-metered emission**. A trader is efficiently computable
in the digit model if one program emits the *digit-stream* length of the day-`n` strategy
and a second emits that stream one digit at a time, both under one polynomial clock.
Since every digit is `≤ 4`, the emitted-value constraint of the token model disappears:
poly digit-stream length is exactly poly *bit* size, the paper's `def:ec` accounting.
This class strictly contains `EfficientlyComputableTok` (inclusion lemma:
`EfficientlyComputableTok.toDigit`) and additionally admits per-day large rational
literals and deep sentence codes.
Paper node: `def:ec` -/
def EfficientlyComputableDigit (Tr : Trader) : Prop :=
  ∃ (lengthCode tokenCode : Nat.Partrec.Code) (a k : ℕ),
    clockedTraderDigit lengthCode tokenCode (fun n => a * (n + 1) ^ k + a) = Tr

/-! ### The Polish-notation serialization layer

Sentence slots of the flat strategy stream may carry Polish-notation symbol runs
instead of single pair-code tokens (one token per formula symbol, escape tag `1` for
a literal pair code).  The grammar defs live here beside the serializers; the lemma
corpus is `Framework/RpnSentence.lean`. -/

section
open LO.Propositional

/-- Polish-notation symbol run of a sentence (no escapes: the canonical form). -/
def rpn : Sentence → List ℕ
  | Formula.atom a => [a + 5]
  | Formula.falsum => [0]
  | Formula.and φ ψ => 3 :: (rpn φ ++ rpn ψ)
  | Formula.or φ ψ => 4 :: (rpn φ ++ rpn ψ)
  | Formula.imp φ ψ => 2 :: (rpn φ ++ rpn ψ)

/-! ### Structured arithmetic leaves

The escape prefix `[1, 0]` introduces an exact paper-prime atom.  Its
payload is a small-token prefix tree.  Tags `0`--`2` encode naturals in binary; tags
`3`--`8` encode arithmetic terms; and tags `9`--`18` together with `20`--`22`
encode arithmetic formulas: `9`--`18` are Foundation's negation-normal-form
constructors, and `20` (`¬`), `21` (`⟹`), `22` (`⟺`) are the paper's remaining
primitive connectives (tex:560), contracted into normal form by the parser.  The
numeric parser below deliberately constructs Foundation's established Godel code only
inside contraction.  In particular, the emitted stream never contains that code as a
token. -/

/-- The code of the two-element argument vector `![a, b]`, as a cons list. -/
public def arithmeticVec2Code (a b : ℕ) : ℕ :=
  Nat.pair a (Nat.pair b 0 + 1) + 1

/-- The code of a function-symbol term: symbol `symbol` of arity `arity` applied to the
argument vector coded by `args`. -/
public def arithmeticFuncCode (arity symbol args : ℕ) : ℕ :=
  Nat.pair 2 (Nat.pair arity (Nat.pair symbol args)) + 1

/-- The code of a binary atomic formula: `rel` when `negative` is `false` and `nrel` when
it is `true`, since Foundation's `Semiformula` is in negation-normal form. -/
public def arithmeticRelCode (negative : Bool) (symbol a b : ℕ) : ℕ :=
  Nat.pair (if negative then 1 else 0)
    (Nat.pair 2 (Nat.pair symbol (arithmeticVec2Code a b))) + 1

/-- Negation as a map on Foundation's arithmetic formula codes.  Foundation's
`Semiformula` is a negation-normal-form datatype, so `∼` is not a constructor: it is the
De Morgan involution that swaps the constructor tags `0↔1` (`rel`/`nrel`), `2↔3`
(`verum`/`falsum`), `4↔5` (`and`/`or`) and `6↔7` (`all`/`exs`), recursing into the
subcodes at the last two pairs.  This is the numeric mirror of that involution, used by
the structured parser to realize the paper's primitive `¬`, `⟹` and `⟺` (tex:560)
without those connectives ever being emitted as codes.

*Proof kind:* `Def`.  Its correctness against Foundation's `∼` is
`negFormulaCode_spec`. -/
public def negFormulaCode (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | e + 1 =>
      let a := e.unpair.1
      let c := e.unpair.2
      if a = 0 then Nat.pair 1 c + 1
      else if a = 1 then Nat.pair 0 c + 1
      else if a = 2 then Nat.pair 3 0 + 1
      else if a = 3 then Nat.pair 2 0 + 1
      else if a = 4 then
        Nat.pair 5 (Nat.pair (negFormulaCode c.unpair.1) (negFormulaCode c.unpair.2)) + 1
      else if a = 5 then
        Nat.pair 4 (Nat.pair (negFormulaCode c.unpair.1) (negFormulaCode c.unpair.2)) + 1
      else if a = 6 then Nat.pair 7 (negFormulaCode c) + 1
      else if a = 7 then Nat.pair 6 (negFormulaCode c) + 1
      else 0
decreasing_by
  all_goals
    simp_wf
    first
      | exact le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      | exact le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      | exact Nat.unpair_right_le _

/-! ### The structured-arithmetic parsers

The numeric mirror of the structural arithmetic codec.  The three mutually recursive
parsers each return an exact Foundation code together with the untouched suffix of the
token stream. -/

mutual
  /-- Parse a natural number written in the small-token binary encoding (tags `0`--`2`),
  returning its value and the remaining tokens. -/
  public def parseStructuredNat : ℕ → List ℕ → Option (ℕ × List ℕ)
    | 0, _ => none
    | _ + 1, [] => none
    | fuel + 1, t :: rest =>
        if t = 0 then some (0, rest)
        else if t = 1 then
          (parseStructuredNat fuel rest).map fun p => (2 * p.1, p.2)
        else if t = 2 then
          (parseStructuredNat fuel rest).map fun p => (2 * p.1 + 1, p.2)
        else none

  /-- Parse an arithmetic term (tags `3`--`8`), returning its Foundation term code and the
  remaining tokens.  The `depth` slot is fixed at `0` throughout and carries no
  information; it is retained because it appears in the statement of the lemma corpus in
  `Framework/RpnSentence.lean`. -/
  public def parseStructuredArithmeticTerm : ℕ → ℕ → List ℕ → Option (ℕ × List ℕ)
    | 0, _, _ => none
    | _ + 1, _, [] => none
    | fuel + 1, depth, t :: rest =>
        if t = 3 then
          (parseStructuredNat fuel rest).map fun p =>
            (Nat.pair 0 p.1 + 1, p.2)
        else if t = 4 then
          (parseStructuredNat fuel rest).map fun p => (Nat.pair 1 p.1 + 1, p.2)
        else if t = 5 then some (arithmeticFuncCode 0 0 0, rest)
        else if t = 6 then some (arithmeticFuncCode 0 1 0, rest)
        else if t = 7 ∨ t = 8 then
          (parseStructuredArithmeticTerm fuel 0 rest).bind fun p =>
            (parseStructuredArithmeticTerm fuel 0 p.2).map fun q =>
              (arithmeticFuncCode 2 (if t = 7 then 0 else 1)
                (arithmeticVec2Code p.1 q.1), q.2)
        else none

  /-- Parse an arithmetic formula (tags `9`--`18`, plus `20`--`22` for the paper's `¬`,
  `⟹`, `⟺`, contracted into negation-normal form here), returning its Foundation formula
  code and the remaining tokens.  The `depth` slot is fixed at `0` throughout and carries
  no information; it is retained because it appears in the statement of the lemma corpus in
  `Framework/RpnSentence.lean`. -/
  public def parseStructuredArithmeticFormula : ℕ → ℕ → List ℕ → Option (ℕ × List ℕ)
    | 0, _, _ => none
    | _ + 1, _, [] => none
    | fuel + 1, depth, t :: rest =>
        if t = 9 then some (Nat.pair 2 0 + 1, rest)
        else if t = 10 then some (Nat.pair 3 0 + 1, rest)
        else if t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 then
          (parseStructuredArithmeticTerm fuel 0 rest).bind fun p =>
            (parseStructuredArithmeticTerm fuel 0 p.2).map fun q =>
              (arithmeticRelCode (t = 12 ∨ t = 14) (if t = 11 ∨ t = 12 then 0 else 1)
                p.1 q.1, q.2)
        else if t = 15 ∨ t = 16 then
          (parseStructuredArithmeticFormula fuel 0 rest).bind fun p =>
            (parseStructuredArithmeticFormula fuel 0 p.2).map fun q =>
              (Nat.pair (if t = 15 then 4 else 5) (Nat.pair p.1 q.1) + 1, q.2)
        else if t = 17 ∨ t = 18 then
          (parseStructuredArithmeticFormula fuel 0 rest).map fun p =>
            (Nat.pair (if t = 17 then 6 else 7) p.1 + 1, p.2)
        else if t = 20 then
          (parseStructuredArithmeticFormula fuel 0 rest).map fun p =>
            (negFormulaCode p.1, p.2)
        else if t = 21 then
          (parseStructuredArithmeticFormula fuel 0 rest).bind fun p =>
            (parseStructuredArithmeticFormula fuel 0 p.2).map fun q =>
              (Nat.pair 5 (Nat.pair (negFormulaCode p.1) q.1) + 1, q.2)
        else if t = 22 then
          (parseStructuredArithmeticFormula fuel 0 rest).bind fun p =>
            (parseStructuredArithmeticFormula fuel 0 p.2).map fun q =>
              (Nat.pair 4
                (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode p.1) q.1) + 1)
                  (Nat.pair 5 (Nat.pair (negFormulaCode q.1) p.1) + 1)) + 1, q.2)
        else none
end

/-- Unary payload-length field.  Unary is intentional: every framing token stays small
even on malformed input, so grammar scanners retain polynomially bounded state. -/
def readStructuredLength : List ℕ → Option (ℕ × List ℕ)
  | 0 :: rest => some (0, rest)
  | 1 :: rest => (readStructuredLength rest).map fun p => (p.1 + 1, p.2)
  | _ => none

/-- Parse the tail of a `[1, 0, ...]` structured paper-prime escape.  After polarity,
`L` copies of `1` and a terminating `0` delimit exactly `L` payload symbols.  Token
`19`, the one value reserved out of the arithmetic codec alphabet
`0..18, 20..22`, closes the atomic block
for syntax-preserving streaming scanners. -/
def parseStructuredPaperPrime : List ℕ → Option (Sentence × List ℕ)
  | polarity :: framed =>
      if polarity ≤ 1 then
        (readStructuredLength framed).bind fun p =>
          if p.1 ≤ p.2.length then
            match parseStructuredArithmeticFormula p.1 0 (p.2.take p.1) with
            | some (formulaCode, []) =>
                if List.getD p.2 p.1 0 = 19 then
                  some (Formula.atom (Nat.pair 5 (Nat.pair polarity formulaCode)),
                    p.2.drop (p.1 + 1))
                else none
            | _ => none
          else none
      else none
  | [] => none

/-- Code-level result of the same structured leaf contraction. -/
def parseStructuredPaperPrimeC : List ℕ → Option (ℕ × List ℕ)
  | polarity :: framed =>
      if polarity ≤ 1 then
        (readStructuredLength framed).bind fun p =>
          if p.1 ≤ p.2.length then
            match parseStructuredArithmeticFormula p.1 0 (p.2.take p.1) with
            | some (formulaCode, []) =>
                if List.getD p.2 p.1 0 = 19 then
                  some (Nat.pair 1 (Nat.pair 5 (Nat.pair polarity formulaCode)) + 1,
                    p.2.drop (p.1 + 1))
                else none
            | _ => none
          else none
      else none
  | [] => none

/-- The unstructured RPN grammar: sentence blocks without the `[1, 0]` escape.
`Construction/Witnesses/RpnFreeze.lean` states the freeze recognizer against it
(`parseRpnLegacy_iff_patMatch`, `parseRpn_imp_parseRpnLegacy`). -/
def parseRpnLegacy : ℕ → List ℕ → Option (Sentence × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 0 then some (Formula.falsum, rest)
      else if t = 1 then
        rest.head?.bind fun c =>
          (Encodable.decode (α := Sentence) c).map fun φ => (φ, rest.tail)
      else if t = 2 then
        (parseRpnLegacy fuel rest).bind fun p =>
          (parseRpnLegacy fuel p.2).bind fun q => some (Formula.imp p.1 q.1, q.2)
      else if t = 3 then
        (parseRpnLegacy fuel rest).bind fun p =>
          (parseRpnLegacy fuel p.2).bind fun q => some (Formula.and p.1 q.1, q.2)
      else if t = 4 then
        (parseRpnLegacy fuel rest).bind fun p =>
          (parseRpnLegacy fuel p.2).bind fun q => some (Formula.or p.1 q.1, q.2)
      else some (Formula.atom (t - 5), rest)

/-- `parseRpn fuel ts` reads one sentence block from the front of `ts`, returning the
parsed sentence and the unread suffix.  Any `fuel ≥ ts.length` is enough. -/
def parseRpn : ℕ → List ℕ → Option (Sentence × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 0 then some (Formula.falsum, rest)
      else if t = 1 then
        match rest with
        | 0 :: payload => parseStructuredPaperPrime payload
        | c :: tail => (Encodable.decode (α := Sentence) c).map fun φ => (φ, tail)
        | [] => none
      else if t = 2 then
        (parseRpn fuel rest).bind fun p =>
          (parseRpn fuel p.2).bind fun q => some (Formula.imp p.1 q.1, q.2)
      else if t = 3 then
        (parseRpn fuel rest).bind fun p =>
          (parseRpn fuel p.2).bind fun q => some (Formula.and p.1 q.1, q.2)
      else if t = 4 then
        (parseRpn fuel rest).bind fun p =>
          (parseRpn fuel p.2).bind fun q => some (Formula.or p.1 q.1, q.2)
      else some (Formula.atom (t - 5), rest)

/-- Grammar-driven stream contraction: walk the flat strategy grammar and contract
each sentence block back to a single pair-code token; a failed block parse emits the
undecodable code `0` and stops, preserving rejection. -/
def unRpnTokens : ℕ → List ℕ → List ℕ
  | _, [] => []
  | 0, _ => []
  | fuel + 1, t :: rest =>
      if t = 0 then
        match parseRpn rest.length rest with
        | none => [0, 0]
        | some (φ, r1) =>
            match r1 with
            | [] => [0, Encodable.encode φ]
            | d :: r2 => 0 :: Encodable.encode φ :: d :: unRpnTokens fuel r2
      else if t = 6 then
        match parseRpn rest.length rest with
        | none => [6, 0]
        | some (φ, r1) => 6 :: Encodable.encode φ :: unRpnTokens fuel r1
      else if t = 1 then
        match rest with
        | [] => [1]
        | c :: r => 1 :: c :: unRpnTokens fuel r
      else if t = 7 then
        match rest with
        | [] => [7]
        | c :: r => 7 :: c :: unRpnTokens fuel r
      else t :: unRpnTokens fuel rest

/-- Contract every sentence block of a flat strategy stream to its pair code. -/
def unRpn (ts : List ℕ) : List ℕ := unRpnTokens ts.length ts

/-- The total trader denoted by two digit-emission programs under a day clock, with
Polish sentence blocks contracted before validation.
Paper node: `def:trader`, `def:ec` -/
def clockedTrader (lengthCode tokenCode : Nat.Partrec.Code) (clock : ℕ → ℕ) :
    Trader where
  strat n := strategyOfTokens n (unRpn (undigitize
    (clockedTokens lengthCode tokenCode (clock n) n)))

/-- **The token-metered efficient-computability class** (`def:ec`): two
programs under one polynomial clock emit the digit stream of an RPN-expanded strategy
serialization.  "Token" here counts emitted stream tokens, not the derivation symbols
`dSize` counts under `dd:symbolcount`.
Paper node: `def:ec` -/
def EfficientlyComputable (Tr : Trader) : Prop :=
  ∃ (lengthCode tokenCode : Nat.Partrec.Code) (a k : ℕ),
    clockedTrader lengthCode tokenCode (fun n => a * (n + 1) ^ k + a) = Tr

end

/-! ### The machine class (`def:ec`, machine reading)

`EfficientlyComputable` above renders `def:ec` through a fuel-clocked interpreter — a
sufficient certification device, and a disclosed modeling choice. The paper's own reading is
ordinary polynomial time, and this is it: a trader is efficient when some `Complexity.FP`
function of the *unary* day emits its day-`n` strategy through the standard token decoding.

Unary days matter: `unaryDay n` has length exactly `n`, so a machine polynomial in its input
length is polynomial in the day, which is the paper's meter. A binary rendering would
silently strengthen the class.

The output is a finite bit word rather than a giant numeral, read back three bits per digit.
No new parser is introduced: the decoding is `strategyOfTokens ∘ unRpn ∘ undigitize`, exactly
as in the fuel reading, with `bitsToDigits` the one adapter between the machine's `List Bool`
and the digit layer's `List ℕ`. -/

/-- The paper-faithful unary rendering of day `n`. -/
def unaryDay (n : ℕ) : List Bool := List.replicate n true

@[simp] lemma length_unaryDay (n : ℕ) : (unaryDay n).length = n := by simp [unaryDay]

/-- `Bool` as `0`/`1`. -/
def b2n (b : Bool) : ℕ := if b then 1 else 0

/-- One digit of the output stream: three bits, most significant first. -/
def digitAt (l : List Bool) (i : ℕ) : ℕ :=
  4 * b2n ((l[3 * i]?).getD false)
    + 2 * b2n ((l[3 * i + 1]?).getD false)
    + b2n ((l[3 * i + 2]?).getD false)

/-- Read a machine's output bitstring as a digit stream, three bits per digit, most
significant first; a trailing partial group is dropped.

It needs no validity side condition: groups with value `≥ 4` are exactly what
`undigitizeStep` already treats as block terminators, so *every* bitstring denotes some
digit stream, and malformed cases are absorbed downstream by `strategyOfTokens`. -/
def bitsToDigits (l : List Bool) : List ℕ :=
  (List.range (l.length / 3)).map (digitAt l)

@[simp] lemma length_bitsToDigits (l : List Bool) :
    (bitsToDigits l).length = l.length / 3 := by simp [bitsToDigits]

/-- Decode a machine's finite output word into the day-`n` strategy, through the existing
token pipeline. This is the only place the machine's output convention meets the trader
serialization, and it introduces no new parser. -/
def strategyOfOutput (n : ℕ) (w : List Bool) : Strategy n :=
  strategyOfTokens n (unRpn (undigitize (bitsToDigits w)))

/-- **The polynomial-time trader class** (`def:ec`, machine reading). A trader is
machine-efficient when some honestly polynomial-time function of the *unary* day emits its
day-`n` strategy through the standard token decoding.

This is the class the Logical Induction construction enumerates and dominates. Contrast
`EfficientlyComputable`, which asks for a fuel-clocked `Nat.Partrec.Code` pair; every trader
that certifies is one of these (`EfficientlyComputable.toMachine`, in
`Framework/MachineEfficiency.lean`), and the converse is neither needed nor claimed.
Paper node: `def:ec` -/
def MachineEfficientTrader (Tr : Trader) : Prop :=
  ∃ F : List Bool → List Bool, F ∈ Complexity.FP ∧
    ∀ n, strategyOfOutput n (F (unaryDay n)) = Tr.strat n

/-! ## `def:lic` — the criterion -/

/-- `def:lic`, in the fuel-certified reading.  The market `P` satisfies the **Logical
Induction Criterion** relative to `DP` if no efficiently computable trader exploits it,
where efficiency is the token-metered class `EfficientlyComputable` above.

**This is the compatibility reading, not the paper's quantifier.**  The paper's own
quantifier is ordinary machine polynomial time, and `IsMachineLogicalInductor`
(`Framework/MachineEfficiency.lean`) states it; that is the criterion the construction
proves.  Every fuel certificate is a machine-efficiency certificate
(`EfficientlyComputable.toMachine`), so `dd:fuel` is a *sufficient certification device*
for the machine class: a machine logical inductor is one of these, and the whole property
tail transfers unchanged through that instance.  The converse inclusion is
neither proved nor claimed; the `dd:fuel` model card (`Framework/Computable.lean`,
"### `dd:fuel` model card") records what is and is not settled.

This is the hypothesis the entire property tail is conditioned on
(`[IsLogicalInductor P DP]`).
Token-model and digit-model no-exploitation follow through the emission constructors
`EfficientlyComputable.ofTokenEmitter` / `.ofDigitEmitter`
(`IsLogicalInductor.noExploitTok` / `.noExploitDigit` in `Framework/RpnEmission.lean`).
Paper node: `def:lic` -/
class IsLogicalInductor (P : History) (DP : DeductiveProcess) : Prop where
  /-- Markets are computable rational pricing sequences in the paper's definition. -/
  marketComputable : ComputableMarket P
  /-- Deductive processes are computable nested finite-set sequences in the paper's
  definition. -/
  processComputable : ComputableDeductiveProcess DP
  /-- No efficiently computable trader exploits `P`, in the fuel-certified reading. The
  paper's own quantifier is the machine class: `IsMachineLogicalInductor` in
  `Framework/MachineEfficiency.lean` is that criterion, and it implies this one. -/
  noExploit : ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits P DP

/-- The pricing range carried by every logical inductor's computable-market certificate. -/
lemma IsLogicalInductor.price_mem_Icc
    {P : History} {DP : DeductiveProcess} [hLI : IsLogicalInductor P DP]
    (n : ℕ) (φ : Sentence) :
    0 ≤ P n φ ∧ P n φ ≤ 1 :=
  hLI.marketComputable.price_mem_Icc n φ

/-! ### Sanity / non-vacuity for the criterion machinery.

`Exploits` must be a genuinely refutable condition, not vacuously true — otherwise `def:lic`
would be empty. The do-nothing trader witnesses this: it never trades, so its net worth is
identically `0`, its plausible assessments lie in `{0}`, and it does **not** exploit. -/

/-- The trader that never trades. -/
def Trader.zero : Trader := ⟨fun _ => ⟨[], by simp⟩⟩

@[simp] lemma Trader.zero_netWorth (V : History) (v : PCWorld) (n : ℕ) :
    Trader.zero.netWorth V v n = 0 := by
  simp [Trader.netWorth, Trader.zero, Strategy.value]

/-- The do-nothing trader exploits nothing: `Exploits` is refutable, so the criterion is
not vacuous. -/
lemma Trader.zero_not_exploits (V : History) (DP : DeductiveProcess) :
    ¬ Trader.zero.Exploits V DP := by
  rintro ⟨_, hnab⟩
  refine hnab ⟨0, ?_⟩
  rintro x ⟨n, v, _, rfl⟩
  simp

end LogicalInduction
