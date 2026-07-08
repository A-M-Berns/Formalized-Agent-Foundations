/-
# Part I — Criterion (`LogicalInduction.Criterion`)

The expressible-feature DSL keystone, traders, and the Logical Induction Criterion. The
DSL is the keystone — invest disproportionately and add non-vacuity examples. Nodes
hosted here (see roadmap §3, Part I):

* `def:tf` (keystone) → `EF`, `EF.denote`, `EF.cost`, `instCommRing EF_n`. An inductive
  syntax over price features `pf φ`, `ℚ`, `+`, `×`, `max(·,·)`, safe reciprocation
  `max(1,·)⁻¹`, with two semantics:
    - `EF.denote : EF → (History → ℝ)` — continuous ℝ-valued; feeds Brouwer.
    - `EF.cost   : EF → ℕ` — syntactic size; an auxiliary bound on description size.
  `EF_n` (rank ≤ `n`) is a commutative ring. The continuity of `denote` is *stated* here;
  its proof may defer.
* `def:valfeature` → `ValuationFeature` — semantic target `EF.denote` lands in.
* `def:tradestrat` → `TradingStrategy` — affine combo `cash + Σ ef_i · φ_i`.
* `def:trader`     → `Trader` — sequence of `n`-strategies.
* `def:exploitation` → `Exploits` — plausible-world values bounded below, `sup = +∞`.
* `def:lic`        → `IsLogicalInductor` — "no e.c. trader exploits the market." The
  hypothesis the entire property tail is conditioned on.

Status (M1): the `def:tf` keystone is landed below (`EF`, `denote`, `cost`, `rank`, the
`CommRing` on rank-≤`n` features, continuity **proved**, non-vacuity witnesses). The
remaining Part-I criterion nodes (`ValuationFeature`, `TradingStrategy`, `Trader`,
`Exploits`, `IsLogicalInductor`) are still TODO in this milestone.
-/
import LogicalInduction.Foundations
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Rat.Encodable
import Foundation.Propositional.Boolean.Basic

namespace LogicalInduction

/-! ## `def:tf` — Expressible Features (the keystone)

A reified DSL (`dd:dsl`) with two semantics. The *syntax* `EF` is the object that carries
`cost` (for efficient computability) and `rank` (dependence horizon); the *denotation*
`EF.denote` is the continuous ℝ-valued feature the paper's algebra lives on. -/

/-- `def:tf` (Expressible Feature), as syntax. Built from price features `pf φ n`,
rational constants, `+`, `×`, `max(·,·)`, and the safe reciprocation `max(1,·)⁻¹`. -/
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
  deriving DecidableEq

namespace EF

/-- Continuous ℝ-valued semantics (`def:tf`). Feeds Brouwer via `continuous_denote`.
Noncomputable because safe reciprocation uses `ℝ`'s (noncomputable) inverse; efficient
computability is tracked syntactically by `cost`, not by running `denote`. -/
noncomputable def denote : EF → History → ℝ
  | price φ n,   V => V n φ
  | const q,     _ => (q : ℝ)
  | add a b,     V => a.denote V + b.denote V
  | mul a b,     V => a.denote V * b.denote V
  | max a b,     V => Max.max (a.denote V) (b.denote V)
  | safeRecip a, V => (Max.max 1 (a.denote V))⁻¹

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

/-- Rank = the latest day the feature inspects (`def:valfeature`); `EF_n` = rank ≤ `n`.
`const` inspects nothing (rank `0`); a binary node takes the `max` of its children. -/
def rank : EF → ℕ
  | price _ n   => n
  | const _     => 0
  | add a b     => Nat.max a.rank b.rank
  | mul a b     => Nat.max a.rank b.rank
  | max a b     => Nat.max a.rank b.rank
  | safeRecip a => a.rank

/-! ### `denote` is a ring map on the nose (all `rfl`), packaged for `simp`. -/

@[simp] theorem denote_price (φ : Sentence) (n : ℕ) :
    (price φ n).denote = fun V => V n φ := rfl

@[simp] theorem denote_const (q : ℚ) :
    (const q).denote = fun _ => (q : ℝ) := rfl

@[simp] theorem denote_add (a b : EF) : (add a b).denote = a.denote + b.denote := by
  funext V; simp [denote, Pi.add_apply]

@[simp] theorem denote_mul (a b : EF) : (mul a b).denote = a.denote * b.denote := by
  funext V; simp [denote, Pi.mul_apply]

@[simp] theorem denote_max (a b : EF) (V : History) :
    (max a b).denote V = Max.max (a.denote V) (b.denote V) := rfl

@[simp] theorem denote_safeRecip (a : EF) (V : History) :
    (safeRecip a).denote V = (Max.max 1 (a.denote V))⁻¹ := rfl

/-! ### Continuity (`def:tf`).  Discharged for the whole DSL rather than left as a
constraint — this is what breaks the price/trade circularity the paper needs for Brouwer.
Safe reciprocation is the only nontrivial case: `max 1 x ≥ 1 > 0`, so the reciprocal is
continuous with no removable singularity. -/

theorem continuous_denote (e : EF) : Continuous e.denote := by
  induction e with
  | price φ n => exact (continuous_apply φ).comp (continuous_apply n)
  | const q => exact continuous_const
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | max a b ha hb => exact ha.max hb
  | safeRecip a ha =>
      refine (continuous_const.max ha).inv₀ (fun V => ?_)
      have : (1 : ℝ) ≤ Max.max 1 (a.denote V) := le_max_left _ _
      positivity

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
  zero_mem' := ⟨const 0, by simp [rank], by funext V; simp [denote]⟩
  one_mem' := ⟨const 1, by simp [rank], by funext V; simp [denote]⟩
  add_mem' := by
    rintro f g ⟨ef, hf, rfl⟩ ⟨eg, hg, rfl⟩
    exact ⟨add ef eg, Nat.max_le.mpr ⟨hf, hg⟩, by simp⟩
  mul_mem' := by
    rintro f g ⟨ef, hf, rfl⟩ ⟨eg, hg, rfl⟩
    exact ⟨mul ef eg, Nat.max_le.mpr ⟨hf, hg⟩, by simp⟩
  neg_mem' := by
    rintro f ⟨ef, hf, rfl⟩
    refine ⟨mul (const (-1)) ef, by simpa [rank] using hf, ?_⟩
    funext V; simp [denote]

/-- `EF_n`: the rank-≤`n` expressible features. A commutative ring (`def:tf`). -/
abbrev EFn (n : ℕ) : Subring (History → ℝ) := ExpressibleRankLE n

/-- The required `CommRing EF_n` instance (`def:tf`), inherited from the ambient function
ring via the subring structure. -/
example (n : ℕ) : CommRing (EFn n) := inferInstance

theorem denote_mem_EFn (e : EF) : e.denote ∈ EFn e.rank := ⟨e, le_rfl, rfl⟩

/-! ### Non-vacuity witnesses (`def:tf`).  Concrete features with computed denotations,
so the DSL is not an empty shell. -/

/-- Non-vacuity 1 — the paper's running example (`def:tf`): `max(0, φ*6 − ψ*7)`.
Subtraction is sugar for `add a (mul (const (-1)) b)`. -/
def exMaxDiff (φ ψ : Sentence) : EF :=
  max (const 0) (add (price φ 6) (mul (const (-1)) (price ψ 7)))

/-- Its rank is `7`, matching the paper. -/
example (φ ψ : Sentence) : (exMaxDiff φ ψ).rank = 7 := by
  simp [exMaxDiff, rank]

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
provable (see `Computable.lean`). The encoding is still a genuine computable bijection, so
faithfulness of the poly-time e.c. class is unchanged. -/
def toNat : EF → ℕ
  | const q     => Nat.pair 0 (Encodable.encode q)
  | price φ n   => Nat.pair 1 (Nat.pair (Encodable.encode φ) n)
  | add a b     => Nat.pair 2 (Nat.pair a.toNat b.toNat)
  | mul a b     => Nat.pair 3 (Nat.pair a.toNat b.toNat)
  | max a b     => Nat.pair 4 (Nat.pair a.toNat b.toNat)
  | safeRecip a => Nat.pair 5 a.toNat

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
    | _ => none

/-- Decoder inverting `EF.toNat`, with fuel `m + 1` (always enough). -/
def ofNat (m : ℕ) : Option EF := ofNatAux (m + 1) m

/-- `Nat.pair t X > X` when the tag `t ≥ 1` — the strict decrease making children smaller. -/
private theorem lt_pair_tag (t X : ℕ) (ht : 0 < t) : X < Nat.pair t X :=
  lt_of_le_of_lt (Nat.right_le_pair 0 X) (Nat.pair_lt_pair_left X ht)

theorem ofNatAux_toNat : ∀ (fuel : ℕ) (e : EF), e.toNat < fuel → ofNatAux fuel e.toNat = some e := by
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

theorem ofNat_toNat (e : EF) : ofNat e.toNat = some e :=
  ofNatAux_toNat _ e (Nat.lt_succ_self _)

instance : Encodable EF := ⟨toNat, ofNat, ofNat_toNat⟩

/-! ### `EF.serialize` — a **flat, poly-size** token stream for the feature.

`toNat` (above) is a faithful *bijective* code, but its **value blows up doubly-exponentially
in tree depth** (`Nat.pair`-nesting squares the magnitude per level), so a size-`n`, depth-`n`
feature has a `2^{2^n}`-value `toNat` — a `4ⁿ`-*bit* number. Under the clocked interpreter a
fixed program run for `poly n` fuel can only *output* a `poly n`-**value** natural (every
`evaln` clause fuel-guards its inputs, so intermediates stay `≤ fuel`; see
`EfficientlyComputableTok`), i.e. `O(log n)` bits. So whole-number emission of `toNat` wrongly
excludes deep-but-poly-*size* features — the wall behind OPEN RISK 4.

`serialize` is the fix: a flat postfix (RPN) token stream whose **length is `Θ(node count)`**
(`serialize_length_le_cost`), so poly-*size* ⇔ poly-*length*, and whose individual tokens are
small (tags `0..5`, day indices, and the atomic sentence/constant codes). Efficient
computability (`EfficientlyComputableTok`) asks a program to emit this stream *one token at a
time* — polynomially many small tokens — which deep poly-size features admit. The stream is a
genuine encoding: `serialize_injective` (via the stack machine `readM`) shows it determines the
feature. -/
def serialize : EF → List ℕ
  | price φ n   => [0, Encodable.encode φ, n]
  | const q     => [1, Encodable.encode q]
  | add a b     => a.serialize ++ b.serialize ++ [2]
  | mul a b     => a.serialize ++ b.serialize ++ [3]
  | max a b     => a.serialize ++ b.serialize ++ [4]
  | safeRecip a => a.serialize ++ [5]

/-- `serialize`'s length is bounded by `3 · cost` — linear in the node count. This is the
whole point: poly-*size* (poly-`cost`) features have poly-*length* serializations, so
`EfficientlyComputableTok` admits them (unlike `toNat`, whose *value* is exponential). -/
theorem serialize_length_le_cost (e : EF) : (serialize e).length ≤ 3 * e.cost := by
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

end EF

/-! ## Flat serialization of strategies + unique decodability

A **strategy** is a `List (EF × Sentence)`; `serializeTrades` flattens it to a token stream by
concatenating each coefficient's `EF.serialize` followed by a trade-frame `[6, ⌜φ⌝]`. A single
stack machine `readM` decodes both features (tags `0..5`, pushing onto an `EF` stack) and trade
frames (tag `6`, popping a coefficient and recording the trade), which lets us prove both
`serialize` and `serializeTrades` injective from one roundtrip induction — the honesty guarantee
that the token stream `EfficientlyComputableTok` emits genuinely determines the strategy. -/

namespace EF

/-- The stack machine decoding a token stream. `efst` is the stack of features built so far;
`tr` accumulates decoded trades. Tags `0..5` build features (pushing); tag `6` reads a sentence
code and pops one feature to record a trade. Returns the final `(feature stack, trades)`. -/
def readM : List ℕ → List EF → List (EF × Sentence) → Option (List EF × List (EF × Sentence))
  | [], efst, tr => some (efst, tr)
  | (0 :: p1 :: p2 :: rest), efst, tr =>
      match (Encodable.decode p1 : Option Sentence) with
      | some φ => readM rest (price φ p2 :: efst) tr
      | none => none
  | (1 :: p :: rest), efst, tr =>
      match (Encodable.decode p : Option ℚ) with
      | some q => readM rest (const q :: efst) tr
      | none => none
  | (2 :: rest), (b :: a :: efst), tr => readM rest (add a b :: efst) tr
  | (3 :: rest), (b :: a :: efst), tr => readM rest (mul a b :: efst) tr
  | (4 :: rest), (b :: a :: efst), tr => readM rest (max a b :: efst) tr
  | (5 :: rest), (a :: efst), tr => readM rest (safeRecip a :: efst) tr
  | (6 :: p :: rest), (e :: efst), tr =>
      match (Encodable.decode p : Option Sentence) with
      | some φ => readM rest efst (tr ++ [(e, φ)])
      | none => none
  | _, _, _ => none

/-- Reading a feature's serialization pushes exactly that feature (for any stack/trade state).
The single roundtrip induction both `serialize` and `serializeTrades` injectivity rest on. -/
theorem readM_serialize (e : EF) : ∀ (rest : List ℕ) (efst : List EF)
    (tr : List (EF × Sentence)), readM (e.serialize ++ rest) efst tr = readM rest (e :: efst) tr := by
  induction e with
  | price φ n => intro rest efst tr; simp [serialize, readM, Encodable.encodek]
  | const q => intro rest efst tr; simp [serialize, readM, Encodable.encodek]
  | add a b iha ihb => intro rest efst tr
                       simp only [serialize, List.append_assoc, List.cons_append,
                         List.nil_append]
                       rw [iha, ihb]; simp only [readM]
  | mul a b iha ihb => intro rest efst tr
                       simp only [serialize, List.append_assoc, List.cons_append,
                         List.nil_append]
                       rw [iha, ihb]; simp only [readM]
  | max a b iha ihb => intro rest efst tr
                       simp only [serialize, List.append_assoc, List.cons_append,
                         List.nil_append]
                       rw [iha, ihb]; simp only [readM]
  | safeRecip a iha => intro rest efst tr
                       simp only [serialize, List.append_assoc, List.cons_append,
                         List.nil_append]
                       rw [iha]; simp only [readM]

/-- Decode a lone feature: accept iff the machine ends with a single feature and no trades. -/
def deserialize (toks : List ℕ) : Option EF :=
  match readM toks [] [] with
  | some ([e], []) => some e
  | _ => none

theorem deserialize_serialize (e : EF) : deserialize e.serialize = some e := by
  unfold deserialize
  rw [← List.append_nil e.serialize, readM_serialize]
  simp only [readM]

/-- **`serialize` is injective** — the token stream determines the feature. -/
theorem serialize_injective : Function.Injective serialize := by
  intro a b h
  have ha := deserialize_serialize a
  rw [h, deserialize_serialize] at ha
  exact (Option.some.inj ha).symm

end EF

/-- Flatten a strategy to a token stream: each trade is its coefficient's `EF.serialize`
followed by the frame `[6, ⌜φ⌝]`. This is the object `EfficientlyComputableTok` requires a
program to emit token-by-token. -/
def serializeTrades : List (EF × Sentence) → List ℕ
  | [] => []
  | (e, φ) :: rest => e.serialize ++ (6 :: Encodable.encode φ :: serializeTrades rest)

/-- Reading a strategy's serialization records exactly its trades (onto any state). -/
theorem readM_serializeTrades (l : List (EF × Sentence)) : ∀ (rest : List ℕ) (efst : List EF)
    (tr : List (EF × Sentence)),
    EF.readM (serializeTrades l ++ rest) efst tr = EF.readM rest efst (tr ++ l) := by
  induction l with
  | nil => intro rest efst tr; simp [serializeTrades]
  | cons t rest_l ih =>
      obtain ⟨e, φ⟩ := t
      intro rest efst tr
      simp only [serializeTrades, List.append_assoc, List.cons_append]
      rw [EF.readM_serialize]
      simp only [EF.readM, Encodable.encodek]
      rw [ih, List.append_assoc]
      rfl

/-- Decode a strategy: accept iff the machine ends with an empty feature stack. -/
def deserializeTrades (toks : List ℕ) : Option (List (EF × Sentence)) :=
  match EF.readM toks [] [] with
  | some ([], l) => some l
  | _ => none

theorem deserializeTrades_serializeTrades (l : List (EF × Sentence)) :
    deserializeTrades (serializeTrades l) = some l := by
  unfold deserializeTrades
  rw [← List.append_nil (serializeTrades l), readM_serializeTrades]
  simp only [EF.readM, List.nil_append]

/-- **`serializeTrades` is injective** — the token stream determines the strategy. -/
theorem serializeTrades_injective : Function.Injective serializeTrades := by
  intro a b h
  have ha := deserializeTrades_serializeTrades a
  rw [h, deserializeTrades_serializeTrades] at ha
  exact (Option.some.inj ha).symm

/-! ## `def:world` + Propositional Consistency

A world (`def:world`) is a truth assignment `Sentence → 𝔹`. The only worlds the criterion
quantifies over are the **propositionally consistent** ones (`def:pc`): those determined by
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

/-! ## `def:dedproc` — Deductive Process -/

/-- `def:dedproc`. A nested sequence `D 0 ⊆ D 1 ⊆ ⋯` of finite sets of sentences,
interpreted as the theorems revealed by day `n`.

Modeling note (disclosed type-`(c)`): the paper additionally requires `D` to be
*computable*. We do not carry a computability witness in the type; the criterion's
statement quantifies over traders, not over `D`, so it is unaffected, and computability of
`D` re-enters only in the construction (Part IV). -/
structure DeductiveProcess where
  /-- The sentences revealed by day `n`. -/
  D : ℕ → Finset Sentence
  /-- The revealed sets are nondecreasing. -/
  mono : ∀ n, D n ⊆ D (n + 1)

/-! ## `def:tradestrat`, `def:trader` — Trading strategies and traders

An `n`-strategy (`def:tradestrat`) is the paper's canonical encoding: a finite list of
`(coefficient, sentence)` pairs `(eᵢ, φᵢ)` with each `eᵢ` an expressible feature of rank
`≤ n`. It denotes `∑ᵢ eᵢ · (φᵢ − φᵢ*ⁿ)` — "buy `eᵢ(𝓥)` shares of `φᵢ` at the day-`n`
price", the cash term being determined by the pairs. -/

/-- `def:tradestrat`. A trading strategy for day `n`. -/
structure Strategy (n : ℕ) where
  /-- The `(expressible-feature coefficient, sentence)` pairs `(eᵢ, φᵢ)`. -/
  trades : List (EF × Sentence)
  /-- Every coefficient has rank `≤ n` (the strategy sees only prices up to day `n`). -/
  rank_le : ∀ p ∈ trades, p.1.rank ≤ n

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

end Strategy

/-- `def:trader`. A sequence of trading strategies, one per day. -/
structure Trader where
  /-- The strategy the trader plays on day `n`. -/
  strat : (n : ℕ) → Strategy n

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
theorem evaln_const_self : ∀ (K n : ℕ),
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

/-- `def:ec` (`dd:fuel`) — **whole-number clocked model. SUPERSEDED by
`EfficientlyComputableTok`** (below); no longer the definition `IsLogicalInductor` uses. Kept
because its statement is true and its certification pipeline (`EfficientlyComputable.of_fueled`,
`ec_of_polyEF`, …) is sound — but it is **faithful only for bounded-depth traders**: it asks a
program to output the day-`n` strategy's `Encodable.encode` *as one number*, and that number's
value is `2^{poly n}` for a deep poly-size feature, unemittable in `evaln (poly n)`. That is
OPEN RISK 4; the fix is the token-indexed `EfficientlyComputableTok`. A trader is (Val-)e.c. if a
program `c`, run on input `n` for a *polynomial* fuel budget `a·(n+1)ᵏ + a`, outputs the encoded
day-`n` strategy. -/
def EfficientlyComputable (Tr : Trader) : Prop :=
  ∃ (c : Nat.Partrec.Code) (a k : ℕ),
    ∀ n, Nat.Partrec.Code.evaln (a * (n + 1) ^ k + a) c n
        = some (Encodable.encode (Tr.strat n).trades)

/-- `def:ec` (`dd:fuel`) — **token-indexed emission, the poly-*size* model**. A trader is
**efficiently computable** if a single program `c` emits the day-`n` strategy's *flat token
stream* `serializeTrades (strat n)` **one token at a time**: run on input `⟨n, i⟩` for a
polynomial fuel budget, `c` outputs the `i`-th token, and the stream has polynomially many
tokens.

This replaces whole-number emission of `Encodable.encode` (`EfficientlyComputable` above). The
reason is a hard limit of the clocked interpreter, not a stylistic choice: every `evaln` clause
fuel-guards its inputs (`guard (n ≤ k)` in `Mathlib.Computability.PartrecCode`), so a fixed
program run for `poly n` fuel can only *output* a value `≤ poly n` — `O(log n)` bits. A strategy
whose `Encodable.encode` is a large number (any poly-*size* but deep feature: its `toNat` value
is `2^{poly n}`) is therefore *unemittable as one number*, though the paper's poly-*size*
`def:ec` admits it. Emitting the `serializeTrades` stream token-by-token — polynomially many
`poly n`-value tokens (`serialize_length_le_cost` makes the stream length `Θ(size)`) — is the
faithful poly-*size* rendering, and it is what deep traders (`thm:con` hysteresis, `thm:nd`
purchase counters) need. See OPEN RISK 4 in `PROGRESS.md`.

**Residual disclosure (type-`(c)`):** each token's *value* is still `≤ poly n`, so a traded
sentence's atomic code `⌜φ⌝` must be `poly n`-value on day `n`. Fixed sentences (every current
trader) are constant, absorbed into `a`; varying-sentence traders already carry a poly bound on
`⌜φₙ⌝`. Formula-level sub-tokenization would remove even this and is a later refinement. -/
def EfficientlyComputableTok (Tr : Trader) : Prop :=
  ∃ (c : Nat.Partrec.Code) (a k : ℕ),
    (∀ n, (serializeTrades (Tr.strat n).trades).length ≤ a * (n + 1) ^ k + a) ∧
    ∀ n i, i < (serializeTrades (Tr.strat n).trades).length →
      Nat.Partrec.Code.evaln (a * (n + 1) ^ k + a) c (Nat.pair n i)
        = some ((serializeTrades (Tr.strat n).trades).getD i 0)

/-- `def:lic`. The market `P` satisfies the **Logical Induction Criterion** relative to
`DP` if no efficiently computable trader exploits it. This is the hypothesis the entire
property tail is conditioned on (`[IsLogicalInductor P DP]`). With the faithful
`EfficientlyComputableTok` above (the poly-*size*, token-indexed model — OPEN RISK 4
resolved), this is the paper's `def:lic` on the nose, and it now admits deep poly-size
exploiters (hysteresis, purchase counters) that the whole-number `EfficientlyComputable`
excluded. -/
class IsLogicalInductor (P : History) (DP : DeductiveProcess) : Prop where
  /-- No efficiently computable trader exploits `P`. -/
  noExploit : ∀ Tr : Trader, EfficientlyComputableTok Tr → ¬ Tr.Exploits P DP

/-! ### Sanity / non-vacuity for the criterion machinery.

`Exploits` must be a genuinely refutable condition, not vacuously true — otherwise `def:lic`
would be empty. The do-nothing trader witnesses this: it never trades, so its net worth is
identically `0`, its plausible assessments lie in `{0}`, and it does **not** exploit. -/

/-- The trader that never trades. -/
def Trader.zero : Trader := ⟨fun _ => ⟨[], by simp⟩⟩

@[simp] theorem Trader.zero_netWorth (V : History) (v : PCWorld) (n : ℕ) :
    Trader.zero.netWorth V v n = 0 := by
  simp [Trader.netWorth, Trader.zero, Strategy.value]

/-- The do-nothing trader exploits nothing: `Exploits` is refutable, so the criterion is
not vacuous. -/
theorem Trader.zero_not_exploits (V : History) (DP : DeductiveProcess) :
    ¬ Trader.zero.Exploits V DP := by
  rintro ⟨_, hnab⟩
  refine hnab ⟨0, ?_⟩
  rintro x ⟨n, v, _, rfl⟩
  simp

end LogicalInduction
