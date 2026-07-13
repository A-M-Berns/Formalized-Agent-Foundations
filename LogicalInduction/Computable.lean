/-
# Efficient-computability infrastructure (`dd:fuel`) — prec-free fuel combinators

Certifying that a *responsive* trader is efficiently computable (`def:ec`) means exhibiting a
`Nat.Partrec.Code` and a polynomial `evaln` fuel budget that reproduces the encoded day-`n`
strategy. The obstacle was fuel accounting through `Nat.pair` — but with the `Nat.pair`-tagged
`EF` encoding (`Criterion.lean`), the strategy-encoding function is a tree of the interpreter's
**prec-free** primitives (`const`/`left`/`right`/`pair`/`comp`), and for those `evaln` does not
decrement fuel: a single budget exceeding every intermediate value evaluates the whole tree.

This file packages that as a `Fueled c f b` predicate — "`c` computes `f` within `b n` fuel" —
closed under the primitives, so a trader's code is assembled compositionally and its fuel bound
falls out. Composing const/pair over a fixed template gives a bound polynomial in `n`, which is
exactly `EfficientlyComputable`. Faithfulness is untouched: this is the paper's poly-time
`def:ec`, only now with a tractable membership proof.
-/
import LogicalInduction.Criterion

namespace LogicalInduction

open Nat.Partrec.Code

/-- `c` computes `f` on every input `n` within `b n` fuel of the clocked interpreter. -/
def Fueled (c : Nat.Partrec.Code) (f : ℕ → ℕ) (b : ℕ → ℕ) : Prop :=
  ∀ n, evaln (b n) c n = some (f n)

theorem Fueled.mono {c : Nat.Partrec.Code} {f b b' : ℕ → ℕ}
    (h : Fueled c f b) (hb : ∀ n, b n ≤ b' n) : Fueled c f b' :=
  fun n => evaln_mono (hb n) (h n)

/-- Constant: `Code.const K` outputs `K` within `n + K + 1` fuel. -/
theorem fueled_const (K : ℕ) :
    Fueled (Nat.Partrec.Code.const K) (fun _ => K) (fun n => n + K + 1) :=
  fun n => evaln_const_self K n

/-- Left projection `n ↦ (unpair n).1`. -/
theorem fueled_left :
    Fueled Nat.Partrec.Code.left (fun n => n.unpair.1) (fun n => n + 1) := by
  intro n; show evaln (n + 1) Nat.Partrec.Code.left n = some n.unpair.1
  simp [evaln]

/-- Right projection `n ↦ (unpair n).2`. -/
theorem fueled_right :
    Fueled Nat.Partrec.Code.right (fun n => n.unpair.2) (fun n => n + 1) := by
  intro n; show evaln (n + 1) Nat.Partrec.Code.right n = some n.unpair.2
  simp [evaln]

/-- Successor `n ↦ n + 1`. -/
theorem fueled_succ :
    Fueled Nat.Partrec.Code.succ (fun n => n + 1) (fun n => n + 1) := by
  intro n; show evaln (n + 1) Nat.Partrec.Code.succ n = some (n + 1)
  simp [evaln]

/-- Pairing: `Code.pair` computes `Nat.pair (f n) (g n)` (a primitive — no `prec`, no fuel
decrement), so a shared budget `max (bf n) (bg n)` suffices. -/
theorem fueled_pair {cf cg : Nat.Partrec.Code} {f g bf bg : ℕ → ℕ}
    (hf : Fueled cf f bf) (hg : Fueled cg g bg) :
    Fueled (cf.pair cg) (fun n => Nat.pair (f n) (g n)) (fun n => max (bf n) (bg n)) := by
  intro n
  show evaln (max (bf n) (bg n)) (cf.pair cg) n = some (Nat.pair (f n) (g n))
  have hn : n < max (bf n) (bg n) := by
    have := evaln_bound (hf n); have := evaln_bound (hg n); omega
  obtain ⟨k, hk⟩ : ∃ k, max (bf n) (bg n) = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [hk]
  have hfn : evaln (k + 1) cf n = some (f n) := by
    rw [← hk]; exact evaln_mono (le_max_left _ _) (hf n)
  have hgn : evaln (k + 1) cg n = some (g n) := by
    rw [← hk]; exact evaln_mono (le_max_right _ _) (hg n)
  simp [evaln, Option.guard_eq_some', hfn, hgn, Seq.seq, Option.bind_eq_some_iff]
  omega

/-- Composition: `Code.comp cf cg` computes `f ∘ g`. The intermediate value `g n` is fed to
`cf`, so the budget is `max (bg n) (bf (g n))`. -/
theorem fueled_comp {cf cg : Nat.Partrec.Code} {f g bf bg : ℕ → ℕ}
    (hf : Fueled cf f bf) (hg : Fueled cg g bg) :
    Fueled (cf.comp cg) (fun n => f (g n)) (fun n => max (bg n) (bf (g n))) := by
  intro n
  show evaln (max (bg n) (bf (g n))) (cf.comp cg) n = some (f (g n))
  have hn : n < max (bg n) (bf (g n)) := by have := evaln_bound (hg n); omega
  obtain ⟨k, hk⟩ : ∃ k, max (bg n) (bf (g n)) = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [hk]
  have hgn : evaln (k + 1) cg n = some (g n) := by
    rw [← hk]; exact evaln_mono (le_max_left _ _) (hg n)
  have hfn : evaln (k + 1) cf (g n) = some (f (g n)) := by
    rw [← hk]; exact evaln_mono (le_max_right _ _) (hf (g n))
  have hb2 := evaln_bound (hf (g n))
  have hm2 := le_max_right (bg n) (bf (g n))
  simp [evaln, Option.guard_eq_some', hgn, hfn, Option.bind_eq_some_iff]
  omega

/-- Identity `n ↦ n`, built from `pair left right` (`Nat.pair (unpair n).1 (unpair n).2 = n`). -/
theorem fueled_id :
    Fueled (Nat.Partrec.Code.left.pair Nat.Partrec.Code.right) (fun n => n) (fun n => n + 1) := by
  have h := fueled_pair fueled_left fueled_right
  simpa [Nat.pair_unpair] using h.mono (fun n => by simp)

/-! ## Polynomial fuel bounds — the bridge to `EfficientlyComputable`

A `Fueled` bound built from the combinators over a fixed trader template is a fixed
composition, hence bounded by a polynomial in `n`. `IsPolyBounded` packages that, and
`EfficientlyComputable.of_fueled` turns a poly-bounded `Fueled` fact for the strategy-encoding
function into `def:ec`. -/

/-- `b` is bounded by a polynomial (in the `a·(n+1)ᵏ + a` normal form used by `def:ec`). -/
def IsPolyBounded (b : ℕ → ℕ) : Prop := ∃ a k : ℕ, ∀ n, b n ≤ a * (n + 1) ^ k + a

theorem IsPolyBounded.of_le {b b' : ℕ → ℕ} (h : IsPolyBounded b') (hb : ∀ n, b n ≤ b' n) :
    IsPolyBounded b := by
  obtain ⟨a, k, hk⟩ := h; exact ⟨a, k, fun n => (hb n).trans (hk n)⟩

theorem IsPolyBounded.linear (c : ℕ) : IsPolyBounded (fun n => n + c) :=
  ⟨c + 1, 1, fun n => by simp only [pow_one]; nlinarith⟩

theorem IsPolyBounded.max {b₁ b₂ : ℕ → ℕ} (h₁ : IsPolyBounded b₁) (h₂ : IsPolyBounded b₂) :
    IsPolyBounded (fun n => max (b₁ n) (b₂ n)) := by
  obtain ⟨a₁, k₁, hk₁⟩ := h₁
  obtain ⟨a₂, k₂, hk₂⟩ := h₂
  refine ⟨a₁ + a₂, Max.max k₁ k₂, fun n => max_le ((hk₁ n).trans ?_) ((hk₂ n).trans ?_)⟩
  · gcongr <;> omega
  · gcongr <;> omega

/-- Degree-2 growth of `Nat.pair`: `Nat.pair m n < (m + n + 1)²`. -/
theorem pair_lt_sq (m n : ℕ) : Nat.pair m n < (m + n + 1) ^ 2 :=
  (Nat.pair_lt_max_add_one_sq m n).trans_le (by gcongr; omega)

theorem IsPolyBounded.add_one {b : ℕ → ℕ} (h : IsPolyBounded b) :
    IsPolyBounded (fun n => b n + 1) := by
  obtain ⟨a, k, hk⟩ := h
  exact ⟨a + 1, k, fun n => by have := hk n; nlinarith [Nat.one_le_pow k (n + 1) (by omega)]⟩

/-- Degree-2 growth: `Nat.pair` of two poly-bounded functions is poly-bounded (degree
doubles). This is what makes a strategy-encoding function — a tree of `Nat.pair`s over `n`
and constants — polynomial. -/
theorem IsPolyBounded.pair {f g : ℕ → ℕ} (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded (fun n => Nat.pair (f n) (g n)) := by
  obtain ⟨a₁, k₁, hk₁⟩ := hf
  obtain ⟨a₂, k₂, hk₂⟩ := hg
  refine ⟨4 * (a₁ + a₂ + 1) ^ 2, 2 * Max.max k₁ k₂, fun n => ?_⟩
  set X := (n + 1) ^ (Max.max k₁ k₂) with hX
  have hXpos : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hf' : f n ≤ a₁ * X + a₁ := (hk₁ n).trans (by
    gcongr; exact Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hg' : g n ≤ a₂ * X + a₂ := (hk₂ n).trans (by
    gcongr; exact Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  have hsum : f n + g n + 1 ≤ 2 * (a₁ + a₂ + 1) * X := by nlinarith [hf', hg', hXpos]
  have hsq : (n + 1) ^ (2 * Max.max k₁ k₂) = X ^ 2 := by rw [hX, mul_comm, pow_mul]
  calc Nat.pair (f n) (g n)
      ≤ (f n + g n + 1) ^ 2 := le_of_lt (pair_lt_sq _ _)
    _ ≤ (2 * (a₁ + a₂ + 1) * X) ^ 2 := Nat.pow_le_pow_left hsum 2
    _ = 4 * (a₁ + a₂ + 1) ^ 2 * X ^ 2 := by ring
    _ ≤ 4 * (a₁ + a₂ + 1) ^ 2 * (n + 1) ^ (2 * Max.max k₁ k₂) + 4 * (a₁ + a₂ + 1) ^ 2 := by
        rw [hsq]; exact Nat.le_add_right _ _

/-- **The bridge.** A poly-bounded `Fueled` fact for a trader's strategy-encoding function is
exactly efficient computability (`def:ec`). -/
theorem EfficientlyComputable.of_fueled {Tr : Trader} {code : Nat.Partrec.Code} {b : ℕ → ℕ}
    (h : Fueled code (fun n => Encodable.encode (Tr.strat n).trades) b)
    (hb : IsPolyBounded b) : EfficientlyComputable Tr := by
  obtain ⟨a, k, hk⟩ := hb
  exact ⟨code, a, k, fun n => h.mono hk n⟩

/-! ## `PolyFueled` — the composable capstone

`PolyFueled c f` bundles `Fueled c f b` with `IsPolyBounded` of *both* `f` (the output size,
needed when a value is fed onward) and `b` (the fuel). It is closed under `const`, `id`,
`pair`, and `comp` with `succ` — enough to assemble any single-sentence responsive trader's
strategy-encoding function, so its efficient computability drops out. -/

/-- A code computes `f`, with both `f` and its fuel polynomially bounded. -/
def PolyFueled (c : Nat.Partrec.Code) (f : ℕ → ℕ) : Prop :=
  ∃ b, Fueled c f b ∧ IsPolyBounded f ∧ IsPolyBounded b

theorem PolyFueled.const (K : ℕ) : PolyFueled (Nat.Partrec.Code.const K) (fun _ => K) :=
  ⟨fun n => n + K + 1, fueled_const K, ⟨K, 0, fun n => by simp⟩, IsPolyBounded.linear (K + 1)⟩

theorem PolyFueled.id :
    PolyFueled (Nat.Partrec.Code.left.pair Nat.Partrec.Code.right) (fun n => n) :=
  ⟨fun n => n + 1, fueled_id, IsPolyBounded.linear 0, IsPolyBounded.linear 1⟩

theorem PolyFueled.pair {cf cg : Nat.Partrec.Code} {f g : ℕ → ℕ}
    (hf : PolyFueled cf f) (hg : PolyFueled cg g) :
    PolyFueled (cf.pair cg) (fun n => Nat.pair (f n) (g n)) := by
  obtain ⟨bf, hff, hpff, hpbf⟩ := hf
  obtain ⟨bg, hfg, hpfg, hpbg⟩ := hg
  exact ⟨fun n => max (bf n) (bg n), fueled_pair hff hfg, hpff.pair hpfg, hpbf.max hpbg⟩

/-- Composition with `succ` (`n ↦ f n + 1`) — the only `comp` a single-sentence trader's
encoding needs (the outer `succ` of the `List` cons). -/
theorem PolyFueled.succ_comp {cg : Nat.Partrec.Code} {g : ℕ → ℕ} (hg : PolyFueled cg g) :
    PolyFueled (Nat.Partrec.Code.succ.comp cg) (fun n => g n + 1) := by
  obtain ⟨bg, hfg, hpfg, hpbg⟩ := hg
  exact ⟨fun n => max (bg n) (g n + 1), fueled_comp fueled_succ hfg, hpfg.add_one,
    hpbg.max hpfg.add_one⟩

theorem EfficientlyComputable.of_polyFueled {Tr : Trader} {code : Nat.Partrec.Code}
    (h : PolyFueled code (fun n => Encodable.encode (Tr.strat n).trades)) :
    EfficientlyComputable Tr := by
  obtain ⟨b, hf, _, hpb⟩ := h
  exact EfficientlyComputable.of_fueled hf hpb

/-! ### A worked responsive trader: efficient computability, end to end.

`priceTrader φ` plays `[(φ*ⁿ, φ)]` on day `n` — its coefficient is the *price feature*
`price φ n`, so the strategy genuinely varies with `n` (unlike the constant `buyDaily`). We
assemble the code computing `n ↦ encode [(price φ n, φ)]` from `PolyFueled` primitives and
read off efficient computability — the first responsive trader certified under the faithful
`def:ec`, validating the whole pipeline. -/

/-- The trader playing the price feature `φ*ⁿ` on `φ` each day (a responsive trade). -/
def priceTrader (φ : Sentence) : Trader where
  strat n := { trades := [(EF.price φ n, φ)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp
                             subst hp; simp [EF.rank] }

/-! ### `PolyEF` — day-indexed feature templates with e.c. codes.

`PolyEF t` says the per-day code `n ↦ (t n).toNat` is poly-fueled. It is closed under the
`EF` constructors (leaves `const`/`price φ n`), so *any* feature template a property proof
builds — e.g. the responsive `max(0, c − φ*ⁿ)` buy-signal — is e.c. for free, and a
single-sentence responsive trader's efficient computability drops out via `ec_of_polyEF`. -/

/-- The per-day code of the template `t` is efficiently computable. -/
def PolyEF (t : ℕ → EF) : Prop := ∃ c, PolyFueled c (fun n => (t n).toNat)

theorem PolyEF.const (q : ℚ) : PolyEF (fun _ => EF.const q) :=
  ⟨_, PolyFueled.const (Nat.pair 0 (Encodable.encode q))⟩

theorem PolyEF.price (φ : Sentence) : PolyEF (fun n => EF.price φ n) :=
  ⟨_, (PolyFueled.const 1).pair ((PolyFueled.const (Encodable.encode φ)).pair PolyFueled.id)⟩

theorem PolyEF.add {a b : ℕ → EF} (ha : PolyEF a) (hb : PolyEF b) :
    PolyEF (fun n => EF.add (a n) (b n)) := by
  obtain ⟨_, hca⟩ := ha; obtain ⟨_, hcb⟩ := hb
  exact ⟨_, (PolyFueled.const 2).pair (hca.pair hcb)⟩

theorem PolyEF.mul {a b : ℕ → EF} (ha : PolyEF a) (hb : PolyEF b) :
    PolyEF (fun n => EF.mul (a n) (b n)) := by
  obtain ⟨_, hca⟩ := ha; obtain ⟨_, hcb⟩ := hb
  exact ⟨_, (PolyFueled.const 3).pair (hca.pair hcb)⟩

theorem PolyEF.max {a b : ℕ → EF} (ha : PolyEF a) (hb : PolyEF b) :
    PolyEF (fun n => EF.max (a n) (b n)) := by
  obtain ⟨_, hca⟩ := ha; obtain ⟨_, hcb⟩ := hb
  exact ⟨_, (PolyFueled.const 4).pair (hca.pair hcb)⟩

theorem PolyEF.safeRecip {a : ℕ → EF} (ha : PolyEF a) :
    PolyEF (fun n => EF.safeRecip (a n)) := by
  obtain ⟨_, hca⟩ := ha
  exact ⟨_, (PolyFueled.const 5).pair hca⟩

/-- A single-sentence responsive trader `[(t n, φ)]` with a `PolyEF` coefficient is
efficiently computable. -/
theorem ec_of_polyEF {t : ℕ → EF} (φ : Sentence) (ht : PolyEF t) {Tr : Trader}
    (hTr : ∀ n, (Tr.strat n).trades = [(t n, φ)]) : EfficientlyComputable Tr := by
  obtain ⟨_, hct⟩ := ht
  have hpf := PolyFueled.succ_comp
    ((hct.pair (PolyFueled.const (Encodable.encode φ))).pair (PolyFueled.const 0))
  have heq : (fun n => Nat.pair (Nat.pair (t n).toNat (Encodable.encode φ)) 0 + 1)
      = (fun n => Encodable.encode (Tr.strat n).trades) := by funext n; rw [hTr n]; rfl
  rw [heq] at hpf
  exact EfficientlyComputable.of_polyFueled hpf

theorem priceTrader_ec (φ : Sentence) : EfficientlyComputable (priceTrader φ) :=
  ec_of_polyEF φ (PolyEF.price φ) (fun _ => rfl)

/-- A single-trade trader `[(t n, φ n)]` whose **sentence also varies** with `n` is efficiently
computable, given that the sentence sequence's codes are poly-fueled (an *efficiently
computable sequence of sentences*, the paper's `𝓔𝓒`-sequence). This is what lets the
*sequence* form of Provability Induction certify its trader. -/
theorem ec_of_polyEF_seq {t : ℕ → EF} {φ : ℕ → Sentence} {cφ : Nat.Partrec.Code}
    (ht : PolyEF t) (hφ : PolyFueled cφ (fun n => Encodable.encode (φ n))) {Tr : Trader}
    (hTr : ∀ n, (Tr.strat n).trades = [(t n, φ n)]) : EfficientlyComputable Tr := by
  obtain ⟨_, hct⟩ := ht
  have hpf := PolyFueled.succ_comp ((hct.pair hφ).pair (PolyFueled.const 0))
  have heq : (fun n => Nat.pair (Nat.pair (t n).toNat (Encodable.encode (φ n))) 0 + 1)
      = (fun n => Encodable.encode (Tr.strat n).trades) := by funext n; rw [hTr n]; rfl
  rw [heq] at hpf
  exact EfficientlyComputable.of_polyFueled hpf

/-- Payoff: the responsive **buy-signal** coefficient `max(0, c − φ*ⁿ)` — the actual shape
the convergence / provability-induction property proofs use — is `PolyEF` in one line, so
any trader built from it is efficiently computable via `ec_of_polyEF`. -/
example (φ : Sentence) (c : ℚ) :
    PolyEF (fun n => EF.max (EF.const 0) (EF.add (EF.const c) (EF.mul (EF.const (-1))
      (EF.price φ n)))) :=
  (PolyEF.const 0).max ((PolyEF.const c).add ((PolyEF.const (-1)).mul (PolyEF.price φ)))

/-! ## Prec-fueled predecessor — the day-`(n-1)` price reference.

The single-day templates above (`PolyEF.price φ n`) suffice for accumulation traders, but the
**convergence arbitrage trader** (`thm:con`) is the first to reference *two consecutive days'*
prices — it must know the previous day's holding to close a position risk-free — so its
coefficient template contains `EF.price φ (n-1)`, whose encoding contains `n - 1 = Nat.pred n`.

`Nat.pred` is *the* canonical primitive-recursive function: it cannot be built from the
prec-free primitives (`const`/`succ`/`pair`/`comp`/`left`/`right`), so this is the one place we
must account `evaln` fuel through a genuine `Code.prec` — which *does* decrement fuel. We do it
once, here, and bound the cost by a degree-4 polynomial, so every multi-day-referencing trader
(convergence, moving-threshold expectation control, …) reuses `PolyEF.pricePred` for free. -/

/-- The core recursor: `prec zero (comp left right)` on `pair a m` returns `pred m`
(independent of the dummy `a`) — the `succ`-case `cg = comp left right` extracts the recursion
index `y` and ignores the recursive value. -/
def predAux : Nat.Partrec.Code := prec zero (comp left right)

/-- One unrolling of the `prec` recursion for `predAux` at `pair 0 (m+1)`, given the recursive
value `i` and the two guard bounds it produces. -/
theorem predAux_step (k m i : ℕ) (hg : Nat.pair 0 (m+1) ≤ k)
    (hrec : evaln k predAux (Nat.pair 0 m) = some i)
    (hg2 : Nat.pair 0 (Nat.pair m i) ≤ k) :
    evaln (k+1) predAux (Nat.pair 0 (m+1)) = some m := by
  have hmi : Nat.pair m i ≤ k := le_trans (Nat.right_le_pair 0 (Nat.pair m i)) hg2
  conv_lhs => rw [predAux, evaln]
  simp only [Nat.unpaired, Nat.unpair_pair, predAux] at hrec ⊢
  rw [hrec]
  simp only [evaln, Option.guard, Nat.unpair_pair]
  simp [hg, hg2, hmi]

/-- `predAux` computes `m ↦ pred m` on `pair 0 m` within a degree-4 fuel budget. The recursion
depth is `m` (each `prec` level decrements `evaln`'s fuel by one), and the dominant guard is the
`comp` call on `pair 0 (pair m (m-1))` — of size `≈ (2m)⁴` — hence the `32·(m+1)⁴` bound. -/
theorem predAux_evaln : ∀ (m F : ℕ), 32 * (m+1)^4 < F →
    evaln F predAux (Nat.pair 0 m) = some (m - 1) := by
  intro m
  induction m with
  | zero =>
      intro F hF
      obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by omega⟩
      rw [show Nat.pair 0 0 = 0 from rfl]
      simp [predAux, evaln, Nat.unpaired]
  | succ m ih =>
      intro F hF
      obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by omega⟩
      have hA : 32 * (m+2)^4 ≤ k := by
        have : (m+1+1) = m+2 := by ring
        rw [this] at hF; omega
      have hIH : evaln k predAux (Nat.pair 0 m) = some (m - 1) := by
        refine ih k ?_
        have h4 : (m+1)^4 < (m+2)^4 := by gcongr <;> omega
        omega
      refine predAux_step k m (m-1) ?hg hIH ?hg2
      case hg =>
        have h1 : Nat.pair 0 (m+1) < (m+2)^2 := by simpa using pair_lt_sq 0 (m+1)
        have h2 : (m+2)^2 ≤ (m+2)^4 := by gcongr <;> omega
        omega
      case hg2 =>
        have h1 : Nat.pair m (m-1) < (2*m+1)^2 := by
          calc Nat.pair m (m-1) < (m+(m-1)+1)^2 := pair_lt_sq m (m-1)
            _ ≤ (2*m+1)^2 := by gcongr <;> omega
        have h2 : Nat.pair 0 (Nat.pair m (m-1)) < ((2*m+1)^2)^2 := by
          calc Nat.pair 0 (Nat.pair m (m-1)) < (Nat.pair m (m-1) + 1)^2 := by
                simpa using pair_lt_sq 0 (Nat.pair m (m-1))
            _ ≤ ((2*m+1)^2)^2 := by gcongr; omega
        have h3 : ((2*m+1)^2)^2 ≤ 16 * (m+2)^4 := by
          have : ((2*m+1)^2)^2 = (2*m+1)^4 := by ring
          rw [this]; calc (2*m+1)^4 ≤ (2*m+4)^4 := by gcongr <;> omega
            _ = 16 * (m+2)^4 := by ring
        omega

/-- The one-argument predecessor code: feed `n` as the recursion variable via `pair 0 n`. -/
def predc : Nat.Partrec.Code :=
  comp predAux (pair (Nat.Partrec.Code.const 0) (left.pair right))

theorem predc_fueled : Fueled predc Nat.pred (fun n => 32*(n+1)^4 + n + 1) := by
  intro n
  have hgn : evaln (32*(n+1)^4+n+1) (pair (Nat.Partrec.Code.const 0) (left.pair right)) n
      = some (Nat.pair 0 n) :=
    evaln_mono (by show max (n+0+1) (n+1) ≤ 32*(n+1)^4+n+1; omega)
      ((fueled_pair (fueled_const 0) fueled_id) n)
  have hfn : evaln (32*(n+1)^4+n+1) predAux (Nat.pair 0 n) = some (Nat.pred n) := by
    have := predAux_evaln n (32*(n+1)^4+n+1) (by omega); rwa [Nat.sub_one] at this
  show evaln (32*(n+1)^4+n+1) predc n = some (Nat.pred n)
  rw [predc]
  generalize predAux = pa at hfn ⊢
  generalize (pair (Nat.Partrec.Code.const 0) (left.pair right)) = cg at hgn ⊢
  simp [evaln, Option.guard_eq_some', hgn, hfn, Option.bind_eq_some_iff]

/-- **The predecessor combinator.** `predc` computes `Nat.pred` with polynomial (degree-4) fuel
— the reusable e.c. primitive for day-`(n-1)` price references. -/
theorem predc_polyFueled : PolyFueled predc Nat.pred := by
  refine ⟨fun n => 32*(n+1)^4 + n + 1, predc_fueled,
    ⟨1, 1, fun n => by simp only [pow_one, one_mul, Nat.pred_eq_sub_one]; omega⟩,
    ⟨33, 4, fun n => ?_⟩⟩
  show 32*(n+1)^4 + n + 1 ≤ 33*(n+1)^4 + 33
  have hx : n+1 ≤ (n+1)^4 := Nat.le_self_pow (by norm_num) _
  omega

/-- The **previous-day** price feature `φ*⁽ⁿ⁻¹⁾` is an efficiently-computable template — the
piece the convergence arbitrage trader needs beyond the single-day `PolyEF.price`. -/
theorem PolyEF.pricePred (φ : Sentence) : PolyEF (fun n => EF.price φ (n-1)) := by
  have h := (PolyFueled.const 1).pair
    ((PolyFueled.const (Encodable.encode φ)).pair predc_polyFueled)
  have heq : (fun n => Nat.pair 1 (Nat.pair (Encodable.encode φ) (Nat.pred n)))
      = (fun n => (EF.price φ (n-1)).toNat) := by
    funext n; simp only [EF.toNat, Nat.pred_eq_sub_one]
  rw [heq] at h
  exact ⟨_, h⟩

/-! ## Token-indexed dispatch — emitting the `i`-th token of a fixed-length stream.

`EfficientlyComputableTok` asks for a program that, on input `⟨n, i⟩`, outputs the `i`-th token
of `serializeTrades (strat n)`. For every trader in the development the token stream has a
**fixed length** `L` (the strategy's tree shape is `n`-independent; only day-index tokens and
sentence codes vary with `n`), so the stream is `[t₀ n, …, t_{L-1} n]` with each `tⱼ`
poly-fueled. This section builds the one reusable tool for that shape:

* encode the tuple `⟨t₀ n, …, t_{L-1} n⟩` as the right-nested pair `pair (t₀ n) (pair … 0)`
  (`tupleEnc`), poly-fueled from the `tⱼ` (`tupleCode`);
* select index `i` by `left ∘ right^i` (`sel = comp left iterRight`), a single `prec` recursion
  on `i` — the analogue of `predc`, fuel bounded through the clocked interpreter;
* package the two into `ecTok_of_tokenList`, turning "the day-`n` stream is `ts.map (· n)` with
  each token poly-fueled" into `EfficientlyComputableTok`.

The one genuine `prec` fuel proof is `iterRight_evaln` (mirrors `predAux_evaln`). -/

/-- Spec: `right` iterated `i` times on `T` (`Nat.unpair · |>.2`). `sel`'s meaning. -/
def rightIterFn (T : ℕ) : ℕ → ℕ
  | 0 => T
  | (i + 1) => (rightIterFn T i).unpair.2

/-- Selection spec: the `i`-th component of the right-nested tuple headed at `T`. -/
def selFn (T i : ℕ) : ℕ := (rightIterFn T i).unpair.1

/-- Encode a list as a right-nested pair tuple `pair v₀ (pair v₁ (… 0))`. -/
def tupleEnc : List ℕ → ℕ
  | [] => 0
  | v :: vs => Nat.pair v (tupleEnc vs)

/-- Iterating `right` once more on `pair v T'` peels the head: `right^{i+1}(pair v T') = right^i T'`. -/
theorem rightIterFn_pair (v T' : ℕ) : ∀ i, rightIterFn (Nat.pair v T') (i + 1) = rightIterFn T' i := by
  intro i
  induction i with
  | zero => simp [rightIterFn, Nat.unpair_pair]
  | succ i ih => rw [rightIterFn, ih]; rw [rightIterFn]

/-- `right^i` on the all-zero tuple stays `0` (`unpair 0 = (0,0)`). -/
theorem rightIterFn_zero (i : ℕ) : rightIterFn 0 i = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => rw [rightIterFn, ih]; rfl

/-- **Selection correctness (pure spec).** `selFn (tupleEnc vs) i = vs.getD i 0`. -/
theorem selFn_tupleEnc (vs : List ℕ) (i : ℕ) : selFn (tupleEnc vs) i = vs.getD i 0 := by
  induction vs generalizing i with
  | nil => simp only [tupleEnc, selFn, rightIterFn_zero, List.getD_nil]; rfl
  | cons v vs ih =>
      cases i with
      | zero => simp [selFn, tupleEnc, rightIterFn, Nat.unpair_pair]
      | succ i => simp only [selFn, tupleEnc, rightIterFn_pair, List.getD_cons_succ]; exact ih i

/-- `iterRight = prec id (right ∘ right ∘ right)`: on `pair T i`, returns `right^i T`. The
`succ` step ignores the recursion index and the fixed `T`, applying one `right` to the previous
value — so `f(T, i+1) = right (f(T, i))`. -/
def iterRight : Nat.Partrec.Code :=
  Nat.Partrec.Code.prec (left.pair right) (comp right (comp right right))

/-- Index selection code: `sel (pair T i) = left (right^i T) = selFn T i`. -/
def sel : Nat.Partrec.Code := comp left iterRight

theorem rightIterFn_le (T i : ℕ) : rightIterFn T i ≤ T := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact le_trans (Nat.unpair_right_le _) ih

theorem pair_le_pair_right' (a : ℕ) {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) :
    Nat.pair a b₁ ≤ Nat.pair a b₂ := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact le_of_lt (Nat.pair_lt_pair_right a h)

theorem pair_le_pair_left' (b : ℕ) {a₁ a₂ : ℕ} (h : a₁ ≤ a₂) :
    Nat.pair a₁ b ≤ Nat.pair a₂ b := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact le_of_lt (Nat.pair_lt_pair_left b h)

/-- One unrolling of the `prec` recursion for `iterRight`. -/
theorem iterRight_step (T i r k : ℕ)
    (hrec : evaln k iterRight (Nat.pair T i) = some r)
    (hg1 : Nat.pair T (i + 1) ≤ k) (hg2 : Nat.pair T (Nat.pair i r) ≤ k) :
    evaln (k + 1) iterRight (Nat.pair T (i + 1)) = some r.unpair.2 := by
  have hir : Nat.pair i r ≤ k := le_trans (Nat.right_le_pair T (Nat.pair i r)) hg2
  have hr : r ≤ k := le_trans (Nat.right_le_pair i r) hir
  conv_lhs => rw [iterRight, evaln]
  simp only [Nat.unpaired, Nat.unpair_pair, iterRight] at hrec ⊢
  rw [hrec]
  simp only [evaln, Nat.unpair_pair]
  simp [hg1, hg2, hir, hr]

/-- **`iterRight` computes `right^i` with a polynomial fuel budget** (one genuine `prec`
recursion through the clocked interpreter; mirrors `predAux_evaln`). The dominant guard is
`pair T (pair i T)`, and the recursion depth is `i`, so the budget is degree-2 in `pair T i`. -/
theorem iterRight_evaln : ∀ (T i F : ℕ), Nat.pair T (Nat.pair i T) + i + 1 < F →
    evaln F iterRight (Nat.pair T i) = some (rightIterFn T i) := by
  intro T i
  induction i with
  | zero =>
      intro F hF
      obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by omega⟩
      have hg : Nat.pair T 0 ≤ k := by
        have h1 : Nat.pair T 0 ≤ Nat.pair T (Nat.pair 0 T) :=
          pair_le_pair_right' T (Nat.left_le_pair 0 T)
        omega
      have hTk : T ≤ k := le_trans (Nat.left_le_pair T 0) hg
      show evaln (k + 1) iterRight (Nat.pair T 0) = some (rightIterFn T 0)
      rw [iterRight, evaln]
      simp only [Nat.unpaired, Nat.unpair_pair, Nat.rec_zero, rightIterFn]
      simp [Seq.seq, hg, hTk, evaln, Nat.pair_unpair]
  | succ i ih =>
      intro F hF
      obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by omega⟩
      have hmono : Nat.pair T (Nat.pair i T) ≤ Nat.pair T (Nat.pair (i + 1) T) :=
        pair_le_pair_right' T (pair_le_pair_left' T (by omega))
      have hIH : evaln k iterRight (Nat.pair T i) = some (rightIterFn T i) := by
        refine ih k ?_; omega
      have hri : rightIterFn T i ≤ T := rightIterFn_le T i
      have hstep := iterRight_step T i (rightIterFn T i) k hIH ?_ ?_
      · rw [rightIterFn]; exact hstep
      · -- hg1 : pair T (i+1) ≤ k
        have : Nat.pair T (i + 1) ≤ Nat.pair T (Nat.pair (i + 1) T) :=
          pair_le_pair_right' T (Nat.left_le_pair (i + 1) T)
        omega
      · -- hg2 : pair T (pair i (rightIterFn T i)) ≤ k
        have hp : Nat.pair i (rightIterFn T i) ≤ Nat.pair (i + 1) T :=
          le_trans (pair_le_pair_left' _ (by omega)) (pair_le_pair_right' _ hri)
        have : Nat.pair T (Nat.pair i (rightIterFn T i)) ≤ Nat.pair T (Nat.pair (i + 1) T) :=
          pair_le_pair_right' T hp
        omega

/-! ### `sel` as a poly-fueled function, and `IsPolyBounded` closure under `+`. -/

theorem IsPolyBounded.add {b₁ b₂ : ℕ → ℕ} (h₁ : IsPolyBounded b₁) (h₂ : IsPolyBounded b₂) :
    IsPolyBounded (fun n => b₁ n + b₂ n) := by
  obtain ⟨a₁, k₁, hk₁⟩ := h₁; obtain ⟨a₂, k₂, hk₂⟩ := h₂
  refine ⟨a₁ + a₂, Max.max k₁ k₂, fun n => ?_⟩
  have e₁ : (n + 1) ^ k₁ ≤ (n + 1) ^ Max.max k₁ k₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e₂ : (n + 1) ^ k₂ ≤ (n + 1) ^ Max.max k₁ k₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have := hk₁ n; have := hk₂ n; nlinarith [e₁, e₂]

/-- `m.unpair.1` is poly-bounded (it is `≤ m`). -/
theorem isPolyBounded_fst : IsPolyBounded (fun m => m.unpair.1) :=
  (IsPolyBounded.linear 0).of_le (fun m => by simpa using Nat.unpair_left_le m)

theorem isPolyBounded_snd : IsPolyBounded (fun m => m.unpair.2) :=
  (IsPolyBounded.linear 0).of_le (fun m => by simpa using Nat.unpair_right_le m)

/-- `iterRight` as a `Fueled` fact on arbitrary input `m` (read as `pair m.1 m.2`). -/
theorem iterRight_fueled :
    Fueled iterRight (fun m => rightIterFn m.unpair.1 m.unpair.2)
      (fun m => Nat.pair m.unpair.1 (Nat.pair m.unpair.2 m.unpair.1) + m.unpair.2 + 2) := by
  intro m
  set T := m.unpair.1 with hT
  set i := m.unpair.2 with hi
  have hm : Nat.pair T i = m := Nat.pair_unpair m
  show evaln (Nat.pair T (Nat.pair i T) + i + 2) iterRight m = some (rightIterFn T i)
  rw [← hm]
  exact iterRight_evaln T i _ (by omega)

theorem isPolyBounded_iterRight_fuel :
    IsPolyBounded (fun m => Nat.pair m.unpair.1 (Nat.pair m.unpair.2 m.unpair.1) + m.unpair.2 + 2) :=
  ((isPolyBounded_fst.pair (isPolyBounded_snd.pair isPolyBounded_fst)).add
    isPolyBounded_snd).add (IsPolyBounded.linear 2 |>.of_le (fun _ => by omega))

/-- **`sel` computes `selFn` with polynomial fuel.** `sel = comp left iterRight`, so its output
is `(right^i T).unpair.1 = selFn T i` and its fuel is the `iterRight` budget plus one. -/
theorem sel_fueled :
    Fueled sel (fun m => selFn m.unpair.1 m.unpair.2)
      (fun m => Max.max (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 m.unpair.1) + m.unpair.2 + 2)
        (rightIterFn m.unpair.1 m.unpair.2 + 1)) :=
  fueled_comp fueled_left iterRight_fueled

theorem isPolyBounded_sel_fuel :
    IsPolyBounded (fun m => Max.max
      (Nat.pair m.unpair.1 (Nat.pair m.unpair.2 m.unpair.1) + m.unpair.2 + 2)
      (rightIterFn m.unpair.1 m.unpair.2 + 1)) :=
  isPolyBounded_iterRight_fuel.max
    ((isPolyBounded_fst.of_le (fun _ => rightIterFn_le _ _)).add_one)

/-- Composition of poly-bounded functions is poly-bounded — the missing closure needed to
compose `sel` with the tuple code. -/
theorem IsPolyBounded.comp {b g : ℕ → ℕ} (hb : IsPolyBounded b) (hg : IsPolyBounded g) :
    IsPolyBounded (fun n => b (g n)) := by
  obtain ⟨a, k, hk⟩ := hb
  obtain ⟨a', k', hk'⟩ := hg
  refine ⟨a * (2 * (a' + 1)) ^ k, k * k', fun n => ?_⟩
  have hp : 1 ≤ (n + 1) ^ k' := Nat.one_le_pow _ _ (by omega)
  have hstep : g n + 1 ≤ 2 * (a' + 1) * (n + 1) ^ k' := by
    have h1 : g n ≤ a' * (n + 1) ^ k' + a' := hk' n
    nlinarith [h1, hp]
  have hpow : 1 ≤ (2 * (a' + 1)) ^ k := Nat.one_le_pow _ _ (by omega)
  calc b (g n) ≤ a * (g n + 1) ^ k + a := hk (g n)
    _ ≤ a * (2 * (a' + 1) * (n + 1) ^ k') ^ k + a := by gcongr
    _ = a * (2 * (a' + 1)) ^ k * (n + 1) ^ (k * k') + a := by
        rw [mul_pow, ← pow_mul]; ring
    _ ≤ a * (2 * (a' + 1)) ^ k * (n + 1) ^ (k * k') + a * (2 * (a' + 1)) ^ k := by
        gcongr; exact Nat.le_mul_of_pos_right a hpow

theorem PolyFueled.left : PolyFueled Nat.Partrec.Code.left (fun m => m.unpair.1) :=
  ⟨fun n => n + 1, fueled_left, isPolyBounded_fst, IsPolyBounded.linear 1⟩

theorem PolyFueled.right : PolyFueled Nat.Partrec.Code.right (fun m => m.unpair.2) :=
  ⟨fun n => n + 1, fueled_right, isPolyBounded_snd, IsPolyBounded.linear 1⟩

/-- **`PolyFueled` is closed under composition.** Needs `IsPolyBounded.comp` for both the
output size `f ∘ g` and the fuel `bf ∘ g`. -/
theorem PolyFueled.comp {cf cg : Nat.Partrec.Code} {f g : ℕ → ℕ}
    (hf : PolyFueled cf f) (hg : PolyFueled cg g) :
    PolyFueled (cf.comp cg) (fun n => f (g n)) := by
  obtain ⟨bf, hff, hpff, hpbf⟩ := hf
  obtain ⟨bg, hfg, hpfg, hpbg⟩ := hg
  exact ⟨fun n => max (bg n) (bf (g n)), fueled_comp hff hfg,
    hpff.comp hpfg, hpbg.max (hpbf.comp hpfg)⟩

/-- `sel` bundled as `PolyFueled`. -/
theorem sel_polyFueled : PolyFueled sel (fun m => selFn m.unpair.1 m.unpair.2) :=
  ⟨_, sel_fueled, (isPolyBounded_fst.of_le (fun _ => le_trans (Nat.unpair_left_le _)
    (rightIterFn_le _ _))), isPolyBounded_sel_fuel⟩

/-! ### `ifzSel` — a branchless zero-test selector (toward varying-length emission).

`ifzSel (pair (pair A B) i) = if i = 0 then A else B`. The two candidates ride *in the input*
(`A = T.unpair.1`, `B = T.unpair.2` with `T = pair A B`), so the `prec` uses only projections
(`cf = left`, `cg = comp right left`) — no `const` in the recursion, so the fuel proof is as
cheap as `iterRight`'s. This is the bottleneck primitive for emitting a *growing* token stream:
the `i`-th token of a size-`Θ(n)` strategy is a fixed nesting of `ifzSel`s over `pred`-shifted
indices (comparisons against small constants), each poly-fuel. -/
def ifzSel : Nat.Partrec.Code := Nat.Partrec.Code.prec left (comp right left)

/-- Spec of `ifzSel`: pick `T.unpair.1` (`i = 0`) or `T.unpair.2` (`i > 0`). -/
def ifzSelFn (T i : ℕ) : ℕ := if i = 0 then T.unpair.1 else T.unpair.2

theorem ifzSelFn_le (T i : ℕ) : ifzSelFn T i ≤ T := by
  rw [ifzSelFn]; split
  · exact Nat.unpair_left_le T
  · exact Nat.unpair_right_le T

/-- One unrolling of the `prec` recursion for `ifzSel` (the `succ` step returns `T.unpair.2`
regardless of the recursive value — `cg = comp right left` ignores it). -/
theorem ifzSel_step (T i r k : ℕ)
    (hrec : evaln k ifzSel (Nat.pair T i) = some r)
    (hg1 : Nat.pair T (i + 1) ≤ k) (hg2 : Nat.pair T (Nat.pair i r) ≤ k) :
    evaln (k + 1) ifzSel (Nat.pair T (i + 1)) = some T.unpair.2 := by
  have hTle : T ≤ k := le_trans (Nat.left_le_pair T (Nat.pair i r)) hg2
  conv_lhs => rw [ifzSel, evaln]
  simp only [Nat.unpaired, Nat.unpair_pair, ifzSel] at hrec ⊢
  rw [hrec]
  simp only [evaln, Nat.unpair_pair]
  simp [hg1, hg2, hTle]

/-- **`ifzSel` computes the zero-test selection with polynomial fuel** (mirrors
`iterRight_evaln`: same `prec`-with-projections shape, same degree-2 budget). -/
theorem ifzSel_evaln : ∀ (T i F : ℕ), Nat.pair T (Nat.pair i T) + i + 1 < F →
    evaln F ifzSel (Nat.pair T i) = some (ifzSelFn T i) := by
  intro T i
  induction i with
  | zero =>
      intro F hF
      obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by omega⟩
      have hg : Nat.pair T 0 ≤ k := by
        have h1 : Nat.pair T 0 ≤ Nat.pair T (Nat.pair 0 T) :=
          pair_le_pair_right' T (Nat.left_le_pair 0 T)
        omega
      have hTk : T ≤ k := le_trans (Nat.left_le_pair T 0) hg
      show evaln (k + 1) ifzSel (Nat.pair T 0) = some (ifzSelFn T 0)
      rw [ifzSel, evaln]
      simp only [Nat.unpaired, Nat.unpair_pair, Nat.rec_zero, ifzSelFn, if_pos rfl]
      simp [hg, hTk, evaln]
  | succ i ih =>
      intro F hF
      obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by omega⟩
      have hmono : Nat.pair T (Nat.pair i T) ≤ Nat.pair T (Nat.pair (i + 1) T) :=
        pair_le_pair_right' T (pair_le_pair_left' T (by omega))
      have hIH : evaln k ifzSel (Nat.pair T i) = some (ifzSelFn T i) := by
        refine ih k ?_; omega
      have hri : ifzSelFn T i ≤ T := ifzSelFn_le T i
      have hstep := ifzSel_step T i (ifzSelFn T i) k hIH ?_ ?_
      · rw [ifzSelFn, if_neg (Nat.succ_ne_zero i)]; exact hstep
      · have : Nat.pair T (i + 1) ≤ Nat.pair T (Nat.pair (i + 1) T) :=
          pair_le_pair_right' T (Nat.left_le_pair (i + 1) T)
        omega
      · have hp : Nat.pair i (ifzSelFn T i) ≤ Nat.pair (i + 1) T :=
          le_trans (pair_le_pair_left' _ (by omega)) (pair_le_pair_right' _ hri)
        have : Nat.pair T (Nat.pair i (ifzSelFn T i)) ≤ Nat.pair T (Nat.pair (i + 1) T) :=
          pair_le_pair_right' T hp
        omega

theorem ifzSel_fueled :
    Fueled ifzSel (fun m => ifzSelFn m.unpair.1 m.unpair.2)
      (fun m => Nat.pair m.unpair.1 (Nat.pair m.unpair.2 m.unpair.1) + m.unpair.2 + 2) := by
  intro m
  set T := m.unpair.1 with hT
  set i := m.unpair.2 with hi
  have hm : Nat.pair T i = m := Nat.pair_unpair m
  show evaln (Nat.pair T (Nat.pair i T) + i + 2) ifzSel m = some (ifzSelFn T i)
  rw [← hm]
  exact ifzSel_evaln T i _ (by omega)

theorem ifzSel_polyFueled : PolyFueled ifzSel (fun m => ifzSelFn m.unpair.1 m.unpair.2) :=
  ⟨_, ifzSel_fueled,
    isPolyBounded_fst.of_le (fun m => ifzSelFn_le m.unpair.1 m.unpair.2),
    isPolyBounded_iterRight_fuel⟩

/-! ### `ecTok_of_tokenList` — the re-certification workhorse.

A trader whose day-`n` token stream is a **fixed-length** list `ts.map (· n)` of poly-fueled
tokens is `EfficientlyComputableTok`. The emitter is `comp sel ((comp cV left).pair right)`:
on `⟨n, i⟩` it builds the tuple `⟨t₀ n, …⟩` (`cV`), then selects index `i` (`sel`). -/

/-- The day-`n` tuple `⟨t₀ n, …, t_{L-1} n⟩` is poly-fueled (built from the tokens by `pair`). -/
def PolyFueledTuple (ts : List (ℕ → ℕ)) : Prop :=
  ∃ c, PolyFueled c (fun n => tupleEnc (ts.map (fun t => t n)))

theorem PolyFueledTuple.nil : PolyFueledTuple [] :=
  ⟨Nat.Partrec.Code.const 0, by simpa [tupleEnc] using PolyFueled.const 0⟩

theorem PolyFueledTuple.cons {t : ℕ → ℕ} {ts : List (ℕ → ℕ)} {ct : Nat.Partrec.Code}
    (ht : PolyFueled ct t) (hts : PolyFueledTuple ts) : PolyFueledTuple (t :: ts) := by
  obtain ⟨cs, hcs⟩ := hts
  refine ⟨ct.pair cs, ?_⟩
  have heq : (fun n => tupleEnc ((t :: ts).map (fun t => t n)))
      = (fun n => Nat.pair (t n) (tupleEnc (ts.map (fun t => t n)))) := by
    funext n; simp [tupleEnc]
  rw [heq]; exact ht.pair hcs

/-- **The token-emission re-certification lemma.** If the day-`n` strategy serializes to a
fixed-length list `ts.map (· n)` of poly-fueled tokens, the trader is `EfficientlyComputableTok`. -/
theorem ecTok_of_tokenList (Tr : Trader) (ts : List (ℕ → ℕ)) (hts : PolyFueledTuple ts)
    (hTr : ∀ n, serializeTrades (Tr.strat n).trades = ts.map (fun t => t n)) :
    EfficientlyComputableTok Tr := by
  obtain ⟨cV, hV⟩ := hts
  set c := Nat.Partrec.Code.comp sel
      ((Nat.Partrec.Code.comp cV Nat.Partrec.Code.left).pair Nat.Partrec.Code.right) with hc
  -- The full emitter, as a PolyFueled fact.
  have hcode : PolyFueled c
      (fun m => selFn (Nat.pair
        (tupleEnc (ts.map (fun t => t m.unpair.1))) m.unpair.2).unpair.1
        (Nat.pair (tupleEnc (ts.map (fun t => t m.unpair.1))) m.unpair.2).unpair.2) :=
    sel_polyFueled.comp ((hV.comp PolyFueled.left).pair PolyFueled.right)
  obtain ⟨bc, hfc, _, hpbc⟩ := hcode
  obtain ⟨a₀, k₀, hk₀⟩ := hpbc
  -- Length of the stream is the constant `ts.length`.
  have hlen : ∀ n, (serializeTrades (Tr.strat n).trades).length = ts.length := by
    intro n; rw [hTr n, List.length_map]
  -- The polynomial fuel: coefficient absorbs the `(L+1)^{2k₀}` blow-up, plus `L` for the
  -- length clause; degree `2k₀` from `pair n i < (n+L+1)²`.
  set A := a₀ * (ts.length + 1) ^ (2 * k₀) + a₀ + ts.length with hA
  refine ⟨c, A, 2 * k₀, ?_, ?_⟩
  · intro n; rw [hlen n]
    have : ts.length ≤ A := by rw [hA]; omega
    exact le_trans this (Nat.le_add_left _ _)
  · intro n i hi
    rw [hlen n] at hi
    -- The emitter outputs the i-th token at input ⟨n, i⟩.
    have hout : selFn (tupleEnc (ts.map (fun t => t n))) i
        = (serializeTrades (Tr.strat n).trades).getD i 0 := by
      rw [selFn_tupleEnc, hTr n]
    -- `bc ⟨n,i⟩` is bounded by the chosen polynomial (uses `i < ts.length`).
    have hbc : bc (Nat.pair n i) ≤ A * (n + 1) ^ (2 * k₀) + A := by
      have h1 : Nat.pair n i + 1 ≤ (n + ts.length + 1) ^ 2 := by
        have hlt := pair_lt_sq n i
        have hle : (n + i + 1) ^ 2 ≤ (n + ts.length + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega
      have h2 : (Nat.pair n i + 1) ^ k₀ ≤ (n + ts.length + 1) ^ (2 * k₀) := by
        calc (Nat.pair n i + 1) ^ k₀ ≤ ((n + ts.length + 1) ^ 2) ^ k₀ :=
              Nat.pow_le_pow_left h1 k₀
          _ = (n + ts.length + 1) ^ (2 * k₀) := by rw [← pow_mul]
      have h4 : n + ts.length + 1 ≤ (n + 1) * (ts.length + 1) := by nlinarith
      have h5 : (n + ts.length + 1) ^ (2 * k₀) ≤
          (n + 1) ^ (2 * k₀) * (ts.length + 1) ^ (2 * k₀) := by
        calc (n + ts.length + 1) ^ (2 * k₀) ≤ ((n + 1) * (ts.length + 1)) ^ (2 * k₀) :=
              Nat.pow_le_pow_left h4 _
          _ = (n + 1) ^ (2 * k₀) * (ts.length + 1) ^ (2 * k₀) := by rw [mul_pow]
      calc bc (Nat.pair n i) ≤ a₀ * (Nat.pair n i + 1) ^ k₀ + a₀ := hk₀ (Nat.pair n i)
        _ ≤ a₀ * ((n + 1) ^ (2 * k₀) * (ts.length + 1) ^ (2 * k₀)) + a₀ := by
            gcongr; exact le_trans h2 h5
        _ = (a₀ * (ts.length + 1) ^ (2 * k₀)) * (n + 1) ^ (2 * k₀) + a₀ := by ring
        _ ≤ A * (n + 1) ^ (2 * k₀) + A := by rw [hA]; gcongr <;> omega
    have key := hfc (Nat.pair n i)
    simp only [Nat.unpair_pair] at key
    rw [hout] at key
    exact evaln_mono hbc key

/-- **Validation of the pipeline** (the `def:ec`-Tok analogue of `priceTrader_ec`): the
responsive trader `priceTrader φ` — whose day-`n` stream `[0, ⌜φ⌝, n, 6, ⌜φ⌝]` contains the
*varying* day-index token `n` — is `EfficientlyComputableTok`. The `n` token is `PolyFueled.id`;
the rest are constants. This is the template the property-file re-certifications follow. -/
theorem priceTrader_ecTok (φ : Sentence) : EfficientlyComputableTok (priceTrader φ) := by
  refine ecTok_of_tokenList _ [fun _ => 0, fun _ => Encodable.encode φ, fun n => n,
    fun _ => 6, fun _ => Encodable.encode φ] ?_ ?_
  · exact PolyFueledTuple.cons (PolyFueled.const 0)
      (PolyFueledTuple.cons (PolyFueled.const (Encodable.encode φ))
      (PolyFueledTuple.cons PolyFueled.id
      (PolyFueledTuple.cons (PolyFueled.const 6)
      (PolyFueledTuple.cons (PolyFueled.const (Encodable.encode φ)) PolyFueledTuple.nil))))
  · intro n; simp [priceTrader, serializeTrades, EF.serialize]

/-! ### `PolyTokenStream` — compositional re-certification over the serialization tree.

Writing an explicit token list for a deep trader (its stream is `Θ(size)` tokens long) is
error-prone. `PolyTokenStream s` bundles "the day-`n` stream `s n` is `ts.map (· n)` for a
fixed-length list of poly-fueled tokens", and — crucially — is **closed under append**, so a
re-certification mirrors the trader's `serialize` tree via combinators, never a flat list. -/

/-- The day-`n` token stream `s n` is a fixed-length list of poly-fueled tokens. -/
def PolyTokenStream (s : ℕ → List ℕ) : Prop :=
  ∃ ts : List (ℕ → ℕ), (∀ n, s n = ts.map (fun t => t n)) ∧ (∀ t ∈ ts, ∃ c, PolyFueled c t)

theorem PolyFueledTuple.of_forall {ts : List (ℕ → ℕ)} (h : ∀ t ∈ ts, ∃ c, PolyFueled c t) :
    PolyFueledTuple ts := by
  induction ts with
  | nil => exact PolyFueledTuple.nil
  | cons t ts ih =>
      obtain ⟨ct, hct⟩ := h t (List.mem_cons_self)
      exact PolyFueledTuple.cons hct (ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')))

theorem PolyTokenStream.nil : PolyTokenStream (fun _ => []) :=
  ⟨[], fun _ => rfl, fun _ h => absurd h (List.not_mem_nil)⟩

theorem PolyTokenStream.append {a b : ℕ → List ℕ} (ha : PolyTokenStream a)
    (hb : PolyTokenStream b) : PolyTokenStream (fun n => a n ++ b n) := by
  obtain ⟨tsa, hmapa, hpfa⟩ := ha
  obtain ⟨tsb, hmapb, hpfb⟩ := hb
  refine ⟨tsa ++ tsb, fun n => ?_, fun t ht => ?_⟩
  · show a n ++ b n = (tsa ++ tsb).map (fun t => t n)
    rw [hmapa n, hmapb n, List.map_append]
  · rcases List.mem_append.mp ht with h | h
    · exact hpfa t h
    · exact hpfb t h

theorem PolyTokenStream.const (k : ℕ) : PolyTokenStream (fun _ => [k]) := by
  refine ⟨[fun _ => k], fun _ => rfl, fun t ht => ?_⟩
  simp only [List.mem_singleton] at ht; subst ht; exact ⟨_, PolyFueled.const k⟩

theorem PolyTokenStream.idTok : PolyTokenStream (fun n => [n]) := by
  refine ⟨[fun n => n], fun _ => rfl, fun t ht => ?_⟩
  simp only [List.mem_singleton] at ht; subst ht; exact ⟨_, PolyFueled.id⟩

theorem PolyTokenStream.polyTok {c : Nat.Partrec.Code} {f : ℕ → ℕ} (h : PolyFueled c f) :
    PolyTokenStream (fun n => [f n]) := by
  refine ⟨[f], fun _ => rfl, fun t ht => ?_⟩
  simp only [List.mem_singleton] at ht; subst ht; exact ⟨c, h⟩

/-- Efficient computability from a compositional stream proof. -/
theorem ecTok_of_stream (Tr : Trader)
    (h : PolyTokenStream (fun n => serializeTrades (Tr.strat n).trades)) :
    EfficientlyComputableTok Tr := by
  obtain ⟨ts, hmap, hpf⟩ := h
  exact ecTok_of_tokenList Tr ts (PolyFueledTuple.of_forall hpf) hmap

/-! #### Per-constructor `serialize` stream lemmas (family level). -/

theorem PolyTokenStream.serialize_const (q : ℚ) :
    PolyTokenStream (fun _ => (EF.const q).serialize) := by
  have : (fun _ : ℕ => (EF.const q).serialize) = (fun _ => [1] ++ [Encodable.encode q]) := by
    funext n; simp [EF.serialize]
  rw [this]; exact (PolyTokenStream.const 1).append (PolyTokenStream.const _)

/-! #### Rational-constant token values in closed arithmetic form.

`Encodable.encode` on `ℚ` unfolds definitionally to `Nat.pair (encode q.num) q.den`
(through the `Encodable.ofEquiv` Sigma/Subtype layers of `Rat`'s instance), and on
`ℤ`-from-`ℕ` to the sign-fold `2n`. Parametric-family traders (`thm:nd`'s scale
ladder) emit tokens `⌜q(j)⌝` for rung-varying rationals, so their emitters need
these values as poly-fueled arithmetic in `j` (`dd:fuel`). -/

theorem encode_rat_eq (q : ℚ) :
    Encodable.encode q = Nat.pair (Encodable.encode q.num) q.den := rfl

theorem encode_int_natCast (n : ℕ) : Encodable.encode ((n : ℤ)) = 2 * n := rfl

theorem encode_rat_natCast (n : ℕ) :
    Encodable.encode ((n : ℚ)) = Nat.pair (2 * n) 1 := by
  rw [encode_rat_eq, Rat.num_natCast, Rat.den_natCast, encode_int_natCast]

theorem encode_rat_inv_natCast {n : ℕ} (hn : 0 < n) :
    Encodable.encode ((n : ℚ)⁻¹) = Nat.pair 2 n := by
  rw [encode_rat_eq, Rat.inv_natCast_num_of_pos hn, Rat.inv_natCast_den_of_pos hn]
  rfl

/-- Token stream of a **varying**-constant family: `[1, ⌜q(m)⌝]` with the encoded
value poly-fueled. The fixed-constant `serialize_const` is the special case. -/
theorem PolyTokenStream.serialize_const_comp {qf : ℕ → ℚ}
    (h : ∃ c, PolyFueled c (fun m => Encodable.encode (qf m))) :
    PolyTokenStream (fun m => (EF.const (qf m)).serialize) := by
  obtain ⟨c, hc⟩ := h
  have heq : (fun m => (EF.const (qf m)).serialize)
      = (fun m => [1] ++ [Encodable.encode (qf m)]) := by
    funext m; simp [EF.serialize]
  rw [heq]
  exact (PolyTokenStream.const 1).append (PolyTokenStream.polyTok hc)

theorem PolyTokenStream.serialize_price (φ : Sentence) :
    PolyTokenStream (fun n => (EF.price φ n).serialize) := by
  have : (fun n => (EF.price φ n).serialize)
      = (fun n => [0] ++ ([Encodable.encode φ] ++ [n])) := by funext n; simp [EF.serialize]
  rw [this]
  exact (PolyTokenStream.const 0).append ((PolyTokenStream.const _).append PolyTokenStream.idTok)

theorem PolyTokenStream.serialize_add {A B : ℕ → EF}
    (hA : PolyTokenStream (fun n => (A n).serialize))
    (hB : PolyTokenStream (fun n => (B n).serialize)) :
    PolyTokenStream (fun n => (EF.add (A n) (B n)).serialize) := by
  have : (fun n => (EF.add (A n) (B n)).serialize)
      = (fun n => ((A n).serialize ++ (B n).serialize) ++ [2]) := by funext n; simp [EF.serialize]
  rw [this]; exact (hA.append hB).append (PolyTokenStream.const 2)

theorem PolyTokenStream.serialize_mul {A B : ℕ → EF}
    (hA : PolyTokenStream (fun n => (A n).serialize))
    (hB : PolyTokenStream (fun n => (B n).serialize)) :
    PolyTokenStream (fun n => (EF.mul (A n) (B n)).serialize) := by
  have : (fun n => (EF.mul (A n) (B n)).serialize)
      = (fun n => ((A n).serialize ++ (B n).serialize) ++ [3]) := by funext n; simp [EF.serialize]
  rw [this]; exact (hA.append hB).append (PolyTokenStream.const 3)

theorem PolyTokenStream.serialize_max {A B : ℕ → EF}
    (hA : PolyTokenStream (fun n => (A n).serialize))
    (hB : PolyTokenStream (fun n => (B n).serialize)) :
    PolyTokenStream (fun n => (EF.max (A n) (B n)).serialize) := by
  have : (fun n => (EF.max (A n) (B n)).serialize)
      = (fun n => ((A n).serialize ++ (B n).serialize) ++ [4]) := by funext n; simp [EF.serialize]
  rw [this]; exact (hA.append hB).append (PolyTokenStream.const 4)

/-- The trade frame: `serializeTrades ((e,φ)::rest) = e.serialize ++ [6] ++ [⌜φ⌝] ++ …`. The
sentence code is supplied as a poly-fueled token (constant for fixed `φ`, `PolyFueled`-bounded
for a varying `φ n`). -/
theorem PolyTokenStream.trades_cons {e : ℕ → EF} {φ : ℕ → Sentence}
    {rest : ℕ → List (EF × Sentence)} {cφ : Nat.Partrec.Code}
    (he : PolyTokenStream (fun n => (e n).serialize))
    (hφ : PolyFueled cφ (fun n => Encodable.encode (φ n)))
    (hrest : PolyTokenStream (fun n => serializeTrades (rest n))) :
    PolyTokenStream (fun n => serializeTrades ((e n, φ n) :: rest n)) := by
  have : (fun n => serializeTrades ((e n, φ n) :: rest n))
      = (fun n => ((e n).serialize ++ [6]) ++ [Encodable.encode (φ n)] ++ serializeTrades (rest n)) := by
    funext n; simp [serializeTrades]
  rw [this]
  exact ((he.append (PolyTokenStream.const 6)).append (PolyTokenStream.polyTok hφ)).append hrest

theorem PolyTokenStream.trades_nil : PolyTokenStream (fun _ => serializeTrades []) := by
  simpa [serializeTrades] using PolyTokenStream.nil

/-! ### `subc` — truncated subtraction with polynomial fuel.

`subc ⟨a, b⟩ = a - b`, via `prec` on `b` whose `succ` step applies `predc` to the previous
value (`sub a (b+1) = pred (sub a b)`). This is the one **nested** `prec` in the file — its
recursive step invokes `predc` (itself a `prec`) — so the fuel proof composes `predc`'s
degree-4 budget across `b` levels. It is the remaining primitive for varying-length token
emission: a deep trader's trailing frame sits at an `n`-dependent stream position, so emitting
its tokens needs a comparison against `n`, i.e. `subc`. -/
def subAux : Nat.Partrec.Code :=
  Nat.Partrec.Code.prec (left.pair right) (comp predc (comp right right))

/-- The `comp predc (comp right right)` recursive step evaluates to `pred prev` when the fuel
covers `predc`'s degree-4 budget on `prev`. -/
theorem subAux_cg_eval (a b prev k : ℕ) (hg2 : Nat.pair a (Nat.pair b prev) ≤ k)
    (hpc : 32 * (prev + 1) ^ 4 + prev + 1 ≤ k) :
    evaln (k + 1) (comp predc (comp right right)) (Nat.pair a (Nat.pair b prev))
      = some (Nat.pred prev) := by
  have hbp : Nat.pair b prev ≤ k :=
    le_trans (Nat.right_le_pair a (Nat.pair b prev)) hg2
  have key := (fueled_comp predc_fueled (fueled_comp fueled_right fueled_right))
    (Nat.pair a (Nat.pair b prev))
  simp only [Nat.unpair_pair] at key
  exact evaln_mono (by omega) key

/-- One unrolling of the `prec` recursion for `subAux`. -/
theorem subAux_step (a b prev k : ℕ)
    (hg1 : Nat.pair a (b + 1) ≤ k)
    (hrec : evaln k subAux (Nat.pair a b) = some prev)
    (hcg : evaln (k + 1) (comp predc (comp right right))
        (Nat.pair a (Nat.pair b prev)) = some (Nat.pred prev)) :
    evaln (k + 1) subAux (Nat.pair a (b + 1)) = some (Nat.pred prev) := by
  conv_lhs => rw [subAux, evaln]
  simp only [Nat.unpaired, Nat.unpair_pair, subAux] at hrec ⊢
  simp [hrec, hcg, hg1]

/-- **`subc` computes truncated subtraction with a polynomial fuel budget.** Degree-4 (from
`predc`) times the recursion depth `b`; the explicit bound `32(a+1)⁴ + pair a (pair b a) + a +
b + 8` dominates every level's `predc` call and guard. -/
theorem subAux_evaln : ∀ (a b F : ℕ),
    32 * (a + 1) ^ 4 + Nat.pair a (Nat.pair b a) + a + b + 8 < F →
    evaln F subAux (Nat.pair a b) = some (a - b) := by
  intro a b
  induction b with
  | zero =>
      intro F hF
      obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by omega⟩
      have hg : Nat.pair a 0 ≤ k := by
        have h1 : Nat.pair a 0 ≤ Nat.pair a (Nat.pair 0 a) :=
          pair_le_pair_right' a (Nat.zero_le _)
        omega
      have hak : a ≤ k := le_trans (Nat.left_le_pair a 0) hg
      show evaln (k + 1) subAux (Nat.pair a 0) = some (a - 0)
      rw [subAux, evaln]
      simp only [Nat.unpaired, Nat.unpair_pair, Nat.rec_zero, Nat.sub_zero]
      simp [Seq.seq, hg, hak, evaln, Nat.pair_unpair]
  | succ b ih =>
      intro F hF
      obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by omega⟩
      have hmono : Nat.pair a (Nat.pair b a) ≤ Nat.pair a (Nat.pair (b + 1) a) :=
        pair_le_pair_right' a (pair_le_pair_left' a (by omega))
      have hIH : evaln k subAux (Nat.pair a b) = some (a - b) := by
        refine ih k ?_; omega
      have hprev : a - b ≤ a := Nat.sub_le a b
      have hg2 : Nat.pair a (Nat.pair b (a - b)) ≤ k := by
        have h1 : Nat.pair b (a - b) ≤ Nat.pair b a := pair_le_pair_right' b hprev
        have h2 : Nat.pair a (Nat.pair b (a - b)) ≤ Nat.pair a (Nat.pair b a) :=
          pair_le_pair_right' a h1
        omega
      have hpc : 32 * ((a - b) + 1) ^ 4 + (a - b) + 1 ≤ k := by
        have : (a - b) + 1 ≤ a + 1 := by omega
        have hp : ((a - b) + 1) ^ 4 ≤ (a + 1) ^ 4 := Nat.pow_le_pow_left this 4
        omega
      have hcg := subAux_cg_eval a b (a - b) k hg2 hpc
      have hstep := subAux_step a b (a - b) k ?_ hIH hcg
      · rw [Nat.sub_succ]; exact hstep
      · have : Nat.pair a (b + 1) ≤ Nat.pair a (Nat.pair (b + 1) a) :=
          pair_le_pair_right' a (Nat.left_le_pair (b + 1) a)
        omega

/-- The one-argument-pair truncated subtraction code and its `Fueled`/`PolyFueled` bundle. -/
def subc : Nat.Partrec.Code := subAux

theorem subc_fueled :
    Fueled subc (fun m => m.unpair.1 - m.unpair.2)
      (fun m => 32 * (m.unpair.1 + 1) ^ 4 +
        Nat.pair m.unpair.1 (Nat.pair m.unpair.2 m.unpair.1) + m.unpair.1 + m.unpair.2 + 9) := by
  intro m
  set a := m.unpair.1 with ha
  set b := m.unpair.2 with hb
  have hm : Nat.pair a b = m := Nat.pair_unpair m
  show evaln (32 * (a + 1) ^ 4 + Nat.pair a (Nat.pair b a) + a + b + 9) subc m = some (a - b)
  rw [← hm, subc]
  exact subAux_evaln a b _ (by omega)

theorem subc_polyFueled : PolyFueled subc (fun m => m.unpair.1 - m.unpair.2) := by
  refine ⟨_, subc_fueled, isPolyBounded_fst.of_le (fun m => Nat.sub_le _ _), ?_⟩
  have h4 : IsPolyBounded (fun m => 32 * (m.unpair.1 + 1) ^ 4) :=
    (show IsPolyBounded (fun x => 32 * (x + 1) ^ 4) from ⟨32, 4, fun _ => Nat.le_add_right _ _⟩).comp
      isPolyBounded_fst
  have hpair : IsPolyBounded (fun m => Nat.pair m.unpair.1 (Nat.pair m.unpair.2 m.unpair.1)) :=
    isPolyBounded_fst.pair (isPolyBounded_snd.pair isPolyBounded_fst)
  exact (((h4.add hpair).add isPolyBounded_fst).add isPolyBounded_snd).add
    (⟨9, 0, fun _ => by simp⟩ : IsPolyBounded (fun _ => 9))

/-! ### Generic `prec` fuel accounting — `PolyFueled` closure under primitive recursion.

Every fuel proof above (`predAux_evaln`, `iterRight_evaln`, `ifzSel_evaln`, `subAux_evaln`)
is the same induction: unroll `evaln`'s `prec` clause once per level, feed the recursive
value to the step code, and dominate every level's budget and guard by one monotone
polynomial. This section does that induction **once**, generically: `evaln_prec` runs any
`prec cf cg` whose base/step codes are `Fueled`, and `PolyFueled.prec` packages it —
`PolyFueled` is closed under `Code.prec` whenever the iterated state stays polynomially
bounded. Every further primitive-recursive combinator (`addc`, `mulc`, `divmodc`, …) is a
corollary, with no new `evaln` reasoning. -/

/-- Transport a `PolyFueled` fact along a pointwise-equal spec. -/
theorem PolyFueled.of_eq {c : Nat.Partrec.Code} {f f' : ℕ → ℕ}
    (h : PolyFueled c f) (he : ∀ n, f n = f' n) : PolyFueled c f' := by
  rwa [funext he] at h

/-- Base unrolling of `evaln`'s `prec` clause. -/
theorem evaln_prec_zero {cf cg : Nat.Partrec.Code} {k a v : ℕ}
    (hg : Nat.pair a 0 ≤ k) (hcf : evaln (k + 1) cf a = some v) :
    evaln (k + 1) (Nat.Partrec.Code.prec cf cg) (Nat.pair a 0) = some v := by
  rw [evaln]
  simp [Nat.unpaired, hg, hcf]

/-- Step unrolling of `evaln`'s `prec` clause. -/
theorem evaln_prec_succ {cf cg : Nat.Partrec.Code} {k a m prev v : ℕ}
    (hg1 : Nat.pair a (m + 1) ≤ k)
    (hrec : evaln k (Nat.Partrec.Code.prec cf cg) (Nat.pair a m) = some prev)
    (hcg : evaln (k + 1) cg (Nat.pair a (Nat.pair m prev)) = some v) :
    evaln (k + 1) (Nat.Partrec.Code.prec cf cg) (Nat.pair a (m + 1)) = some v := by
  conv_lhs => rw [evaln]
  simp [Nat.unpaired, hg1, hrec, hcg]

/-- **Generic fueled `prec` evaluation.** If `cf`/`cg` are `Fueled` and `st` satisfies the
primitive recursion `st a 0 = f a`, `st a (j+1) = g ⟨a, j, st a j⟩`, then `prec cf cg`
computes `st a i` within any fuel exceeding `B + i`, where `B` dominates the base budget,
every level's step budget, and the input (each level costs one fuel decrement plus its
step-code budget, all of which `B` majorizes). -/
theorem evaln_prec {cf cg : Nat.Partrec.Code} {f g bf bg : ℕ → ℕ}
    (hf : Fueled cf f bf) (hg : Fueled cg g bg)
    {st : ℕ → ℕ → ℕ} (h0 : ∀ a, st a 0 = f a)
    (hS : ∀ a j, st a (j + 1) = g (Nat.pair a (Nat.pair j (st a j))))
    (a : ℕ) {B : ℕ} (hBf : bf a ≤ B) :
    ∀ i, (∀ j < i, bg (Nat.pair a (Nat.pair j (st a j))) ≤ B) → Nat.pair a i ≤ B →
      ∀ F, B + i < F →
      evaln F (Nat.Partrec.Code.prec cf cg) (Nat.pair a i) = some (st a i) := by
  intro i
  induction i with
  | zero =>
      intro _ hBi F hF
      obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by omega⟩
      rw [h0 a]
      exact evaln_prec_zero (by omega) (evaln_mono (by omega) (hf a))
  | succ i ih =>
      intro hBg hBi F hF
      obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by omega⟩
      have hBi' : Nat.pair a i ≤ B := le_trans (pair_le_pair_right' a (by omega)) hBi
      have hrec := ih (fun j hj => hBg j (by omega)) hBi' k (by omega)
      have hcg : evaln (k + 1) cg (Nat.pair a (Nat.pair i (st a i)))
          = some (g (Nat.pair a (Nat.pair i (st a i)))) :=
        evaln_mono (le_trans (hBg i (Nat.lt_succ_self i)) (by omega)) (hg _)
      rw [hS a i]
      exact evaln_prec_succ (by omega) hrec hcg

/-- Monotonicity of the `def:ec` polynomial normal form. -/
private theorem poly_mono {a k x y : ℕ} (h : x ≤ y) :
    a * (x + 1) ^ k + a ≤ a * (y + 1) ^ k + a := by
  gcongr

/-- **`PolyFueled` is closed under `Code.prec`** whenever the iterated state is polynomially
bounded in the input `⟨a, i⟩`. The budget dominates every level `j ≤ i` at once, by
monotonicity of `Nat.pair` and of the polynomial bounds. -/
theorem PolyFueled.prec {cf cg : Nat.Partrec.Code} {f g : ℕ → ℕ}
    (hf : PolyFueled cf f) (hg : PolyFueled cg g)
    {st : ℕ → ℕ → ℕ} (h0 : ∀ a, st a 0 = f a)
    (hS : ∀ a j, st a (j + 1) = g (Nat.pair a (Nat.pair j (st a j))))
    (hst : IsPolyBounded (fun m => st m.unpair.1 m.unpair.2)) :
    PolyFueled (cf.prec cg) (fun m => st m.unpair.1 m.unpair.2) := by
  obtain ⟨bf, hff, _, a₃, k₃, hk₃⟩ := hf
  obtain ⟨bg, hfg, _, a₂, k₂, hk₂⟩ := hg
  obtain ⟨a₁, k₁, hk₁⟩ : IsPolyBounded (fun m => st m.unpair.1 m.unpair.2) := hst
  -- Monotone majorants: `S m` for the state at any level `j ≤ m.unpair.2`, `X m` for the
  -- step input at any level, `B m` for all budgets and guards.
  set S : ℕ → ℕ := fun m => a₁ * (m + 1) ^ k₁ + a₁ with hSdef
  set X : ℕ → ℕ := fun m => Nat.pair m.unpair.1 (Nat.pair m.unpair.2 (S m)) with hXdef
  set B : ℕ → ℕ :=
    fun m => a₃ * (m + 1) ^ k₃ + a₃ + (a₂ * (X m + 1) ^ k₂ + a₂) + m with hBdef
  refine ⟨fun m => B m + m.unpair.2 + 1, fun m => ?_, ⟨a₁, k₁, hk₁⟩, ?_⟩
  · have hBf : bf m.unpair.1 ≤ B m := by
      have h1 : bf m.unpair.1 ≤ a₃ * (m.unpair.1 + 1) ^ k₃ + a₃ := hk₃ _
      have h2 : a₃ * (m.unpair.1 + 1) ^ k₃ + a₃ ≤ a₃ * (m + 1) ^ k₃ + a₃ :=
        poly_mono (Nat.unpair_left_le m)
      simp only [hBdef]; omega
    have hBg : ∀ j < m.unpair.2,
        bg (Nat.pair m.unpair.1 (Nat.pair j (st m.unpair.1 j))) ≤ B m := by
      intro j hj
      have hstj : st m.unpair.1 j ≤ S m := by
        have h1 := hk₁ (Nat.pair m.unpair.1 j)
        simp only [Nat.unpair_pair] at h1
        refine le_trans h1 (poly_mono ?_)
        calc Nat.pair m.unpair.1 j
            ≤ Nat.pair m.unpair.1 m.unpair.2 := pair_le_pair_right' _ (le_of_lt hj)
          _ = m := Nat.pair_unpair m
      have hx : Nat.pair m.unpair.1 (Nat.pair j (st m.unpair.1 j)) ≤ X m :=
        pair_le_pair_right' _ (le_trans (pair_le_pair_right' _ hstj)
          (pair_le_pair_left' _ (le_of_lt hj)))
      have h1 := hk₂ (Nat.pair m.unpair.1 (Nat.pair j (st m.unpair.1 j)))
      have h2 : a₂ * (Nat.pair m.unpair.1 (Nat.pair j (st m.unpair.1 j)) + 1) ^ k₂ + a₂
          ≤ a₂ * (X m + 1) ^ k₂ + a₂ := poly_mono hx
      simp only [hBdef]; omega
    have hBi : Nat.pair m.unpair.1 m.unpair.2 ≤ B m := by
      simp only [hBdef]; rw [Nat.pair_unpair]; omega
    have key := evaln_prec hff hfg h0 hS m.unpair.1 hBf m.unpair.2 hBg hBi
      (B m + m.unpair.2 + 1) (by omega)
    rwa [Nat.pair_unpair] at key
  · have hSpb : IsPolyBounded S := ⟨a₁, k₁, fun _ => le_rfl⟩
    have hXpb : IsPolyBounded X := isPolyBounded_fst.pair (isPolyBounded_snd.pair hSpb)
    have hpoly₂ : IsPolyBounded (fun x => a₂ * (x + 1) ^ k₂ + a₂) := ⟨a₂, k₂, fun _ => le_rfl⟩
    have ht2 : IsPolyBounded (fun m => a₂ * (X m + 1) ^ k₂ + a₂) := hpoly₂.comp hXpb
    have ht1 : IsPolyBounded (fun m => a₃ * (m + 1) ^ k₃ + a₃) := ⟨a₃, k₃, fun _ => le_rfl⟩
    have hid : IsPolyBounded (fun m : ℕ => m) :=
      (IsPolyBounded.linear 0).of_le (fun _ => by omega)
    exact (((ht1.add ht2).add hid).add isPolyBounded_snd).add_one

/-! ### Poly-fueled arithmetic: `addc`, `mulc`, `divmodc`.

The `prec` closure makes the arithmetic combinators the block-emission tooling needs
(`thm:con` / `thm:nd` traders: block index and offset from a token position) one-liners:
each is a primitive recursion with a polynomially-bounded state. -/

/-- Addition: `addc ⟨a, b⟩ = a + b`, as the `prec` iterate of `succ`. -/
theorem addc_polyFueled : ∃ c, PolyFueled c (fun m => m.unpair.1 + m.unpair.2) :=
  ⟨_, PolyFueled.prec PolyFueled.id ((PolyFueled.right.comp PolyFueled.right).succ_comp)
    (st := fun a j => a + j) (fun _ => rfl)
    (fun a j => by simp only [Nat.unpair_pair]; omega)
    (isPolyBounded_fst.add isPolyBounded_snd)⟩

/-- Adding a constant: `n ↦ f n + K`, a fixed `succ` chain over `c`. -/
theorem PolyFueled.addConst {c : Nat.Partrec.Code} {f : ℕ → ℕ} (h : PolyFueled c f) :
    ∀ K : ℕ, ∃ c', PolyFueled c' (fun n => f n + K)
  | 0 => ⟨c, h⟩
  | (K + 1) => by
      obtain ⟨c', h'⟩ := h.addConst K
      exact ⟨_, h'.succ_comp.of_eq (fun n => by omega)⟩

theorem isPolyBounded_mul_const (W : ℕ) : IsPolyBounded (fun x => x * W) :=
  ⟨W, 1, fun n => by
    show n * W ≤ W * (n + 1) ^ 1 + W
    rw [pow_one, Nat.mul_add, Nat.mul_comm W n]; omega⟩

/-- Multiplication by a constant: `n ↦ n * W`, as the `prec` iterate of `+ W`. -/
theorem mulc_polyFueled (W : ℕ) : ∃ c, PolyFueled c (fun n => n * W) := by
  obtain ⟨ca, hca⟩ := (PolyFueled.right.comp PolyFueled.right).addConst W
  have hstW : IsPolyBounded (fun m => m.unpair.2 * W) :=
    (isPolyBounded_mul_const W).comp isPolyBounded_snd
  have hprec := PolyFueled.prec (PolyFueled.const 0) hca
    (st := fun _ j => j * W) (fun _ => by simp)
    (fun a j => by simp [Nat.unpair_pair, Nat.succ_mul]) hstW
  exact ⟨_, (hprec.comp ((PolyFueled.const 0).pair PolyFueled.id)).of_eq
    (fun n => by simp only [Nat.unpair_pair])⟩

/-- Uniqueness of division with remainder, in rewrite-ready form. -/
private theorem div_mod_of_decomp {w q s x : ℕ} (hw : 0 < w) (hx : x = w * q + s)
    (hs : s < w) : x / w = q ∧ x % w = s := by
  subst hx
  exact ⟨by rw [Nat.mul_add_div hw, Nat.div_eq_of_lt hs, Nat.add_zero],
         by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]⟩

/-- **`divmodc` (`dd:fuel`): division and remainder by a constant width `w > 0`.** One
`prec` recursion on the input whose state is `⟨quotient, remainder⟩`: the step wraps
(`⟨q+1, 0⟩`) when the remainder is about to reach `w`, else increments the remainder —
the wrap test is `(w-1) − r` via `subc`, dispatched by `ifzSel`. This is the block-index /
block-offset primitive for repeating-block token emission (`def:ec`). -/
theorem divmodc_polyFueled (w : ℕ) (hw : 0 < w) :
    ∃ c, PolyFueled c (fun n => Nat.pair (n / w) (n % w)) := by
  -- Step pieces, on the `prec` state `x = ⟨a, j, ⟨q, r⟩⟩`.
  have prevPF := PolyFueled.right.comp PolyFueled.right
  have qPF := PolyFueled.left.comp prevPF
  have rPF := PolyFueled.right.comp prevPF
  have wrapPF := qPF.succ_comp.pair (PolyFueled.const 0)
  have stayPF := qPF.pair rPF.succ_comp
  have testPF := subc_polyFueled.comp ((PolyFueled.const (w - 1)).pair rPF)
  have gPF := ifzSel_polyFueled.comp ((wrapPF.pair stayPF).pair testPF)
  have hst : IsPolyBounded (fun m => Nat.pair (m.unpair.2 / w) (m.unpair.2 % w)) :=
    (isPolyBounded_snd.pair isPolyBounded_snd).of_le (fun m =>
      le_trans (pair_le_pair_right' _ (Nat.mod_le _ _))
        (pair_le_pair_left' _ (Nat.div_le_self _ _)))
  have hprec := PolyFueled.prec (PolyFueled.const 0) gPF
    (st := fun _ j => Nat.pair (j / w) (j % w))
    (fun _ => by
      show Nat.pair (0 / w) (0 % w) = 0
      rw [Nat.zero_div, Nat.zero_mod]
      rfl)
    (fun a j => by
      have hqr := Nat.div_add_mod j w
      have hrlt := Nat.mod_lt j hw
      show Nat.pair ((j + 1) / w) ((j + 1) % w) = _
      simp only [Nat.unpair_pair, ifzSelFn]
      by_cases hcase : w - 1 - j % w = 0
      · have h1 : j + 1 = w * (j / w + 1) + 0 := by rw [Nat.mul_succ]; omega
        obtain ⟨hd, hm⟩ := div_mod_of_decomp hw h1 hw
        rw [if_pos hcase, hd, hm]
      · have h1 : j + 1 = w * (j / w) + (j % w + 1) := by omega
        obtain ⟨hd, hm⟩ := div_mod_of_decomp hw h1 (by omega)
        rw [if_neg hcase, hd, hm])
    hst
  exact ⟨_, (hprec.comp ((PolyFueled.const 0).pair PolyFueled.id)).of_eq
    (fun n => by simp only [Nat.unpair_pair])⟩

/-- **Runtime multiplication**: `⟨a, b⟩ ↦ a · b`, the `prec` iterate of `+ a`. (`mulc`
multiplies by a baked-in constant; the ladder/bundle stream lengths are runtime
products `cnt n · width n`.) -/
theorem mul_polyFueled : ∃ c, PolyFueled c (fun m => m.unpair.1 * m.unpair.2) := by
  obtain ⟨cad, had⟩ := addc_polyFueled
  have gPF := had.comp ((PolyFueled.right.comp PolyFueled.right).pair PolyFueled.left)
  have hst : IsPolyBounded (fun m => m.unpair.1 * m.unpair.2) :=
    ⟨1, 2, fun m => by
      have h1 := Nat.unpair_left_le m
      have h2 := Nat.unpair_right_le m
      nlinarith⟩
  exact ⟨_, PolyFueled.prec (PolyFueled.const 0) gPF
    (st := fun a j => a * j) (fun a => by simp)
    (fun a j => by simp only [Function.comp_apply, Nat.unpair_pair]; ring) hst⟩

/-- **Runtime-divisor division**: `⟨w, x⟩ ↦ ⟨x / (w+1), x % (w+1)⟩`. The divisor is
`w + 1`, so the spec is total with no division-by-zero case; callers pass `w := W − 1`
for a positive runtime width `W`. Mirrors `divmodc` with the divisor read from the
input: the wrap test is `w − r` via `subc`, dispatched by `ifzSel`. -/
theorem divmod1_polyFueled :
    ∃ c, PolyFueled c (fun m =>
      Nat.pair (m.unpair.2 / (m.unpair.1 + 1)) (m.unpair.2 % (m.unpair.1 + 1))) := by
  have prevPF := PolyFueled.right.comp PolyFueled.right
  have qPF := PolyFueled.left.comp prevPF
  have rPF := PolyFueled.right.comp prevPF
  have wrapPF := qPF.succ_comp.pair (PolyFueled.const 0)
  have stayPF := qPF.pair rPF.succ_comp
  have testPF := subc_polyFueled.comp (PolyFueled.left.pair rPF)
  have gPF := ifzSel_polyFueled.comp ((wrapPF.pair stayPF).pair testPF)
  have hst : IsPolyBounded (fun m =>
      Nat.pair (m.unpair.2 / (m.unpair.1 + 1)) (m.unpair.2 % (m.unpair.1 + 1))) :=
    (isPolyBounded_snd.pair isPolyBounded_snd).of_le (fun m =>
      le_trans (pair_le_pair_right' _ (Nat.mod_le _ _))
        (pair_le_pair_left' _ (Nat.div_le_self _ _)))
  have hprec := PolyFueled.prec (PolyFueled.const 0) gPF
    (st := fun w j => Nat.pair (j / (w + 1)) (j % (w + 1)))
    (fun w => by
      show Nat.pair (0 / (w + 1)) (0 % (w + 1)) = 0
      rw [Nat.zero_div, Nat.zero_mod]
      rfl)
    (fun w j => by
      have hw : 0 < w + 1 := Nat.succ_pos w
      have hqr := Nat.div_add_mod j (w + 1)
      have hrlt := Nat.mod_lt j hw
      show Nat.pair ((j + 1) / (w + 1)) ((j + 1) % (w + 1)) = _
      simp only [Function.comp_apply, Nat.unpair_pair, ifzSelFn]
      by_cases hcase : w - j % (w + 1) = 0
      · have h1 : j + 1 = (w + 1) * (j / (w + 1) + 1) + 0 := by rw [Nat.mul_succ]; omega
        obtain ⟨hd, hm⟩ := div_mod_of_decomp hw h1 hw
        rw [if_pos hcase, hd, hm]
      · have h1 : j + 1 = (w + 1) * (j / (w + 1)) + (j % (w + 1) + 1) := by omega
        obtain ⟨hd, hm⟩ := div_mod_of_decomp hw h1 (by omega)
        rw [if_neg hcase, hd, hm])
    hst
  exact ⟨_, hprec⟩

/-! ### `ecTok_of_tokenFn` — the varying-length emission workhorse.

Generalizes `ecTok_of_tokenList` (fixed length) to **growing** streams: a trader is
`EfficientlyComputableTok` as soon as a *single* poly-fueled function `tokenFn` computes the
`i`-th token of `serializeTrades (strat n)` from `⟨n, i⟩`, and the stream length is polynomial.
This is what deep (size-`Θ(n)`) traders need — their `i`-th token is a fixed arithmetic
expression in `⟨n,i⟩` (built from `ifzSel`/`predc`/`subc`), not a lookup in a fixed list. -/
theorem ecTok_of_tokenFn (Tr : Trader) {tokenFn : ℕ → ℕ} {c : Nat.Partrec.Code}
    (hpf : PolyFueled c tokenFn)
    (hlen : IsPolyBounded (fun n => (serializeTrades (Tr.strat n).trades).length))
    (htok : ∀ n i, i < (serializeTrades (Tr.strat n).trades).length →
        tokenFn (Nat.pair n i) = (serializeTrades (Tr.strat n).trades).getD i 0) :
    EfficientlyComputableTok Tr := by
  obtain ⟨bc, hfc, _, a₀, k₀, hk₀⟩ := hpf
  set len := fun n => (serializeTrades (Tr.strat n).trades).length with hlendef
  -- A poly upper bound for `bc ⟨n,i⟩` over all `i < len n`, monotone in the pair.
  have hbcbound : IsPolyBounded (fun n => a₀ * (Nat.pair n (len n) + 1) ^ k₀ + a₀) :=
    (show IsPolyBounded (fun x => a₀ * (x + 1) ^ k₀ + a₀) from ⟨a₀, k₀, fun _ => le_rfl⟩).comp
      ((IsPolyBounded.linear 0).pair hlen)
  obtain ⟨A, K, hAK⟩ := hlen.max hbcbound
  refine ⟨c, A, K, fun n => ?_, fun n i hi => ?_⟩
  · exact le_trans (le_max_left _ _) (hAK n)
  · -- `bc ⟨n,i⟩ ≤ A(n+1)^K + A`, then `evaln_mono` on `hfc`.
    have hple : Nat.pair n i ≤ Nat.pair n (len n) :=
      pair_le_pair_right' n (le_of_lt hi)
    have hbc : bc (Nat.pair n i) ≤ A * (n + 1) ^ K + A := by
      calc bc (Nat.pair n i) ≤ a₀ * (Nat.pair n i + 1) ^ k₀ + a₀ := hk₀ _
        _ ≤ a₀ * (Nat.pair n (len n) + 1) ^ k₀ + a₀ := by gcongr
        _ ≤ A * (n + 1) ^ K + A := le_trans (le_max_right _ _) (hAK n)
    have key := hfc (Nat.pair n i)
    rw [htok n i hi] at key
    exact evaln_mono hbc key

/-! ### Validation: a genuinely size-`Θ(n)` trader is `EfficientlyComputableTok`.

`srChain n = safeRecip^[n] (const 1)` is a **depth-`n`** feature: its `serialize` is
`[1, ⌜1⌝] ++ replicate n 5` — a *growing* (length `n+2`) token stream, exactly the shape the
old whole-number `def:ec` could not emit (its `toNat` is `~2^{2^n}`). `deepTrader φ` trades it;
we certify `EfficientlyComputableTok` via `ecTok_of_tokenFn`, with the `i`-th token computed by
a fixed nesting of `ifzSel` over `predc`/`subc`-shifted indices. This is the payoff of the whole
`ifzSel`/`subc`/`ecTok_of_tokenFn` toolkit — the first deep trader admitted by the new `def:ec`. -/

/-- A depth-`n` feature: `n`-fold safe reciprocal of the constant `1`. Rank `0` (no price
features), so it is a legal day-`n` coefficient; its *size* is `Θ(n)`. -/
def srChain : ℕ → EF
  | 0 => EF.const 1
  | (k + 1) => EF.safeRecip (srChain k)

theorem srChain_rank (n : ℕ) : (srChain n).rank = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [srChain, EF.rank, ih]

/-- The trader playing the depth-`n` feature on `φ` each day. -/
def deepTrader (φ : Sentence) : Trader where
  strat n := { trades := [(srChain n, φ)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp
                             subst hp; rw [srChain_rank]; exact Nat.zero_le _ }

/-- `serialize (srChain n) = [1, ⌜1⌝] ++ replicate n 5` — a growing stream. -/
theorem serialize_srChain (n : ℕ) :
    (srChain n).serialize = [1, Encodable.encode (1 : ℚ)] ++ List.replicate n 5 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [srChain, EF.serialize, ih, List.replicate_succ']
      simp [List.append_assoc]

/-- The day-`n` token stream and its length `n + 4`. -/
theorem serializeTrades_deepTrader (φ : Sentence) (n : ℕ) :
    serializeTrades ((deepTrader φ).strat n).trades
      = [1, Encodable.encode (1 : ℚ)] ++ List.replicate n 5
        ++ [6, Encodable.encode φ] := by
  show serializeTrades [(srChain n, φ)] = _
  rw [serializeTrades, serialize_srChain]
  simp [serializeTrades]

theorem length_serializeTrades_deepTrader (φ : Sentence) (n : ℕ) :
    (serializeTrades ((deepTrader φ).strat n).trades).length = n + 4 := by
  rw [serializeTrades_deepTrader]
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- The `i`-th token of the deep stream, by region. -/
theorem deepStream_getD (n i eφ : ℕ) (hi : i < n + 4) :
    ([1, Encodable.encode (1 : ℚ)] ++ List.replicate n 5 ++ [6, eφ]).getD i 0
      = if i = 0 then 1 else if i = 1 then Encodable.encode (1 : ℚ)
        else if i ≤ n + 1 then 5 else if i = n + 2 then 6 else eφ := by
  rcases Nat.lt_or_ge i 2 with h2 | h2
  · -- head [1, ⌜1⌝]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simp
    · simp
  · rw [if_neg (by omega : ¬ i = 0), if_neg (by omega : ¬ i = 1)]
    rcases Nat.lt_or_ge i (n + 2) with h3 | h3
    · -- inside the run of 5s
      rw [if_pos (by omega : i ≤ n + 1)]
      rw [List.getD_append ([1, Encodable.encode (1 : ℚ)] ++ List.replicate n 5) [6, eφ] 0 i
          (by simp only [List.length_append, List.length_cons, List.length_nil,
            List.length_replicate]; omega)]
      rw [List.getD_append_right [1, Encodable.encode (1 : ℚ)] (List.replicate n 5) 0 i
          ((by simp only [List.length_cons, List.length_nil]; omega) :
            ([1, Encodable.encode (1 : ℚ)]).length ≤ i)]
      rw [List.getD_replicate (h := (by simp only [List.length_cons, List.length_nil]; omega :
            i - ([1, Encodable.encode (1 : ℚ)]).length < n))]
    · -- tail [6, eφ]
      have hlen2 : ([1, Encodable.encode (1 : ℚ)] ++ List.replicate n 5).length = n + 2 := by
        simp only [List.length_append, List.length_cons, List.length_nil,
          List.length_replicate]; omega
      rw [if_neg (by omega : ¬ i ≤ n + 1)]
      rw [List.getD_append_right ([1, Encodable.encode (1 : ℚ)] ++ List.replicate n 5) [6, eφ] 0 i
          (by rw [hlen2]; omega)]
      rw [hlen2]
      rcases Nat.lt_or_ge i (n + 3) with h4 | h4
      · rw [if_pos (by omega : i = n + 2), show i - (n + 2) = 0 by omega]
        rfl
      · rw [if_neg (by omega : ¬ i = n + 2), show i - (n + 2) = 1 by omega]
        rfl

/-- **Validation of `ecTok_of_tokenFn`**: the depth-`n` (size-`Θ(n)`) `deepTrader φ` — whose
day-`n` token stream *grows* with `n` — is `EfficientlyComputableTok`. The old whole-number
`def:ec` could not certify it; the new one does. The `i`-th token is a fixed nesting of
`ifzSel` over `predc`/`subc`-shifted indices. -/
theorem deepTrader_ecTok (φ : Sentence) : EfficientlyComputableTok (deepTrader φ) := by
  have nPlus3 : PolyFueled _ (fun m => m.unpair.1 + 1 + 1 + 1) :=
    PolyFueled.left.succ_comp.succ_comp.succ_comp
  have rSel := subc_polyFueled.comp (nPlus3.pair PolyFueled.right)
  have predR := predc_polyFueled.comp rSel
  have predI := predc_polyFueled.comp PolyFueled.right
  have L4 :=
    ifzSel_polyFueled.comp (((PolyFueled.const 6).pair (PolyFueled.const 5)).pair predR)
  have L3 :=
    ifzSel_polyFueled.comp (((PolyFueled.const (Encodable.encode φ)).pair L4).pair rSel)
  have L2 :=
    ifzSel_polyFueled.comp
      (((PolyFueled.const (Encodable.encode (1 : ℚ))).pair L3).pair predI)
  have L1 :=
    ifzSel_polyFueled.comp (((PolyFueled.const 1).pair L2).pair PolyFueled.right)
  refine ecTok_of_tokenFn (deepTrader φ) L1 ?_ ?_
  · have hL : (fun n => (serializeTrades ((deepTrader φ).strat n).trades).length)
        = (fun n => n + 4) := by funext n; exact length_serializeTrades_deepTrader φ n
    rw [hL]; exact IsPolyBounded.linear 4
  · intro n i hi
    rw [length_serializeTrades_deepTrader] at hi
    rw [serializeTrades_deepTrader, deepStream_getD n i (Encodable.encode φ) hi]
    simp only [Nat.unpair_pair, ifzSelFn, Nat.pred_eq_sub_one]
    -- LHS = the `ifzSel` token nesting, RHS = the by-region value; equal in every case.
    split_ifs <;> omega

/-! ### `ecTok_of_blockStream` — the repeating-block emission workhorse (Phase A2).

Every remaining property-tail trader is *deep*: its day-`n` feature scans history, so its
token stream is `head ++ block 0 ++ … ++ block (cnt n − 1) ++ tail` with fixed-width blocks,
where `block j` may contain the day index `j` (e.g. a `price φ j` node serializes to
`[0, ⌜φ⌝, j]`). This lemma certifies any such trader `EfficientlyComputableTok` from
poly-fueled per-region tokens: the emitter dispatches on the region (`subc` comparisons via
`ifzSel`), computes the block index/offset by `divmodc`, and selects within the region's
fixed tuple (`sel`). -/

/-- Length of a flat concatenation of constant-width blocks. -/
theorem length_flatMap_const_width {α : Type _} (f : ℕ → List α) (W : ℕ) :
    ∀ c, (∀ j < c, (f j).length = W) → ((List.range c).flatMap f).length = c * W := by
  intro c
  induction c with
  | zero => intro _; simp
  | succ c ih =>
      intro hW
      rw [List.range_succ, List.flatMap_append, List.length_append,
        ih (fun j hj => hW j (by omega)), List.flatMap_singleton, hW c (by omega),
        Nat.succ_mul]

/-- Indexing into a flat concatenation of constant-width blocks: token `d` sits in block
`d / W` at offset `d % W`. -/
theorem getD_flatMap_const_width (f : ℕ → List ℕ) (W : ℕ) (hW0 : 0 < W) :
    ∀ c d, (∀ j < c, (f j).length = W) → d < c * W →
    ((List.range c).flatMap f).getD d 0 = (f (d / W)).getD (d % W) 0 := by
  intro c
  induction c with
  | zero => intro d _ hd; simp at hd
  | succ c ih =>
      intro d hW hd
      have hsm : Nat.succ c * W = c * W + W := Nat.succ_mul c W
      have hsm' : (c + 1) * W = c * W + W := by ring
      have hlen : ((List.range c).flatMap f).length = c * W :=
        length_flatMap_const_width f W c (fun j hj => hW j (by omega))
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      rcases Nat.lt_or_ge d (c * W) with h | h
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact ih d (fun j hj => hW j (by omega)) h
      · rw [List.getD_append_right _ _ _ _ (by omega), hlen]
        obtain ⟨hdiv, hmod⟩ := div_mod_of_decomp hW0
          (show d = W * c + (d - c * W) by have := Nat.mul_comm W c; omega)
          (by omega)
        rw [hdiv, hmod]

/-- **The block-emission workhorse (`def:ec`, Phase A2).** A trader whose day-`n` token
stream is `head.map (· n) ++ (range (cnt n)).flatMap (fun j => bs.map (· ⟨n, j⟩)) ++
tail.map (· n)` — fixed head/tail, `cnt n` fixed-width blocks of poly-fueled tokens of
`⟨n, j⟩`, `cnt` poly-fueled — is `EfficientlyComputableTok`. -/
theorem ecTok_of_blockStream (Tr : Trader) (head bs tail : List (ℕ → ℕ))
    {ccnt : Nat.Partrec.Code} {cnt : ℕ → ℕ} (hcnt : PolyFueled ccnt cnt)
    (hhead : ∀ t ∈ head, ∃ c, PolyFueled c t)
    (hbs : ∀ b ∈ bs, ∃ c, PolyFueled c b)
    (htail : ∀ t ∈ tail, ∃ c, PolyFueled c t)
    (hbs0 : bs ≠ [])
    (hTr : ∀ n, serializeTrades (Tr.strat n).trades
        = head.map (fun t => t n)
          ++ (List.range (cnt n)).flatMap (fun j => bs.map (fun b => b (Nat.pair n j)))
          ++ tail.map (fun t => t n)) :
    EfficientlyComputableTok Tr := by
  set H := head.length with hHdef
  set W := bs.length with hWdef
  set T := tail.length with hTdef
  have hW0 : 0 < W := List.length_pos_iff.mpr hbs0
  obtain ⟨cH, hHt⟩ := PolyFueledTuple.of_forall hhead
  obtain ⟨cB, hBt⟩ := PolyFueledTuple.of_forall hbs
  obtain ⟨cT, hTt⟩ := PolyFueledTuple.of_forall htail
  obtain ⟨cdm, hdm⟩ := divmodc_polyFueled W hW0
  obtain ⟨cml, hml⟩ := mulc_polyFueled W
  obtain ⟨cad, had⟩ := addc_polyFueled
  -- The emitter, assembled on input `m = ⟨n, i⟩`.
  have t1PF := subc_polyFueled.comp (PolyFueled.right.succ_comp.pair (PolyFueled.const H))
  have dmPF := hdm.comp (subc_polyFueled.comp (PolyFueled.right.pair (PolyFueled.const H)))
  have jPF := PolyFueled.left.comp dmPF
  have oPF := PolyFueled.right.comp dmPF
  have cntPF := hcnt.comp PolyFueled.left
  have t2PF := subc_polyFueled.comp (jPF.succ_comp.pair cntPF)
  have headTok := sel_polyFueled.comp ((hHt.comp PolyFueled.left).pair PolyFueled.right)
  have bodyTok := sel_polyFueled.comp ((hBt.comp (PolyFueled.left.pair jPF)).pair oPF)
  have offPF := had.comp ((PolyFueled.const H).pair (hml.comp cntPF))
  have tailIdxPF := subc_polyFueled.comp (PolyFueled.right.pair offPF)
  have tailTok := sel_polyFueled.comp ((hTt.comp PolyFueled.left).pair tailIdxPF)
  have innerPF := ifzSel_polyFueled.comp ((bodyTok.pair tailTok).pair t2PF)
  have tokPF := ifzSel_polyFueled.comp ((headTok.pair innerPF).pair t1PF)
  have hblockLen : ∀ n j, (bs.map (fun b => b (Nat.pair n j))).length = W := by
    intro n j; simp [hWdef]
  have hlen' : ∀ n, (serializeTrades (Tr.strat n).trades).length = H + cnt n * W + T := by
    intro n
    rw [hTr n]
    simp only [List.length_append, List.length_map,
      length_flatMap_const_width _ W (cnt n) (fun j _ => hblockLen n j)]
    omega
  refine ecTok_of_tokenFn Tr tokPF ?_ ?_
  · -- Stream length is `H + cnt n · W + T`, polynomial since `cnt` is.
    obtain ⟨_, _, hcntpb, _⟩ := hcnt
    have heq : (fun n => (serializeTrades (Tr.strat n).trades).length)
        = (fun n => H + cnt n * W + T) := funext hlen'
    rw [heq]
    have hHc : IsPolyBounded (fun _ => H) := ⟨H, 0, fun _ => by simp⟩
    have hTc : IsPolyBounded (fun _ => T) := ⟨T, 0, fun _ => by simp⟩
    exact (hHc.add ((isPolyBounded_mul_const W).comp hcntpb)).add hTc
  · intro n i hi
    rw [hlen' n] at hi
    rw [hTr n]
    simp only [Nat.unpair_pair, ifzSelFn, selFn_tupleEnc]
    have hlenH : (head.map (fun t => t n)).length = H := by simp [hHdef]
    have hlenB : ((List.range (cnt n)).flatMap
        (fun j => bs.map (fun b => b (Nat.pair n j)))).length = cnt n * W :=
      length_flatMap_const_width _ W (cnt n) (fun j _ => hblockLen n j)
    rcases Nat.lt_or_ge i H with h1 | h1
    · -- head region
      rw [if_pos (by omega)]
      rw [List.getD_append _ _ _ _ (by rw [List.length_append, hlenH, hlenB]; omega),
        List.getD_append _ _ _ _ (by omega)]
    · rcases Nat.lt_or_ge i (H + cnt n * W) with h2 | h2
      · -- block region: block index `(i−H)/W`, offset `(i−H)%W`
        have hj : (i - H) / W < cnt n := (Nat.div_lt_iff_lt_mul hW0).mpr (by omega)
        rw [if_neg (by omega), if_pos (by omega)]
        rw [List.getD_append _ _ _ _ (by rw [List.length_append, hlenH, hlenB]; omega),
          List.getD_append_right _ _ _ _ (by omega), hlenH,
          getD_flatMap_const_width _ W hW0 (cnt n) (i - H)
            (fun j _ => hblockLen n j) (by omega)]
      · -- tail region
        have hj : cnt n ≤ (i - H) / W := (Nat.le_div_iff_mul_le hW0).mpr (by omega)
        rw [if_neg (by omega), if_neg (by omega)]
        rw [List.getD_append_right _ _ _ _
            (by rw [List.length_append, hlenH, hlenB]; omega),
          List.length_append, hlenH, hlenB]

/-! ### Validation (Phase A3): a size-`Θ(n)` history-scanning trader.

`histSum φ n = Σ_{k<n} φ*ᵏ` (left-nested adds) is the direct dress rehearsal for the
`thm:con`/`thm:nd` traders: its day-`n` serialization is `[1, ⌜0⌝]` followed by `n`
fixed-width blocks `[0, ⌜φ⌝, k, 2]` **containing the day index `k`** — exactly the shape
`ecTok_of_blockStream` emits (the `k` token is `PolyFueled.right` of the block input
`⟨n, k⟩`). -/

/-- The history-scanning feature `Σ_{k<n} φ*ᵏ`, as left-nested `add`s. -/
def histSum (φ : Sentence) : ℕ → EF
  | 0 => EF.const 0
  | (n + 1) => EF.add (histSum φ n) (EF.price φ n)

theorem histSum_rank (φ : Sentence) : ∀ n, (histSum φ n).rank ≤ n
  | 0 => Nat.le_refl 0
  | (n + 1) => by
      rw [histSum, EF.rank]
      exact max_le ((histSum_rank φ n).trans (by omega)) (by rw [EF.rank]; omega)

/-- The trader playing the history sum on `φ` each day. -/
def histTrader (φ : Sentence) : Trader where
  strat n := { trades := [(histSum φ n, φ)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp
                             subst hp; exact histSum_rank φ n }

theorem serialize_histSum (φ : Sentence) : ∀ n,
    (histSum φ n).serialize
      = [1, Encodable.encode (0 : ℚ)]
        ++ (List.range n).flatMap (fun k => [0, Encodable.encode φ, k, 2])
  | 0 => by simp [histSum, EF.serialize]
  | (n + 1) => by
      rw [histSum, EF.serialize, serialize_histSum φ n, List.range_succ]
      simp [EF.serialize, List.flatMap_append]

/-- **Validation of `ecTok_of_blockStream`**: the size-`Θ(n)` `histTrader φ`, whose day-`n`
stream has `n` width-4 blocks each containing the day index, is `EfficientlyComputableTok`. -/
theorem histTrader_ecTok (φ : Sentence) : EfficientlyComputableTok (histTrader φ) := by
  refine ecTok_of_blockStream _
    [fun _ => 1, fun _ => Encodable.encode (0 : ℚ)]
    [fun _ => 0, fun _ => Encodable.encode φ, fun x => x.unpair.2, fun _ => 2]
    [fun _ => 6, fun _ => Encodable.encode φ]
    PolyFueled.id ?_ ?_ ?_ (by simp) ?_
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    exacts [⟨_, PolyFueled.const 1⟩, ⟨_, PolyFueled.const (Encodable.encode (0 : ℚ))⟩]
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    exacts [⟨_, PolyFueled.const 0⟩, ⟨_, PolyFueled.const (Encodable.encode φ)⟩,
      ⟨_, PolyFueled.right⟩, ⟨_, PolyFueled.const 2⟩]
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    exacts [⟨_, PolyFueled.const 6⟩, ⟨_, PolyFueled.const (Encodable.encode φ)⟩]
  · intro n
    show serializeTrades [(histSum φ n, φ)] = _
    rw [serializeTrades, serializeTrades, serialize_histSum]
    simp [Nat.unpair_pair]

/-! ### `PolySegStream` — segment-composable emission.

`ecTok_of_blockStream` covers `head ++ blocks ++ tail`. The hysteresis trade
(`thm:con`) serializes to **five** segments — two block runs (the `H (n+1)` and `H n`
chains) interleaved with fixed frames — so this layer makes emission *compositional*: a
`PolySegStream` is a stream family with poly-fueled emitter **and length**, closed under
append (dispatch on the runtime boundary via `subc`/`ifzSel`), with fixed-tuple and
repeating-block base cases. Any future multi-segment trader (B2's budget chains, D2's
bundles) composes. -/

/-- A stream family with a poly-fueled per-token emitter and a poly-fueled length. -/
def PolySegStream (s : ℕ → List ℕ) : Prop :=
  ∃ (ct cl : Nat.Partrec.Code) (tokenFn lenFn : ℕ → ℕ),
    PolyFueled ct tokenFn ∧ PolyFueled cl lenFn ∧
    (∀ n, (s n).length = lenFn n) ∧
    (∀ n i, i < lenFn n → tokenFn (Nat.pair n i) = (s n).getD i 0)

theorem PolySegStream.of_eq {s s' : ℕ → List ℕ} (h : PolySegStream s)
    (he : ∀ n, s n = s' n) : PolySegStream s' := by
  rwa [funext he] at h

/-- Base case: a fixed-length stream of poly-fueled tokens (tuple-select emitter). -/
theorem PolySegStream.ofTokenStream {s : ℕ → List ℕ} (h : PolyTokenStream s) :
    PolySegStream s := by
  obtain ⟨ts, hmap, hpf⟩ := h
  obtain ⟨cV, hV⟩ := PolyFueledTuple.of_forall hpf
  refine ⟨_, _, _, _,
    sel_polyFueled.comp ((hV.comp PolyFueled.left).pair PolyFueled.right),
    PolyFueled.const ts.length, fun n => by rw [hmap n, List.length_map], ?_⟩
  intro n i _
  simp only [Nat.unpair_pair, selFn_tupleEnc]
  rw [hmap n]

/-- Closure under append: dispatch on the runtime boundary `lenFn₁ n`. -/
theorem PolySegStream.append {s₁ s₂ : ℕ → List ℕ} (h₁ : PolySegStream s₁)
    (h₂ : PolySegStream s₂) : PolySegStream (fun n => s₁ n ++ s₂ n) := by
  obtain ⟨ct₁, cl₁, t₁, l₁, ht₁, hl₁, hlen₁, htok₁⟩ := h₁
  obtain ⟨ct₂, cl₂, t₂, l₂, ht₂, hl₂, hlen₂, htok₂⟩ := h₂
  obtain ⟨cad, had⟩ := addc_polyFueled
  have lenPF := PolyFueled.of_eq (f' := fun n => l₁ n + l₂ n)
    (had.comp (hl₁.pair hl₂)) (fun n => by simp only [Nat.unpair_pair])
  have testPF := subc_polyFueled.comp (PolyFueled.right.succ_comp.pair
    (hl₁.comp PolyFueled.left))
  have shiftPF := ht₂.comp (PolyFueled.left.pair
    (subc_polyFueled.comp (PolyFueled.right.pair (hl₁.comp PolyFueled.left))))
  have tokPF := ifzSel_polyFueled.comp ((ht₁.pair shiftPF).pair testPF)
  refine ⟨_, _, _, _, tokPF, lenPF,
    fun n => by rw [List.length_append, hlen₁ n, hlen₂ n], ?_⟩
  intro n i hi
  simp only [Nat.unpair_pair, ifzSelFn]
  rcases Nat.lt_or_ge i (l₁ n) with h | h
  · rw [if_pos (by omega), htok₁ n i h,
      List.getD_append _ _ _ _ (by rw [hlen₁ n]; omega)]
  · rw [if_neg (by omega), htok₂ n (i - l₁ n) (by omega),
      List.getD_append_right _ _ _ _ (by rw [hlen₁ n]; omega), hlen₁ n]

/-- Base case: `cnt n` repetitions of a fixed-width block of poly-fueled tokens of
`⟨n, j⟩` (`divmodc` emitter). -/
theorem PolySegStream.blocks {blk : ℕ → List ℕ} (hblk : PolyTokenStream blk)
    (W : ℕ) (hW : ∀ m, (blk m).length = W) (hW0 : 0 < W)
    {ccnt : Nat.Partrec.Code} {cnt : ℕ → ℕ} (hcnt : PolyFueled ccnt cnt) :
    PolySegStream (fun n => (List.range (cnt n)).flatMap (fun j => blk (Nat.pair n j))) := by
  obtain ⟨ts, hmap, hpf⟩ := hblk
  obtain ⟨cV, hV⟩ := PolyFueledTuple.of_forall hpf
  obtain ⟨cml, hml⟩ := mulc_polyFueled W
  obtain ⟨cdm, hdm⟩ := divmodc_polyFueled W hW0
  have dmPF := hdm.comp PolyFueled.right
  have jPF := PolyFueled.left.comp dmPF
  have oPF := PolyFueled.right.comp dmPF
  have tokPF := sel_polyFueled.comp
    ((hV.comp (PolyFueled.left.pair jPF)).pair oPF)
  have lenPF := hml.comp hcnt
  refine ⟨_, _, _, _, tokPF, lenPF,
    fun n => length_flatMap_const_width _ W (cnt n) (fun j _ => hW _), ?_⟩
  intro n i hi
  simp only [Nat.unpair_pair, selFn_tupleEnc]
  rw [getD_flatMap_const_width _ W hW0 (cnt n) i (fun j _ => hW _) hi, hmap]

/-- **`n`-fold segment concatenation, uniform runtime width**: if `seg` is a
`PolySegStream` over the paired input `⟨n, j⟩` whose length depends only on `n`, and
`cnt` is poly-fueled, then `n ↦ seg ⟨n,0⟩ ++ … ++ seg ⟨n, cnt n − 1⟩` is a
`PolySegStream`. The emitter finds block index and offset by runtime-divisor division
(`divmod1_polyFueled` at divisor `(L n − 1) + 1`, harmless when `L n = 0` since the
spec range is then empty); the length is the runtime product `cnt n · L n`. This is the
`thm:nd`-ladder / `thm:ec`-bundle emission shape: `cnt n` rung/bundle chunks per day,
each of day-dependent (but rung-independent) width. -/
theorem PolySegStream.concat {seg : ℕ → List ℕ} (hseg : PolySegStream seg)
    {ccnt : Nat.Partrec.Code} {cnt : ℕ → ℕ} (hcnt : PolyFueled ccnt cnt)
    (hunif : ∀ n j, (seg (Nat.pair n j)).length = (seg (Nat.pair n 0)).length) :
    PolySegStream (fun n => (List.range (cnt n)).flatMap (fun j => seg (Nat.pair n j))) := by
  obtain ⟨ct, cl, tokenFn, lenFn, htok, hlen, hlens, hspec⟩ := hseg
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  -- the common width L n = lenFn ⟨n, 0⟩
  have hL := hlen.comp (PolyFueled.id.pair (PolyFueled.const 0))
  -- stream length: cnt n · L n
  have lenPF := (hmul.comp (hcnt.pair hL)).of_eq
    (f' := fun n => cnt n * lenFn (Nat.pair n 0))
    (fun n => by simp only [Function.comp_apply, Nat.unpair_pair])
  -- block index / offset: divmod1 ⟨L n − 1, i⟩ on input m = ⟨n, i⟩
  have hLm := hL.comp PolyFueled.left
  have hLpred := predc_polyFueled.comp hLm
  have dmPF := hdm.comp (hLpred.pair PolyFueled.right)
  have jPF := PolyFueled.left.comp dmPF
  have oPF := PolyFueled.right.comp dmPF
  have tokPF := htok.comp ((PolyFueled.left.pair jPF).pair oPF)
  have hlf : ∀ n j, lenFn (Nat.pair n j) = lenFn (Nat.pair n 0) := fun n j => by
    rw [← hlens, hunif n j, hlens]
  refine ⟨_, _, _, _, tokPF, lenPF, ?_, ?_⟩
  · intro n
    exact length_flatMap_const_width _ (lenFn (Nat.pair n 0)) (cnt n)
      (fun j _ => by rw [hlens, hlf])
  · intro n i hi
    -- the width is positive on the spec range
    have hW0 : 0 < lenFn (Nat.pair n 0) := by
      rcases Nat.eq_zero_or_pos (lenFn (Nat.pair n 0)) with h0 | h0
      · rw [h0, Nat.mul_zero] at hi; omega
      · exact h0
    have hpred : (lenFn (Nat.pair n 0)).pred + 1 = lenFn (Nat.pair n 0) := by
      rw [Nat.pred_eq_sub_one]
      omega
    simp only [Function.comp_apply, Nat.unpair_pair]
    rw [getD_flatMap_const_width _ (lenFn (Nat.pair n 0)) hW0 (cnt n) i
      (fun j _ => by rw [hlens, hlf]) hi, hpred]
    exact hspec (Nat.pair n (i / lenFn (Nat.pair n 0))) (i % lenFn (Nat.pair n 0))
      (by rw [hlf n (i / lenFn (Nat.pair n 0))]; exact Nat.mod_lt _ hW0)

/-- **The segment-emission capstone**: a trader whose day-`n` stream is a
`PolySegStream` is `EfficientlyComputableTok`. -/
theorem ecTok_of_segStream (Tr : Trader)
    (h : PolySegStream (fun n => serializeTrades (Tr.strat n).trades)) :
    EfficientlyComputableTok Tr := by
  obtain ⟨ct, cl, tokenFn, lenFn, htok, hlen, hlens, hspec⟩ := h
  obtain ⟨_, _, hlpb, _⟩ := hlen
  refine ecTok_of_tokenFn Tr htok ?_ ?_
  · exact hlpb.of_le (fun n => le_of_eq (hlens n))
  · intro n i hi
    exact hspec n i (by rw [← hlens n]; exact hi)

/-- `price φ (f m)` streams for a poly-fueled index `f` — the day-index-in-block case. -/
theorem PolyTokenStream.serialize_price_comp {f : ℕ → ℕ} {c : Nat.Partrec.Code}
    (hf : PolyFueled c f) (φ : Sentence) :
    PolyTokenStream (fun m => (EF.price φ (f m)).serialize) := by
  have heq : (fun m => (EF.price φ (f m)).serialize)
      = (fun m => [0] ++ ([Encodable.encode φ] ++ [f m])) := by
    funext m; simp [EF.serialize]
  rw [heq]
  exact (PolyTokenStream.const 0).append
    ((PolyTokenStream.const _).append (PolyTokenStream.polyTok hf))

end LogicalInduction




