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

end LogicalInduction
