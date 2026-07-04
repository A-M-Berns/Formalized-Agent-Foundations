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

theorem priceTrader_ec (φ : Sentence) : EfficientlyComputable (priceTrader φ) := by
  have hpf := PolyFueled.succ_comp
      ((((PolyFueled.const 1).pair
          ((PolyFueled.const (Encodable.encode φ)).pair PolyFueled.id)).pair
        (PolyFueled.const (Encodable.encode φ))).pair (PolyFueled.const 0))
  have heq : (fun n => Nat.pair (Nat.pair (Nat.pair 1
        (Nat.pair (Encodable.encode φ) n)) (Encodable.encode φ)) 0 + 1)
      = (fun n => Encodable.encode ((priceTrader φ).strat n).trades) := by
    funext n; rfl
  rw [heq] at hpf
  exact EfficientlyComputable.of_polyFueled hpf


end LogicalInduction
