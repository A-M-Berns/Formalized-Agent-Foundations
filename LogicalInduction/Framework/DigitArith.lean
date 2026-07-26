/-
# Digit-stream bignum arithmetic (`dd:fuel`, digit model)

The digit-metered emission model (`EfficientlyComputableTok₂`) admits token *values*
exponential in the day, held only as base-4 digit blocks.  Transducers that must
*compute* on such values — the conditioning translation derives `⌜φ ⋏ ψ⌝` from `⌜φ⌝`,
a `Nat.pair`-shell (square + add) at exponential values — therefore need arithmetic
directly on digit streams: the clocked machine can never materialize the values
(`evaln` outputs are fuel-bounded).

This file provides that layer.  `BigDigits x` certifies poly-fueled *digit access*
(length + per-digit) to a possibly-exponential value family `x : ℕ → ℕ`, and is closed
under addition, multiplication (schoolbook column convolution with a poly-bounded
carry), comparison, `Nat.pair`, and the conjunction-code shell.  The spec layer is the
elementary base-4 carry arithmetic; the implementation layer runs the carry loops with
`PolyFueled.prec`.

Paper node: `def:ec` (digit model), `thm:scon` (conditioning translation residual).
-/
import LogicalInduction.Framework.Computable
import LogicalInduction.Framework.Expectations

namespace LogicalInduction

open Nat.Partrec (Code)
open Nat.Partrec.Code

-- Deep `Primrec`/`PolyFueled` compositions over paired inputs loop `whnf` on `Nat.sqrt`
-- (pair/unpair unfolding); keep it opaque throughout (the standard `dd:fuel` safeguard).
attribute [local irreducible] Nat.sqrt

/-! ## Spec layer — base-4 digit/carry arithmetic -/

/-- The `j`-th base-4 digit of `t`. -/
def dig4 (t j : ℕ) : ℕ := t / 4 ^ j % 4

lemma dig4_lt (t j : ℕ) : dig4 t j < 4 := Nat.mod_lt _ (by norm_num)

lemma dig4_le (t j : ℕ) : dig4 t j ≤ 3 := by have := dig4_lt t j; omega

lemma dig4_eq_zero_of_le {t j : ℕ} (h : len4 t ≤ j) : dig4 t j = 0 := by
  have ht : t < 4 ^ j := by
    by_contra hcon
    have := (lt_len4_iff t j).mpr (not_lt.mp hcon)
    omega
  simp [dig4, Nat.div_eq_of_lt ht]

lemma lt_four_pow_len4 (t : ℕ) : t < 4 ^ len4 t := by
  by_contra hcon
  have := (lt_len4_iff t (len4 t)).mpr (le_of_not_gt hcon)
  omega

lemma four_pow_le_of_dig4_ne {t j : ℕ} (h : dig4 t j ≠ 0) : 4 ^ j ≤ t := by
  by_contra hcon
  simp [dig4, Nat.div_eq_of_lt (lt_of_not_ge hcon)] at h

lemma lt_len4_of_dig4_ne {t j : ℕ} (h : dig4 t j ≠ 0) : j < len4 t :=
  (lt_len4_iff t j).mpr (four_pow_le_of_dig4_ne h)

lemma dig4_len4_pred_ne_zero {t : ℕ} (ht : 0 < t) :
    dig4 t (len4 t - 1) ≠ 0 := by
  have hlen : 0 < len4 t := by
    have := (lt_len4_iff t 0).mpr (by simpa using ht)
    omega
  have hle : 4 ^ (len4 t - 1) ≤ t := (lt_len4_iff t _).mp (by omega)
  have hlt : t < 4 ^ (len4 t - 1 + 1) := by
    have := lt_four_pow_len4 t
    have heq : len4 t - 1 + 1 = len4 t := by omega
    rwa [heq]
  have hq1 : 1 ≤ t / 4 ^ (len4 t - 1) := (Nat.one_le_div_iff (by positivity)).mpr hle
  have hq4 : t / 4 ^ (len4 t - 1) < 4 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity : (0:ℕ) < 4 ^ (len4 t - 1))]
    calc t < 4 ^ (len4 t - 1 + 1) := hlt
      _ = 4 * 4 ^ (len4 t - 1) := by rw [pow_succ]; ring
  have heq : dig4 t (len4 t - 1) = t / 4 ^ (len4 t - 1) := Nat.mod_eq_of_lt hq4
  omega

/-- `len4` is determined by the digits: the length is the least strict bound on the
positions of nonzero digits. -/
lemma len4_eq_iff {t L : ℕ} :
    len4 t = L ↔ (∀ j, L ≤ j → dig4 t j = 0) ∧ (0 < L → dig4 t (L - 1) ≠ 0) := by
  constructor
  · rintro rfl
    exact ⟨fun j hj => dig4_eq_zero_of_le hj, fun hL => dig4_len4_pred_ne_zero (by
      by_contra ht
      simp only [not_lt, Nat.le_zero] at ht
      subst ht
      simp [len4_zero] at hL)⟩
  · rintro ⟨hz, hnz⟩
    rcases Nat.lt_trichotomy (len4 t) L with h | h | h
    · exfalso
      have hL : 0 < L := by omega
      exact hnz hL (dig4_eq_zero_of_le (by omega))
    · exact h
    · exfalso
      have ht : 0 < t := by
        by_contra h0
        have : t = 0 := by omega
        subst this
        simp [len4_zero] at h
      exact dig4_len4_pred_ne_zero ht (hz _ (by omega))

/-- Peel one digit off a truncation: `t % 4^(j+1) = t % 4^j + 4^j * dig4 t j`. -/
lemma mod_pow_succ4 (t j : ℕ) :
    t % 4 ^ (j + 1) = t % 4 ^ j + 4 ^ j * dig4 t j := by
  have hpos : (0:ℕ) < 4 ^ j := by positivity
  have hdecomp : t = 4 ^ (j + 1) * (t / 4 ^ (j + 1)) + (t % 4 ^ j + 4 ^ j * dig4 t j) := by
    have h1 : t = 4 ^ j * (t / 4 ^ j) + t % 4 ^ j := (Nat.div_add_mod _ _).symm
    have h2 : t / 4 ^ j = 4 * (t / 4 ^ j / 4) + t / 4 ^ j % 4 :=
      (Nat.div_add_mod _ _).symm
    have h3 : t / 4 ^ j / 4 = t / 4 ^ (j + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    rw [dig4]
    calc t = 4 ^ j * (t / 4 ^ j) + t % 4 ^ j := h1
      _ = 4 ^ j * (4 * (t / 4 ^ (j + 1)) + t / 4 ^ j % 4) + t % 4 ^ j := by
          rw [← h3, ← h2]
      _ = 4 ^ (j + 1) * (t / 4 ^ (j + 1)) + (t % 4 ^ j + 4 ^ j * (t / 4 ^ j % 4)) := by
          rw [pow_succ]; ring
  have hlt : t % 4 ^ j + 4 ^ j * dig4 t j < 4 ^ (j + 1) := by
    have hm := Nat.mod_lt t hpos
    have hd := dig4_le t j
    have : 4 ^ j * dig4 t j ≤ 4 ^ j * 3 := by
      exact Nat.mul_le_mul_left _ hd
    rw [pow_succ]
    omega
  conv_lhs => rw [hdecomp]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hlt

/-- The truncation is the digit sum: `t % 4^p = ∑_{j<p} dig4 t j * 4^j`. -/
lemma mod_pow_eq_sum_dig4 (t p : ℕ) :
    t % 4 ^ p = ∑ j ∈ Finset.range p, dig4 t j * 4 ^ j := by
  induction p with
  | zero => simp [Nat.mod_one]
  | succ p ih => rw [mod_pow_succ4, ih, Finset.sum_range_succ]; ring

/-! ### Addition carries -/

/-- The carry entering column `j` of `x + y`. -/
def addCarry4 (x y j : ℕ) : ℕ := (x % 4 ^ j + y % 4 ^ j) / 4 ^ j

@[simp] lemma addCarry4_zero (x y : ℕ) : addCarry4 x y 0 = 0 := by
  simp [addCarry4, Nat.mod_one]

lemma addCarry4_le_one (x y j : ℕ) : addCarry4 x y j ≤ 1 := by
  rw [addCarry4]
  have hpos : (0:ℕ) < 4 ^ j := by positivity
  have hx := Nat.mod_lt x hpos
  have hy := Nat.mod_lt y hpos
  have h2 : x % 4 ^ j + y % 4 ^ j < 2 * 4 ^ j := by omega
  have := (Nat.div_lt_iff_lt_mul hpos).mpr h2
  omega

/-- The division split of `x + y` at column `j`. -/
lemma add_div_pow4 (x y j : ℕ) :
    (x + y) / 4 ^ j = x / 4 ^ j + y / 4 ^ j + addCarry4 x y j := by
  have hpos : (0:ℕ) < 4 ^ j := by positivity
  have hdecomp : x + y =
      4 ^ j * (x / 4 ^ j + y / 4 ^ j) + (x % 4 ^ j + y % 4 ^ j) := by
    calc x + y
        = (4 ^ j * (x / 4 ^ j) + x % 4 ^ j) + (4 ^ j * (y / 4 ^ j) + y % 4 ^ j) := by
          rw [Nat.div_add_mod, Nat.div_add_mod]
      _ = 4 ^ j * (x / 4 ^ j + y / 4 ^ j) + (x % 4 ^ j + y % 4 ^ j) := by ring
  rw [hdecomp, Nat.mul_add_div hpos, addCarry4]

lemma addCarry4_succ (x y j : ℕ) :
    addCarry4 x y (j + 1) = (dig4 x j + dig4 y j + addCarry4 x y j) / 4 := by
  have hpos : (0:ℕ) < 4 ^ j := by positivity
  rw [addCarry4, mod_pow_succ4 x j, mod_pow_succ4 y j, addCarry4]
  generalize hdx : dig4 x j = dx
  generalize hdy : dig4 y j = dy
  generalize ha : x % 4 ^ j = a
  generalize hb : y % 4 ^ j = b
  have hab := Nat.div_add_mod (a + b) (4 ^ j)
  set c := (a + b) / 4 ^ j with hc
  set r := (a + b) % 4 ^ j with hr
  have hrlt : r < 4 ^ j := Nat.mod_lt _ hpos
  have hnum : a + 4 ^ j * dx + (b + 4 ^ j * dy) = 4 ^ j * (dx + dy + c) + r := by
    calc a + 4 ^ j * dx + (b + 4 ^ j * dy)
        = (a + b) + 4 ^ j * (dx + dy) := by ring
      _ = (4 ^ j * c + r) + 4 ^ j * (dx + dy) := by rw [hab]
      _ = 4 ^ j * (dx + dy + c) + r := by ring
  rw [hnum, pow_succ, ← Nat.div_div_eq_div_mul, Nat.mul_add_div hpos,
    Nat.div_eq_of_lt hrlt, Nat.add_zero]

lemma dig4_add (x y j : ℕ) :
    dig4 (x + y) j = (dig4 x j + dig4 y j + addCarry4 x y j) % 4 := by
  rw [dig4, add_div_pow4, dig4, dig4]
  omega

/-- `len4` in bound form: `len4 t ≤ L ↔ t < 4^L`. -/
lemma len4_le_iff (t L : ℕ) : len4 t ≤ L ↔ t < 4 ^ L := by
  constructor
  · intro h
    exact lt_of_lt_of_le (lt_four_pow_len4 t) (Nat.pow_le_pow_right (by norm_num) h)
  · intro h
    by_contra hcon
    have := (lt_len4_iff t L).mp (by omega)
    omega

lemma len4_add_le (x y : ℕ) : len4 (x + y) ≤ max (len4 x) (len4 y) + 1 := by
  rw [len4_le_iff]
  have hx := lt_four_pow_len4 x
  have hy := lt_four_pow_len4 y
  have hxle : (4:ℕ) ^ len4 x ≤ 4 ^ max (len4 x) (len4 y) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have hyle : (4:ℕ) ^ len4 y ≤ 4 ^ max (len4 x) (len4 y) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  rw [pow_succ]
  omega

lemma len4_add_le' (x y : ℕ) : len4 (x + y) ≤ len4 x + len4 y + 1 :=
  le_trans (len4_add_le x y) (by
    have h := max_le (Nat.le_add_right (len4 x) (len4 y))
      (Nat.le_add_left (len4 y) (len4 x))
    omega)

lemma len4_mul_le (x y : ℕ) : len4 (x * y) ≤ len4 x + len4 y := by
  rw [len4_le_iff, pow_add]
  calc x * y ≤ x * y + (x + y) := by omega
    _ < (x + 1) * (y + 1) := by ring_nf; omega
    _ ≤ 4 ^ len4 x * 4 ^ len4 y :=
        Nat.mul_le_mul (lt_four_pow_len4 x) (lt_four_pow_len4 y)

/-! ### Multiplication columns

Schoolbook column convolution.  `conv4 x y p` is the raw column-`p` product sum;
`mulCarry4` is the running carry.  The central fact (`colSum4_decomp`) is that the
partial column sums reproduce `x * y` modulo `4^p` with a *polynomially bounded* carry —
which is exactly what lets a fuel-clocked machine emit product digits without ever
materializing the product. -/

/-- Column `p` of the schoolbook product: the digit convolution. -/
def conv4 (x y p : ℕ) : ℕ := ∑ i ∈ Finset.range (p + 1), dig4 x i * dig4 y (p - i)

lemma conv4_le (x y p : ℕ) : conv4 x y p ≤ 9 * (p + 1) := by
  calc conv4 x y p ≤ ∑ _i ∈ Finset.range (p + 1), 9 :=
        Finset.sum_le_sum fun i _ => by
          have h1 := dig4_le x i
          have h2 := dig4_le y (p - i)
          calc dig4 x i * dig4 y (p - i) ≤ 3 * 3 := Nat.mul_le_mul h1 h2
            _ ≤ 9 := by norm_num
    _ = 9 * (p + 1) := by rw [Finset.sum_const, Finset.card_range]; ring

/-- The running column carry of `x * y`. -/
def mulCarry4 (x y : ℕ) : ℕ → ℕ
  | 0 => 0
  | p + 1 => (mulCarry4 x y p + conv4 x y p) / 4

@[simp] lemma mulCarry4_zero (x y : ℕ) : mulCarry4 x y 0 = 0 := rfl

lemma mulCarry4_succ (x y p : ℕ) :
    mulCarry4 x y (p + 1) = (mulCarry4 x y p + conv4 x y p) / 4 := rfl

lemma mulCarry4_le (x y : ℕ) : ∀ p, mulCarry4 x y p ≤ 3 * (p + 1)
  | 0 => by simp
  | p + 1 => by
      have hc := mulCarry4_le x y p
      have hv := conv4_le x y p
      rw [mulCarry4_succ]
      omega

/-- The partial column sum `∑_{q<p} conv4 x y q · 4^q`. -/
def colSum4 (x y p : ℕ) : ℕ := ∑ q ∈ Finset.range p, conv4 x y q * 4 ^ q

@[simp] lemma colSum4_zero (x y : ℕ) : colSum4 x y 0 = 0 := by simp [colSum4]

lemma colSum4_succ (x y p : ℕ) :
    colSum4 x y (p + 1) = colSum4 x y p + conv4 x y p * 4 ^ p := by
  rw [colSum4, Finset.sum_range_succ, colSum4]

/-- The truncated product decomposes into the triangle of columns below `p` plus a
`4^p`-divisible remainder. -/
lemma modmul_eq_colSum (x y p : ℕ) :
    ∃ C, (x % 4 ^ p) * (y % 4 ^ p) = colSum4 x y p + 4 ^ p * C := by
  have hexp : (x % 4 ^ p) * (y % 4 ^ p) =
      ∑ z ∈ Finset.range p ×ˢ Finset.range p,
        dig4 x z.1 * dig4 y z.2 * 4 ^ (z.1 + z.2) := by
    rw [mod_pow_eq_sum_dig4 x p, mod_pow_eq_sum_dig4 y p, Finset.sum_mul_sum,
      Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add]; ring
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.range p ×ˢ Finset.range p) (fun z => z.1 + z.2 < p)
    (fun z => dig4 x z.1 * dig4 y z.2 * 4 ^ (z.1 + z.2))
  have htriSet : Finset.filter (fun z : ℕ × ℕ => z.1 + z.2 < p)
      (Finset.range p ×ˢ Finset.range p) =
      (Finset.range p).biUnion (fun q => Finset.antidiagonal q) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_biUnion, Finset.mem_antidiagonal]
    constructor
    · rintro ⟨⟨_, _⟩, h3⟩
      exact ⟨z.1 + z.2, h3, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  have hdisj : (↑(Finset.range p) : Set ℕ).PairwiseDisjoint Finset.antidiagonal := by
    intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left]
    intro z hza hzb
    rw [Finset.mem_antidiagonal] at hza hzb
    exact hab (by omega)
  have htri : ∑ z ∈ Finset.filter (fun z : ℕ × ℕ => z.1 + z.2 < p)
      (Finset.range p ×ˢ Finset.range p),
        dig4 x z.1 * dig4 y z.2 * 4 ^ (z.1 + z.2) = colSum4 x y p := by
    rw [htriSet, Finset.sum_biUnion hdisj, colSum4]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, conv4, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have : i + (q - i) = q := by omega
    rw [this]
  have hdvd : (4 : ℕ) ^ p ∣ ∑ z ∈ Finset.filter (fun z : ℕ × ℕ => ¬ z.1 + z.2 < p)
      (Finset.range p ×ˢ Finset.range p),
        dig4 x z.1 * dig4 y z.2 * 4 ^ (z.1 + z.2) := by
    refine Finset.dvd_sum fun z hz => ?_
    rw [Finset.mem_filter] at hz
    have hge : p ≤ z.1 + z.2 := by omega
    exact Dvd.dvd.mul_left ⟨4 ^ (z.1 + z.2 - p), by
      rw [← pow_add]
      congr 1
      omega⟩ _
  obtain ⟨C, hC⟩ := hdvd
  exact ⟨C, by rw [hexp, ← hsplit, htri, hC]⟩

/-- The full product also decomposes: `x·y = colSum4 x y p + 4^p·C`. -/
lemma mul_eq_colSum (x y p : ℕ) : ∃ C, x * y = colSum4 x y p + 4 ^ p * C := by
  obtain ⟨C, hC⟩ := modmul_eq_colSum x y p
  refine ⟨x / 4 ^ p * 4 ^ p * (y / 4 ^ p) + x / 4 ^ p * (y % 4 ^ p) +
    (x % 4 ^ p) * (y / 4 ^ p) + C, ?_⟩
  conv_lhs => rw [← Nat.div_add_mod x (4 ^ p), ← Nat.div_add_mod y (4 ^ p)]
  ring_nf
  ring_nf at hC
  rw [hC]
  ring

/-- **The column-carry decomposition**: the partial column sums are exactly the carry
plus the product's truncation.  This is the loop invariant of the digit-emitting
multiplier. -/
lemma colSum4_decomp (x y : ℕ) : ∀ p,
    colSum4 x y p = 4 ^ p * mulCarry4 x y p + (x * y) % 4 ^ p
  | 0 => by simp [Nat.mod_one]
  | p + 1 => by
      have ih := colSum4_decomp x y p
      set A := mulCarry4 x y p + conv4 x y p with hA
      have hAsplit : A = 4 * (A / 4) + A % 4 := (Nat.div_add_mod A 4).symm
      have htail : 4 ^ p * (A % 4) + (x * y) % 4 ^ p < 4 ^ (p + 1) := by
        have h1 : A % 4 ≤ 3 := by omega
        have h2 : (x * y) % 4 ^ p < 4 ^ p := Nat.mod_lt _ (by positivity)
        have h3 : 4 ^ p * (A % 4) ≤ 4 ^ p * 3 := Nat.mul_le_mul_left _ h1
        rw [pow_succ]
        omega
      have hcol : colSum4 x y (p + 1) =
          4 ^ (p + 1) * mulCarry4 x y (p + 1) +
            (4 ^ p * (A % 4) + (x * y) % 4 ^ p) := by
        rw [colSum4_succ, ih, mulCarry4_succ, ← hA]
        calc 4 ^ p * mulCarry4 x y p + (x * y) % 4 ^ p + conv4 x y p * 4 ^ p
            = 4 ^ p * A + (x * y) % 4 ^ p := by rw [hA]; ring
          _ = 4 ^ p * (4 * (A / 4) + A % 4) + (x * y) % 4 ^ p := by rw [← hAsplit]
          _ = 4 ^ (p + 1) * (A / 4) + (4 ^ p * (A % 4) + (x * y) % 4 ^ p) := by
              rw [pow_succ]; ring
      obtain ⟨C, hC⟩ := mul_eq_colSum x y (p + 1)
      have hmod : (x * y) % 4 ^ (p + 1) = 4 ^ p * (A % 4) + (x * y) % 4 ^ p := by
        conv_lhs => rw [hC, hcol]
        rw [show 4 ^ (p + 1) * mulCarry4 x y (p + 1) +
            (4 ^ p * (A % 4) + (x * y) % 4 ^ p) + 4 ^ (p + 1) * C =
          4 ^ (p + 1) * (mulCarry4 x y (p + 1) + C) +
            (4 ^ p * (A % 4) + (x * y) % 4 ^ p) by ring]
        rw [Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt htail
      rw [hcol, hmod]

/-- **Product digit formula**: digit `p` of `x·y` is carry-plus-column mod 4. -/
lemma dig4_mul (x y p : ℕ) :
    dig4 (x * y) p = (mulCarry4 x y p + conv4 x y p) % 4 := by
  have hp := colSum4_decomp x y p
  have hp1 := colSum4_decomp x y (p + 1)
  rw [colSum4_succ, hp] at hp1
  rw [mod_pow_succ4 (x * y) p] at hp1
  set A := mulCarry4 x y p + conv4 x y p with hA
  have hrec : mulCarry4 x y (p + 1) = A / 4 := mulCarry4_succ x y p
  have hd := dig4_lt (x * y) p
  have h2 : 4 ^ p * mulCarry4 x y p + conv4 x y p * 4 ^ p =
      4 ^ (p + 1) * (A / 4) + 4 ^ p * dig4 (x * y) p := by
    rw [← hrec]
    omega
  have hfact : 4 ^ p * A = 4 ^ p * (4 * (A / 4) + dig4 (x * y) p) := by
    calc 4 ^ p * A = 4 ^ p * mulCarry4 x y p + conv4 x y p * 4 ^ p := by
          rw [hA]; ring
      _ = 4 ^ (p + 1) * (A / 4) + 4 ^ p * dig4 (x * y) p := h2
      _ = 4 ^ p * (4 * (A / 4) + dig4 (x * y) p) := by rw [pow_succ]; ring
  have hcancel := Nat.eq_of_mul_eq_mul_left
    (show (0:ℕ) < 4 ^ p by positivity) hfact
  omega

/-! ### Comparison flags -/

/-- The truncated comparison flag: `1` iff `x` is below `y` on the low `p` digits. -/
def ltFlag4 (x y p : ℕ) : ℕ := if x % 4 ^ p < y % 4 ^ p then 1 else 0

@[simp] lemma ltFlag4_zero (x y : ℕ) : ltFlag4 x y 0 = 0 := by
  simp [ltFlag4, Nat.mod_one]

lemma ltFlag4_le_one (x y p : ℕ) : ltFlag4 x y p ≤ 1 := by
  rw [ltFlag4]; split <;> omega

lemma ltFlag4_succ (x y p : ℕ) :
    ltFlag4 x y (p + 1) =
      if dig4 x p < dig4 y p then 1
      else if dig4 y p < dig4 x p then 0
      else ltFlag4 x y p := by
  have hpos : (0:ℕ) < 4 ^ p := by positivity
  rw [ltFlag4, ltFlag4, mod_pow_succ4 x p, mod_pow_succ4 y p]
  have hxr : x % 4 ^ p < 4 ^ p := Nat.mod_lt _ hpos
  have hyr : y % 4 ^ p < 4 ^ p := Nat.mod_lt _ hpos
  rcases Nat.lt_trichotomy (dig4 x p) (dig4 y p) with h | h | h
  · have h1 : 4 ^ p * dig4 x p + 4 ^ p ≤ 4 ^ p * dig4 y p := by
      have hm := Nat.mul_le_mul_left (4 ^ p) (Nat.succ_le_of_lt h)
      calc 4 ^ p * dig4 x p + 4 ^ p = 4 ^ p * (dig4 x p + 1) := by ring
        _ ≤ 4 ^ p * dig4 y p := hm
    have hstep : x % 4 ^ p + 4 ^ p * dig4 x p < y % 4 ^ p + 4 ^ p * dig4 y p := by
      omega
    rw [if_pos hstep, if_pos h]
  · have hnot1 : ¬ dig4 x p < dig4 y p := by rw [h]; exact lt_irrefl _
    have hnot2 : ¬ dig4 y p < dig4 x p := by rw [h]; exact lt_irrefl _
    rw [if_neg hnot1, if_neg hnot2, h]
    simp only [add_lt_add_iff_right]
  · have h1 : 4 ^ p * dig4 y p + 4 ^ p ≤ 4 ^ p * dig4 x p := by
      have hm := Nat.mul_le_mul_left (4 ^ p) (Nat.succ_le_of_lt h)
      calc 4 ^ p * dig4 y p + 4 ^ p = 4 ^ p * (dig4 y p + 1) := by ring
        _ ≤ 4 ^ p * dig4 x p := hm
    have hstep : ¬ (x % 4 ^ p + 4 ^ p * dig4 x p < y % 4 ^ p + 4 ^ p * dig4 y p) := by
      omega
    rw [if_neg hstep, if_neg (by omega), if_pos h]

/-- At full precision the flag decides the order. -/
lemma ltFlag4_spec {x y p : ℕ} (hx : x < 4 ^ p) (hy : y < 4 ^ p) :
    ltFlag4 x y p = if x < y then 1 else 0 := by
  rw [ltFlag4, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-! ### Truncation digits (for the length scanner) -/

/-- Digits of a truncation: below the cut they agree, above they vanish. -/
lemma dig4_mod_pow (t P j : ℕ) :
    dig4 (t % 4 ^ P) j = if j < P then dig4 t j else 0 := by
  by_cases h : j < P
  · rw [if_pos h, dig4, dig4]
    have hsplit : (4:ℕ) ^ P = 4 ^ j * 4 ^ (P - j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, Nat.mod_mul_right_div_self]
    have hdvd : (4:ℕ) ∣ 4 ^ (P - j) := dvd_pow_self 4 (by omega)
    rw [Nat.mod_mod_of_dvd _ hdvd]
  · rw [if_neg h]
    have hlt : t % 4 ^ P < 4 ^ j :=
      lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [dig4, Nat.div_eq_of_lt hlt]

/-- One step of the running length scanner. -/
lemma len4_mod_pow_succ (t J : ℕ) :
    len4 (t % 4 ^ (J + 1)) =
      if dig4 t J = 0 then len4 (t % 4 ^ J) else J + 1 := by
  by_cases h : dig4 t J = 0
  · rw [if_pos h, mod_pow_succ4, h, Nat.mul_zero, Nat.add_zero]
  · rw [if_neg h]
    rw [len4_eq_iff]
    constructor
    · intro j hj
      rw [dig4_mod_pow, if_neg (by omega)]
    · intro _
      rw [show J + 1 - 1 = J by omega, dig4_mod_pow, if_pos (by omega)]
      exact h

/-- Partial column convolution (the inner-loop state of the digit multiplier). -/
def conv4Partial (x y p i : ℕ) : ℕ :=
  ∑ i' ∈ Finset.range i, dig4 x i' * dig4 y (p - i')

@[simp] lemma conv4Partial_zero (x y p : ℕ) : conv4Partial x y p 0 = 0 := by
  simp [conv4Partial]

lemma conv4Partial_succ (x y p i : ℕ) :
    conv4Partial x y p (i + 1) =
      conv4Partial x y p i + dig4 x i * dig4 y (p - i) := by
  rw [conv4Partial, Finset.sum_range_succ, conv4Partial]

lemma conv4Partial_eq_conv4 (x y p : ℕ) : conv4Partial x y p (p + 1) = conv4 x y p := rfl

lemma conv4Partial_le (x y p i : ℕ) : conv4Partial x y p i ≤ 9 * i := by
  calc conv4Partial x y p i ≤ ∑ _i' ∈ Finset.range i, 9 :=
        Finset.sum_le_sum fun i' _ => by
          have h1 := dig4_le x i'
          have h2 := dig4_le y (p - i')
          calc dig4 x i' * dig4 y (p - i') ≤ 3 * 3 := Nat.mul_le_mul h1 h2
            _ ≤ 9 := by norm_num
    _ = 9 * i := by rw [Finset.sum_const, Finset.card_range]; ring

/-! ## Implementation layer — poly-fueled digit access

`BigDigits x` is the interface the digit-model transducers consume: the *value* `x m`
may be exponential in `m`, but its digit count and each digit are poly-fueled.  Every
closure below runs a carry loop with `PolyFueled.prec`, whose iterated state (a carry, a
flag, or a partial column sum) is polynomially bounded even though the represented value
is not — that is the entire trick. -/

/-- Poly-fueled digit access to a (possibly exponentially large) value family. -/
def BigDigits (x : ℕ → ℕ) : Prop :=
  ∃ (cl cd : Code),
    PolyFueled cl (fun m => len4 (x m)) ∧
    PolyFueled cd (fun z => dig4 (x z.unpair.1) z.unpair.2)

namespace BigDigits

lemma of_eq {x x' : ℕ → ℕ} (h : BigDigits x) (he : ∀ m, x m = x' m) :
    BigDigits x' := by
  rwa [funext he] at h

/-- Polynomial *values* have digit access (the inclusion of the old world). -/
lemma of_polyFueled {c : Code} {x : ℕ → ℕ} (h : PolyFueled c x) : BigDigits x := by
  obtain ⟨cl4, hl4⟩ := len4_polyFueled
  obtain ⟨cdg, hdg⟩ := digitAt_polyFueled
  have hdig : PolyFueled (cdg.comp ((c.comp Code.left).pair Code.right))
      (fun z => dig4 (x z.unpair.1) z.unpair.2) :=
    (hdg.comp ((h.comp PolyFueled.left).pair PolyFueled.right)).of_eq
      (fun z => by simp only [Nat.unpair_pair, dig4])
  exact ⟨_, _, hl4.comp h, hdig⟩

lemma const (K : ℕ) : BigDigits (fun _ => K) := of_polyFueled (PolyFueled.const K)

/-- Reindex digit access along a poly-fueled index map. -/
lemma comp {x : ℕ → ℕ} (h : BigDigits x) {cg : Code} {g : ℕ → ℕ}
    (hg : PolyFueled cg g) : BigDigits (fun m => x (g m)) := by
  obtain ⟨cl, cd, hl, hd⟩ := h
  exact ⟨_, _, hl.comp hg,
    (hd.comp ((hg.comp PolyFueled.left).pair PolyFueled.right)).of_eq
      (fun z => by simp only [Nat.unpair_pair])⟩

/-- The generic length scanner: digit access plus any poly length bound recovers the
exact length. -/
lemma len_of_digits {cd cB : Code} {s B : ℕ → ℕ}
    (hd : PolyFueled cd (fun z => dig4 (s z.unpair.1) z.unpair.2))
    (hB : PolyFueled cB B) (hbound : ∀ m, len4 (s m) ≤ B m) :
    ∃ c, PolyFueled c (fun m => len4 (s m)) := by
  -- State at `⟨m, J⟩`: the length of the truncation `s m % 4^J` (always `≤ J`).
  have hdig := hd.comp (PolyFueled.left.pair (PolyFueled.left.comp PolyFueled.right))
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hnext := (PolyFueled.left.comp PolyFueled.right).succ_comp
  have hstep := ifzSel_polyFueled.comp ((hprev.pair hnext).pair hdig)
  have hst : IsPolyBounded (fun z => len4 (s z.unpair.1 % 4 ^ z.unpair.2)) := by
    refine (IsPolyBounded.linear 0).of_le (fun z => ?_)
    have h1 : len4 (s z.unpair.1 % 4 ^ z.unpair.2) ≤ z.unpair.2 := by
      rw [len4_le_iff]
      exact Nat.mod_lt _ (by positivity)
    exact h1.trans (Nat.unpair_right_le z)
  have hscan := PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun m J => len4 (s m % 4 ^ J))
    (fun m => by simp [Nat.mod_one, len4_zero])
    (fun m J => by
      simp only [Nat.unpair_pair, ifzSelFn]
      rw [len4_mod_pow_succ])
    hst
  refine ⟨_, (hscan.comp (PolyFueled.id.pair hB)).of_eq (fun m => ?_)⟩
  simp only [Nat.unpair_pair]
  rw [Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le (lt_four_pow_len4 (s m))
    (Nat.pow_le_pow_right (by norm_num) (hbound m))

/-- **Closure under addition** — the ripple-carry loop. -/
lemma add {x y : ℕ → ℕ} (hx : BigDigits x) (hy : BigDigits y) :
    BigDigits (fun m => x m + y m) := by
  obtain ⟨clx, cdx, hlx, hdx⟩ := hx
  obtain ⟨cly, cdy, hly, hdy⟩ := hy
  obtain ⟨cad, had⟩ := addc_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  -- Carry loop: state at `⟨m, j⟩` is `addCarry4 (x m) (y m) j ≤ 1`.
  have hdigx := hdx.comp (PolyFueled.left.pair (PolyFueled.left.comp PolyFueled.right))
  have hdigy := hdy.comp (PolyFueled.left.pair (PolyFueled.left.comp PolyFueled.right))
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hsum := had.comp ((had.comp (hdigx.pair hdigy)).pair hprev)
  have hstep := PolyFueled.left.comp (hdm.comp ((PolyFueled.const 3).pair hsum))
  have hcarry := PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun m j => addCarry4 (x m) (y m) j)
    (fun m => by simp)
    (fun m j => by simp only [Nat.unpair_pair]; rw [addCarry4_succ])
    ((IsPolyBounded.linear 1).of_le (fun z =>
      le_trans (addCarry4_le_one (x z.unpair.1) (y z.unpair.1) z.unpair.2)
        (by omega)))
  -- Digit emitter: `(dx + dy + carry) % 4`.
  have hdigx' := hdx
  have hdigy' := hdy
  have hsum' := had.comp ((had.comp (hdigx'.pair hdigy')).pair hcarry)
  have hdig := (PolyFueled.right.comp
    (hdm.comp ((PolyFueled.const 3).pair hsum'))).of_eq (fun z => by
      simp only [Nat.unpair_pair]
      rw [← dig4_add])
  -- Length: scan under the (loose) bound `lenx + leny + 1`.
  have hlsum : PolyFueled (cad.comp (clx.pair cly))
      (fun m => len4 (x m) + len4 (y m)) :=
    (had.comp (hlx.pair hly)).of_eq (fun m => by simp only [Nat.unpair_pair])
  obtain ⟨cl, hl⟩ := len_of_digits hdig hlsum.succ_comp
    (fun m => len4_add_le' (x m) (y m))
  exact ⟨_, _, hl, hdig⟩

/-- **Closure under multiplication** — the schoolbook column loop.  The inner `prec`
accumulates the column convolution, the outer `prec` runs the carry; both states are
polynomially bounded even though the product is not. -/
lemma mul {x y : ℕ → ℕ} (hx : BigDigits x) (hy : BigDigits y) :
    BigDigits (fun m => x m * y m) := by
  obtain ⟨clx, cdx, hlx, hdx⟩ := hx
  obtain ⟨cly, cdy, hly, hdy⟩ := hy
  obtain ⟨cad, had⟩ := addc_polyFueled
  obtain ⟨cml, hml⟩ := mul_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  -- Inner loop, input `⟨⟨m,p⟩, ⟨i, prev⟩⟩`: partial column sums.
  have hm := PolyFueled.left.comp PolyFueled.left
  have hp := PolyFueled.right.comp PolyFueled.left
  have hi := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hdigx := hdx.comp (hm.pair hi)
  have hdigy := hdy.comp (hm.pair (subc_polyFueled.comp (hp.pair hi)))
  have hstep := had.comp (hprev.pair (hml.comp (hdigx.pair hdigy)))
  have hconvPartial := PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun a i => conv4Partial (x a.unpair.1) (y a.unpair.1) a.unpair.2 i)
    (fun a => by simp)
    (fun a i => by
      simp only [Nat.unpair_pair]
      rw [conv4Partial_succ])
    ⟨9, 1, fun z => by
      simp only []
      have h1 := conv4Partial_le (x z.unpair.1.unpair.1) (y z.unpair.1.unpair.1)
        z.unpair.1.unpair.2 z.unpair.2
      have h2 := Nat.unpair_right_le z
      rw [pow_one]
      omega⟩
  -- The full column at `⟨m, p⟩`.
  have hconv : PolyFueled _
      (fun z => conv4 (x z.unpair.1) (y z.unpair.1) z.unpair.2) :=
    (hconvPartial.comp (PolyFueled.id.pair PolyFueled.right.succ_comp)).of_eq
      (fun z => by
        simp only [Nat.unpair_pair]
        rw [conv4Partial_eq_conv4])
  -- The carry loop at `⟨m, ⟨p, prev⟩⟩`.
  have hm2 := PolyFueled.left
  have hp2 := PolyFueled.left.comp PolyFueled.right
  have hprev2 := PolyFueled.right.comp PolyFueled.right
  have hsum2 := had.comp (hprev2.pair (hconv.comp (hm2.pair hp2)))
  have hstep2 := PolyFueled.left.comp (hdm.comp ((PolyFueled.const 3).pair hsum2))
  have hcarry := PolyFueled.prec (PolyFueled.const 0) hstep2
    (st := fun m p => mulCarry4 (x m) (y m) p)
    (fun m => by simp)
    (fun m p => by
      simp only [Nat.unpair_pair]
      rw [mulCarry4_succ])
    ⟨3, 1, fun z => by
      simp only []
      have h1 := mulCarry4_le (x z.unpair.1) (y z.unpair.1) z.unpair.2
      have h2 := Nat.unpair_right_le z
      rw [pow_one]
      omega⟩
  -- The digit emitter: `(carry + column) % 4`.
  have hsum3 := had.comp (hcarry.pair hconv)
  have hdig : PolyFueled _
      (fun z => dig4 (x z.unpair.1 * y z.unpair.1) z.unpair.2) :=
    (PolyFueled.right.comp (hdm.comp ((PolyFueled.const 3).pair hsum3))).of_eq
      (fun z => by
        simp only [Nat.unpair_pair]
        rw [← dig4_mul])
  have hlsum : PolyFueled (cad.comp (clx.pair cly))
      (fun m => len4 (x m) + len4 (y m)) :=
    (had.comp (hlx.pair hly)).of_eq (fun m => by simp only [Nat.unpair_pair])
  obtain ⟨cl, hl⟩ := len_of_digits hdig hlsum (fun m => len4_mul_le (x m) (y m))
  exact ⟨_, _, hl, hdig⟩

/-- The comparison flag `if x < y then 1 else 0` is poly-fueled from digit access
(most-significant-difference scan with a one-bit state). -/
lemma ltNat {x y : ℕ → ℕ} (hx : BigDigits x) (hy : BigDigits y) :
    ∃ c, PolyFueled c (fun m => if x m < y m then 1 else 0) := by
  obtain ⟨clx, cdx, hlx, hdx⟩ := hx
  obtain ⟨cly, cdy, hly, hdy⟩ := hy
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hm := PolyFueled.left
  have hpi := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hdigx := hdx.comp (hm.pair hpi)
  have hdigy := hdy.comp (hm.pair hpi)
  have ht1 := subc_polyFueled.comp (hdigy.pair hdigx)
  have ht2 := subc_polyFueled.comp (hdigx.pair hdigy)
  have hinner := ifzSel_polyFueled.comp ((hprev.pair (PolyFueled.const 0)).pair ht2)
  have hstep := ifzSel_polyFueled.comp ((hinner.pair (PolyFueled.const 1)).pair ht1)
  have hflag := PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun m p => ltFlag4 (x m) (y m) p)
    (fun m => by simp)
    (fun m p => by
      simp only [Nat.unpair_pair, ifzSelFn]
      rw [ltFlag4_succ]
      rcases Nat.lt_trichotomy (dig4 (x m) p) (dig4 (y m) p) with h | h | h
      · have c1 : ¬ dig4 (y m) p - dig4 (x m) p = 0 := by omega
        rw [if_pos h, if_neg c1]
      · have n1 : ¬ dig4 (x m) p < dig4 (y m) p := by omega
        have n2 : ¬ dig4 (y m) p < dig4 (x m) p := by omega
        have c1 : dig4 (y m) p - dig4 (x m) p = 0 := by omega
        have c2 : dig4 (x m) p - dig4 (y m) p = 0 := by omega
        rw [if_neg n1, if_neg n2, if_pos c1, if_pos c2]
      · have n1 : ¬ dig4 (x m) p < dig4 (y m) p := by omega
        have c1 : dig4 (y m) p - dig4 (x m) p = 0 := by omega
        have c2 : ¬ dig4 (x m) p - dig4 (y m) p = 0 := by omega
        rw [if_neg n1, if_pos h, if_pos c1, if_neg c2])
    ((IsPolyBounded.linear 1).of_le fun z =>
      le_trans (ltFlag4_le_one _ _ _) (by omega))
  have hlen := had.comp (hlx.pair hly)
  refine ⟨_, (hflag.comp (PolyFueled.id.pair hlen)).of_eq (fun m => ?_)⟩
  simp only [Nat.unpair_pair]
  have hxb : x m < 4 ^ (len4 (x m) + len4 (y m)) :=
    lt_of_lt_of_le (lt_four_pow_len4 (x m))
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hyb : y m < 4 ^ (len4 (x m) + len4 (y m)) :=
    lt_of_lt_of_le (lt_four_pow_len4 (y m))
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [ltFlag4_spec hxb hyb]

/-- **Closure under `Nat.pair`** — branch on the comparison flag between the two
square-and-add arms. -/
lemma natPair {x y : ℕ → ℕ} (hx : BigDigits x) (hy : BigDigits y) :
    BigDigits (fun m => Nat.pair (x m) (y m)) := by
  obtain ⟨cf, hflag⟩ := ltNat hx hy
  obtain ⟨cl1, cd1, hl1, hd1⟩ := (hy.mul hy).add hx
  obtain ⟨cl2, cd2, hl2, hd2⟩ := ((hx.mul hx).add hx).add hy
  have hflagAtZ := hflag.comp PolyFueled.left
  have hdig : PolyFueled _
      (fun z => dig4 (Nat.pair (x z.unpair.1) (y z.unpair.1)) z.unpair.2) :=
    (ifzSel_polyFueled.comp ((hd2.pair hd1).pair hflagAtZ)).of_eq (fun z => by
      simp only [Nat.unpair_pair, ifzSelFn]
      by_cases h : x z.unpair.1 < y z.unpair.1
      · rw [if_pos h, if_neg (by norm_num : ¬ (1:ℕ) = 0)]
        show dig4 _ _ = dig4 (Nat.pair _ _) _
        rw [Nat.pair, if_pos h]
      · rw [if_neg h, if_pos rfl]
        show dig4 _ _ = dig4 (Nat.pair _ _) _
        rw [Nat.pair, if_neg h])
  have hlen : PolyFueled _
      (fun m => len4 (Nat.pair (x m) (y m))) :=
    (ifzSel_polyFueled.comp ((hl2.pair hl1).pair hflag)).of_eq (fun m => by
      simp only [Nat.unpair_pair, ifzSelFn]
      by_cases h : x m < y m
      · rw [if_pos h, if_neg (by norm_num : ¬ (1:ℕ) = 0)]
        show len4 _ = len4 (Nat.pair _ _)
        rw [Nat.pair, if_pos h]
      · rw [if_neg h, if_pos rfl]
        show len4 _ = len4 (Nat.pair _ _)
        rw [Nat.pair, if_neg h])
  exact ⟨_, _, hlen, hdig⟩

/-- Closure under successor (the `+ 1` of encoding shells). -/
lemma succ {x : ℕ → ℕ} (hx : BigDigits x) : BigDigits (fun m => x m + 1) :=
  hx.add (const 1)

/-- One clamped accumulation step: clamping accumulator and place value at `M` loses
nothing about the clamped total. -/
lemma min_clamp_step (a p d M : ℕ) :
    min (a + d * p) M = min (min a M + d * min p M) M := by
  by_cases ha : a ≤ M
  · rw [Nat.min_eq_left ha]
    by_cases hp : p ≤ M
    · rw [Nat.min_eq_left hp]
    · rw [show min p M = M from Nat.min_eq_right (by omega)]
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · have hdp : p ≤ d * p := Nat.le_mul_of_pos_left p hd
        have hdM : M ≤ d * M := Nat.le_mul_of_pos_left M hd
        rw [show min (a + d * p) M = M from Nat.min_eq_right (by omega),
          show min (a + d * M) M = M from Nat.min_eq_right (by omega)]
  · rw [show min a M = M from Nat.min_eq_right (by omega)]
    have h1 : M ≤ a + d * p := by omega
    have h2 : M ≤ M + d * min p M := by omega
    rw [show min (a + d * p) M = M from Nat.min_eq_right h1,
      show min (M + d * min p M) M = M from Nat.min_eq_right h2]

lemma min_clamp_pow (p M : ℕ) :
    min (4 * p) M = min (4 * min p M) M := by
  by_cases hp : p ≤ M
  · rw [Nat.min_eq_left hp]
  · rw [show min p M = M from Nat.min_eq_right (by omega),
      show min (4 * p) M = M from Nat.min_eq_right (by omega),
      show min (4 * M) M = M from Nat.min_eq_right (by omega)]

/-- **Bounded materialization**: the clamp `min x (B+1)` of a big value against a
poly-fueled bound is poly-fueled — exact when `x ≤ B`, the sentinel `B+1` otherwise.
This is how digit-model transducers decide smallness (tags, day indices) without ever
holding a large value. -/
lemma clampVal {x : ℕ → ℕ} (hx : BigDigits x) {cB : Code} {B : ℕ → ℕ}
    (hB : PolyFueled cB B) :
    ∃ c, PolyFueled c (fun m => min (x m) (B m + 1)) := by
  obtain ⟨clx, cdx, hlx, hdx⟩ := hx
  obtain ⟨cad, had⟩ := addc_polyFueled
  obtain ⟨cml, hml⟩ := mul_polyFueled
  -- `minc ⟨a,b⟩ = a - (a - b) = min a b`.
  have hminc : PolyFueled _ (fun z => min z.unpair.1 z.unpair.2) :=
    (subc_polyFueled.comp (PolyFueled.left.pair
      (subc_polyFueled.comp (PolyFueled.left.pair PolyFueled.right)))).of_eq
      (fun z => by simp only [Nat.unpair_pair]; omega)
  -- Step at `⟨m, ⟨i, prev⟩⟩` with `prev = ⟨acc', pow'⟩`.
  have hm := PolyFueled.left
  have hii := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hacc := PolyFueled.left.comp hprev
  have hpow := PolyFueled.right.comp hprev
  have hM := (hB.comp hm).succ_comp
  have hd := hdx.comp (hm.pair hii)
  have haccNew := hminc.comp ((had.comp (hacc.pair (hml.comp (hd.pair hpow)))).pair hM)
  have hpowNew := hminc.comp ((hml.comp ((PolyFueled.const 4).pair hpow)).pair hM)
  have hstep := haccNew.pair hpowNew
  have hvalB : IsPolyBounded B := by
    obtain ⟨_, _, h, _⟩ := hB
    exact h
  have hstBound : IsPolyBounded (fun z =>
      Nat.pair (min (x z.unpair.1 % 4 ^ z.unpair.2) (B z.unpair.1 + 1))
        (min (4 ^ z.unpair.2) (B z.unpair.1 + 1))) := by
    have hBz : IsPolyBounded (fun z : ℕ => B z.unpair.1 + 1) :=
      (hvalB.comp isPolyBounded_fst).add_one
    exact (hBz.pair hBz).of_le (fun z => by
      exact le_trans (pair_le_pair_left' _ (min_le_right _ _))
        (pair_le_pair_right' _ (min_le_right _ _)))
  have hscan := PolyFueled.prec
    (PolyFueled.const (Nat.pair 0 1))
    hstep
    (st := fun m i =>
      Nat.pair (min (x m % 4 ^ i) (B m + 1)) (min (4 ^ i) (B m + 1)))
    (fun m => by
      simp only [pow_zero, Nat.mod_one]
      rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)])
    (fun m i => by
      simp only [Nat.unpair_pair]
      rw [mod_pow_succ4, pow_succ]
      rw [show x m % 4 ^ i + 4 ^ i * dig4 (x m) i =
        x m % 4 ^ i + dig4 (x m) i * 4 ^ i by ring]
      rw [min_clamp_step, show (4:ℕ) ^ i * 4 = 4 * 4 ^ i by ring, min_clamp_pow])
    hstBound
  refine ⟨_, (PolyFueled.left.comp
    (hscan.comp (PolyFueled.id.pair hlx))).of_eq (fun m => ?_)⟩
  simp only [Nat.unpair_pair]
  rw [Nat.mod_eq_of_lt (lt_four_pow_len4 (x m))]

/-- The self-delimiting digit block family of a big value family is a `PolySegStream` —
the digit-access analogue of `PolySegStream.block`, and the delivery interface from
bignum arithmetic back to digit-stream emission. -/
lemma blockSeg {x : ℕ → ℕ} (hx : BigDigits x) :
    PolySegStream (fun m => tokenBlock (x m)) := by
  obtain ⟨cl, cd, hl, hd⟩ := hx
  have lenPF := hl.succ_comp
  have l4PF := hl.comp PolyFueled.left
  have testPF := subc_polyFueled.comp (PolyFueled.right.succ_comp.pair l4PF)
  have tokPF := ifzSel_polyFueled.comp ((hd.pair (PolyFueled.const 4)).pair testPF)
  refine ⟨_, _, _, _, tokPF, lenPF, fun m => tokenBlock_length _, fun m j hj => ?_⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  rw [tokenBlock_getD]
  by_cases h : j < len4 (x m)
  · rw [if_pos h, if_pos (by omega : j + 1 - len4 (x m) = 0)]
    rfl
  · have hje : j = len4 (x m) := by omega
    rw [if_neg h, if_pos hje, if_neg (by omega : ¬ j + 1 - len4 (x m) = 0)]

end BigDigits

/-! ## The undigitize block view — list-level spec

`undigitize` (Criterion.lean) reads a digit stream as blocks separated by terminator
digits (`≥ 4`), dropping the trailing partial block.  The digit-model transducers need
random access to that block structure.  `blockSplit` re-expresses the same fold with
the block *digit lists* kept intact, so every fueled scan downstream has a clean
per-prefix invariant. -/

/-- One step of the block split: digits `< 4` extend the current block, anything else
closes it. -/
def blockStep (s : List (List ℕ) × List ℕ) (d : ℕ) : List (List ℕ) × List ℕ :=
  if d < 4 then (s.1, s.2 ++ [d]) else (s.1 ++ [s.2], [])

/-- Split a digit stream at terminators: completed blocks and the trailing partial. -/
def blockSplit (ds : List ℕ) : List (List ℕ) × List ℕ :=
  ds.foldl blockStep ([], [])

/-- Little-endian base-4 value of a digit block. -/
def digitVal : List ℕ → ℕ
  | [] => 0
  | d :: b => d + 4 * digitVal b

@[simp] lemma digitVal_nil : digitVal [] = 0 := rfl

lemma digitVal_append_singleton (b : List ℕ) (d : ℕ) :
    digitVal (b ++ [d]) = digitVal b + d * 4 ^ b.length := by
  induction b with
  | nil => simp [digitVal]
  | cons d' b ih =>
      simp only [List.cons_append, digitVal, ih, List.length_cons]
      ring

lemma blockSplit_snoc (ds : List ℕ) (d : ℕ) :
    blockSplit (ds ++ [d]) = blockStep (blockSplit ds) d := by
  rw [blockSplit, List.foldl_append, List.foldl_cons, List.foldl_nil, blockSplit]

/-- The undigitize fold tracks the block split: accumulator = value of the current
block, place = `4 ^` its digit count. -/
lemma foldl_undigitizeStep_blockStep (ds : List ℕ) : ∀ (bs : List (List ℕ)) (cur : List ℕ),
    List.foldl undigitizeStep (bs.map digitVal, digitVal cur, 4 ^ cur.length) ds =
      ((List.foldl blockStep (bs, cur) ds).1.map digitVal,
        digitVal (List.foldl blockStep (bs, cur) ds).2,
        4 ^ (List.foldl blockStep (bs, cur) ds).2.length) := by
  induction ds with
  | nil => intros; rfl
  | cons d rest ih =>
      intro bs cur
      simp only [List.foldl_cons]
      by_cases h : d < 4
      · rw [show undigitizeStep (bs.map digitVal, digitVal cur, 4 ^ cur.length) d =
            (bs.map digitVal, digitVal cur + d * 4 ^ cur.length, 4 * 4 ^ cur.length) from
              if_pos h,
          show blockStep (bs, cur) d = (bs, cur ++ [d]) from if_pos h]
        have hval := (digitVal_append_singleton cur d).symm
        have hlen : 4 * (4:ℕ) ^ cur.length = 4 ^ (cur ++ [d]).length := by
          rw [List.length_append, List.length_cons, List.length_nil, pow_succ]
          ring
        rw [hval, hlen]
        exact ih bs (cur ++ [d])
      · rw [show undigitizeStep (bs.map digitVal, digitVal cur, 4 ^ cur.length) d =
            (bs.map digitVal ++ [digitVal cur], 0, 1) from if_neg h,
          show blockStep (bs, cur) d = (bs ++ [cur], []) from if_neg h]
        have hmap : bs.map digitVal ++ [digitVal cur] = (bs ++ [cur]).map digitVal := by
          rw [List.map_append, List.map_cons, List.map_nil]
        rw [hmap, show (0:ℕ) = digitVal [] from rfl, show (1:ℕ) = 4 ^ ([] : List ℕ).length by simp]
        exact ih (bs ++ [cur]) []

/-- **`undigitize` through the block split**: the token stream is the block values. -/
lemma undigitize_eq_blockSplit (ds : List ℕ) :
    undigitize ds = (blockSplit ds).1.map digitVal := by
  have h := foldl_undigitizeStep_blockStep ds [] []
  rw [undigitize, blockSplit]
  rw [show (([], 0, 1) : List ℕ × ℕ × ℕ) = (List.map digitVal [], digitVal [], 4 ^ ([] : List ℕ).length) by simp]
  rw [h]

/-- Every completed block consists of digits `< 4`. -/
lemma blockSplit_digits_lt (ds : List ℕ) :
    (∀ b ∈ (blockSplit ds).1, ∀ d ∈ b, d < 4) ∧ (∀ d ∈ (blockSplit ds).2, d < 4) := by
  rw [blockSplit]
  generalize hinit : (([], []) : List (List ℕ) × List ℕ) = init
  have hbase : (∀ b ∈ init.1, ∀ d ∈ b, d < 4) ∧ (∀ d ∈ init.2, d < 4) := by
    rw [← hinit]; simp
  clear hinit
  induction ds generalizing init with
  | nil => exact hbase
  | cons d rest ih =>
      rw [List.foldl_cons]
      refine ih _ ?_
      rw [blockStep]
      by_cases h : d < 4
      · rw [if_pos h]
        refine ⟨hbase.1, ?_⟩
        intro d' hd'
        rcases List.mem_append.mp hd' with h' | h'
        · exact hbase.2 d' h'
        · rw [List.mem_singleton] at h'
          omega
      · rw [if_neg h]
        refine ⟨?_, by simp⟩
        intro b hb
        rcases List.mem_append.mp hb with h' | h'
        · exact hbase.1 b h'
        · rw [List.mem_singleton] at h'
          subst h'
          exact hbase.2

/-- A block of digits `< 4` has value below `4 ^ length`. -/
lemma digitVal_lt (b : List ℕ) (hb : ∀ d ∈ b, d < 4) : digitVal b < 4 ^ b.length := by
  induction b with
  | nil => simp [digitVal]
  | cons d rest ih =>
      have hd : d < 4 := hb d (List.mem_cons_self ..)
      have hr : digitVal rest < 4 ^ rest.length :=
        ih (fun d' hd' => hb d' (List.mem_cons_of_mem _ hd'))
      simp only [digitVal, List.length_cons, pow_succ]
      omega

/-- The base-4 digits of a block value are the block digits (with implicit zeros
beyond the block). -/
lemma dig4_digitVal (b : List ℕ) (hb : ∀ d ∈ b, d < 4) :
    ∀ k, dig4 (digitVal b) k = b.getD k 0 := by
  induction b with
  | nil => intro k; simp [digitVal, dig4]
  | cons d rest ih =>
      intro k
      have hd : d < 4 := hb d (List.mem_cons_self ..)
      have hrest : ∀ d' ∈ rest, d' < 4 := fun d' hd' => hb d' (List.mem_cons_of_mem _ hd')
      cases k with
      | zero =>
          simp only [digitVal, dig4, pow_zero, Nat.div_one, List.getD_cons_zero]
          omega
      | succ k =>
          simp only [digitVal, List.getD_cons_succ]
          rw [← ih hrest k, dig4, dig4, pow_succ]
          rw [Nat.mul_comm (4 ^ k) 4, ← Nat.div_div_eq_div_mul]
          congr 2
          omega

lemma len4_digitVal_le (b : List ℕ) (hb : ∀ d ∈ b, d < 4) :
    len4 (digitVal b) ≤ b.length := by
  rw [len4_le_iff]
  exact digitVal_lt b hb

/-! ### Per-block tracking (the scan invariants)

`blkTrack s j` is block `j` as seen mid-fold — a completed block, the current partial
(when `j` is the next index), or `[]`.  Its step recurrence is what the fueled scans
iterate; the final-select lemma discharges the closed/unclosed distinction. -/

/-- Block `j` of the running split, counting the trailing partial as next block. -/
def blkTrack (s : List (List ℕ) × List ℕ) (j : ℕ) : List ℕ := (s.1 ++ [s.2]).getD j []

lemma blkTrack_blockStep (s : List (List ℕ) × List ℕ) (d j : ℕ) :
    blkTrack (blockStep s d) j =
      if d < 4 ∧ s.1.length = j then blkTrack s j ++ [d] else blkTrack s j := by
  obtain ⟨bs, cur⟩ := s
  rw [blockStep]
  by_cases hd : d < 4
  · rw [if_pos hd]
    simp only
    rcases Nat.lt_trichotomy j bs.length with hj | hj | hj
    · rw [if_neg (by simp only [not_and]; intro; omega), blkTrack, blkTrack]
      simp only
      rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hj]
    · subst hj
      rw [if_pos ⟨hd, rfl⟩, blkTrack, blkTrack]
      simp only
      rw [List.getD_append_right _ _ _ _ (le_refl _),
        List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    · rw [if_neg (by simp only [not_and]; intro; omega), blkTrack, blkTrack]
      simp only
      rw [List.getD_eq_default _ _ (by simp only [List.length_append,
          List.length_cons, List.length_nil]; omega),
        List.getD_eq_default _ _ (by simp only [List.length_append,
          List.length_cons, List.length_nil]; omega)]
  · rw [if_neg hd, if_neg (by simp only [not_and]; intro; omega)]
    rw [blkTrack, blkTrack]
    simp only
    by_cases hj : j < bs.length + 1
    · rw [List.getD_append _ _ _ _ (by simp only [List.length_append,
        List.length_cons, List.length_nil]; omega)]
    · have hge : (bs ++ [cur]).length ≤ j := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hRHS : (bs ++ [cur]).getD j [] = [] := List.getD_eq_default _ _ hge
      have hLHS : ((bs ++ [cur]) ++ [([] : List ℕ)]).getD j [] = [] := by
        rw [List.getD_append_right _ _ _ _ hge]
        generalize j - (bs ++ [cur]).length = k
        cases k <;> simp
      rw [hLHS, hRHS]

lemma blkTrack_closed (s : List (List ℕ) × List ℕ) {j : ℕ} (hj : j < s.1.length) :
    blkTrack s j = s.1.getD j [] := by
  rw [blkTrack, List.getD_append _ _ _ _ hj]

lemma blockStep_fst_length (s : List (List ℕ) × List ℕ) (d : ℕ) :
    (blockStep s d).1.length =
      if d < 4 then s.1.length else s.1.length + 1 := by
  rw [blockStep]
  by_cases h : d < 4 <;> simp [h]

lemma blockSplit_fst_length_le (ds : List ℕ) :
    (blockSplit ds).1.length ≤ ds.length := by
  suffices h : ∀ init : List (List ℕ) × List ℕ,
      (List.foldl blockStep init ds).1.length ≤ init.1.length + ds.length by
    simpa [blockSplit] using h ([], [])
  induction ds with
  | nil => intro init; simp
  | cons d rest ih =>
      intro init
      rw [List.foldl_cons, List.length_cons]
      refine le_trans (ih (blockStep init d)) ?_
      rw [blockStep_fst_length]
      split <;> omega

/-- Snoc access: appending one element shifts `getD` in the expected way. -/
lemma getD_snoc (l : List ℕ) (d k : ℕ) :
    (l ++ [d]).getD k 0 = if l.length = k then d else l.getD k 0 := by
  rcases Nat.lt_trichotomy k l.length with h | h | h
  · rw [if_neg (by omega), List.getD_append _ _ _ _ h]
  · subst h
    rw [if_pos rfl, List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · rw [if_neg (by omega),
      List.getD_eq_default _ _ (show (l ++ [d]).length ≤ k by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega),
      List.getD_eq_default _ _ (by omega : l.length ≤ k)]

/-! ### The fueled block scans

Each scan iterates `PolyFueled.prec` over the digit index of an emitted stream, with a
small packed state.  The specs are phrased over the *virtual prefix* — the digits the
emitter itself produces — so the `prec` step equations hold unconditionally, and the
final evaluation at the emitted length rewrites to the actual stream. -/

/-- The first `i` digits the emitter produces for day `n`. -/
def vpre (tokenFn : ℕ → ℕ) (n i : ℕ) : List ℕ :=
  (List.range i).map fun k => tokenFn (Nat.pair n k)

lemma vpre_succ (tokenFn : ℕ → ℕ) (n i : ℕ) :
    vpre tokenFn n (i + 1) = vpre tokenFn n i ++ [tokenFn (Nat.pair n i)] := by
  rw [vpre, List.range_succ, List.map_append, vpre]
  rfl

lemma vpre_eq_stream {s : ℕ → List ℕ} {tokenFn lenFn : ℕ → ℕ}
    (hslen : ∀ n, (s n).length = lenFn n)
    (hget : ∀ n i, i < lenFn n → tokenFn (Nat.pair n i) = (s n).getD i 0) (n : ℕ) :
    vpre tokenFn n (lenFn n) = s n := by
  apply List.ext_getElem
  · simp [vpre, hslen n]
  · intro i h1 h2
    simp only [vpre, List.getElem_map, List.getElem_range]
    rw [hget n i (by simpa [vpre] using h1)]
    exact List.getD_eq_getElem (s n) 0 h2

/-- The completed-block count of the virtual prefix is poly-fueled. -/
lemma blockCount_polyFueled {ct : Code} {tokenFn : ℕ → ℕ}
    (htok : PolyFueled ct tokenFn) :
    ∃ c, PolyFueled c (fun z =>
      (blockSplit (vpre tokenFn z.unpair.1 z.unpair.2)).1.length) := by
  -- Step on `⟨n, ⟨i, prev⟩⟩`: bump on terminator digits.
  have hd := htok.comp (PolyFueled.left.pair (PolyFueled.left.comp PolyFueled.right))
  have hprev := PolyFueled.right.comp PolyFueled.right
  have htest := subc_polyFueled.comp (hd.pair (PolyFueled.const 3))
  have hstep := ifzSel_polyFueled.comp ((hprev.pair hprev.succ_comp).pair htest)
  refine ⟨_, PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun n i => (blockSplit (vpre tokenFn n i)).1.length)
    (fun n => by simp [vpre, blockSplit])
    (fun n i => ?_)
    (⟨1, 1, fun z => ?_⟩)⟩
  · simp only [Nat.unpair_pair, ifzSelFn]
    rw [vpre_succ, blockSplit_snoc, blockStep_fst_length]
    by_cases h : tokenFn (Nat.pair n i) < 4
    · rw [if_pos h, if_pos (by omega : tokenFn (Nat.pair n i) - 3 = 0)]
    · rw [if_neg h, if_neg (by omega : ¬ tokenFn (Nat.pair n i) - 3 = 0)]
  · simp only []
    have h1 := blockSplit_fst_length_le (vpre tokenFn z.unpair.1 z.unpair.2)
    have h2 : (vpre tokenFn z.unpair.1 z.unpair.2).length = z.unpair.2 := by
      simp [vpre]
    have h3 := Nat.unpair_right_le z
    rw [pow_one]
    omega

lemma pair_le_one_add_sq (z : ℕ) : Nat.pair z z ≤ 1 * (z + 1) ^ 2 + 1 := by
  have hp : Nat.pair z z = z * z + z + z := by
    rw [Nat.pair, if_neg (lt_irrefl z)]
  have hsq : (z + 1) ^ 2 = z * z + 2 * z + 1 := by ring
  omega

lemma blockSplit_track_length_le (ds : List ℕ) (j : ℕ) :
    (blkTrack (blockSplit ds) j).length ≤ ds.length := by
  suffices h : ∀ init : List (List ℕ) × List ℕ,
      (blkTrack (List.foldl blockStep init ds) j).length ≤
        (blkTrack init j).length + ds.length by
    simpa [blockSplit, blkTrack] using h ([], [])
  induction ds with
  | nil => intro init; simp
  | cons d rest ih =>
      intro init
      rw [List.foldl_cons, List.length_cons]
      refine le_trans (ih (blockStep init d)) ?_
      rw [blkTrack_blockStep]
      split
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · omega

lemma blkTrack_digits_lt (ds : List ℕ) (j : ℕ) :
    ∀ d ∈ blkTrack (blockSplit ds) j, d < 4 := by
  intro d hd
  rw [blkTrack] at hd
  by_cases hj : j < ((blockSplit ds).1 ++ [(blockSplit ds).2]).length
  · have hget := List.getD_eq_getElem ((blockSplit ds).1 ++ [(blockSplit ds).2]) [] hj
    rw [hget] at hd
    have hmem := List.getElem_mem (l := (blockSplit ds).1 ++ [(blockSplit ds).2]) hj
    rcases List.mem_append.mp hmem with hb | hb
    · exact (blockSplit_digits_lt ds).1 _ hb d hd
    · rw [List.mem_singleton] at hb
      exact (blockSplit_digits_lt ds).2 d (hb ▸ hd)
  · rw [List.getD_eq_default _ _ (by omega)] at hd
    simp at hd

/-- The `blkTrack` length scan: state `⟨count, trackLen⟩` at `⟨⟨n,j⟩, i⟩`. -/
lemma blkTrackLen_polyFueled {ct : Code} {tokenFn : ℕ → ℕ}
    (htok : PolyFueled ct tokenFn) :
    ∃ c, PolyFueled c (fun z =>
      Nat.pair
        (blockSplit (vpre tokenFn z.unpair.1.unpair.1 z.unpair.2)).1.length
        (blkTrack (blockSplit (vpre tokenFn z.unpair.1.unpair.1 z.unpair.2))
          z.unpair.1.unpair.2).length) := by
  -- `z = ⟨⟨n,j⟩, ⟨i, prev⟩⟩` in the step.
  have hn := PolyFueled.left.comp PolyFueled.left
  have hj := PolyFueled.right.comp PolyFueled.left
  have hi := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hcount := PolyFueled.left.comp hprev
  have htl := PolyFueled.right.comp hprev
  have hd := htok.comp (hn.pair hi)
  have ht1 := subc_polyFueled.comp (hd.pair (PolyFueled.const 3))
  obtain ⟨cad, had⟩ := addc_polyFueled
  have ht2 := had.comp ((subc_polyFueled.comp (hcount.pair hj)).pair
    (subc_polyFueled.comp (hj.pair hcount)))
  have hcount' := ifzSel_polyFueled.comp ((hcount.pair hcount.succ_comp).pair ht1)
  have htlInner := ifzSel_polyFueled.comp ((htl.succ_comp.pair htl).pair ht2)
  have htl' := ifzSel_polyFueled.comp ((htlInner.pair htl).pair ht1)
  have hstep := hcount'.pair htl'
  refine ⟨_, PolyFueled.prec (PolyFueled.const (Nat.pair 0 0)) hstep
    (st := fun a i => Nat.pair
      (blockSplit (vpre tokenFn a.unpair.1 i)).1.length
      (blkTrack (blockSplit (vpre tokenFn a.unpair.1 i)) a.unpair.2).length)
    (fun a => by simp [vpre, blockSplit, blkTrack])
    (fun a i => ?_)
    (⟨1, 2, fun z => ?_⟩)⟩
  · simp only [Nat.unpair_pair, ifzSelFn]
    rw [vpre_succ, blockSplit_snoc, blockStep_fst_length, blkTrack_blockStep]
    set C := (blockSplit (vpre tokenFn a.unpair.1 i)).1.length with hC
    by_cases h1 : tokenFn (Nat.pair a.unpair.1 i) < 4
    · have hd0 : tokenFn (Nat.pair a.unpair.1 i) - 3 = 0 := by omega
      by_cases h2 : C = a.unpair.2
      · have ht20 : C - a.unpair.2 + (a.unpair.2 - C) = 0 := by omega
        rw [if_pos h1, if_pos ⟨h1, h2⟩, if_pos hd0, if_pos ht20, if_pos hd0]
        simp [List.length_append]
      · have ht2n : ¬ C - a.unpair.2 + (a.unpair.2 - C) = 0 := by omega
        have hcn : ¬ (tokenFn (Nat.pair a.unpair.1 i) < 4 ∧ C = a.unpair.2) := by
          tauto
        rw [if_pos h1, if_neg hcn, if_pos hd0, if_neg ht2n, if_pos hd0]
    · have hdn : ¬ tokenFn (Nat.pair a.unpair.1 i) - 3 = 0 := by omega
      have hcn : ¬ (tokenFn (Nat.pair a.unpair.1 i) < 4 ∧ C = a.unpair.2) := by
        tauto
      rw [if_neg h1, if_neg hcn, if_neg hdn, if_neg hdn]
  · simp only []
    have hpre : (vpre tokenFn z.unpair.1.unpair.1 z.unpair.2).length = z.unpair.2 := by
      simp [vpre]
    have h1 : (blockSplit (vpre tokenFn z.unpair.1.unpair.1 z.unpair.2)).1.length ≤ z := by
      have := blockSplit_fst_length_le (vpre tokenFn z.unpair.1.unpair.1 z.unpair.2)
      have := Nat.unpair_right_le z
      omega
    have h2 : (blkTrack (blockSplit (vpre tokenFn z.unpair.1.unpair.1 z.unpair.2))
        z.unpair.1.unpair.2).length ≤ z := by
      have := blockSplit_track_length_le (vpre tokenFn z.unpair.1.unpair.1 z.unpair.2)
        z.unpair.1.unpair.2
      have := Nat.unpair_right_le z
      omega
    exact le_trans (le_trans (pair_le_pair_left' _ h1) (pair_le_pair_right' _ h2))
      (pair_le_one_add_sq z)

/-- The block digit scan: state `⟨count, ⟨trackLen, ans⟩⟩` at `⟨⟨⟨n,j⟩,k⟩, i⟩`, where
`ans` is digit `k` of block `j` seen so far (digits stored are `< 4`, so the whole
state stays small). -/
lemma blkDig_polyFueled {ct : Code} {tokenFn : ℕ → ℕ}
    (htok : PolyFueled ct tokenFn) :
    ∃ c, PolyFueled c (fun z =>
      Nat.pair
        (blockSplit (vpre tokenFn z.unpair.1.unpair.1.unpair.1 z.unpair.2)).1.length
        (Nat.pair
          (blkTrack (blockSplit (vpre tokenFn z.unpair.1.unpair.1.unpair.1 z.unpair.2))
            z.unpair.1.unpair.1.unpair.2).length
          ((blkTrack (blockSplit (vpre tokenFn z.unpair.1.unpair.1.unpair.1 z.unpair.2))
            z.unpair.1.unpair.1.unpair.2).getD z.unpair.1.unpair.2 0))) := by
  -- Step input `⟨a, ⟨i, prev⟩⟩` with `a = ⟨⟨n,j⟩,k⟩`.
  have hn := PolyFueled.left.comp (PolyFueled.left.comp PolyFueled.left)
  have hj := PolyFueled.right.comp (PolyFueled.left.comp PolyFueled.left)
  have hk := PolyFueled.right.comp PolyFueled.left
  have hi := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hcount := PolyFueled.left.comp hprev
  have htl := PolyFueled.left.comp (PolyFueled.right.comp hprev)
  have hans := PolyFueled.right.comp (PolyFueled.right.comp hprev)
  have hd := htok.comp (hn.pair hi)
  obtain ⟨cad, had⟩ := addc_polyFueled
  have ht1 := subc_polyFueled.comp (hd.pair (PolyFueled.const 3))
  have ht2 := had.comp ((subc_polyFueled.comp (hcount.pair hj)).pair
    (subc_polyFueled.comp (hj.pair hcount)))
  have ht3 := had.comp ((subc_polyFueled.comp (htl.pair hk)).pair
    (subc_polyFueled.comp (hk.pair htl)))
  have hcount' := ifzSel_polyFueled.comp ((hcount.pair hcount.succ_comp).pair ht1)
  have htlInner := ifzSel_polyFueled.comp ((htl.succ_comp.pair htl).pair ht2)
  have htl' := ifzSel_polyFueled.comp ((htlInner.pair htl).pair ht1)
  have hans3 := ifzSel_polyFueled.comp ((hd.pair hans).pair ht3)
  have hans2 := ifzSel_polyFueled.comp ((hans3.pair hans).pair ht2)
  have hans' := ifzSel_polyFueled.comp ((hans2.pair hans).pair ht1)
  have hstep := hcount'.pair (htl'.pair hans')
  have hBpoly : IsPolyBounded (fun z : ℕ => Nat.pair z (Nat.pair z (z + 3))) :=
    (IsPolyBounded.linear 0).pair ((IsPolyBounded.linear 0).pair
      (IsPolyBounded.linear 3))
  refine ⟨_, PolyFueled.prec (PolyFueled.const (Nat.pair 0 (Nat.pair 0 0))) hstep
    (st := fun a i => Nat.pair
      (blockSplit (vpre tokenFn a.unpair.1.unpair.1 i)).1.length
      (Nat.pair
        (blkTrack (blockSplit (vpre tokenFn a.unpair.1.unpair.1 i))
          a.unpair.1.unpair.2).length
        ((blkTrack (blockSplit (vpre tokenFn a.unpair.1.unpair.1 i))
          a.unpair.1.unpair.2).getD a.unpair.2 0)))
    (fun a => by simp [vpre, blockSplit, blkTrack])
    (fun a i => ?_)
    (hBpoly.of_le (fun z => ?_))⟩
  · simp only [Nat.unpair_pair, ifzSelFn]
    rw [vpre_succ, blockSplit_snoc, blockStep_fst_length, blkTrack_blockStep]
    set D := tokenFn (Nat.pair a.unpair.1.unpair.1 i) with hD
    set C := (blockSplit (vpre tokenFn a.unpair.1.unpair.1 i)).1.length with hC
    set TR := blkTrack (blockSplit (vpre tokenFn a.unpair.1.unpair.1 i))
      a.unpair.1.unpair.2 with hTR
    set J := a.unpair.1.unpair.2 with hJ
    set K := a.unpair.2 with hK
    congr 1
    · by_cases h1 : D < 4
      · rw [if_pos h1, if_pos (by omega : D - 3 = 0)]
      · rw [if_neg h1, if_neg (by omega : ¬ D - 3 = 0)]
    congr 1
    · by_cases h1 : D < 4
      · by_cases h2 : C = J
        · rw [if_pos (show D < 4 ∧ C = J from ⟨h1, h2⟩),
            if_pos (by omega : D - 3 = 0), if_pos (by omega : C - J + (J - C) = 0)]
          simp [List.length_append]
        · rw [if_neg (show ¬ (D < 4 ∧ C = J) by tauto),
            if_pos (by omega : D - 3 = 0), if_neg (by omega : ¬ C - J + (J - C) = 0)]
      · rw [if_neg (show ¬ (D < 4 ∧ C = J) by tauto),
          if_neg (by omega : ¬ D - 3 = 0)]
    · by_cases h1 : D < 4
      · by_cases h2 : C = J
        · rw [if_pos (show D < 4 ∧ C = J from ⟨h1, h2⟩), getD_snoc,
            if_pos (by omega : D - 3 = 0), if_pos (by omega : C - J + (J - C) = 0)]
          by_cases h3 : TR.length = K
          · rw [if_pos h3, if_pos (by omega : TR.length - K + (K - TR.length) = 0)]
          · rw [if_neg h3, if_neg (by omega : ¬ TR.length - K + (K - TR.length) = 0)]
        · rw [if_neg (show ¬ (D < 4 ∧ C = J) by tauto),
            if_pos (by omega : D - 3 = 0), if_neg (by omega : ¬ C - J + (J - C) = 0)]
      · rw [if_neg (show ¬ (D < 4 ∧ C = J) by tauto),
          if_neg (by omega : ¬ D - 3 = 0)]
  · simp only []
    have hpre : (vpre tokenFn z.unpair.1.unpair.1.unpair.1 z.unpair.2).length
        = z.unpair.2 := by simp [vpre]
    have h1 : (blockSplit (vpre tokenFn z.unpair.1.unpair.1.unpair.1
        z.unpair.2)).1.length ≤ z := by
      have := blockSplit_fst_length_le
        (vpre tokenFn z.unpair.1.unpair.1.unpair.1 z.unpair.2)
      have := Nat.unpair_right_le z
      omega
    have h2 : (blkTrack (blockSplit (vpre tokenFn z.unpair.1.unpair.1.unpair.1
        z.unpair.2)) z.unpair.1.unpair.1.unpair.2).length ≤ z := by
      have := blockSplit_track_length_le
        (vpre tokenFn z.unpair.1.unpair.1.unpair.1 z.unpair.2)
        z.unpair.1.unpair.1.unpair.2
      have := Nat.unpair_right_le z
      omega
    have h3 : (blkTrack (blockSplit (vpre tokenFn z.unpair.1.unpair.1.unpair.1
        z.unpair.2)) z.unpair.1.unpair.1.unpair.2).getD z.unpair.1.unpair.2 0
        ≤ z + 3 := by
      set TR := blkTrack (blockSplit (vpre tokenFn z.unpair.1.unpair.1.unpair.1
        z.unpair.2)) z.unpair.1.unpair.1.unpair.2 with hTR
      by_cases hkk : z.unpair.1.unpair.2 < TR.length
      · have hget := List.getD_eq_getElem TR 0 hkk
        rw [hget]
        have hmem := List.getElem_mem (l := TR) hkk
        have := blkTrack_digits_lt (vpre tokenFn z.unpair.1.unpair.1.unpair.1
          z.unpair.2) z.unpair.1.unpair.1.unpair.2 _ hmem
        omega
      · rw [List.getD_eq_default _ _ (by omega)]
        omega
    exact le_trans (pair_le_pair_right' _ (le_trans (pair_le_pair_right' _ h3)
      (pair_le_pair_left' _ h2))) (pair_le_pair_left' _ h1)

lemma getD_map_digitVal (bl : List (List ℕ)) (j : ℕ) :
    (bl.map digitVal).getD j 0 = digitVal (bl.getD j []) := by
  by_cases hj : j < bl.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      List.getD_eq_getElem _ _ hj]
  · rw [List.getD_eq_default _ _ (by simpa using hj),
      List.getD_eq_default _ _ (by omega)]
    rfl

/-- Digits of a possibly-out-of-range block are `< 4` (vacuously for `[]`). -/
lemma blockSplit_getD_digits_lt (ds : List ℕ) (j : ℕ) :
    ∀ d ∈ (blockSplit ds).1.getD j [], d < 4 := by
  by_cases hj : j < (blockSplit ds).1.length
  · intro d hd
    rw [List.getD_eq_getElem _ _ hj] at hd
    exact (blockSplit_digits_lt ds).1 _ (List.getElem_mem hj) d hd
  · rw [List.getD_eq_default _ _ (by omega)]
    intro d hd
    simp at hd

/-- **The undigitize view**: any digit `PolySegStream` gives a poly-fueled token count
and `BigDigits` access to the tokens of its undigitized stream (indexed by `⟨n, j⟩`).
This is the read-side interface the digit-model transducers consume: token *values* may
be exponential, but their digit counts and digits are poly-fueled. -/
lemma PolySegStream.undigitizeTokens {s : ℕ → List ℕ} (h : PolySegStream s) :
    (∃ c, PolyFueled c (fun n => (undigitize (s n)).length)) ∧
      BigDigits (fun z => (undigitize (s z.unpair.1)).getD z.unpair.2 0) := by
  obtain ⟨ct, cl, tokenFn, lenFn, htok, hlen, hslen, hget⟩ := h
  have hvs : ∀ n, vpre tokenFn n (lenFn n) = s n := vpre_eq_stream hslen hget
  have hcountS : ∀ n, (undigitize (s n)).length = (blockSplit (s n)).1.length := by
    intro n
    rw [undigitize_eq_blockSplit, List.length_map]
  have htokS : ∀ n j, (undigitize (s n)).getD j 0 =
      digitVal ((blockSplit (s n)).1.getD j []) := by
    intro n j
    rw [undigitize_eq_blockSplit, getD_map_digitVal]
  obtain ⟨cc, hcc⟩ := blockCount_polyFueled htok
  obtain ⟨ctr, htr⟩ := blkTrackLen_polyFueled htok
  obtain ⟨cdg, hdg⟩ := blkDig_polyFueled htok
  -- Token count.
  have hcount : ∃ c, PolyFueled c (fun n => (undigitize (s n)).length) := by
    refine ⟨_, (hcc.comp (PolyFueled.id.pair hlen)).of_eq (fun n => ?_)⟩
    simp only [Nat.unpair_pair]
    rw [hvs n, hcountS n]
  -- Per-token digit access.  Input `w = ⟨⟨n,j⟩,k⟩`; run the digit scan to the end of
  -- the stream and select `0` for the unclosed/out-of-range blocks.
  have hnW := PolyFueled.left.comp PolyFueled.left
  have hjW := PolyFueled.right.comp PolyFueled.left
  have hscan := hdg.comp (PolyFueled.id.pair (hlen.comp hnW))
  have hcountW := PolyFueled.left.comp hscan
  have hansW := PolyFueled.right.comp (PolyFueled.right.comp hscan)
  have htest := subc_polyFueled.comp (hjW.succ_comp.pair hcountW)
  have hdig : PolyFueled _ (fun w => dig4
      ((undigitize (s w.unpair.1.unpair.1)).getD w.unpair.1.unpair.2 0)
      w.unpair.2) :=
    (ifzSel_polyFueled.comp ((hansW.pair (PolyFueled.const 0)).pair htest)).of_eq
      (fun w => by
        simp only [Nat.unpair_pair, ifzSelFn]
        rw [hvs, htokS]
        rw [dig4_digitVal _ (blockSplit_getD_digits_lt (s w.unpair.1.unpair.1)
          w.unpair.1.unpair.2)]
        by_cases hj : w.unpair.1.unpair.2 <
            (blockSplit (s w.unpair.1.unpair.1)).1.length
        · rw [if_pos (by omega :
            w.unpair.1.unpair.2 + 1 -
              (blockSplit (s w.unpair.1.unpair.1)).1.length = 0)]
          rw [blkTrack_closed _ hj]
        · rw [if_neg (by omega :
            ¬ w.unpair.1.unpair.2 + 1 -
              (blockSplit (s w.unpair.1.unpair.1)).1.length = 0)]
          rw [List.getD_eq_default (l := (blockSplit
            (s w.unpair.1.unpair.1)).1) _ (by omega)]
          simp)
  -- Token digit count, from the generic scanner under the closed-block-length bound.
  have hscan2 := htr.comp (PolyFueled.id.pair (hlen.comp PolyFueled.left))
  have hcount2 := PolyFueled.left.comp hscan2
  have htl2 := PolyFueled.right.comp hscan2
  have htest2 := subc_polyFueled.comp (PolyFueled.right.succ_comp.pair hcount2)
  have hB := ifzSel_polyFueled.comp ((htl2.pair (PolyFueled.const 0)).pair htest2)
  obtain ⟨clen, hlenTok⟩ := BigDigits.len_of_digits
    (s := fun m => (undigitize (s m.unpair.1)).getD m.unpair.2 0) hdig hB (fun m => by
    simp only [Nat.unpair_pair, ifzSelFn]
    rw [hvs, htokS]
    by_cases hj : m.unpair.2 < (blockSplit (s m.unpair.1)).1.length
    · rw [if_pos (by omega :
        m.unpair.2 + 1 - (blockSplit (s m.unpair.1)).1.length = 0),
        blkTrack_closed _ hj]
      exact len4_digitVal_le _ (blockSplit_getD_digits_lt (s m.unpair.1) m.unpair.2)
    · rw [if_neg (by omega :
        ¬ m.unpair.2 + 1 - (blockSplit (s m.unpair.1)).1.length = 0),
        List.getD_eq_default (l := (blockSplit (s m.unpair.1)).1) _ (by omega)]
      simp [len4_zero])
  exact ⟨hcount, _, _, hlenTok, hdig⟩

/-! ## The digit-level freeze-mode scan

The conditioning transducer's parser control (`EF.freezeTokenNext`, Properties layer)
tracks a mode `≤ 5` plus the pending sentence code.  In the digit model the pending
code may be exponential, so the scan tracks the mode only — the pending code is
recovered *by position* (it is always the immediately preceding token).  The mode
transitions test the token against the small serializer tags `0/1/6/7`, so they factor
through the clamp `min token 9`; that is what makes the scan poly-fueled over tokens
whose values are held only as digit blocks. -/

/-- Mode component of the freeze automaton (mirror of `EF.freezeTokenNext`'s first
component; the pending payload is dropped). -/
def freezeMode4Step (m t : ℕ) : ℕ :=
  if m = 0 then
    if t = 0 then 1
    else if t = 1 then 3
    else if t = 6 then 4
    else if t = 7 then 5
    else 0
  else if m = 1 then 2
  else 0

/-- Mode after consuming a token prefix. -/
def freezeMode4 (ts : List ℕ) : ℕ := ts.foldl freezeMode4Step 0

lemma freezeMode4Step_le (m t : ℕ) : freezeMode4Step m t ≤ 5 := by
  rw [freezeMode4Step]
  split_ifs <;> omega

lemma foldl_freezeMode4Step_le (ts : List ℕ) : ∀ {m}, m ≤ 5 →
    ts.foldl freezeMode4Step m ≤ 5 := by
  induction ts with
  | nil => intro m hm; exact hm
  | cons t rest ih => intro m _; exact ih (freezeMode4Step_le m t)

lemma freezeMode4_le (ts : List ℕ) : freezeMode4 ts ≤ 5 :=
  foldl_freezeMode4Step_le ts (by norm_num)

lemma freezeMode4_snoc (ts : List ℕ) (t : ℕ) :
    freezeMode4 (ts ++ [t]) = freezeMode4Step (freezeMode4 ts) t := by
  rw [freezeMode4, List.foldl_append, List.foldl_cons, List.foldl_nil, freezeMode4]

/-- The mode transitions only test the small tags, so they factor through the clamp. -/
lemma freezeMode4Step_clamp (m t : ℕ) :
    freezeMode4Step m (min t 9) = freezeMode4Step m t := by
  by_cases h : t ≤ 9
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega : 9 ≤ t)]
    rw [freezeMode4Step, freezeMode4Step]
    split_ifs <;> omega

/-- **The freeze-mode scan**: over any digit `PolySegStream`, the freeze mode at each
token position of the undigitized stream is poly-fueled (input `⟨n, j⟩`; the mode is
taken over the virtual token prefix `vpre`, which agrees with the actual token stream
at every `j ≤` token count). -/
lemma PolySegStream.freezeModeScan {s : ℕ → List ℕ} (h : PolySegStream s) :
    ∃ c, PolyFueled c (fun z =>
      freezeMode4 (vpre (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0)
        z.unpair.1 z.unpair.2)) := by
  obtain ⟨-, hbig⟩ := h.undigitizeTokens
  obtain ⟨ctc, htc⟩ := hbig.clampVal (PolyFueled.const 8)
  obtain ⟨cad, had⟩ := addc_polyFueled
  -- Step input `⟨n, ⟨j, prev⟩⟩`.
  have hn := PolyFueled.left
  have hj := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have htok := htc.comp (hn.pair hj)
  have heq1 := had.comp ((subc_polyFueled.comp (htok.pair (PolyFueled.const 1))).pair
    (subc_polyFueled.comp ((PolyFueled.const 1).pair htok)))
  have heq6 := had.comp ((subc_polyFueled.comp (htok.pair (PolyFueled.const 6))).pair
    (subc_polyFueled.comp ((PolyFueled.const 6).pair htok)))
  have heq7 := had.comp ((subc_polyFueled.comp (htok.pair (PolyFueled.const 7))).pair
    (subc_polyFueled.comp ((PolyFueled.const 7).pair htok)))
  have hA3 := ifzSel_polyFueled.comp
    (((PolyFueled.const 5).pair (PolyFueled.const 0)).pair heq7)
  have hA2 := ifzSel_polyFueled.comp (((PolyFueled.const 4).pair hA3).pair heq6)
  have hA1 := ifzSel_polyFueled.comp (((PolyFueled.const 3).pair hA2).pair heq1)
  have hA0 := ifzSel_polyFueled.comp (((PolyFueled.const 1).pair hA1).pair htok)
  have hM1 := ifzSel_polyFueled.comp
    (((PolyFueled.const 2).pair (PolyFueled.const 0)).pair
      (subc_polyFueled.comp (hprev.pair (PolyFueled.const 1))))
  have hstep := ifzSel_polyFueled.comp ((hA0.pair hM1).pair hprev)
  refine ⟨_, PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun n j =>
      freezeMode4 (vpre (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0) n j))
    (fun n => by simp [vpre, freezeMode4])
    (fun n j => ?_)
    ((IsPolyBounded.linear 5).of_le fun z =>
      le_trans (freezeMode4_le _) (by omega))⟩
  simp only []
  rw [vpre_succ, freezeMode4_snoc, ← freezeMode4Step_clamp]
  simp only [freezeMode4Step, Nat.unpair_pair, ifzSelFn, Nat.reduceAdd]
  split_ifs <;> omega

/-- **Bounded day materialization**: `min token (n+1)` at each token position — exact
when the token (a price day, at mode-2 positions) is `≤ n`, the sentinel `n+1`
otherwise.  This is the day-sanity test of the digit transducer: an in-range day is
recovered exactly, an oversized day is detected without ever materializing it. -/
lemma PolySegStream.dayClampTokens {s : ℕ → List ℕ} (h : PolySegStream s) :
    ∃ c, PolyFueled c (fun z =>
      min ((undigitize (s z.unpair.1)).getD z.unpair.2 0) (z.unpair.1 + 1)) :=
  h.undigitizeTokens.2.clampVal PolyFueled.left

/-! ## Digit-metered sentence-code sequences (the Tranche-4 hypothesis core)

`PolySentenceCodes` demands a polynomial code *value* — admitting only sentences whose
`Encodable` pair-codes stay small.  The digit-metered widening demands only poly-fueled
*digit access*: sequences whose code bit-size is polynomial in the day qualify, code
values may be exponential.  Property endpoints migrate hypothesis-by-hypothesis as
their exploiting traders' emissions are re-certified in the digit model (the
conditioning family is done; see `DigitConditioning.lean`); the inclusion below
transfers every existing instantiation. -/

/-- Digit-metered efficient sentence codeability: poly-fueled digit access to the
(possibly exponentially large) codes. -/
def DigitSentenceCodes (φ : ℕ → Sentence) : Prop :=
  BigDigits (fun n => Encodable.encode (φ n))

/-- Every poly-value code sequence has digit access (the inclusion that transfers
existing `PolySentenceCodes` instantiations to digit-metered hypotheses). -/
lemma PolySentenceCodes.toDigit {φ : ℕ → Sentence} (h : PolySentenceCodes φ) :
    DigitSentenceCodes φ := by
  obtain ⟨c, hc⟩ := h
  exact BigDigits.of_polyFueled hc

/-- Digit sentence codes reindex along poly-fueled day maps. -/
lemma DigitSentenceCodes.comp {φ : ℕ → Sentence} (h : DigitSentenceCodes φ)
    {cg : Code} {g : ℕ → ℕ} (hg : PolyFueled cg g) :
    DigitSentenceCodes (fun n => φ (g n)) :=
  BigDigits.comp h hg

#print axioms DigitSentenceCodes
#print axioms PolySentenceCodes.toDigit

#print axioms PolySegStream.freezeModeScan
#print axioms PolySegStream.dayClampTokens

#print axioms PolySegStream.undigitizeTokens
#print axioms BigDigits.add
#print axioms BigDigits.mul
#print axioms BigDigits.natPair
#print axioms BigDigits.blockSeg

end LogicalInduction
