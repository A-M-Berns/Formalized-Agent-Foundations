/-
# A symbol measure on Foundation's internal derivation codes — §4.10

The paper's `Con(Θ′)(ν)` (tex:1855-1866) says there is no proof of `⊥` from `⌜Θ′⌝` with
`ν` **or fewer symbols**.  Metering that statement needs a size function on Foundation's
*arithmetized* derivations, and Foundation has none: there is no size, length, height or
symbol count on internal codes anywhere in its `Bootstrapping` tree (`formulaComplexity` is
connective depth, `bv` a bound-variable bound, and both are `V`-valued internal
recursions).  This module supplies one, externally, at `V := ℕ` — which is the only place
§4.10 meters anything.

## The counting convention

A derivation code is a tree of `⟪…⟫ + 1` nodes (`Bootstrapping/Syntax/Proof/Basic.lean`),
whose leaves reach down through sequents (bitsets of formula codes), formulas, terms and
term vectors (cons lists).  Writing such a derivation out costs:

* one symbol for each rule name, connective, quantifier, predicate or function symbol, and
  each variable occurrence;
* one separator per argument-list entry;
* the **written length of every index**, plus one marker token — a variable, function or
  relation index is a numeral when the proof is written out, so it contributes
  `idxLen n = Nat.size n + 1` rather than one symbol: its binary digit count *and* one
  token separating the numeral from the material that follows it.  (So `idxLen 0 = 1` and
  `idxLen 1 = 2`; the marker makes an index numeral self-delimiting.  Over-counting by a
  fixed token per index is the safe direction — the measure is a metering convention, and
  only the two bounds below are ever spent on it.)  This is what makes the measure
  finite-fibred: without it, `^&x` would be one symbol for every `x`, and a bounded-symbol
  search would range over unboundedly many codes.  It is also the write-out convention the
  rest of this development meters with, `def:ec`.
* every member of a node's sequent, and every sub-derivation, recursively.

The paper fixes neither a Gödel encoding nor an alphabet ("written in `ℒ` using a Gödel
encoding"), so a formalization must choose a convention; this is that choice, stated, and
is the only residue of the retired `dd:proofcode` substitution.  Nothing downstream depends
on the choice beyond the arithmetic of `dSize_pos` and `le_G_dSize`.

Numbers that are not well-formed codes are given their own numeric value.  That branch is
never observed: every use sits under `Bootstrapping.Proof`, which forces well-formedness.
It is what makes the converse bound `d ≤ G (dSize d)` hold *unconditionally*, with no
well-formedness hypothesis to thread.

## Why the converse bound is the point

`dSize d ≤ d` is the useless direction.  What the §4.10 decider needs is
`d ≤ G (dSize d)` for a computable monotone `G`: it turns "some derivation of `φ` has at
most `k` symbols" into a search over `d ≤ G k`, which is decidable in *both* polarities.
`G` is a tower and no attempt is made to make it tight.
-/
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
import Mathlib.Computability.Partrec
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases

namespace LogicalInduction

/-! ## Reading a right-nested pairing

Foundation's `⟪a₀, a₁, …, aₙ⟫` is right-nested `pair`, and at `ℕ` `pair` is `Nat.pair`
(`nat_pair_eq`).  `arg i` reads the `i`-th component; `tail i` reads what is left after `i`
components, which for an `(i+1)`-component pairing is the last one. -/

/-- Left projection of the pairing.  Internal decoding helper. -/
def pl (n : ℕ) : ℕ := (Nat.unpair n).1

/-- Right projection of the pairing.  Internal decoding helper. -/
def pr (n : ℕ) : ℕ := (Nat.unpair n).2

lemma pl_le (n : ℕ) : pl n ≤ n := Nat.unpair_left_le n

lemma pr_le (n : ℕ) : pr n ≤ n := Nat.unpair_right_le n

/-- The `i`-th component of a right-nested pairing.  Internal decoding helper. -/
def arg : ℕ → ℕ → ℕ
  | 0, m => pl m
  | (i + 1), m => arg i (pr m)

/-- What is left of a right-nested pairing after `i` components.  Internal helper. -/
def tail : ℕ → ℕ → ℕ
  | 0, m => m
  | (i + 1), m => tail i (pr m)

lemma tail_le : ∀ (i m : ℕ), tail i m ≤ m
  | 0, _ => le_rfl
  | (i + 1), m => le_trans (tail_le i (pr m)) (pr_le m)

lemma arg_le : ∀ (i m : ℕ), arg i m ≤ m
  | 0, m => pl_le m
  | (i + 1), m => le_trans (arg_le i (pr m)) (pr_le m)

lemma arg_lt_succ (i m : ℕ) : arg i m < m + 1 := Nat.lt_succ_of_le (arg_le i m)

lemma tail_lt_succ (i m : ℕ) : tail i m < m + 1 := Nat.lt_succ_of_le (tail_le i m)

/-! ## Written length of an index -/

/-- The written length of an index: its binary digit count `Nat.size n`, **plus one** for
the marker token that separates the numeral from the following material.  So `idxLen 0 = 1`
and `idxLen 1 = 2` — this is a digit count plus one, not a digit count. -/
def idxLen (n : ℕ) : ℕ := Nat.size n + 1

lemma one_le_idxLen (n : ℕ) : 1 ≤ idxLen n := Nat.le_add_left 1 _

lemma lt_two_pow_idxLen (n : ℕ) : n < 2 ^ idxLen n :=
  lt_of_lt_of_le (Nat.lt_size_self n) (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))

/-! ## Terms and term vectors

Mutually recursive, packed into one function on a mode so that a single well-founded
recursion at `ℕ` carries both: mode `0` reads a term code, any other mode a term-vector
code.  Foundation's vectors are cons lists (`x ∷ v = ⟪x, v⟫ + 1`, nil `= 0`). -/

/-- Terms and term vectors share one well-founded recursion; mode `0` reads a term code,
any other mode a term-vector code. -/
def tvAux : ℕ → ℕ → ℕ
  | _, 0 => 0
  | mode, m + 1 =>
      if mode = 0 then
        (if arg 0 m = 0 then 1 + idxLen (tail 1 m)
         else if arg 0 m = 1 then 1 + idxLen (tail 1 m)
         else if arg 0 m = 2 then
           1 + idxLen (arg 1 m) + idxLen (arg 2 m) + tvAux 1 (tail 3 m)
         else m + 1)
      else 1 + tvAux 0 (arg 0 m) + tvAux 1 (tail 1 m)
termination_by _ n => n
decreasing_by
  · exact tail_lt_succ 3 m
  · exact arg_lt_succ 0 m
  · exact tail_lt_succ 1 m

/-- **Symbol count of a term code.** -/
def tSize (t : ℕ) : ℕ := tvAux 0 t

/-- **Symbol count of a term-vector code**, one separator per entry. -/
def tvSize (v : ℕ) : ℕ := tvAux 1 v

@[simp] lemma tSize_zero : tSize 0 = 0 := by rw [tSize, tvAux]

@[simp] lemma tvSize_zero : tvSize 0 = 0 := by rw [tvSize, tvAux]

lemma tSize_succ (m : ℕ) :
    tSize (m + 1) =
      (if arg 0 m = 0 then 1 + idxLen (tail 1 m)
       else if arg 0 m = 1 then 1 + idxLen (tail 1 m)
       else if arg 0 m = 2 then
         1 + idxLen (arg 1 m) + idxLen (arg 2 m) + tvSize (tail 3 m)
       else m + 1) := by
  rw [tSize, tvAux]; simp [tvSize]

lemma tvSize_succ (m : ℕ) :
    tvSize (m + 1) = 1 + tSize (arg 0 m) + tvSize (tail 1 m) := by
  rw [tvSize, tvAux]; simp [tSize, tvSize]

lemma tvAux_zero_eq (n : ℕ) : tvAux 0 n = tSize n := rfl

lemma tvAux_one_eq (n : ℕ) : tvAux 1 n = tvSize n := rfl

lemma tvAux_succ_of_ne {mode : ℕ} (h : mode ≠ 0) (m : ℕ) :
    tvAux mode (m + 1) = 1 + tSize (arg 0 m) + tvSize (tail 1 m) := by
  rw [tvAux, if_neg h]
  rfl

/-! ## Formulas -/

/-- **Symbol count of a formula code.**  One symbol per connective, quantifier or predicate
symbol; predicate indices and arities are written out; `^⊤` and `^⊥` are one symbol each. -/
def fSize : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
      if arg 0 m = 0 ∨ arg 0 m = 1 then
        1 + idxLen (arg 1 m) + idxLen (arg 2 m) + tvSize (tail 3 m)
      else if arg 0 m = 2 ∨ arg 0 m = 3 then
        (if tail 1 m = 0 then 1 else m + 1)
      else if arg 0 m = 4 ∨ arg 0 m = 5 then
        1 + fSize (arg 1 m) + fSize (tail 2 m)
      else if arg 0 m = 6 ∨ arg 0 m = 7 then
        1 + fSize (tail 1 m)
      else m + 1
termination_by n => n
decreasing_by
  · exact arg_lt_succ 1 m
  · exact tail_lt_succ 2 m
  · exact tail_lt_succ 1 m

/-! ## Sequents

Foundation's sequents are bitsets: `p ∈ s` is `LenBit (exp p) s`, which at `ℕ` is exactly
`s.testBit p` (`mem_iff_testBit` below).  A sequent is written out as its members. -/

/-- **Symbol count of a sequent.** -/
def sSize (s : ℕ) : ℕ := ∑ i ∈ Finset.range s, if s.testBit i then fSize i else 0

/-! ## Derivations -/

/-- **Symbol count of a derivation code.**  One symbol for the rule name, plus the node's
sequent, its principal formulas and terms, and its sub-derivations. -/
def dSize : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
      if arg 1 m = 0 then 1 + sSize (arg 0 m) + fSize (tail 2 m)
      else if arg 1 m = 1 then
        (if tail 2 m = 0 then 1 + sSize (arg 0 m) else m + 1)
      else if arg 1 m = 2 then
        1 + sSize (arg 0 m) + fSize (arg 2 m) + fSize (arg 3 m)
          + dSize (arg 4 m) + dSize (tail 5 m)
      else if arg 1 m = 3 then
        1 + sSize (arg 0 m) + fSize (arg 2 m) + fSize (arg 3 m) + dSize (tail 4 m)
      else if arg 1 m = 4 then
        1 + sSize (arg 0 m) + fSize (arg 2 m) + dSize (tail 3 m)
      else if arg 1 m = 5 then
        1 + sSize (arg 0 m) + fSize (arg 2 m) + tSize (arg 3 m) + dSize (tail 4 m)
      else if arg 1 m = 6 ∨ arg 1 m = 7 then
        1 + sSize (arg 0 m) + dSize (tail 2 m)
      else if arg 1 m = 8 then
        1 + sSize (arg 0 m) + fSize (arg 2 m) + dSize (arg 3 m) + dSize (tail 4 m)
      else if arg 1 m = 9 then
        1 + sSize (arg 0 m) + fSize (tail 2 m)
      else m + 1
termination_by n => n
decreasing_by
  · exact arg_lt_succ 4 m
  · exact tail_lt_succ 5 m
  · exact tail_lt_succ 4 m
  · exact tail_lt_succ 3 m
  · exact tail_lt_succ 4 m
  · exact tail_lt_succ 2 m
  · exact arg_lt_succ 3 m
  · exact tail_lt_succ 4 m

/-! ## The converse bound `d ≤ G (dSize d)`

The bound is unconditional — no well-formedness hypothesis — because the ill-formed branch
of each size function returns the code itself.  `G` is built to absorb, at each unit of
size, one exponential (for a sequent bitset) and six squarings (for a six-component
pairing node). -/

private def P (b : ℕ) : ℕ := (b + 1) ^ 2

private lemma succ_le_P (b : ℕ) : b + 1 ≤ P b := Nat.le_self_pow (by norm_num) _

private lemma le_P (b : ℕ) : b ≤ P b := le_trans (Nat.le_succ b) (succ_le_P b)

private lemma P_mono : Monotone P := fun _ _ h => Nat.pow_le_pow_left (by omega) 2

private lemma P_iter_mono (j : ℕ) : Monotone (P^[j]) := by
  induction j with
  | zero => simpa using monotone_id
  | succ j ih =>
      intro a b h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact P_mono (ih h)

private lemma le_P_iter (j b : ℕ) : b ≤ P^[j] b := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (le_P _)

private lemma P_iter_le_of_le {i j b : ℕ} (h : i ≤ j) : P^[i] b ≤ P^[j] b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Function.iterate_add_apply]
  exact P_iter_mono i (le_P_iter k b)

private lemma pair_le_P {a b B : ℕ} (ha : a ≤ B) (hb : b ≤ B) : Nat.pair a b ≤ P B :=
  le_of_lt (lt_of_lt_of_le (Nat.pair_lt_max_add_one_sq a b) (P_mono (max_le ha hb)))

private lemma pairing_le : ∀ (j m B : ℕ), (∀ i < j, arg i m ≤ B) → tail j m ≤ B →
    m ≤ P^[j] B
  | 0, m, B, _, ht => by simpa [tail] using ht
  | (j + 1), m, B, ha, ht => by
      have h0 : pl m ≤ B := by simpa [arg] using ha 0 (Nat.succ_pos j)
      have hrec : pr m ≤ P^[j] B := by
        refine pairing_le j (pr m) B (fun i hi => ?_) (by simpa [tail] using ht)
        simpa [arg] using ha (i + 1) (Nat.succ_lt_succ hi)
      have hm : m = Nat.pair (pl m) (pr m) := (Nat.pair_unpair m).symm
      rw [Function.iterate_succ_apply', hm]
      exact pair_le_P (le_trans h0 (le_P_iter j B)) hrec

private lemma node_le {j m B : ℕ} (ha : ∀ i < j, arg i m ≤ B) (ht : tail j m ≤ B) :
    m + 1 ≤ P^[j + 1] B := by
  rw [Function.iterate_succ_apply']
  exact le_trans (Nat.succ_le_succ (pairing_le j m B ha ht)) (succ_le_P _)

/-- **The bounding function.**  A tower: each unit of symbol size buys one exponential and
six squarings, which is what the sequent bitsets and the six-component derivation nodes
respectively cost.  No attempt is made to make it tight. -/
def G : ℕ → ℕ
  | 0 => 1
  | (N + 1) => P^[6] (2 ^ (G N + 1) + 9)

/-- The slack available to a node of symbol size `N + 1`. -/
private def Bd (N : ℕ) : ℕ := 2 ^ (G N + 1) + 9

private lemma G_succ (N : ℕ) : G (N + 1) = P^[6] (Bd N) := rfl

private lemma nine_le_Bd (N : ℕ) : 9 ≤ Bd N := Nat.le_add_left 9 _

private lemma G_le_Bd (N : ℕ) : G N ≤ Bd N :=
  le_trans (le_of_lt Nat.lt_two_pow_self)
    (le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)) (Nat.le_add_right _ 9))

private lemma G_lt_G_succ (N : ℕ) : G N < G (N + 1) := by
  rw [G_succ]
  have h0 : G N < 2 ^ (G N) := Nat.lt_two_pow_self
  have h1 : (2 : ℕ) ^ (G N) ≤ 2 ^ (G N + 1) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
  have h2 : G N < Bd N := by unfold Bd; omega
  exact lt_of_lt_of_le h2 (le_P_iter 6 _)

/-- `G` is monotone, which is what lets a bound at one size be reused at any larger one. -/
lemma G_mono : Monotone G := monotone_nat_of_le_succ fun N => le_of_lt (G_lt_G_succ N)

lemma self_le_G : ∀ n : ℕ, n ≤ G n
  | 0 => Nat.zero_le _
  | (n + 1) => Nat.succ_le_of_lt (lt_of_le_of_lt (self_le_G n) (G_lt_G_succ n))

private lemma idx_le_Bd {n N : ℕ} (h : idxLen n ≤ N) : n ≤ Bd N :=
  le_trans (le_of_lt (lt_two_pow_idxLen n))
    (le_trans (Nat.pow_le_pow_right (by norm_num)
      (le_trans h (le_trans (self_le_G N) (Nat.le_succ _)))) (Nat.le_add_right _ 9))

private lemma sub_le_Bd {c k N : ℕ} (h1 : c ≤ G k) (h2 : k ≤ N) : c ≤ Bd N :=
  le_trans (le_trans h1 (G_mono h2)) (G_le_Bd N)

private lemma tag_le_Bd {t N : ℕ} (h : t ≤ 9) : t ≤ Bd N := le_trans h (nine_le_Bd N)

private lemma node_bound {j m N : ℕ} (hj : j ≤ 5)
    (ha : ∀ i < j, arg i m ≤ Bd N) (ht : tail j m ≤ Bd N) : m + 1 ≤ G (N + 1) := by
  rw [G_succ]
  exact le_trans (node_le ha ht) (P_iter_le_of_le (by omega))

/-! ### Terms and term vectors -/

private lemma le_G_tvAux : ∀ (n mode : ℕ), n ≤ G (tvAux mode n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro mode
    match n with
    | 0 => exact Nat.zero_le _
    | (m + 1) =>
      have ih0 : ∀ x < m + 1, x ≤ G (tSize x) := fun x hx => ih x hx 0
      have ih1 : ∀ x < m + 1, x ≤ G (tvSize x) := fun x hx => ih x hx 1
      by_cases hmode : mode = 0
      · subst hmode
        rw [tvAux_zero_eq, tSize_succ]
        by_cases h0 : arg 0 m = 0
        · rw [if_pos h0, show 1 + idxLen (tail 1 m) = idxLen (tail 1 m) + 1 by omega]
          refine node_bound (j := 1) (N := idxLen (tail 1 m)) (by omega) ?_ (idx_le_Bd le_rfl)
          intro i hi
          interval_cases i
          exact tag_le_Bd (by omega)
        · rw [if_neg h0]
          by_cases h1 : arg 0 m = 1
          · rw [if_pos h1, show 1 + idxLen (tail 1 m) = idxLen (tail 1 m) + 1 by omega]
            refine node_bound (j := 1) (N := idxLen (tail 1 m)) (by omega) ?_ (idx_le_Bd le_rfl)
            intro i hi
            interval_cases i
            exact tag_le_Bd (by omega)
          · rw [if_neg h1]
            by_cases h2 : arg 0 m = 2
            · rw [if_pos h2, show 1 + idxLen (arg 1 m) + idxLen (arg 2 m)
                  + tvSize (tail 3 m)
                = (idxLen (arg 1 m) + idxLen (arg 2 m) + tvSize (tail 3 m)) + 1 by omega]
              refine node_bound (j := 3) (by omega) ?_ ?_
              · intro i hi
                interval_cases i
                · exact tag_le_Bd (by omega)
                · exact idx_le_Bd (by omega)
                · exact idx_le_Bd (by omega)
              · exact sub_le_Bd (ih1 _ (tail_lt_succ 3 m)) (by omega)
            · rw [if_neg h2]
              exact self_le_G (m + 1)
      · rw [tvAux_succ_of_ne hmode,
            show 1 + tSize (arg 0 m) + tvSize (tail 1 m)
                = (tSize (arg 0 m) + tvSize (tail 1 m)) + 1 by omega]
        refine node_bound (j := 1) (by omega) ?_ ?_
        · intro i hi
          interval_cases i
          exact sub_le_Bd (ih0 _ (arg_lt_succ 0 m)) (by omega)
        · exact sub_le_Bd (ih1 _ (tail_lt_succ 1 m)) (by omega)

lemma le_G_tSize (n : ℕ) : n ≤ G (tSize n) := le_G_tvAux n 0

lemma le_G_tvSize (n : ℕ) : n ≤ G (tvSize n) := le_G_tvAux n 1

/-! ### Formulas -/

lemma le_G_fSize (n : ℕ) : n ≤ G (fSize n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact Nat.zero_le _
    | (m + 1) =>
      rw [fSize]
      by_cases h01 : arg 0 m = 0 ∨ arg 0 m = 1
      · rw [if_pos h01, show 1 + idxLen (arg 1 m) + idxLen (arg 2 m) + tvSize (tail 3 m)
              = (idxLen (arg 1 m) + idxLen (arg 2 m) + tvSize (tail 3 m)) + 1 by omega]
        refine node_bound (j := 3) (by omega) ?_ ?_
        · intro i hi
          interval_cases i
          · exact tag_le_Bd (by rcases h01 with h | h <;> omega)
          · exact idx_le_Bd (by omega)
          · exact idx_le_Bd (by omega)
        · exact sub_le_Bd (le_G_tvSize (tail 3 m)) (by omega)
      · rw [if_neg h01]
        by_cases h23 : arg 0 m = 2 ∨ arg 0 m = 3
        · rw [if_pos h23]
          by_cases hz : tail 1 m = 0
          · rw [if_pos hz, show (1 : ℕ) = 0 + 1 by omega]
            refine node_bound (j := 1) (N := 0) (by omega) ?_ (by rw [hz]; exact Nat.zero_le _)
            intro i hi
            interval_cases i
            exact tag_le_Bd (by rcases h23 with h | h <;> omega)
          · rw [if_neg hz]
            exact self_le_G (m + 1)
        · rw [if_neg h23]
          by_cases h45 : arg 0 m = 4 ∨ arg 0 m = 5
          · rw [if_pos h45, show 1 + fSize (arg 1 m) + fSize (tail 2 m)
                  = (fSize (arg 1 m) + fSize (tail 2 m)) + 1 by omega]
            refine node_bound (j := 2) (by omega) ?_ ?_
            · intro i hi
              interval_cases i
              · exact tag_le_Bd (by rcases h45 with h | h <;> omega)
              · exact sub_le_Bd (ih _ (arg_lt_succ 1 m)) (by omega)
            · exact sub_le_Bd (ih _ (tail_lt_succ 2 m)) (by omega)
          · rw [if_neg h45]
            by_cases h67 : arg 0 m = 6 ∨ arg 0 m = 7
            · rw [if_pos h67, show 1 + fSize (tail 1 m) = fSize (tail 1 m) + 1 by omega]
              refine node_bound (j := 1) (by omega) ?_ ?_
              · intro i hi
                interval_cases i
                exact tag_le_Bd (by rcases h67 with h | h <;> omega)
              · exact sub_le_Bd (ih _ (tail_lt_succ 1 m)) (by omega)
            · rw [if_neg h67]
              exact self_le_G (m + 1)

/-! ### Sequents -/

private lemma lt_of_testBit {s i : ℕ} (h : s.testBit i = true) : i < s := by
  by_contra hc
  push_neg at hc
  have hlt : s < 2 ^ i := lt_of_le_of_lt hc Nat.lt_two_pow_self
  rw [Nat.testBit_lt_two_pow hlt] at h
  exact Bool.noConfusion h

/-- Every member of a sequent contributes its own symbols to the sequent's count. -/
lemma fSize_le_sSize {s i : ℕ} (h : s.testBit i = true) : fSize i ≤ sSize s := by
  have hi : i ∈ Finset.range s := Finset.mem_range.mpr (lt_of_testBit h)
  have hsum := Finset.single_le_sum
    (f := fun j => if s.testBit j then fSize j else 0) (fun j _ => Nat.zero_le _) hi
  simpa [sSize, h] using hsum

/-- **The sequent bound.**  A bitset whose members all have small formula codes is itself
small: this is the one exponential the tower has to absorb per unit of size. -/
lemma lt_two_pow_G_sSize (s : ℕ) : s < 2 ^ (G (sSize s) + 1) := by
  have hbits : ∀ i, s.testBit (G (sSize s) + 1 + i) = false := by
    intro i
    cases hb : s.testBit (G (sSize s) + 1 + i) with
    | false => rfl
    | true =>
        have h1 : G (sSize s) + 1 + i ≤ G (fSize (G (sSize s) + 1 + i)) := le_G_fSize _
        have h2 : G (fSize (G (sSize s) + 1 + i)) ≤ G (sSize s) := G_mono (fSize_le_sSize hb)
        omega
  have hshift : s >>> (G (sSize s) + 1) = 0 :=
    Nat.eq_of_testBit_eq fun i => by rw [Nat.testBit_shiftRight, hbits i, Nat.zero_testBit]
  rw [Nat.shiftRight_eq_div_pow] at hshift
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mp hshift

private lemma seq_le_Bd {s N : ℕ} (h : sSize s ≤ N) : s ≤ Bd N :=
  le_trans (le_of_lt (lt_two_pow_G_sSize s))
    (le_trans (Nat.pow_le_pow_right (by norm_num) (by have := G_mono h; omega))
      (Nat.le_add_right _ 9))

/-! ### Derivations

The load-bearing statement of the module: a derivation code is bounded by a computable
function of its symbol count.  `dSize d ≤ d` is the useless direction; this is the one that
keeps the bounded search decidable in both polarities. -/

lemma le_G_dSize (n : ℕ) : n ≤ G (dSize n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact Nat.zero_le _
    | (m + 1) =>
      rw [dSize]
      by_cases h0 : arg 1 m = 0
      · rw [if_pos h0, show 1 + sSize (arg 0 m) + fSize (tail 2 m)
              = (sSize (arg 0 m) + fSize (tail 2 m)) + 1 by omega]
        refine node_bound (j := 2) (by omega) ?_ ?_
        · intro i hi
          interval_cases i
          · exact seq_le_Bd (by omega)
          · exact tag_le_Bd (by omega)
        · exact sub_le_Bd (le_G_fSize (tail 2 m)) (by omega)
      · rw [if_neg h0]
        by_cases h1 : arg 1 m = 1
        · rw [if_pos h1]
          by_cases hz : tail 2 m = 0
          · rw [if_pos hz, show 1 + sSize (arg 0 m) = sSize (arg 0 m) + 1 by omega]
            refine node_bound (j := 2) (by omega) ?_ (by rw [hz]; exact Nat.zero_le _)
            intro i hi
            interval_cases i
            · exact seq_le_Bd le_rfl
            · exact tag_le_Bd (by omega)
          · rw [if_neg hz]
            exact self_le_G (m + 1)
        · rw [if_neg h1]
          by_cases h2 : arg 1 m = 2
          · rw [if_pos h2, show 1 + sSize (arg 0 m) + fSize (arg 2 m) + fSize (arg 3 m)
                  + dSize (arg 4 m) + dSize (tail 5 m)
                = (sSize (arg 0 m) + fSize (arg 2 m) + fSize (arg 3 m)
                  + dSize (arg 4 m) + dSize (tail 5 m)) + 1 by omega]
            refine node_bound (j := 5) (by omega) ?_ ?_
            · intro i hi
              interval_cases i
              · exact seq_le_Bd (by omega)
              · exact tag_le_Bd (by omega)
              · exact sub_le_Bd (le_G_fSize (arg 2 m)) (by omega)
              · exact sub_le_Bd (le_G_fSize (arg 3 m)) (by omega)
              · exact sub_le_Bd (ih _ (arg_lt_succ 4 m)) (by omega)
            · exact sub_le_Bd (ih _ (tail_lt_succ 5 m)) (by omega)
          · rw [if_neg h2]
            by_cases h3 : arg 1 m = 3
            · rw [if_pos h3, show 1 + sSize (arg 0 m) + fSize (arg 2 m) + fSize (arg 3 m)
                    + dSize (tail 4 m)
                  = (sSize (arg 0 m) + fSize (arg 2 m) + fSize (arg 3 m)
                    + dSize (tail 4 m)) + 1 by omega]
              refine node_bound (j := 4) (by omega) ?_ ?_
              · intro i hi
                interval_cases i
                · exact seq_le_Bd (by omega)
                · exact tag_le_Bd (by omega)
                · exact sub_le_Bd (le_G_fSize (arg 2 m)) (by omega)
                · exact sub_le_Bd (le_G_fSize (arg 3 m)) (by omega)
              · exact sub_le_Bd (ih _ (tail_lt_succ 4 m)) (by omega)
            · rw [if_neg h3]
              by_cases h4 : arg 1 m = 4
              · rw [if_pos h4, show 1 + sSize (arg 0 m) + fSize (arg 2 m) + dSize (tail 3 m)
                      = (sSize (arg 0 m) + fSize (arg 2 m) + dSize (tail 3 m)) + 1 by omega]
                refine node_bound (j := 3) (by omega) ?_ ?_
                · intro i hi
                  interval_cases i
                  · exact seq_le_Bd (by omega)
                  · exact tag_le_Bd (by omega)
                  · exact sub_le_Bd (le_G_fSize (arg 2 m)) (by omega)
                · exact sub_le_Bd (ih _ (tail_lt_succ 3 m)) (by omega)
              · rw [if_neg h4]
                by_cases h5 : arg 1 m = 5
                · rw [if_pos h5, show 1 + sSize (arg 0 m) + fSize (arg 2 m) + tSize (arg 3 m)
                        + dSize (tail 4 m)
                      = (sSize (arg 0 m) + fSize (arg 2 m) + tSize (arg 3 m)
                        + dSize (tail 4 m)) + 1 by omega]
                  refine node_bound (j := 4) (by omega) ?_ ?_
                  · intro i hi
                    interval_cases i
                    · exact seq_le_Bd (by omega)
                    · exact tag_le_Bd (by omega)
                    · exact sub_le_Bd (le_G_fSize (arg 2 m)) (by omega)
                    · exact sub_le_Bd (le_G_tSize (arg 3 m)) (by omega)
                  · exact sub_le_Bd (ih _ (tail_lt_succ 4 m)) (by omega)
                · rw [if_neg h5]
                  by_cases h67 : arg 1 m = 6 ∨ arg 1 m = 7
                  · rw [if_pos h67, show 1 + sSize (arg 0 m) + dSize (tail 2 m)
                          = (sSize (arg 0 m) + dSize (tail 2 m)) + 1 by omega]
                    refine node_bound (j := 2) (by omega) ?_ ?_
                    · intro i hi
                      interval_cases i
                      · exact seq_le_Bd (by omega)
                      · exact tag_le_Bd (by rcases h67 with h | h <;> omega)
                    · exact sub_le_Bd (ih _ (tail_lt_succ 2 m)) (by omega)
                  · rw [if_neg h67]
                    by_cases h8 : arg 1 m = 8
                    · rw [if_pos h8, show 1 + sSize (arg 0 m) + fSize (arg 2 m)
                            + dSize (arg 3 m) + dSize (tail 4 m)
                          = (sSize (arg 0 m) + fSize (arg 2 m) + dSize (arg 3 m)
                            + dSize (tail 4 m)) + 1 by omega]
                      refine node_bound (j := 4) (by omega) ?_ ?_
                      · intro i hi
                        interval_cases i
                        · exact seq_le_Bd (by omega)
                        · exact tag_le_Bd (by omega)
                        · exact sub_le_Bd (le_G_fSize (arg 2 m)) (by omega)
                        · exact sub_le_Bd (ih _ (arg_lt_succ 3 m)) (by omega)
                      · exact sub_le_Bd (ih _ (tail_lt_succ 4 m)) (by omega)
                    · rw [if_neg h8]
                      by_cases h9 : arg 1 m = 9
                      · rw [if_pos h9, show 1 + sSize (arg 0 m) + fSize (tail 2 m)
                              = (sSize (arg 0 m) + fSize (tail 2 m)) + 1 by omega]
                        refine node_bound (j := 2) (by omega) ?_ ?_
                        · intro i hi
                          interval_cases i
                          · exact seq_le_Bd (by omega)
                          · exact tag_le_Bd (by omega)
                        · exact sub_le_Bd (le_G_fSize (tail 2 m)) (by omega)
                      · rw [if_neg h9]
                        exact self_le_G (m + 1)

/-! ## What the measure counts

Everything above is arithmetic on numbers.  This section is the faithfulness statement: at
`V := ℕ` the recursion really does decompose Foundation's own derivation codes, so `dSize`
really is the symbol count of the derivation `d` denotes, node by node.  These equations are
the thing to read against the paper. -/

/-- Stated **before** Foundation's scoped `Div` instance is in scope, so every `/` here is
unambiguously `Nat`'s: if `q` is the quotient of `s` by `2 ^ i`, then `q` is odd exactly when
the `i`-th bit of `s` is set. -/
private lemma not_two_dvd_iff_testBit {s i q : ℕ}
    (h1 : q * 2 ^ i ≤ s) (h2 : s < (q + 1) * 2 ^ i) : ¬ 2 ∣ q ↔ s.testBit i = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt_le h1 h2, decide_eq_true_eq]
  exact Nat.two_dvd_ne_zero

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping

/-- Foundation's `Exp.exp` is `2 ^ ·` at the standard model. -/
lemma exp_nat_eq : ∀ n : ℕ, Exp.exp n = 2 ^ n
  | 0 => by simp
  | (n + 1) => by
      have h : Exp.exp ((n : ℕ) + 1) = 2 * Exp.exp (n : ℕ) := exp_succ (V := ℕ) n
      rw [h, exp_nat_eq n, pow_succ]
      exact Nat.mul_comm 2 (2 ^ n)

/-- **Sequent membership is bit membership.**  Foundation's `p ∈ s` on a sequent bitset is
exactly `s.testBit p` at `V := ℕ`, which is what `sSize` sums over. -/
lemma mem_iff_testBit (i s : ℕ) : i ∈ s ↔ s.testBit i = true := by
  -- Foundation's `/` on a model is its own scoped instance, distinct from `Nat`'s even at
  -- `V := ℕ`.  Unfolding first puts Foundation's quotient in the goal, which is what fixes
  -- `q` in `not_two_dvd_iff_testBit`.
  simp only [mem_iff_bit, Bit, exp_nat_eq, LenBit]
  -- Foundation's `≤` on a model is `x = y ∨ x < y`, a scoped instance distinct from `Nat`'s
  -- even at `V := ℕ`; `<`, `+`, `*` are shared, `≤` and `/` are not.
  refine not_two_dvd_iff_testBit ?_ ?_
  · rcases le_def.mp (div_mul_le s (2 ^ i)) with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  · rw [Nat.mul_comm]
    exact lt_mul_div_succ s (Nat.two_pow_pos i)

/-- Every member of a sequent contributes its own symbols, stated at Foundation's
membership. -/
lemma fSize_le_sSize_of_mem {s i : ℕ} (h : i ∈ s) : fSize i ≤ sSize s :=
  fSize_le_sSize ((mem_iff_testBit i s).mp h)

/-! ### The derivation equations

One symbol for the rule name, then the node's sequent, its principal formulas and terms, and
its sub-derivations. -/

private lemma pair_nat (a b : ℕ) : (⟪a, b⟫ : ℕ) = Nat.pair a b := nat_pair_eq b a

@[simp] lemma dSize_axL (s p : ℕ) : dSize (axL s p) = 1 + sSize s + fSize p := by
  rw [show axL (V := ℕ) s p = Nat.pair s (Nat.pair 0 p) + 1 by simp [axL, pair_nat], dSize]
  simp [arg, tail, pl, pr]

@[simp] lemma dSize_verumIntro (s : ℕ) : dSize (verumIntro s) = 1 + sSize s := by
  rw [show verumIntro (V := ℕ) s = Nat.pair s (Nat.pair 1 0) + 1 by simp [verumIntro, pair_nat],
    dSize]
  simp [arg, tail, pl, pr]

@[simp] lemma dSize_andIntro (s p q dp dq : ℕ) :
    dSize (andIntro s p q dp dq)
      = 1 + sSize s + fSize p + fSize q + dSize dp + dSize dq := by
  rw [show andIntro (V := ℕ) s p q dp dq
        = Nat.pair s (Nat.pair 2 (Nat.pair p (Nat.pair q (Nat.pair dp dq)))) + 1 by
      simp [andIntro, pair_nat], dSize]
  simp [arg, tail, pl, pr]

@[simp] lemma dSize_orIntro (s p q d : ℕ) :
    dSize (orIntro s p q d) = 1 + sSize s + fSize p + fSize q + dSize d := by
  rw [show orIntro (V := ℕ) s p q d
        = Nat.pair s (Nat.pair 3 (Nat.pair p (Nat.pair q d))) + 1 by simp [orIntro, pair_nat],
    dSize]
  simp [arg, tail, pl, pr]

@[simp] lemma dSize_allIntro (s p d : ℕ) :
    dSize (allIntro s p d) = 1 + sSize s + fSize p + dSize d := by
  rw [show allIntro (V := ℕ) s p d = Nat.pair s (Nat.pair 4 (Nat.pair p d)) + 1 by
      simp [allIntro, pair_nat], dSize]
  simp [arg, tail, pl, pr]

@[simp] lemma dSize_exsIntro (s p t d : ℕ) :
    dSize (exsIntro s p t d) = 1 + sSize s + fSize p + tSize t + dSize d := by
  rw [show exsIntro (V := ℕ) s p t d
        = Nat.pair s (Nat.pair 5 (Nat.pair p (Nat.pair t d))) + 1 by simp [exsIntro, pair_nat],
    dSize]
  simp [arg, tail, pl, pr]

@[simp] lemma dSize_wkRule (s d : ℕ) : dSize (wkRule s d) = 1 + sSize s + dSize d := by
  rw [show wkRule (V := ℕ) s d = Nat.pair s (Nat.pair 6 d) + 1 by simp [wkRule, pair_nat], dSize]
  simp [arg, tail, pl, pr]

@[simp] lemma dSize_shiftRule (s d : ℕ) : dSize (shiftRule s d) = 1 + sSize s + dSize d := by
  rw [show shiftRule (V := ℕ) s d = Nat.pair s (Nat.pair 7 d) + 1 by simp [shiftRule, pair_nat],
    dSize]
  simp [arg, tail, pl, pr]

@[simp] lemma dSize_cutRule (s p d₁ d₂ : ℕ) :
    dSize (cutRule s p d₁ d₂) = 1 + sSize s + fSize p + dSize d₁ + dSize d₂ := by
  rw [show cutRule (V := ℕ) s p d₁ d₂
        = Nat.pair s (Nat.pair 8 (Nat.pair p (Nat.pair d₁ d₂))) + 1 by simp [cutRule, pair_nat],
    dSize]
  simp [arg, tail, pl, pr]

@[simp] lemma dSize_axm (s p : ℕ) : dSize (axm s p) = 1 + sSize s + fSize p := by
  rw [show axm (V := ℕ) s p = Nat.pair s (Nat.pair 9 p) + 1 by simp [axm, pair_nat], dSize]
  simp [arg, tail, pl, pr]

/-! ### The formula and term equations -/

@[simp] lemma fSize_qqRel (k r v : ℕ) :
    fSize (qqRel k r v) = 1 + idxLen k + idxLen r + tvSize v := by
  rw [show qqRel (V := ℕ) k r v = Nat.pair 0 (Nat.pair k (Nat.pair r v)) + 1 by
      simp [qqRel, pair_nat], fSize]
  simp [arg, tail, pl, pr]

@[simp] lemma fSize_qqNRel (k r v : ℕ) :
    fSize (qqNRel k r v) = 1 + idxLen k + idxLen r + tvSize v := by
  rw [show qqNRel (V := ℕ) k r v = Nat.pair 1 (Nat.pair k (Nat.pair r v)) + 1 by
      simp [qqNRel, pair_nat], fSize]
  simp [arg, tail, pl, pr]

@[simp] lemma fSize_qqVerum : fSize (qqVerum : ℕ) = 1 := by
  rw [show (qqVerum : ℕ) = Nat.pair 2 0 + 1 by simp [qqVerum, pair_nat], fSize]
  simp [arg, tail, pl, pr]

@[simp] lemma fSize_qqFalsum : fSize (qqFalsum : ℕ) = 1 := by
  rw [show (qqFalsum : ℕ) = Nat.pair 3 0 + 1 by simp [qqFalsum, pair_nat], fSize]
  simp [arg, tail, pl, pr]

@[simp] lemma fSize_qqAnd (p q : ℕ) : fSize (qqAnd p q) = 1 + fSize p + fSize q := by
  rw [show qqAnd (V := ℕ) p q = Nat.pair 4 (Nat.pair p q) + 1 by simp [qqAnd, pair_nat], fSize]
  simp [arg, tail, pl, pr]

@[simp] lemma fSize_qqOr (p q : ℕ) : fSize (qqOr p q) = 1 + fSize p + fSize q := by
  rw [show qqOr (V := ℕ) p q = Nat.pair 5 (Nat.pair p q) + 1 by simp [qqOr, pair_nat], fSize]
  simp [arg, tail, pl, pr]

@[simp] lemma fSize_qqAll (p : ℕ) : fSize (qqAll p) = 1 + fSize p := by
  rw [show qqAll (V := ℕ) p = Nat.pair 6 p + 1 by simp [qqAll, pair_nat], fSize]
  simp [arg, tail, pl, pr]

@[simp] lemma fSize_qqExs (p : ℕ) : fSize (qqExs p) = 1 + fSize p := by
  rw [show qqExs (V := ℕ) p = Nat.pair 7 p + 1 by simp [qqExs, pair_nat], fSize]
  simp [arg, tail, pl, pr]

@[simp] lemma tSize_qqBvar (z : ℕ) : tSize (qqBvar z) = 1 + idxLen z := by
  rw [show qqBvar (V := ℕ) z = Nat.pair 0 z + 1 by simp [qqBvar, pair_nat], tSize_succ]
  simp [arg, tail, pl, pr]

@[simp] lemma tSize_qqFvar (x : ℕ) : tSize (qqFvar x) = 1 + idxLen x := by
  rw [show qqFvar (V := ℕ) x = Nat.pair 1 x + 1 by simp [qqFvar, pair_nat], tSize_succ]
  simp [arg, tail, pl, pr]

@[simp] lemma tSize_qqFunc (k f v : ℕ) :
    tSize (qqFunc k f v) = 1 + idxLen k + idxLen f + tvSize v := by
  rw [show qqFunc (V := ℕ) k f v = Nat.pair 2 (Nat.pair k (Nat.pair f v)) + 1 by
      simp [qqFunc, pair_nat], tSize_succ]
  simp [arg, tail, pl, pr]

/-- A term vector is written out with one separator per entry. -/
@[simp] lemma tvSize_adjoin (x v : ℕ) : tvSize (x ∷ v) = 1 + tSize x + tvSize v := by
  rw [show (x ∷ v : ℕ) = Nat.pair x v + 1 by simp [adjoin_def, pair_nat], tvSize_succ]
  simp [arg, tail, pl, pr]

/-- **Every nonzero code has positive size.**  Each rule branch costs at least its own rule
name (`1 + …`), and the ill-formed catch-all returns the code itself (`m + 1`), so `dSize`
vanishes only at `0` — which is not a derivation code, every Foundation constructor being a
successor. -/
lemma dSize_pos {d : ℕ} (h : 0 < d) : 0 < dSize d := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  rw [dSize]
  split_ifs <;> omega

/-! ## Axiom accounting

The whole public surface of this module, printed for the audit log.  The symbol measure is
the `dd:symbolcount` counting convention supporting `thm:pac` / `thm:pazfc`, not a paper
node of its own, so no declaration here carries the annotation
`scripts/check-paper-nodes.sh` demands of names in an `#assert_axioms_clean` block, and the
accounting is done here instead.  This is **logging only**: nothing fails on a dirty print, and the control is the
human read of the build log, per the audit doctrine.  See `AxiomAudit.lean`'s
`Framework/DerivationSize.lean` block. -/

#print axioms pl
#print axioms pr
#print axioms pl_le
#print axioms pr_le
#print axioms arg
#print axioms tail
#print axioms tail_le
#print axioms arg_le
#print axioms arg_lt_succ
#print axioms tail_lt_succ
#print axioms idxLen
#print axioms one_le_idxLen
#print axioms lt_two_pow_idxLen
#print axioms tvAux
#print axioms tSize
#print axioms tvSize
#print axioms tSize_zero
#print axioms tvSize_zero
#print axioms tSize_succ
#print axioms tvSize_succ
#print axioms tvAux_zero_eq
#print axioms tvAux_one_eq
#print axioms tvAux_succ_of_ne
#print axioms fSize
#print axioms sSize
#print axioms dSize
#print axioms dSize_pos
#print axioms G
#print axioms G_mono
#print axioms self_le_G
#print axioms le_G_tSize
#print axioms le_G_tvSize
#print axioms le_G_fSize
#print axioms fSize_le_sSize
#print axioms fSize_le_sSize_of_mem
#print axioms lt_two_pow_G_sSize
#print axioms le_G_dSize
#print axioms exp_nat_eq
#print axioms mem_iff_testBit
#print axioms dSize_axL
#print axioms dSize_verumIntro
#print axioms dSize_andIntro
#print axioms dSize_orIntro
#print axioms dSize_allIntro
#print axioms dSize_exsIntro
#print axioms dSize_wkRule
#print axioms dSize_shiftRule
#print axioms dSize_cutRule
#print axioms dSize_axm
#print axioms fSize_qqRel
#print axioms fSize_qqNRel
#print axioms fSize_qqVerum
#print axioms fSize_qqFalsum
#print axioms fSize_qqAnd
#print axioms fSize_qqOr
#print axioms fSize_qqAll
#print axioms fSize_qqExs
#print axioms tSize_qqBvar
#print axioms tSize_qqFvar
#print axioms tSize_qqFunc
#print axioms tvSize_adjoin

end LogicalInduction
