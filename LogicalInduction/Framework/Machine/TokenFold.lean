/-
# Tokenizing transductions in `Complexity.FP`

`MachineEfficientTrader` (`Framework/Criterion.lean`) reads a machine's output word as a
*token* stream: three bits per digit (`Machine/DigitBits.lean`), digits below four
accumulating little-endian into a token and any digit from four up closing the block
(`undigitize`).  Transporting a trader across a rewrite of that stream — splicing a
conditioning block, freezing a price leaf — therefore means running a token-level
transducer on a *bit* word, in polynomial time.

`Machine/FPFold.lean` supplies the engine (`foldlBits_mem_FP`: a left fold whose step is
`FP` and whose state stays polynomially bounded).  This file supplies the two pieces a
client of that engine still has to build, and neither is a new combinator:

* **`LEUnary`** — the endianness residual.  `FPFold.unaryOfBits_le_mem_FP` reads its value
  big-endian through `Nat.fromBits`, while the stream carries token values as
  `undigitize`'s little-endian base-four digit runs.  `unaryOfDigitsLE_le_mem_FP` is the
  matching primitive: a three-phase shift register (`leStep`) that folds a token's own
  digit-bit block into `min value cap` marks, with `cap` a length already in hand.  The
  guard is not optional — a `k`-bit value denotes up to `4 ^ k` marks — and it is exactly
  what the clients have: a day read out of a day-`n` stream is `≤ n`, and every token test
  the conditioning automaton makes factors through a small clamp.

* **`TokenFold`** — the tokenizer itself.  `tkStep` is one bit of the digit/token parser:
  a two-slot phase fills, a complete digit either extends the current token block or (its
  leading bit set) closes it, and closing calls the client's `STEP`/`EMIT` on the token's
  digit-bit block.  `tkFold` is the digit-level model it realizes, `tkFold_out` proves the
  realization on *every* bit word — malformed ones included, where a trailing partial
  digit is discarded exactly as `bitsToDigits` discards it — and `tkFold_mem_FP` places the
  composite in `FP` from two per-step length hypotheses on the client.

The client receives each token as its raw digit-bit block rather than as a number, which is
deliberate: an arbitrary machine word may carry a *non-canonical* run (`[1, 0]` and `[1]`
are both the token `1`), so a client that compared blocks against constant words would be
wrong on inputs `undigitize` reads identically.  The supported interface is to read the
value through `LEUnary`, whose clamp makes it a length; every test the conditioning and
freeze automata make is a comparison against a small constant or against the day, and both
have a cap available.

Everything here is supporting infrastructure rather than a paper claim, so the declarations
are `lemma`s and carry no `Paper node:` line.  It sits beside `FPFold.lean` and could be
merged into it; it is a separate module only because the two were written on different
tracks.
-/
import LogicalInduction.Framework.Machine.FPFold
import LogicalInduction.Framework.DigitArith

namespace LogicalInduction.TokenFold

open Complexity Complexity.Cobham LogicalInduction.FPFold

/-! ## Folding a bit word in blocks

`FPFold.foldlBits_append_singleton` peels the last bit; block reasoning needs the general
append.

Proof kind: `P`.  Provenance: (a) `FPFold.foldlBits`. -/
lemma foldlBits_append (A B : List Bool → List Bool) (W : List Bool) :
    ∀ (st xs ys : List Bool),
      foldlBits A B W st (xs ++ ys) = foldlBits A B W (foldlBits A B W st xs) ys
  | _, [], _ => rfl
  | st, x :: xs, ys => by
      rw [List.cons_append, foldlBits_cons, foldlBits_cons,
        foldlBits_append A B W _ xs ys]

namespace LEUnary

/-! ## Little-endian base-four values

The value a digit run denotes is `Framework/DigitArith.lean`'s `digitVal`, the same
little-endian base-four reading `undigitize` performs; nothing new is defined here. -/

@[simp] private lemma digitVal_cons (d : ℕ) (ds : List ℕ) :
    digitVal (d :: ds) = d + 4 * digitVal ds := rfl

lemma digitBits_of_bits (b0 b1 b2 : Bool) :
    digitBits (4 * b2n b0 + 2 * b2n b1 + b2n b2) = [b0, b1, b2] := by
  cases b0 <;> cases b1 <;> cases b2 <;> rfl

lemma bitsToDigits_cons3 (b0 b1 b2 : Bool) (rest : List Bool) :
    bitsToDigits (b0 :: b1 :: b2 :: rest)
      = (4 * b2n b0 + 2 * b2n b1 + b2n b2) :: bitsToDigits rest := by
  have hd : 4 * b2n b0 + 2 * b2n b1 + b2n b2 < 8 := by
    cases b0 <;> cases b1 <;> cases b2 <;> simp [b2n]
  have := bitsToDigits_digitBits (4 * b2n b0 + 2 * b2n b1 + b2n b2) hd rest
  rwa [digitBits_of_bits] at this

lemma bitsToDigits_of_length_lt_three (w : List Bool) (h : w.length < 3) :
    bitsToDigits w = [] := by
  rw [bitsToDigits, Nat.div_eq_of_lt h]
  simp

/-! ## The step function -/

private def capw (v : List Bool) : List Bool := fstBlock v
private def stw (v : List Bool) : List Bool := sndBlock v
private def phw (v : List Bool) : List Bool := fstBlock (stw v)
private def accw (v : List Bool) : List Bool := fstBlock (sndBlock (stw v))
private def poww (v : List Bool) : List Bool := sndBlock (sndBlock (stw v))
private def ph0 (v : List Bool) : List Bool := fstBlock (phw v)
private def ph1 (v : List Bool) : List Bool := sndBlock (phw v)

/-- The packed fold state: phase pair, accumulator, place value. -/
def mkSt (p0 p1 acc pow : List Bool) : List Bool :=
  pair (pair p0 p1) (pair acc pow)

private def repPow : ℕ → List Bool → List Bool
  | 0, _ => []
  | k + 1, v => poww v ++ repPow k v

private def mulSel (b : Bool) (v : List Bool) : List Bool :=
  selectHead (ph0 v)
    (selectHead (ph1 v) (repPow (if b then 7 else 6) v) (repPow (if b then 5 else 4) v))
    (selectHead (ph1 v) (repPow (if b then 3 else 2) v) (repPow (if b then 1 else 0) v))

private def flush (b : Bool) (v : List Bool) : List Bool :=
  mkSt [] []
    (List.take (capw v).length (accw v ++ mulSel b v))
    (List.take (capw v ++ [true]).length (repPow 4 v))

/-- One bit of the guarded little-endian expansion. -/
def leStep (b : Bool) (v : List Bool) : List Bool :=
  selectHead (emptyFlag (ph0 v))
    (mkSt [b] [] (accw v) (poww v))
    (selectHead (emptyFlag (ph1 v))
      (mkSt (ph0 v) [b] (accw v) (poww v))
      (flush b v))

/-! ### Selection helpers -/

lemma selectHead_true (x y : List Bool) : selectHead [true] x y = x := by
  rw [selectHead_eq]
  simp [headFlag]

lemma selectHead_false (x y : List Bool) : selectHead [false] x y = y := by
  rw [selectHead_eq]
  simp [headFlag]

lemma selectHead_singleton (b : Bool) (x y : List Bool) :
    selectHead [b] x y = if b then x else y := by
  cases b
  · simpa using selectHead_false x y
  · simpa using selectHead_true x y



private def rep : ℕ → List Bool → List Bool
  | 0, _ => []
  | k + 1, p => p ++ rep k p

private lemma repPow_eq : ∀ (k : ℕ) (v : List Bool), repPow k v = rep k (poww v)
  | 0, _ => rfl
  | k + 1, v => by rw [repPow, rep, repPow_eq k v]

lemma foldl_three (W acc pow : List Bool) (b0 b1 b2 : Bool) :
    foldlBits (leStep false) (leStep true) W (mkSt [] [] acc pow) [b0, b1, b2]
      = mkSt [] []
          (List.take W.length (acc ++ rep (4 * b2n b0 + 2 * b2n b1 + b2n b2) pow))
          (List.take (W.length + 1) (rep 4 pow)) := by
  cases b0 <;> cases b1 <;> cases b2 <;>
    simp [foldlBits, leStep, flush, mulSel, mkSt, capw, stw, phw, accw, poww, ph0, ph1,
      repPow_eq, selectHead_singleton, selectHead_emptyFlag_cons,
      b2n, rep]



private lemma rep_replicate (k p : ℕ) :
    rep k (List.replicate p true) = List.replicate (k * p) true := by
  induction k with
  | zero => simp [rep]
  | succ k ih => rw [rep, ih, ← List.replicate_add]; ring_nf

private lemma step_spec (W : List Bool) (m p : ℕ) (b0 b1 b2 : Bool) :
    foldlBits (leStep false) (leStep true) W
        (mkSt [] [] (List.replicate m true) (List.replicate p true)) [b0, b1, b2]
      = mkSt [] []
          (List.replicate (min (m + (4 * b2n b0 + 2 * b2n b1 + b2n b2) * p) W.length) true)
          (List.replicate (min (4 * p) (W.length + 1)) true) := by
  rw [foldl_three, rep_replicate, rep_replicate, ← List.replicate_add,
    List.take_replicate, List.take_replicate]
  rw [Nat.min_comm W.length, Nat.min_comm (W.length + 1)]

/-- The value the clamped accumulator holds after a digit list. -/
def leAccVal (cap : ℕ) : ℕ → ℕ → List ℕ → ℕ
  | m, _, [] => m
  | m, p, d :: ds => leAccVal cap (min (m + d * p) cap) (min (4 * p) (cap + 1)) ds

lemma leAccVal_spec (cap : ℕ) : ∀ (ds : List ℕ) (m p : ℕ), m ≤ cap →
    leAccVal cap m p ds = min (m + p * digitVal ds) cap
  | [], m, p, hm => by simp [leAccVal, hm]
  | d :: ds, m, p, hm => by
      rw [leAccVal, leAccVal_spec cap ds _ _ (min_le_right _ _)]
      set V := digitVal ds with hV
      by_cases hsat : cap ≤ m + d * p
      · rw [min_eq_right hsat]
        have h1 : cap ≤ cap + min (4 * p) (cap + 1) * V := Nat.le_add_right _ _
        have h2 : cap ≤ m + p * (d + 4 * V) := by
          calc cap ≤ m + d * p := hsat
            _ ≤ m + p * (d + 4 * V) := by
                have : d * p ≤ p * (d + 4 * V) := by
                  rw [Nat.mul_comm d p]
                  exact Nat.mul_le_mul_left p (Nat.le_add_right _ _)
                omega
        rw [min_eq_right h1, digitVal_cons, ← hV, min_eq_right h2]
      · rw [min_eq_left (by omega : m + d * p ≤ cap)]
        by_cases hp : 4 * p ≤ cap + 1
        · rw [min_eq_left hp, digitVal_cons, ← hV]
          congr 1
          ring
        · rw [min_eq_right (by omega : cap + 1 ≤ 4 * p), digitVal_cons, ← hV]
          rcases Nat.eq_zero_or_pos V with hz | hz
          · rw [hz]
            simp [Nat.mul_comm]
          · have hL : cap ≤ m + d * p + (cap + 1) * V := by
              have : cap + 1 ≤ (cap + 1) * V := Nat.le_mul_of_pos_right _ hz
              omega
            have hR : cap ≤ m + p * (d + 4 * V) := by
              have h4 : cap + 1 ≤ 4 * p := by omega
              have : 4 * p ≤ p * (d + 4 * V) := by
                calc 4 * p = p * 4 := by ring
                  _ ≤ p * (4 * V) := Nat.mul_le_mul_left p (by omega)
                  _ ≤ p * (d + 4 * V) := Nat.mul_le_mul_left p (Nat.le_add_left _ _)
              omega
            rw [min_eq_right hL, min_eq_right hR]



lemma foldl_acc (W : List Bool) : ∀ (w : List Bool) (m p : ℕ),
    fstBlock (sndBlock (foldlBits (leStep false) (leStep true) W
        (mkSt [] [] (List.replicate m true) (List.replicate p true)) w))
      = List.replicate (leAccVal W.length m p (bitsToDigits w)) true
  | [], m, p => by
      rw [foldlBits_nil, mkSt, sndBlock_pair, fstBlock_pair,
        bitsToDigits_of_length_lt_three [] (by simp), leAccVal]
  | [b0], m, p => by
      rw [bitsToDigits_of_length_lt_three [b0] (by simp), leAccVal,
        show ([b0] : List Bool) = [] ++ [b0] from rfl,
        foldlBits_append_singleton, foldlBits_nil]
      cases b0 <;>
        simp [leStep, mkSt, stw, phw, accw, poww, ph0, ph1,
          selectHead_true]
  | [b0, b1], m, p => by
      rw [bitsToDigits_of_length_lt_three [b0, b1] (by simp), leAccVal,
        show ([b0, b1] : List Bool) = [b0] ++ [b1] from rfl,
        foldlBits_append_singleton]
      cases b0 <;> cases b1 <;>
        simp [foldlBits, leStep, mkSt, stw, phw, accw, poww, ph0, ph1,
          selectHead_true, selectHead_emptyFlag_cons]
  | b0 :: b1 :: b2 :: rest, m, p => by
      rw [bitsToDigits_cons3, leAccVal,
        show (b0 :: b1 :: b2 :: rest) = [b0, b1, b2] ++ rest from rfl,
        foldlBits_append, step_spec, foldl_acc W rest _ _]

/-- **The guarded little-endian expansion computes the clamped value.**  Starting empty,
with place value one, the register holds `min value cap` after the whole word — on every
word, a trailing partial digit contributing nothing, exactly as `bitsToDigits` drops it.

Proof kind: `C` composition.  Provenance: (a) `foldl_acc`, `leAccVal_spec`. -/
lemma foldl_acc_init (W w : List Bool) :
    fstBlock (sndBlock (foldlBits (leStep false) (leStep true) W
        (mkSt [] [] [] [true]) w))
      = List.replicate (min (digitVal (bitsToDigits w)) W.length) true := by
  have h := foldl_acc W w 0 1
  rw [show (List.replicate 0 true : List Bool) = [] from rfl,
    show (List.replicate 1 true : List Bool) = [true] from rfl] at h
  rw [h, leAccVal_spec W.length (bitsToDigits w) 0 1 (Nat.zero_le _)]
  simp



/-- The reachable-state invariant: a two-slot phase, an all-`true` accumulator clamped at
the guard, and an all-`true` place value clamped one past it. -/
private def StBnd (W st : List Bool) : Prop :=
  ∃ (p0 p1 : List Bool) (m p : ℕ),
    st = mkSt p0 p1 (List.replicate m true) (List.replicate p true) ∧
      p0.length ≤ 1 ∧ p1.length ≤ 1 ∧ m ≤ W.length ∧ p ≤ W.length + 1

private lemma StBnd.step {W st : List Bool} (h : StBnd W st) (b : Bool) :
    StBnd W (leStep b (pair W st)) := by
  obtain ⟨p0, p1, m, p, rfl, h0, h1, hm, hp⟩ := h
  match p0, h0 with
  | [], _ =>
      refine ⟨[b], [], m, p, ?_, by simp, by simp, hm, hp⟩
      simp [leStep, mkSt, stw, phw, accw, poww, ph0, ph1,
        selectHead_true]
  | [x], _ =>
      match p1, h1 with
      | [], _ =>
          refine ⟨[x], [b], m, p, ?_, by simp, by simp, hm, hp⟩
          cases x <;>
            simp [leStep, mkSt, stw, phw, accw, poww, ph0, ph1,
              selectHead_true, selectHead_emptyFlag_cons]
      | [y], _ =>
          refine ⟨[], [], min (m + (4 * b2n x + 2 * b2n y + b2n b) * p) W.length,
            min (4 * p) (W.length + 1), ?_, by simp, by simp,
            min_le_right _ _, min_le_right _ _⟩
          have hflush : leStep b (pair W (mkSt [x] [y] (List.replicate m true)
              (List.replicate p true)))
              = flush b (pair W (mkSt [x] [y] (List.replicate m true)
                  (List.replicate p true))) := by
            cases x <;> cases y <;>
              simp [leStep, mkSt, stw, phw, accw, poww, ph0, ph1,
                selectHead_emptyFlag_cons]
          rw [hflush]
          cases x <;> cases y <;> cases b <;>
            simp [flush, mkSt, capw, stw, phw, accw, poww, ph0, ph1, mulSel,
              repPow_eq, selectHead_true, selectHead_false, rep, b2n,
              List.take_replicate] <;>
            (congr 3 <;> omega)

private lemma StBnd.fold (W : List Bool) : ∀ (w st : List Bool), StBnd W st →
    StBnd W (foldlBits (leStep false) (leStep true) W st w)
  | [], st, h => h
  | b :: bs, st, h => by
      rw [foldlBits_cons]
      refine StBnd.fold W bs _ ?_
      cases b
      · exact h.step false
      · exact h.step true

private lemma StBnd.length_le {W st : List Bool} (h : StBnd W st) :
    st.length ≤ 3 * W.length + 15 := by
  obtain ⟨p0, p1, m, p, rfl, h0, h1, hm, hp⟩ := h
  simp only [mkSt, pair_length, List.length_replicate]
  omega



private lemma capw_mem_FP : capw ∈ FP := fstBlock_mem_FP
private lemma stw_mem_FP : stw ∈ FP := sndBlock_mem_FP
private lemma phw_mem_FP : phw ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
private lemma accw_mem_FP : accw ∈ FP :=
  mem_FP_comp (mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP) fstBlock_mem_FP
private lemma poww_mem_FP : poww ∈ FP :=
  mem_FP_comp (mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP) sndBlock_mem_FP
private lemma ph0_mem_FP : ph0 ∈ FP := mem_FP_comp phw_mem_FP fstBlock_mem_FP
private lemma ph1_mem_FP : ph1 ∈ FP := mem_FP_comp phw_mem_FP sndBlock_mem_FP

private lemma repPow_mem_FP : ∀ k : ℕ, repPow k ∈ FP
  | 0 => constFn_mem_FP []
  | k + 1 => appendFn_mem_FP poww_mem_FP (repPow_mem_FP k)

private lemma mulSel_mem_FP (b : Bool) : mulSel b ∈ FP :=
  selectHeadFn_mem_FP ph0_mem_FP
    (selectHeadFn_mem_FP ph1_mem_FP (repPow_mem_FP _) (repPow_mem_FP _))
    (selectHeadFn_mem_FP ph1_mem_FP (repPow_mem_FP _) (repPow_mem_FP _))

private lemma flush_mem_FP (b : Bool) : flush b ∈ FP :=
  pairFn_mem_FP (constFn_mem_FP (pair [] []))
    (pairFn_mem_FP
      (takeLenFn_mem_FP capw_mem_FP (appendFn_mem_FP accw_mem_FP (mulSel_mem_FP b)))
      (takeLenFn_mem_FP (appendFn_mem_FP capw_mem_FP (constFn_mem_FP [true]))
        (repPow_mem_FP 4)))

lemma leStep_mem_FP (b : Bool) : leStep b ∈ FP :=
  selectHeadFn_mem_FP (emptyFlag_mem_FP ph0_mem_FP)
    (pairFn_mem_FP (constFn_mem_FP (pair [b] []))
      (pairFn_mem_FP accw_mem_FP poww_mem_FP))
    (selectHeadFn_mem_FP (emptyFlag_mem_FP ph1_mem_FP)
      (pairFn_mem_FP (pairFn_mem_FP ph0_mem_FP (constFn_mem_FP [b]))
        (pairFn_mem_FP accw_mem_FP poww_mem_FP))
      (flush_mem_FP b))



/-- **The guarded little-endian expansion is polynomial time.**  `V z` is a token's own
digit-bit block, read little-endian base four the way `undigitize` reads it; `C z` is a word
whose *length* is the guard.  This is `FPFold.unaryOfBits_le_mem_FP` in the endianness the
token stream actually uses, and, like it, the clamp is what makes the claim true at all.

Proof kind: `C` composition.  Provenance: (b) `FPFold.foldlBits_mem_FP`; (a)
`leStep_mem_FP`, `foldl_acc_init`, `StBnd.fold`. -/
lemma unaryOfDigitsLE_le_mem_FP {V C : List Bool → List Bool} (hV : V ∈ FP) (hC : C ∈ FP) :
    (fun z => List.replicate (min (digitVal (bitsToDigits (V z))) (C z).length) true) ∈ FP := by
  have hinit : ∀ W : List Bool, StBnd W (mkSt [] [] [] [true]) := by
    intro W
    exact ⟨[], [], 0, 1, rfl, by simp, by simp, Nat.zero_le _, by omega⟩
  have hfold : (fun z => foldlBits (leStep false) (leStep true) (C z)
      (mkSt [] [] [] [true]) (V z)) ∈ FP := by
    refine foldlBits_mem_FP (leStep_mem_FP false) (leStep_mem_FP true) hC hV
      (mkSt [] [] [] [true]) (3 * Polynomial.X + 15) (fun z u _ => ?_)
    have hb := (StBnd.fold (C z) u _ (hinit (C z))).length_le
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega
  have hcomp := mem_FP_comp hfold (mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP)
  have heq : ((fstBlock ∘ sndBlock) ∘ fun z => foldlBits (leStep false) (leStep true) (C z)
        (mkSt [] [] [] [true]) (V z))
      = fun z => List.replicate (min (digitVal (bitsToDigits (V z))) (C z).length) true := by
    funext z
    exact foldl_acc_init (C z) (V z)
  rwa [heq] at hcomp



lemma digitVal_natDigits4 : ∀ n : ℕ, digitVal (natDigits4 n) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero => simp [natDigits4]
      | succ m =>
          rw [natDigits4, digitVal_cons, ih ((m + 1) / 4) (Nat.div_lt_self (Nat.succ_pos m) (by norm_num))]
          omega

/-- The value the guard reads back from a token's own digit block. -/
lemma digitVal_bitsToDigits_digitsToBits_natDigits4 (t : ℕ) :
    digitVal (bitsToDigits (digitsToBits (natDigits4 t))) = t := by
  rw [bitsToDigits_digitsToBits _ (fun d hd => lt_trans (natDigits4_lt t d hd) (by norm_num)),
    digitVal_natDigits4]



end LEUnary

open LEUnary

/-! ## The generic bit-level tokenizer -/



/-- The packed tokenizer state: two-slot phase, current token block, client state,
output so far. -/
def tkSt (ph tok cli out : List Bool) : List Bool := pair ph (pair tok (pair cli out))

/-- The output component of a tokenizer state. -/
def outOf (st : List Bool) : List Bool := sndBlock (sndBlock (sndBlock st))

private def wpar (v : List Bool) : List Bool := fstBlock v
private def sst (v : List Bool) : List Bool := sndBlock v
private def phv (v : List Bool) : List Bool := fstBlock (sst v)
private def p0v (v : List Bool) : List Bool := fstBlock (phv v)
private def p1v (v : List Bool) : List Bool := sndBlock (phv v)
private def tokv (v : List Bool) : List Bool := fstBlock (sndBlock (sst v))
private def cliv (v : List Bool) : List Bool := fstBlock (sndBlock (sndBlock (sst v)))
private def outv (v : List Bool) : List Bool := sndBlock (sndBlock (sndBlock (sst v)))
private def argv (v : List Bool) : List Bool := pair (wpar v) (pair (cliv v) (tokv v))

/-- One bit of the tokenizer: fill the phase, then on a complete digit either close the
token block (leading bit set: the digit is a block terminator) or append it. -/
def tkStep (STEP EMIT : List Bool → List Bool) (b : Bool) (v : List Bool) : List Bool :=
  selectHead (emptyFlag (p0v v))
    (tkSt (pair [b] []) (tokv v) (cliv v) (outv v))
    (selectHead (emptyFlag (p1v v))
      (tkSt (pair (p0v v) [b]) (tokv v) (cliv v) (outv v))
      (selectHead (p0v v)
        (tkSt (pair [] []) [] (STEP (argv v)) (outv v ++ EMIT (argv v)))
        (tkSt (pair [] []) (tokv v ++ p0v v ++ p1v v ++ [b]) (cliv v) (outv v))))

/-- The digit-level model the bit-level tokenizer realizes. -/
def tkFold (STEP EMIT : List Bool → List Bool) (W : List Bool) :
    List Bool → List Bool → List Bool → List ℕ → List Bool × List Bool × List Bool
  | tok, cli, out, [] => (tok, cli, out)
  | tok, cli, out, d :: ds =>
      if d < 4 then tkFold STEP EMIT W (tok ++ digitBits d) cli out ds
      else tkFold STEP EMIT W [] (STEP (pair W (pair cli tok)))
             (out ++ EMIT (pair W (pair cli tok))) ds

private lemma tkStep_three (STEP EMIT : List Bool → List Bool)
    (W tok cli out : List Bool) (b0 b1 b2 : Bool) :
    foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) W
        (tkSt (pair [] []) tok cli out) [b0, b1, b2]
      = (if 4 * b2n b0 + 2 * b2n b1 + b2n b2 < 4 then
            tkSt (pair [] []) (tok ++ digitBits (4 * b2n b0 + 2 * b2n b1 + b2n b2)) cli out
          else tkSt (pair [] []) [] (STEP (pair W (pair cli tok)))
                 (out ++ EMIT (pair W (pair cli tok)))) := by
  cases b0 <;> cases b1 <;> cases b2 <;>
    simp [foldlBits, tkStep, tkSt, wpar, sst, phv, p0v, p1v, tokv, cliv, outv, argv,
      selectHead_true, selectHead_false,
      selectHead_emptyFlag_cons, b2n, digitBits]

/-- **The bit-level tokenizer realizes the digit-level model**, on every bit word.  A
trailing partial digit is discarded exactly as `bitsToDigits` discards it, so no
well-formedness hypothesis appears; the client sees each token as its raw digit-bit block.

Proof kind: `P` proved.  Provenance: (a) `tkStep_three`, `foldlBits_append`,
`bitsToDigits_cons3`. -/
lemma tkFold_out (STEP EMIT : List Bool → List Bool) (W : List Bool) :
    ∀ (w tok cli out : List Bool),
    outOf (foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) W
        (tkSt (pair [] []) tok cli out) w)
      = (tkFold STEP EMIT W tok cli out (bitsToDigits w)).2.2
  | [], tok, cli, out => by
      rw [foldlBits_nil, bitsToDigits_of_length_lt_three [] (by simp),
        tkFold]
      simp [outOf, tkSt]
  | [b0], tok, cli, out => by
      rw [bitsToDigits_of_length_lt_three [b0] (by simp), tkFold,
        show ([b0] : List Bool) = [] ++ [b0] from rfl,
        foldlBits_append_singleton, foldlBits_nil]
      cases b0 <;>
        simp [tkStep, tkSt, outOf, sst, phv, p0v, p1v, tokv, cliv, outv,
          selectHead_true]
  | [b0, b1], tok, cli, out => by
      rw [bitsToDigits_of_length_lt_three [b0, b1] (by simp), tkFold,
        show ([b0, b1] : List Bool) = [b0] ++ [b1] from rfl,
        foldlBits_append_singleton]
      cases b0 <;> cases b1 <;>
        simp [foldlBits, tkStep, tkSt, outOf, sst, phv, p0v, p1v, tokv, cliv, outv,
          selectHead_true, selectHead_false, selectHead_emptyFlag_cons]
  | b0 :: b1 :: b2 :: rest, tok, cli, out => by
      rw [bitsToDigits_cons3, tkFold,
        show (b0 :: b1 :: b2 :: rest) = [b0, b1, b2] ++ rest from rfl,
        foldlBits_append, tkStep_three]
      by_cases hd : 4 * b2n b0 + 2 * b2n b1 + b2n b2 < 4
      · rw [if_pos hd, if_pos hd, tkFold_out STEP EMIT W rest _ _ _]
      · rw [if_neg hd, if_neg hd, tkFold_out STEP EMIT W rest _ _ _]



private lemma tkStep_bound {STEP EMIT : List Bool → List Bool} {c Q k : ℕ}
    {W : List Bool}
    (hS : ∀ cli tok : List Bool,
      (STEP (pair W (pair cli tok))).length ≤ cli.length + tok.length + c)
    (hE : ∀ cli tok : List Bool,
      (EMIT (pair W (pair cli tok))).length ≤ Q + k * (cli.length + tok.length))
    (p0 p1 tok cli out : List Bool) (h0 : p0.length ≤ 1) (h1 : p1.length ≤ 1)
    (b : Bool) :
    ∃ p0' p1' tok' cli' out',
      tkStep STEP EMIT b (pair W (tkSt (pair p0 p1) tok cli out))
          = tkSt (pair p0' p1') tok' cli' out' ∧
        p0'.length ≤ 1 ∧ p1'.length ≤ 1 ∧
        cli'.length + tok'.length ≤ cli.length + tok.length + (3 + c) ∧
        out'.length ≤ out.length + Q + k * (cli.length + tok.length) := by
  have harg : argv (pair W (tkSt (pair p0 p1) tok cli out)) = pair W (pair cli tok) := by
    simp [argv, wpar, sst, cliv, tokv, tkSt]
  have hSt : (STEP (pair W (pair cli tok))).length ≤ cli.length + tok.length + c :=
    hS cli tok
  have hEt : (EMIT (pair W (pair cli tok))).length ≤ Q + k * (cli.length + tok.length) :=
    hE cli tok
  match p0, h0 with
  | [], _ =>
      refine ⟨[b], [], tok, cli, out, ?_, by simp, by simp, by omega, by omega⟩
      simp [tkStep, tkSt, sst, phv, p0v, p1v, tokv, cliv, outv,
        selectHead_true]
  | [x], _ =>
      match p1, h1 with
      | [], _ =>
          refine ⟨[x], [b], tok, cli, out, ?_, by simp, by simp, by omega, by omega⟩
          cases x <;>
            simp [tkStep, tkSt, sst, phv, p0v, p1v, tokv, cliv, outv,
              selectHead_true, selectHead_false, selectHead_emptyFlag_cons]
      | [y], _ =>
          cases x
          · refine ⟨[], [], tok ++ [false] ++ [y] ++ [b], cli, out, ?_, by simp, by simp,
              by simp; omega, by omega⟩
            simp [tkStep, tkSt, sst, phv, p0v, p1v, tokv, cliv, outv,
              selectHead_false, selectHead_emptyFlag_cons]
          · refine ⟨[], [], [], STEP (pair W (pair cli tok)),
              out ++ EMIT (pair W (pair cli tok)), ?_, by simp, by simp, by simp; omega,
              by simp; omega⟩
            rw [show tkStep STEP EMIT b (pair W (tkSt (pair [true] [y]) tok cli out))
                = tkSt (pair [] []) [] (STEP (argv (pair W (tkSt (pair [true] [y]) tok cli out))))
                    (outv (pair W (tkSt (pair [true] [y]) tok cli out))
                      ++ EMIT (argv (pair W (tkSt (pair [true] [y]) tok cli out)))) from ?_]
            · rw [harg]
              simp [outv, sst, tkSt]
            · simp [tkStep, tkSt, sst, phv, p0v, p1v, tokv, cliv, outv,
                selectHead_true, selectHead_emptyFlag_cons]



private lemma tkRun_arith (o o1 O Q k K S0 S1 L : ℕ)
    (h1 : o1 ≤ O + Q + k * S0) (h2 : S1 ≤ S0 + K)
    (h3 : o ≤ o1 + L * (Q + k * S1 + k * (K * L))) :
    o ≤ O + (L + 1) * (Q + k * S0 + k * (K * (L + 1))) := by
  have hstep : L * (Q + k * S1 + k * (K * L))
      ≤ L * (Q + k * S0 + k * K + k * (K * L)) := by
    have : k * S1 ≤ k * S0 + k * K := by nlinarith [h2]
    exact Nat.mul_le_mul_left _ (by omega)
  have e1 : (L + 1) * (Q + k * S0 + k * (K * (L + 1)))
      = L * Q + Q + L * (k * S0) + k * S0 + k * K * (L * L) + 2 * (k * K * L) + k * K := by
    ring
  have e2 : L * (Q + k * S0 + k * K + k * (K * L))
      = L * Q + L * (k * S0) + k * K * L + k * K * (L * L) := by ring
  rw [e1]
  rw [e2] at hstep
  omega

private lemma tkRun_bound {STEP EMIT : List Bool → List Bool} {c Q k : ℕ}
    {W : List Bool}
    (hS : ∀ cli tok : List Bool,
      (STEP (pair W (pair cli tok))).length ≤ cli.length + tok.length + c)
    (hE : ∀ cli tok : List Bool,
      (EMIT (pair W (pair cli tok))).length ≤ Q + k * (cli.length + tok.length)) :
    ∀ (u p0 p1 tok cli out : List Bool),
    p0.length ≤ 1 → p1.length ≤ 1 →
    ∃ p0' p1' tok' cli' out',
      foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) W
          (tkSt (pair p0 p1) tok cli out) u = tkSt (pair p0' p1') tok' cli' out' ∧
        p0'.length ≤ 1 ∧ p1'.length ≤ 1 ∧
        cli'.length + tok'.length ≤ cli.length + tok.length + (3 + c) * u.length ∧
        out'.length ≤ out.length
          + u.length * (Q + k * (cli.length + tok.length) + k * ((3 + c) * u.length))
  | [], p0, p1, tok, cli, out, h0, h1 => ⟨p0, p1, tok, cli, out, rfl, h0, h1, by simp, by simp⟩
  | b :: bs, p0, p1, tok, cli, out, h0, h1 => by
      obtain ⟨q0, q1, tok₁, cli₁, out₁, hst, hq0, hq1, hsum, hout⟩ :=
        tkStep_bound hS hE p0 p1 tok cli out h0 h1 b
      have hfold : foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) W
          (tkSt (pair p0 p1) tok cli out) (b :: bs)
          = foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) W
              (tkSt (pair q0 q1) tok₁ cli₁ out₁) bs := by
        rw [foldlBits_cons, ← hst]
        cases b <;> rfl
      obtain ⟨p0', p1', tok', cli', out', hst', h0', h1', hsum', hout'⟩ :=
        tkRun_bound hS hE bs q0 q1 tok₁ cli₁ out₁ hq0 hq1
      refine ⟨p0', p1', tok', cli', out', by rw [hfold, hst'], h0', h1', ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith [hsum, hsum']
      · simp only [List.length_cons]
        exact tkRun_arith out'.length out₁.length out.length Q k (3 + c)
          (cli.length + tok.length) (cli₁.length + tok₁.length) bs.length
          (by omega) hsum (by
            have := hout'
            omega)



private lemma wpar_mem_FP : wpar ∈ FP := fstBlock_mem_FP
private lemma sst_mem_FP : sst ∈ FP := sndBlock_mem_FP
private lemma phv_mem_FP : phv ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
private lemma p0v_mem_FP : p0v ∈ FP := mem_FP_comp phv_mem_FP fstBlock_mem_FP
private lemma p1v_mem_FP : p1v ∈ FP := mem_FP_comp phv_mem_FP sndBlock_mem_FP
private lemma tokv_mem_FP : tokv ∈ FP :=
  mem_FP_comp (mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP) fstBlock_mem_FP
private lemma cliv_mem_FP : cliv ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP) sndBlock_mem_FP)
    fstBlock_mem_FP
private lemma outv_mem_FP : outv ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP) sndBlock_mem_FP)
    sndBlock_mem_FP
private lemma argv_mem_FP : argv ∈ FP :=
  pairFn_mem_FP wpar_mem_FP (pairFn_mem_FP cliv_mem_FP tokv_mem_FP)

lemma tkStep_mem_FP {STEP EMIT : List Bool → List Bool} (hSTEP : STEP ∈ FP)
    (hEMIT : EMIT ∈ FP) (b : Bool) : tkStep STEP EMIT b ∈ FP :=
  selectHeadFn_mem_FP (emptyFlag_mem_FP p0v_mem_FP)
    (pairFn_mem_FP (constFn_mem_FP (pair [b] []))
      (pairFn_mem_FP tokv_mem_FP (pairFn_mem_FP cliv_mem_FP outv_mem_FP)))
    (selectHeadFn_mem_FP (emptyFlag_mem_FP p1v_mem_FP)
      (pairFn_mem_FP (pairFn_mem_FP p0v_mem_FP (constFn_mem_FP [b]))
        (pairFn_mem_FP tokv_mem_FP (pairFn_mem_FP cliv_mem_FP outv_mem_FP)))
      (selectHeadFn_mem_FP p0v_mem_FP
        (pairFn_mem_FP (constFn_mem_FP (pair [] []))
          (pairFn_mem_FP (constFn_mem_FP [])
            (pairFn_mem_FP (mem_FP_comp argv_mem_FP hSTEP)
              (appendFn_mem_FP outv_mem_FP (mem_FP_comp argv_mem_FP hEMIT)))))
        (pairFn_mem_FP (constFn_mem_FP (pair [] []))
          (pairFn_mem_FP
            (appendFn_mem_FP
              (appendFn_mem_FP (appendFn_mem_FP tokv_mem_FP p0v_mem_FP) p1v_mem_FP)
              (constFn_mem_FP [b]))
            (pairFn_mem_FP cliv_mem_FP outv_mem_FP)))))



private lemma tkFold_arith (a b t cl o L n Q Qn C0 O0 K k : ℕ)
    (ha : a ≤ 1) (hb : b ≤ 1) (hsum : cl + t ≤ C0 + K * L)
    (ho : o ≤ O0 + L * (Q + k * (C0 + 0) + k * (K * L))) (hL : L ≤ n) (hQ : Q ≤ Qn) :
    2 * (2 * a + 2 + b) + 2 + (2 * t + 2 + (2 * cl + 2 + o))
      ≤ 16 + 2 * C0 + O0 + 2 * K * n + n * Qn + k * C0 * n + k * K * (n * n) := by
  have h1 : L * Q ≤ n * Qn := Nat.mul_le_mul hL hQ
  have h2 : L * (k * C0) ≤ n * (k * C0) := Nat.mul_le_mul_right _ hL
  have h3 : L * (k * (K * L)) ≤ n * (k * (K * n)) :=
    Nat.mul_le_mul hL (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL))
  have h4 : K * L ≤ K * n := Nat.mul_le_mul_left _ hL
  have hoexp : o ≤ O0 + (L * Q + L * (k * C0) + L * (k * (K * L))) := by
    calc o ≤ O0 + L * (Q + k * (C0 + 0) + k * (K * L)) := ho
      _ = O0 + (L * Q + L * (k * C0) + L * (k * (K * L))) := by ring
  nlinarith [h1, h2, h3, h4, hoexp, hsum, ha, hb]

/-- **The generic tokenizing transduction is polynomial time.**

The two hypotheses are the client's whole obligation, and both are per-step inequalities
over *arbitrary* words rather than statements about reachable states — which is what
`FPFold.foldlBits_mem_FP` needs, since its clamp must be discharged on the machine's
malformed inputs too.  `c` bounds the client state's growth per closed token, and `qQ` with `k`
bound what the emitter appends: a polynomial in the parameter block plus a constant
multiple of the state and token it is handed — `k` is not cosmetic, since a splicing
emitter copies its buffer more than once.  Together they make the packed state
`O(n²)`-bounded with no well-formedness hypothesis.

Proof kind: `C` composition.  Provenance: (b) `FPFold.foldlBits_mem_FP`,
`Cobham.sndBlock_mem_FP`, `Complexity.mem_FP_comp`; (a) `tkStep_mem_FP`, `tkFold_out`,
`tkRun_bound`. -/
lemma tkFold_mem_FP {STEP EMIT Wf Sf : List Bool → List Bool} {c k : ℕ}
    {qQ : Polynomial ℕ}
    (hSTEP : STEP ∈ FP) (hEMIT : EMIT ∈ FP) (hW : Wf ∈ FP) (hSf : Sf ∈ FP)
    (hSbnd : ∀ W cli tok : List Bool,
      (STEP (pair W (pair cli tok))).length ≤ cli.length + tok.length + c)
    (hEbnd : ∀ W cli tok : List Bool,
      (EMIT (pair W (pair cli tok))).length
        ≤ qQ.eval W.length + k * (cli.length + tok.length))
    (cli₀ out₀ : List Bool) :
    (fun z => (tkFold STEP EMIT (Wf z) [] cli₀ out₀ (bitsToDigits (Sf z))).2.2) ∈ FP := by
  classical
  set p : Polynomial ℕ := Polynomial.C (16 + 2 * cli₀.length + out₀.length)
      + Polynomial.C (2 * (3 + c)) * Polynomial.X
      + Polynomial.X * qQ
      + Polynomial.C (k * cli₀.length) * Polynomial.X
      + Polynomial.C (k * (3 + c)) * (Polynomial.X * Polynomial.X) with hp
  have hfold : (fun z => foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) (Wf z)
      (tkSt (pair [] []) [] cli₀ out₀) (Sf z)) ∈ FP := by
    refine foldlBits_mem_FP (tkStep_mem_FP hSTEP hEMIT false)
      (tkStep_mem_FP hSTEP hEMIT true) hW hSf (tkSt (pair [] []) [] cli₀ out₀) p
      (fun z u hu => ?_)
    obtain ⟨p0', p1', tok', cli', out', hst, h0', h1', hsum, hout⟩ :=
      tkRun_bound (c := c) (Q := qQ.eval (Wf z).length) (W := Wf z)
        (fun cli tok => hSbnd (Wf z) cli tok)
        (fun cli tok => hEbnd (Wf z) cli tok) u [] [] [] cli₀ out₀ (by simp) (by simp)
    rw [hst, tkSt, pair_length, pair_length, pair_length, pair_length]
    have hQ : qQ.eval (Wf z).length ≤ qQ.eval ((Wf z).length + (Sf z).length) :=
      polynomial_eval_mono_nat qQ (by omega)
    have hL : u.length ≤ (Wf z).length + (Sf z).length := by omega
    simp only [hp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    simp only [List.length_nil] at hsum hout
    exact tkFold_arith _ _ _ _ _ _ _ _ _ _ _ _ _ h0' h1' hsum hout hL hQ
  have hcomp := mem_FP_comp hfold
    (mem_FP_comp (mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP) sndBlock_mem_FP)
  have heq : ((sndBlock ∘ sndBlock ∘ sndBlock) ∘
        fun z => foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) (Wf z)
          (tkSt (pair [] []) [] cli₀ out₀) (Sf z))
      = fun z => (tkFold STEP EMIT (Wf z) [] cli₀ out₀ (bitsToDigits (Sf z))).2.2 := by
    funext z
    exact tkFold_out STEP EMIT (Wf z) (Sf z) [] cli₀ out₀
  rwa [heq] at hcomp


#print axioms LogicalInduction.TokenFold.LEUnary.unaryOfDigitsLE_le_mem_FP
#print axioms LogicalInduction.TokenFold.tkFold_out
#print axioms LogicalInduction.TokenFold.tkFold_mem_FP

end LogicalInduction.TokenFold
