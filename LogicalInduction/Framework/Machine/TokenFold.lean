import LogicalInduction.Framework.Machine.FPFold
import LogicalInduction.Framework.DigitArith
import Complexitylib.Classes.P.Cobham

/-!
# Tokenizing transductions in `Complexity.FP`

`MachineEfficientTrader` (`Framework/Criterion.lean`) reads a machine's output word as a
*token* stream: three bits per digit (`Framework/Machine/DigitBits.lean`), digits below four
accumulating little-endian into a token and any digit from four up closing the block
(`undigitize`). Transporting a trader across a rewrite of that stream — splicing a
conditioning block, freezing a price leaf — therefore means running a token-level transducer
on a *bit* word, in polynomial time.

`Framework/Machine/FPFold.lean` is the engine: `foldlBits_mem_FP`, a left fold whose step is
`FP` and whose state stays polynomially bounded. This file is the tokenizer built on that
engine — the pieces a client of it has to supply. Nothing here is a paper claim, so the
declarations are `lemma`s carrying no `Paper node` line.

## What the file builds

* **`dgFold`** — the three-bit digit fold. Every reader of this stream consumes it three
  bits at a time, so `dgStep` does that once and for all: a two-slot phase fills, the third
  bit completes a digit, and the client is handed it as `digitSlots` — three separately
  *headable* one-bit words, because `Complexity.FP` has `selectHead` but no `tail`.
  `dgFold_cli` proves the realization on every bit word and `dgFold_mem_FP` places it in
  `FP` from one per-digit length hypothesis. The two clients below are instances.

* **`LEUnary`** — reading a token's value back as a length. The stream carries token values
  as `undigitize`'s little-endian base-four digit runs, and `unaryOfDigitsLE_le_mem_FP` is
  the primitive that reads one: `leDigit`, a digit-fold client folding a token's own
  digit-bit block into `min value cap` marks, with `cap` a length already in hand. The guard
  is not optional — a `k`-bit value denotes up to `4 ^ k` marks — and it is exactly what the
  clients have: a day read out of a day-`n` stream is `≤ n`, and every token test the
  conditioning automaton makes factors through a small clamp.

* **`Increment`** — the converse direction: a value known only as a *length* rendered back
  into the stream as base-four digits, one carry-propagating increment per mark. The run it
  builds is deliberately not the canonical `natDigits4` one; `undigitize` reads a token's
  value, and `unaryToDigits_val` is that value.

* **`TokenFold`** — the tokenizer itself. `tkStep` is one bit of the digit/token parser: a
  two-slot phase fills, a complete digit either extends the current token block or (its
  leading bit set) closes it, and closing calls the client's `STEP`/`EMIT` on the token's
  digit-bit block. `tkFold` is the digit-level model it realizes, `tkFold_out` proves the
  realization on *every* bit word — malformed ones included, where a trailing partial digit
  is discarded exactly as `bitsToDigits` discards it — and `tkFold_mem_FP` places the
  composite in `FP` from two per-step length hypotheses on the client.

## Three client granularities

`tkFold` (one digit) → `runFold` (one block, `tkFold_blockSplit`) → `natFold` (one token
value, `runFold_natFold`), each with an `FP` closure lemma and an `_cli` variant for a client
computing a value rather than a stream. `BlockWF` and `decodeBits` are the splice discipline
— every piece a whole number of complete blocks — under which the machine's reading
distributes over a concatenation. `matchPass`/`ifMatch_mem_FP` decide whether a word's token
stream is one particular fixed list, the run matcher's per-candidate call.

## Why the client sees bits, not numbers

The client receives each token as its raw digit-bit block rather than as a number, which is
deliberate: an arbitrary machine word may carry a *non-canonical* run (`[1, 0]` and `[1]` are
both the token `1`), so a client that compared blocks against constant words would be wrong
on inputs `undigitize` reads identically. The supported reads are `LEUnary`'s clamp, whose
guard makes the value a length, and the fixed-numeral test `ifNumEq_mem_FP`, justified by
`digitVal_eq_iff_zero_padded`. Every test the conditioning and freeze automata make is a
comparison against a small constant or against the day, and both have a cap available.
-/

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

/-! ## Digits: values, bits, and slots

The value a digit run denotes is `Framework/DigitArith.lean`'s `digitVal`, the same
little-endian base-four reading `undigitize` performs; nothing new is defined here.  What
is new is `digitSlots`, the shape a *client* of the digit fold below can branch on.

Proof kind: `P` throughout.  Provenance: (b) `Machine/DigitBits.lean`,
`Framework/DigitArith.lean`. -/

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

lemma mem_bitsToDigits_lt_eight (w : List Bool) : ∀ d ∈ bitsToDigits w, d < 8 := by
  intro d hd
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp (by rwa [bitsToDigits] at hd)
  rw [digitAt]
  have h : ∀ b : Bool, b2n b ≤ 1 := by intro b; cases b <;> simp [b2n]
  have h0 := h ((w[3 * i]?).getD false)
  have h1 := h ((w[3 * i + 1]?).getD false)
  have h2 := h ((w[3 * i + 2]?).getD false)
  omega

@[simp] lemma digitsToBits_nil : digitsToBits [] = [] := rfl

@[simp] lemma digitsToBits_cons (d : ℕ) (ds : List ℕ) :
    digitsToBits (d :: ds) = digitBits d ++ digitsToBits ds := rfl

lemma digitsToBits_append (a b : List ℕ) :
    digitsToBits (a ++ b) = digitsToBits a ++ digitsToBits b := by
  simp [digitsToBits, List.flatMap_append]

@[simp] lemma length_digitsToBits (ds : List ℕ) :
    (digitsToBits ds).length = 3 * ds.length := by
  induction ds with
  | nil => simp [digitsToBits]
  | cons d ds ih =>
      rw [digitsToBits_cons, List.length_append, length_digitBits, ih, List.length_cons]
      omega

/-- A digit handed to a client as three separately-headable one-bit slots.  This is the
shape a client can branch on: `Complexity.FP` has `selectHead` but no `tail`, so a flat
three-bit word would be unusable past its first bit. -/
def digitSlots (d : ℕ) : List Bool :=
  pair [(d / 4) % 2 == 1] (pair [(d / 2) % 2 == 1] [d % 2 == 1])

/-! ### Selection helpers -/

lemma selectHead_true (x y : List Bool) : selectHead [true] x y = x := by
  rw [selectHead_eq]
  simp [headFlag]

lemma selectHead_false (x y : List Bool) : selectHead [false] x y = y := by
  rw [selectHead_eq]
  simp [headFlag]

/-! ### Length bounds on the block projections

The clamp inside `FPFold.foldlBits_mem_FP` has to be discharged on malformed words, where
`fstBlock`/`sndBlock` are the partial decoders rather than projections.  Both are still
non-expanding, which is all a client's length hypothesis needs; the fork proves neither. -/

lemma unpair?_length_le : ∀ (z : List Bool) (p : List Bool × List Bool),
    Complexity.unpair? z = some p → p.2.length ≤ z.length
  | [], _, h => by simp [Complexity.unpair?] at h
  | false :: true :: y, p, h => by
      rw [Complexity.unpair?] at h
      cases h
      simp
      omega
  | false :: false :: z, p, h => by
      rw [Complexity.unpair?] at h
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
      have := unpair?_length_le z q hq
      simpa using by omega
  | true :: true :: z, p, h => by
      rw [Complexity.unpair?] at h
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
      have := unpair?_length_le z q hq
      simpa using by omega
  | [_], _, h => by simp [Complexity.unpair?] at h
  | true :: false :: _, _, h => by simp [Complexity.unpair?] at h

lemma sndBlock_length_le (z : List Bool) : (sndBlock z).length ≤ z.length := by
  rw [sndBlock]
  cases hz : Complexity.unpair? z with
  | none => simp
  | some p => exact unpair?_length_le z p hz

/-- The suffix decoder ignores a leading doubled bit. -/
private lemma sndBlock_cons_cons (b : Bool) (z : List Bool) (h : b = false ∨ b = true) :
    sndBlock (b :: b :: z) = sndBlock z := by
  rw [sndBlock, sndBlock]
  cases b <;>
    · rw [Complexity.unpair?]
      cases hz : Complexity.unpair? z with
      | none => simp
      | some p => simp

/-- **The packed-word budget.**  Unpairing never costs more than the word it unpacks, and
the doubling in `pair`'s framing is charged to the first component.  This is what keeps a
client whose state is a nest of `pair`s on an *additive* per-step bound: bounding each
projection separately by the whole word gives a multiplier, and a multiplicative per-step
bound compounds to `k ^ L`, which is not polynomial.

Proof kind: `P` proved.  Provenance: (b) `Complexity.unpair?`, `Cobham.fstBlock`. -/
lemma two_fstBlock_add_sndBlock_le : ∀ z : List Bool,
    2 * (fstBlock z).length + (sndBlock z).length ≤ z.length
  | [] => by simp [fstBlock, sndBlock, Complexity.unpair?]
  | [_] => by simp [fstBlock, sndBlock, Complexity.unpair?]
  | false :: true :: y => by
      rw [show fstBlock (false :: true :: y) = [] from rfl,
        show sndBlock (false :: true :: y) = y by rw [sndBlock, Complexity.unpair?]]
      simp
      omega
  | true :: false :: y => by
      rw [show fstBlock (true :: false :: y) = [] from rfl,
        show sndBlock (true :: false :: y) = [] by
          rw [sndBlock, show Complexity.unpair? (true :: false :: y) = none from rfl]]
      simp
  | false :: false :: z => by
      rw [show fstBlock (false :: false :: z) = false :: fstBlock z from rfl,
        sndBlock_cons_cons false z (Or.inl rfl)]
      have := two_fstBlock_add_sndBlock_le z
      simp only [List.length_cons]
      omega
  | true :: true :: z => by
      rw [show fstBlock (true :: true :: z) = true :: fstBlock z from rfl,
        sndBlock_cons_cons true z (Or.inr rfl)]
      have := two_fstBlock_add_sndBlock_le z
      simp only [List.length_cons]
      omega

lemma fstBlock_length_le : ∀ z : List Bool, (fstBlock z).length ≤ z.length
  | [] => by simp [fstBlock]
  | [_] => by simp [fstBlock]
  | false :: false :: z => by
      rw [fstBlock]
      have := fstBlock_length_le z
      simp only [List.length_cons]
      omega
  | true :: true :: z => by
      rw [fstBlock]
      have := fstBlock_length_le z
      simp only [List.length_cons]
      omega
  | false :: true :: _ => by simp [fstBlock]
  | true :: false :: _ => by simp [fstBlock]

/-! ### Comparing lengths

Every client of the folds below has to test a small number against a token value or a
counter, and all of those tests factor through "is this word at least as long as that one".
`Complexity.FP` has `takeLen` but no `drop`, so the flag has to come from the Cobham
algebra, where the fork proves `dropFn`; `CobhamFP_eq_FP` carries it back.

Proof kind: `C` composition.  Provenance: (b) `Cobham.dropFn`, `Cobham.tailFn`,
`CobhamFP_subset_FP`, `FP_subset_CobhamFP`, `Cobham.selectHead_emptyFlag_nil/_cons`. -/

lemma mem_FP_of_cobham {f : List Bool → List Bool}
    (h : Cobham fun v : Fin 1 → List Bool => f (v 0)) : f ∈ FP :=
  CobhamFP_subset_FP h

lemma cobham_of_mem_FP {f : List Bool → List Bool} (h : f ∈ FP) :
    Cobham fun v : Fin 1 → List Bool => f (v 0) :=
  FP_subset_CobhamFP h

/-- Dropping a prefix at the width of another word is polynomial time.  The fork proves it
in the Cobham algebra (`Cobham.dropFn`) but exposes no `FP` form; this is that form, and it
is the primitive the length comparisons below are built from. -/
lemma dropLenFn_mem_FP {A B : List Bool → List Bool} (hA : A ∈ FP) (hB : B ∈ FP) :
    (fun z => (B z).drop (A z).length) ∈ FP :=
  mem_FP_of_cobham (Cobham.dropFn (cobham_of_mem_FP hA) (cobham_of_mem_FP hB))

/-- A flag word whose head is `true` exactly when `|b| ≤ |a|`. -/
def leFlag (a b : List Bool) : List Bool := emptyFlag (b.drop a.length)

lemma selectHead_leFlag (a b x y : List Bool) :
    selectHead (leFlag a b) x y = if b.length ≤ a.length then x else y := by
  rw [leFlag]
  by_cases h : b.length ≤ a.length
  · rw [if_pos h, List.drop_eq_nil_of_le h]
    exact selectHead_emptyFlag_nil x y
  · rw [if_neg h]
    obtain ⟨c, cs, hc⟩ : ∃ c cs, b.drop a.length = c :: cs := by
      cases hd : b.drop a.length with
      | nil =>
          exact absurd (List.drop_eq_nil_iff.mp hd) h
      | cons c cs => exact ⟨c, cs, rfl⟩
    rw [hc]
    exact selectHead_emptyFlag_cons c cs x y

lemma leFlag_mem_FP {A B : List Bool → List Bool} (hA : A ∈ FP) (hB : B ∈ FP) :
    (fun z => leFlag (A z) (B z)) ∈ FP :=
  emptyFlag_mem_FP (dropLenFn_mem_FP hA hB)

/-- Branch on `|b| ≤ |a|`. -/
lemma selectHeadFn_leFlag_mem_FP {A B X Y : List Bool → List Bool}
    (hA : A ∈ FP) (hB : B ∈ FP) (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if (B z).length ≤ (A z).length then X z else Y z) ∈ FP := by
  have h := selectHeadFn_mem_FP (leFlag_mem_FP hA hB) hX hY
  have heq : (fun z => selectHead (leFlag (A z) (B z)) (X z) (Y z))
      = fun z => if (B z).length ≤ (A z).length then X z else Y z := by
    funext z
    exact selectHead_leFlag (A z) (B z) (X z) (Y z)
  rwa [heq] at h

/-- Branch on `|a| = |b|`, the test every small-numeral comparison factors through. -/
lemma selectHeadFn_eqLen_mem_FP {A B X Y : List Bool → List Bool}
    (hA : A ∈ FP) (hB : B ∈ FP) (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if (A z).length = (B z).length then X z else Y z) ∈ FP := by
  have h := selectHeadFn_leFlag_mem_FP hA hB
    (selectHeadFn_leFlag_mem_FP hB hA hX hY) hY
  have heq : (fun z => if (B z).length ≤ (A z).length then
        (if (A z).length ≤ (B z).length then X z else Y z) else Y z)
      = fun z => if (A z).length = (B z).length then X z else Y z := by
    funext z
    by_cases h1 : (B z).length ≤ (A z).length
    · by_cases h2 : (A z).length ≤ (B z).length
      · rw [if_pos h1, if_pos h2, if_pos (by omega)]
      · rw [if_pos h1, if_neg h2, if_neg (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
  rwa [heq] at h

/-- The `tail` of a member of the class: the unary predecessor. -/
lemma tail_mem_FP {A : List Bool → List Bool} (hA : A ∈ FP) :
    (fun z => (A z).tail) ∈ FP :=
  mem_FP_of_cobham (Cobham.tailFn (cobham_of_mem_FP hA))

/-! ### Branching on a length, and on a whole constant word

`ifEqLen_mem_FP` and `ifLeLen_mem_FP` are the two shapes every small-numeral comparison
factors through, and both machine clients reach them here.

`eqConstFn_mem_FP` is the piece the fork does not supply: deciding a word against
a **fixed** constant.  `Complexity.selectHead` branches on one bit, so equality against a
constant of length `k` is a nest of `k` such branches over iterated tails — constant depth,
because the constant is fixed at elaboration time.  It is what a token test needs when the
value compared against is too large to reach through a clamp: a `k`-bit numeral cannot be
named by a unary word, but its *digit bits* are a constant word. -/

/-- Branch on `|A z| = k` for a fixed `k`. -/
lemma ifEqLen_mem_FP {A X Y : List Bool → List Bool} (hA : A ∈ FP) (k : ℕ)
    (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if (A z).length = k then X z else Y z) ∈ FP := by
  have h := selectHeadFn_eqLen_mem_FP hA
    (constFn_mem_FP (List.replicate k true)) hX hY
  simpa using h

/-- Branch on `|A z| ≤ k` for a fixed `k`. -/
lemma ifLeLen_mem_FP {A X Y : List Bool → List Bool} (hA : A ∈ FP) (k : ℕ)
    (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if (A z).length ≤ k then X z else Y z) ∈ FP := by
  have h := selectHeadFn_leFlag_mem_FP (constFn_mem_FP (List.replicate k true)) hA hX hY
  simpa using h

/-- **Branching on equality with a fixed word.**

`selectHead` gives nothing on the empty word, so each level guards with `emptyFlag` first
and only then reads the leading bit; the recursion is on the constant, so its depth is a
literal rather than data.

Proof kind: `P` proved.  Provenance: (b) `Complexity.selectHeadFn_mem_FP`,
`Cobham.emptyFlag_mem_FP`, `tail_mem_FP`, `selectHeadFn_eqLen_mem_FP`. -/
lemma eqConstFn_mem_FP : ∀ (c : List Bool) {A X Y : List Bool → List Bool},
    A ∈ FP → X ∈ FP → Y ∈ FP → (fun z => if A z = c then X z else Y z) ∈ FP
  | [], A, X, Y, hA, hX, hY => by
      have h := ifEqLen_mem_FP hA 0 hX hY
      have heq : (fun z => if (A z).length = 0 then X z else Y z)
          = fun z => if A z = [] then X z else Y z := by
        funext z
        by_cases hz : A z = []
        · rw [if_pos hz, if_pos (by rw [hz]; rfl)]
        · rw [if_neg hz, if_neg (by simpa using hz)]
      rwa [heq] at h
  | (b :: cs), A, X, Y, hA, hX, hY => by
      have hT : (fun z => (A z).tail) ∈ FP := tail_mem_FP hA
      have hrec : (fun z => if (A z).tail = cs then X z else Y z) ∈ FP :=
        eqConstFn_mem_FP cs hT hX hY
      have hbranch : (fun z => selectHead (A z)
            (if b then (if (A z).tail = cs then X z else Y z) else Y z)
            (if b then Y z else (if (A z).tail = cs then X z else Y z))) ∈ FP := by
        cases b
        · simpa using selectHeadFn_mem_FP hA hY hrec
        · simpa using selectHeadFn_mem_FP hA hrec hY
      have h := selectHeadFn_mem_FP (emptyFlag_mem_FP hA) hY hbranch
      have heq : (fun z => selectHead (emptyFlag (A z)) (Y z)
            (selectHead (A z)
              (if b then (if (A z).tail = cs then X z else Y z) else Y z)
              (if b then Y z else (if (A z).tail = cs then X z else Y z))))
          = fun z => if A z = b :: cs then X z else Y z := by
        funext z
        cases hz : A z with
        | nil =>
            rw [selectHead_emptyFlag_nil, if_neg (by simp)]
        | cons a t =>
            rw [selectHead_emptyFlag_cons, selectHead]
            cases a <;> cases b <;> simp [List.cons.injEq]
      rwa [heq] at h

/-! ## The digit-level fold -/

/-- The packed digit-fold state: a two-slot phase and the client state. -/
def dgSt (ph cli : List Bool) : List Bool := pair ph cli

-- The digit step's argument is `pair W (dgSt (pair p0 p1) cli)`; these read its parts.
private def dW (v : List Bool) : List Bool := fstBlock v
private def dst (v : List Bool) : List Bool := sndBlock v
private def dph (v : List Bool) : List Bool := fstBlock (dst v)
private def dp0 (v : List Bool) : List Bool := fstBlock (dph v)
private def dp1 (v : List Bool) : List Bool := sndBlock (dph v)
private def dcli (v : List Bool) : List Bool := sndBlock (dst v)

/-- One bit of a three-bit digit fold: two slots fill, the third completes the digit and
hands the client its three bits. -/
def dgStep (STEP : List Bool → List Bool) (b : Bool) (v : List Bool) : List Bool :=
  selectHead (emptyFlag (dp0 v))
    (dgSt (pair [b] []) (dcli v))
    (selectHead (emptyFlag (dp1 v))
      (dgSt (pair (dp0 v) [b]) (dcli v))
      (dgSt (pair [] [])
        (STEP (pair (dW v) (pair (dcli v) (pair (dp0 v) (pair (dp1 v) [b])))))))

/-- The digit-level model `dgStep` realizes. -/
def dgFold (STEP : List Bool → List Bool) (W : List Bool) :
    List Bool → List ℕ → List Bool
  | cli, [] => cli
  | cli, d :: ds => dgFold STEP W (STEP (pair W (pair cli (digitSlots d)))) ds

private lemma dgStep_three (STEP : List Bool → List Bool) (W cli : List Bool)
    (b0 b1 b2 : Bool) :
    foldlBits (dgStep STEP false) (dgStep STEP true) W (dgSt (pair [] []) cli) [b0, b1, b2]
      = dgSt (pair [] [])
          (STEP (pair W (pair cli (digitSlots (4 * b2n b0 + 2 * b2n b1 + b2n b2))))) := by
  cases b0 <;> cases b1 <;> cases b2 <;>
    simp [foldlBits, dgStep, dgSt, dW, dst, dph, dp0, dp1, dcli,
      selectHead_true, selectHead_emptyFlag_cons, b2n, digitSlots]

/-- **The bit-level digit fold realizes the digit-level model, on every bit word.** A
trailing partial digit is discarded exactly as `bitsToDigits` discards it, so the statement
needs no well-formedness hypothesis on `W`. -/
lemma dgFold_cli (STEP : List Bool → List Bool) (W : List Bool) :
    ∀ (w cli : List Bool),
      sndBlock (foldlBits (dgStep STEP false) (dgStep STEP true) W
          (dgSt (pair [] []) cli) w)
        = dgFold STEP W cli (bitsToDigits w)
  | [], cli => by
      rw [foldlBits_nil, bitsToDigits_of_length_lt_three [] (by simp), dgFold]
      simp [dgSt]
  | [b0], cli => by
      rw [bitsToDigits_of_length_lt_three [b0] (by simp), dgFold,
        show ([b0] : List Bool) = [] ++ [b0] from rfl,
        foldlBits_append_singleton, foldlBits_nil]
      cases b0 <;>
        simp [dgStep, dgSt, dW, dst, dph, dp0, dp1, dcli, selectHead_true]
  | [b0, b1], cli => by
      rw [bitsToDigits_of_length_lt_three [b0, b1] (by simp), dgFold,
        show ([b0, b1] : List Bool) = [b0] ++ [b1] from rfl,
        foldlBits_append_singleton]
      cases b0 <;> cases b1 <;>
        simp [foldlBits, dgStep, dgSt, dW, dst, dph, dp0, dp1, dcli,
          selectHead_true, selectHead_emptyFlag_cons]
  | b0 :: b1 :: b2 :: rest, cli => by
      rw [bitsToDigits_cons3, dgFold,
        show (b0 :: b1 :: b2 :: rest) = [b0, b1, b2] ++ rest from rfl,
        foldlBits_append, dgStep_three, dgFold_cli STEP W rest _]

/-! ### The state bound -/

private def DgBnd (m : ℕ) (st : List Bool) : Prop :=
  ∃ p0 p1 cli, st = dgSt (pair p0 p1) cli ∧
    p0.length ≤ 1 ∧ p1.length ≤ 1 ∧ cli.length ≤ m

private lemma DgBnd.step {STEP : List Bool → List Bool} {Q c m : ℕ} {W : List Bool}
    (hS : ∀ (cli : List Bool) (b0 b1 b2 : Bool),
      (STEP (pair W (pair cli (pair [b0] (pair [b1] [b2]))))).length ≤ Q + cli.length + c)
    {st : List Bool} (h : DgBnd m st) (b : Bool) :
    DgBnd (m + Q + c) (dgStep STEP b (pair W st)) := by
  obtain ⟨p0, p1, cli, rfl, h0, h1, hm⟩ := h
  match p0, h0 with
  | [], _ =>
      refine ⟨[b], [], cli, ?_, by simp, by simp, by omega⟩
      simp [dgStep, dgSt, dW, dst, dph, dp0, dp1, dcli, selectHead_true]
  | [x], _ =>
      match p1, h1 with
      | [], _ =>
          refine ⟨[x], [b], cli, ?_, by simp, by simp, by omega⟩
          cases x <;>
            simp [dgStep, dgSt, dW, dst, dph, dp0, dp1, dcli,
              selectHead_true, selectHead_emptyFlag_cons]
      | [y], _ =>
          refine ⟨[], [], STEP (pair W (pair cli (pair [x] (pair [y] [b])))), ?_,
            by simp, by simp, ?_⟩
          · cases x <;> cases y <;>
              simp [dgStep, dgSt, dW, dst, dph, dp0, dp1, dcli,
                selectHead_emptyFlag_cons]
          · have hb := hS cli x y b
            omega

private lemma DgBnd.fold {STEP : List Bool → List Bool} {Q c : ℕ} {W : List Bool}
    (hS : ∀ (cli : List Bool) (b0 b1 b2 : Bool),
      (STEP (pair W (pair cli (pair [b0] (pair [b1] [b2]))))).length ≤ Q + cli.length + c) :
    ∀ (u st : List Bool) (m : ℕ), DgBnd m st →
      DgBnd (m + u.length * (Q + c))
        (foldlBits (dgStep STEP false) (dgStep STEP true) W st u)
  | [], st, m, h => by simpa using h
  | b :: bs, st, m, h => by
      rw [foldlBits_cons]
      have hstep : DgBnd (m + Q + c)
          ((bif b then dgStep STEP true else dgStep STEP false) (pair W st)) := by
        cases b
        · exact h.step hS false
        · exact h.step hS true
      have := DgBnd.fold hS bs _ (m + Q + c) hstep
      obtain ⟨p0, p1, cli, hst, h0, h1, hm⟩ := this
      refine ⟨p0, p1, cli, hst, h0, h1, ?_⟩
      simp only [List.length_cons]
      nlinarith [hm]

private lemma DgBnd.length_le {m : ℕ} {st : List Bool} (h : DgBnd m st) :
    st.length ≤ 12 + m := by
  obtain ⟨p0, p1, cli, rfl, h0, h1, hm⟩ := h
  simp only [dgSt, pair_length]
  omega

/-! ### Membership -/

private lemma dW_mem_FP : dW ∈ FP := fstBlock_mem_FP
private lemma dph_mem_FP : dph ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
private lemma dp0_mem_FP : dp0 ∈ FP := mem_FP_comp dph_mem_FP fstBlock_mem_FP
private lemma dp1_mem_FP : dp1 ∈ FP := mem_FP_comp dph_mem_FP sndBlock_mem_FP
private lemma dcli_mem_FP : dcli ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP

lemma dgStep_mem_FP {STEP : List Bool → List Bool} (hSTEP : STEP ∈ FP) (b : Bool) :
    dgStep STEP b ∈ FP :=
  selectHeadFn_mem_FP (emptyFlag_mem_FP dp0_mem_FP)
    (pairFn_mem_FP (constFn_mem_FP (pair [b] [])) dcli_mem_FP)
    (selectHeadFn_mem_FP (emptyFlag_mem_FP dp1_mem_FP)
      (pairFn_mem_FP (pairFn_mem_FP dp0_mem_FP (constFn_mem_FP [b])) dcli_mem_FP)
      (pairFn_mem_FP (constFn_mem_FP (pair [] []))
        (mem_FP_comp
          (pairFn_mem_FP dW_mem_FP
            (pairFn_mem_FP dcli_mem_FP
              (pairFn_mem_FP dp0_mem_FP
                (pairFn_mem_FP dp1_mem_FP (constFn_mem_FP [b])))))
          hSTEP)))

/-- **The digit fold is in `FP`.** The client's whole obligation is one per-digit length
inequality, `hSbnd`, quantified over *arbitrary* words rather than over reachable states —
which is what `FPFold.foldlBits_mem_FP`'s clamp needs, since it must be discharged on the
machine's malformed inputs too. -/
lemma dgFold_mem_FP {STEP Wf Sf : List Bool → List Bool} {c : ℕ} {qP : Polynomial ℕ}
    (hSTEP : STEP ∈ FP) (hW : Wf ∈ FP) (hSf : Sf ∈ FP)
    (hSbnd : ∀ (W cli : List Bool) (b0 b1 b2 : Bool),
      (STEP (pair W (pair cli (pair [b0] (pair [b1] [b2]))))).length
        ≤ qP.eval W.length + cli.length + c)
    (cli₀ : List Bool) :
    (fun z => dgFold STEP (Wf z) cli₀ (bitsToDigits (Sf z))) ∈ FP := by
  set p : Polynomial ℕ := Polynomial.C (12 + cli₀.length)
      + Polynomial.X * qP + Polynomial.C c * Polynomial.X with hp
  have hfold : (fun z => foldlBits (dgStep STEP false) (dgStep STEP true) (Wf z)
      (dgSt (pair [] []) cli₀) (Sf z)) ∈ FP := by
    refine foldlBits_mem_FP (dgStep_mem_FP hSTEP false) (dgStep_mem_FP hSTEP true)
      hW hSf (dgSt (pair [] []) cli₀) p (fun z u hu => ?_)
    have hb := (DgBnd.fold (Q := qP.eval (Wf z).length) (c := c)
      (fun cli b0 b1 b2 => hSbnd (Wf z) cli b0 b1 b2) u (dgSt (pair [] []) cli₀) cli₀.length
      ⟨[], [], cli₀, rfl, by simp, by simp, le_rfl⟩).length_le
    have hQ : qP.eval (Wf z).length ≤ qP.eval ((Wf z).length + (Sf z).length) :=
      polynomial_eval_mono_nat qP (by omega)
    have hL : u.length ≤ (Wf z).length + (Sf z).length := by omega
    simp only [hp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    have hprod : u.length * (qP.eval (Wf z).length + c)
        ≤ ((Wf z).length + (Sf z).length) * qP.eval ((Wf z).length + (Sf z).length)
          + c * ((Wf z).length + (Sf z).length) := by
      have h1 : u.length * qP.eval (Wf z).length
          ≤ ((Wf z).length + (Sf z).length) * qP.eval ((Wf z).length + (Sf z).length) :=
        Nat.mul_le_mul hL hQ
      have h2 : u.length * c ≤ ((Wf z).length + (Sf z).length) * c :=
        Nat.mul_le_mul_right _ hL
      nlinarith [h1, h2]
    omega
  have hcomp := mem_FP_comp hfold sndBlock_mem_FP
  have heq : (sndBlock ∘ fun z => foldlBits (dgStep STEP false) (dgStep STEP true) (Wf z)
        (dgSt (pair [] []) cli₀) (Sf z))
      = fun z => dgFold STEP (Wf z) cli₀ (bitsToDigits (Sf z)) := by
    funext z
    exact dgFold_cli STEP (Wf z) (Sf z) cli₀
  rwa [heq] at hcomp

/-! ## Base-4 numerals: canonical runs, and uniqueness up to trailing zeros

These are general facts about `digitVal` and `natDigits4`, used both by the guarded
little-endian expansion below and by the token tests that compare a block's value
against a fixed numeral.  They sit at the file top level rather than inside `LEUnary`,
which is about one particular client of them. -/

lemma digitVal_natDigits4 : ∀ n : ℕ, digitVal (natDigits4 n) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero => simp [natDigits4]
      | succ m =>
          rw [natDigits4, digitVal_cons,
            ih ((m + 1) / 4) (Nat.div_lt_self (Nat.succ_pos m) (by norm_num))]
          omega

/-! ### Base-4 representation is unique up to trailing zeros

A token's value does not determine its digit run — `[1]` and `[1, 0]` are both the token
`1`, which is why a client reads blocks rather than words.  It determines it *up to trailing
zeros*, and that is what lets a token test compare against a fixed numeral: the run must
begin with the numeral's canonical digits and continue with nothing but zeros.  Both halves
are constant-word tests (`eqConstFn_mem_FP`, and a value-zero clamp). -/

/-- `digitVal` splits over concatenation, the tail shifted by the head's width. -/
lemma digitVal_append : ∀ (a b : List ℕ),
    digitVal (a ++ b) = digitVal a + 4 ^ a.length * digitVal b
  | [], b => by simp
  | (d :: a), b => by
      rw [List.cons_append, digitVal_cons, digitVal_cons, digitVal_append a b,
        List.length_cons, pow_succ]
      ring

@[simp] lemma digitVal_replicate_zero (m : ℕ) : digitVal (List.replicate m 0) = 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, digitVal_cons, ih]

/-- **Every digit run is its value's canonical run, zero-padded.**

Proof kind: `P` proved.  Provenance: (b) `natDigits4`, `Nat.div_add_mod`. -/
lemma exists_zero_pad_of_digitVal : ∀ (cur : List ℕ), (∀ d ∈ cur, d < 4) →
    ∃ m : ℕ, cur = natDigits4 (digitVal cur) ++ List.replicate m 0
  | [], _ => ⟨0, by simp [natDigits4]⟩
  | (d :: ds), hcur => by
      have hd : d < 4 := hcur d (List.mem_cons_self ..)
      have hds : ∀ e ∈ ds, e < 4 := fun e he => hcur e (List.mem_cons_of_mem _ he)
      obtain ⟨m, hm⟩ := exists_zero_pad_of_digitVal ds hds
      rw [digitVal_cons]
      cases hV : d + 4 * digitVal ds with
      | zero =>
          have hd0 : d = 0 := by omega
          have hw0 : digitVal ds = 0 := by omega
          refine ⟨m + 1, ?_⟩
          rw [hd0, natDigits4, List.nil_append, List.replicate_succ]
          congr 1
          rw [hm, hw0, natDigits4, List.nil_append]
      | succ v =>
          have hmod : (v + 1) % 4 = d := by omega
          have hdiv : (v + 1) / 4 = digitVal ds := by omega
          refine ⟨m, ?_⟩
          rw [natDigits4, hmod, hdiv, List.cons_append]
          congr 1

/-- **A digit run has a given value exactly when it is that value's canonical run followed
by zeros.**  This is the shape a fixed-numeral token test checks.

Proof kind: `C` composition.  Provenance: (a) `exists_zero_pad_of_digitVal`,
`digitVal_append`, `digitVal_natDigits4`.
-/
lemma digitVal_eq_iff_zero_padded (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) (K : ℕ) :
    digitVal cur = K ↔ ∃ m : ℕ, cur = natDigits4 K ++ List.replicate m 0 := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := exists_zero_pad_of_digitVal cur hcur
    exact ⟨m, by rw [hm, h]⟩
  · rintro ⟨m, rfl⟩
    rw [digitVal_append, digitVal_natDigits4, digitVal_replicate_zero]
    omega

/-! ## The guarded little-endian expansion

The first client of the digit fold, and the endianness residual named in the file header:
a token block read little-endian base four into `min value cap` unary marks. -/

namespace LEUnary

/-- The value the clamped accumulator holds after a digit list. -/
def leAccVal (cap : ℕ) : ℕ → ℕ → List ℕ → ℕ
  | m, _, [] => m
  | m, p, d :: ds => leAccVal cap (min (m + d * p) cap) (min (4 * p) (cap + 1)) ds

/-- The clamp is invisible below the cap: while the accumulated value stays under `cap`, the
guarded expansion agrees with the unguarded one. -/
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

-- The guarded-expansion client's state is `pair cap (pair acc (pair pow bits))`; these read
-- its parts.
private def leCap (v : List Bool) : List Bool := fstBlock v
private def leCli (v : List Bool) : List Bool := fstBlock (sndBlock v)
private def leAcc (v : List Bool) : List Bool := fstBlock (leCli v)
private def lePow (v : List Bool) : List Bool := sndBlock (leCli v)
private def leSlots (v : List Bool) : List Bool := sndBlock (sndBlock v)
private def leB0 (v : List Bool) : List Bool := fstBlock (leSlots v)
private def leB1 (v : List Bool) : List Bool := fstBlock (sndBlock (leSlots v))
private def leB2 (v : List Bool) : List Bool := sndBlock (sndBlock (leSlots v))

private def rep : ℕ → List Bool → List Bool
  | 0, _ => []
  | k + 1, p => p ++ rep k p

private def repPow (k : ℕ) (v : List Bool) : List Bool := rep k (lePow v)

private def mulSel (v : List Bool) : List Bool :=
  selectHead (leB0 v)
    (selectHead (leB1 v)
      (selectHead (leB2 v) (repPow 7 v) (repPow 6 v))
      (selectHead (leB2 v) (repPow 5 v) (repPow 4 v)))
    (selectHead (leB1 v)
      (selectHead (leB2 v) (repPow 3 v) (repPow 2 v))
      (selectHead (leB2 v) (repPow 1 v) (repPow 0 v)))

/-- One digit of the guarded expansion: fold it into the accumulator at the current place
value, then advance the place value, both truncated against the guard. -/
def leDigit (v : List Bool) : List Bool :=
  pair (List.take (leCap v).length (leAcc v ++ mulSel v))
    (List.take (leCap v ++ [true]).length (repPow 4 v))

private lemma leDigit_spec (W : List Bool) (m p d : ℕ) (hd : d < 8) :
    leDigit (pair W (pair (pair (List.replicate m true) (List.replicate p true))
        (digitSlots d)))
      = pair (List.replicate (min (m + d * p) W.length) true)
          (List.replicate (min (4 * p) (W.length + 1)) true) := by
  interval_cases d <;>
    simp [leDigit, leCap, leCli, leAcc, lePow, leSlots, leB0, leB1, leB2, mulSel,
      repPow, digitSlots, selectHead_true, selectHead_false, rep,
      List.take_replicate] <;>
    (congr 2 <;> omega)

/-- The place value after a digit list, clamped one past the guard. -/
def lePowVal (cap : ℕ) : ℕ → List ℕ → ℕ
  | p, [] => p
  | p, _ :: ds => lePowVal cap (min (4 * p) (cap + 1)) ds

/-- `leDigit` as a digit-fold client: folding a token's digit-bit block accumulates
`min value cap` marks. -/
lemma dgFold_leDigit (W : List Bool) : ∀ (ds : List ℕ) (m p : ℕ), (∀ d ∈ ds, d < 8) →
    dgFold leDigit W (pair (List.replicate m true) (List.replicate p true)) ds
      = pair (List.replicate (leAccVal W.length m p ds) true)
          (List.replicate (lePowVal W.length p ds) true)
  | [], m, p, _ => by rw [dgFold, leAccVal, lePowVal]
  | d :: ds, m, p, hds => by
      rw [dgFold, leDigit_spec W m p d (hds d (List.mem_cons_self ..)),
        dgFold_leDigit W ds _ _ (fun e he => hds e (List.mem_cons_of_mem _ he)),
        leAccVal, lePowVal]

private lemma leDigit_mem_FP : leDigit ∈ FP := by
  have hcap : leCap ∈ FP := fstBlock_mem_FP
  have hcli : leCli ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have hacc : leAcc ∈ FP := mem_FP_comp hcli fstBlock_mem_FP
  have hpow : lePow ∈ FP := mem_FP_comp hcli sndBlock_mem_FP
  have hslots : leSlots ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
  have hb0 : leB0 ∈ FP := mem_FP_comp hslots fstBlock_mem_FP
  have hb1 : leB1 ∈ FP := mem_FP_comp (mem_FP_comp hslots sndBlock_mem_FP) fstBlock_mem_FP
  have hb2 : leB2 ∈ FP := mem_FP_comp (mem_FP_comp hslots sndBlock_mem_FP) sndBlock_mem_FP
  have hrep : ∀ k : ℕ, repPow k ∈ FP := by
    intro k
    induction k with
    | zero => exact constFn_mem_FP []
    | succ k ih => exact appendFn_mem_FP hpow ih
  have hmul : mulSel ∈ FP :=
    selectHeadFn_mem_FP hb0
      (selectHeadFn_mem_FP hb1
        (selectHeadFn_mem_FP hb2 (hrep 7) (hrep 6))
        (selectHeadFn_mem_FP hb2 (hrep 5) (hrep 4)))
      (selectHeadFn_mem_FP hb1
        (selectHeadFn_mem_FP hb2 (hrep 3) (hrep 2))
        (selectHeadFn_mem_FP hb2 (hrep 1) (hrep 0)))
  exact pairFn_mem_FP (takeLenFn_mem_FP hcap (appendFn_mem_FP hacc hmul))
    (takeLenFn_mem_FP (appendFn_mem_FP hcap (constFn_mem_FP [true])) (hrep 4))

private lemma leDigit_length_le (W cli : List Bool) (b0 b1 b2 : Bool) :
    (leDigit (pair W (pair cli (pair [b0] (pair [b1] [b2]))))).length
      ≤ (3 * Polynomial.X + 3 : Polynomial ℕ).eval W.length + cli.length := by
  have hcap : leCap (pair W (pair cli (pair [b0] (pair [b1] [b2])))) = W := by simp [leCap]
  simp only [leDigit, hcap, pair_length, List.length_take, List.length_append,
    List.length_cons, List.length_nil, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

/-- **The guarded little-endian expansion is polynomial time**, as a digit-fold client. -/
lemma unaryOfDigitsLE_le_mem_FP {V C : List Bool → List Bool} (hV : V ∈ FP) (hC : C ∈ FP) :
    (fun z => List.replicate (min (digitVal (bitsToDigits (V z))) (C z).length) true) ∈ FP := by
  have hfold : (fun z => dgFold leDigit (C z) (pair [] [true]) (bitsToDigits (V z))) ∈ FP :=
    dgFold_mem_FP (c := 0) (qP := 3 * Polynomial.X + 3) leDigit_mem_FP hC hV
      (fun W cli b0 b1 b2 => by simpa using leDigit_length_le W cli b0 b1 b2) (pair [] [true])
  have hcomp := mem_FP_comp hfold fstBlock_mem_FP
  have heq : (fstBlock ∘ fun z => dgFold leDigit (C z) (pair [] [true]) (bitsToDigits (V z)))
      = fun z => List.replicate (min (digitVal (bitsToDigits (V z))) (C z).length) true := by
    funext z
    have hrun := dgFold_leDigit (C z) (bitsToDigits (V z)) 0 1
      (mem_bitsToDigits_lt_eight (V z))
    rw [show (List.replicate 0 true : List Bool) = [] from rfl,
      show (List.replicate 1 true : List Bool) = [true] from rfl] at hrun
    simp only [Function.comp_apply, hrun, fstBlock_pair]
    rw [leAccVal_spec (C z).length (bitsToDigits (V z)) 0 1 (Nat.zero_le _)]
    simp
  rwa [heq] at hcomp

end LEUnary

/-! ## The unary counter

The second client of the digit fold, and what the budget codes need: a value known only
as a *length* has to reach the stream as base-four digits.  One carry-propagating
increment per mark does it, and the run it builds need not be the canonical `natDigits4`
one — `undigitize` reads a token's value, and that is what `unaryToDigits_val` fixes. -/

namespace Increment

-- The increment client's state, and the three digit-bit slots it is handed.
private def icCli (v : List Bool) : List Bool := fstBlock (sndBlock v)
private def icDone (v : List Bool) : List Bool := fstBlock (icCli v)
private def icOut (v : List Bool) : List Bool := sndBlock (icCli v)
private def icSlots (v : List Bool) : List Bool := sndBlock (sndBlock v)
private def icB0 (v : List Bool) : List Bool := fstBlock (icSlots v)
private def icB1 (v : List Bool) : List Bool := fstBlock (sndBlock (icSlots v))
private def icB2 (v : List Bool) : List Bool := sndBlock (sndBlock (icSlots v))

/-- One digit of the little-endian carry increment: once the carry is resolved every
further digit is copied; before that a digit below three is raised and resolves it, and a
digit of three (or, on a malformed word, above) becomes zero and passes the carry on.

The resolved flag is re-emitted as the literal `[true]` rather than copied, so that the
client state's length is bounded by `|cli| + O(1)` on *every* word and not merely on the
reachable ones — the additive form is what keeps `dgFold_mem_FP`'s bound polynomial. -/
def incDigit (v : List Bool) : List Bool :=
  selectHead (emptyFlag (icDone v))
    (selectHead (icB0 v)
      (pair [] (icOut v ++ [false, false, false]))
      (selectHead (icB1 v)
        (selectHead (icB2 v)
          (pair [] (icOut v ++ [false, false, false]))
          (pair [true] (icOut v ++ [false, true, true])))
        (selectHead (icB2 v)
          (pair [true] (icOut v ++ [false, true, false]))
          (pair [true] (icOut v ++ [false, false, true])))))
    (pair [true] (icOut v ++ (icB0 v ++ icB1 v ++ icB2 v)))

/-- The digit-level model: the carry flag and the rewritten run. -/
def incRun : List ℕ → Bool × List ℕ
  | [] => (false, [])
  | d :: ds =>
      if d < 3 then (true, (d + 1) :: ds)
      else ((incRun ds).1, 0 :: (incRun ds).2)

/-- Once the carry is resolved the fold copies the rest of the run through. -/
private lemma dgFold_incDigit_done (W : List Bool) : ∀ (ds : List ℕ) (out : List Bool),
    (∀ d ∈ ds, d < 8) →
    dgFold incDigit W (pair [true] out) ds = pair [true] (out ++ digitsToBits ds)
  | [], out, _ => by rw [dgFold]; simp
  | d :: ds, out, hds => by
      rw [dgFold]
      have hd : d < 8 := hds d (List.mem_cons_self ..)
      have hstep : incDigit (pair W (pair (pair [true] out) (digitSlots d)))
          = pair [true] (out ++ digitBits d) := by
        interval_cases d <;>
          simp [incDigit, icCli, icDone, icOut, icSlots, icB0, icB1, icB2, digitSlots,
            digitBits, selectHead_true, selectHead_false, selectHead_emptyFlag_cons]
      rw [hstep, dgFold_incDigit_done W ds _ (fun e he => hds e (List.mem_cons_of_mem _ he)),
        digitsToBits_cons, List.append_assoc]

/-- Before the carry is resolved the fold realizes `incRun`. -/
private lemma dgFold_incDigit_carry (W : List Bool) : ∀ (ds : List ℕ) (out : List Bool),
    (∀ d ∈ ds, d < 8) →
    dgFold incDigit W (pair [] out) ds
      = pair (if (incRun ds).1 then [true] else [])
          (out ++ digitsToBits (incRun ds).2)
  | [], out, _ => by rw [dgFold, incRun]; simp
  | d :: ds, out, hds => by
      rw [dgFold, incRun]
      have hd : d < 8 := hds d (List.mem_cons_self ..)
      have htail : ∀ e ∈ ds, e < 8 := fun e he => hds e (List.mem_cons_of_mem _ he)
      by_cases hlt : d < 3
      · have hstep : incDigit (pair W (pair (pair [] out) (digitSlots d)))
            = pair [true] (out ++ digitBits (d + 1)) := by
          interval_cases d <;>
            simp [incDigit, icCli, icDone, icOut, icSlots, icB0, icB1, icB2, digitSlots,
              digitBits, selectHead_true, selectHead_false]
        rw [hstep, dgFold_incDigit_done W ds _ htail, if_pos hlt]
        simp only [digitsToBits_cons, List.append_assoc, if_true]
      · have hge : 3 ≤ d := by omega
        have hstep : incDigit (pair W (pair (pair [] out) (digitSlots d)))
            = pair [] (out ++ digitBits 0) := by
          interval_cases d <;>
            simp [incDigit, icCli, icDone, icOut, icSlots, icB0, icB1, icB2, digitSlots,
              digitBits, selectHead_true, selectHead_false]
        rw [hstep, dgFold_incDigit_carry W ds _ htail, if_neg hlt]
        simp only [digitsToBits_cons, List.append_assoc]

/-! ### What the increment computes -/

/-- The run the increment produces, with any carry left at the top discharged. -/
def incDigits (ds : List ℕ) : List ℕ :=
  if (incRun ds).1 then (incRun ds).2 else (incRun ds).2 ++ [1]

lemma incRun_length : ∀ ds : List ℕ, (incRun ds).2.length = ds.length
  | [] => rfl
  | d :: ds => by
      rw [incRun]
      by_cases h : d < 3
      · simp [h]
      · simp [h, incRun_length ds]

lemma incRun_digits_lt : ∀ (ds : List ℕ), (∀ d ∈ ds, d < 4) →
    ∀ e ∈ (incRun ds).2, e < 4
  | [], _ => by simp [incRun]
  | d :: ds, hds => by
      rw [incRun]
      have hd : d < 4 := hds d (List.mem_cons_self ..)
      have htail : ∀ e ∈ ds, e < 4 := fun e he => hds e (List.mem_cons_of_mem _ he)
      by_cases h : d < 3
      · simp only [if_pos h]
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · omega
        · exact htail e he
      · simp only [if_neg h]
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · omega
        · exact incRun_digits_lt ds htail e he

lemma incRun_spec : ∀ (ds : List ℕ), (∀ d ∈ ds, d < 4) →
    ((incRun ds).1 = true → digitVal (incRun ds).2 = digitVal ds + 1) ∧
      ((incRun ds).1 = false → digitVal (incRun ds).2 + 4 ^ ds.length = digitVal ds + 1)
  | [], _ => by
      refine ⟨by simp [incRun], fun _ => ?_⟩
      simp [incRun]
  | d :: ds, hds => by
      have hd : d < 4 := hds d (List.mem_cons_self ..)
      have htail : ∀ e ∈ ds, e < 4 := fun e he => hds e (List.mem_cons_of_mem _ he)
      obtain ⟨ih1, ih2⟩ := incRun_spec ds htail
      rw [incRun]
      by_cases h : d < 3
      · simp only [if_pos h]
        exact ⟨fun _ => by simp; omega, fun hf => by simp at hf⟩
      · simp only [if_neg h]
        have hd3 : d = 3 := by omega
        refine ⟨fun hf => ?_, fun hf => ?_⟩
        · have := ih1 hf
          simp only [digitVal_cons, this, hd3]
          omega
        · have := ih2 hf
          simp only [digitVal_cons, List.length_cons, pow_succ, hd3]
          omega

lemma incDigits_digits_lt (ds : List ℕ) (hds : ∀ d ∈ ds, d < 4) :
    ∀ e ∈ incDigits ds, e < 4 := by
  rw [incDigits]
  by_cases h : (incRun ds).1
  · simpa [h] using incRun_digits_lt ds hds
  · simp only [if_neg h]
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact incRun_digits_lt ds hds e he
    · simp at he; omega

lemma incDigits_val (ds : List ℕ) (hds : ∀ d ∈ ds, d < 4) :
    digitVal (incDigits ds) = digitVal ds + 1 := by
  obtain ⟨h1, h2⟩ := incRun_spec ds hds
  rw [incDigits]
  by_cases h : (incRun ds).1
  · rw [if_pos h]
    exact h1 h
  · rw [if_neg h, digitVal_append_singleton, incRun_length]
    have := h2 (by simpa using h)
    omega

lemma incDigits_length (ds : List ℕ) : (incDigits ds).length ≤ ds.length + 1 := by
  rw [incDigits]
  by_cases h : (incRun ds).1
  · rw [if_pos h, incRun_length]; omega
  · rw [if_neg h]; simp [incRun_length]

/-! ### The increment as a word function -/

private def icState (v : List Bool) : List Bool :=
  dgFold incDigit [] (pair [] []) (bitsToDigits (sndBlock v))

/-- One mark of the unary counter: increment the digit word held in the fold state,
discharging at the top any carry the run did not absorb. -/
def incStep (v : List Bool) : List Bool :=
  selectHead (emptyFlag (fstBlock (icState v)))
    (sndBlock (icState v) ++ digitBits 1)
    (sndBlock (icState v))

lemma incStep_spec (ds : List ℕ) (hds : ∀ d ∈ ds, d < 4) :
    incStep (pair [] (digitsToBits ds)) = digitsToBits (incDigits ds) := by
  have hlt8 : ∀ d ∈ ds, d < 8 := fun d hd => lt_trans (hds d hd) (by norm_num)
  have hst : icState (pair [] (digitsToBits ds))
      = pair (if (incRun ds).1 then [true] else []) (digitsToBits (incRun ds).2) := by
    rw [icState, sndBlock_pair, bitsToDigits_digitsToBits ds hlt8,
      dgFold_incDigit_carry [] ds [] hlt8]
    simp
  rw [incStep, hst, incDigits]
  by_cases h : (incRun ds).1
  · rw [if_pos h, if_pos h, fstBlock_pair, sndBlock_pair]
    exact selectHead_emptyFlag_cons true [] _ _
  · rw [if_neg h, if_neg h, fstBlock_pair, sndBlock_pair,
      selectHead_emptyFlag_nil, digitsToBits_append]
    rfl

/-! ### The unary counter -/

/-- The digit run denoting `n`, as the increment builds it. -/
def unaryDigits : ℕ → List ℕ
  | 0 => []
  | n + 1 => incDigits (unaryDigits n)

lemma unaryDigits_lt : ∀ (n : ℕ), ∀ d ∈ unaryDigits n, d < 4
  | 0 => by simp [unaryDigits]
  | n + 1 => incDigits_digits_lt _ (unaryDigits_lt n)

lemma unaryDigits_val : ∀ n : ℕ, digitVal (unaryDigits n) = n
  | 0 => rfl
  | n + 1 => by rw [unaryDigits, incDigits_val _ (unaryDigits_lt n), unaryDigits_val n]

lemma unaryDigits_length : ∀ n : ℕ, (unaryDigits n).length ≤ n
  | 0 => by simp [unaryDigits]
  | n + 1 => le_trans (incDigits_length _) (by have := unaryDigits_length n; omega)

/-- **Render a unary count as a little-endian base-four digit block.**  The run is not the
canonical `natDigits4` one and does not need to be: `undigitize` reads a token's value, and
`unaryToDigits_val` is that value. -/
def unaryToDigits (u : List Bool) : List Bool := foldlBits incStep incStep [] [] u

/-- The increment run, as the bit rendering of `unaryDigits`. -/
lemma unaryToDigits_eq (u : List Bool) :
    unaryToDigits u = digitsToBits (unaryDigits u.length) := by
  induction u using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih =>
      rw [unaryToDigits, foldlBits_append_singleton]
      have hb : (bif b then incStep else incStep) = incStep := by cases b <;> rfl
      rw [hb, show foldlBits incStep incStep [] [] bs = unaryToDigits bs from rfl, ih,
        incStep_spec _ (unaryDigits_lt bs.length)]
      simp [unaryDigits, List.length_append]

/-- The value `undigitize` reads back from the emitted run is the length of the unary word
it came from. The run is deliberately not the canonical `natDigits4` one. -/
lemma unaryToDigits_val (u : List Bool) :
    digitVal (bitsToDigits (unaryToDigits u)) = u.length := by
  rw [unaryToDigits_eq,
    bitsToDigits_digitsToBits _
      (fun d hd => lt_trans (unaryDigits_lt u.length d hd) (by norm_num)),
    unaryDigits_val]

/-! ### Membership -/

private lemma icCli_mem_FP : icCli ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
private lemma icDone_mem_FP : icDone ∈ FP := mem_FP_comp icCli_mem_FP fstBlock_mem_FP
private lemma icOut_mem_FP : icOut ∈ FP := mem_FP_comp icCli_mem_FP sndBlock_mem_FP
private lemma icSlots_mem_FP : icSlots ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
private lemma icB0_mem_FP : icB0 ∈ FP := mem_FP_comp icSlots_mem_FP fstBlock_mem_FP
private lemma icB1_mem_FP : icB1 ∈ FP :=
  mem_FP_comp (mem_FP_comp icSlots_mem_FP sndBlock_mem_FP) fstBlock_mem_FP
private lemma icB2_mem_FP : icB2 ∈ FP :=
  mem_FP_comp (mem_FP_comp icSlots_mem_FP sndBlock_mem_FP) sndBlock_mem_FP

private lemma incDigit_mem_FP : incDigit ∈ FP := by
  have hout3 : ∀ w : List Bool, (fun v => icOut v ++ w) ∈ FP :=
    fun w => appendFn_mem_FP icOut_mem_FP (constFn_mem_FP w)
  have hcarry : ∀ (w : List Bool) (d : List Bool),
      (fun v => pair d (icOut v ++ w)) ∈ FP :=
    fun w d => pairFn_mem_FP (constFn_mem_FP d) (hout3 w)
  exact selectHeadFn_mem_FP (emptyFlag_mem_FP icDone_mem_FP)
    (selectHeadFn_mem_FP icB0_mem_FP
      (hcarry [false, false, false] [])
      (selectHeadFn_mem_FP icB1_mem_FP
        (selectHeadFn_mem_FP icB2_mem_FP
          (hcarry [false, false, false] [])
          (hcarry [false, true, true] [true]))
        (selectHeadFn_mem_FP icB2_mem_FP
          (hcarry [false, true, false] [true])
          (hcarry [false, false, true] [true]))))
    (pairFn_mem_FP (constFn_mem_FP [true])
      (appendFn_mem_FP icOut_mem_FP
        (appendFn_mem_FP (appendFn_mem_FP icB0_mem_FP icB1_mem_FP) icB2_mem_FP)))

private lemma incDigit_length_le (W cli : List Bool) (b0 b1 b2 : Bool) :
    (incDigit (pair W (pair cli (pair [b0] (pair [b1] [b2]))))).length
      ≤ (0 : Polynomial ℕ).eval W.length + cli.length + 7 := by
  have hcli : icCli (pair W (pair cli (pair [b0] (pair [b1] [b2])))) = cli := by simp [icCli]
  have hslots : icSlots (pair W (pair cli (pair [b0] (pair [b1] [b2]))))
      = pair [b0] (pair [b1] [b2]) := by simp [icSlots]
  have hsnd := sndBlock_length_le cli
  have hbound : ∀ (d w : List Bool), d.length ≤ 1 → w.length ≤ 3 →
      (pair d (sndBlock cli ++ w)).length ≤ cli.length + 7 := by
    intro d w hd hw
    simp only [pair_length, List.length_append]
    omega
  simp only [incDigit, hcli, hslots, icDone, icOut, icB0, icB1, icB2, Polynomial.eval_zero,
    Nat.zero_add, fstBlock_pair, sndBlock_pair]
  refine le_trans (selectHead_length_le _ _ _) ?_
  refine max_le ?_ ?_
  · refine le_trans (selectHead_length_le _ _ _) (max_le ?_ ?_)
    · exact hbound [] _ (by simp) (by simp)
    · refine le_trans (selectHead_length_le _ _ _) (max_le ?_ ?_) <;>
        refine le_trans (selectHead_length_le _ _ _) (max_le ?_ ?_) <;>
        first
          | exact hbound [] _ (by simp) (by simp)
          | exact hbound [true] _ (by simp) (by simp)
  · exact hbound [true] _ (by simp) (by simp)

private lemma icState_mem_FP : icState ∈ FP :=
  dgFold_mem_FP (c := 7) (qP := 0) incDigit_mem_FP (constFn_mem_FP []) sndBlock_mem_FP
    incDigit_length_le (pair [] [])

lemma incStep_mem_FP : incStep ∈ FP :=
  selectHeadFn_mem_FP (emptyFlag_mem_FP (mem_FP_comp icState_mem_FP fstBlock_mem_FP))
    (appendFn_mem_FP (mem_FP_comp icState_mem_FP sndBlock_mem_FP)
      (constFn_mem_FP (digitBits 1)))
    (mem_FP_comp icState_mem_FP sndBlock_mem_FP)

/-- **Rendering a unary count as base-four digit bits is polynomial time.** -/
lemma unaryToDigits_mem_FP {U : List Bool → List Bool} (hU : U ∈ FP) :
    (fun z => unaryToDigits (U z)) ∈ FP := by
  have h := foldlBits_mem_FP (A := incStep) (B := incStep) (W := fun _ => [])
    (S := U) incStep_mem_FP incStep_mem_FP (constFn_mem_FP []) hU []
    (3 * Polynomial.X) (fun z u _ => ?_)
  · exact h
  · have : foldlBits incStep incStep [] [] u = digitsToBits (unaryDigits u.length) :=
      unaryToDigits_eq u
    rw [this, digitsToBits, List.length_flatMap]
    have hlen : ((unaryDigits u.length).map fun d => (digitBits d).length).sum
        = 3 * (unaryDigits u.length).length := by
      rw [show ((unaryDigits u.length).map fun d => (digitBits d).length)
          = List.replicate (unaryDigits u.length).length 3 from ?_]
      · simp [List.sum_replicate]; omega
      · rw [List.eq_replicate_iff]
        exact ⟨by simp, by intro b hb; obtain ⟨d, -, rfl⟩ := List.mem_map.mp hb; rfl⟩

    rw [hlen]
    have := unaryDigits_length u.length
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega

end Increment

/-! ## The generic bit-level tokenizer -/

/-- The packed tokenizer state: two-slot phase, current token block, client state,
output so far. -/
def tkSt (ph tok cli out : List Bool) : List Bool := pair ph (pair tok (pair cli out))

/-- The output component of a tokenizer state. -/
def outOf (st : List Bool) : List Bool := sndBlock (sndBlock (sndBlock st))

/-- The client-state component of a tokenizer state.  A client that computes a *value*
rather than a stream — an acceptance test, a counter read at the end — needs this rather
than `outOf`. -/
def cliOf (st : List Bool) : List Bool := fstBlock (sndBlock (sndBlock st))

-- The token step's argument is `pair W (tkSt (pair p0 p1) tok cli out)`; these read its
-- parts.
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
lemma tkFold_cli_out (STEP EMIT : List Bool → List Bool) (W : List Bool) :
    ∀ (w tok cli out : List Bool),
    cliOf (foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) W
        (tkSt (pair [] []) tok cli out) w)
      = (tkFold STEP EMIT W tok cli out (bitsToDigits w)).2.1 ∧
    outOf (foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) W
        (tkSt (pair [] []) tok cli out) w)
      = (tkFold STEP EMIT W tok cli out (bitsToDigits w)).2.2
  | [], tok, cli, out => by
      rw [foldlBits_nil, bitsToDigits_of_length_lt_three [] (by simp), tkFold]
      exact ⟨by simp [cliOf, tkSt], by simp [outOf, tkSt]⟩
  | [b0], tok, cli, out => by
      rw [bitsToDigits_of_length_lt_three [b0] (by simp), tkFold,
        show ([b0] : List Bool) = [] ++ [b0] from rfl,
        foldlBits_append_singleton, foldlBits_nil]
      cases b0 <;>
        exact ⟨by simp [tkStep, tkSt, cliOf, sst, phv, p0v, p1v, tokv, cliv, outv,
                 selectHead_true],
               by simp [tkStep, tkSt, outOf, sst, phv, p0v, p1v, tokv, cliv, outv,
                 selectHead_true]⟩
  | [b0, b1], tok, cli, out => by
      rw [bitsToDigits_of_length_lt_three [b0, b1] (by simp), tkFold,
        show ([b0, b1] : List Bool) = [b0] ++ [b1] from rfl,
        foldlBits_append_singleton]
      cases b0 <;> cases b1 <;>
        exact ⟨by simp [foldlBits, tkStep, tkSt, cliOf, sst, phv, p0v, p1v, tokv, cliv,
                 outv, selectHead_true, selectHead_false, selectHead_emptyFlag_cons],
               by simp [foldlBits, tkStep, tkSt, outOf, sst, phv, p0v, p1v, tokv, cliv,
                 outv, selectHead_true, selectHead_false, selectHead_emptyFlag_cons]⟩
  | b0 :: b1 :: b2 :: rest, tok, cli, out => by
      rw [bitsToDigits_cons3, tkFold,
        show (b0 :: b1 :: b2 :: rest) = [b0, b1, b2] ++ rest from rfl,
        foldlBits_append, tkStep_three]
      by_cases hd : 4 * b2n b0 + 2 * b2n b1 + b2n b2 < 4
      · rw [if_pos hd, if_pos hd]
        exact tkFold_cli_out STEP EMIT W rest _ _ _
      · rw [if_neg hd, if_neg hd]
        exact tkFold_cli_out STEP EMIT W rest _ _ _

/-- The output projection of `tkFold_cli_out`. -/
lemma tkFold_out (STEP EMIT : List Bool → List Bool) (W : List Bool)
    (w tok cli out : List Bool) :
    outOf (foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) W
        (tkSt (pair [] []) tok cli out) w)
      = (tkFold STEP EMIT W tok cli out (bitsToDigits w)).2.2 :=
  (tkFold_cli_out STEP EMIT W w tok cli out).2

/-- The client-state projection of `tkFold_cli_out`. -/
lemma tkFold_cli (STEP EMIT : List Bool → List Bool) (W : List Bool)
    (w tok cli out : List Bool) :
    cliOf (foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) W
        (tkSt (pair [] []) tok cli out) w)
      = (tkFold STEP EMIT W tok cli out (bitsToDigits w)).2.1 :=
  (tkFold_cli_out STEP EMIT W w tok cli out).1

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

/-- The engine step, shared by the two projections below: the bit fold itself is in `FP`
once the client's two length hypotheses hold. -/
lemma tkFoldBits_mem_FP {STEP EMIT Wf Sf : List Bool → List Bool} {c k : ℕ}
    {qQ : Polynomial ℕ}
    (hSTEP : STEP ∈ FP) (hEMIT : EMIT ∈ FP) (hW : Wf ∈ FP) (hSf : Sf ∈ FP)
    (hSbnd : ∀ W cli tok : List Bool,
      (STEP (pair W (pair cli tok))).length ≤ cli.length + tok.length + c)
    (hEbnd : ∀ W cli tok : List Bool,
      (EMIT (pair W (pair cli tok))).length
        ≤ qQ.eval W.length + k * (cli.length + tok.length))
    (cli₀ out₀ : List Bool) :
    (fun z => foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) (Wf z)
      (tkSt (pair [] []) [] cli₀ out₀) (Sf z)) ∈ FP := by
  classical
  set p : Polynomial ℕ := Polynomial.C (16 + 2 * cli₀.length + out₀.length)
      + Polynomial.C (2 * (3 + c)) * Polynomial.X
      + Polynomial.X * qQ
      + Polynomial.C (k * cli₀.length) * Polynomial.X
      + Polynomial.C (k * (3 + c)) * (Polynomial.X * Polynomial.X) with hp
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
  have hcomp := mem_FP_comp (tkFoldBits_mem_FP hSTEP hEMIT hW hSf hSbnd hEbnd cli₀ out₀)
    (mem_FP_comp (mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP) sndBlock_mem_FP)
  have heq : ((sndBlock ∘ sndBlock ∘ sndBlock) ∘
        fun z => foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) (Wf z)
          (tkSt (pair [] []) [] cli₀ out₀) (Sf z))
      = fun z => (tkFold STEP EMIT (Wf z) [] cli₀ out₀ (bitsToDigits (Sf z))).2.2 := by
    funext z
    exact tkFold_out STEP EMIT (Wf z) (Sf z) [] cli₀ out₀
  rwa [heq] at hcomp

/-- The same for the fold's **final client state**, which is what a client computing a
value rather than a stream reads. -/
lemma tkFold_cli_mem_FP {STEP EMIT Wf Sf : List Bool → List Bool} {c k : ℕ}
    {qQ : Polynomial ℕ}
    (hSTEP : STEP ∈ FP) (hEMIT : EMIT ∈ FP) (hW : Wf ∈ FP) (hSf : Sf ∈ FP)
    (hSbnd : ∀ W cli tok : List Bool,
      (STEP (pair W (pair cli tok))).length ≤ cli.length + tok.length + c)
    (hEbnd : ∀ W cli tok : List Bool,
      (EMIT (pair W (pair cli tok))).length
        ≤ qQ.eval W.length + k * (cli.length + tok.length))
    (cli₀ out₀ : List Bool) :
    (fun z => (tkFold STEP EMIT (Wf z) [] cli₀ out₀ (bitsToDigits (Sf z))).2.1) ∈ FP := by
  have hcomp := mem_FP_comp (tkFoldBits_mem_FP hSTEP hEMIT hW hSf hSbnd hEbnd cli₀ out₀)
    (mem_FP_comp (mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP) fstBlock_mem_FP)
  have heq : ((fstBlock ∘ sndBlock ∘ sndBlock) ∘
        fun z => foldlBits (tkStep STEP EMIT false) (tkStep STEP EMIT true) (Wf z)
          (tkSt (pair [] []) [] cli₀ out₀) (Sf z))
      = fun z => (tkFold STEP EMIT (Wf z) [] cli₀ out₀ (bitsToDigits (Sf z))).2.1 := by
    funext z
    exact tkFold_cli STEP EMIT (Wf z) (Sf z) [] cli₀ out₀
  rwa [heq] at hcomp

/-! ## The token-level model -/

/-- The fold a tokenizing client is really running: one step per token of
`undigitize`, with the token as a number. -/
def natFold (STEPn EMITn : List Bool → ℕ → List Bool) :
    List Bool → List Bool → List ℕ → List Bool × List Bool
  | cli, out, [] => (cli, out)
  | cli, out, t :: ts =>
      natFold STEPn EMITn (STEPn cli t) (out ++ EMITn cli t) ts

/-- Block splitting distributes over an append of digit streams. -/
lemma foldl_blockStep_append : ∀ (ds : List ℕ) (bs : List (List ℕ)) (cur : List ℕ),
    (List.foldl blockStep (bs, cur) ds).1 = bs ++ (List.foldl blockStep ([], cur) ds).1 ∧
      (List.foldl blockStep (bs, cur) ds).2 = (List.foldl blockStep ([], cur) ds).2
  | [], bs, cur => by simp
  | d :: ds, bs, cur => by
      by_cases h : d < 4
      · rw [List.foldl_cons, List.foldl_cons,
          show blockStep (bs, cur) d = (bs, cur ++ [d]) from if_pos h,
          show blockStep (([] : List (List ℕ)), cur) d = ([], cur ++ [d]) from if_pos h]
        exact foldl_blockStep_append ds bs (cur ++ [d])
      · rw [List.foldl_cons, List.foldl_cons,
          show blockStep (bs, cur) d = (bs ++ [cur], []) from if_neg h,
          show blockStep (([] : List (List ℕ)), cur) d = ([cur], []) from if_neg h]
        obtain ⟨h1, h2⟩ := foldl_blockStep_append ds (bs ++ [cur]) []
        obtain ⟨h1', h2'⟩ := foldl_blockStep_append ds [cur] []
        exact ⟨by rw [h1, h1', List.append_assoc], by rw [h2, h2']⟩

/-! ### Reading a concatenation back

A rewriter that splices words together needs to know that the reading `undigitize` performs
distributes over the splice.  It does, provided each piece ends on a block boundary — which
is the discipline every emitter here follows. -/

/-- A run of payload digits splits into no completed block and itself. -/
lemma blockSplit_of_digits_lt_four : ∀ (cur : List ℕ), (∀ d ∈ cur, d < 4) →
    blockSplit cur = ([], cur) := by
  suffices h : ∀ (cur acc : List ℕ), (∀ d ∈ cur, d < 4) →
      List.foldl blockStep (([] : List (List ℕ)), acc) cur = ([], acc ++ cur) by
    intro cur hcur
    have := h cur [] hcur
    simpa [blockSplit] using this
  intro cur
  induction cur with
  | nil => intro acc _; simp
  | cons d ds ih =>
      intro acc hcur
      rw [List.foldl_cons,
        show blockStep (([] : List (List ℕ)), acc) d = ([], acc ++ [d]) from
          if_pos (hcur d (List.mem_cons_self ..)),
        ih (acc ++ [d]) (fun e he => hcur e (List.mem_cons_of_mem _ he)),
        List.append_assoc]
      rfl

/-- A payload run followed by a terminator is one complete block, and `undigitize` reads it
as that block's value. -/
lemma undigitize_run_terminator (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    undigitize (cur ++ [4]) = [digitVal cur] ∧ (blockSplit (cur ++ [4])).2 = [] := by
  have hb : blockSplit (cur ++ [4]) = ([cur], []) := by
    rw [blockSplit_snoc, blockSplit_of_digits_lt_four cur hcur,
      show blockStep (([] : List (List ℕ)), cur) 4 = ([] ++ [cur], []) from if_neg (by omega)]
    rfl
  exact ⟨by rw [undigitize_eq_blockSplit, hb]; rfl, by rw [hb]⟩

/-- Splitting a concatenation whose left part ends on a block boundary. -/
lemma blockSplit_append_of_complete (a b : List ℕ) (ha : (blockSplit a).2 = []) :
    blockSplit (a ++ b) = ((blockSplit a).1 ++ (blockSplit b).1, (blockSplit b).2) := by
  rw [blockSplit, List.foldl_append, ← blockSplit]
  conv_lhs => rw [show blockSplit a = ((blockSplit a).1, (blockSplit a).2) from rfl, ha]
  obtain ⟨h1, h2⟩ := foldl_blockStep_append b (blockSplit a).1 []
  rw [show (List.foldl blockStep ((blockSplit a).1, ([] : List ℕ)) b)
      = ((List.foldl blockStep ((blockSplit a).1, ([] : List ℕ)) b).1,
         (List.foldl blockStep ((blockSplit a).1, ([] : List ℕ)) b).2) from rfl, h1, h2]
  rfl

/-- `undigitize` distributes over a concatenation whose left part ends on a block
boundary. -/
lemma undigitize_append_of_complete (a b : List ℕ) (ha : (blockSplit a).2 = []) :
    undigitize (a ++ b) = undigitize a ++ undigitize b := by
  rw [undigitize_eq_blockSplit, undigitize_eq_blockSplit, undigitize_eq_blockSplit,
    blockSplit_append_of_complete a b ha, List.map_append]

/-- Reading resumes cleanly after a whole number of digit groups. -/
lemma bitsToDigits_append_digitsToBits : ∀ (da : List ℕ), (∀ d ∈ da, d < 8) →
    ∀ b : List Bool, bitsToDigits (digitsToBits da ++ b) = da ++ bitsToDigits b
  | [], _, b => by simp [digitsToBits]
  | d :: da, h, b => by
      rw [digitsToBits_cons, List.append_assoc,
        bitsToDigits_digitBits d (h d (List.mem_cons_self ..)),
        bitsToDigits_append_digitsToBits da
          (fun e he => h e (List.mem_cons_of_mem _ he)) b]
      rfl

/-! ## Testing a token's value against a fixed numeral

A token's value is not determined by its digit block as a *word* — `[1]` and `[1, 0]` are the
same token — so a client cannot decide the value by comparing the block against a constant.
`digitVal_eq_iff_zero_padded` says what it may do instead: check that the block *begins*
with the numeral's canonical digits, which is a constant-word comparison
(`eqConstFn_mem_FP`), and that everything after has value zero, which is the guarded
expansion read at cap one.  Both are `FP`, and together they decide the value exactly.

This is the test a run matcher makes at every token, and the reason it can compare against
numerals too large for a clamp: a `k`-bit value cannot be named by a unary word, but its
digit bits are a constant word. -/

/-- The canonical digit bits of a fixed numeral. -/
def numBits (K : ℕ) : List Bool := digitsToBits (natDigits4 K)

/-- Decide a block's value against a fixed numeral, reading only the block's bits. -/
def NumEqBits (K : ℕ) (w : List Bool) : Prop :=
  w.take (numBits K).length = numBits K ∧
    digitVal (bitsToDigits (w.drop (numBits K).length)) = 0

/-- The test is decidable: it is a conjunction of a prefix equality and a value-zero
check. -/
instance NumEqBits.decidable (K : ℕ) (w : List Bool) : Decidable (NumEqBits K w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **The test decides the value**, on every well-formed block.

Proof kind: `P` proved.  Provenance: (a) `digitVal_eq_iff_zero_padded`, `digitVal_append`;
(b) `bitsToDigits_append_digitsToBits`, `bitsToDigits_digitsToBits`. -/
lemma numEqBits_spec (K : ℕ) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    NumEqBits K (digitsToBits cur) ↔ digitVal cur = K := by
  have hcur8 : ∀ d ∈ cur, d < 8 := fun d hd => lt_trans (hcur d hd) (by norm_num)
  have hK8 : ∀ d ∈ natDigits4 K, d < 8 :=
    fun d hd => lt_trans (natDigits4_lt K d hd) (by norm_num)
  constructor
  · rintro ⟨htake, hzero⟩
    have hsplit : digitsToBits cur
        = numBits K ++ (digitsToBits cur).drop (numBits K).length := by
      conv_lhs => rw [← List.take_append_drop (numBits K).length (digitsToBits cur)]
      rw [htake]
    have hcur' : cur = natDigits4 K
        ++ bitsToDigits ((digitsToBits cur).drop (numBits K).length) := by
      conv_lhs => rw [← bitsToDigits_digitsToBits cur hcur8]
      conv_lhs => rw [hsplit]
      exact bitsToDigits_append_digitsToBits (natDigits4 K) hK8 _
    rw [hcur', digitVal_append, digitVal_natDigits4, hzero]
    omega
  · intro hval
    obtain ⟨m, rfl⟩ := (digitVal_eq_iff_zero_padded cur hcur K).mp hval
    have hbits : digitsToBits (natDigits4 K ++ List.replicate m 0)
        = numBits K ++ digitsToBits (List.replicate m 0) := by
      rw [numBits, digitsToBits_append]
    refine ⟨?_, ?_⟩
    · rw [hbits]
      simp
    · rw [hbits]
      have hdrop : (numBits K ++ digitsToBits (List.replicate m 0)).drop
          (numBits K).length = digitsToBits (List.replicate m 0) := by simp
      rw [hdrop, bitsToDigits_digitsToBits _ (by
        intro d hd
        rw [List.eq_of_mem_replicate hd]
        norm_num), digitVal_replicate_zero]

/-- **Branching on a token's value against a fixed numeral is polynomial time.**

Proof kind: `C` composition.  Provenance: (b) `eqConstFn_mem_FP`, `takeLenFn_mem_FP`,
`dropLenFn_mem_FP`, `LEUnary.unaryOfDigitsLE_le_mem_FP`, `ifEqLen_mem_FP`. -/
lemma ifNumEq_mem_FP {A X Y : List Bool → List Bool} (hA : A ∈ FP) (K : ℕ)
    (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if NumEqBits K (A z) then X z else Y z) ∈ FP := by
  have hcap : (fun _ : List Bool => List.replicate (numBits K).length true) ∈ FP :=
    constFn_mem_FP _
  have htake : (fun z => (A z).take (numBits K).length) ∈ FP := by
    have h := takeLenFn_mem_FP hcap hA
    simpa using h
  have hdrop : (fun z => (A z).drop (numBits K).length) ∈ FP := by
    have h := dropLenFn_mem_FP hcap hA
    simpa using h
  have hclamp := LEUnary.unaryOfDigitsLE_le_mem_FP hdrop (constFn_mem_FP [true])
  have hzero : (fun z =>
      if digitVal (bitsToDigits ((A z).drop (numBits K).length)) = 0 then X z else Y z)
      ∈ FP := by
    have h := ifEqLen_mem_FP hclamp 0 hX hY
    have heq : (fun z => if (List.replicate
          (min (digitVal (bitsToDigits ((A z).drop (numBits K).length)))
            ([true] : List Bool).length) true).length = 0 then X z else Y z)
        = fun z =>
          if digitVal (bitsToDigits ((A z).drop (numBits K).length)) = 0 then X z else Y z := by
      funext z
      simp only [List.length_replicate, List.length_singleton]
      by_cases hv : digitVal (bitsToDigits ((A z).drop (numBits K).length)) = 0
      · rw [if_pos (by omega), if_pos hv]
      · rw [if_neg (by omega), if_neg hv]
    rwa [heq] at h
  have h := eqConstFn_mem_FP (numBits K) htake hzero hY
  have heq : (fun z => if (A z).take (numBits K).length = numBits K then
        (if digitVal (bitsToDigits ((A z).drop (numBits K).length)) = 0 then X z else Y z)
      else Y z)
      = fun z => if NumEqBits K (A z) then X z else Y z := by
    funext z
    simp only [NumEqBits]
    by_cases h1 : (A z).take (numBits K).length = numBits K
    · by_cases h2 : digitVal (bitsToDigits ((A z).drop (numBits K).length)) = 0
      · rw [if_pos h1, if_pos h2, if_pos (And.intro h1 h2)]
      · rw [if_pos h1, if_neg h2, if_neg (fun hc => h2 hc.2)]
    · rw [if_neg h1, if_neg (fun hc => h1 hc.1)]
  rwa [heq] at h

/-! ## Matching a token stream against a fixed list

The run matcher's remaining question is whether a buffered stream *is* one particular fixed
token list.  Block boundaries are data, so this is a fold rather than a comparison — but the
state it needs is only a counter bounded by the target's length, and each step is a single
fixed-numeral test (`ifNumEq_mem_FP`).  This section is that fold's arithmetic, independent
of `FP`; the word-level client is built on it. -/

/-- One step of the prefix matcher: at counter `i`, consume `t` and either advance or fail.
`ts.length + 1` is the absorbing failure value. -/
def mstep (ts : List ℕ) (i t : ℕ) : ℕ :=
  if i < ts.length then (if ts.getD i 0 = t then i + 1 else ts.length + 1)
  else ts.length + 1

@[simp] lemma mstep_fail (ts : List ℕ) (t : ℕ) :
    mstep ts (ts.length + 1) t = ts.length + 1 := by
  rw [mstep, if_neg (by omega)]

/-- Failure is absorbing. -/
lemma foldl_mstep_fail (ts : List ℕ) : ∀ l : List ℕ,
    List.foldl (mstep ts) (ts.length + 1) l = ts.length + 1
  | [] => rfl
  | t :: l => by
      rw [List.foldl_cons, mstep_fail]
      exact foldl_mstep_fail ts l

/-- **The counter reaches the target's length exactly on the remaining target.**

This is the fold-correctness statement the run matcher rests on, and the reason a counter
suffices: a wrong token sends the state to the absorbing failure value, a short stream stops
below the target's length, and a long one overshoots.

Proof kind: `P` proved.  Provenance: (a) `foldl_mstep_fail`. -/
lemma foldl_mstep_iff (ts : List ℕ) : ∀ (l : List ℕ) (i : ℕ), i ≤ ts.length →
    (List.foldl (mstep ts) i l = ts.length ↔ l = ts.drop i)
  | [], i, hi => by
      rw [List.foldl_nil]
      constructor
      · intro h
        rw [h, List.drop_length]
      · intro h
        have hlen := congrArg List.length h
        simp only [List.length_nil, List.length_drop] at hlen
        omega
  | (t :: l), i, hi => by
      rw [List.foldl_cons, mstep]
      by_cases hlt : i < ts.length
      · rw [if_pos hlt]
        have hdrop : ts.drop i = ts.getD i 0 :: ts.drop (i + 1) := by
          rw [List.drop_eq_getElem_cons hlt, List.getD_eq_getElem _ _ hlt]
        by_cases hmatch : ts.getD i 0 = t
        · rw [if_pos hmatch, foldl_mstep_iff ts l (i + 1) (by omega), hdrop, hmatch]
          simp
        · rw [if_neg hmatch, foldl_mstep_fail, hdrop]
          constructor
          · intro h; omega
          · intro h
            exact absurd (List.cons.inj h).1.symm hmatch
      · rw [if_neg hlt, foldl_mstep_fail]
        have hi' : i = ts.length := by omega
        rw [hi', List.drop_length]
        constructor
        · intro h; omega
        · intro h; exact absurd h (by simp)

/-- The matcher, run from the start: the counter ends at the target's length exactly when
the stream is the target. -/
lemma foldl_mstep_zero_iff (ts l : List ℕ) :
    List.foldl (mstep ts) 0 l = ts.length ↔ l = ts := by
  have h := foldl_mstep_iff ts l 0 (Nat.zero_le _)
  rwa [List.drop_zero] at h

/-! ### The matcher as a word-level client

The dispatch is on the counter's length, one level per target token, with a fixed-numeral
test at each.  `ts` is a parameter rather than a literal, so the nest is built by recursion
on it (`matchNest`) rather than written out; that is the only difference from
`CondStep.rcModeW_mem_FP`'s shape. -/

/-- The scalar dispatch nest, mirroring `matchNest` exactly. -/
def mstepAux (fail : ℕ) : List ℕ → ℕ → ℕ → ℕ → ℕ
  | [], _, _, _ => fail
  | (k :: ks), base, i, t =>
      if i = base then (if k = t then base + 1 else fail)
      else mstepAux fail ks (base + 1) i t

/-- The nest computes the indexed lookup it is meant to. -/
lemma mstepAux_spec (fail : ℕ) : ∀ (ks : List ℕ) (base i t : ℕ),
    mstepAux fail ks base i t
      = if base ≤ i ∧ i - base < ks.length then
          (if ks.getD (i - base) 0 = t then i + 1 else fail) else fail
  | [], base, i, t => by rw [mstepAux, if_neg (by simp)]
  | (k :: ks), base, i, t => by
      rw [mstepAux]
      by_cases hib : i = base
      · subst hib
        have hcond : i ≤ i ∧ i - i < (k :: ks).length := ⟨le_refl _, by simp⟩
        rw [if_pos rfl]
        rw [if_pos hcond]
        simp
      · rw [if_neg hib, mstepAux_spec fail ks (base + 1) i t]
        by_cases hle : base ≤ i
        · have hlt : base + 1 ≤ i := by omega
          have hshift : (k :: ks).getD (i - base) 0 = ks.getD (i - (base + 1)) 0 := by
            have hpos : i - base = (i - (base + 1)) + 1 := by omega
            rw [hpos]
            rfl
          by_cases hlen : i - (base + 1) < ks.length
          · have hc1 : base + 1 ≤ i ∧ i - (base + 1) < ks.length := ⟨hlt, hlen⟩
            have hc2 : base ≤ i ∧ i - base < (k :: ks).length := by
              refine ⟨hle, ?_⟩
              simp only [List.length_cons]
              omega
            rw [if_pos hc1, if_pos hc2, hshift]
          · have hn1 : ¬(base + 1 ≤ i ∧ i - (base + 1) < ks.length) := by
              rintro ⟨-, h⟩; exact hlen h
            have hn2 : ¬(base ≤ i ∧ i - base < (k :: ks).length) := by
              rintro ⟨-, h⟩
              simp only [List.length_cons] at h
              omega
            rw [if_neg hn1, if_neg hn2]
        · have hn1 : ¬(base + 1 ≤ i ∧ i - (base + 1) < ks.length) := by
            rintro ⟨h, -⟩; omega
          have hn2 : ¬(base ≤ i ∧ i - base < (k :: ks).length) := by
            rintro ⟨h, -⟩; omega
          rw [if_neg hn1, if_neg hn2]

/-- At base zero the nest is `mstep`. -/
lemma mstepAux_zero (ts : List ℕ) (i t : ℕ) :
    mstepAux (ts.length + 1) ts 0 i t = mstep ts i t := by
  rw [mstepAux_spec, mstep]
  by_cases h : i < ts.length
  · rw [if_pos ⟨Nat.zero_le _, by omega⟩, if_pos h]
    simp
  · rw [if_neg (by omega), if_neg h]

/-- The word-level dispatch nest. -/
def matchNest (fail : ℕ) : List ℕ → ℕ → List Bool → List Bool → List Bool
  | [], _, _, _ => List.replicate fail true
  | (k :: ks), base, cli, tok =>
      if cli.length = base then
        (if NumEqBits k tok then List.replicate (base + 1) true
         else List.replicate fail true)
      else matchNest fail ks (base + 1) cli tok

lemma length_matchNest (fail : ℕ) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    ∀ (ks : List ℕ) (base : ℕ) (cli : List Bool),
      (matchNest fail ks base cli (digitsToBits cur)).length
        = mstepAux fail ks base cli.length (digitVal cur)
  | [], base, cli => by rw [matchNest, mstepAux, List.length_replicate]
  | (k :: ks), base, cli => by
      rw [matchNest, mstepAux]
      by_cases hb : cli.length = base
      · rw [if_pos hb, if_pos hb]
        by_cases hm : NumEqBits k (digitsToBits cur)
        · rw [if_pos hm, if_pos ((numEqBits_spec k cur hcur).mp hm).symm,
            List.length_replicate]
        · rw [if_neg hm,
            if_neg (fun hc => hm ((numEqBits_spec k cur hcur).mpr hc.symm)),
            List.length_replicate]
      · rw [if_neg hb, if_neg hb]
        exact length_matchNest fail cur hcur ks (base + 1) cli

lemma length_matchNest_le (fail : ℕ) : ∀ (ks : List ℕ) (base : ℕ) (cli tok : List Bool),
    base + ks.length ≤ fail → (matchNest fail ks base cli tok).length ≤ fail
  | [], base, cli, tok, _ => by rw [matchNest, List.length_replicate]
  | (k :: ks), base, cli, tok, hb => by
      rw [matchNest]
      split_ifs
      · rw [List.length_replicate]; simp at hb; omega
      · rw [List.length_replicate]
      · exact length_matchNest_le fail ks (base + 1) cli tok (by simp at hb; omega)

lemma matchNest_mem_FP (fail : ℕ) : ∀ (ks : List ℕ) (base : ℕ)
    {C T : List Bool → List Bool}, C ∈ FP → T ∈ FP →
    (fun z => matchNest fail ks base (C z) (T z)) ∈ FP
  | [], base, C, T, _, _ => constFn_mem_FP _
  | (k :: ks), base, C, T, hC, hT => by
      have hrec := matchNest_mem_FP fail ks (base + 1) hC hT
      have hleaf : (fun z => if NumEqBits k (T z) then
            List.replicate (base + 1) true else List.replicate fail true) ∈ FP :=
        ifNumEq_mem_FP hT k (constFn_mem_FP _) (constFn_mem_FP _)
      exact ifEqLen_mem_FP hC base hleaf hrec

/-! ### Block-complete words

A rewriter splices words; `decodeBits` is how the machine's reader sees the splice, and
`BlockWF` is the discipline — every piece a whole number of complete blocks — under which
the splice decodes piecewise.  Both the buffered run and every emitted fragment keep it. -/

/-- The token stream a word carries, as `MachineEfficientTrader` reads it. -/
def decodeBits (w : List Bool) : List ℕ := undigitize (bitsToDigits w)

/-- The word carries a whole number of complete digit blocks. -/
def BlockWF (w : List Bool) : Prop :=
  ∃ ds : List ℕ, w = digitsToBits ds ∧ (∀ d ∈ ds, d < 8) ∧ (blockSplit ds).2 = []

lemma BlockWF.nil : BlockWF [] := ⟨[], rfl, by simp, by simp [blockSplit]⟩

lemma BlockWF.append {a b : List Bool} (ha : BlockWF a) (hb : BlockWF b) :
    BlockWF (a ++ b) := by
  obtain ⟨da, rfl, ha8, hac⟩ := ha
  obtain ⟨db, rfl, hb8, hbc⟩ := hb
  refine ⟨da ++ db, (digitsToBits_append da db).symm, ?_, ?_⟩
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ha8 d hd
    · exact hb8 d hd
  · rw [blockSplit_append_of_complete da db hac, hbc]

lemma decodeBits_append {a b : List Bool} (ha : BlockWF a) (hb : BlockWF b) :
    decodeBits (a ++ b) = decodeBits a ++ decodeBits b := by
  obtain ⟨da, rfl, ha8, hac⟩ := ha
  obtain ⟨db, rfl, hb8, -⟩ := hb
  rw [decodeBits, decodeBits, decodeBits, ← digitsToBits_append,
    bitsToDigits_digitsToBits (da ++ db) (by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact ha8 d hd
      · exact hb8 d hd),
    bitsToDigits_digitsToBits da ha8, bitsToDigits_digitsToBits db hb8,
    undigitize_append_of_complete da db hac]

@[simp] lemma decodeBits_nil : decodeBits [] = [] := by
  rw [decodeBits, bitsToDigits_of_length_lt_three [] (by simp)]
  simp [undigitize]

/-- A payload run with its terminator: one complete block, carrying its own value. -/
lemma blockWF_run (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    BlockWF (digitsToBits cur ++ digitBits 4) := by
  refine ⟨cur ++ [4], ?_, ?_, (undigitize_run_terminator cur hcur).2⟩
  · rw [digitsToBits_append]; rfl
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact lt_trans (hcur d hd) (by norm_num)
    · simp at hd; omega

lemma decodeBits_run (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    decodeBits (digitsToBits cur ++ digitBits 4) = [digitVal cur] := by
  have hterm : bitsToDigits (digitBits 4) = [4] := by
    have h4 := bitsToDigits_digitBits 4 (by norm_num) []
    rw [List.append_nil] at h4
    rw [h4]; rfl
  rw [decodeBits, bitsToDigits_append_digitsToBits cur
      (fun d hd => lt_trans (hcur d hd) (by norm_num)), hterm,
    (undigitize_run_terminator cur hcur).1]

/-! ### Constant token words

A fixed token list — the emitter's syntactic scaffolding — is a constant word, and needs no
numeral to be evaluated: the round-trip goes through `undigitize_digitize`. -/

/-- A fixed token list, rendered as constant digit bits. -/
def tokBits (ts : List ℕ) : List Bool := digitsToBits (digitize ts)

lemma mem_digitize_lt_eight (ts : List ℕ) : ∀ d ∈ digitize ts, d < 8 := by
  intro d hd
  rw [digitize, List.mem_flatMap] at hd
  obtain ⟨t, -, hd⟩ := hd
  rw [tokenBlock, List.mem_append] at hd
  rcases hd with hd | hd
  · exact lt_trans (natDigits4_lt t d hd) (by norm_num)
  · simp at hd; omega

lemma blockSplit_digitize (ts : List ℕ) : (blockSplit (digitize ts)).2 = [] := by
  induction ts with
  | nil => simp [digitize, blockSplit]
  | cons t ts ih =>
      rw [digitize, List.flatMap_cons, ← digitize, tokenBlock,
        blockSplit_append_of_complete _ _ (undigitize_run_terminator _ (natDigits4_lt t)).2,
        ih]

lemma blockWF_tokBits (ts : List ℕ) : BlockWF (tokBits ts) :=
  ⟨digitize ts, rfl, mem_digitize_lt_eight ts, blockSplit_digitize ts⟩

@[simp] lemma decodeBits_tokBits (ts : List ℕ) : decodeBits (tokBits ts) = ts := by
  rw [decodeBits, tokBits, bitsToDigits_digitsToBits _ (mem_digitize_lt_eight ts),
    undigitize_digitize]

/-! ## Unary numerals and emitted values

A value the machine knows only as a *length* — a counter, a product of counters — reaches
the stream as one complete token block.  `unaryBlock` is that emission, and `uMul` is the
one arithmetic operation on lengths that is not just `++`. -/

/-- The product of two unary numerals.  `Cobham.mulLenFn_mem_FP` emits `false` marks; the
content is irrelevant, the length is the number. -/
def uMul (a b : List Bool) : List Bool := List.replicate (a.length * b.length) false

@[simp] lemma length_uMul (a b : List Bool) : (uMul a b).length = a.length * b.length := by
  simp [uMul]

lemma uMul_mem_FP {A B : List Bool → List Bool} (hA : A ∈ FP) (hB : B ∈ FP) :
    (fun z => uMul (A z) (B z)) ∈ FP := mulLenFn_mem_FP hA hB

/-- A value known as a length, emitted as one complete token block. -/
def unaryBlock (u : List Bool) : List Bool := Increment.unaryToDigits u ++ digitBits 4

lemma unaryBlock_mem_FP {U : List Bool → List Bool} (hU : U ∈ FP) :
    (fun z => unaryBlock (U z)) ∈ FP :=
  appendFn_mem_FP (Increment.unaryToDigits_mem_FP hU) (constFn_mem_FP (digitBits 4))

lemma blockWF_unaryBlock (u : List Bool) : BlockWF (unaryBlock u) := by
  rw [unaryBlock, Increment.unaryToDigits_eq]
  exact blockWF_run _ (Increment.unaryDigits_lt u.length)

/-- The emitted block is logarithmic in the value, hence certainly linear in the unary
word it came from. -/
lemma length_unaryBlock_le (u : List Bool) : (unaryBlock u).length ≤ 3 * u.length + 3 := by
  rw [unaryBlock, List.length_append, length_digitBits, Increment.unaryToDigits_eq,
    length_digitsToBits]
  have := Increment.unaryDigits_length u.length
  omega

@[simp] lemma decodeBits_unaryBlock (u : List Bool) :
    decodeBits (unaryBlock u) = [u.length] := by
  rw [unaryBlock, Increment.unaryToDigits_eq, decodeBits_run _ (Increment.unaryDigits_lt u.length),
    Increment.unaryDigits_val]

/-- The fold at the granularity the tokenizer actually delivers: one step per *block*
`undigitize` reads, with the block as its digit run.  `natFold` is this with `digitVal`
applied; a client that must copy a token's digits rather than only read its value — a
buffering rewriter, say — needs this one, because a raw stream may carry a non-canonical
run and the copy is then not a function of the value. -/
def runFold (STEPr EMITr : List Bool → List ℕ → List Bool) :
    List Bool → List Bool → List (List ℕ) → List Bool × List Bool
  | cli, out, [] => (cli, out)
  | cli, out, r :: rs => runFold STEPr EMITr (STEPr cli r) (out ++ EMITr cli r) rs

/-- **The tokenizer realizes the block-level fold.**

The hypotheses are demanded only at *well-formed* token blocks — words of the form
`digitsToBits cur` with `cur` a run of digits below four — which is all the tokenizer ever
builds, and is what makes them satisfiable by definition: a client defines `STEPr cli cur`
to be whatever its word step computes at `digitsToBits cur`.

Proof kind: `P` proved.  Provenance: (a) `tkFold`, `foldl_blockStep_append`. -/
lemma tkFold_runFold {STEP EMIT : List Bool → List Bool}
    {STEPr EMITr : List Bool → List ℕ → List Bool} (W : List Bool)
    (hS : ∀ (cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      STEP (pair W (pair cli (digitsToBits cur))) = STEPr cli cur)
    (hE : ∀ (cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      EMIT (pair W (pair cli (digitsToBits cur))) = EMITr cli cur) :
    ∀ (ds cur : List ℕ) (cli out : List Bool), (∀ d ∈ cur, d < 4) →
      (tkFold STEP EMIT W (digitsToBits cur) cli out ds).2.1
          = (runFold STEPr EMITr cli out (List.foldl blockStep ([], cur) ds).1).1 ∧
      (tkFold STEP EMIT W (digitsToBits cur) cli out ds).2.2
        = (runFold STEPr EMITr cli out (List.foldl blockStep ([], cur) ds).1).2
  | [], cur, cli, out, _ => by simp [tkFold, runFold]
  | d :: ds, cur, cli, out, hcur => by
      rw [tkFold, List.foldl_cons]
      by_cases h : d < 4
      · rw [if_pos h, show blockStep (([] : List (List ℕ)), cur) d = ([], cur ++ [d])
              from if_pos h,
          show digitsToBits cur ++ digitBits d = digitsToBits (cur ++ [d]) by
            rw [digitsToBits_append]; rfl]
        exact tkFold_runFold W hS hE ds (cur ++ [d]) cli out (by
          intro e he
          rcases List.mem_append.mp he with he | he
          · exact hcur e he
          · simp at he; omega)
      · rw [if_neg h, show blockStep (([] : List (List ℕ)), cur) d = ([cur], [])
              from if_neg h,
          hS cli cur hcur, hE cli cur hcur,
          (foldl_blockStep_append ds [cur] []).1]
        rw [show ([cur] ++ (List.foldl blockStep ([], []) ds).1)
            = cur :: (List.foldl blockStep ([], []) ds).1 from rfl, runFold]
        exact tkFold_runFold W hS hE ds [] _ _ (by simp)

/-- The block-level fold read against `blockSplit`: what the tokenizer computes on a digit
stream — both its final client state and its output — is what the block-level fold computes
on the blocks that stream splits into. -/
lemma tkFold_blockSplit_cli_out {STEP EMIT : List Bool → List Bool}
    {STEPr EMITr : List Bool → List ℕ → List Bool} (W : List Bool)
    (hS : ∀ (cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      STEP (pair W (pair cli (digitsToBits cur))) = STEPr cli cur)
    (hE : ∀ (cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      EMIT (pair W (pair cli (digitsToBits cur))) = EMITr cli cur)
    (ds : List ℕ) (cli out : List Bool) :
    (tkFold STEP EMIT W [] cli out ds).2.1
        = (runFold STEPr EMITr cli out (blockSplit ds).1).1 ∧
    (tkFold STEP EMIT W [] cli out ds).2.2
      = (runFold STEPr EMITr cli out (blockSplit ds).1).2 := by
  have h := tkFold_runFold W hS hE ds [] cli out (by simp)
  rw [show (digitsToBits [] : List Bool) = [] from rfl] at h
  rw [blockSplit]
  exact h

/-- The digit-level fold, re-read one *block* at a time: `runFold` over the blocks
`blockSplit` cuts the stream into agrees with `tkFold` over its digits. -/
lemma tkFold_blockSplit {STEP EMIT : List Bool → List Bool}
    {STEPr EMITr : List Bool → List ℕ → List Bool} (W : List Bool)
    (hS : ∀ (cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      STEP (pair W (pair cli (digitsToBits cur))) = STEPr cli cur)
    (hE : ∀ (cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      EMIT (pair W (pair cli (digitsToBits cur))) = EMITr cli cur)
    (ds : List ℕ) (cli out : List Bool) :
    (tkFold STEP EMIT W [] cli out ds).2.2
      = (runFold STEPr EMITr cli out (blockSplit ds).1).2 :=
  (tkFold_blockSplit_cli_out W hS hE ds cli out).2

/-- The value-level fold is the block-level fold composed with `digitVal`. -/
lemma runFold_natFold (STEPn EMITn : List Bool → ℕ → List Bool) :
    ∀ (rs : List (List ℕ)) (cli out : List Bool),
      runFold (fun cli r => STEPn cli (digitVal r)) (fun cli r => EMITn cli (digitVal r))
          cli out rs
        = natFold STEPn EMITn cli out (rs.map digitVal)
  | [], cli, out => rfl
  | r :: rs, cli, out => by
      rw [runFold, List.map_cons, natFold, runFold_natFold STEPn EMITn rs]

/-- The same, read against `undigitize`: what the tokenizer emits on a digit stream is what
the token-level fold emits on the tokens that stream denotes. -/
lemma tkFold_undigitize {STEP EMIT : List Bool → List Bool}
    {STEPn EMITn : List Bool → ℕ → List Bool} (W : List Bool)
    (hS : ∀ (cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      STEP (pair W (pair cli (digitsToBits cur))) = STEPn cli (digitVal cur))
    (hE : ∀ (cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      EMIT (pair W (pair cli (digitsToBits cur))) = EMITn cli (digitVal cur))
    (ds : List ℕ) (cli out : List Bool) :
    (tkFold STEP EMIT W [] cli out ds).2.2
      = (natFold STEPn EMITn cli out (undigitize ds)).2 := by
  rw [tkFold_blockSplit (STEPr := fun cli r => STEPn cli (digitVal r))
      (EMITr := fun cli r => EMITn cli (digitVal r)) W hS hE ds cli out,
    runFold_natFold, undigitize_eq_blockSplit]

/-- **The client interface, at block granularity.**  A step and an emitter that read each
token block, with the two per-step length bounds, compute the block-level fold in
polynomial time — over exactly the blocks `MachineEfficientTrader`'s decoding splits its
input into.

Proof kind: `C` composition.  Provenance: (a) `tkFold_mem_FP`, `tkFold_blockSplit`. -/
lemma runFold_mem_FP {STEP EMIT Wf Sf : List Bool → List Bool}
    {STEPr EMITr : List Bool → List Bool → List ℕ → List Bool} {c k : ℕ}
    {qQ : Polynomial ℕ}
    (hSTEP : STEP ∈ FP) (hEMIT : EMIT ∈ FP) (hW : Wf ∈ FP) (hSf : Sf ∈ FP)
    (hSbnd : ∀ W cli tok : List Bool,
      (STEP (pair W (pair cli tok))).length ≤ cli.length + tok.length + c)
    (hEbnd : ∀ W cli tok : List Bool,
      (EMIT (pair W (pair cli tok))).length
        ≤ qQ.eval W.length + k * (cli.length + tok.length))
    (hS : ∀ (W cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      STEP (pair W (pair cli (digitsToBits cur))) = STEPr W cli cur)
    (hE : ∀ (W cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      EMIT (pair W (pair cli (digitsToBits cur))) = EMITr W cli cur)
    (cli₀ out₀ : List Bool) :
    (fun z => (runFold (STEPr (Wf z)) (EMITr (Wf z)) cli₀ out₀
      (blockSplit (bitsToDigits (Sf z))).1).2) ∈ FP := by
  have h := tkFold_mem_FP hSTEP hEMIT hW hSf hSbnd hEbnd cli₀ out₀
  have heq : (fun z => (tkFold STEP EMIT (Wf z) [] cli₀ out₀ (bitsToDigits (Sf z))).2.2)
      = fun z => (runFold (STEPr (Wf z)) (EMITr (Wf z)) cli₀ out₀
          (blockSplit (bitsToDigits (Sf z))).1).2 := by
    funext z
    exact tkFold_blockSplit (Wf z) (fun cli cur h => hS (Wf z) cli cur h)
      (fun cli cur h => hE (Wf z) cli cur h) _ cli₀ out₀
  rwa [heq] at h

/-- **The client interface, for a value.**  The same, projecting the fold's final client
state rather than its output — what an acceptance test or an end-read counter needs.

Proof kind: `C` composition.  Provenance: (a) `tkFold_cli_mem_FP`,
`tkFold_blockSplit_cli_out`. -/
lemma runFold_cli_mem_FP {STEP EMIT Wf Sf : List Bool → List Bool}
    {STEPr EMITr : List Bool → List Bool → List ℕ → List Bool} {c k : ℕ}
    {qQ : Polynomial ℕ}
    (hSTEP : STEP ∈ FP) (hEMIT : EMIT ∈ FP) (hW : Wf ∈ FP) (hSf : Sf ∈ FP)
    (hSbnd : ∀ W cli tok : List Bool,
      (STEP (pair W (pair cli tok))).length ≤ cli.length + tok.length + c)
    (hEbnd : ∀ W cli tok : List Bool,
      (EMIT (pair W (pair cli tok))).length
        ≤ qQ.eval W.length + k * (cli.length + tok.length))
    (hS : ∀ (W cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      STEP (pair W (pair cli (digitsToBits cur))) = STEPr W cli cur)
    (hE : ∀ (W cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      EMIT (pair W (pair cli (digitsToBits cur))) = EMITr W cli cur)
    (cli₀ out₀ : List Bool) :
    (fun z => (runFold (STEPr (Wf z)) (EMITr (Wf z)) cli₀ out₀
      (blockSplit (bitsToDigits (Sf z))).1).1) ∈ FP := by
  have h := tkFold_cli_mem_FP hSTEP hEMIT hW hSf hSbnd hEbnd cli₀ out₀
  have heq : (fun z => (tkFold STEP EMIT (Wf z) [] cli₀ out₀ (bitsToDigits (Sf z))).2.1)
      = fun z => (runFold (STEPr (Wf z)) (EMITr (Wf z)) cli₀ out₀
          (blockSplit (bitsToDigits (Sf z))).1).1 := by
    funext z
    exact (tkFold_blockSplit_cli_out (Wf z) (fun cli cur h => hS (Wf z) cli cur h)
      (fun cli cur h => hE (Wf z) cli cur h) _ cli₀ out₀).1
  rwa [heq] at h

/-- **The client interface.**  A step and an emitter that read each token by the value
`undigitize` gives it, with the two per-step length bounds, compute the token-level fold in
polynomial time — over exactly the token stream `MachineEfficientTrader` decodes.

Proof kind: `C` composition.  Provenance: (a) `runFold_mem_FP`, `runFold_natFold`. -/
lemma natFold_mem_FP {STEP EMIT Wf Sf : List Bool → List Bool}
    {STEPn EMITn : List Bool → ℕ → List Bool} {c k : ℕ} {qQ : Polynomial ℕ}
    (hSTEP : STEP ∈ FP) (hEMIT : EMIT ∈ FP) (hW : Wf ∈ FP) (hSf : Sf ∈ FP)
    (hSbnd : ∀ W cli tok : List Bool,
      (STEP (pair W (pair cli tok))).length ≤ cli.length + tok.length + c)
    (hEbnd : ∀ W cli tok : List Bool,
      (EMIT (pair W (pair cli tok))).length
        ≤ qQ.eval W.length + k * (cli.length + tok.length))
    (hS : ∀ (W cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      STEP (pair W (pair cli (digitsToBits cur))) = STEPn cli (digitVal cur))
    (hE : ∀ (W cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      EMIT (pair W (pair cli (digitsToBits cur))) = EMITn cli (digitVal cur))
    (cli₀ out₀ : List Bool) :
    (fun z => (natFold STEPn EMITn cli₀ out₀
      (undigitize (bitsToDigits (Sf z)))).2) ∈ FP := by
  have h := runFold_mem_FP (STEPr := fun _ cli r => STEPn cli (digitVal r))
    (EMITr := fun _ cli r => EMITn cli (digitVal r))
    hSTEP hEMIT hW hSf hSbnd hEbnd hS hE cli₀ out₀
  have heq : (fun z => (runFold (fun cli r => STEPn cli (digitVal r))
        (fun cli r => EMITn cli (digitVal r)) cli₀ out₀
        (blockSplit (bitsToDigits (Sf z))).1).2)
      = fun z => (natFold STEPn EMITn cli₀ out₀ (undigitize (bitsToDigits (Sf z)))).2 := by
    funext z
    rw [runFold_natFold, undigitize_eq_blockSplit]
  rwa [heq] at h

/-! ## Deciding a token stream against a fixed list, in `FP`

The pieces fit: `matchNest` is the step, `foldl_mstep_zero_iff` is its correctness, and
`runFold_cli_mem_FP` runs it over exactly the blocks `MachineEfficientTrader`'s decoding
splits its input into.  `ifMatch_mem_FP` is the consumer-facing form — branch on whether a
word's token stream *is* one particular fixed list — and it is what a run matcher calls once
per candidate spelling. -/

-- The matcher client's state and the token block it is handed.
private def mvCli (v : List Bool) : List Bool := fstBlock (sndBlock v)
private def mvTok (v : List Bool) : List Bool := sndBlock (sndBlock v)

/-- The matcher's word-level step. -/
def matchStepW (ts : List ℕ) (v : List Bool) : List Bool :=
  matchNest (ts.length + 1) ts 0 (mvCli v) (mvTok v)

/-- Its block-level reading. -/
def matchStepR (ts : List ℕ) (cli : List Bool) (cur : List ℕ) : List Bool :=
  matchNest (ts.length + 1) ts 0 cli (digitsToBits cur)

lemma matchStepW_eq (ts : List ℕ) (W cli : List Bool) (cur : List ℕ) :
    matchStepW ts (pair W (pair cli (digitsToBits cur))) = matchStepR ts cli cur := by
  rw [matchStepW, matchStepR]
  simp only [mvCli, mvTok, sndBlock_pair, fstBlock_pair]

/-- Every state the nest produces is a unary word. -/
lemma matchNest_replicate (fail : ℕ) : ∀ (ks : List ℕ) (base : ℕ) (cli tok : List Bool),
    matchNest fail ks base cli tok
      = List.replicate (matchNest fail ks base cli tok).length true
  | [], base, cli, tok => by rw [matchNest]; simp
  | (k :: ks), base, cli, tok => by
      rw [matchNest]
      split_ifs
      · simp
      · simp
      · exact matchNest_replicate fail ks (base + 1) cli tok

lemma matchStepR_replicate (ts : List ℕ) (i : ℕ) (cur : List ℕ)
    (hcur : ∀ d ∈ cur, d < 4) :
    matchStepR ts (List.replicate i true) cur
      = List.replicate (mstep ts i (digitVal cur)) true := by
  rw [matchStepR, matchNest_replicate,
    length_matchNest (ts.length + 1) cur hcur ts 0 (List.replicate i true),
    List.length_replicate, mstepAux_zero]

lemma matchStepW_mem_FP (ts : List ℕ) : matchStepW ts ∈ FP := by
  have hcli : mvCli ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have htok : mvTok ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
  exact matchNest_mem_FP (ts.length + 1) ts 0 hcli htok

lemma matchStepW_length_le (ts : List ℕ) (W cli tok : List Bool) :
    (matchStepW ts (pair W (pair cli tok))).length ≤ cli.length + tok.length
      + (ts.length + 1) := by
  have h := length_matchNest_le (ts.length + 1) ts 0 (mvCli (pair W (pair cli tok)))
    (mvTok (pair W (pair cli tok))) (by omega)
  rw [matchStepW]
  omega

/-- **The fold's client state is the matcher's counter.** -/
lemma matchFold_cli (ts : List ℕ) : ∀ (rs : List (List ℕ)) (i : ℕ) (out : List Bool),
    (∀ r ∈ rs, ∀ d ∈ r, d < 4) →
    (runFold (matchStepR ts) (fun _ _ => []) (List.replicate i true) out rs).1
      = List.replicate (List.foldl (mstep ts) i (rs.map digitVal)) true
  | [], i, out, _ => by simp [runFold]
  | (r :: rs), i, out, hrs => by
      have hr : ∀ d ∈ r, d < 4 := hrs r (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rs, ∀ d ∈ q, d < 4 :=
        fun q hq => hrs q (List.mem_cons_of_mem _ hq)
      rw [runFold, matchStepR_replicate ts i r hr,
        matchFold_cli ts rs (mstep ts i (digitVal r)) _ hrest, List.map_cons,
        List.foldl_cons]

/-- The matcher, run over a word's blocks. -/
def matchPass (ts : List ℕ) (w : List Bool) : List Bool :=
  (runFold (matchStepR ts) (fun _ _ => []) [] [] (blockSplit (bitsToDigits w)).1).1

/-- **The pass decides the question**: the counter reaches the target's length exactly when
the word's token stream is the target.

Proof kind: `C` composition.  Provenance: (a) `matchFold_cli`, `foldl_mstep_zero_iff`;
(b) `undigitize_eq_blockSplit`. -/
lemma matchPass_iff (ts : List ℕ) (w : List Bool) :
    (matchPass ts w).length = ts.length ↔ decodeBits w = ts := by
  have h := matchFold_cli ts (blockSplit (bitsToDigits w)).1 0 []
    (fun r hr => (blockSplit_digits_lt (bitsToDigits w)).1 r hr)
  rw [show (List.replicate 0 true : List Bool) = [] from rfl] at h
  simp only [matchPass]
  rw [h, List.length_replicate, foldl_mstep_zero_iff, decodeBits,
    undigitize_eq_blockSplit]

lemma matchPass_mem_FP (ts : List ℕ) {Sf : List Bool → List Bool} (hSf : Sf ∈ FP) :
    (fun z => matchPass ts (Sf z)) ∈ FP :=
  runFold_cli_mem_FP (STEPr := fun _ => matchStepR ts) (EMITr := fun _ _ _ => [])
    (c := ts.length + 1) (k := 0) (qQ := 0)
    (matchStepW_mem_FP ts) (constFn_mem_FP []) (constFn_mem_FP []) hSf
    (matchStepW_length_le ts) (fun _ _ _ => by simp)
    (fun W cli cur _ => matchStepW_eq ts W cli cur) (fun _ _ _ _ => rfl) [] []

/-- **Branching on "this word's token stream is exactly `ts`" is polynomial time.**

Proof kind: `C` composition.  Provenance: (a) `matchPass_iff`, `matchPass_mem_FP`;
(b) `ifEqLen_mem_FP`. -/
lemma ifMatch_mem_FP (ts : List ℕ) {A X Y : List Bool → List Bool} (hA : A ∈ FP)
    (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if decodeBits (A z) = ts then X z else Y z) ∈ FP := by
  have h := ifEqLen_mem_FP (matchPass_mem_FP ts hA) ts.length hX hY
  have heq : (fun z => if (matchPass ts (A z)).length = ts.length then X z else Y z)
      = fun z => if decodeBits (A z) = ts then X z else Y z := by
    funext z
    by_cases hm : decodeBits (A z) = ts
    · rw [if_pos ((matchPass_iff ts (A z)).mpr hm), if_pos hm]
    · rw [if_neg (fun hc => hm ((matchPass_iff ts (A z)).mp hc)), if_neg hm]
  rwa [heq] at h

end LogicalInduction.TokenFold
