import LogicalInduction.Framework.Machine.FPFold
import LogicalInduction.Framework.Emission.DigitArith
import Complexitylib.Classes.P.Cobham

/-!
# Tokenizing transductions in `Complexity.FP`

`EfficientlyComputable` (`Framework/Criterion.lean`) reads a machine's output word as a
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

* **`concatUnaryPair_mem_FP`** — the last section: a *variable-count* concatenation, `cnt n`
  segments emitted by one `FP` family at the paired indices `⟨n, j⟩`, with the outer index `n`
  a parameter rather than the input word's own length.  It is the fold client the machine
  reading of a splicing emitter needs, and the reason `unaryPair_mem_FP` exists;
  `BlockWF.flatMap` and `undigitize_flatMap_complete` are its pure-list halves.  It is also
  what `UnaryRuler.segPrefix` and `.segLocate` (`Framework/Machine/Ruler.lean`) run — the same
  fold at a ruler instead of at a stream — which is why the outer index is a parameter: those
  clients hold `n` as a ruler, not as the input.

## Three client granularities

`tkFold` (one digit) → `runFold` (one block, `tkFold_blockSplit`) → `natFold` (one token
value, `runFold_natFold`), each with an `FP` closure lemma and an `_cli` variant for a client
computing a value rather than a stream. `BlockWF` and `decodeBits` are the splice discipline
— every piece a whole number of complete blocks — under which the machine's reading
distributes over a concatenation. Deciding a *property* of the decoded stream is not stated
here: the device for it is `BlockAutomaton` (`Construction/Freeze/RunAutomaton.lean`), built
on `runFold_cli_mem_FP`.

## Why the client sees bits, not numbers

The client receives each token as its raw digit-bit block rather than as a number, which is
deliberate: an arbitrary machine word may carry a *non-canonical* run (`[1, 0]` and `[1]` are
both the token `1`), so a client that compared blocks against constant words would be wrong
on inputs `undigitize` reads identically. The supported reads are `LEUnary`'s clamp, whose
guard makes the value a length, and the fixed-numeral test `ifNumEq_mem_FP`, justified by
`digitVal_eq_iff_zero_padded` (`Framework/Emission/DigitArith.lean`, with the rest of the
base-four numeral arithmetic). Every test the conditioning and freeze automata make is a
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

The value a digit run denotes is `Framework/Emission/DigitArith.lean`'s `digitVal`, the same
little-endian base-four reading `undigitize` performs; nothing new is defined here.  What
is new is `digitSlots`, the shape a *client* of the digit fold below can branch on.

Proof kind: `P` throughout.  Provenance: (b) `Machine/DigitBits.lean`,
`Framework/Emission/DigitArith.lean`. -/

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

/-- A constant one-element emission per element is a replicate.  The shape every
"one mark per token" client reads its own output in; Mathlib has no such lemma
(`List.eq_replicate_length` is the membership form). -/
lemma flatMap_const_singleton {α β : Type*} (a : β) : ∀ l : List α,
    (l.flatMap fun _ => [a]) = List.replicate l.length a
  | [] => rfl
  | _ :: l => by
      rw [List.flatMap_cons, flatMap_const_singleton a l, List.length_cons,
        List.replicate_succ]
      rfl

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

/-! ### The three-block packing

The argument word every automaton below is folded over is `pair W (pair cli tok)`: the
guard word, the client's own state, and the incoming token block.  `fstBlock` reads the
first component; these two read the other two. -/

/-- The middle component of a word packed as `pair W (pair cli tok)`. -/
def midBlock (v : List Bool) : List Bool := fstBlock (sndBlock v)

/-- The last component of a word packed as `pair W (pair cli tok)`. -/
def lastBlock (v : List Bool) : List Bool := sndBlock (sndBlock v)

lemma midBlock_pair (W cli tok : List Bool) :
    midBlock (pair W (pair cli tok)) = cli := by
  rw [midBlock, sndBlock_pair, fstBlock_pair]

lemma lastBlock_pair (W cli tok : List Bool) :
    lastBlock (pair W (pair cli tok)) = tok := by
  rw [lastBlock, sndBlock_pair, sndBlock_pair]

lemma midBlock_mem_FP : midBlock ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP

lemma lastBlock_mem_FP : lastBlock ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP

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

-- The digit step's argument is `pair W (dgSt (pair p0 p1) cli)`; `midBlock` is the phase
-- and `lastBlock` the client state, and these read the guard word and the two phase slots.
private def dW (v : List Bool) : List Bool := fstBlock v
private def dp0 (v : List Bool) : List Bool := fstBlock (midBlock v)
private def dp1 (v : List Bool) : List Bool := sndBlock (midBlock v)

/-- One bit of a three-bit digit fold: two slots fill, the third completes the digit and
hands the client its three bits. -/
def dgStep (STEP : List Bool → List Bool) (b : Bool) (v : List Bool) : List Bool :=
  selectHead (emptyFlag (dp0 v))
    (dgSt (pair [b] []) (lastBlock v))
    (selectHead (emptyFlag (dp1 v))
      (dgSt (pair (dp0 v) [b]) (lastBlock v))
      (dgSt (pair [] [])
        (STEP (pair (dW v) (pair (lastBlock v) (pair (dp0 v) (pair (dp1 v) [b])))))))

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
    simp [foldlBits, dgStep, dgSt, dW, midBlock, dp0, dp1, lastBlock,
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
        simp [dgStep, dgSt, dW, midBlock, dp0, dp1, lastBlock, selectHead_true]
  | [b0, b1], cli => by
      rw [bitsToDigits_of_length_lt_three [b0, b1] (by simp), dgFold,
        show ([b0, b1] : List Bool) = [b0] ++ [b1] from rfl,
        foldlBits_append_singleton]
      cases b0 <;> cases b1 <;>
        simp [foldlBits, dgStep, dgSt, dW, midBlock, dp0, dp1, lastBlock,
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
      simp [dgStep, dgSt, dW, midBlock, dp0, dp1, lastBlock, selectHead_true]
  | [x], _ =>
      match p1, h1 with
      | [], _ =>
          refine ⟨[x], [b], cli, ?_, by simp, by simp, by omega⟩
          cases x <;>
            simp [dgStep, dgSt, dW, midBlock, dp0, dp1, lastBlock,
              selectHead_true, selectHead_emptyFlag_cons]
      | [y], _ =>
          refine ⟨[], [], STEP (pair W (pair cli (pair [x] (pair [y] [b])))), ?_,
            by simp, by simp, ?_⟩
          · cases x <;> cases y <;>
              simp [dgStep, dgSt, dW, midBlock, dp0, dp1, lastBlock,
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
private lemma dp0_mem_FP : dp0 ∈ FP := mem_FP_comp midBlock_mem_FP fstBlock_mem_FP
private lemma dp1_mem_FP : dp1 ∈ FP := mem_FP_comp midBlock_mem_FP sndBlock_mem_FP

lemma dgStep_mem_FP {STEP : List Bool → List Bool} (hSTEP : STEP ∈ FP) (b : Bool) :
    dgStep STEP b ∈ FP :=
  selectHeadFn_mem_FP (emptyFlag_mem_FP dp0_mem_FP)
    (pairFn_mem_FP (constFn_mem_FP (pair [b] [])) lastBlock_mem_FP)
    (selectHeadFn_mem_FP (emptyFlag_mem_FP dp1_mem_FP)
      (pairFn_mem_FP (pairFn_mem_FP dp0_mem_FP (constFn_mem_FP [b])) lastBlock_mem_FP)
      (pairFn_mem_FP (constFn_mem_FP (pair [] []))
        (mem_FP_comp
          (pairFn_mem_FP dW_mem_FP
            (pairFn_mem_FP lastBlock_mem_FP
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
private def leAcc (v : List Bool) : List Bool := fstBlock (midBlock v)
private def lePow (v : List Bool) : List Bool := sndBlock (midBlock v)
private def leB0 (v : List Bool) : List Bool := fstBlock (lastBlock v)
private def leB1 (v : List Bool) : List Bool := fstBlock (sndBlock (lastBlock v))
private def leB2 (v : List Bool) : List Bool := sndBlock (sndBlock (lastBlock v))

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
    simp [leDigit, leCap, midBlock, leAcc, lePow, lastBlock, leB0, leB1, leB2, mulSel,
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
  have hacc : leAcc ∈ FP := mem_FP_comp midBlock_mem_FP fstBlock_mem_FP
  have hpow : lePow ∈ FP := mem_FP_comp midBlock_mem_FP sndBlock_mem_FP
  have hb0 : leB0 ∈ FP := mem_FP_comp lastBlock_mem_FP fstBlock_mem_FP
  have hb1 : leB1 ∈ FP := mem_FP_comp (mem_FP_comp lastBlock_mem_FP sndBlock_mem_FP) fstBlock_mem_FP
  have hb2 : leB2 ∈ FP := mem_FP_comp (mem_FP_comp lastBlock_mem_FP sndBlock_mem_FP) sndBlock_mem_FP
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
private def icDone (v : List Bool) : List Bool := fstBlock (midBlock v)
private def icOut (v : List Bool) : List Bool := sndBlock (midBlock v)
private def icB0 (v : List Bool) : List Bool := fstBlock (lastBlock v)
private def icB1 (v : List Bool) : List Bool := fstBlock (sndBlock (lastBlock v))
private def icB2 (v : List Bool) : List Bool := sndBlock (sndBlock (lastBlock v))

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
          simp [incDigit, midBlock, icDone, icOut, lastBlock, icB0, icB1, icB2, digitSlots,
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
            simp [incDigit, midBlock, icDone, icOut, lastBlock, icB0, icB1, icB2, digitSlots,
              digitBits, selectHead_true, selectHead_false]
        rw [hstep, dgFold_incDigit_done W ds _ htail, if_pos hlt]
        simp only [digitsToBits_cons, List.append_assoc, if_true]
      · have hge : 3 ≤ d := by omega
        have hstep : incDigit (pair W (pair (pair [] out) (digitSlots d)))
            = pair [] (out ++ digitBits 0) := by
          interval_cases d <;>
            simp [incDigit, midBlock, icDone, icOut, lastBlock, icB0, icB1, icB2, digitSlots,
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

private lemma icDone_mem_FP : icDone ∈ FP := mem_FP_comp midBlock_mem_FP fstBlock_mem_FP
private lemma icOut_mem_FP : icOut ∈ FP := mem_FP_comp midBlock_mem_FP sndBlock_mem_FP
private lemma icB0_mem_FP : icB0 ∈ FP := mem_FP_comp lastBlock_mem_FP fstBlock_mem_FP
private lemma icB1_mem_FP : icB1 ∈ FP :=
  mem_FP_comp (mem_FP_comp lastBlock_mem_FP sndBlock_mem_FP) fstBlock_mem_FP
private lemma icB2_mem_FP : icB2 ∈ FP :=
  mem_FP_comp (mem_FP_comp lastBlock_mem_FP sndBlock_mem_FP) sndBlock_mem_FP

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
  have hcli := midBlock_pair W cli (pair [b0] (pair [b1] [b2]))
  have hslots := lastBlock_pair W cli (pair [b0] (pair [b1] [b2]))
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
  refine foldlBits_mem_FP (A := incStep) (B := incStep) (W := fun _ => [])
    (S := U) incStep_mem_FP incStep_mem_FP (constFn_mem_FP []) hU []
    (3 * Polynomial.X) (fun z u _ => ?_)
  have : foldlBits incStep incStep [] [] u = digitsToBits (unaryDigits u.length) :=
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

/-! ## Stripping the high zero digits

The third client of the digit fold, and the one a **compact numeral** emitter needs.  A
machine word carrying a value's base-four digits is not canonical — `undigitize` reads
`[1, 0]` and `[1]` identically, and `Increment` above deliberately builds a non-canonical
run — so an emitter whose output *shape* depends on the value's base-four length (`len4`)
must first find the run's last nonzero digit.  That is one left-to-right pass with two
accumulators: `kept`, the emission for the digits up to and including the last nonzero one
seen, and `pend`, the emission for the zeros seen since.  A nonzero digit flushes `pend`
into `kept`; a zero extends `pend`.  At the end `kept` is the answer and `pend` is
discarded, so `stripAcc_closed` reads the fold against `trimZeros`, which
`trimZeros_eq_natDigits4` identifies with the canonical run.

Two design points make it fit `dgFold`.

*It emits most significant first* although the fold runs least significant first, because
every step **prepends**.  So no word reversal is needed — `Complexity.FP` has no reversal
primitive here — and the compact numeral's digit blocks come out in the paper's order.

*The state is `pair pend kept`, in that order.*  `|pair a b| = 2 |a| + |b| + 2`, so holding
the flushed accumulator in the *second* slot keeps the per-step growth a constant; the other
order doubles `kept` at every flush and no constant `c` bounds it, which is what
`dgFold_mem_FP`'s `Q + |cli| + c` budget demands.  Nothing is truncated against a ruler
here, and nothing needs to be.

The client is parametric in the per-digit emission `E : ℕ → List Bool`, of which only
`E 0 … E 3` are used, so the word step is a two-bit `selectHead` nest over four constant
words.  Its two instances (`Construction/LUV/SourceCodec.lean`) are the numeral's digit
blocks and, at `E = fun _ => [false]`, the numeral's digit *count* as a unary ruler. -/

namespace Strip

-- The strip client's state slots (inside `midBlock`), and the two low digit-bit slots it
-- branches on (inside `lastBlock`).  The leading slot is ignored: a digit word's digits are
-- below four, so it is always `false`.
private def spB1 (v : List Bool) : List Bool := fstBlock (sndBlock (lastBlock v))
private def spB2 (v : List Bool) : List Bool := sndBlock (sndBlock (lastBlock v))
private def spPend (v : List Bool) : List Bool := fstBlock (midBlock v)
private def spKept (v : List Bool) : List Bool := sndBlock (midBlock v)

/-- One digit of the strip pass: a zero extends the pending run, anything else flushes the
pending run into the kept run behind the digit's own emission.  Prepending is what makes
the kept run most-significant-first. -/
def stripStep (E : ℕ → List Bool) (v : List Bool) : List Bool :=
  selectHead (spB1 v)
    (selectHead (spB2 v)
      (pair [] (E 3 ++ spPend v ++ spKept v))
      (pair [] (E 2 ++ spPend v ++ spKept v)))
    (selectHead (spB2 v)
      (pair [] (E 1 ++ spPend v ++ spKept v))
      (pair (E 0 ++ spPend v) (spKept v)))

private lemma spB1_mem_FP : spB1 ∈ FP :=
  mem_FP_comp (mem_FP_comp lastBlock_mem_FP sndBlock_mem_FP) fstBlock_mem_FP
private lemma spB2_mem_FP : spB2 ∈ FP :=
  mem_FP_comp (mem_FP_comp lastBlock_mem_FP sndBlock_mem_FP) sndBlock_mem_FP
private lemma spPend_mem_FP : spPend ∈ FP := mem_FP_comp midBlock_mem_FP fstBlock_mem_FP
private lemma spKept_mem_FP : spKept ∈ FP := mem_FP_comp midBlock_mem_FP sndBlock_mem_FP

lemma stripStep_mem_FP (E : ℕ → List Bool) : stripStep E ∈ FP := by
  have hflush : ∀ K : List Bool, (fun v => pair [] (K ++ spPend v ++ spKept v)) ∈ FP :=
    fun K => pairFn_mem_FP (constFn_mem_FP [])
      (appendFn_mem_FP (appendFn_mem_FP (constFn_mem_FP K) spPend_mem_FP) spKept_mem_FP)
  exact selectHeadFn_mem_FP spB1_mem_FP
    (selectHeadFn_mem_FP spB2_mem_FP (hflush (E 3)) (hflush (E 2)))
    (selectHeadFn_mem_FP spB2_mem_FP (hflush (E 1))
      (pairFn_mem_FP (appendFn_mem_FP (constFn_mem_FP (E 0)) spPend_mem_FP)
        spKept_mem_FP))

/-- The step read at the argument shape `dgStep` builds. -/
private lemma stripStep_pair (E : ℕ → List Bool) (W cli : List Bool) (b0 b1 b2 : Bool) :
    stripStep E (pair W (pair cli (pair [b0] (pair [b1] [b2]))))
      = if b1 then
          (if b2 then pair [] (E 3 ++ fstBlock cli ++ sndBlock cli)
           else pair [] (E 2 ++ fstBlock cli ++ sndBlock cli))
        else
          (if b2 then pair [] (E 1 ++ fstBlock cli ++ sndBlock cli)
           else pair (E 0 ++ fstBlock cli) (sndBlock cli)) := by
  cases b1 <;> cases b2 <;>
    simp [stripStep, midBlock, lastBlock, spB1, spB2, spPend, spKept,
      selectHead_true, selectHead_false]

/-- **The client's whole obligation**: the state grows by a constant at every digit, on
*every* word, because the flushed accumulator sits in `pair`'s second slot. -/
lemma stripStep_length_le (E : ℕ → List Bool) (W cli : List Bool) (b0 b1 b2 : Bool) :
    (stripStep E (pair W (pair cli (pair [b0] (pair [b1] [b2]))))).length
      ≤ cli.length
        + (2 * ((E 0).length + (E 1).length + (E 2).length + (E 3).length) + 2) := by
  have hsplit := two_fstBlock_add_sndBlock_le cli
  rw [stripStep_pair]
  cases b1 <;> cases b2
  · show (pair (E 0 ++ fstBlock cli) (sndBlock cli)).length ≤ _
    simp only [pair_length, List.length_append]
    omega
  · show (pair [] (E 1 ++ fstBlock cli ++ sndBlock cli)).length ≤ _
    simp only [pair_length, List.length_append, List.length_nil]
    omega
  · show (pair [] (E 2 ++ fstBlock cli ++ sndBlock cli)).length ≤ _
    simp only [pair_length, List.length_append, List.length_nil]
    omega
  · show (pair [] (E 3 ++ fstBlock cli ++ sndBlock cli)).length ≤ _
    simp only [pair_length, List.length_append, List.length_nil]
    omega

/-- The step at a digit below four, in the model's own vocabulary. -/
private lemma stripStep_digitSlots (E : ℕ → List Bool) (W cli : List Bool) :
    ∀ d : ℕ, d < 4 →
      stripStep E (pair W (pair cli (digitSlots d)))
        = if d = 0 then pair (E 0 ++ fstBlock cli) (sndBlock cli)
          else pair [] (E d ++ fstBlock cli ++ sndBlock cli) := by
  intro d hd
  interval_cases d
  · rw [show digitSlots 0 = pair [false] (pair [false] [false]) from rfl, stripStep_pair]
    simp
  · rw [show digitSlots 1 = pair [false] (pair [false] [true]) from rfl, stripStep_pair]
    simp
  · rw [show digitSlots 2 = pair [false] (pair [true] [false]) from rfl, stripStep_pair]
    simp
  · rw [show digitSlots 3 = pair [false] (pair [true] [true]) from rfl, stripStep_pair]
    simp

/-- The digit-level model the strip step realizes: the pending and kept runs. -/
def stripAcc (E : ℕ → List Bool) :
    List ℕ → List Bool → List Bool → List Bool × List Bool
  | [], p, k => (p, k)
  | d :: ds, p, k =>
      if d = 0 then stripAcc E ds (E 0 ++ p) k else stripAcc E ds [] (E d ++ p ++ k)

/-- **The digit fold at the strip step computes the model.** -/
lemma dgFold_stripStep (E : ℕ → List Bool) (W : List Bool) :
    ∀ (ds : List ℕ) (p k : List Bool), (∀ d ∈ ds, d < 4) →
      dgFold (stripStep E) W (pair p k) ds
        = pair (stripAcc E ds p k).1 (stripAcc E ds p k).2
  | [], p, k, _ => by rw [dgFold, stripAcc]
  | d :: ds, p, k, h => by
      rw [dgFold, stripStep_digitSlots E W (pair p k) d (h d (List.mem_cons_self ..)),
        stripAcc]
      have htail : ∀ e ∈ ds, e < 4 := fun e he => h e (List.mem_cons_of_mem _ he)
      by_cases h0 : d = 0
      · rw [if_pos h0, if_pos h0, fstBlock_pair, sndBlock_pair]
        exact dgFold_stripStep E W ds _ _ htail
      · rw [if_neg h0, if_neg h0, fstBlock_pair, sndBlock_pair]
        exact dgFold_stripStep E W ds _ _ htail

/-- The model, one digit appended at the *high* end — the shape the closed form's
induction needs. -/
private lemma stripAcc_append (E : ℕ → List Bool) (d : ℕ) :
    ∀ (ds : List ℕ) (p k : List Bool),
      stripAcc E (ds ++ [d]) p k
        = if d = 0 then (E 0 ++ (stripAcc E ds p k).1, (stripAcc E ds p k).2)
          else ([], E d ++ (stripAcc E ds p k).1 ++ (stripAcc E ds p k).2)
  | [], p, k => by
      rw [List.nil_append, stripAcc, stripAcc]
      by_cases h0 : d = 0
      · rw [if_pos h0, if_pos h0, stripAcc]
      · rw [if_neg h0, if_neg h0, stripAcc]
  | e :: ds, p, k => by
      rw [List.cons_append, stripAcc, stripAcc]
      by_cases he : e = 0
      · rw [if_pos he, if_pos he, stripAcc_append E d ds]
      · rw [if_neg he, if_neg he, stripAcc_append E d ds]

/-- A digit run with its high zeros removed. -/
def trimZeros (ds : List ℕ) : List ℕ := (ds.reverse.dropWhile (fun d => d == 0)).reverse

@[simp] lemma trimZeros_nil : trimZeros [] = [] := rfl

lemma trimZeros_append_zero (ds : List ℕ) : trimZeros (ds ++ [0]) = trimZeros ds := by
  simp [trimZeros]

lemma trimZeros_append_ne (ds : List ℕ) {d : ℕ} (hd : d ≠ 0) :
    trimZeros (ds ++ [d]) = ds ++ [d] := by
  simp [trimZeros, hd]

/-- **What was stripped were zeros**: a run is its trimmed run followed by zeros, and the
trimmed run is no longer. -/
lemma trimZeros_spec : ∀ ds : List ℕ,
    ds = trimZeros ds ++ List.replicate (ds.length - (trimZeros ds).length) 0
      ∧ (trimZeros ds).length ≤ ds.length := by
  intro ds
  induction ds using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
      obtain ⟨heq, hle⟩ := ih
      by_cases ha : a = 0
      · subst ha
        rw [trimZeros_append_zero]
        refine ⟨?_, by simp; omega⟩
        have hm : (l ++ [0]).length - (trimZeros l).length
            = (l.length - (trimZeros l).length) + 1 := by simp; omega
        rw [hm, List.replicate_succ', ← List.append_assoc, ← heq]
      · rw [trimZeros_append_ne l ha]
        exact ⟨by simp, le_rfl⟩

/-- **A run whose top digit is nonzero is canonical.**  `exists_zero_pad_of_digitVal` says
every run is its value's canonical run padded with zeros; a nonzero last digit forces the
padding to be empty. -/
lemma natDigits4_digitVal_append (ds : List ℕ) {d : ℕ}
    (h : ∀ e ∈ ds ++ [d], e < 4) (hd : d ≠ 0) :
    natDigits4 (digitVal (ds ++ [d])) = ds ++ [d] := by
  obtain ⟨m, hm⟩ := exists_zero_pad_of_digitVal (ds ++ [d]) h
  cases m with
  | zero => simpa using hm.symm
  | succ m =>
      exfalso
      rw [List.replicate_succ', ← List.append_assoc] at hm
      have hrev := congrArg List.reverse hm
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.cons.injEq] at hrev
      exact hd hrev.1

/-- **The trimmed run is the value's canonical run.** -/
lemma trimZeros_eq_natDigits4 : ∀ ds : List ℕ, (∀ d ∈ ds, d < 4) →
    trimZeros ds = natDigits4 (digitVal ds) := by
  intro ds
  induction ds using List.reverseRecOn with
  | nil => intro _; simp [natDigits4]
  | append_singleton l a ih =>
      intro h
      have hl : ∀ e ∈ l, e < 4 := fun e he => h e (List.mem_append_left _ he)
      by_cases ha : a = 0
      · subst ha
        rw [trimZeros_append_zero, ih hl, digitVal_append_singleton]
        simp
      · rw [trimZeros_append_ne l ha, natDigits4_digitVal_append l h ha]

/-- **The closed form of the strip pass.**  The kept run is the trimmed digit run's
emission, most significant first; the pending run is the stripped zeros' emission, and is
discarded. -/
lemma stripAcc_closed (E : ℕ → List Bool) : ∀ ds : List ℕ,
    (stripAcc E ds [] []).1
        = (List.replicate (ds.length - (trimZeros ds).length) (E 0)).flatten
      ∧ (stripAcc E ds [] []).2 = (trimZeros ds).reverse.flatMap E := by
  intro ds
  induction ds using List.reverseRecOn with
  | nil => simp [stripAcc]
  | append_singleton l a ih =>
      obtain ⟨ih1, ih2⟩ := ih
      obtain ⟨hpad, hle⟩ := trimZeros_spec l
      by_cases ha : a = 0
      · subst ha
        rw [stripAcc_append, if_pos rfl, trimZeros_append_zero]
        refine ⟨?_, ih2⟩
        show E 0 ++ (stripAcc E l [] []).1 = _
        have hm : (l ++ [0]).length - (trimZeros l).length
            = (l.length - (trimZeros l).length) + 1 := by
          simp only [List.length_append, List.length_singleton]; omega
        rw [ih1, hm, List.replicate_succ, List.flatten_cons]
      · rw [stripAcc_append, if_neg ha, trimZeros_append_ne l ha]
        refine ⟨by simp, ?_⟩
        show E a ++ (stripAcc E l [] []).1 ++ (stripAcc E l [] []).2 = _
        rw [ih1, ih2]
        have hflat : (List.replicate (l.length - (trimZeros l).length) 0).flatMap E
            = (List.replicate (l.length - (trimZeros l).length) (E 0)).flatten := by
          rw [List.flatMap_def, List.map_replicate]
        have hrev : l.reverse.flatMap E
            = (List.replicate (l.length - (trimZeros l).length) (E 0)).flatten
              ++ (trimZeros l).reverse.flatMap E := by
          conv_lhs => rw [hpad]
          rw [List.reverse_append, List.reverse_replicate, List.flatMap_append, hflat]
        rw [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append, List.flatMap_cons, hrev, List.append_assoc]

end Strip

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

/-- **`undigitize` distributes over a `flatMap` of block-complete digit runs**, and the
concatenation is itself block-complete — the `flatMap` form of
`undigitize_append_of_complete`, which is what lets a variable-count concatenation of
written-out segments transport. The side condition is per-segment: each `f j` ends on a
block boundary. -/
lemma undigitize_flatMap_complete {ι : Type*} (f : ι → List ℕ) :
    ∀ l : List ι, (∀ j ∈ l, (blockSplit (f j)).2 = []) →
      undigitize (l.flatMap f) = l.flatMap (fun j => undigitize (f j)) ∧
        (blockSplit (l.flatMap f)).2 = []
  | [], _ => ⟨rfl, rfl⟩
  | j :: l, h => by
      have hj := h j (List.mem_cons_self ..)
      have ih := undigitize_flatMap_complete f l
        (fun k hk => h k (List.mem_cons_of_mem _ hk))
      rw [List.flatMap_cons, List.flatMap_cons]
      exact ⟨by rw [undigitize_append_of_complete _ _ hj, ih.1],
        by rw [blockSplit_append_of_complete _ _ hj]; exact ih.2⟩

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

/-! ### Block-complete words

A rewriter splices words; `decodeBits` is how the machine's reader sees the splice, and
`BlockWF` is the discipline — every piece a whole number of complete blocks — under which
the splice decodes piecewise.  Both the buffered run and every emitted fragment keep it. -/

/-- The token stream a word carries, as `EfficientlyComputable` reads it. -/
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

/-- **The splice discipline survives a `flatMap`**: a concatenation of block-complete words
is block-complete, and the machine's reading of it is the concatenation of the readings.
This is `BlockWF.append` and `decodeBits_append` at variable arity — what a rewriter
emitting `cnt n` segments needs, and the pure-list half of
`MachineTokenStream.concatVar` (`Framework/Machine/WriteOutMachine.lean`). The side
condition is per-segment: no bound on the number of segments or on any token's value.

The digit-level twin, one layer below, is `undigitize_flatMap_complete`. -/
lemma BlockWF.flatMap {ι : Type*} (f : ι → List Bool) :
    ∀ l : List ι, (∀ j ∈ l, BlockWF (f j)) →
      BlockWF (l.flatMap f) ∧
        decodeBits (l.flatMap f) = l.flatMap fun j => decodeBits (f j)
  | [], _ => ⟨BlockWF.nil, by simp⟩
  | j :: l, h => by
      have hj := h j (List.mem_cons_self ..)
      have ih := BlockWF.flatMap f l (fun k hk => h k (List.mem_cons_of_mem _ hk))
      rw [List.flatMap_cons, List.flatMap_cons]
      exact ⟨hj.append ih.1, by rw [decodeBits_append hj ih.1, ih.2]⟩

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

/-! ### Reading a one-token block back as a digit run

The three lemmas below invert `blockWF_run`/`decodeBits_run`: a block-complete word decoding
to a single token *is* that token's base-four payload run followed by one terminator digit,
so the run is recovered by dropping the last three bits. They are the pure-list half of
`MachineDigits.exists_digitWord` (`Framework/Machine/WriteOutMachine.lean`), which is where
the `Complexity.FP` truncation that performs the drop lives; kept here beside `BlockWF`
because nothing in them mentions the machine.

The two `blockSplit` inversions are what make the block shape *forced* rather than assumed:
neither the number of blocks nor the token's value is a hypothesis. -/

/-- A digit stream whose block split has completed no block at all is its own partial
block: no terminator was ever read. -/
lemma blockSplit_eq_nil_fst {ds cur : List ℕ} (h : blockSplit ds = ([], cur)) :
    ds = cur := by
  induction ds using List.reverseRecOn generalizing cur with
  | nil => simpa [blockSplit] using h.symm
  | append_singleton ds d ih =>
      rw [blockSplit_snoc, blockStep] at h
      by_cases hd : d < 4
      · rw [if_pos hd] at h
        have h1 : (blockSplit ds).1 = [] := congrArg Prod.fst h
        have h2 : (blockSplit ds).2 ++ [d] = cur := congrArg Prod.snd h
        have := ih (cur := (blockSplit ds).2) (by rw [Prod.ext_iff]; exact ⟨h1, rfl⟩)
        rw [← h2, ← this]
      · rw [if_neg hd] at h
        have h1 : (blockSplit ds).1 ++ [(blockSplit ds).2] = [] := congrArg Prod.fst h
        simp at h1

/-- A digit stream whose block split is one complete block and nothing over is that block
followed by a single terminator digit. -/
lemma blockSplit_eq_single {ds cur : List ℕ} (h : blockSplit ds = ([cur], [])) :
    ∃ t, 4 ≤ t ∧ ds = cur ++ [t] := by
  induction ds using List.reverseRecOn with
  | nil => simp [blockSplit] at h
  | append_singleton ds d ih =>
      rw [blockSplit_snoc, blockStep] at h
      by_cases hd : d < 4
      · rw [if_pos hd] at h
        have h2 : (blockSplit ds).2 ++ [d] = [] := congrArg Prod.snd h
        simp at h2
      · rw [if_neg hd] at h
        have h1 : (blockSplit ds).1 ++ [(blockSplit ds).2] = [cur] := congrArg Prod.fst h
        have hnil : (blockSplit ds).1 = [] ∧ (blockSplit ds).2 = cur := by
          cases hb : (blockSplit ds).1 with
          | nil => rw [hb] at h1; simpa using h1
          | cons b bs => rw [hb] at h1; simp at h1
        refine ⟨d, by omega, ?_⟩
        rw [blockSplit_eq_nil_fst (ds := ds) (cur := cur)
          (by rw [Prod.ext_iff]; exact ⟨hnil.1, hnil.2⟩)]

/-- **A one-token block word is a digit run plus a terminator.** Dropping the last three
bits of a block-complete word decoding to `[v]` leaves the base-four payload run of `v`.
Side condition: none beyond the two hypotheses — `v` itself is unbounded, which is the
point: the word's *length* is what a polynomial bounds, never the token's value.

The truncation is written `w.take (w.drop 3).length` rather than `w.take (w.length - 3)`
because that is the shape `Cobham.takeLenFn_mem_FP` consumes, the two lengths being
compared rather than subtracted. -/
lemma digitRun_of_blockWF {w : List Bool} {v : ℕ}
    (hwf : BlockWF w) (hv : decodeBits w = [v]) :
    ∃ cur : List ℕ, (∀ d ∈ cur, d < 4) ∧ digitVal cur = v ∧
      w.take (w.drop 3).length = digitsToBits cur := by
  obtain ⟨ds, rfl, h8, hcomp⟩ := hwf
  rw [decodeBits, bitsToDigits_digitsToBits ds h8, undigitize_eq_blockSplit] at hv
  obtain ⟨cur, hcur1, hcur2⟩ : ∃ cur, (blockSplit ds).1 = [cur] ∧ digitVal cur = v := by
    cases hb : (blockSplit ds).1 with
    | nil => rw [hb] at hv; simp at hv
    | cons b bs =>
        rw [hb] at hv
        simp only [List.map_cons, List.cons.injEq] at hv
        exact ⟨b, by rw [List.map_eq_nil_iff.mp hv.2], hv.1⟩
  have hlt : ∀ d ∈ cur, d < 4 :=
    (blockSplit_digits_lt ds).1 cur (by rw [hcur1]; simp)
  obtain ⟨t, -, rfl⟩ := blockSplit_eq_single (ds := ds) (cur := cur)
    (by rw [Prod.ext_iff]; exact ⟨hcur1, hcomp⟩)
  refine ⟨cur, hlt, hcur2, ?_⟩
  rw [digitsToBits_append]
  simp only [List.length_drop, List.length_append, length_digitsToBits,
    List.length_cons, List.length_nil]
  rw [show 3 * cur.length + 3 * (0 + 1) - 3 = (digitsToBits cur).length by simp]
  simp

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

/-- Every digit a `digitize` emits is a base-four payload digit or the terminator `4`.
`mem_digitize_lt_eight` is the same induction at the coarser bound the *decoder* needs;
this is the sharper bound the emitted *word* needs, since the emitter clamps each digit
with `min · 4` and this says that clamp is the identity. -/
lemma mem_digitize_le_four (ts : List ℕ) : ∀ d ∈ digitize ts, d ≤ 4 := by
  intro d hd
  rw [digitize, List.mem_flatMap] at hd
  obtain ⟨t, -, hd⟩ := hd
  rw [tokenBlock, List.mem_append] at hd
  rcases hd with hd | hd
  · exact le_of_lt (natDigits4_lt t d hd)
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

/-- **A concatenated constant word is the concatenation of the constant words.**  What a
`Strip` client emitting one `tokBits` block per digit builds is `tokBits` of the
concatenated token list — so its output is block-complete and decodes without a further
splice argument. -/
lemma tokBits_flatMap (f : ℕ → List ℕ) (l : List ℕ) :
    (l.flatMap fun x => tokBits (f x)) = tokBits (l.flatMap f) := by
  rw [tokBits, digitize_flatMap, ← digitsToBits_flatMap]
  rfl

/-! ## Unary numerals and emitted values

A value the machine knows only as a *length* — a counter, a product of counters — reaches
the stream as one complete token block.  `unaryBlock` is that emission; `uMul` and
`unaryPair_mem_FP` are the arithmetic on lengths that is not just `++`. -/

/-- The product of two unary numerals.  `Cobham.mulLenFn_mem_FP` emits `false` marks; the
content is irrelevant, the length is the number. -/
def uMul (a b : List Bool) : List Bool := List.replicate (a.length * b.length) false

@[simp] lemma length_uMul (a b : List Bool) : (uMul a b).length = a.length * b.length := by
  simp [uMul]

lemma uMul_mem_FP {A B : List Bool → List Bool} (hA : A ∈ FP) (hB : B ∈ FP) :
    (fun z => uMul (A z) (B z)) ∈ FP := mulLenFn_mem_FP hA hB

/-- **Pairing two values known as lengths is polynomial time.**

`Nat.pair a b` is `if a < b then b * b + a else a * a + a + b`, so it is two length
products, three concatenations and one length comparison: `Cobham.mulLenFn_mem_FP`,
`Cobham.appendFn_mem_FP` and `selectHeadFn_leFlag_mem_FP`, with
`Complexity.unaryLength_mem_FP` recolouring the assembled ruler to the `true` marks
`unaryDay` uses. The emitted word is literally `unaryDay (Nat.pair (A z).length (B z).length)`.

This is what lets a machine build the *argument* of a day-indexed emitter from a day and a
loop counter it holds only as lengths — the step of `concatUnaryPair_mem_FP` below.
Proof kind: `C` composition.  Provenance: (b) `Complexitylib.Classes.P.Cobham.Internal`,
`Complexitylib.Classes.P.UnaryLength`. -/
lemma unaryPair_mem_FP {A B : List Bool → List Bool} (hA : A ∈ FP) (hB : B ∈ FP) :
    (fun z => List.replicate (Nat.pair (A z).length (B z).length) true) ∈ FP := by
  have hbig : (fun z => List.replicate ((B z).length * (B z).length) false ++ A z) ∈ FP :=
    appendFn_mem_FP (mulLenFn_mem_FP hB hB) hA
  have hsmall :
      (fun z => List.replicate ((A z).length * (A z).length) false ++ A z ++ B z) ∈ FP :=
    appendFn_mem_FP (appendFn_mem_FP (mulLenFn_mem_FP hA hA) hA) hB
  have hsel := selectHeadFn_leFlag_mem_FP hA hB hsmall hbig
  have h := mem_FP_comp hsel unaryLength_mem_FP
  have heq : ((fun x : List Bool => List.replicate x.length true) ∘
        fun z => if (B z).length ≤ (A z).length then
          List.replicate ((A z).length * (A z).length) false ++ A z ++ B z
        else List.replicate ((B z).length * (B z).length) false ++ A z)
      = fun z => List.replicate (Nat.pair (A z).length (B z).length) true := by
    funext z
    simp only [Function.comp_apply]
    congr 1
    rw [Nat.pair]
    by_cases hz : (B z).length ≤ (A z).length
    · rw [if_pos hz, if_neg (by omega)]
      simp only [List.length_append, List.length_replicate]
    · rw [if_neg hz, if_pos (by omega)]
      simp only [List.length_append, List.length_replicate]
  rwa [heq] at h

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

/-- **The client interface, at block granularity.**  A step and an emitter that read each
token block, with the two per-step length bounds, compute the block-level fold in
polynomial time — over exactly the blocks `EfficientlyComputable`'s decoding splits its
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
polynomial time — over exactly the token stream `EfficientlyComputable` decodes.

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

/-! ## Variable-count concatenation

The machine has no random access into its own future output, so a stream that concatenates
`cnt n` day-`n` segments has to *stream* the concatenation: a fold over a unary ruler of
`cnt n` marks, carrying `pair (unary loop counter) (output so far)` as its state, whose step
rebuilds the emitter's argument `unaryDay (Nat.pair n j)` from the day and the counter
(`unaryPair_mem_FP`) and appends the emitter's answer.  This is the machine-side counterpart
of the fuel side's `PolySegStream.concatVar` (`Framework/Emission/Computable.lean`), which
instead scans a prefix table and reads the enclosing segment off it — a random access
`Complexity.FP` cannot mimic and does not need.

**Why the loop counter is clamped.**  `FPFold.foldlBits_mem_FP`'s state bound is quantified
over *every* word no longer than the ruler, not over the trajectory the machine actually
runs, so the step has to be bounded on malformed inputs too.  On such a word the counter is
bounded only by the input length, and `Nat.pair n j` is quadratic in it, so an unclamped
step would need a bound that grows with each iteration.  `cvJc` therefore clamps the counter
against the ruler before pairing (`selectHeadFn_leFlag_mem_FP`), which makes the per-step
emission bound *unconditional* — `Q.eval (|W z| + |S z|)`, uniform in the step — and the
fold bound `|u| * Q.eval (…)`, the shape `dgFold_mem_FP` already discharges.

**Where the per-step polynomial comes from.**  Not from the emitter's class: `F ∈ FP` alone
bounds `|F x|` by a polynomial in `|x|`, because a time bound is an output-length bound
(`Cobham.output_length_poly_of_mem_FP`).  So no data class carrying its own length
polynomial is needed, and none of the write-out classes acquires such a field. -/

-- The concatenation step's argument is `pair (pair ruler day) (pair counter out)`; the
-- counter and the output word are `midBlock` and `lastBlock`, and these read the parameter
-- block.  That block is `pair (R z) z` rather than `pair z (R z)` so that
-- `Complexity.mem_FP_pairWithInput` builds it, the input word itself being the day.
private def cvRl (v : List Bool) : List Bool := fstBlock (fstBlock v)
private def cvDay (v : List Bool) : List Bool := sndBlock (fstBlock v)

/-- The loop counter, clamped against the ruler: never longer than the ruler, so the paired
argument the step builds is never larger than `Nat.pair day (cnt day)`. -/
private def cvJc (v : List Bool) : List Bool :=
  if (cvRl v).length ≤ (midBlock v).length then cvRl v else midBlock v

/-- One segment: advance the counter by a mark and append `F` at the paired index. -/
private def cvStep (F : List Bool → List Bool) (v : List Bool) : List Bool :=
  pair (midBlock v ++ [false])
    (lastBlock v ++ F (List.replicate (Nat.pair (cvDay v).length (cvJc v).length) true))

private lemma cvStep_mem_FP {F : List Bool → List Bool} (hF : F ∈ FP) : cvStep F ∈ FP := by
  have hrl : cvRl ∈ FP := mem_FP_comp fstBlock_mem_FP fstBlock_mem_FP
  have hday : cvDay ∈ FP := mem_FP_comp fstBlock_mem_FP sndBlock_mem_FP
  have hjc : cvJc ∈ FP := selectHeadFn_leFlag_mem_FP midBlock_mem_FP hrl hrl midBlock_mem_FP
  exact pairFn_mem_FP (appendFn_mem_FP midBlock_mem_FP (constFn_mem_FP [false]))
    (appendFn_mem_FP lastBlock_mem_FP (mem_FP_comp (unaryPair_mem_FP hday hjc) hF))

/-- The word the fold accumulates after `k` steps: the emitter's answers at the first `k`
paired indices, the index clamped exactly as the step clamps it. -/
private def cvFlat (F : List Bool → List Bool) (day rl : List Bool) (k : ℕ) : List Bool :=
  (List.range k).flatMap fun j =>
    F (List.replicate (Nat.pair day.length (min j rl.length)) true)

private lemma cvFlat_succ (F : List Bool → List Bool) (day rl : List Bool) (k : ℕ) :
    cvFlat F day rl (k + 1)
      = cvFlat F day rl k
        ++ F (List.replicate (Nat.pair day.length (min k rl.length)) true) := by
  simp [cvFlat, List.range_succ]

/-- What the fold computes, on the all-`false` words the ruler supplies. -/
private lemma cvFold_replicate (F : List Bool → List Bool) (day rl : List Bool) : ∀ k : ℕ,
    foldlBits (cvStep F) (cvStep F) (pair rl day) (pair [] []) (List.replicate k false)
      = pair (List.replicate k false) (cvFlat F day rl k)
  | 0 => rfl
  | k + 1 => by
      have hrep : (List.replicate (k + 1) false : List Bool)
          = List.replicate k false ++ [false] := List.replicate_succ'
      rw [hrep, foldlBits_append_singleton, cvFold_replicate F day rl k, cvFlat_succ]
      simp only [cond_false, cvStep, cvDay, cvRl, midBlock, lastBlock, cvJc,
        fstBlock_pair, sndBlock_pair, List.length_replicate]
      by_cases hk : rl.length ≤ k
      · rw [if_pos hk, min_eq_right hk]
      · rw [if_neg hk, List.length_replicate,
          min_eq_left (by omega : k ≤ rl.length)]

/-- Both branches of the fold are the same step, so only the *length* of the folded word
matters — which is what makes the clamp bound hold on malformed words as well. -/
private lemma cvFold_any (F : List Bool → List Bool) (W : List Bool) :
    ∀ (st u : List Bool),
      foldlBits (cvStep F) (cvStep F) W st u
        = foldlBits (cvStep F) (cvStep F) W st (List.replicate u.length false)
  | _, [] => rfl
  | st, b :: bs => by
      rw [foldlBits_cons, List.length_cons, List.replicate_succ, foldlBits_cons]
      cases b <;> simp only [cond_false, cond_true] <;>
        exact cvFold_any F W _ bs

private lemma cvFlat_length_le (F : List Bool → List Bool) (day rl : List Bool) (M : ℕ)
    (hM : ∀ j : ℕ,
      (F (List.replicate (Nat.pair day.length (min j rl.length)) true)).length ≤ M) :
    ∀ k : ℕ, (cvFlat F day rl k).length ≤ k * M
  | 0 => by simp [cvFlat]
  | k + 1 => by
      rw [cvFlat_succ, List.length_append]
      have h1 := cvFlat_length_le F day rl M hM k
      have h2 := hM k
      have h3 : (k + 1) * M = k * M + M := by ring
      omega

/-- **A variable-count concatenation of an `FP`-emitted family is `FP`.**

`R z` is a *unary ruler*: only its length is read, and that length is the number of segments
to emit.  `D z` is the outer index, likewise read only as a length.  The result concatenates
`F` evaluated at `unaryDay (Nat.pair (D z).length j)` for each `j` below that count — the
machine reading of "outer index `|D z|` plays `|R z|` segments, the `j`-th of them indexed
`⟨n, j⟩`", with no bound on any emitted segment beyond the one `F ∈ FP` already carries.

The outer index is a *parameter* rather than the input word itself because the two clients
disagree about it: a day-`n` stream takes `D = id` (the input is `unaryDay n`), while the
prefix-scan rulers of `Framework/Machine/Ruler.lean` run on `unaryDay (Nat.pair n k)` and
need `D` to be the ruler for `n`.

Proof kind: `P` proved.  Provenance: (a) `unaryPair_mem_FP`, `cvFold_replicate`;
(b) `FPFold.foldlBits_mem_FP`, `Cobham.output_length_poly_of_mem_FP`. -/
lemma concatUnaryPair_mem_FP {F R D : List Bool → List Bool} (hF : F ∈ FP) (hR : R ∈ FP)
    (hD : D ∈ FP) :
    ∃ G ∈ FP, ∀ z, G z = (List.range (R z).length).flatMap
        fun j => F (List.replicate (Nat.pair (D z).length j) true) := by
  obtain ⟨q, hq⟩ := output_length_poly_of_mem_FP hF
  set Q : Polynomial ℕ := q.comp ((2 * Polynomial.X + 1) ^ 2) with hQ
  set p : Polynomial ℕ :=
    Polynomial.C 2 + 2 * Polynomial.X + Polynomial.X * Q with hp
  have hW : (fun z : List Bool => pair (R z) (D z)) ∈ FP := pairFn_mem_FP hR hD
  have hchunk : ∀ (z : List Bool) (j : ℕ),
      (F (List.replicate (Nat.pair (D z).length (min j (R z).length)) true)).length
        ≤ Q.eval ((pair (R z) (D z)).length + (R z).length) := by
    intro z j
    refine le_trans (hq _) ?_
    rw [hQ, Polynomial.eval_comp]
    refine polynomial_eval_mono_nat q ?_
    simp only [List.length_replicate, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X]
    refine le_trans (Nat.pair_lt_max_add_one_sq _ _).le ?_
    have hmin : min j (R z).length ≤ (R z).length := min_le_right _ _
    have hlen : (pair (R z) (D z)).length = 2 * (R z).length + 2 + (D z).length :=
      pair_length _ _
    refine Nat.pow_le_pow_left ?_ 2
    omega
  have hfold : (fun z : List Bool =>
      foldlBits (cvStep F) (cvStep F) (pair (R z) (D z)) (pair [] []) (R z)) ∈ FP := by
    refine foldlBits_mem_FP (cvStep_mem_FP hF) (cvStep_mem_FP hF) hW hR (pair [] []) p ?_
    intro z u hu
    rw [cvFold_any F (pair (R z) (D z)) (pair [] []) u, cvFold_replicate]
    rw [pair_length, List.length_replicate]
    have hflat := cvFlat_length_le F (D z) (R z) _ (hchunk z) u.length
    have hlen : (pair (R z) (D z)).length = 2 * (R z).length + 2 + (D z).length :=
      pair_length _ _
    have hu' : u.length ≤ (pair (R z) (D z)).length + (R z).length := by omega
    have hmul : u.length * Q.eval ((pair (R z) (D z)).length + (R z).length)
        ≤ ((pair (R z) (D z)).length + (R z).length)
          * Q.eval ((pair (R z) (D z)).length + (R z).length) :=
      Nat.mul_le_mul_right _ hu'
    rw [hp]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  refine ⟨fun z =>
      sndBlock (foldlBits (cvStep F) (cvStep F) (pair (R z) (D z)) (pair [] []) (R z)),
    mem_FP_comp hfold sndBlock_mem_FP, fun z => ?_⟩
  show sndBlock (foldlBits (cvStep F) (cvStep F) (pair (R z) (D z)) (pair [] []) (R z)) = _
  rw [cvFold_any F (pair (R z) (D z)) (pair [] []) (R z), cvFold_replicate, sndBlock_pair,
    cvFlat]
  refine List.flatMap_congr (fun j hj => ?_)
  rw [min_eq_left (le_of_lt (List.mem_range.mp hj))]

end LogicalInduction.TokenFold
