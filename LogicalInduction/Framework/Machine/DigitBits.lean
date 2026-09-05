import LogicalInduction.Framework.Criterion
import Mathlib.Tactic.IntervalCases

/-!
# The bit rendering of a digit stream

The machine reading of `def:ec` — `MachineEfficientTrader` in `Framework/Criterion.lean` —
decodes a machine's output word through `bitsToDigits`, which groups three bits into a
digit, most significant first. This file supplies the other direction and the round trip.

Two definitions: `digitBits d`, the three bits `bitsToDigits` reads back as `d`, and
`digitsToBits`, a digit stream written out three bits per digit. The result they exist for
is `bitsToDigits_digitsToBits`, the round trip: a stream written out by `digitsToBits` reads
back as itself, provided every digit is below eight. It rests on the one-digit step
`bitsToDigits_digitBits`, and that on the two position lemmas `digitAt_digitBits` and
`digitAt_digitBits_succ`.

Three bits hold only the digits below eight, while the digits a `Nat.Partrec.Code` emits are
arbitrary naturals. They do not have to fit. `undigitizeStep` tests a digit only against
`4`, so every value from `4` up is the same block terminator, and `undigitize_map_min_four`
proves that clamping each digit at `4` leaves the token stream — hence the trader —
unchanged. Clamping is therefore what the machine emits, and this file is where that
convention is fixed and justified.

`Framework/Machine/TraderMachine.lean` writes the convention, emitting `digitBits (min d 4)`
per digit and assembling the word through `digitsToBits`; `Framework/MachineEfficiency.lean`,
`Framework/Machine/TokenFold.lean`, `Framework/Machine/DigitArithFP.lean`,
`Framework/Machine/WriteOutMachine.lean` and `Construction/Machine/CondStep.lean` read it
back. No `dd:` label applies: a fixed encoding convention is not a choice the paper leaves
open. Everything here is supporting infrastructure rather than a paper claim, so the
declarations are `lemma`s and carry no `Paper node` line.
-/

namespace LogicalInduction

/-! ## A digit as three bits -/

/-- The three bits `bitsToDigits` reads back as the digit `d`, most significant first. -/
def digitBits (d : ℕ) : List Bool :=
  [(d / 4) % 2 == 1, (d / 2) % 2 == 1, d % 2 == 1]

@[simp] lemma length_digitBits (d : ℕ) : (digitBits d).length = 3 := rfl

/-- The zeroth digit of `digitBits d ++ rest` is `d`, for `d < 8`. -/
lemma digitAt_digitBits (d : ℕ) (hd : d < 8) (rest : List Bool) :
    digitAt (digitBits d ++ rest) 0 = d := by
  interval_cases d <;> simp [digitAt, digitBits, b2n]

/-- Every later digit of `digitBits d ++ rest` is the corresponding digit of `rest`. -/
lemma digitAt_digitBits_succ (d i : ℕ) (rest : List Bool) :
    digitAt (digitBits d ++ rest) (i + 1) = digitAt rest i := by
  have h : ∀ j, 3 ≤ j → (digitBits d ++ rest)[j]? = rest[j - 3]? := by
    intro j hj
    rw [List.getElem?_append_right (by simpa using hj)]
    simp
  simp only [digitAt]
  rw [h _ (by omega : 3 ≤ 3 * (i + 1)), h _ (by omega : 3 ≤ 3 * (i + 1) + 1),
    h _ (by omega : 3 ≤ 3 * (i + 1) + 2),
    show 3 * (i + 1) - 3 = 3 * i from by omega,
    show 3 * (i + 1) + 1 - 3 = 3 * i + 1 from by omega,
    show 3 * (i + 1) + 2 - 3 = 3 * i + 2 from by omega]

/-- Reading a stream that begins with `digitBits d` recovers `d` and then reads the rest:
the one-digit step of the round trip, for `d < 8`. -/
lemma bitsToDigits_digitBits (d : ℕ) (hd : d < 8) (rest : List Bool) :
    bitsToDigits (digitBits d ++ rest) = d :: bitsToDigits rest := by
  have hlen : (digitBits d ++ rest).length / 3 = rest.length / 3 + 1 := by
    simp only [List.length_append, length_digitBits]
    omega
  rw [bitsToDigits, hlen, List.range_succ_eq_map, List.map_cons, List.map_map,
    digitAt_digitBits d hd rest, bitsToDigits]
  exact congrArg _ (List.map_congr_left (fun i _ => digitAt_digitBits_succ d i rest))

/-! ## The stream encoding and its round trip -/

/-- Encode a digit stream as bits, three bits per digit. -/
def digitsToBits (ds : List ℕ) : List Bool := ds.flatMap digitBits

/-- **The round trip.** Writing a digit stream out three bits per digit and reading it back
recovers it, provided every digit is below eight. -/
lemma bitsToDigits_digitsToBits : ∀ ds : List ℕ, (∀ d ∈ ds, d < 8) →
    bitsToDigits (digitsToBits ds) = ds
  | [], _ => rfl
  | d :: ds, h => by
      rw [digitsToBits, List.flatMap_cons,
        bitsToDigits_digitBits d (h d (List.mem_cons_self ..)) _]
      congr 1
      exact bitsToDigits_digitsToBits ds (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## Clamping at the block terminator -/

/-- `undigitize` reads a digit only through the test `d < 4`, so clamping every digit at
    the terminator value leaves the token stream alone. -/
lemma undigitize_map_min_four (ds : List ℕ) :
    undigitize (ds.map (fun d => min d 4)) = undigitize ds := by
  rw [undigitize, undigitize]
  congr 1
  suffices h : ∀ (st : List ℕ × ℕ × ℕ),
      List.foldl undigitizeStep st (ds.map (fun d => min d 4))
        = List.foldl undigitizeStep st ds from h _
  induction ds with
  | nil => intro st; rfl
  | cons d ds ih =>
      intro st
      simp only [List.map_cons, List.foldl_cons]
      have hstep : undigitizeStep st (min d 4) = undigitizeStep st d := by
        obtain ⟨out, acc, pow⟩ := st
        by_cases hd : d < 4
        · rw [show min d 4 = d from by omega]
        · rw [undigitizeStep, undigitizeStep, if_neg (by omega), if_neg hd]
      rw [hstep, ih]

end LogicalInduction
