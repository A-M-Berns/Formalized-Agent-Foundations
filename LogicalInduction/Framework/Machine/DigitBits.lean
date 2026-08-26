/-
# The bit rendering of a digit stream

`MachineEfficientTrader` reads a machine's output word through `bitsToDigits`, which groups
three bits into a digit, most significant first. This file is the inverse: `digitsToBits`
writes a digit stream as bits, and `bitsToDigits_digitsToBits` says the reading recovers it,
for digits below eight.

The digits a `Nat.Partrec.Code` emits are arbitrary naturals, so they do not all fit in
three bits. They do not have to: `undigitizeStep` tests a digit only against `4`, so every
value from `4` up is the same block terminator, and `undigitize_map_min_four` says clamping
at `4` leaves the token stream — hence the trader — alone. Clamping is therefore what the
machine emits, and this file is where that convention is fixed and justified.
-/
import LogicalInduction.Framework.Criterion
import Mathlib.Tactic.IntervalCases

namespace LogicalInduction

/-- The three bits `bitsToDigits` reads back as the digit `d`, most significant first. -/
def digitBits (d : ℕ) : List Bool :=
  [(d / 4) % 2 == 1, (d / 2) % 2 == 1, d % 2 == 1]

@[simp] lemma length_digitBits (d : ℕ) : (digitBits d).length = 3 := rfl

lemma digitAt_digitBits (d : ℕ) (hd : d < 8) (rest : List Bool) :
    digitAt (digitBits d ++ rest) 0 = d := by
  interval_cases d <;> simp [digitAt, digitBits, b2n]

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

lemma bitsToDigits_digitBits (d : ℕ) (hd : d < 8) (rest : List Bool) :
    bitsToDigits (digitBits d ++ rest) = d :: bitsToDigits rest := by
  have hlen : (digitBits d ++ rest).length / 3 = rest.length / 3 + 1 := by
    simp only [List.length_append, length_digitBits]
    omega
  rw [bitsToDigits, hlen, List.range_succ_eq_map, List.map_cons, List.map_map,
    digitAt_digitBits d hd rest, bitsToDigits]
  exact congrArg _ (List.map_congr_left (fun i _ => digitAt_digitBits_succ d i rest))

/-- Encode a digit stream as bits, three bits per digit. -/
def digitsToBits (ds : List ℕ) : List Bool := ds.flatMap digitBits

lemma bitsToDigits_digitsToBits : ∀ ds : List ℕ, (∀ d ∈ ds, d < 8) →
    bitsToDigits (digitsToBits ds) = ds
  | [], _ => rfl
  | d :: ds, h => by
      rw [digitsToBits, List.flatMap_cons,
        bitsToDigits_digitBits d (h d (List.mem_cons_self ..)) _]
      congr 1
      exact bitsToDigits_digitsToBits ds (fun x hx => h x (List.mem_cons_of_mem _ hx))

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
