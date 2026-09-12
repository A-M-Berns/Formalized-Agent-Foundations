import LogicalInduction.Framework.Machine.DigitArithFP

/-!
# `UnaryRuler` — the machine reading of a count

A machine cannot take a `ℕ → ℕ` parameter as a number: its input is a word, and the only
thing it reads off that word for free is a *length*.  So the machine reading of a count —
a term count, a segment count, a reindexing day map — is the **unary ruler**

    fun z : List Bool => List.replicate (f z.length) false   ∈   Complexity.FP,

the function that, handed the unary numeral for `n`, writes out `f n` marks.  This file
names that predicate and builds its closure calculus.

## Why a class of its own

`Framework/Machine/WriteOutMachine.lean` declares the six machine readings of an emitted
*stream* (`MachineTokenStream`, `MachineSpliceStream`, `MachineSentenceCodes`, …).  A count is not a stream: it is a number that *reindexes* one,
and the two-role rule says it therefore gets its own reading.  Where a count is read as a
*value* written into a stream rather than as a reindexer, the reading is
`MachineDigits`, and `MachineDigits.ofUnaryRuler` is the bridge.

## Direction of the bridge

`UnaryRuler.of_polyFueled` (`Framework/Machine/WriteOutMachine.lean`, stated there because it
needs the write-out layer) turns a fuel certificate `PolyFueled c f` into `UnaryRuler f`.
**No converse is claimed.**  A ruler is a polynomial-time *machine*; a fuel certificate is a
`Nat.Partrec.Code` clocked by a polynomial, and recovering one from the other would be a
statement about P and the fuel model that this development does not have — a P-versus-L
flavoured containment; the `dd:fuel` model card in `Framework/Emission/Computable.lean`
states the calibration in full, and `Framework/Machine/WriteOutMachine.lean`'s *Reach*
section spells out why the converse is open rather than merely unproved.  So the proved
relation is one-way — every fuel certificate yields a ruler — and `UnaryRuler` is the weaker
hypothesis, every consumer stated at it the stronger theorem.  Whether it is *strictly*
weaker is not settled here: no converse is provided, and the absence of one is not a proof
that none exists.

## The length side condition

Each combinator below records what it needs beyond membership.  Most need nothing: the
ruler's *own* output length is the value it denotes, so `Complexity.FP`'s built-in
polynomial output bound already bounds the number.  The two devices this file exists for —
`UnaryRuler.segPrefix` and `UnaryRuler.segLocate`, the machine twins of
`segPrefix_polyFueled` and `segLocate_polyFueled` — are folds, and there the bound is taken
once, at the largest input, from `Cobham.output_length_poly_of_mem_FP` applied to the
segment ruler; it is never compounded inside the loop.  That is what
`TokenFold.concatUnaryPair_mem_FP` already arranges.
-/

namespace LogicalInduction

open Complexity.Cobham

/-- **A unary ruler for `f`**: some polynomial-time machine, handed the unary numeral for
`n`, writes out exactly `f n` marks.

This is the machine reading of a fuel-metered *count* — a value that reindexes a stream —
as `MachineTokenStream` and friends are the machine readings of emitted streams.  A fuel
certificate gives one (`UnaryRuler.of_polyFueled`); no converse is claimed.  The side
condition a client might expect — a bound on `f` — is not needed, because the ruler's own
output length *is* the value, and `Complexity.FP` bounds an output's length by a polynomial
in the input's. -/
def UnaryRuler (f : ℕ → ℕ) : Prop :=
  (fun z : List Bool => List.replicate (f z.length) false) ∈ Complexity.FP

/-- Congruence: only the values of the count matter. -/
lemma UnaryRuler.of_eq {f g : ℕ → ℕ} (h : UnaryRuler f) (he : ∀ n, f n = g n) :
    UnaryRuler g := by
  have hm : (fun z : List Bool => List.replicate (f z.length) false) ∈ Complexity.FP := h
  have heq : (fun z : List Bool => List.replicate (f z.length) false)
      = fun z : List Bool => List.replicate (g z.length) false := by
    funext z; rw [he]
  show (fun z : List Bool => List.replicate (g z.length) false) ∈ Complexity.FP
  rwa [heq] at hm

/-! ## The calculus

Each lemma below is the machine twin of a `PolyFueled` closure lemma in
`Framework/Emission/Computable.lean`, and its docstring names the length side condition it
carries.  A consumer assembles the ruler directly from these; converting a fuel code with
`UnaryRuler.of_polyFueled` is the route in for a caller who holds one already. -/

/-- **A constant count.** The machine ignores its input and writes a fixed word.
No length side condition. -/
lemma UnaryRuler.const (k : ℕ) : UnaryRuler (fun _ => k) :=
  FPFold.constFn_mem_FP (List.replicate k false)

/-- **The identity count.** `Cobham.mulLenFn_mem_FP` against a one-bit constant recolours
`Complexity.unaryLength_mem_FP`'s `true` marks to the `false` marks the ruler convention
uses. No length side condition. -/
lemma UnaryRuler.id : UnaryRuler (fun n => n) := by
  show (fun z : List Bool => List.replicate z.length false) ∈ Complexity.FP
  simpa using Complexity.Cobham.mulLenFn_mem_FP Complexity.unaryLength_mem_FP
    (FPFold.constFn_mem_FP [true])

/-- **Composition.** The inner ruler's output is the unary numeral the outer one reads, so
this is one `Complexity.mem_FP_comp`. No length side condition: the intermediate word's
length is `g n`, which the inner machine already bounded. -/
lemma UnaryRuler.comp {f g : ℕ → ℕ} (hf : UnaryRuler f) (hg : UnaryRuler g) :
    UnaryRuler (fun n => f (g n)) := by
  have h := Complexity.mem_FP_comp hg hf
  show (fun z : List Bool => List.replicate (f (g z.length)) false) ∈ Complexity.FP
  have heq : ((fun z : List Bool => List.replicate (f z.length) false) ∘
      fun z : List Bool => List.replicate (g z.length) false)
      = fun z : List Bool => List.replicate (f (g z.length)) false := by
    funext z; simp
  rwa [heq] at h

/-- **Addition**, as concatenation of the two rulers. No length side condition. -/
lemma UnaryRuler.add {f g : ℕ → ℕ} (hf : UnaryRuler f) (hg : UnaryRuler g) :
    UnaryRuler (fun n => f n + g n) := by
  have h := Complexity.Cobham.appendFn_mem_FP hf hg
  show (fun z : List Bool => List.replicate (f z.length + g z.length) false) ∈ Complexity.FP
  have heq : (fun z : List Bool =>
      List.replicate (f z.length) false ++ List.replicate (g z.length) false)
      = fun z : List Bool => List.replicate (f z.length + g z.length) false := by
    funext z; simp
  rwa [heq] at h

/-- **Multiplication**, as `Cobham.mulLenFn_mem_FP` on the two rulers' lengths.
No length side condition. -/
lemma UnaryRuler.mul {f g : ℕ → ℕ} (hf : UnaryRuler f) (hg : UnaryRuler g) :
    UnaryRuler (fun n => f n * g n) := by
  show (fun z : List Bool => List.replicate (f z.length * g z.length) false) ∈ Complexity.FP
  simpa using Complexity.Cobham.mulLenFn_mem_FP hf hg

/-- **Truncated subtraction**, as dropping the subtrahend's marks off the minuend's ruler
(`TokenFold.dropLenFn_mem_FP`): `List.length_drop` *is* `Nat.sub`, so the truncation at zero
is the machine's own behaviour rather than a clamp the proof adds.
No length side condition. -/
lemma UnaryRuler.sub {f g : ℕ → ℕ} (hf : UnaryRuler f) (hg : UnaryRuler g) :
    UnaryRuler (fun n => f n - g n) := by
  have h := TokenFold.dropLenFn_mem_FP hg hf
  show (fun z : List Bool => List.replicate (f z.length - g z.length) false) ∈ Complexity.FP
  have heq : (fun z : List Bool =>
      (List.replicate (f z.length) false).drop (List.replicate (g z.length) false).length)
      = fun z : List Bool => List.replicate (f z.length - g z.length) false := by
    funext z; simp
  rwa [heq] at h

/-- **Successor.** One extra mark. No length side condition. -/
lemma UnaryRuler.succ {f : ℕ → ℕ} (hf : UnaryRuler f) : UnaryRuler (fun n => f n + 1) :=
  hf.add (UnaryRuler.const 1)

/-- **Dispatch on a count being zero**, the machine twin of the fuel side's `ifzSel`: the
test is itself a ruler, and a ruler is zero exactly when its word is empty, which
`TokenFold.ifEqLen_mem_FP` decides at `0`. This is the same test `MachineTokenStream.ifZero`
makes on a stream. No length side condition. -/
lemma UnaryRuler.ifZero {t a b : ℕ → ℕ} (ht : UnaryRuler t) (ha : UnaryRuler a)
    (hb : UnaryRuler b) : UnaryRuler (fun n => if t n = 0 then a n else b n) := by
  have h := TokenFold.ifEqLen_mem_FP ht 0 ha hb
  show (fun z : List Bool =>
    List.replicate (if t z.length = 0 then a z.length else b z.length) false) ∈ Complexity.FP
  have heq : (fun z : List Bool =>
      if (List.replicate (t z.length) false).length = 0
        then List.replicate (a z.length) false else List.replicate (b z.length) false)
      = fun z : List Bool =>
        List.replicate (if t z.length = 0 then a z.length else b z.length) false := by
    funext z
    by_cases hz : t z.length = 0
    · rw [if_pos (by simp [hz]), if_pos hz]
    · rw [if_neg (by simpa using hz), if_neg hz]
  rwa [heq] at h

/-- **Equality of two counts**, as the symmetric difference tested against zero: the two
truncated subtractions cancel exactly when the counts agree, and `UnaryRuler.ifZero` decides
that. No length side condition. -/
lemma UnaryRuler.eqFlag {a b : ℕ → ℕ} (ha : UnaryRuler a) (hb : UnaryRuler b) :
    UnaryRuler (fun n => if a n = b n then 1 else 0) :=
  (((ha.sub hb).add (hb.sub ha)).ifZero (UnaryRuler.const 1) (UnaryRuler.const 0)).of_eq
    (fun n => by split_ifs <;> omega)

/-- **A fixed threshold between two fixed counts**: the test is on the input's own length,
so `TokenFold.ifLeLen_mem_FP` decides it against a literal. No length side condition. -/
lemma UnaryRuler.ite_lt_const (i a b : ℕ) :
    UnaryRuler (fun n => if n < i then a else b) := by
  show (fun z : List Bool => List.replicate (if z.length < i then a else b) false)
    ∈ Complexity.FP
  cases i with
  | zero => simpa using FPFold.constFn_mem_FP (List.replicate b false)
  | succ i =>
      have h := TokenFold.ifLeLen_mem_FP (A := fun z : List Bool => z) Complexity.id_mem_FP i
        (FPFold.constFn_mem_FP (List.replicate a false))
        (FPFold.constFn_mem_FP (List.replicate b false))
      have heq : (fun z : List Bool =>
          if z.length ≤ i then List.replicate a false else List.replicate b false)
          = fun z : List Bool => List.replicate (if z.length < i + 1 then a else b) false := by
        funext z
        by_cases hz : z.length ≤ i
        · rw [if_pos hz, if_pos (by omega)]
        · rw [if_neg hz, if_neg (by omega)]
      rwa [heq] at h

/-! ### Unpairing

`Nat.unpair` is not length arithmetic, so the tally has to go through digits: render it as a
base-four digit word (`TokenFold.Increment.unaryToDigits`), unpair there
(`DigitFP.unpairFstW` / `.unpairSndW`, which is the square-root loop's case split and needs
no squaring), and read the digit word back as a length with the guarded expansion
`TokenFold.LEUnary.unaryOfDigitsLE_le_mem_FP`.  **The guard is the whole length side
condition**: a `k`-digit word denotes up to `4 ^ k` marks, so the read-back needs a cap, and
here the cap is the input's own length, since `m.unpair.i ≤ m`. -/

private lemma unaryTally_mem_FP :
    (fun z : List Bool =>
      TokenFold.Increment.unaryToDigits (List.replicate z.length true)) ∈ Complexity.FP :=
  TokenFold.Increment.unaryToDigits_mem_FP Complexity.unaryLength_mem_FP

private lemma isDigitWord_unaryToDigits (u : List Bool) :
    DigitFP.IsDigitWord (TokenFold.Increment.unaryToDigits u) := by
  rw [TokenFold.Increment.unaryToDigits_eq]
  exact DigitFP.isDigitWord_digitsToBits (TokenFold.Increment.unaryDigits_lt u.length)

private lemma wordVal_unaryTally (z : List Bool) :
    DigitFP.wordVal (TokenFold.Increment.unaryToDigits (List.replicate z.length true))
      = z.length := by
  rw [DigitFP.wordVal, TokenFold.Increment.unaryToDigits_val, List.length_replicate]

/-- **The left component of `Nat.unpair` is a ruler.** Route: digitize the tally, unpair the
digit word, read it back capped by the input's own length — legitimate because
`m.unpair.1 ≤ m`. -/
lemma UnaryRuler.unpairFst : UnaryRuler (fun n => n.unpair.1) := by
  have hV : (fun z : List Bool => DigitFP.unpairFstW
      (TokenFold.Increment.unaryToDigits (List.replicate z.length true))) ∈ Complexity.FP := by
    simpa [Function.comp_def] using
      Complexity.mem_FP_comp unaryTally_mem_FP DigitFP.unpairFstW_mem_FP
  have h := TokenFold.LEUnary.unaryOfDigitsLE_le_mem_FP hV Complexity.unaryLength_mem_FP
  have heq : (fun z : List Bool => List.replicate
        (min (digitVal (bitsToDigits (DigitFP.unpairFstW
          (TokenFold.Increment.unaryToDigits (List.replicate z.length true)))))
          (List.replicate z.length true).length) true)
      = fun z : List Bool => List.replicate z.length.unpair.1 true := by
    funext z
    have hspec := DigitFP.unpairW_spec
      (isDigitWord_unaryToDigits (List.replicate z.length true))
    have hval : digitVal (bitsToDigits (DigitFP.unpairFstW
        (TokenFold.Increment.unaryToDigits (List.replicate z.length true))))
        = z.length.unpair.1 := by
      rw [show digitVal (bitsToDigits (DigitFP.unpairFstW
          (TokenFold.Increment.unaryToDigits (List.replicate z.length true))))
          = DigitFP.wordVal (DigitFP.unpairFstW
            (TokenFold.Increment.unaryToDigits (List.replicate z.length true))) from rfl,
        hspec.2.2.1, wordVal_unaryTally z]
    rw [hval, List.length_replicate, min_eq_left (Nat.unpair_left_le z.length)]
  rw [heq] at h
  show (fun z : List Bool => List.replicate z.length.unpair.1 false) ∈ Complexity.FP
  simpa using Complexity.Cobham.mulLenFn_mem_FP h (FPFold.constFn_mem_FP [true])

/-- **The right component of `Nat.unpair` is a ruler.** As `UnaryRuler.unpairFst`, with the
cap justified by `Nat.unpair_right_le`. -/
lemma UnaryRuler.unpairSnd : UnaryRuler (fun n => n.unpair.2) := by
  have hV : (fun z : List Bool => DigitFP.unpairSndW
      (TokenFold.Increment.unaryToDigits (List.replicate z.length true))) ∈ Complexity.FP := by
    simpa [Function.comp_def] using
      Complexity.mem_FP_comp unaryTally_mem_FP DigitFP.unpairSndW_mem_FP
  have h := TokenFold.LEUnary.unaryOfDigitsLE_le_mem_FP hV Complexity.unaryLength_mem_FP
  have heq : (fun z : List Bool => List.replicate
        (min (digitVal (bitsToDigits (DigitFP.unpairSndW
          (TokenFold.Increment.unaryToDigits (List.replicate z.length true)))))
          (List.replicate z.length true).length) true)
      = fun z : List Bool => List.replicate z.length.unpair.2 true := by
    funext z
    have hspec := DigitFP.unpairW_spec
      (isDigitWord_unaryToDigits (List.replicate z.length true))
    have hval : digitVal (bitsToDigits (DigitFP.unpairSndW
        (TokenFold.Increment.unaryToDigits (List.replicate z.length true))))
        = z.length.unpair.2 := by
      rw [show digitVal (bitsToDigits (DigitFP.unpairSndW
          (TokenFold.Increment.unaryToDigits (List.replicate z.length true))))
          = DigitFP.wordVal (DigitFP.unpairSndW
            (TokenFold.Increment.unaryToDigits (List.replicate z.length true))) from rfl,
        hspec.2.2.2, wordVal_unaryTally z]
    rw [hval, List.length_replicate, min_eq_left (Nat.unpair_right_le z.length)]
  rw [heq] at h
  show (fun z : List Bool => List.replicate z.length.unpair.2 false) ∈ Complexity.FP
  simpa using Complexity.Cobham.mulLenFn_mem_FP h (FPFold.constFn_mem_FP [true])

/-- **Pairing two counts is a ruler.** `TokenFold.unaryPair_mem_FP` assembles
`Nat.pair` out of two length products, three concatenations and one length comparison.
No length side condition. -/
lemma UnaryRuler.pair {f g : ℕ → ℕ} (hf : UnaryRuler f) (hg : UnaryRuler g) :
    UnaryRuler (fun n => Nat.pair (f n) (g n)) := by
  have h := TokenFold.unaryPair_mem_FP hf hg
  simp only [List.length_replicate] at h
  show (fun z : List Bool => List.replicate (Nat.pair (f z.length) (g z.length)) false)
    ∈ Complexity.FP
  simpa using Complexity.Cobham.mulLenFn_mem_FP h (FPFold.constFn_mem_FP [true])

/-! ### The two prefix-scan devices

`segPrefix` and `segLocate` (`Framework/Emission/Computable.lean`) are the variable-width
concatenation's arithmetic: the running sum of segment lengths, and the block enclosing a
given token offset.  The fuel side computes both by primitive recursion
(`segPrefix_polyFueled`, `segLocate_polyFueled`); the machine side computes both by the
*same* fold, `TokenFold.concatUnaryPair_mem_FP`, run at a ruler rather than at a stream:
concatenating `k` copies of the segment ruler's output makes a word whose length is the
prefix sum, and concatenating one mark per block that fits makes a word whose length is the
locator.

The polynomial cap is taken **once**, by `Cobham.output_length_poly_of_mem_FP` inside that
fold, at the largest paired index the loop reaches — never compounded per iteration. -/

/-- Every block up to `k` fits when block `k` does, by monotonicity of the prefix sum. -/
private lemma segLocate_count_eq_self (lenFn : ℕ → ℕ) (n i : ℕ) : ∀ k : ℕ,
    LogicalInduction.segPrefix lenFn n k ≤ i →
    ((List.range k).flatMap fun j =>
        if LogicalInduction.segPrefix lenFn n (j + 1) ≤ i then [false]
        else ([] : List Bool)).length = k
  | 0, _ => by simp
  | k + 1, hk => by
      have hprev : LogicalInduction.segPrefix lenFn n k ≤ i :=
        le_trans (segPrefix_mono lenFn n (Nat.le_succ k)) hk
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append,
        segLocate_count_eq_self lenFn n i k hprev, if_pos hk]
      simp

/-- **The locator is a count.** Marking each block `j + 1 ≤ k` whose prefix sum still fits
under `i` produces `segLocate lenFn n i k` marks, because the blocks that fit are an initial
segment. This is what lets the machine compute the locator by the same concatenating fold
the prefix sum uses, instead of by the fuel side's downward scan. -/
private lemma segLocate_eq_count (lenFn : ℕ → ℕ) (n i : ℕ) : ∀ k : ℕ,
    ((List.range k).flatMap fun j =>
        if LogicalInduction.segPrefix lenFn n (j + 1) ≤ i then [false]
        else ([] : List Bool)).length = LogicalInduction.segLocate lenFn n i k
  | 0 => by simp [LogicalInduction.segLocate]
  | k + 1 => by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append,
        LogicalInduction.segLocate]
      by_cases hk : LogicalInduction.segPrefix lenFn n (k + 1) ≤ i
      · rw [if_pos hk, if_pos hk,
          segLocate_count_eq_self lenFn n i k
            (le_trans (segPrefix_mono lenFn n (Nat.le_succ k)) hk)]
        simp
      · rw [if_neg hk, if_neg hk, segLocate_eq_count lenFn n i k]
        simp

/-- **The prefix sum of a ruler-metered segment length is a ruler.** The machine twin of
`segPrefix_polyFueled`, at the same argument packaging: the input `m` is `⟨n, k⟩`, the outer
index and the number of blocks.

The fold is `TokenFold.concatUnaryPair_mem_FP` with the segment ruler as its emitter: at
step `j` it rebuilds `unaryDay (Nat.pair n j)` and appends `lenFn (Nat.pair n j)` marks, so
the accumulated word's length is exactly the prefix sum.

Length side condition: none beyond the segment ruler's own membership. The state stays
polynomially bounded because `Cobham.output_length_poly_of_mem_FP` is applied once to that
ruler and the loop counter is clamped against the block count, so the bound is uniform in
the step rather than compounded through it. -/
lemma UnaryRuler.segPrefix {lenFn : ℕ → ℕ} (hlen : UnaryRuler lenFn) :
    UnaryRuler (fun m => LogicalInduction.segPrefix lenFn m.unpair.1 m.unpair.2) := by
  have hF : (fun z : List Bool => List.replicate (lenFn z.length) false) ∈ Complexity.FP := hlen
  have hR : (fun z : List Bool => List.replicate z.length.unpair.2 false) ∈ Complexity.FP :=
    UnaryRuler.unpairSnd
  have hD : (fun z : List Bool => List.replicate z.length.unpair.1 false) ∈ Complexity.FP :=
    UnaryRuler.unpairFst
  obtain ⟨G, hG, hGeq⟩ := TokenFold.concatUnaryPair_mem_FP hF hR hD
  have hGlen : ∀ z : List Bool, (G z).length
      = LogicalInduction.segPrefix lenFn z.length.unpair.1 z.length.unpair.2 := by
    intro z
    rw [hGeq z]
    simp only [List.length_replicate]
    exact length_flatMap_eq_segPrefix (fun q => List.replicate (lenFn q) false) lenFn
      z.length.unpair.1 (fun j => by simp) _
  show (fun z : List Bool => List.replicate
      (LogicalInduction.segPrefix lenFn z.length.unpair.1 z.length.unpair.2) false)
    ∈ Complexity.FP
  have h := Complexity.Cobham.mulLenFn_mem_FP hG (FPFold.constFn_mem_FP [true])
  have heq : (fun z : List Bool =>
      List.replicate ((G z).length * ([true] : List Bool).length) false)
      = fun z : List Bool => List.replicate
        (LogicalInduction.segPrefix lenFn z.length.unpair.1 z.length.unpair.2) false := by
    funext z; rw [hGlen z]; simp
  rwa [heq] at h

/-- **The prefix-scan block locator is a ruler.** The machine twin of
`segLocate_polyFueled`, at the same argument packaging: the input `m` is `⟨⟨n, i⟩, k⟩` — the
outer index, the token offset, and the number of blocks to scan.

Where the fuel side scans downwards from `k`, the machine runs the *same* concatenating fold
as `UnaryRuler.segPrefix`, emitting one mark per block that still fits under `i`
(`segLocate_eq_count`); the comparison is at the tally level
(`TokenFold.selectHeadFn_leFlag_mem_FP`), never on digit words, so no digit comparison
device is involved.

Length side condition: none beyond the segment ruler's own membership; the emitter's output
is one bit. -/
lemma UnaryRuler.segLocate {lenFn : ℕ → ℕ} (hlen : UnaryRuler lenFn) :
    UnaryRuler (fun m => LogicalInduction.segLocate lenFn
      m.unpair.1.unpair.1 m.unpair.1.unpair.2 m.unpair.2) := by
  have hA : UnaryRuler (fun m => LogicalInduction.segPrefix lenFn
      m.unpair.1.unpair.1 (m.unpair.2 + 1)) :=
    ((UnaryRuler.segPrefix hlen).comp
      ((UnaryRuler.unpairFst.comp UnaryRuler.unpairFst).pair UnaryRuler.unpairSnd.succ)).of_eq
      (fun m => by simp)
  have hB : UnaryRuler (fun m => m.unpair.1.unpair.2) :=
    UnaryRuler.unpairSnd.comp UnaryRuler.unpairFst
  have hF : (fun z : List Bool =>
      if LogicalInduction.segPrefix lenFn z.length.unpair.1.unpair.1 (z.length.unpair.2 + 1)
          ≤ z.length.unpair.1.unpair.2 then [false] else ([] : List Bool)) ∈ Complexity.FP := by
    have hAm : (fun z : List Bool => List.replicate
        (LogicalInduction.segPrefix lenFn z.length.unpair.1.unpair.1 (z.length.unpair.2 + 1))
        false) ∈ Complexity.FP := hA
    have hBm : (fun z : List Bool => List.replicate z.length.unpair.1.unpair.2 false)
        ∈ Complexity.FP := hB
    have h := TokenFold.selectHeadFn_leFlag_mem_FP hBm hAm
      (FPFold.constFn_mem_FP [false]) (FPFold.constFn_mem_FP ([] : List Bool))
    simp only [List.length_replicate] at h
    exact h
  have hR : (fun z : List Bool => List.replicate z.length.unpair.2 false) ∈ Complexity.FP :=
    UnaryRuler.unpairSnd
  have hD : (fun z : List Bool => List.replicate z.length.unpair.1 false) ∈ Complexity.FP :=
    UnaryRuler.unpairFst
  obtain ⟨G, hG, hGeq⟩ := TokenFold.concatUnaryPair_mem_FP hF hR hD
  have hGlen : ∀ z : List Bool, (G z).length = LogicalInduction.segLocate lenFn
      z.length.unpair.1.unpair.1 z.length.unpair.1.unpair.2 z.length.unpair.2 := by
    intro z
    rw [hGeq z]
    simp only [List.length_replicate, Nat.unpair_pair]
    exact segLocate_eq_count lenFn z.length.unpair.1.unpair.1 z.length.unpair.1.unpair.2 _
  show (fun z : List Bool => List.replicate (LogicalInduction.segLocate lenFn
      z.length.unpair.1.unpair.1 z.length.unpair.1.unpair.2 z.length.unpair.2) false)
    ∈ Complexity.FP
  have h := Complexity.Cobham.mulLenFn_mem_FP hG (FPFold.constFn_mem_FP [true])
  have heq : (fun z : List Bool =>
      List.replicate ((G z).length * ([true] : List Bool).length) false)
      = fun z : List Bool => List.replicate (LogicalInduction.segLocate lenFn
        z.length.unpair.1.unpair.1 z.length.unpair.1.unpair.2 z.length.unpair.2) false := by
    funext z; rw [hGlen z]; simp
  rwa [heq] at h

/-! ### Capped doubling

Length arithmetic cannot reach `2 ^ n`: a ruler's output word *is* the value it denotes, so
an exponential count would be an exponentially long output, which `Complexity.FP` forbids.
What it can reach is `2 ^ n` **capped** by another ruler — `min (2 ^ a n) (c n)` — since the
capped value never exceeds `c n`, which the cap's own membership already bounds
polynomially.  That is exactly the shape an output-sensitive *graph* test needs: deciding
`2 ^ n = m` needs only `min (2 ^ n) (m + 1)`, because `min (2 ^ n) (m + 1) = m ↔ 2 ^ n = m`.

The device is `FPFold.foldlBits_mem_FP`, the bounded-iteration combinator whose step reads a
parameter block beside the state, run over `a n` marks with the cap as the parameter block
and a single mark as the initial state.  Each step doubles the state word and truncates it
back to the cap's width, so the state length is bounded by the cap on *every* prefix — which
is the combinator's hypothesis, quantified over the machine's malformed inputs too and not
only over the intended trajectory.  The truncation is written as `drop` twice
(`|s| - (|s| - |W|) = min |W| |s|`), the fork exposing `drop` but no `take`.

Length side condition: the cap must be positive, since the loop starts from one mark. -/

/-- One capped doubling step, reading the cap from `fstBlock` and the state from `sndBlock`
exactly as `FPFold.foldlBits` packages them. -/
private def capDoubleStep (w : List Bool) : List Bool :=
  (sndBlock w ++ sndBlock w).drop
    (((sndBlock w ++ sndBlock w).drop (fstBlock w).length).length)

private lemma capDoubleStep_mem_FP : capDoubleStep ∈ Complexity.FP := by
  have hs : (fun w : List Bool => sndBlock w ++ sndBlock w) ∈ Complexity.FP :=
    Complexity.Cobham.appendFn_mem_FP sndBlock_mem_FP sndBlock_mem_FP
  exact TokenFold.dropLenFn_mem_FP (TokenFold.dropLenFn_mem_FP fstBlock_mem_FP hs) hs

private lemma capDoubleStep_length (W st : List Bool) :
    (capDoubleStep (Complexity.pair W st)).length
      = min W.length (st.length + st.length) := by
  simp only [capDoubleStep, fstBlock_pair, sndBlock_pair, List.length_drop,
    List.length_append]
  omega

private lemma capDoubleStep_replicate (W : List Bool) (a : ℕ) :
    capDoubleStep (Complexity.pair W (List.replicate a false))
      = List.replicate (min W.length (a + a)) false := by
  have hcat : List.replicate a false ++ List.replicate a false
      = List.replicate (a + a) false := (List.replicate_add a a false).symm
  simp only [capDoubleStep, fstBlock_pair, sndBlock_pair, hcat, List.drop_replicate,
    List.length_replicate]
  congr 1
  omega

/-- The state word after `j` capped doublings is `min (2 ^ j) |W|` marks. -/
private lemma foldlBits_capDoubleStep (W : List Bool) (hW : 0 < W.length) : ∀ j : ℕ,
    FPFold.foldlBits capDoubleStep capDoubleStep W [false] (List.replicate j false)
      = List.replicate (min (2 ^ j) W.length) false
  | 0 => by
      simp only [List.replicate_zero, FPFold.foldlBits_nil, pow_zero]
      rw [min_eq_left hW]
      rfl
  | (j + 1) => by
      have hstep := foldlBits_capDoubleStep W hW j
      rw [List.replicate_succ', FPFold.foldlBits_append_singleton]
      simp only [cond_false]
      rw [hstep, capDoubleStep_replicate]
      congr 1
      rw [pow_succ]
      omega

/-- The state word never outgrows the cap, on every input the combinator's clamp must be
discharged on and not only on the all-`false` trajectory the caller supplies. -/
private lemma foldlBits_capDoubleStep_length (W : List Bool) :
    ∀ u st : List Bool, st.length ≤ max 1 W.length →
      (FPFold.foldlBits capDoubleStep capDoubleStep W st u).length ≤ max 1 W.length
  | [], _, h => by simpa using h
  | (b :: bs), st, h => by
      rw [FPFold.foldlBits_cons]
      have hb : (bif b then capDoubleStep else capDoubleStep) (Complexity.pair W st)
          = capDoubleStep (Complexity.pair W st) := by cases b <;> rfl
      rw [hb]
      refine foldlBits_capDoubleStep_length W bs _ ?_
      rw [capDoubleStep_length]
      omega

/-- **A capped power of two is a ruler**: `min (2 ^ a n) (c n)` whenever `a` and `c` are
rulers and the cap `c` is positive.  The uncapped `2 ^ a n` is *not* a ruler and cannot be —
its word would be exponentially long — so the cap is not a convenience but the whole reason
the count stays inside `Complexity.FP`.

Length side condition: `0 < c n`, the loop's initial mark. -/
lemma UnaryRuler.two_pow_min {a c : ℕ → ℕ} (ha : UnaryRuler a) (hc : UnaryRuler c)
    (hpos : ∀ n, 0 < c n) : UnaryRuler (fun n => min (2 ^ a n) (c n)) := by
  have hS : (fun z : List Bool => List.replicate (a z.length) false) ∈ Complexity.FP := ha
  have hW : (fun z : List Bool => List.replicate (c z.length) false) ∈ Complexity.FP := hc
  have h := FPFold.foldlBits_mem_FP capDoubleStep_mem_FP capDoubleStep_mem_FP hW hS
    [false] Polynomial.X (fun z u _ => by
      have hb := foldlBits_capDoubleStep_length (List.replicate (c z.length) false) u [false]
        (by simp)
      simp only [Polynomial.eval_X, List.length_replicate] at hb ⊢
      have hc0 := hpos z.length
      omega)
  have heq : (fun z : List Bool => FPFold.foldlBits capDoubleStep capDoubleStep
      (List.replicate (c z.length) false) [false] (List.replicate (a z.length) false))
      = fun z : List Bool =>
        List.replicate (min (2 ^ a z.length) (c z.length)) false := by
    funext z
    rw [foldlBits_capDoubleStep _ (by simpa using hpos z.length) (a z.length)]
    simp
  show (fun z : List Bool => List.replicate (min (2 ^ a z.length) (c z.length)) false)
    ∈ Complexity.FP
  rwa [heq] at h

end LogicalInduction
