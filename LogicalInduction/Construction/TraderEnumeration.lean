/-
# Redundant enumeration of efficiently computable traders (`prop:enumeration`)

The construction needs more than a complexity predicate: it needs a total, clocked
emulator whose index contains both the exact serialized-length program and the token
program.  This file starts that construction and proves the coverage half: every
`EfficientlyComputableTok` trader is reproduced extensionally by one emulator program.
-/
import LogicalInduction.Framework.Computable

namespace LogicalInduction

open Nat.Partrec.Code

/-- The concrete program data enumerated by the TradingFirm. -/
structure TraderProgram where
  lengthCode : Nat.Partrec.Code
  tokenCode : Nat.Partrec.Code
  coefficient : ℕ
  degree : ℕ

/-- Decode an arbitrary natural as a partial-recursive program, using the zero program
for malformed indices. -/
def codeAt (i : ℕ) : Nat.Partrec.Code :=
  (Encodable.decode i).getD Nat.Partrec.Code.zero

@[simp] theorem codeAt_encode (c : Nat.Partrec.Code) :
    codeAt (Encodable.encode c) = c := by
  simp [codeAt]

/-- A canonical natural index for a clock/program tuple. -/
def TraderProgram.index (p : TraderProgram) : ℕ :=
  Nat.pair
    (Nat.pair
      (Nat.pair (Encodable.encode p.lengthCode) (Encodable.encode p.tokenCode))
      p.coefficient)
    p.degree

/-- Decode every natural into a clock/program tuple.  Invalid program codes become the
zero code, making this a total enumeration. -/
def traderProgramAt (j : ℕ) : TraderProgram :=
  let outer := Nat.unpair j
  let middle := Nat.unpair outer.1
  let inner := Nat.unpair middle.1
  ⟨codeAt inner.1, codeAt inner.2, middle.2, outer.2⟩

@[simp] theorem traderProgramAt_index (p : TraderProgram) :
    traderProgramAt p.index = p := by
  cases p
  simp [traderProgramAt, TraderProgram.index]

/-- The common unary polynomial clock carried by a trader program. -/
def TraderProgram.clock (p : TraderProgram) (n : ℕ) : ℕ :=
  p.coefficient * (n + 1) ^ p.degree + p.coefficient

/-- Run this tuple through the common bounded emulator. -/
def TraderProgram.tokens (p : TraderProgram) (n : ℕ) : List ℕ :=
  clockedTokens p.lengthCode p.tokenCode (p.clock n) n

/-- The total trader emulated by one clock/program tuple. -/
def TraderProgram.trader (p : TraderProgram) : Trader where
  strat n := strategyOfTokens n (p.tokens n)

/-- The concrete natural-indexed trader enumeration. -/
def enumeratedTrader (j : ℕ) : Trader := (traderProgramAt j).trader

/-- Coverage half of the paper's redundant enumeration: every e.c. trader occurs as the
exact extensional output of one concrete program tuple. -/
theorem exists_traderProgram_eq (Tr : Trader) (hTr : EfficientlyComputableTok Tr) :
    ∃ p : TraderProgram, p.trader = Tr := by
  obtain ⟨lengthCode, tokenCode, a, k, h⟩ := hTr
  let p : TraderProgram := ⟨lengthCode, tokenCode, a, k⟩
  refine ⟨p, ?_⟩
  simpa [TraderProgram.trader, TraderProgram.tokens, TraderProgram.clock,
    clockedTrader] using h

/-- Every entry in the enumeration is e.c.; total bounded emulation is part of the
definition, not an unproved compiler assumption. -/
theorem enumeratedTrader_ecTok (j : ℕ) : EfficientlyComputableTok (enumeratedTrader j) := by
  let p := traderProgramAt j
  refine ⟨p.lengthCode, p.tokenCode, p.coefficient, p.degree, ?_⟩
  rfl

/-- `prop:enumeration`, coverage clause: every efficiently computable trader occurs in the
concrete natural-indexed sequence. -/
theorem exists_enumeratedTrader_eq (Tr : Trader) (hTr : EfficientlyComputableTok Tr) :
    ∃ j : ℕ, enumeratedTrader j = Tr := by
  obtain ⟨p, hp⟩ := exists_traderProgram_eq Tr hTr
  exact ⟨p.index, by simpa [enumeratedTrader] using hp⟩

end LogicalInduction
