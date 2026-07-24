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

/-- The total trader emulated by one clock/program tuple (token-model decode). -/
def TraderProgram.trader (p : TraderProgram) : Trader where
  strat n := strategyOfTokens n (p.tokens n)

/-- The total trader emulated by one clock/program tuple, read through the digit layer
(digit-model decode). -/
def TraderProgram.trader₂ (p : TraderProgram) : Trader where
  strat n := strategyOfTokens n (undigitize (p.tokens n))

/-- The concrete natural-indexed trader enumeration, covering **both** emission models:
even indices decode the token model, odd indices the digit model.  This is what lets one
firm dominate the digit-metered class while every token-model certificate still indexes
in unchanged. -/
def enumeratedTrader (j : ℕ) : Trader :=
  if j % 2 = 1 then (traderProgramAt (j / 2)).trader₂
  else (traderProgramAt (j / 2)).trader

/-- Coverage half of the paper's redundant enumeration: every token-model e.c. trader
occurs as the exact extensional output of one concrete program tuple. -/
lemma exists_traderProgram_eq (Tr : Trader) (hTr : EfficientlyComputableTok Tr) :
    ∃ p : TraderProgram, p.trader = Tr := by
  obtain ⟨lengthCode, tokenCode, a, k, h⟩ := hTr
  let p : TraderProgram := ⟨lengthCode, tokenCode, a, k⟩
  refine ⟨p, ?_⟩
  simpa [TraderProgram.trader, TraderProgram.tokens, TraderProgram.clock,
    clockedTrader] using h

/-- Digit-model coverage: every digit-model e.c. trader occurs as the digit decode of one
concrete program tuple. -/
lemma exists_traderProgram₂_eq (Tr : Trader) (hTr : EfficientlyComputableTok₂ Tr) :
    ∃ p : TraderProgram, p.trader₂ = Tr := by
  obtain ⟨lengthCode, tokenCode, a, k, h⟩ := hTr
  let p : TraderProgram := ⟨lengthCode, tokenCode, a, k⟩
  refine ⟨p, ?_⟩
  simpa [TraderProgram.trader₂, TraderProgram.tokens, TraderProgram.clock,
    clockedTrader₂] using h

/-- Every even entry is token-model e.c.; total bounded emulation is part of the
definition, not an unproved compiler assumption. -/
lemma enumeratedTrader_even_ecTok (j : ℕ) :
    EfficientlyComputableTok (enumeratedTrader (2 * j)) := by
  let p := traderProgramAt j
  refine ⟨p.lengthCode, p.tokenCode, p.coefficient, p.degree, ?_⟩
  rw [enumeratedTrader, if_neg (by omega), Nat.mul_div_cancel_left j (by norm_num)]
  rfl

/-- Every odd entry is digit-model e.c. -/
lemma enumeratedTrader_odd_ecTok₂ (j : ℕ) :
    EfficientlyComputableTok₂ (enumeratedTrader (2 * j + 1)) := by
  let p := traderProgramAt j
  refine ⟨p.lengthCode, p.tokenCode, p.coefficient, p.degree, ?_⟩
  rw [enumeratedTrader, if_pos (by omega), show (2 * j + 1) / 2 = j by omega]
  rfl

/-- `prop:enumeration`, coverage clause: every token-model efficiently computable trader
occurs in the concrete natural-indexed sequence (at an even index). -/
lemma exists_enumeratedTrader_eq (Tr : Trader) (hTr : EfficientlyComputableTok Tr) :
    ∃ j : ℕ, enumeratedTrader j = Tr := by
  obtain ⟨p, hp⟩ := exists_traderProgram_eq Tr hTr
  refine ⟨2 * p.index, ?_⟩
  rw [enumeratedTrader, if_neg (by omega),
    Nat.mul_div_cancel_left p.index (by norm_num), traderProgramAt_index]
  exact hp

/-- `prop:enumeration`, digit-model coverage clause: every digit-model efficiently
computable trader occurs in the concrete natural-indexed sequence (at an odd index). -/
lemma exists_enumeratedTrader₂_eq (Tr : Trader) (hTr : EfficientlyComputableTok₂ Tr) :
    ∃ j : ℕ, enumeratedTrader j = Tr := by
  obtain ⟨p, hp⟩ := exists_traderProgram₂_eq Tr hTr
  refine ⟨2 * p.index + 1, ?_⟩
  rw [enumeratedTrader, if_pos (by omega),
    show (2 * p.index + 1) / 2 = p.index by omega, traderProgramAt_index]
  exact hp

end LogicalInduction
