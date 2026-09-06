import LogicalInduction.Construction.Conditioning.Transduction

/-! # The conditioning transduction: frame legs and the `def:ec` transport

The second half of the machine-model rendering of the conditioning translation.
`Construction/Conditioning/Transduction.lean` builds the word-level automaton `condStepR`
and the passes that read a priced stream; this module adds the two frame legs, assembles the
whole transduction, and proves the transport theorems.  Both halves are in namespace
`CondStep`.

Two declarations here are paper-facing: `conditionedTranslation_preserves_machine` and
`eventualConditionedTranslation_preserves_machine` render `thm:scon` — closure of the
trader class under conditioning — at `def:ec`'s own class `MachineEfficientTrader`.
Everything else is a definition of the transduction they are assembled from, or a `lemma`
about it, and carries no `Paper node` line.

## The frame legs and the join

`frameEmitR` at `second = false` and at `second = true` is a fixed concatenation tree with
five word-valued leaves, giving `rpnFrameOutput` (`decodeBits_frameLegW`); `safeFrameW`
joins the legs on the acceptance word; and `condOutputOf`/`condOutputW` assemble the whole
transduction, which is `rpnConditionOutput` (`decodeBits_condOutputW`).  `rpnFrameRun` steps
with `rpnCondStep` and `rpnCondBuf` verbatim, so the frame pass is another client of the
same word-level automaton and only its emitter differs.

## The `def:ec` bridge and the finite-zero lane

The splicing emitter concatenates the condition block with other fragments, so it needs the
oracle's word to carry whole blocks.  `MachineSentenceBlocks` is that reading of `def:ec`'s
sentence class, and `machineSentenceBlocks_of_big` produces it from `BigSentenceCodes`
through `BigTokenStream.digitizeStream`, the downstream digit clamp `min · 4` being the
identity on a list of base-4 digits and terminators (`mem_digitize_le_four`).

`zeroEmitR` replaces the conditional-price expansion by the fixed run `[D, 1, ⌜1⌝, 8]` on
the finitely many days where the condition's price is zero; `mem_zeroDays_clamp` is what
lets that membership test read a clamped day.  The guard, the count, the budget codes, the
acceptance test and the frame join all take the priced stream as their input, so the
finite-zero lane reuses them unchanged and restates only the price pass.

## Consumers

`Construction/Conditioning/Endpoints.lean` packages the two theorems as criterion-level
endpoints.
-/

namespace LogicalInduction.CondStep

open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold
open LogicalInduction.RpnConditioning LogicalInduction.ConditioningCompile

/-! ## The frame pass

`rpnFrameRun` steps with `rpnCondStep` and `rpnCondBuf` verbatim, so the frame pass is
another client of the same word-level automaton and only its emitter differs.  That emitter
is a fixed concatenation tree — `rawMulTokens`, `rawMinTokens` and their relatives are all
`left ++ right ++ [op]` — with just five word-valued leaves: the buffered trade run, the
condition block, the day, and the two budget codes.  So the mirrors below are one line each,
and `decodeBits_append` carries the whole tree.

`rpnFrameOutput` then appends a trailing `[6]` conditional on the *final* mode, which is why
this pass reads `runFold`'s client state as well as its output. -/

/-! ### Word-level mirrors of the token constructors -/

/-- `rawConstTokens` on words: a rational's code block behind the constant tag. -/
def wConst (cBlk : List Bool) : List Bool := tokBits [1] ++ cBlk
/-- `rawAddTokens` on words. -/
def wAdd (l r : List Bool) : List Bool := l ++ r ++ tokBits [2]
/-- `rawMulTokens` on words. -/
def wMul (l r : List Bool) : List Bool := l ++ r ++ tokBits [3]
/-- `rawMaxTokens` on words. -/
def wMax (l r : List Bool) : List Bool := l ++ r ++ tokBits [4]
/-- `rawSafeRecipTokens` on words. -/
def wSafeRecip (a : List Bool) : List Bool := a ++ tokBits [5]

/-- A fixed rational's code, as a constant leaf. -/
def wRat (c : ℕ) : List Bool := wConst (tokBits [c])

lemma blockWF_wConst {cBlk : List Bool} (h : BlockWF cBlk) : BlockWF (wConst cBlk) :=
  (blockWF_tokBits _).append h
lemma blockWF_wAdd {l r : List Bool} (hl : BlockWF l) (hr : BlockWF r) :
    BlockWF (wAdd l r) := (hl.append hr).append (blockWF_tokBits _)
lemma blockWF_wMul {l r : List Bool} (hl : BlockWF l) (hr : BlockWF r) :
    BlockWF (wMul l r) := (hl.append hr).append (blockWF_tokBits _)
lemma blockWF_wMax {l r : List Bool} (hl : BlockWF l) (hr : BlockWF r) :
    BlockWF (wMax l r) := (hl.append hr).append (blockWF_tokBits _)
lemma blockWF_wSafeRecip {a : List Bool} (h : BlockWF a) : BlockWF (wSafeRecip a) :=
  h.append (blockWF_tokBits _)
lemma blockWF_wRat (c : ℕ) : BlockWF (wRat c) := blockWF_wConst (blockWF_tokBits _)

lemma decodeBits_wConst {cBlk : List Bool} {c : ℕ} (h : BlockWF cBlk)
    (hc : decodeBits cBlk = [c]) : decodeBits (wConst cBlk) = rawConstTokens c := by
  rw [wConst, decodeBits_append (blockWF_tokBits _) h, decodeBits_tokBits, hc,
    rawConstTokens]
  rfl

@[simp] lemma decodeBits_wRat (c : ℕ) : decodeBits (wRat c) = rawConstTokens c :=
  decodeBits_wConst (blockWF_tokBits _) (decodeBits_tokBits _)

lemma decodeBits_wAdd {l r : List Bool} (hl : BlockWF l) (hr : BlockWF r) :
    decodeBits (wAdd l r) = rawAddTokens (decodeBits l) (decodeBits r) := by
  rw [wAdd, decodeBits_append (hl.append hr) (blockWF_tokBits _),
    decodeBits_append hl hr, decodeBits_tokBits, rawAddTokens]

lemma decodeBits_wMul {l r : List Bool} (hl : BlockWF l) (hr : BlockWF r) :
    decodeBits (wMul l r) = rawMulTokens (decodeBits l) (decodeBits r) := by
  rw [wMul, decodeBits_append (hl.append hr) (blockWF_tokBits _),
    decodeBits_append hl hr, decodeBits_tokBits, rawMulTokens]

lemma decodeBits_wMax {l r : List Bool} (hl : BlockWF l) (hr : BlockWF r) :
    decodeBits (wMax l r) = rawMaxTokens (decodeBits l) (decodeBits r) := by
  rw [wMax, decodeBits_append (hl.append hr) (blockWF_tokBits _),
    decodeBits_append hl hr, decodeBits_tokBits, rawMaxTokens]

lemma decodeBits_wSafeRecip {a : List Bool} (h : BlockWF a) :
    decodeBits (wSafeRecip a) = rawSafeRecipTokens (decodeBits a) := by
  rw [wSafeRecip, decodeBits_append h (blockWF_tokBits _), decodeBits_tokBits,
    rawSafeRecipTokens]

/-! ### The derived constructors -/

/-- `rawMinTokens` on words. -/
def wMin (l r : List Bool) : List Bool :=
  wMul (wRat (Encodable.encode (-1 : ℚ)))
    (wMax (wMul (wRat (Encodable.encode (-1 : ℚ))) l)
      (wMul (wRat (Encodable.encode (-1 : ℚ))) r))

/-- `rawLowerSafeRecipTokens` on words: the reciprocal floored at `ε`. -/
def wLowerSafeRecip (d : List Bool) (ε : ℚ) : List Bool :=
  wMul (wRat (Encodable.encode (1 / ε)))
    (wSafeRecip (wMul (wRat (Encodable.encode (1 / ε))) d))

/-- `rawAbsTokens` on words. -/
def wAbs (a : List Bool) : List Bool :=
  wMax a (wMul (wRat (Encodable.encode (-1 : ℚ))) a)

/-- `rawClip01Tokens` on words. -/
def wClip01 (a : List Bool) : List Bool :=
  wMax (wRat (Encodable.encode (0 : ℚ))) (wMin (wRat (Encodable.encode (1 : ℚ))) a)

/-- `rawConditioningGateTokens` on words, with the two budget codes as word arguments. -/
def wGate (ratio magnitude bcW ibcW : List Bool) : List Bool :=
  wClip01 (wMul
    (wAdd (wAdd (wRat (Encodable.encode (1 : ℚ)))
        (wMul (wConst bcW) (wSafeRecip magnitude)))
      (wMul (wRat (Encodable.encode (-1 : ℚ))) ratio))
    (wMul (wConst ibcW) (wMax (wRat (Encodable.encode (1 : ℚ))) magnitude)))

lemma blockWF_wMin {l r : List Bool} (hl : BlockWF l) (hr : BlockWF r) :
    BlockWF (wMin l r) :=
  blockWF_wMul (blockWF_wRat _)
    (blockWF_wMax (blockWF_wMul (blockWF_wRat _) hl)
      (blockWF_wMul (blockWF_wRat _) hr))

lemma blockWF_wLowerSafeRecip {d : List Bool} (h : BlockWF d) (ε : ℚ) :
    BlockWF (wLowerSafeRecip d ε) :=
  blockWF_wMul (blockWF_wRat _)
    (blockWF_wSafeRecip (blockWF_wMul (blockWF_wRat _) h))

lemma blockWF_wAbs {a : List Bool} (h : BlockWF a) : BlockWF (wAbs a) :=
  blockWF_wMax h (blockWF_wMul (blockWF_wRat _) h)

lemma blockWF_wClip01 {a : List Bool} (h : BlockWF a) : BlockWF (wClip01 a) :=
  blockWF_wMax (blockWF_wRat _) (blockWF_wMin (blockWF_wRat _) h)

lemma blockWF_wGate {ratio magnitude bcW ibcW : List Bool}
    (hr : BlockWF ratio) (hm : BlockWF magnitude) (hb : BlockWF bcW)
    (hi : BlockWF ibcW) : BlockWF (wGate ratio magnitude bcW ibcW) :=
  blockWF_wClip01 (blockWF_wMul
    (blockWF_wAdd (blockWF_wAdd (blockWF_wRat _)
        (blockWF_wMul (blockWF_wConst hb) (blockWF_wSafeRecip hm)))
      (blockWF_wMul (blockWF_wRat _) hr))
    (blockWF_wMul (blockWF_wConst hi) (blockWF_wMax (blockWF_wRat _) hm)))

lemma decodeBits_wMin {l r : List Bool} (hl : BlockWF l) (hr : BlockWF r) :
    decodeBits (wMin l r) = rawMinTokens (decodeBits l) (decodeBits r) := by
  rw [wMin, rawMinTokens,
    decodeBits_wMul (blockWF_wRat _)
      (blockWF_wMax (blockWF_wMul (blockWF_wRat _) hl)
        (blockWF_wMul (blockWF_wRat _) hr)),
    decodeBits_wMax (blockWF_wMul (blockWF_wRat _) hl)
      (blockWF_wMul (blockWF_wRat _) hr),
    decodeBits_wMul (blockWF_wRat _) hl, decodeBits_wMul (blockWF_wRat _) hr,
    decodeBits_wRat]

lemma decodeBits_wLowerSafeRecip {d : List Bool} (h : BlockWF d) (ε : ℚ) :
    decodeBits (wLowerSafeRecip d ε) = rawLowerSafeRecipTokens (decodeBits d) ε := by
  rw [wLowerSafeRecip, rawLowerSafeRecipTokens,
    decodeBits_wMul (blockWF_wRat _)
      (blockWF_wSafeRecip (blockWF_wMul (blockWF_wRat _) h)),
    decodeBits_wSafeRecip (blockWF_wMul (blockWF_wRat _) h),
    decodeBits_wMul (blockWF_wRat _) h, decodeBits_wRat]

lemma decodeBits_wAbs {a : List Bool} (h : BlockWF a) :
    decodeBits (wAbs a) = rawAbsTokens (decodeBits a) := by
  rw [wAbs, rawAbsTokens, decodeBits_wMax h (blockWF_wMul (blockWF_wRat _) h),
    decodeBits_wMul (blockWF_wRat _) h, decodeBits_wRat]

lemma decodeBits_wClip01 {a : List Bool} (h : BlockWF a) :
    decodeBits (wClip01 a) = rawClip01Tokens (decodeBits a) := by
  rw [wClip01, rawClip01Tokens,
    decodeBits_wMax (blockWF_wRat _) (blockWF_wMin (blockWF_wRat _) h),
    decodeBits_wMin (blockWF_wRat _) h]
  simp only [decodeBits_wRat]

lemma decodeBits_wGate {ratio magnitude bcW ibcW : List Bool} {bc ibc : ℕ}
    (hr : BlockWF ratio) (hm : BlockWF magnitude) (hb : BlockWF bcW)
    (hi : BlockWF ibcW) (hbc : decodeBits bcW = [bc]) (hibc : decodeBits ibcW = [ibc]) :
    decodeBits (wGate ratio magnitude bcW ibcW)
      = rawConditioningGateTokens (decodeBits ratio) (decodeBits magnitude) bc ibc := by
  rw [wGate, rawConditioningGateTokens,
    decodeBits_wClip01 (blockWF_wMul
      (blockWF_wAdd (blockWF_wAdd (blockWF_wRat _)
          (blockWF_wMul (blockWF_wConst hb) (blockWF_wSafeRecip hm)))
        (blockWF_wMul (blockWF_wRat _) hr))
      (blockWF_wMul (blockWF_wConst hi) (blockWF_wMax (blockWF_wRat _) hm))),
    decodeBits_wMul
      (blockWF_wAdd (blockWF_wAdd (blockWF_wRat _)
          (blockWF_wMul (blockWF_wConst hb) (blockWF_wSafeRecip hm)))
        (blockWF_wMul (blockWF_wRat _) hr))
      (blockWF_wMul (blockWF_wConst hi) (blockWF_wMax (blockWF_wRat _) hm)),
    decodeBits_wAdd (blockWF_wAdd (blockWF_wRat _)
        (blockWF_wMul (blockWF_wConst hb) (blockWF_wSafeRecip hm)))
      (blockWF_wMul (blockWF_wRat _) hr),
    decodeBits_wAdd (blockWF_wRat _)
      (blockWF_wMul (blockWF_wConst hb) (blockWF_wSafeRecip hm)),
    decodeBits_wMul (blockWF_wConst hb) (blockWF_wSafeRecip hm),
    decodeBits_wMul (blockWF_wRat _) hr,
    decodeBits_wMul (blockWF_wConst hi) (blockWF_wMax (blockWF_wRat _) hm),
    decodeBits_wMax (blockWF_wRat _) hm,
    decodeBits_wSafeRecip hm,
    decodeBits_wConst hb hbc, decodeBits_wConst hi hibc]
  simp only [decodeBits_wRat]

/-! ### The frame emission -/

/-- `rpnFramePriceSym` on words: a sentence block's price at a day block. -/
def wPriceSym (blockW dayBlk : List Bool) : List Bool := tokBits [0] ++ blockW ++ dayBlk

/-- `rpnFrameRatioSym` on words: the conditional-ratio value at expanded sentence blocks. -/
def wRatioSym (conjW psiW dayBlk : List Bool) (ε : ℚ) : List Bool :=
  wMul (wPriceSym conjW dayBlk) (wLowerSafeRecip (wPriceSym psiW dayBlk) ε)

/-- `rpnFrameGate` on words: the conditioning gate over the two `letE` variables. -/
def wFrameGate (bcW ibcW : List Bool) : List Bool :=
  wGate (tokBits [7, 0]) (wAbs (tokBits [7, 1])) bcW ibcW

/-- The leg body: the conditional-ratio value times the gate, closed by `8`. -/
def wLegBody (second : Bool) (ε : ℚ) (blkW bufW dayBlk bcW ibcW : List Bool) : List Bool :=
  if second then
    wRatioSym (tokBits [3] ++ bufW ++ blkW) blkW dayBlk ε ++
      wMul (wRat (Encodable.encode (-1 : ℚ)))
        (wMul (wMin (tokBits [7, 1]) (wMul (tokBits [7, 1]) (wFrameGate bcW ibcW)))
          (tokBits [7, 0])) ++ tokBits [8]
  else
    wRatioSym (tokBits [3] ++ bufW ++ blkW) blkW dayBlk ε ++
      wMin (tokBits [7, 1]) (wMul (tokBits [7, 1]) (wFrameGate bcW ibcW)) ++ tokBits [8]

/-- `rpnFrameEmit` on words. -/
def wFrameEmit (second : Bool) (ε : ℚ) (blkW bufW dayBlk bcW ibcW : List Bool) :
    List Bool :=
  wLegBody second ε blkW bufW dayBlk bcW ibcW ++ tokBits [8, 6] ++
    (if second then blkW else tokBits [3] ++ bufW ++ blkW)

lemma blockWF_wPriceSym {blockW dayBlk : List Bool} (hb : BlockWF blockW)
    (hd : BlockWF dayBlk) : BlockWF (wPriceSym blockW dayBlk) :=
  ((blockWF_tokBits _).append hb).append hd

lemma decodeBits_wPriceSym {blockW dayBlk : List Bool} {day : ℕ} (hb : BlockWF blockW)
    (hd : BlockWF dayBlk) (hday : decodeBits dayBlk = [day]) :
    decodeBits (wPriceSym blockW dayBlk) = rpnFramePriceSym (decodeBits blockW) day := by
  rw [wPriceSym, decodeBits_append ((blockWF_tokBits _).append hb) hd,
    decodeBits_append (blockWF_tokBits _) hb, decodeBits_tokBits, hday, rpnFramePriceSym]
  rfl

lemma blockWF_wRatioSym {conjW psiW dayBlk : List Bool} (hc : BlockWF conjW)
    (hp : BlockWF psiW) (hd : BlockWF dayBlk) (ε : ℚ) :
    BlockWF (wRatioSym conjW psiW dayBlk ε) :=
  blockWF_wMul (blockWF_wPriceSym hc hd)
    (blockWF_wLowerSafeRecip (blockWF_wPriceSym hp hd) ε)

lemma decodeBits_wRatioSym {conjW psiW dayBlk : List Bool} {day : ℕ} (hc : BlockWF conjW)
    (hp : BlockWF psiW) (hd : BlockWF dayBlk) (hday : decodeBits dayBlk = [day]) (ε : ℚ) :
    decodeBits (wRatioSym conjW psiW dayBlk ε)
      = rpnFrameRatioSym (decodeBits conjW) (decodeBits psiW) day ε := by
  rw [wRatioSym, rpnFrameRatioSym,
    decodeBits_wMul (blockWF_wPriceSym hc hd)
      (blockWF_wLowerSafeRecip (blockWF_wPriceSym hp hd) ε),
    decodeBits_wLowerSafeRecip (blockWF_wPriceSym hp hd) ε,
    decodeBits_wPriceSym hc hd hday, decodeBits_wPriceSym hp hd hday]

lemma blockWF_wFrameGate {bcW ibcW : List Bool} (hb : BlockWF bcW) (hi : BlockWF ibcW) :
    BlockWF (wFrameGate bcW ibcW) :=
  blockWF_wGate (blockWF_tokBits _) (blockWF_wAbs (blockWF_tokBits _)) hb hi

lemma decodeBits_wFrameGate {bcW ibcW : List Bool} {bc ibc : ℕ} (hb : BlockWF bcW)
    (hi : BlockWF ibcW) (hbc : decodeBits bcW = [bc]) (hibc : decodeBits ibcW = [ibc]) :
    decodeBits (wFrameGate bcW ibcW) = rpnFrameGate bc ibc := by
  rw [wFrameGate, rpnFrameGate,
    decodeBits_wGate (blockWF_tokBits _) (blockWF_wAbs (blockWF_tokBits _)) hb hi hbc hibc,
    decodeBits_wAbs (blockWF_tokBits _), decodeBits_tokBits, decodeBits_tokBits]

lemma blockWF_wFrameEmit (second : Bool) (ε : ℚ) {blkW bufW dayBlk bcW ibcW : List Bool}
    (hblk : BlockWF blkW) (hbuf : BlockWF bufW) (hd : BlockWF dayBlk)
    (hb : BlockWF bcW) (hi : BlockWF ibcW) :
    BlockWF (wFrameEmit second ε blkW bufW dayBlk bcW ibcW) := by
  have hC : BlockWF (tokBits [3] ++ bufW ++ blkW) :=
    ((blockWF_tokBits _).append hbuf).append hblk
  have hMin : BlockWF (wMin (tokBits [7, 1]) (wMul (tokBits [7, 1])
      (wFrameGate bcW ibcW))) :=
    blockWF_wMin (blockWF_tokBits _)
      (blockWF_wMul (blockWF_tokBits _) (blockWF_wFrameGate hb hi))
  have hbody : BlockWF (wLegBody second ε blkW bufW dayBlk bcW ibcW) := by
    rw [wLegBody]
    cases second
    · exact ((blockWF_wRatioSym hC hblk hd ε).append hMin).append (blockWF_tokBits _)
    · exact ((blockWF_wRatioSym hC hblk hd ε).append
        (blockWF_wMul (blockWF_wRat _)
          (blockWF_wMul hMin (blockWF_tokBits _)))).append (blockWF_tokBits _)
  rw [wFrameEmit]
  refine (hbody.append (blockWF_tokBits _)).append ?_
  cases second
  · exact hC
  · exact hblk

lemma decodeBits_wFrameEmit (second : Bool) (ε : ℚ)
    {blkW bufW dayBlk bcW ibcW : List Bool} {day bc ibc : ℕ}
    (hblk : BlockWF blkW) (hbuf : BlockWF bufW) (hd : BlockWF dayBlk)
    (hb : BlockWF bcW) (hi : BlockWF ibcW) (hday : decodeBits dayBlk = [day])
    (hbc : decodeBits bcW = [bc]) (hibc : decodeBits ibcW = [ibc]) :
    decodeBits (wFrameEmit second ε blkW bufW dayBlk bcW ibcW)
      = rpnFrameEmit second (decodeBits blkW) ε day bc ibc (decodeBits bufW) := by
  have hC : BlockWF (tokBits [3] ++ bufW ++ blkW) :=
    ((blockWF_tokBits _).append hbuf).append hblk
  have hCd : decodeBits (tokBits [3] ++ bufW ++ blkW)
      = 3 :: decodeBits bufW ++ decodeBits blkW := by
    rw [decodeBits_append ((blockWF_tokBits _).append hbuf) hblk,
      decodeBits_append (blockWF_tokBits _) hbuf, decodeBits_tokBits]
    rfl
  have hM1 : BlockWF (wMul (tokBits [7, 1]) (wFrameGate bcW ibcW)) :=
    blockWF_wMul (blockWF_tokBits _) (blockWF_wFrameGate hb hi)
  have hM1d : decodeBits (wMul (tokBits [7, 1]) (wFrameGate bcW ibcW))
      = rawMulTokens [7, 1] (rpnFrameGate bc ibc) := by
    rw [decodeBits_wMul (blockWF_tokBits _) (blockWF_wFrameGate hb hi),
      decodeBits_tokBits, decodeBits_wFrameGate hb hi hbc hibc]
  have hMin : BlockWF (wMin (tokBits [7, 1]) (wMul (tokBits [7, 1])
      (wFrameGate bcW ibcW))) := blockWF_wMin (blockWF_tokBits _) hM1
  have hMind : decodeBits (wMin (tokBits [7, 1]) (wMul (tokBits [7, 1])
      (wFrameGate bcW ibcW))) = rawMinTokens [7, 1] (rawMulTokens [7, 1]
        (rpnFrameGate bc ibc)) := by
    rw [decodeBits_wMin (blockWF_tokBits _) hM1, decodeBits_tokBits, hM1d]
  rw [wFrameEmit, rpnFrameEmit]
  cases second
  · simp only [Bool.false_eq_true, if_false]
    have hb0 : BlockWF (wLegBody false ε blkW bufW dayBlk bcW ibcW) := by
      rw [wLegBody]
      exact ((blockWF_wRatioSym hC hblk hd ε).append hMin).append (blockWF_tokBits _)
    rw [decodeBits_append (hb0.append (blockWF_tokBits _)) hC,
      decodeBits_append hb0 (blockWF_tokBits _), wLegBody]
    simp only [Bool.false_eq_true, if_false]
    rw [decodeBits_append ((blockWF_wRatioSym hC hblk hd ε).append hMin)
        (blockWF_tokBits _),
      decodeBits_append (blockWF_wRatioSym hC hblk hd ε) hMin,
      decodeBits_wRatioSym hC hblk hd hday ε, hCd, hMind]
    simp only [decodeBits_tokBits]
    simp [List.append_assoc]
  · simp only [if_true]
    have hb1 : BlockWF (wLegBody true ε blkW bufW dayBlk bcW ibcW) := by
      rw [wLegBody]
      exact ((blockWF_wRatioSym hC hblk hd ε).append
        (blockWF_wMul (blockWF_wRat _)
          (blockWF_wMul hMin (blockWF_tokBits _)))).append (blockWF_tokBits _)
    rw [decodeBits_append (hb1.append (blockWF_tokBits _)) hblk,
      decodeBits_append hb1 (blockWF_tokBits _), wLegBody]
    simp only [if_true]
    rw [decodeBits_append ((blockWF_wRatioSym hC hblk hd ε).append
          (blockWF_wMul (blockWF_wRat _)
            (blockWF_wMul hMin (blockWF_tokBits _)))) (blockWF_tokBits _),
      decodeBits_append (blockWF_wRatioSym hC hblk hd ε)
        (blockWF_wMul (blockWF_wRat _) (blockWF_wMul hMin (blockWF_tokBits _))),
      decodeBits_wRatioSym hC hblk hd hday ε, hCd,
      decodeBits_wMul (blockWF_wRat _) (blockWF_wMul hMin (blockWF_tokBits _)),
      decodeBits_wMul hMin (blockWF_tokBits _), hMind, decodeBits_wRat]
    simp only [decodeBits_tokBits]
    simp [List.append_assoc]

/-! ### The buffer with the current token appended

`rpnFrameEmitAt` emits at `buf ++ [t]`, the same word the buffer step builds. -/

lemma blockWF_bufSnoc (cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4)
    (hwf : BlockWF (csBuf cli)) :
    BlockWF (csBuf cli ++ digitsToBits cur ++ digitBits 4) := by
  rw [List.append_assoc]
  exact hwf.append (blockWF_run cur hcur)

lemma decodeBits_bufSnoc (cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4)
    (hwf : BlockWF (csBuf cli)) :
    decodeBits (csBuf cli ++ digitsToBits cur ++ digitBits 4)
      = csTokens cli ++ [digitVal cur] := by
  rw [List.append_assoc, decodeBits_append hwf (blockWF_run cur hcur),
    decodeBits_run cur hcur, csTokens]

/-! ### The frame parameter block

The frame emitter needs four things beyond the state: the day, the condition block, and
the two budget codes.  They travel in `runFold`'s parameter slot. -/

/-- The frame emitter's parameter block: the day, the condition block and the two budget
codes, packed for `runFold`'s parameter slot. -/
def frameParams (dayW blkW bcW ibcW : List Bool) : List Bool :=
  pair dayW (pair blkW (pair bcW ibcW))

/-- The trading day, in unary. -/
def fpDay (W : List Bool) : List Bool := fstBlock W
/-- The condition sentence's block. -/
def fpBlk (W : List Bool) : List Bool := fstBlock (sndBlock W)
/-- The frame budget's code, as one complete block. -/
def fpBc (W : List Bool) : List Bool := fstBlock (sndBlock (sndBlock W))
/-- The inverse budget's code, as one complete block. -/
def fpIbc (W : List Bool) : List Bool := sndBlock (sndBlock (sndBlock W))

@[simp] lemma fpDay_frameParams (d b c i : List Bool) :
    fpDay (frameParams d b c i) = d := by simp [fpDay, frameParams]
@[simp] lemma fpBlk_frameParams (d b c i : List Bool) :
    fpBlk (frameParams d b c i) = b := by simp [fpBlk, frameParams]
@[simp] lemma fpBc_frameParams (d b c i : List Bool) :
    fpBc (frameParams d b c i) = c := by simp [fpBc, frameParams]
@[simp] lemma fpIbc_frameParams (d b c i : List Bool) :
    fpIbc (frameParams d b c i) = i := by simp [fpIbc, frameParams]

/-! ### The branching emitter -/

/-- `rpnFrameEmitAt` on words: nothing at a price-block opener, the leg emission at a trade
run's exit, and the copied token everywhere else. -/
def frameEmitOf (second : Bool) (ε : ℚ) (W cli tw tok : List Bool) : List Bool :=
  if (csMode cli).length = 0 ∧ tw.length = 6 then []
  else if (csMode cli).length = 4 ∨ (csMode cli).length = 7 ∨ (csMode cli).length = 9 then
    (if (csModeStep cli tw).length = 0 then
      wFrameEmit second ε (fpBlk W) (csBuf cli ++ tok ++ digitBits 4)
        (unaryBlock (fpDay W)) (fpBc W) (fpIbc W)
     else [])
  else tok ++ digitBits 4

/-- The frame pass's word-level emitter. -/
def frameEmitW (second : Bool) (ε : ℚ) (v : List Bool) : List Bool :=
  frameEmitOf second ε (cvW v) (cvCli v) (clampTok v) (cvTok v)

/-- Its block-level reading. -/
def frameEmitR (second : Bool) (ε : ℚ) (W cli : List Bool) (cur : List ℕ) : List Bool :=
  frameEmitOf second ε W cli (List.replicate (min (digitVal cur) 20) true)
    (digitsToBits cur)

lemma frameEmitW_eq (second : Bool) (ε : ℚ) (W cli : List Bool) (cur : List ℕ)
    (hcur : ∀ d ∈ cur, d < 4) :
    frameEmitW second ε (pair W (pair cli (digitsToBits cur)))
      = frameEmitR second ε W cli cur := by
  rw [frameEmitW, frameEmitR, clampTok_pair W cli cur hcur]
  simp only [cvW, cvCli, cvTok, sndBlock_pair, fstBlock_pair]

lemma blockWF_frameEmitR (second : Bool) (ε : ℚ) (W cli : List Bool) (cur : List ℕ)
    (hcur : ∀ d ∈ cur, d < 4) (hwf : BlockWF (csBuf cli)) (hblk : BlockWF (fpBlk W))
    (hbc : BlockWF (fpBc W)) (hibc : BlockWF (fpIbc W)) :
    BlockWF (frameEmitR second ε W cli cur) := by
  rw [frameEmitR, frameEmitOf]
  split_ifs
  · exact BlockWF.nil
  · exact blockWF_wFrameEmit second ε hblk (blockWF_bufSnoc cli cur hcur hwf)
      (blockWF_unaryBlock _) hbc hibc
  · exact BlockWF.nil
  · exact blockWF_run cur hcur

lemma decodeBits_frameEmitR (second : Bool) (ε : ℚ) (W cli : List Bool) (cur : List ℕ)
    {bc ibc : ℕ} (hcur : ∀ d ∈ cur, d < 4) (hwf : BlockWF (csBuf cli))
    (hblk : BlockWF (fpBlk W)) (hbc : BlockWF (fpBc W)) (hibc : BlockWF (fpIbc W))
    (hbcv : decodeBits (fpBc W) = [bc]) (hibcv : decodeBits (fpIbc W) = [ibc]) :
    decodeBits (frameEmitR second ε W cli cur)
      = rpnFrameEmitAt second (decodeBits (fpBlk W)) ε (fpDay W).length bc ibc
          (csPack cli) (csTokens cli) (digitVal cur) := by
  have hmode : rcMode (csPack cli) = (csMode cli).length := by rw [csPack, rcMode_pack]
  have hstep := length_csModeStep cli cur
  have e6 : (min (digitVal cur) 20 = 6) ↔ (digitVal cur = 6) := by omega
  rw [frameEmitR, frameEmitOf, rpnFrameEmitAt, hmode, ← hstep]
  simp only [List.length_replicate, e6]
  by_cases h1 : (csMode cli).length = 0 ∧ digitVal cur = 6
  · rw [if_pos h1, if_pos h1, decodeBits_nil]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : (csMode cli).length = 4 ∨ (csMode cli).length = 7
        ∨ (csMode cli).length = 9
    · rw [if_pos h2, if_pos h2]
      by_cases h3 : (csModeStep cli (List.replicate (min (digitVal cur) 20) true)).length
          = 0
      · rw [if_pos h3, if_pos h3,
          decodeBits_wFrameEmit second ε hblk (blockWF_bufSnoc cli cur hcur hwf)
            (blockWF_unaryBlock _) hbc hibc (decodeBits_unaryBlock _) hbcv hibcv,
          decodeBits_bufSnoc cli cur hcur hwf]
      · rw [if_neg h3, if_neg h3, decodeBits_nil]
    · rw [if_neg h2, if_neg h2, decodeBits_run cur hcur]

/-! ### The frame fold -/

/-- The automaton's evolution does not depend on the emitter, so every client of
`condStepR` — the price pass, the guard, the count, the frame legs — ends in the same
state. -/
lemma csPack_runFold (EMITr : List Bool → List ℕ → List Bool) :
    ∀ (rs : List (List ℕ)) (cli out : List Bool),
      csPack (runFold condStepR EMITr cli out rs).1
        = (rs.map digitVal).foldl rpnCondStep (csPack cli)
  | [], cli, out => by rw [runFold, List.map_nil, List.foldl_nil]
  | r :: rs, cli, out => by
      rw [runFold, csPack_runFold EMITr rs, csPack_condStepR, List.map_cons,
        List.foldl_cons]

/-- The same on the paper side. -/
lemma rpnFrameRun_state (second : Bool) (blk : List ℕ) (ε : ℚ) (day bc ibc : ℕ) :
    ∀ (ts : List ℕ) (st : ℕ) (buf : List ℕ),
      (rpnFrameRun second blk ε day bc ibc (st, buf) ts).1.1 = ts.foldl rpnCondStep st
  | [], st, buf => rfl
  | t :: ts, st, buf => by
      rw [rpnFrameRun, List.foldl_cons,
        rpnFrameRun_state second blk ε day bc ibc ts (rpnCondStep st t)
          (rpnCondBuf st buf t)]

lemma decodeBits_runFold_frame (second : Bool) (ε : ℚ) (W : List Bool) {bc ibc : ℕ}
    (hblk : BlockWF (fpBlk W)) (hbc : BlockWF (fpBc W)) (hibc : BlockWF (fpIbc W))
    (hbcv : decodeBits (fpBc W) = [bc]) (hibcv : decodeBits (fpIbc W) = [ibc]) :
    ∀ (rs : List (List ℕ)) (cli out : List Bool),
      (∀ r ∈ rs, ∀ d ∈ r, d < 4) → BlockWF (csBuf cli) → BlockWF out →
      decodeBits (runFold condStepR (frameEmitR second ε W) cli out rs).2
        = decodeBits out
          ++ (rpnFrameRun second (decodeBits (fpBlk W)) ε (fpDay W).length bc ibc
                (csPack cli, csTokens cli) (rs.map digitVal)).2
  | [], cli, out, _, _, _ => by
      rw [runFold, List.map_nil, rpnFrameRun]
      simp
  | r :: rs, cli, out, hrs, hbuf, hout => by
      have hr : ∀ d ∈ r, d < 4 := hrs r (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rs, ∀ d ∈ q, d < 4 :=
        fun q hq => hrs q (List.mem_cons_of_mem _ hq)
      have hbuf' : BlockWF (csBuf (condStepR cli r)) := bufWF_condStepR cli r hr hbuf
      have hemit : BlockWF (frameEmitR second ε W cli r) :=
        blockWF_frameEmitR second ε W cli r hr hbuf hblk hbc hibc
      rw [runFold, decodeBits_runFold_frame second ε W hblk hbc hibc hbcv hibcv rs _ _
          hrest hbuf' (hout.append hemit),
        decodeBits_append hout hemit, csPack_condStepR, csTokens_condStepR cli r hr hbuf,
        decodeBits_frameEmitR second ε W cli r hr hbuf hblk hbc hibc hbcv hibcv,
        List.map_cons]
      rw [show (csPack cli, csTokens cli) = ((csPack cli, csTokens cli).1,
            (csPack cli, csTokens cli).2) from rfl, rpnFrameRun]
      simp only [List.append_assoc]

/-! ### The leg output and the gated join -/

/-- The trailing `6` of `rpnFrameOutput`: emitted when the run ends inside a trade
sentence.  This is the final-state read that `runFold_cli_mem_FP` exists for. -/
def frameTailOf (st : List Bool) : List Bool :=
  if (csMode st).length = 4 then tokBits [6]
  else if (csMode st).length = 7 then tokBits [6]
  else if (csMode st).length = 9 then tokBits [6]
  else []

lemma blockWF_frameTailOf (st : List Bool) : BlockWF (frameTailOf st) := by
  rw [frameTailOf]
  split_ifs <;> first | exact blockWF_tokBits _ | exact BlockWF.nil

lemma decodeBits_frameTailOf (st : List Bool) :
    decodeBits (frameTailOf st)
      = (if rcMode (csPack st) = 4 ∨ rcMode (csPack st) = 7 ∨ rcMode (csPack st) = 9
          then [6] else []) := by
  have hmode : rcMode (csPack st) = (csMode st).length := by rw [csPack, rcMode_pack]
  rw [frameTailOf, hmode]
  by_cases h4 : (csMode st).length = 4
  · rw [if_pos h4, if_pos (by tauto), decodeBits_tokBits]
  · by_cases h7 : (csMode st).length = 7
    · rw [if_neg h4, if_pos h7, if_pos (by tauto), decodeBits_tokBits]
    · by_cases h9 : (csMode st).length = 9
      · rw [if_neg h4, if_neg h7, if_pos h9, if_pos (by tauto), decodeBits_tokBits]
      · rw [if_neg h4, if_neg h7, if_neg h9, if_neg (by tauto), decodeBits_nil]

/-- One frame leg, on words. -/
def frameLegW (second : Bool) (ε : ℚ) (W Src : List Bool) : List Bool :=
  (runFold condStepR (frameEmitR second ε W) condInit [] (blockSplit (bitsToDigits Src)).1).2
    ++ frameTailOf
      (runFold condStepR (frameEmitR second ε W) condInit []
        (blockSplit (bitsToDigits Src)).1).1

lemma blockWF_frameBody (second : Bool) (ε : ℚ) (W : List Bool)
    (hblk : BlockWF (fpBlk W)) (hbc : BlockWF (fpBc W)) (hibc : BlockWF (fpIbc W)) :
    ∀ (rs : List (List ℕ)) (cli out : List Bool),
      (∀ r ∈ rs, ∀ d ∈ r, d < 4) → BlockWF (csBuf cli) → BlockWF out →
      BlockWF (runFold condStepR (frameEmitR second ε W) cli out rs).2
  | [], cli, out, _, _, hout => by rw [runFold]; exact hout
  | r :: rs, cli, out, hrs, hbuf, hout => by
      have hr : ∀ d ∈ r, d < 4 := hrs r (List.mem_cons_self ..)
      rw [runFold]
      exact blockWF_frameBody second ε W hblk hbc hibc rs _ _
        (fun q hq => hrs q (List.mem_cons_of_mem _ hq)) (bufWF_condStepR cli r hr hbuf)
        (hout.append (blockWF_frameEmitR second ε W cli r hr hbuf hblk hbc hibc))

lemma blockWF_frameLegW (second : Bool) (ε : ℚ) (W Src : List Bool)
    (hblk : BlockWF (fpBlk W)) (hbc : BlockWF (fpBc W)) (hibc : BlockWF (fpIbc W)) :
    BlockWF (frameLegW second ε W Src) :=
  BlockWF.append
    (blockWF_frameBody second ε W hblk hbc hibc _ condInit []
      (fun r hr => (blockSplit_digits_lt _).1 r hr) (by simpa using BlockWF.nil)
      BlockWF.nil)
    (blockWF_frameTailOf _)

lemma decodeBits_frameLegW (second : Bool) (ε : ℚ) (W Src : List Bool) {bc ibc : ℕ}
    (hblk : BlockWF (fpBlk W)) (hbc : BlockWF (fpBc W)) (hibc : BlockWF (fpIbc W))
    (hbcv : decodeBits (fpBc W) = [bc]) (hibcv : decodeBits (fpIbc W) = [ibc]) :
    decodeBits (frameLegW second ε W Src)
      = rpnFrameOutput second (decodeBits (fpBlk W)) ε (fpDay W).length bc ibc
          (undigitize (bitsToDigits Src)) := by
  have hmap : (blockSplit (bitsToDigits Src)).1.map digitVal
      = undigitize (bitsToDigits Src) := (undigitize_eq_blockSplit _).symm
  have hwfbody := blockWF_frameBody second ε W hblk hbc hibc
    (blockSplit (bitsToDigits Src)).1 condInit []
    (fun r hr => (blockSplit_digits_lt _).1 r hr) (by simpa using BlockWF.nil) BlockWF.nil
  have hbody := decodeBits_runFold_frame second ε W hblk hbc hibc hbcv hibcv
    (blockSplit (bitsToDigits Src)).1 condInit []
    (fun r hr => (blockSplit_digits_lt _).1 r hr) (by simpa using BlockWF.nil) BlockWF.nil
  have hstate := csPack_runFold (frameEmitR second ε W)
    (blockSplit (bitsToDigits Src)).1 condInit []
  rw [frameLegW, decodeBits_append hwfbody (blockWF_frameTailOf _), hbody,
    decodeBits_frameTailOf, hstate, csPack_condInit, csTokens_condInit, hmap,
    rpnFrameOutput, rpnFrameRun_state]
  simp

/-- The gated two-leg join: one leg when the run is not structurally accepted, both when it
is.  `acc` is the acceptance word, whose *length* is `rpnAcceptsRuns`. -/
def safeFrameW (ε : ℚ) (W Src acc : List Bool) : List Bool :=
  selectHead (emptyFlag acc) (frameLegW false ε W Src)
    (frameLegW false ε W Src ++ frameLegW true ε W Src)

lemma blockWF_safeFrameW (ε : ℚ) (W Src acc : List Bool)
    (hblk : BlockWF (fpBlk W)) (hbc : BlockWF (fpBc W)) (hibc : BlockWF (fpIbc W)) :
    BlockWF (safeFrameW ε W Src acc) := by
  rw [safeFrameW]
  cases acc with
  | nil =>
      rw [selectHead_emptyFlag_nil]
      exact blockWF_frameLegW false ε W Src hblk hbc hibc
  | cons b bs =>
      rw [selectHead_emptyFlag_cons]
      exact (blockWF_frameLegW false ε W Src hblk hbc hibc).append
        (blockWF_frameLegW true ε W Src hblk hbc hibc)

lemma decodeBits_safeFrameW (ε : ℚ) (W Src acc : List Bool) {bc ibc : ℕ}
    (hblk : BlockWF (fpBlk W)) (hbc : BlockWF (fpBc W)) (hibc : BlockWF (fpIbc W))
    (hbcv : decodeBits (fpBc W) = [bc]) (hibcv : decodeBits (fpIbc W) = [ibc])
    (hacc : acc.length = rpnAcceptsRuns (undigitize (bitsToDigits Src))) :
    decodeBits (safeFrameW ε W Src acc)
      = rpnSafeSeparatedFrameRuns (decodeBits (fpBlk W)) ε (fpDay W).length bc ibc
          (undigitize (bitsToDigits Src)) := by
  rw [safeFrameW, rpnSafeSeparatedFrameRuns]
  cases acc with
  | nil =>
      rw [selectHead_emptyFlag_nil, if_pos (by simpa using hacc.symm),
        decodeBits_frameLegW false ε W Src hblk hbc hibc hbcv hibcv]
  | cons b bs =>
      rw [selectHead_emptyFlag_cons, if_neg (by simp at hacc; omega),
        decodeBits_append (blockWF_frameLegW false ε W Src hblk hbc hibc)
          (blockWF_frameLegW true ε W Src hblk hbc hibc),
        decodeBits_frameLegW false ε W Src hblk hbc hibc hbcv hibcv,
        decodeBits_frameLegW true ε W Src hblk hbc hibc hbcv hibcv]

/-! ## The conditioning transduction, whole

`rpnConditionOutput` is the guarded price pass, the trade-run count turned into two budget
codes, and the gated two-leg frame join over the priced stream.  All of them are built
above; this is the assembly. -/

/-- The frame join over an arbitrary *priced* stream `Pr`.  The gated conditioning rewrite
and the finite-zero one differ only in `Pr`, so this one definition carries both. -/
def condOutputOf (ε : ℚ) (B Wf Pr : List Bool → List Bool) (z : List Bool) : List Bool :=
  safeFrameW ε
    (frameParams (Wf z) (B (Wf z)) (budgetOf Wf Pr z) (invBudgetOf Wf Pr z))
    (Pr z) (acceptsW Pr z)

/-- The gated conditioning transduction: the frame join over the guarded price pass. -/
def condOutputW (ε : ℚ) (B Wf Sf : List Bool → List Bool) : List Bool → List Bool :=
  condOutputOf ε B Wf (guardedPassW ε B Wf Sf)

/-- **The frame join computes what `rpnConditionOutput` and `rpnZeroAwareOutput` both ask
for**: the gated two-leg join at the day, the condition block, and the two budget codes of
the priced stream.  Which price rewrite produced that stream is invisible here. -/
lemma decodeBits_condOutputOf (ε : ℚ) (B Wf Pr : List Bool → List Bool)
    (hB : ∀ d, BlockWF (B (unaryDay d))) (z : List Bool)
    (hWz : Wf z = unaryDay (Wf z).length) :
    decodeBits (condOutputOf ε B Wf Pr z)
      = rpnSafeSeparatedFrameRuns (blocksOf B (Wf z).length) ε (Wf z).length
          (frameBudgetCode (Wf z).length
            (rpnTradeRuns (rcPack 0 0 0) (decodeBits (Pr z))))
          (frameInverseBudgetCode (Wf z).length
            (rpnTradeRuns (rcPack 0 0 0) (decodeBits (Pr z))))
          (decodeBits (Pr z)) := by
  obtain ⟨n, hWn⟩ : ∃ n, Wf z = unaryDay n := ⟨(Wf z).length, hWz⟩
  set P := frameParams (Wf z) (B (Wf z)) (budgetOf Wf Pr z) (invBudgetOf Wf Pr z) with hP
  have hblkW : fpBlk P = B (Wf z) := by rw [hP, fpBlk_frameParams]
  have hdayW : fpDay P = Wf z := by rw [hP, fpDay_frameParams]
  have hbcW : fpBc P = budgetOf Wf Pr z := by rw [hP, fpBc_frameParams]
  have hibcW : fpIbc P = invBudgetOf Wf Pr z := by rw [hP, fpIbc_frameParams]
  have hblk : BlockWF (fpBlk P) := by
    rw [hblkW, hWn]
    exact hB n
  have hbc : BlockWF (fpBc P) := by
    rw [hbcW, budgetOf]; exact blockWF_budgetCodeW _ _
  have hibc : BlockWF (fpIbc P) := by
    rw [hibcW, invBudgetOf]; exact blockWF_invBudgetCodeW _ _
  have hblkv : decodeBits (fpBlk P) = blocksOf B (Wf z).length := by
    rw [hblkW, hWn, blocksOf, length_unaryDay]
  have hbcv := hbcW ▸ decodeBits_budgetOf Wf Pr z
  have hibcv := hibcW ▸ decodeBits_invBudgetOf Wf Pr z
  have hacc := length_acceptsW Pr z
  rw [condOutputOf, ← hP,
    decodeBits_safeFrameW ε P _ _ hblk hbc hibc hbcv hibcv hacc, hblkv, hdayW]
  rfl

/-- **The gated conditioning transduction computes `rpnConditionOutput`.**  Decoding the
word the passes produce gives exactly the token-level transduction whose correctness is
`RpnConditioning.strategyOfTokens_rpnConditionOutput`. -/
lemma decodeBits_condOutputW (ε : ℚ) (B Wf Sf : List Bool → List Bool)
    (hB : ∀ d, BlockWF (B (unaryDay d))) (z : List Bool)
    (hWz : Wf z = unaryDay (Wf z).length) :
    decodeBits (condOutputW ε B Wf Sf z)
      = rpnConditionOutput (blocksOf B) ε (Wf z).length
          (undigitize (bitsToDigits (Sf z))) := by
  rw [condOutputW, decodeBits_condOutputOf ε B Wf _ hB z hWz, rpnConditionOutput,
    decodeBits_guardedPassW ε B Wf Sf hB z]

/-! ### The frame emitter's length

Every constructor is a concatenation, so the emission's length is a fixed constant — the
emission at empty arguments — plus a bounded multiple of each argument.  The constant is
*named* rather than computed: nothing here needs its value, only that it does not depend on
the stream. -/

/-- The frame emission's fixed part: the length of both legs at empty arguments. -/
def wFrameEmitConst (ε : ℚ) : ℕ :=
  (wFrameEmit false ε [] [] [] [] []).length
    + (wFrameEmit true ε [] [] [] [] []).length + 3

lemma length_wFrameEmit_le (second : Bool) (ε : ℚ)
    (blkW bufW dayBlk bcW ibcW : List Bool) :
    (wFrameEmit second ε blkW bufW dayBlk bcW ibcW).length
      ≤ wFrameEmitConst ε
        + 4 * (blkW.length + bufW.length + dayBlk.length + bcW.length + ibcW.length) := by
  rw [wFrameEmitConst]
  cases second <;>
    simp only [wFrameEmit, wLegBody, wRatioSym, wPriceSym, wFrameGate, wGate, wClip01,
      wMin, wMax, wMul, wAdd, wSafeRecip, wAbs, wLowerSafeRecip, wConst, wRat,
      List.length_append, List.length_nil, Bool.false_eq_true, if_false, if_true] <;>
    omega

lemma frameEmitW_length_le (second : Bool) (ε : ℚ) (W cli tok : List Bool) :
    (frameEmitW second ε (pair W (pair cli tok))).length
      ≤ (Polynomial.C (wFrameEmitConst ε + 30) + 32 * Polynomial.X).eval W.length
        + 4 * (cli.length + tok.length) := by
  have hW : cvW (pair W (pair cli tok)) = W := by simp [cvW]
  have hcli : cvCli (pair W (pair cli tok)) = cli := by simp [cvCli]
  have htok : cvTok (pair W (pair cli tok)) = tok := by simp [cvTok]
  have hblk : (fpBlk W).length ≤ W.length :=
    le_trans (fstBlock_length_le _) (sndBlock_length_le _)
  have hday : (fpDay W).length ≤ W.length := fstBlock_length_le _
  have hbc : (fpBc W).length ≤ W.length :=
    le_trans (fstBlock_length_le _) (le_trans (sndBlock_length_le _) (sndBlock_length_le _))
  have hibc : (fpIbc W).length ≤ W.length :=
    le_trans (sndBlock_length_le _) (le_trans (sndBlock_length_le _) (sndBlock_length_le _))
  have hdayB : (unaryBlock (fpDay W)).length ≤ 3 * W.length + 3 :=
    le_trans (length_unaryBlock_le _) (by omega)
  have hbuf : (csBuf cli).length ≤ cli.length :=
    le_trans (sndBlock_length_le _) (sndBlock_length_le _)
  have hconst : 3 ≤ wFrameEmitConst ε := by rw [wFrameEmitConst]; omega
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  rw [frameEmitW, hW, hcli, htok, frameEmitOf]
  split_ifs
  · simp
  · refine le_trans (length_wFrameEmit_le _ ε _ _ _ _ _) ?_
    simp only [List.length_append, length_digitBits]
    omega
  · simp
  · simp only [List.length_append, length_digitBits]
    omega

/-! ### The frame emitter is polynomial time -/

lemma wConst_mem_FP {C : List Bool → List Bool} (h : C ∈ FP) :
    (fun v => wConst (C v)) ∈ FP := appendFn_mem_FP (constFn_mem_FP _) h
lemma wAdd_mem_FP {L R : List Bool → List Bool} (hl : L ∈ FP) (hr : R ∈ FP) :
    (fun v => wAdd (L v) (R v)) ∈ FP :=
  appendFn_mem_FP (appendFn_mem_FP hl hr) (constFn_mem_FP _)
lemma wMul_mem_FP {L R : List Bool → List Bool} (hl : L ∈ FP) (hr : R ∈ FP) :
    (fun v => wMul (L v) (R v)) ∈ FP :=
  appendFn_mem_FP (appendFn_mem_FP hl hr) (constFn_mem_FP _)
lemma wMax_mem_FP {L R : List Bool → List Bool} (hl : L ∈ FP) (hr : R ∈ FP) :
    (fun v => wMax (L v) (R v)) ∈ FP :=
  appendFn_mem_FP (appendFn_mem_FP hl hr) (constFn_mem_FP _)
lemma wSafeRecip_mem_FP {A : List Bool → List Bool} (h : A ∈ FP) :
    (fun v => wSafeRecip (A v)) ∈ FP := appendFn_mem_FP h (constFn_mem_FP _)
lemma wRat_mem_FP (c : ℕ) : (fun _ : List Bool => wRat c) ∈ FP := constFn_mem_FP _

lemma wMin_mem_FP {L R : List Bool → List Bool} (hl : L ∈ FP) (hr : R ∈ FP) :
    (fun v => wMin (L v) (R v)) ∈ FP :=
  wMul_mem_FP (wRat_mem_FP _)
    (wMax_mem_FP (wMul_mem_FP (wRat_mem_FP _) hl) (wMul_mem_FP (wRat_mem_FP _) hr))

lemma wLowerSafeRecip_mem_FP {D : List Bool → List Bool} (h : D ∈ FP) (ε : ℚ) :
    (fun v => wLowerSafeRecip (D v) ε) ∈ FP :=
  wMul_mem_FP (wRat_mem_FP _) (wSafeRecip_mem_FP (wMul_mem_FP (wRat_mem_FP _) h))

lemma wAbs_mem_FP {A : List Bool → List Bool} (h : A ∈ FP) :
    (fun v => wAbs (A v)) ∈ FP := wMax_mem_FP h (wMul_mem_FP (wRat_mem_FP _) h)

lemma wClip01_mem_FP {A : List Bool → List Bool} (h : A ∈ FP) :
    (fun v => wClip01 (A v)) ∈ FP := wMax_mem_FP (wRat_mem_FP _) (wMin_mem_FP (wRat_mem_FP _) h)

lemma wGate_mem_FP {R M Bc Ibc : List Bool → List Bool} (hr : R ∈ FP) (hm : M ∈ FP)
    (hb : Bc ∈ FP) (hi : Ibc ∈ FP) :
    (fun v => wGate (R v) (M v) (Bc v) (Ibc v)) ∈ FP :=
  wClip01_mem_FP (wMul_mem_FP
    (wAdd_mem_FP (wAdd_mem_FP (wRat_mem_FP _)
        (wMul_mem_FP (wConst_mem_FP hb) (wSafeRecip_mem_FP hm)))
      (wMul_mem_FP (wRat_mem_FP _) hr))
    (wMul_mem_FP (wConst_mem_FP hi) (wMax_mem_FP (wRat_mem_FP _) hm)))

lemma wPriceSym_mem_FP {Bl D : List Bool → List Bool} (hb : Bl ∈ FP) (hd : D ∈ FP) :
    (fun v => wPriceSym (Bl v) (D v)) ∈ FP :=
  appendFn_mem_FP (appendFn_mem_FP (constFn_mem_FP _) hb) hd

lemma wRatioSym_mem_FP {C P D : List Bool → List Bool} (hc : C ∈ FP) (hp : P ∈ FP)
    (hd : D ∈ FP) (ε : ℚ) : (fun v => wRatioSym (C v) (P v) (D v) ε) ∈ FP :=
  wMul_mem_FP (wPriceSym_mem_FP hc hd)
    (wLowerSafeRecip_mem_FP (wPriceSym_mem_FP hp hd) ε)

lemma wFrameGate_mem_FP {Bc Ibc : List Bool → List Bool} (hb : Bc ∈ FP) (hi : Ibc ∈ FP) :
    (fun v => wFrameGate (Bc v) (Ibc v)) ∈ FP :=
  wGate_mem_FP (constFn_mem_FP _) (wAbs_mem_FP (constFn_mem_FP _)) hb hi

lemma wFrameEmit_mem_FP (second : Bool) (ε : ℚ)
    {Bl Bu D Bc Ibc : List Bool → List Bool} (hbl : Bl ∈ FP) (hbu : Bu ∈ FP)
    (hd : D ∈ FP) (hb : Bc ∈ FP) (hi : Ibc ∈ FP) :
    (fun v => wFrameEmit second ε (Bl v) (Bu v) (D v) (Bc v) (Ibc v)) ∈ FP := by
  have hC : (fun v => tokBits [3] ++ Bu v ++ Bl v) ∈ FP :=
    appendFn_mem_FP (appendFn_mem_FP (constFn_mem_FP _) hbu) hbl
  have hMin : (fun v => wMin (tokBits [7, 1]) (wMul (tokBits [7, 1])
      (wFrameGate (Bc v) (Ibc v)))) ∈ FP :=
    wMin_mem_FP (constFn_mem_FP _)
      (wMul_mem_FP (constFn_mem_FP _) (wFrameGate_mem_FP hb hi))
  have hbody : (fun v => wLegBody second ε (Bl v) (Bu v) (D v) (Bc v) (Ibc v)) ∈ FP := by
    cases second
    · simpa [wLegBody] using
        appendFn_mem_FP (appendFn_mem_FP (wRatioSym_mem_FP hC hbl hd ε) hMin)
          (constFn_mem_FP (tokBits [8]))
    · simpa [wLegBody] using
        appendFn_mem_FP (appendFn_mem_FP (wRatioSym_mem_FP hC hbl hd ε)
          (wMul_mem_FP (wRat_mem_FP _)
            (wMul_mem_FP hMin (constFn_mem_FP (tokBits [7, 0])))))
          (constFn_mem_FP (tokBits [8]))
  have htail : (fun v => if second then Bl v else tokBits [3] ++ Bu v ++ Bl v) ∈ FP := by
    cases second
    · simpa using hC
    · simpa using hbl
  simpa [wFrameEmit] using
    appendFn_mem_FP (appendFn_mem_FP hbody (constFn_mem_FP (tokBits [8, 6]))) htail

private lemma ifAndLen_mem_FP {A B X Y : List Bool → List Bool} (hA : A ∈ FP)
    (hB : B ∈ FP) (a b : ℕ) (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if (A z).length = a ∧ (B z).length = b then X z else Y z) ∈ FP := by
  have h := ifEqLen_mem_FP hA a (ifEqLen_mem_FP hB b hX hY) hY
  have heq : (fun z => if (A z).length = a then
        (if (B z).length = b then X z else Y z) else Y z)
      = fun z => if (A z).length = a ∧ (B z).length = b then X z else Y z := by
    funext z
    split_ifs <;> tauto
  rwa [heq] at h

lemma frameEmitW_mem_FP (second : Bool) (ε : ℚ) : frameEmitW second ε ∈ FP := by
  have hWs : (fun v => sndBlock (cvW v)) ∈ FP := mem_FP_comp cvW_mem_FP sndBlock_mem_FP
  have hWss : (fun v => sndBlock (sndBlock (cvW v))) ∈ FP :=
    mem_FP_comp hWs sndBlock_mem_FP
  have hblk : (fun v => fpBlk (cvW v)) ∈ FP := mem_FP_comp hWs fstBlock_mem_FP
  have hday : (fun v => fpDay (cvW v)) ∈ FP := mem_FP_comp cvW_mem_FP fstBlock_mem_FP
  have hbc : (fun v => fpBc (cvW v)) ∈ FP := mem_FP_comp hWss fstBlock_mem_FP
  have hibc : (fun v => fpIbc (cvW v)) ∈ FP := mem_FP_comp hWss sndBlock_mem_FP
  have hbufSnoc : (fun v => csBuf (cvCli v) ++ cvTok v ++ digitBits 4) ∈ FP :=
    appendFn_mem_FP (appendFn_mem_FP csBuf_cvCli_mem_FP cvTok_mem_FP)
      (constFn_mem_FP (digitBits 4))
  exact ifAndLen_mem_FP csMode_cvCli_mem_FP clampTok_mem_FP 0 6 (constFn_mem_FP [])
    (ifOr479_mem_FP csMode_cvCli_mem_FP
      (ifEqLen_mem_FP csModeStep_cvCli_mem_FP 0
        (wFrameEmit_mem_FP second ε hblk hbufSnoc
          (unaryBlock_mem_FP hday) hbc hibc)
        (constFn_mem_FP []))
      (appendFn_mem_FP cvTok_mem_FP (constFn_mem_FP (digitBits 4))))

/-! ### The frame passes are polynomial time -/

lemma frameTailOf_mem_FP {S : List Bool → List Bool} (h : S ∈ FP) :
    (fun z => frameTailOf (S z)) ∈ FP := by
  have hm : (fun z => csMode (S z)) ∈ FP :=
    mem_FP_comp (mem_FP_comp h fstBlock_mem_FP) fstBlock_mem_FP
  exact ifEqLen_mem_FP hm 4 (constFn_mem_FP _)
    (ifEqLen_mem_FP hm 7 (constFn_mem_FP _)
      (ifEqLen_mem_FP hm 9 (constFn_mem_FP _) (constFn_mem_FP [])))

lemma frameLegW_mem_FP (second : Bool) (ε : ℚ) {Wf Sf : List Bool → List Bool}
    (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) :
    (fun z => frameLegW second ε (Wf z) (Sf z)) ∈ FP := by
  have hbody := runFold_mem_FP (STEPr := fun _ => condStepR)
    (EMITr := fun W => frameEmitR second ε W) (c := 51) (k := 4)
    (qQ := Polynomial.C (wFrameEmitConst ε + 30) + 32 * Polynomial.X)
    condStepW_mem_FP (frameEmitW_mem_FP second ε) hWf hSf
    condStepW_length_le (frameEmitW_length_le second ε)
    (fun W cli cur h => condStepW_eq W cli cur h)
    (fun W cli cur h => frameEmitW_eq second ε W cli cur h) condInit []
  have hstate := runFold_cli_mem_FP (STEPr := fun _ => condStepR)
    (EMITr := fun W => frameEmitR second ε W) (c := 51) (k := 4)
    (qQ := Polynomial.C (wFrameEmitConst ε + 30) + 32 * Polynomial.X)
    condStepW_mem_FP (frameEmitW_mem_FP second ε) hWf hSf
    condStepW_length_le (frameEmitW_length_le second ε)
    (fun W cli cur h => condStepW_eq W cli cur h)
    (fun W cli cur h => frameEmitW_eq second ε W cli cur h) condInit []
  exact appendFn_mem_FP hbody (frameTailOf_mem_FP hstate)

lemma safeFrameW_mem_FP (ε : ℚ) {Wf Sf Acc : List Bool → List Bool}
    (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) (hAcc : Acc ∈ FP) :
    (fun z => safeFrameW ε (Wf z) (Sf z) (Acc z)) ∈ FP :=
  selectHeadFn_mem_FP (emptyFlag_mem_FP hAcc)
    (frameLegW_mem_FP false ε hWf hSf)
    (appendFn_mem_FP (frameLegW_mem_FP false ε hWf hSf)
      (frameLegW_mem_FP true ε hWf hSf))

/-- The trade-run count of a priced stream is polynomial time. -/
lemma countOf_mem_FP {Wf Pr : List Bool → List Bool} (hWf : Wf ∈ FP) (hPr : Pr ∈ FP) :
    countOf Pr ∈ FP := countPass_mem_FP hWf hPr

lemma budgetOf_mem_FP {Wf Pr : List Bool → List Bool} (hWf : Wf ∈ FP) (hPr : Pr ∈ FP) :
    budgetOf Wf Pr ∈ FP := budgetCodeW_mem_FP hWf (countOf_mem_FP hWf hPr)

lemma invBudgetOf_mem_FP {Wf Pr : List Bool → List Bool} (hWf : Wf ∈ FP) (hPr : Pr ∈ FP) :
    invBudgetOf Wf Pr ∈ FP := invBudgetCodeW_mem_FP hWf (countOf_mem_FP hWf hPr)

/-- **The frame join is polynomial time over any polynomial-time priced stream.** -/
lemma condOutputOf_mem_FP (ε : ℚ) {B Wf Pr : List Bool → List Bool}
    (hB : B ∈ FP) (hWf : Wf ∈ FP) (hPr : Pr ∈ FP) : condOutputOf ε B Wf Pr ∈ FP := by
  have hparams : (fun z => frameParams (Wf z) (B (Wf z)) (budgetOf Wf Pr z)
      (invBudgetOf Wf Pr z)) ∈ FP :=
    pairFn_mem_FP hWf (pairFn_mem_FP (mem_FP_comp hWf hB)
      (pairFn_mem_FP (budgetOf_mem_FP hWf hPr) (invBudgetOf_mem_FP hWf hPr)))
  exact safeFrameW_mem_FP ε hparams hPr (acceptsW_mem_FP hWf hPr)

lemma condOutputW_mem_FP (ε : ℚ) {B Wf Sf : List Bool → List Bool}
    (hB : B ∈ FP) (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) : condOutputW ε B Wf Sf ∈ FP :=
  condOutputOf_mem_FP ε hB hWf (guardedPassW_mem_FP ε hB hWf hSf)

/-! ## The machine reading of an efficient sentence sequence

The splicing emitter concatenates the condition block with other fragments, so it needs the
oracle's word to carry a whole number of complete blocks.  `MachineSentenceBlocks` below is
a predicate of its own, not `MachineSentenceCodes`
(`Framework/Machine/WriteOutMachine.lean`), which fixes only the *decode* and so does not
constrain the raw word's block structure.

No strengthening of the hypothesis is needed: for **any** write-out certificate the word is
`digitsToBits (digitize ·)` of the certificate's own token stream, and the downstream digit
clamp `min · 4` is the identity on it because the object is a list of base-4 digits and
terminators (`mem_digitize_le_four`) — *not* because the stream's token values are bounded.
`BigTokenStream.digitizeStream` supplies the clocked digit stream in the write-out class,
so `MachineSentenceBlocks` is produced from `def:ec`'s own sentence class. -/

/-- The machine reading of `𝓔𝓒`, with the block discipline the splicing emitter needs. -/
def MachineSentenceBlocks (ψ : ℕ → Sentence) : Prop :=
  ∃ B : List Bool → List Bool, B ∈ FP ∧ (∀ d, BlockWF (B (unaryDay d))) ∧
    ∀ d, parseRpn (blocksOf B d).length (blocksOf B d) = some (ψ d, [])

lemma mem_digitize_le_four (ts : List ℕ) : ∀ d ∈ digitize ts, d ≤ 4 := by
  intro d hd
  rw [digitize, List.mem_flatMap] at hd
  obtain ⟨t, -, hd⟩ := hd
  rw [tokenBlock, List.mem_append] at hd
  rcases hd with hd | hd
  · exact le_of_lt (natDigits4_lt t d hd)
  · simp at hd; omega

/-- **Every write-out efficient sentence sequence is machine-metered, block-complete.**
The word produced is `digitsToBits (digitize ·)` of the certificate's block stream, with its
digits already below the clamp, so the clamp is the identity on it and the block structure
survives.  The digit stream is clocked by `BigTokenStream.digitizeStream`, which needs no
bound on token values.  Kind `P`, provenance (a). -/
lemma machineSentenceBlocks_of_big {ψ : ℕ → Sentence} (h : BigSentenceCodes ψ) :
    MachineSentenceBlocks ψ := by
  obtain ⟨s, hs, hp⟩ := h
  obtain ⟨lc, tc, a, k, hclk⟩ := PolySegStream.clockedTokens_certificate hs.digitizeStream
  refine ⟨TraderMachine.traderOutput lc tc a k,
    TraderMachine.traderOutput_mem_FP lc tc a k, fun d => ?_, fun d => ?_⟩
  · have hout : TraderMachine.traderOutput lc tc a k (unaryDay d) = tokBits (s d) := by
      rw [TraderMachine.traderOutput, length_unaryDay]
      simp only [TraderMachine.clockOf]
      rw [hclk d, tokBits]
      congr 1
      have hid : List.map (fun x => min x 4) (digitize (s d))
          = List.map id (digitize (s d)) :=
        List.map_congr_left (fun x hx => by
          have := mem_digitize_le_four (s d) x hx
          simp only [id_eq]
          omega)
      rw [hid, List.map_id]
    rw [hout]
    exact blockWF_tokBits _
  · have hread : blocksOf (TraderMachine.traderOutput lc tc a k) d = s d := by
      rw [blocksOf, decodeBits, TraderMachine.bitsToDigits_traderOutput, length_unaryDay,
        undigitize_map_min_four]
      simp only [TraderMachine.clockOf]
      rw [hclk d, undigitize_digitize]
    rw [hread]
    exact hp d

/-! ## The transport theorem

Closure under conditioning, at the paper's own trader class: the conditioned translation of
a *machine*-efficient trader is machine-efficient.  The witness is the passes composed,
run on the packed word `pair (F x) x` so that the transduction can read the trading day off
the machine's own input; correctness is the class-agnostic core
`RpnConditioning.strategyOfTokens_rpnConditionOutput`, applied to the token stream the
source word denotes. -/

/-- **Closure under conditioning at the paper's own trader class, gated form**: the
conditioned translation of a machine-efficient trader is machine-efficient.

The `ψ` hypothesis is `BigSentenceCodes` — `def:ec`'s own write-out sentence class, in which
a condition's Gödel code may be exponential in the day — exactly as in the fuel-class
counterpart `RpnConditioning.conditionedTranslation_preserves_ecRpn` (whose `Rpn` names the
RPN *symbol model* the compiler emits in, not the sentence class), so nothing about the
sentence sequence is weakened; the trader hypothesis is the *machine* class, so the theorem
is strictly stronger there.
Kind: `P` proved; provenance: (a) derived in-project.
Paper node: `thm:scon` -/
theorem conditionedTranslation_preserves_machine
    (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ) (ε : ℚ)
    (T : Trader) (hT : MachineEfficientTrader T) :
    MachineEfficientTrader (T.conditionedTranslation ψ ε) := by
  obtain ⟨B, hB, hBwf, hBparse⟩ := machineSentenceBlocks_of_big hψ
  obtain ⟨F, hF, hFspec⟩ := hT
  refine ⟨fun x => condOutputW ε B sndBlock fstBlock (pair (F x) x),
    mem_FP_withInput hF
      (condOutputW_mem_FP ε hB sndBlock_mem_FP fstBlock_mem_FP), fun n => ?_⟩
  have hdec := decodeBits_condOutputW ε B sndBlock fstBlock hBwf
    (pair (F (unaryDay n)) (unaryDay n)) (by simp [unaryDay])
  simp only [sndBlock_pair, fstBlock_pair, length_unaryDay] at hdec
  show strategyOfTokens n (unRpn (decodeBits
    (condOutputW ε B sndBlock fstBlock (pair (F (unaryDay n)) (unaryDay n))))) = _
  rw [hdec]
  refine strategyOfTokens_rpnConditionOutput (blocksOf B) ψ hBparse ε T n _ ?_
  exact hFspec n

/-! ## The finite-zero price rewrite

`rpnZeroAwareEmit` replaces the conditional-price expansion by the fixed run
`[D, 1, ⌜1⌝, 8]` on the finitely many days where the condition's price is exactly zero.
Everything else in the pipeline is untouched: the guard, the count, the budget codes, the
acceptance test and the frame join all take the priced stream as input, so only the emitter
is new. -/

/-- Membership in a *fixed* finite set is a polynomial-time test of an `FP` word. -/
lemma ifMemFinset_mem_FP {A X Y : List Bool → List Bool} (hA : A ∈ FP)
    (S : Finset (List Bool)) (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if A z ∈ S then X z else Y z) ∈ FP := by
  have hflag : (fun z => if A z ∈ S then ([true] : List Bool) else []) ∈ FP :=
    mem_FP_comp hA (Complexity.ite_mem_finset_mem_FP (fun _ => [true]) S)
  have h := selectHeadFn_mem_FP (emptyFlag_mem_FP hflag) hY hX
  have heq : (fun z => selectHead (emptyFlag (if A z ∈ S then [true] else [])) (Y z) (X z))
      = fun z => if A z ∈ S then X z else Y z := by
    funext z
    by_cases hc : A z ∈ S
    · rw [if_pos hc, if_pos hc, selectHead_emptyFlag_cons]
    · rw [if_neg hc, if_neg hc, selectHead_emptyFlag_nil]
  rwa [heq] at h

lemma unaryDay_injective : Function.Injective unaryDay := by
  intro a b h
  have := congrArg List.length h
  simpa using this

/-- **The zero-day test may be clamped at the cutoff, and the clamp separates.**  Every zero
day is *strictly* below the cutoff, so `min D cutoff` lands on `D` when `D` is a zero day
and otherwise on `cutoff`, which is not one.  Clamping at `cutoff - 1` or admitting `cutoff`
itself into `zeroDays` would collapse the two cases and make the test accept days it must
reject. -/
lemma mem_zeroDays_clamp (zeroDays : Finset ℕ) (cutoff : ℕ)
    (hlt : ∀ d ∈ zeroDays, d < cutoff) (D : ℕ) :
    min D cutoff ∈ zeroDays ↔ D ∈ zeroDays := by
  by_cases h : D < cutoff
  · rw [Nat.min_eq_left (le_of_lt h)]
  · rw [Nat.min_eq_right (by omega)]
    constructor
    · intro hc; exact absurd (hlt cutoff hc) (by omega)
    · intro hD; exact absurd (hlt D hD) (by omega)

/-- The incoming day clamped at the cutoff: the word the zero-day test reads. -/
def zeroTokW (cutoff : ℕ) (v : List Bool) : List Bool :=
  List.replicate (min (digitVal (bitsToDigits (cvTok v))) cutoff) true

lemma zeroTokW_mem_FP (cutoff : ℕ) : zeroTokW cutoff ∈ FP := by
  have h := LEUnary.unaryOfDigitsLE_le_mem_FP cvTok_mem_FP (constFn_mem_FP (uw cutoff))
  simp only [length_uw] at h
  exact h

/-- The finite-zero price emitter, on words. -/
def zeroEmitW (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ) (B : List Bool → List Bool)
    (v : List Bool) : List Bool :=
  if (csMode (cvCli v)).length = 2 then
    (if zeroTokW cutoff v ∈ zeroDays.image unaryDay then
      dayBits (cvTok v) ++ tokBits [1, Encodable.encode (1 : ℚ), 8]
     else condEmitOf ε (B (dayClamp v)) (csBuf (cvCli v)) (cvTok v))
  else dayBits (cvTok v)

/-- Its block-level reading. -/
def zeroEmitR (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ) (B : List Bool → List Bool)
    (n : ℕ) (cli : List Bool) (cur : List ℕ) : List Bool :=
  if (csMode cli).length = 2 then
    (if List.replicate (min (digitVal cur) cutoff) true ∈ zeroDays.image unaryDay then
      dayBits (digitsToBits cur) ++ tokBits [1, Encodable.encode (1 : ℚ), 8]
     else condEmitOf ε (B (unaryDay (min (digitVal cur) n))) (csBuf cli) (digitsToBits cur))
  else dayBits (digitsToBits cur)

lemma zeroEmitW_eq (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ) (B : List Bool → List Bool)
    (W cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    zeroEmitW zeroDays cutoff ε B (pair W (pair cli (digitsToBits cur)))
      = zeroEmitR zeroDays cutoff ε B W.length cli cur := by
  have hd : bitsToDigits (digitsToBits cur) = cur :=
    bitsToDigits_digitsToBits cur (fun d hd => lt_trans (hcur d hd) (by norm_num))
  rw [zeroEmitW, zeroEmitR, zeroTokW, dayClamp]
  simp only [cvW, cvCli, cvTok, sndBlock_pair, fstBlock_pair, hd]
  rfl

lemma mem_image_unaryDay (S : Finset ℕ) (k : ℕ) :
    List.replicate k true ∈ S.image unaryDay ↔ k ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨d, hd, he⟩
    have hdk : d = k := unaryDay_injective (by rw [he]; rfl)
    exact hdk ▸ hd
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- The finite-zero price emitter with its condition-block oracle clamped to the trading
day, exactly as `clampedEmit` is for the gated rewrite. -/
def clampedZeroEmit (zeroDays : Finset ℕ) (ε : ℚ) (B : List Bool → List Bool) (n : ℕ) :
    List ℕ → ℕ → List ℕ :=
  fun buf D => if D ∈ zeroDays then [D, 1, Encodable.encode (1 : ℚ), 8]
    else rpnConditionEmit (blocksOf B (min D n)) ε buf D

lemma blockWF_zeroEmitR (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ)
    (B : List Bool → List Bool) (n : ℕ) (cli : List Bool) (cur : List ℕ)
    (hcur : ∀ d ∈ cur, d < 4) (hwf : BlockWF (csBuf cli))
    (hB : ∀ d, BlockWF (B (unaryDay d))) :
    BlockWF (zeroEmitR zeroDays cutoff ε B n cli cur) := by
  rw [zeroEmitR]
  split_ifs
  · exact (blockWF_run cur hcur).append (blockWF_tokBits _)
  · exact blockWF_condEmitOf ε _ _ cur hcur (hB _) hwf
  · exact blockWF_run cur hcur

lemma decodeBits_zeroEmitR (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ)
    (B : List Bool → List Bool) (n : ℕ) (cli : List Bool) (cur : List ℕ)
    (hcur : ∀ d ∈ cur, d < 4) (hwf : BlockWF (csBuf cli))
    (hB : ∀ d, BlockWF (B (unaryDay d))) (hlt : ∀ d ∈ zeroDays, d < cutoff) :
    decodeBits (zeroEmitR zeroDays cutoff ε B n cli cur)
      = if rcMode (csPack cli) = 2 then
          clampedZeroEmit zeroDays ε B n (csTokens cli) (digitVal cur)
        else [digitVal cur] := by
  have hmode : rcMode (csPack cli) = (csMode cli).length := by rw [csPack, rcMode_pack]
  have hzero : (List.replicate (min (digitVal cur) cutoff) true
      ∈ zeroDays.image unaryDay) ↔ digitVal cur ∈ zeroDays := by
    rw [mem_image_unaryDay, mem_zeroDays_clamp zeroDays cutoff hlt]
  rw [zeroEmitR, hmode, clampedZeroEmit]
  by_cases h2 : (csMode cli).length = 2
  · rw [if_pos h2, if_pos h2]
    by_cases hz : digitVal cur ∈ zeroDays
    · rw [if_pos (hzero.mpr hz), if_pos hz, dayBits,
        decodeBits_append (blockWF_run cur hcur) (blockWF_tokBits _),
        decodeBits_run cur hcur, decodeBits_tokBits]
      rfl
    · rw [if_neg (fun hc => hz (hzero.mp hc)), if_neg hz,
        decodeBits_condEmitOf ε _ _ cur hcur (hB _) hwf, csTokens, blocksOf]
  · rw [if_neg h2, if_neg h2]
    exact decodeBits_run cur hcur

lemma zeroEmitW_mem_FP (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ)
    {B : List Bool → List Bool} (hB : B ∈ FP) : zeroEmitW zeroDays cutoff ε B ∈ FP :=
  ifEqLen_mem_FP csMode_cvCli_mem_FP 2
    (ifMemFinset_mem_FP (zeroTokW_mem_FP cutoff) (zeroDays.image unaryDay)
      (appendFn_mem_FP (dayBits_mem_FP cvTok_mem_FP)
        (constFn_mem_FP (tokBits [1, Encodable.encode (1 : ℚ), 8])))
      (condEmitOf_mem_FP ε (mem_FP_comp dayClamp_mem_FP hB) csBuf_cvCli_mem_FP
        cvTok_mem_FP))
    (dayBits_mem_FP cvTok_mem_FP)

/-- The zero branch emits a *constant* plus the copied day, so it adds nothing to the
state-dependence of the bound: the multiplier on `cli` and `tok` is the gated emitter's. -/
def zeroEmitConstLen (ε : ℚ) : ℕ :=
  emitConstLen ε + (tokBits [1, Encodable.encode (1 : ℚ), 8]).length + 3

lemma zeroEmitW_length_le (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ)
    {B : List Bool → List Bool} {pB : Polynomial ℕ}
    (hBlen : ∀ w, (B w).length ≤ pB.eval w.length) (W cli tok : List Bool) :
    (zeroEmitW zeroDays cutoff ε B (pair W (pair cli tok))).length
      ≤ (2 * pB + Polynomial.C (zeroEmitConstLen ε)).eval W.length
        + 3 * (cli.length + tok.length) := by
  have hcli : cvCli (pair W (pair cli tok)) = cli := by simp [cvCli]
  have htok : cvTok (pair W (pair cli tok)) = tok := by simp [cvTok]
  have hW : cvW (pair W (pair cli tok)) = W := by simp [cvW]
  have hclamp : (dayClamp (pair W (pair cli tok))).length ≤ W.length := by
    rw [dayClamp, hW, List.length_replicate]
    omega
  have hblk : (B (dayClamp (pair W (pair cli tok)))).length ≤ pB.eval W.length :=
    le_trans (hBlen _) (polynomial_eval_mono_nat pB hclamp)
  have hbuf : (csBuf cli).length ≤ cli.length :=
    le_trans (sndBlock_length_le _) (sndBlock_length_le _)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_ofNat, zeroEmitConstLen, emitConstLen]
  rw [zeroEmitW, hcli, htok]
  split_ifs
  · rw [dayBits]
    simp only [List.length_append, length_digitBits]
    omega
  · rw [condEmitOf, dayBits]
    simp only [List.length_append, length_digitBits]
    omega
  · rw [dayBits]
    simp only [List.length_append, length_digitBits]
    omega

/-! ### The finite-zero pipeline

The guard, the count, the budget codes, the acceptance test and the frame join are the same
functions as in the gated case; only the price emitter differs, so only the price pass and
its guarded wrapper are restated here. -/

/-- The finite-zero guarded price pass: `guardedPassW` with `zeroEmitR` in place of
`condEmitR`.  The guard fold is the same one. -/
def zeroGuardedPassW (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ)
    (B Wf Sf : List Bool → List Bool) (z : List Bool) : List Bool :=
  selectHead
    (emptyFlag (runFold condStepR (guardEmitR (Wf z).length) condInit []
      (blockSplit (bitsToDigits (Sf z))).1).2)
    (runFold condStepR (zeroEmitR zeroDays cutoff ε B (Wf z).length) condInit []
      (blockSplit (bitsToDigits (Sf z))).1).2
    []

lemma zeroPass_mem_FP (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ)
    {B Wf Sf : List Bool → List Bool} (hB : B ∈ FP) (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) :
    (fun z => (runFold condStepR (zeroEmitR zeroDays cutoff ε B (Wf z).length) condInit []
        (blockSplit (bitsToDigits (Sf z))).1).2) ∈ FP := by
  obtain ⟨pB, hBlen⟩ := output_length_poly_of_mem_FP hB
  exact runFold_mem_FP (STEPr := fun _ => condStepR)
    (EMITr := fun W => zeroEmitR zeroDays cutoff ε B W.length)
    (c := 51) (k := 3) (qQ := 2 * pB + Polynomial.C (zeroEmitConstLen ε))
    condStepW_mem_FP (zeroEmitW_mem_FP zeroDays cutoff ε hB) hWf hSf
    condStepW_length_le (zeroEmitW_length_le zeroDays cutoff ε hBlen)
    (fun W cli cur h => condStepW_eq W cli cur h)
    (fun W cli cur h => zeroEmitW_eq zeroDays cutoff ε B W cli cur h) condInit []

lemma zeroGuardedPassW_mem_FP (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ)
    {B Wf Sf : List Bool → List Bool} (hB : B ∈ FP) (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) :
    zeroGuardedPassW zeroDays cutoff ε B Wf Sf ∈ FP :=
  selectHeadFn_mem_FP (emptyFlag_mem_FP (guardPass_mem_FP hWf hSf))
    (zeroPass_mem_FP zeroDays cutoff ε hB hWf hSf) (constFn_mem_FP [])

lemma decodeBits_zeroGuardedPassW (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ)
    (B Wf Sf : List Bool → List Bool) (hB : ∀ d, BlockWF (B (unaryDay d)))
    (hlt : ∀ d ∈ zeroDays, d < cutoff) (z : List Bool) :
    decodeBits (zeroGuardedPassW zeroDays cutoff ε B Wf Sf z)
      = rpnGuardedConditionTokens (rpnZeroAwareEmit zeroDays (blocksOf B) ε)
          (Wf z).length (undigitize (bitsToDigits (Sf z))) :=
  decodeBits_guardedOf (emitC := clampedZeroEmit zeroDays ε B (Wf z).length)
    (emitT := rpnZeroAwareEmit zeroDays (blocksOf B) ε) (Wf z).length
    (fun cli cur hcur hbuf =>
      blockWF_zeroEmitR zeroDays cutoff ε B (Wf z).length cli cur hcur hbuf hB)
    (fun cli cur hcur hbuf =>
      decodeBits_zeroEmitR zeroDays cutoff ε B (Wf z).length cli cur hcur hbuf hB hlt)
    (fun buf D hD => by
      simp only [clampedZeroEmit, rpnZeroAwareEmit, Nat.min_eq_left hD])
    (bitsToDigits (Sf z))

/-- The finite-zero conditioning transduction. -/
def zeroCondOutputW (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ)
    (B Wf Sf : List Bool → List Bool) : List Bool → List Bool :=
  condOutputOf ε B Wf (zeroGuardedPassW zeroDays cutoff ε B Wf Sf)

lemma zeroCondOutputW_mem_FP (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ)
    {B Wf Sf : List Bool → List Bool} (hB : B ∈ FP) (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) :
    zeroCondOutputW zeroDays cutoff ε B Wf Sf ∈ FP :=
  condOutputOf_mem_FP ε hB hWf (zeroGuardedPassW_mem_FP zeroDays cutoff ε hB hWf hSf)

/-- **The finite-zero conditioning transduction computes `rpnZeroAwareOutput`.** -/
lemma decodeBits_zeroCondOutputW (zeroDays : Finset ℕ) (cutoff : ℕ) (ε : ℚ)
    (B Wf Sf : List Bool → List Bool) (hB : ∀ d, BlockWF (B (unaryDay d)))
    (hlt : ∀ d ∈ zeroDays, d < cutoff) (z : List Bool)
    (hWz : Wf z = unaryDay (Wf z).length) :
    decodeBits (zeroCondOutputW zeroDays cutoff ε B Wf Sf z)
      = rpnZeroAwareOutput zeroDays (blocksOf B) ε (Wf z).length
          (undigitize (bitsToDigits (Sf z))) := by
  rw [zeroCondOutputW, decodeBits_condOutputOf ε B Wf _ hB z hWz, rpnZeroAwareOutput,
    decodeBits_zeroGuardedPassW zeroDays cutoff ε B Wf Sf hB hlt z]

/-! ## The finite-zero transport theorem

The eventual translation silences the trader below the floor's cutoff and applies the
finite-zero conditional contract above it.  At the word level the silencing is a single
length comparison against a fixed numeral — and it must compare the *right* way round: the
gate fires when the day reaches the cutoff, not when it is bounded by it. -/

private lemma ifConstLeLen_mem_FP {A X Y : List Bool → List Bool} (hA : A ∈ FP) (k : ℕ)
    (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if k ≤ (A z).length then X z else Y z) ∈ FP := by
  have h := selectHeadFn_leFlag_mem_FP hA (constFn_mem_FP (uw k)) hX hY
  simp only [length_uw] at h
  exact h

/-- **Closure under conditioning at the paper's own trader class, finite-zero form**: the
eventual conditioned translation of a machine-efficient trader is machine-efficient.

As with the gated form, the `ψ` hypothesis is `BigSentenceCodes` — `def:ec`'s own write-out
sentence class — the same one the fuel counterpart
`RpnConditioning.eventualConditionedTranslation_preserves_ecRpn` takes (whose `Rpn` names
the RPN *symbol model*, not the sentence class), and the trader hypothesis is the machine
class.
Kind: `P` proved; provenance: (a) derived in-project.
Paper node: `thm:scon` -/
theorem eventualConditionedTranslation_preserves_machine
    {P : History} {ψ : ℕ → Sentence}
    (F : EventualConditioningFloor P ψ) (hψ : BigSentenceCodes ψ)
    (T : Trader) (hT : MachineEfficientTrader T) :
    MachineEfficientTrader (T.eventualConditionedTranslation F) := by
  obtain ⟨B, hB, hBwf, hBparse⟩ := machineSentenceBlocks_of_big hψ
  obtain ⟨G, hG, hGspec⟩ := hT
  refine ⟨fun x =>
    (if F.cutoff ≤ (sndBlock (pair (G x) x)).length then
      zeroCondOutputW F.zeroDays F.cutoff F.epsilon B sndBlock fstBlock (pair (G x) x)
     else []),
    mem_FP_withInput hG
      (ifConstLeLen_mem_FP sndBlock_mem_FP F.cutoff
        (zeroCondOutputW_mem_FP F.zeroDays F.cutoff F.epsilon hB sndBlock_mem_FP
          fstBlock_mem_FP) (constFn_mem_FP [])), fun n => ?_⟩
  dsimp only
  have hsnd : sndBlock (pair (G (unaryDay n)) (unaryDay n)) = unaryDay n := by simp
  by_cases hn : F.cutoff ≤ n
  · have hcond : F.cutoff ≤ (sndBlock (pair (G (unaryDay n)) (unaryDay n))).length := by
      rw [hsnd, length_unaryDay]; exact hn
    rw [if_pos hcond]
    have hdec := decodeBits_zeroCondOutputW F.zeroDays F.cutoff F.epsilon B sndBlock
      fstBlock hBwf F.zeroDays_lt (pair (G (unaryDay n)) (unaryDay n))
      (by simp [unaryDay])
    simp only [sndBlock_pair, fstBlock_pair, length_unaryDay] at hdec
    show strategyOfTokens n (unRpn (decodeBits
      (zeroCondOutputW F.zeroDays F.cutoff F.epsilon B sndBlock fstBlock
        (pair (G (unaryDay n)) (unaryDay n))))) = _
    rw [hdec, T.eventualConditionedTranslation_strat_of_le F hn]
    exact strategyOfTokens_rpnZeroAwareOutput F.zeroDays (blocksOf B) ψ hBparse F.epsilon
      T n _ (hGspec n)
  · have hcond : ¬ F.cutoff ≤ (sndBlock (pair (G (unaryDay n)) (unaryDay n))).length := by
      rw [hsnd, length_unaryDay]; exact hn
    rw [if_neg hcond, T.eventualConditionedTranslation_strat_of_lt F (by omega)]
    simp [strategyOfOutput, strategyOfTokens, deserializeTrades, unRpn, unRpnTokens,
      EF.streamReadFrom, EF.streamInitial, Trader.zero, undigitize, bitsToDigits]
    rfl

end LogicalInduction.CondStep
