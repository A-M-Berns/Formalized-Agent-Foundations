/-
# The finite-support freeze as a polynomial-time transduction

`Properties/FinitePerturbations.lean` builds the selector-indexed freeze as a token-level
transducer, `EF.freezeTokenRunOn`, and `FreezeStreamRewriter` there names the one
`Complexity.FP` fact the machine-class patch still needs.  This file is that transducer in
the machine model: a client of `Framework/Machine/TokenFold.lean`'s block fold, so that the
freeze is an honest `Complexity.FP` function of the trader's serialized stream.

The freeze automaton is much smaller than the conditioning one
(`Construction/Machine/CondStep.lean`, the parallel client): its state is a mode and the
buffered sentence-code block, with no counter and no run length, and the buffer is
*replaced* at a price frame rather than extended, so the state bound is trivially additive.

* **The state.**  The mode is a unary word, so the automaton's tests are length
  comparisons; the pending sentence code is carried as its own digit bits, so the emitter
  can hand it to the quote oracle without re-rendering it.  That choice is why the client
  reads token *blocks* rather than token values: a raw machine word may carry a
  non-canonical run, and copying it is then not a function of the value.

* **The step.**  `frModeW` mirrors the scalar `frModeF` branch for branch, and
  `frModeF_clamp` is what lets the token arrive as `min t 8` marks rather than an unbounded
  numeral — the automaton only ever tests `0`, `1`, `6`, `7`.

* **The emitter.**  Everywhere except a price-day slot it copies the token through.  At a
  price-day slot it appends the frozen suffix, which comes from a `QuoteOracle`: given the
  day and the buffered code block, the bits of `[1, quote, 8]` when the coordinate is
  selected and nothing when it is not.

## Two disclosed boundaries, both named rather than buried

**The clamp.**  `frEmitR` calls the oracle at `min D n` rather than at `D`, because a
word-level emitter cannot call an oracle at an unbounded day.  So this pass computes the
freeze whose selector and quote table are *composed with that clamp*
(`clampSel`, `clampQuote`), and `decodeBits_freezePass` states exactly that.  Discharging
the clamp — showing the two agree on the streams a day-`n` strategy actually emits — is a
guard obligation, not something this file assumes away.

**The constant output bound.**  `QuoteOracle.Q_length_le` asks the oracle's *output* to be
bounded by a constant.  That is not a convenience: `TokenFold.runFold_mem_FP`'s emission
budget is `qQ.eval W.length + k * (cli.length + tok.length)`, polynomial in the parameter
block but only *linear* in the state, and an emitted numeral that grew with the buffered
sentence code would blow it.  For a **finite** quote table the bound holds for free — the
table has finitely many entries, so finitely many quote codes — and for an arbitrary market
it fails.  This is the paper's erratum (`app:ifp`) reappearing as a complexity side
condition: hard-coding the constants is legitimate exactly when there are finitely many.

`QuoteOracle` has **no instance** in this repo; building one for a finite table is the
lookup obligation (`RpnFreeze.matchRun`, and the structured paper-prime leaf).

## Which stream this pass runs on — read this before citing it

`EF.freezeTokenRunOn` is the **contracted** automaton: a price frame reaches it as
`[0, code, day]`, one token per sentence.  So the pass below rewrites a contracted stream,
and that is *not* the stream a machine holds — a machine holds the flat RPN stream, whose
price frame is `0 :: run :: day`, and contracting it would mean re-encoding each parsed
sentence.  Discharging `FreezeStreamRewriter` therefore needs the **flat** pass, whose
automaton is `CondStep.condStepR` and whose emitter is the run-level lookup;
`RpnFreeze.freezeStreamRewriter_of_flatPass` is the reduction, and
`RpnFreeze.unRpn_rpnFreezeRunOn` the commutation that licenses it.

What this file settles is that the freeze *shape* — a mode automaton with a buffered code
block and an oracle-fed splice — fits inside `runFold_mem_FP`'s budget, with the two
per-step bounds discharged and the constant-output condition identified.  It does not by
itself inhabit `FreezeStreamRewriter`.

Everything here is construction infrastructure rather than a paper statement, so the
declarations are `lemma`s and carry no `Paper node:` line.
-/
import LogicalInduction.Properties.FinitePerturbations
import LogicalInduction.Framework.Machine.TokenFold

namespace LogicalInduction.FreezeStep

open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold

/-- A natural number as a unary word. -/
abbrev uw (k : ℕ) : List Bool := List.replicate k true

@[simp] lemma length_uw (k : ℕ) : (uw k).length = k := by simp [uw]

/-- "This length equals the numeral `k`" as a `selectHead` against a constant unary word.

`CondStep` carries the same four-line helper privately; when the two machine clients are
merged it belongs in `TokenFold` once. -/
private lemma ifEqLen_mem_FP {A X Y : List Bool → List Bool} (hA : A ∈ FP) (k : ℕ)
    (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if (A z).length = k then X z else Y z) ∈ FP := by
  have h := selectHeadFn_eqLen_mem_FP hA (constFn_mem_FP (uw k)) hX hY
  simp only [length_uw] at h
  exact h

/-! ## The mode component -/

/-- `EF.freezeTokenNext`'s mode component, as a scalar function. -/
def frModeF (m t : ℕ) : ℕ :=
  if m = 0 then
    (if t = 0 then 1 else if t = 1 then 3 else if t = 6 then 4 else if t = 7 then 5 else 0)
  else if m = 1 then 2 else 0

/-- The same on unary words. -/
def frModeW (mW tW : List Bool) : List Bool :=
  if mW.length = 0 then
    (if tW.length = 0 then uw 1
     else if tW.length = 1 then uw 3
     else if tW.length = 6 then uw 4
     else if tW.length = 7 then uw 5 else uw 0)
  else if mW.length = 1 then uw 2 else uw 0

lemma length_frModeW (mW tW : List Bool) :
    (frModeW mW tW).length = frModeF mW.length tW.length := by
  rw [frModeW, frModeF]
  simp only [apply_ite List.length, length_uw]

lemma frModeF_eq (m c t : ℕ) : frModeF m t = (EF.freezeTokenNext (m, c) t).1 := by
  match m with
  | 0 => simp only [frModeF, EF.freezeTokenNext]; norm_num; split_ifs <;> rfl
  | 1 => simp [frModeF, EF.freezeTokenNext]
  | (k + 2) => simp [frModeF, EF.freezeTokenNext]

lemma freezeTokenNext_snd (m c t : ℕ) :
    (EF.freezeTokenNext (m, c) t).2 = if m = 1 then t else 0 := by
  match m with
  | 0 => simp only [EF.freezeTokenNext]; norm_num; split_ifs <;> rfl
  | 1 => simp [EF.freezeTokenNext]
  | (k + 2) => simp [EF.freezeTokenNext]

/-- The automaton only tests `0`, `1`, `6`, `7`, so the token may arrive clamped at `8`. -/
lemma frModeF_clamp (m t : ℕ) : frModeF m (min t 8) = frModeF m t := by
  rcases le_or_gt 8 t with h | h
  · rw [min_eq_right h, frModeF, frModeF]
    have h0 : t ≠ 0 := by omega
    have h1 : t ≠ 1 := by omega
    have h6 : t ≠ 6 := by omega
    have h7 : t ≠ 7 := by omega
    simp [h0, h1, h6, h7]
  · rw [min_eq_left (le_of_lt h)]

lemma frModeF_le (m t : ℕ) : frModeF m t ≤ 5 := by
  rw [frModeF]; split_ifs <;> omega

lemma frModeW_mem_FP {M T : List Bool → List Bool} (hM : M ∈ FP) (hT : T ∈ FP) :
    (fun z => frModeW (M z) (T z)) ∈ FP := by
  have hu : ∀ k : ℕ, (fun _ : List Bool => uw k) ∈ FP := fun k => constFn_mem_FP (uw k)
  refine ifEqLen_mem_FP hM 0
    (ifEqLen_mem_FP hT 0 (hu 1) (ifEqLen_mem_FP hT 1 (hu 3)
      (ifEqLen_mem_FP hT 6 (hu 4) (ifEqLen_mem_FP hT 7 (hu 5) (hu 0))))) ?_
  exact ifEqLen_mem_FP hM 1 (hu 2) (hu 0)

/-! ## The client state -/

/-- The client state: the mode as unary marks, the pending sentence code as its own
complete digit block. -/
def frSt (mW bufW : List Bool) : List Bool := pair mW bufW

def frMode (st : List Bool) : List Bool := fstBlock st
def frBuf (st : List Bool) : List Bool := sndBlock st

@[simp] lemma frMode_frSt (m b : List Bool) : frMode (frSt m b) = m := by
  simp [frMode, frSt]
@[simp] lemma frBuf_frSt (m b : List Bool) : frBuf (frSt m b) = b := by
  simp [frBuf, frSt]

/-- The pending sentence code a client state denotes. -/
def frCode (st : List Bool) : ℕ := (decodeBits (frBuf st)).headD 0

/-- The automaton state a client state denotes. -/
def frPack (st : List Bool) : EF.FreezeTokenState := ((frMode st).length, frCode st)

/-! ## The step, on words -/

def frModeStep (cli tw : List Bool) : List Bool := frModeW (frMode cli) tw

/-- The buffer is the pending sentence code: set from the incoming block at the slot right
after a price tag, cleared everywhere else.  The block is stored *verbatim*, which is why
the client reads blocks rather than values. -/
def frBufStep (cli tok : List Bool) : List Bool :=
  if (frMode cli).length = 1 then tok ++ digitBits 4 else []

def frStepOf (cli tw tok : List Bool) : List Bool :=
  frSt (frModeStep cli tw) (frBufStep cli tok)

private def fvW (v : List Bool) : List Bool := fstBlock v
private def fvCli (v : List Bool) : List Bool := fstBlock (sndBlock v)
private def fvTok (v : List Bool) : List Bool := sndBlock (sndBlock v)

/-- The incoming token, clamped to the automaton's test window and rendered in unary. -/
def clampTok (v : List Bool) : List Bool :=
  List.replicate (min (digitVal (bitsToDigits (fvTok v))) 8) true

/-- The freeze pass's word-level step. -/
def frStepW (v : List Bool) : List Bool := frStepOf (fvCli v) (clampTok v) (fvTok v)

/-- Its block-level reading, which is what `TokenFold.runFold` folds. -/
def frStepR (cli : List Bool) (cur : List ℕ) : List Bool :=
  frStepOf cli (List.replicate (min (digitVal cur) 8) true) (digitsToBits cur)

lemma frStepW_eq (W cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    frStepW (pair W (pair cli (digitsToBits cur))) = frStepR cli cur := by
  rw [frStepW, frStepR, clampTok]
  simp only [fvCli, fvTok, sndBlock_pair, fstBlock_pair,
    bitsToDigits_digitsToBits cur (fun d hd => lt_trans (hcur d hd) (by norm_num))]

/-! ### Agreement with the token-level automaton -/

/-- **The word step realizes the automaton.**  Both components: the mode, through the
clamped token, and the pending sentence code, which is the buffered block's own value.

Proof kind: `P` proved.  Provenance: (a) `length_frModeW`, `frModeF_clamp`,
`TokenFold.decodeBits_run`.
Paper node: `app:ifp` -/
lemma frPack_frStepR (cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    frPack (frStepR cli cur) = EF.freezeTokenNext (frPack cli) (digitVal cur) := by
  have hmode : (frMode (frStepR cli cur)).length
      = (EF.freezeTokenNext (frPack cli) (digitVal cur)).1 := by
    rw [frStepR, frStepOf, frMode_frSt, frModeStep, length_frModeW,
      List.length_replicate, frModeF_clamp, frModeF_eq (c := frCode cli), frPack]
  have hcode : frCode (frStepR cli cur)
      = (EF.freezeTokenNext (frPack cli) (digitVal cur)).2 := by
    rw [frStepR, frStepOf, frCode, frBuf_frSt, frBufStep, frPack, freezeTokenNext_snd]
    split_ifs with h
    · rw [decodeBits_run cur hcur]
      rfl
    · simp
  rw [frPack, hmode, hcode]

lemma bufWF_frStepR (cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    BlockWF (frBuf (frStepR cli cur)) := by
  rw [frStepR, frStepOf, frBuf_frSt, frBufStep]
  split_ifs
  · exact blockWF_run cur hcur
  · exact BlockWF.nil

/-! ### Membership and the state bound -/

lemma frStepW_mem_FP : frStepW ∈ FP := by
  have hcli : fvCli ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have htok : fvTok ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
  have hclamp : clampTok ∈ FP := by
    have h := LEUnary.unaryOfDigitsLE_le_mem_FP htok (constFn_mem_FP (uw 8))
    simp only [length_uw] at h
    exact h
  have hm : (fun v => frMode (fvCli v)) ∈ FP := mem_FP_comp hcli fstBlock_mem_FP
  have hmode : (fun v => frModeStep (fvCli v) (clampTok v)) ∈ FP :=
    frModeW_mem_FP hm hclamp
  have hbuf : (fun v => frBufStep (fvCli v) (fvTok v)) ∈ FP :=
    ifEqLen_mem_FP hm 1
      (appendFn_mem_FP htok (constFn_mem_FP (digitBits 4))) (constFn_mem_FP [])
  exact pairFn_mem_FP hmode hbuf

/-- The state bound is additive, and does not even need the old state: the freeze buffer is
*replaced* at a price frame rather than extended, so one step's state is bounded by the
incoming block plus a constant. -/
lemma frStepW_length_le (W cli tok : List Bool) :
    (frStepW (pair W (pair cli tok))).length ≤ cli.length + tok.length + 15 := by
  have hcli : fvCli (pair W (pair cli tok)) = cli := by simp [fvCli]
  have htok : fvTok (pair W (pair cli tok)) = tok := by simp [fvTok]
  have hm : (frModeStep cli (clampTok (pair W (pair cli tok)))).length ≤ 5 := by
    rw [frModeStep, length_frModeW]; exact frModeF_le _ _
  have hb : (frBufStep cli tok).length ≤ tok.length + 3 := by
    rw [frBufStep]
    split_ifs
    · simp
    · simp
  rw [frStepW, hcli, htok, frStepOf, frSt, pair_length]
  omega

/-! ## The emitter -/

/-- The incoming token, re-emitted as its own complete block. -/
def dayBits (tok : List Bool) : List Bool := tok ++ digitBits 4

/-- The day the oracle is called at: the incoming token, clamped by the trading day. -/
def dayClamp (v : List Bool) : List Bool :=
  List.replicate (min (digitVal (bitsToDigits (fvTok v))) (fvW v).length) true

/-- **The quote oracle**: the frozen suffix at a selected price coordinate.

Given the day and the buffered sentence-code block, it returns the bits of `[1, quote, 8]`
when the coordinate is selected and nothing when it is not.  `Q_length_le` is the
finite-table condition in complexity clothing — see this file's header. -/
structure QuoteOracle (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) where
  /-- The oracle. -/
  Q : List Bool → List Bool
  /-- It is polynomial time. -/
  Q_FP : Q ∈ FP
  /-- Its output is a whole number of complete blocks, so splices decode piecewise. -/
  Q_wf : ∀ (d : ℕ) (bufW : List Bool), BlockWF (Q (pair (unaryDay d) bufW))
  /-- The constant output budget: the quote table is finite. -/
  Q_len : ℕ
  /-- The constant bound itself. -/
  Q_length_le : ∀ v : List Bool, (Q v).length ≤ Q_len
  /-- And it emits the freeze suffix. -/
  Q_spec : ∀ (d : ℕ) (bufW : List Bool),
    decodeBits (Q (pair (unaryDay d) bufW))
      = if selCode d ((decodeBits bufW).headD 0) then
          [1, quoteCode d ((decodeBits bufW).headD 0), 8] else []

/-- The freeze pass's word-level emitter. -/
def frEmitW (Q : List Bool → List Bool) (v : List Bool) : List Bool :=
  if (frMode (fvCli v)).length = 2 then
    dayBits (fvTok v) ++ Q (pair (dayClamp v) (frBuf (fvCli v)))
  else dayBits (fvTok v)

/-- Its block-level reading. -/
def frEmitR (Q : List Bool → List Bool) (n : ℕ) (cli : List Bool) (cur : List ℕ) :
    List Bool :=
  if (frMode cli).length = 2 then
    dayBits (digitsToBits cur) ++ Q (pair (unaryDay (min (digitVal cur) n)) (frBuf cli))
  else dayBits (digitsToBits cur)

lemma frEmitW_eq (Q : List Bool → List Bool) (W cli : List Bool) (cur : List ℕ)
    (hcur : ∀ d ∈ cur, d < 4) :
    frEmitW Q (pair W (pair cli (digitsToBits cur))) = frEmitR Q W.length cli cur := by
  rw [frEmitW, frEmitR, dayClamp]
  simp only [fvCli, fvTok, fvW, sndBlock_pair, fstBlock_pair,
    bitsToDigits_digitsToBits cur (fun d hd => lt_trans (hcur d hd) (by norm_num))]
  rfl

/-! ### The clamped selector and quote table

A word-level emitter cannot call an oracle at an unbounded day, so the pass computes the
freeze whose *selector and quote table are composed with the clamp*.  Nothing else changes:
the day token the emitter copies through is still the unclamped one, exactly as
`EF.freezeTokenEmitOn` emits it. -/

/-- The selector, read at the clamped day. -/
def clampSel (selCode : ℕ → ℕ → Bool) (n : ℕ) : ℕ → ℕ → Bool :=
  fun D c => selCode (min D n) c

/-- The quote table, read at the clamped day. -/
def clampQuote (quoteCode : ℕ → ℕ → ℕ) (n : ℕ) : ℕ → ℕ → ℕ :=
  fun D c => quoteCode (min D n) c

lemma blockWF_frEmitR {selCode : ℕ → ℕ → Bool} {quoteCode : ℕ → ℕ → ℕ}
    (E : QuoteOracle selCode quoteCode) (n : ℕ) (cli : List Bool) (cur : List ℕ)
    (hcur : ∀ d ∈ cur, d < 4) : BlockWF (frEmitR E.Q n cli cur) := by
  have hday : BlockWF (dayBits (digitsToBits cur)) := blockWF_run cur hcur
  rw [frEmitR]
  split_ifs
  · exact hday.append (E.Q_wf _ _)
  · exact hday

lemma decodeBits_frEmitR {selCode : ℕ → ℕ → Bool} {quoteCode : ℕ → ℕ → ℕ}
    (E : QuoteOracle selCode quoteCode) (n : ℕ) (cli : List Bool) (cur : List ℕ)
    (hcur : ∀ d ∈ cur, d < 4) :
    decodeBits (frEmitR E.Q n cli cur)
      = EF.freezeTokenEmitOn (clampSel selCode n) (clampQuote quoteCode n)
          (frPack cli) (digitVal cur) := by
  have hday : BlockWF (dayBits (digitsToBits cur)) := blockWF_run cur hcur
  have hdayd : decodeBits (dayBits (digitsToBits cur)) = [digitVal cur] :=
    decodeBits_run cur hcur
  have hmode : (frPack cli).1 = (frMode cli).length := rfl
  have hcode : (frPack cli).2 = (decodeBits (frBuf cli)).headD 0 := rfl
  rw [frEmitR, EF.freezeTokenEmitOn, hmode, hcode, clampSel, clampQuote]
  by_cases h2 : (frMode cli).length = 2
  · rw [if_pos h2, decodeBits_append hday (E.Q_wf _ _), hdayd, E.Q_spec]
    by_cases hs : selCode (min (digitVal cur) n) ((decodeBits (frBuf cli)).headD 0) = true
    · rw [if_pos hs, if_pos ⟨h2, hs⟩]
      rfl
    · rw [if_neg hs, if_neg (fun h => hs h.2)]
      simp
  · rw [if_neg h2, if_neg (fun h => h2 h.1)]
    exact hdayd

/-! ### Membership and the emission bound -/

lemma frEmitW_mem_FP {selCode : ℕ → ℕ → Bool} {quoteCode : ℕ → ℕ → ℕ}
    (E : QuoteOracle selCode quoteCode) : frEmitW E.Q ∈ FP := by
  have hW : fvW ∈ FP := fstBlock_mem_FP
  have hcli : fvCli ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have htok : fvTok ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
  have hm : (fun v => frMode (fvCli v)) ∈ FP := mem_FP_comp hcli fstBlock_mem_FP
  have hbuf : (fun v => frBuf (fvCli v)) ∈ FP := mem_FP_comp hcli sndBlock_mem_FP
  have hclamp : dayClamp ∈ FP := LEUnary.unaryOfDigitsLE_le_mem_FP htok hW
  have hq : (fun v => E.Q (pair (dayClamp v) (frBuf (fvCli v)))) ∈ FP :=
    mem_FP_comp (pairFn_mem_FP hclamp hbuf) E.Q_FP
  have hday : (fun v => dayBits (fvTok v)) ∈ FP :=
    appendFn_mem_FP htok (constFn_mem_FP (digitBits 4))
  exact ifEqLen_mem_FP hm 2 (appendFn_mem_FP hday hq) hday

lemma frEmitW_length_le {selCode : ℕ → ℕ → Bool} {quoteCode : ℕ → ℕ → ℕ}
    (E : QuoteOracle selCode quoteCode) (W cli tok : List Bool) :
    (frEmitW E.Q (pair W (pair cli tok))).length
      ≤ (Polynomial.C (E.Q_len + 3)).eval W.length + 1 * (cli.length + tok.length) := by
  have hcli : fvCli (pair W (pair cli tok)) = cli := by simp [fvCli]
  have htok : fvTok (pair W (pair cli tok)) = tok := by simp [fvTok]
  have hq := E.Q_length_le (pair (dayClamp (pair W (pair cli tok))) (frBuf cli))
  simp only [Polynomial.eval_C]
  rw [frEmitW, hcli, htok]
  split_ifs
  · rw [dayBits]
    simp only [List.length_append, length_digitBits]
    omega
  · rw [dayBits]
    simp only [List.length_append, length_digitBits]
    omega

/-! ## The freeze pass, decoded -/

/-- The initial client state: base mode, empty buffer. -/
def frInit : List Bool := frSt [] []

@[simp] lemma frPack_frInit : frPack frInit = (0, 0) := by
  simp [frPack, frInit, frCode]

@[simp] lemma frBuf_frInit : frBuf frInit = [] := by simp [frInit]

lemma decodeBits_runFold_freeze {selCode : ℕ → ℕ → Bool} {quoteCode : ℕ → ℕ → ℕ}
    (E : QuoteOracle selCode quoteCode) (n : ℕ) :
    ∀ (rs : List (List ℕ)) (cli out : List Bool),
      (∀ r ∈ rs, ∀ d ∈ r, d < 4) → BlockWF out →
      decodeBits (runFold frStepR (frEmitR E.Q n) cli out rs).2
        = decodeBits out
          ++ (EF.freezeTokenRunOn (clampSel selCode n) (clampQuote quoteCode n)
                (frPack cli) (rs.map digitVal)).2
  | [], cli, out, _, _ => by
      rw [runFold, List.map_nil]
      simp [EF.freezeTokenRunOn]
  | r :: rs, cli, out, hrs, hout => by
      have hr : ∀ d ∈ r, d < 4 := hrs r (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rs, ∀ d ∈ q, d < 4 :=
        fun q hq => hrs q (List.mem_cons_of_mem _ hq)
      have hemit : BlockWF (frEmitR E.Q n cli r) := blockWF_frEmitR E n cli r hr
      rw [runFold, decodeBits_runFold_freeze E n rs _ _ hrest (hout.append hemit),
        decodeBits_append hout hemit, frPack_frStepR cli r hr,
        decodeBits_frEmitR E n cli r hr, List.map_cons, EF.freezeTokenRunOn]
      simp only [List.append_assoc]

/-- **The freeze pass is polynomial time.**  `Wf` carries the trading day (the machine's own
input, through `FPFold.mem_FP_withInput`), `Sf` the trader's serialized stream, and `E` the
quote oracle.

Kind `C`; hypotheses `(a)` except `E`, which has no instance.
Paper node: `app:ifp` -/
lemma freezePass_mem_FP {selCode : ℕ → ℕ → Bool} {quoteCode : ℕ → ℕ → ℕ}
    (E : QuoteOracle selCode quoteCode) {Wf Sf : List Bool → List Bool}
    (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) :
    (fun z => (runFold frStepR (frEmitR E.Q (Wf z).length) frInit []
        (blockSplit (bitsToDigits (Sf z))).1).2) ∈ FP :=
  runFold_mem_FP (STEPr := fun _ => frStepR)
    (EMITr := fun W => frEmitR E.Q W.length)
    (c := 15) (k := 1) (qQ := Polynomial.C (E.Q_len + 3))
    frStepW_mem_FP (frEmitW_mem_FP E) hWf hSf
    frStepW_length_le (frEmitW_length_le E)
    (fun W cli cur h => frStepW_eq W cli cur h)
    (fun W cli cur h => frEmitW_eq E.Q W cli cur h) frInit []

/-- **And it computes the freeze.**  Decoding the pass's output word gives the token-level
`EF.freezeTokenRunOn` over the tokens the input stream denotes — with the selector and quote
table read at the clamped day, which is the disclosed boundary described in the header.

Kind `C`; hypotheses `(a)` except `E`; the clamp is a type-`(c)` substitution, disclosed
here, at `clampSel`/`clampQuote` and in this file's header.
Paper node: `app:ifp` -/
lemma decodeBits_freezePass {selCode : ℕ → ℕ → Bool} {quoteCode : ℕ → ℕ → ℕ}
    (E : QuoteOracle selCode quoteCode) (n : ℕ) (ds : List ℕ) :
    decodeBits (runFold frStepR (frEmitR E.Q n) frInit [] (blockSplit ds).1).2
      = (EF.freezeTokenRunOn (clampSel selCode n) (clampQuote quoteCode n) (0, 0)
          (undigitize ds)).2 := by
  have h := decodeBits_runFold_freeze E n (blockSplit ds).1 frInit []
    (fun r hr => (blockSplit_digits_lt ds).1 r hr) BlockWF.nil
  rw [frPack_frInit] at h
  simpa [← undigitize_eq_blockSplit] using h

#print axioms LogicalInduction.FreezeStep.frPack_frStepR
#print axioms LogicalInduction.FreezeStep.freezePass_mem_FP
#print axioms LogicalInduction.FreezeStep.decodeBits_freezePass

end LogicalInduction.FreezeStep
