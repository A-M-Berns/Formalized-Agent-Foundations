/-
# The conditioning automaton as a polynomial-time transduction

`Construction/Witnesses/RpnConditioning.lean` builds the price rewrite of `thm:scon` as a
token-level transducer, `rpnConditionRun`, and certifies it in the `dd:fuel` model.  This
file is the same transducer in the machine model: a client of
`Framework/Machine/TokenFold.lean`'s block fold, so that the rewrite is an honest
`Complexity.FP` function of the trader's serialized stream.

The three pieces, in the order they are built:

* **The state.**  Mode, open-subtree counter and run length are unary words, so that the
  automaton's tests are length comparisons; the buffered sentence run is carried as its own
  digit bits, so that the emitter can splice it without re-rendering it.  That choice is why
  the client reads token *blocks* rather than token values: a raw machine word may carry a
  non-canonical run, and copying it is then not a function of the value.

* **The step.**  `rcModeW`/`rcCntW`/`rcLenW` mirror the scalar decomposition
  `rcModeF`/`rcCntF`/`rcLenF` branch for branch, so both the agreement proofs and the
  membership proofs are uniform rather than bespoke — one `simp only` each for the former,
  a nest of two branch combinators for the latter.  `rpnCondStep_clamp` is what lets the
  token arrive as `min t 20` marks rather than an unbounded numeral.

* **The emitter.**  Its syntactic scaffolding is three fixed token lists, hence constant
  words; the buffered run is already in the state; and the condition block comes from an
  oracle indexed by unary days, called at `min D n`.

* **The count and the codes.**  `rpnTradeRuns` runs on the same automaton, so the trade-run
  count is a fourth client; the frame budget's two codes are then arithmetic on lengths.

* **The acceptance test.**  `rpnAcceptsRuns` asks two questions of the *finished* run, so
  that client reads `runFold`'s final state rather than its output and emits nothing.  Its
  state wraps the automaton's with one more unary counter, the parser depth — and the depth
  goes *first* in the pair, because `pair` doubles its first component and the cond-state is
  the one that grows with the token.

* **The guard.**  `rpnGuardedConditionTokens` emits the rewrite only when every price-day
  token is within the trading day.  That test is a second fold over the *same* automaton —
  `condStepR` again, so there is one word-level automaton, not two — whose emitter drops a
  mark at each violating position, and the guard holds exactly when the pass emits nothing.

**The clamp, and how it is discharged.**  `condEmitR` draws the condition block at
`min D n` rather than at `D`, because a word-level emitter cannot call an oracle at an
unbounded day; unclamped the claim would be *false*, not merely unproved, since a `k`-bit
day names up to `4 ^ k` marks.  `decodeBits_condPass` therefore states the price pass
against `clampedEmit`.  `rpnConditionRun_congr_of_guard` closes it: on a stream the guard
accepts, both emitters are called only at days `D ≤ n`, where `min D n = D`, so
`decodeBits_guardedPassW` states the guarded pass against the *true* emitter
`rpnPriceEmit`.  The fuel-model certificate `rpnGuardedConditionRun_polySegStream_of` reads
its emitted segment at the same clamped day for the same reason.

Everything here is construction infrastructure rather than a paper statement, so the
declarations are `lemma`s and carry no `Paper node:` line; the fuel-model counterparts in
`RpnConditioning.lean` (`rpnGuardedConditionRun_polySegStream` and its neighbours) are
`lemma`s for the same reason.
-/
import LogicalInduction.Construction.Witnesses.RpnConditioning
import LogicalInduction.Framework.Machine.TokenFold

namespace LogicalInduction.CondStep

open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold
open LogicalInduction.RpnConditioning LogicalInduction.ConditioningCompile


open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold
open LogicalInduction.RpnConditioning LogicalInduction.ConditioningCompile

/-- A natural number as a unary word. -/
abbrev uw (k : ℕ) : List Bool := List.replicate k true

@[simp] lemma length_uw (k : ℕ) : (uw k).length = k := by simp [uw]

/-! ## The three scalar components, on words -/

/-- `rcModeF` on unary words. -/
def rcModeW (mW cW tW : List Bool) : List Bool :=
  if mW.length = 0 then
    if tW.length = 0 then uw 1 else if tW.length = 1 then uw 3
    else if tW.length = 6 then uw 4
    else if tW.length = 7 then uw 5 else uw 0
  else if mW.length = 1 then
    if tW.length = 1 then uw 6
    else if tW.length = 2 then uw 1
    else if tW.length = 3 then uw 1
    else if tW.length = 4 then uw 1
    else if cW.length ≤ 1 then uw 2 else uw 1
  else if mW.length = 6 then
    if tW.length = 0 then uw 8 else if cW.length ≤ 1 then uw 2 else uw 1
  else if mW.length = 8 then
    if tW.length = 19 then (if cW.length ≤ 1 then uw 2 else uw 1) else uw 8
  else if mW.length = 4 then
    if tW.length = 1 then uw 7
    else if tW.length = 2 then uw 4
    else if tW.length = 3 then uw 4
    else if tW.length = 4 then uw 4
    else if cW.length ≤ 1 then uw 0 else uw 4
  else if mW.length = 7 then
    if tW.length = 0 then uw 9 else if cW.length ≤ 1 then uw 0 else uw 4
  else if mW.length = 9 then
    if tW.length = 19 then (if cW.length ≤ 1 then uw 0 else uw 4) else uw 9
  else uw 0

/-- `rcCntF` on unary words: the counter is carried, incremented by a mark, or
decremented by a `tail`. -/
def rcCntW (mW cW tW : List Bool) : List Bool :=
  if mW.length = 0 then
    (if tW.length = 0 then uw 1 else if tW.length = 6 then uw 1 else uw 0)
  else if mW.length = 1 then
    if tW.length = 1 then cW
    else if tW.length = 2 then cW ++ [true]
    else if tW.length = 3 then cW ++ [true]
    else if tW.length = 4 then cW ++ [true]
    else if cW.length ≤ 1 then uw 0 else cW.tail
  else if mW.length = 6 then
    if tW.length = 0 then cW else if cW.length ≤ 1 then uw 0 else cW.tail
  else if mW.length = 8 then
    if tW.length = 19 then (if cW.length ≤ 1 then uw 0 else cW.tail) else cW
  else if mW.length = 4 then
    if tW.length = 1 then cW
    else if tW.length = 2 then cW ++ [true]
    else if tW.length = 3 then cW ++ [true]
    else if tW.length = 4 then cW ++ [true]
    else if cW.length ≤ 1 then uw 0 else cW.tail
  else if mW.length = 7 then
    if tW.length = 0 then cW else if cW.length ≤ 1 then uw 0 else cW.tail
  else if mW.length = 9 then
    if tW.length = 19 then (if cW.length ≤ 1 then uw 0 else cW.tail) else cW
  else uw 0

/-- `rcLenF` on unary words. -/
def rcLenW (mW cW rW tW : List Bool) : List Bool :=
  if mW.length = 0 then uw 0
  else if mW.length = 1 then rW ++ [true]
  else if mW.length = 6 then rW ++ [true]
  else if mW.length = 8 then rW ++ [true]
  else if mW.length = 4 then
    if tW.length = 1 then rW ++ [true]
    else if tW.length = 2 then rW ++ [true]
    else if tW.length = 3 then rW ++ [true]
    else if tW.length = 4 then rW ++ [true]
    else if cW.length ≤ 1 then uw 0 else rW ++ [true]
  else if mW.length = 7 then
    if tW.length = 0 then rW ++ [true] else if cW.length ≤ 1 then uw 0 else rW ++ [true]
  else if mW.length = 9 then
    if tW.length = 19 then (if cW.length ≤ 1 then uw 0 else rW ++ [true])
    else rW ++ [true]
  else uw 0

/-! ### Agreement with the scalar components -/

lemma length_rcModeW (mW cW tW : List Bool) :
    (rcModeW mW cW tW).length = rcModeF mW.length cW.length tW.length := by
  rw [rcModeW, rcModeF]
  simp only [apply_ite List.length, length_uw]

lemma length_rcCntW (mW cW tW : List Bool) :
    (rcCntW mW cW tW).length = rcCntF mW.length cW.length tW.length := by
  rw [rcCntW, rcCntF]
  simp only [apply_ite List.length, length_uw, List.length_append, List.length_cons,
    List.length_nil, List.length_tail]

lemma length_rcLenW (mW cW rW tW : List Bool) :
    (rcLenW mW cW rW tW).length = rcLenF mW.length cW.length rW.length tW.length := by
  rw [rcLenW, rcLenF]
  simp only [apply_ite List.length, length_uw, List.length_append, List.length_cons,
    List.length_nil]

/-! ### Membership

Both branch shapes the automaton uses — "this counter or token equals the numeral `k`" and
"this counter is at most `k`" — are `selectHead` against a constant unary word.  With those
two the three functions above are mechanical nests. -/

private lemma ifEqLen_mem_FP {A X Y : List Bool → List Bool} (hA : A ∈ FP) (k : ℕ)
    (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if (A z).length = k then X z else Y z) ∈ FP := by
  have h := selectHeadFn_eqLen_mem_FP hA (constFn_mem_FP (uw k)) hX hY
  simp only [length_uw] at h
  exact h

private lemma ifLeLen_mem_FP {A X Y : List Bool → List Bool} (hA : A ∈ FP) (k : ℕ)
    (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if (A z).length ≤ k then X z else Y z) ∈ FP := by
  have h := selectHeadFn_leFlag_mem_FP (constFn_mem_FP (uw k)) hA hX hY
  simp only [length_uw] at h
  exact h

lemma rcModeW_mem_FP {M C T : List Bool → List Bool}
    (hM : M ∈ FP) (hC : C ∈ FP) (hT : T ∈ FP) :
    (fun z => rcModeW (M z) (C z) (T z)) ∈ FP := by
  have hu : ∀ k : ℕ, (fun _ : List Bool => uw k) ∈ FP := fun k => constFn_mem_FP (uw k)
  refine ifEqLen_mem_FP hM 0
    (ifEqLen_mem_FP hT 0 (hu 1) (ifEqLen_mem_FP hT 1 (hu 3)
      (ifEqLen_mem_FP hT 6 (hu 4) (ifEqLen_mem_FP hT 7 (hu 5) (hu 0))))) ?_
  refine ifEqLen_mem_FP hM 1
    (ifEqLen_mem_FP hT 1 (hu 6) (ifEqLen_mem_FP hT 2 (hu 1)
      (ifEqLen_mem_FP hT 3 (hu 1) (ifEqLen_mem_FP hT 4 (hu 1)
        (ifLeLen_mem_FP hC 1 (hu 2) (hu 1)))))) ?_
  refine ifEqLen_mem_FP hM 6
    (ifEqLen_mem_FP hT 0 (hu 8) (ifLeLen_mem_FP hC 1 (hu 2) (hu 1))) ?_
  refine ifEqLen_mem_FP hM 8
    (ifEqLen_mem_FP hT 19 (ifLeLen_mem_FP hC 1 (hu 2) (hu 1)) (hu 8)) ?_
  refine ifEqLen_mem_FP hM 4
    (ifEqLen_mem_FP hT 1 (hu 7) (ifEqLen_mem_FP hT 2 (hu 4)
      (ifEqLen_mem_FP hT 3 (hu 4) (ifEqLen_mem_FP hT 4 (hu 4)
        (ifLeLen_mem_FP hC 1 (hu 0) (hu 4)))))) ?_
  refine ifEqLen_mem_FP hM 7
    (ifEqLen_mem_FP hT 0 (hu 9) (ifLeLen_mem_FP hC 1 (hu 0) (hu 4))) ?_
  exact ifEqLen_mem_FP hM 9
    (ifEqLen_mem_FP hT 19 (ifLeLen_mem_FP hC 1 (hu 0) (hu 4)) (hu 9)) (hu 0)

lemma rcCntW_mem_FP {M C T : List Bool → List Bool}
    (hM : M ∈ FP) (hC : C ∈ FP) (hT : T ∈ FP) :
    (fun z => rcCntW (M z) (C z) (T z)) ∈ FP := by
  have hu : ∀ k : ℕ, (fun _ : List Bool => uw k) ∈ FP := fun k => constFn_mem_FP (uw k)
  have hsucc : (fun z => C z ++ [true]) ∈ FP :=
    appendFn_mem_FP hC (constFn_mem_FP [true])
  have hpred : (fun z => (C z).tail) ∈ FP := tail_mem_FP hC
  have hdec : ∀ X : List Bool → List Bool, X ∈ FP →
      (fun z => if (C z).length ≤ 1 then uw 0 else (C z).tail) ∈ FP :=
    fun _ _ => ifLeLen_mem_FP hC 1 (hu 0) hpred
  refine ifEqLen_mem_FP hM 0
    (ifEqLen_mem_FP hT 0 (hu 1) (ifEqLen_mem_FP hT 6 (hu 1) (hu 0))) ?_
  refine ifEqLen_mem_FP hM 1
    (ifEqLen_mem_FP hT 1 hC (ifEqLen_mem_FP hT 2 hsucc
      (ifEqLen_mem_FP hT 3 hsucc (ifEqLen_mem_FP hT 4 hsucc
        (ifLeLen_mem_FP hC 1 (hu 0) hpred))))) ?_
  refine ifEqLen_mem_FP hM 6
    (ifEqLen_mem_FP hT 0 hC (ifLeLen_mem_FP hC 1 (hu 0) hpred)) ?_
  refine ifEqLen_mem_FP hM 8
    (ifEqLen_mem_FP hT 19 (ifLeLen_mem_FP hC 1 (hu 0) hpred) hC) ?_
  refine ifEqLen_mem_FP hM 4
    (ifEqLen_mem_FP hT 1 hC (ifEqLen_mem_FP hT 2 hsucc
      (ifEqLen_mem_FP hT 3 hsucc (ifEqLen_mem_FP hT 4 hsucc
        (ifLeLen_mem_FP hC 1 (hu 0) hpred))))) ?_
  refine ifEqLen_mem_FP hM 7
    (ifEqLen_mem_FP hT 0 hC (ifLeLen_mem_FP hC 1 (hu 0) hpred)) ?_
  exact ifEqLen_mem_FP hM 9
    (ifEqLen_mem_FP hT 19 (ifLeLen_mem_FP hC 1 (hu 0) hpred) hC) (hu 0)

lemma rcLenW_mem_FP {M C R T : List Bool → List Bool}
    (hM : M ∈ FP) (hC : C ∈ FP) (hR : R ∈ FP) (hT : T ∈ FP) :
    (fun z => rcLenW (M z) (C z) (R z) (T z)) ∈ FP := by
  have hu : ∀ k : ℕ, (fun _ : List Bool => uw k) ∈ FP := fun k => constFn_mem_FP (uw k)
  have hsucc : (fun z => R z ++ [true]) ∈ FP :=
    appendFn_mem_FP hR (constFn_mem_FP [true])
  refine ifEqLen_mem_FP hM 0 (hu 0) ?_
  refine ifEqLen_mem_FP hM 1 hsucc ?_
  refine ifEqLen_mem_FP hM 6 hsucc ?_
  refine ifEqLen_mem_FP hM 8 hsucc ?_
  refine ifEqLen_mem_FP hM 4
    (ifEqLen_mem_FP hT 1 hsucc (ifEqLen_mem_FP hT 2 hsucc
      (ifEqLen_mem_FP hT 3 hsucc (ifEqLen_mem_FP hT 4 hsucc
        (ifLeLen_mem_FP hC 1 (hu 0) hsucc))))) ?_
  refine ifEqLen_mem_FP hM 7
    (ifEqLen_mem_FP hT 0 hsucc (ifLeLen_mem_FP hC 1 (hu 0) hsucc)) ?_
  exact ifEqLen_mem_FP hM 9
    (ifEqLen_mem_FP hT 19 (ifLeLen_mem_FP hC 1 (hu 0) hsucc) hsucc) (hu 0)

/-! ### The clamp, on the scalar components

`rpnCondStep_clamp` says the automaton tests only the small grammar tags; the three
components inherit that, which is what lets the word step carry the token as `min t 20`
marks instead of an unbounded numeral. -/

lemma rcModeF_clamp (m c t : ℕ) : rcModeF m c (min t 20) = rcModeF m c t := by
  have h := congrArg rcMode (rpnCondStep_clamp (rcPack m c 0) t)
  rwa [rcMode_step_eq, rcMode_step_eq, rcMode_pack, rcCnt_pack] at h

lemma rcCntF_clamp (m c t : ℕ) : rcCntF m c (min t 20) = rcCntF m c t := by
  have h := congrArg rcCnt (rpnCondStep_clamp (rcPack m c 0) t)
  rwa [rcCnt_step_eq, rcCnt_step_eq, rcMode_pack, rcCnt_pack] at h

lemma rcLenF_clamp (m c r t : ℕ) : rcLenF m c r (min t 20) = rcLenF m c r t := by
  have h := congrArg rcLen (rpnCondStep_clamp (rcPack m c r) t)
  rwa [rcLen_step_eq, rcLen_step_eq, rcMode_pack, rcCnt_pack, rcLen_pack] at h

/-! ## The client state

Mode, open-subtree counter and run length are unary words; the buffered sentence run is its
own digit bits, so that the emitter can splice it without re-rendering it. -/

def condSt (mW cW rW bufW : List Bool) : List Bool := pair (pair mW cW) (pair rW bufW)

def csMode (st : List Bool) : List Bool := fstBlock (fstBlock st)
def csCnt (st : List Bool) : List Bool := sndBlock (fstBlock st)
def csLen (st : List Bool) : List Bool := fstBlock (sndBlock st)
def csBuf (st : List Bool) : List Bool := sndBlock (sndBlock st)

@[simp] lemma csMode_condSt (m c r b : List Bool) : csMode (condSt m c r b) = m := by
  simp [csMode, condSt]
@[simp] lemma csCnt_condSt (m c r b : List Bool) : csCnt (condSt m c r b) = c := by
  simp [csCnt, condSt]
@[simp] lemma csLen_condSt (m c r b : List Bool) : csLen (condSt m c r b) = r := by
  simp [csLen, condSt]
@[simp] lemma csBuf_condSt (m c r b : List Bool) : csBuf (condSt m c r b) = b := by
  simp [csBuf, condSt]

/-- The automaton state a client state denotes. -/
def csPack (st : List Bool) : ℕ :=
  rcPack (csMode st).length (csCnt st).length (csLen st).length

/-- The buffered run a client state denotes. -/
def csTokens (st : List Bool) : List ℕ := decodeBits (csBuf st)

/-! ## The step, on words -/

def csModeStep (cli tw : List Bool) : List Bool := rcModeW (csMode cli) (csCnt cli) tw
def csCntStep (cli tw : List Bool) : List Bool := rcCntW (csMode cli) (csCnt cli) tw
def csLenStep (cli tw : List Bool) : List Bool :=
  rcLenW (csMode cli) (csCnt cli) (csLen cli) tw

/-- The buffer is the current sentence run: reset whenever the run length returns to zero,
extended by the incoming block otherwise.  The block is spliced *verbatim*, which is why the
client reads blocks rather than values. -/
def csBufStep (cli tw tok : List Bool) : List Bool :=
  if (csLenStep cli tw).length = 0 then [] else csBuf cli ++ tok ++ digitBits 4

def condStepOf (cli tw tok : List Bool) : List Bool :=
  condSt (csModeStep cli tw) (csCntStep cli tw) (csLenStep cli tw) (csBufStep cli tw tok)

/-- The client state slot of a step argument `pair W (pair cli tok)`. -/
def cvCli (v : List Bool) : List Bool := fstBlock (sndBlock v)
/-- The token-block slot of a step argument. -/
def cvTok (v : List Bool) : List Bool := sndBlock (sndBlock v)

/-- The incoming token, clamped to the automaton's test window and rendered in unary. -/
def clampTok (v : List Bool) : List Bool :=
  List.replicate (min (digitVal (bitsToDigits (cvTok v))) 20) true

/-- The price pass's word-level step. -/
def condStepW (v : List Bool) : List Bool :=
  condStepOf (cvCli v) (clampTok v) (cvTok v)

/-- Its block-level reading, which is what `TokenFold.runFold` folds. -/
def condStepR (cli : List Bool) (cur : List ℕ) : List Bool :=
  condStepOf cli (List.replicate (min (digitVal cur) 20) true) (digitsToBits cur)

/-- The word step reads a well-formed block exactly as `condStepR` does — by definition, so
`runFold_mem_FP`'s hypothesis is discharged without a side condition on the client. -/
lemma condStepW_eq (W cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    condStepW (pair W (pair cli (digitsToBits cur))) = condStepR cli cur := by
  rw [condStepW, condStepR, clampTok]
  simp only [cvCli, cvTok, sndBlock_pair, fstBlock_pair,
    bitsToDigits_digitsToBits cur (fun d hd => lt_trans (hcur d hd) (by norm_num))]

/-! ### Agreement with the paper-level automaton -/

lemma csPack_condStepR (cli : List Bool) (cur : List ℕ) :
    csPack (condStepR cli cur) = rpnCondStep (csPack cli) (digitVal cur) := by
  rw [condStepR, condStepOf, csPack, csMode_condSt, csCnt_condSt, csLen_condSt,
    csModeStep, csCntStep, csLenStep, length_rcModeW, length_rcCntW, length_rcLenW,
    List.length_replicate, rcModeF_clamp, rcCntF_clamp, rcLenF_clamp,
    rpnCondStep_components, csPack]
  simp [rcMode_pack, rcCnt_pack, rcLen_pack]

lemma csTokens_condStepR (cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4)
    (hwf : BlockWF (csBuf cli)) :
    csTokens (condStepR cli cur)
      = rpnCondBuf (csPack cli) (csTokens cli) (digitVal cur) := by
  obtain ⟨bd, hbd, hbd8, hbdc⟩ := hwf
  have hcond : (csLenStep cli (List.replicate (min (digitVal cur) 20) true)).length
      = rcLen (rpnCondStep (csPack cli) (digitVal cur)) := by
    rw [csLenStep, length_rcLenW, List.length_replicate, rcLenF_clamp, rcLen_step_eq, csPack]
    simp [rcMode_pack, rcCnt_pack, rcLen_pack]
  rw [csTokens, decodeBits, condStepR, condStepOf, csBuf_condSt, csBufStep, rpnCondBuf,
    hcond]
  by_cases h : rcLen (rpnCondStep (csPack cli) (digitVal cur)) = 0
  · rw [if_pos h, if_pos h]
    simp [bitsToDigits, undigitize]
  · have hterm : bitsToDigits (digitBits 4) = [4] := by
      have h4 := bitsToDigits_digitBits 4 (by norm_num) []
      rw [List.append_nil] at h4
      rw [h4]
      rfl
    rw [if_neg h, if_neg h, hbd, List.append_assoc,
      bitsToDigits_append_digitsToBits bd hbd8,
      bitsToDigits_append_digitsToBits cur
        (fun d hd => lt_trans (hcur d hd) (by norm_num)),
      hterm, undigitize_append_of_complete bd _ hbdc,
      (undigitize_run_terminator cur hcur).1, csTokens, decodeBits, hbd,
      bitsToDigits_digitsToBits bd hbd8]

lemma bufWF_condStepR (cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4)
    (hwf : BlockWF (csBuf cli)) : BlockWF (csBuf (condStepR cli cur)) := by
  obtain ⟨bd, hbd, hbd8, hbdc⟩ := hwf
  rw [condStepR, condStepOf, csBuf_condSt, csBufStep]
  by_cases h : (csLenStep cli (List.replicate (min (digitVal cur) 20) true)).length = 0
  · rw [if_pos h]; exact BlockWF.nil
  · rw [if_neg h]
    refine ⟨bd ++ (cur ++ [4]), ?_, ?_, ?_⟩
    · rw [digitsToBits_append, digitsToBits_append, hbd, List.append_assoc]
      rfl
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hbd8 d hd
      · rcases List.mem_append.mp hd with hd | hd
        · exact lt_trans (hcur d hd) (by norm_num)
        · simp at hd; omega
    · rw [blockSplit_append_of_complete bd _ hbdc]
      exact (undigitize_run_terminator cur hcur).2

/-! ### Membership and the state bound -/

lemma rcModeF_le (m c t : ℕ) : rcModeF m c t ≤ 9 := by
  have h := rcMode_step_le (rcPack m c 0) t
  rwa [rcMode_step_eq, rcMode_pack, rcCnt_pack] at h

lemma rcCntF_le (m c t : ℕ) : rcCntF m c t ≤ c + 1 := by
  have h := rcCnt_step_le (rcPack m c 0) t
  rwa [rcCnt_step_eq, rcMode_pack, rcCnt_pack] at h

lemma rcLenF_le (m c r t : ℕ) : rcLenF m c r t ≤ r + 1 := by
  have h := rcLen_step_le (rcPack m c r) t
  rwa [rcLen_step_eq, rcMode_pack, rcCnt_pack, rcLen_pack] at h

/-- The clamped token is polynomial time.  Every client below needs it. -/
lemma clampTok_mem_FP : clampTok ∈ FP := by
  have htok : cvTok ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
  have h := LEUnary.unaryOfDigitsLE_le_mem_FP htok (constFn_mem_FP (uw 20))
  simp only [length_uw] at h
  exact h

lemma cvCli_mem_FP : cvCli ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
lemma cvTok_mem_FP : cvTok ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
/-- The step is polynomial time at the level of `condStepOf`, so that a client wrapping the
state can reuse it. -/
lemma condStepOf_mem_FP {C TW T : List Bool → List Bool}
    (hC : C ∈ FP) (hTW : TW ∈ FP) (hT : T ∈ FP) :
    (fun v => condStepOf (C v) (TW v) (T v)) ∈ FP := by
  have hff : (fun v => fstBlock (C v)) ∈ FP := mem_FP_comp hC fstBlock_mem_FP
  have hsf : (fun v => sndBlock (C v)) ∈ FP := mem_FP_comp hC sndBlock_mem_FP
  have hm : (fun v => csMode (C v)) ∈ FP := mem_FP_comp hff fstBlock_mem_FP
  have hc : (fun v => csCnt (C v)) ∈ FP := mem_FP_comp hff sndBlock_mem_FP
  have hr : (fun v => csLen (C v)) ∈ FP := mem_FP_comp hsf fstBlock_mem_FP
  have hb : (fun v => csBuf (C v)) ∈ FP := mem_FP_comp hsf sndBlock_mem_FP
  have hlen : (fun v => csLenStep (C v) (TW v)) ∈ FP := rcLenW_mem_FP hm hc hr hTW
  have hbuf : (fun v => csBufStep (C v) (TW v) (T v)) ∈ FP :=
    ifEqLen_mem_FP hlen 0 (constFn_mem_FP [])
      (appendFn_mem_FP (appendFn_mem_FP hb hT) (constFn_mem_FP (digitBits 4)))
  exact pairFn_mem_FP (pairFn_mem_FP (rcModeW_mem_FP hm hc hTW) (rcCntW_mem_FP hm hc hTW))
    (pairFn_mem_FP hlen hbuf)

lemma condStepW_mem_FP : condStepW ∈ FP :=
  condStepOf_mem_FP cvCli_mem_FP clampTok_mem_FP cvTok_mem_FP

/-- The step's length bound, at the level of `condStepOf` so that a client wrapping the
state can reuse it.  The bound is *additive* in `cli` and in `tok`, and both coefficients
are load-bearing: `pair`'s framing doubles its first component, so a multiplier on either
would compound to `k ^ L` over the fold. -/
lemma condStepOf_length_le (cli tw tok : List Bool) :
    (condStepOf cli tw tok).length ≤ cli.length + tok.length + 51 := by
  have hm : (csModeStep cli tw).length ≤ 9 := by
    rw [csModeStep, length_rcModeW]; exact rcModeF_le _ _ _
  have hc : (csCntStep cli tw).length ≤ (csCnt cli).length + 1 := by
    rw [csCntStep, length_rcCntW]; exact rcCntF_le _ _ _
  have hr : (csLenStep cli tw).length ≤ (csLen cli).length + 1 := by
    rw [csLenStep, length_rcLenW]; exact rcLenF_le _ _ _ _
  have hb : (csBufStep cli tw tok).length ≤ (csBuf cli).length + tok.length + 3 := by
    rw [csBufStep]
    split_ifs
    · simp
    · simp only [List.length_append, length_digitBits]
      omega
  have H1 : 2 * (csMode cli).length + (csCnt cli).length ≤ (fstBlock cli).length :=
    two_fstBlock_add_sndBlock_le (fstBlock cli)
  have H2 : 2 * (csLen cli).length + (csBuf cli).length ≤ (sndBlock cli).length :=
    two_fstBlock_add_sndBlock_le (sndBlock cli)
  have H3 : 2 * (fstBlock cli).length + (sndBlock cli).length ≤ cli.length :=
    two_fstBlock_add_sndBlock_le cli
  rw [condStepOf, condSt, pair_length, pair_length, pair_length]
  omega

lemma condStepW_length_le (W cli tok : List Bool) :
    (condStepW (pair W (pair cli tok))).length ≤ cli.length + tok.length + 51 := by
  have hcli : cvCli (pair W (pair cli tok)) = cli := by simp [cvCli]
  have htok : cvTok (pair W (pair cli tok)) = tok := by simp [cvTok]
  rw [condStepW, hcli, htok]
  exact condStepOf_length_le cli _ tok

/-! ## The emitter

At a price-day position the rewrite splices the conditional price expression around the
buffered run; everywhere else it copies the token through.  Its syntactic scaffolding is
three fixed token lists — constant words — and the only data it needs beyond the state are
the incoming block and the condition block `blocks D`, which arrives from an oracle indexed
by unary days. -/

def emitConstA : List ℕ :=
  [1, Encodable.encode (-1 : ℚ), 1, Encodable.encode (-1 : ℚ),
   1, Encodable.encode (1 : ℚ), 3, 1, Encodable.encode (-1 : ℚ), 0, 3]

def emitConstB (ε : ℚ) : List ℕ :=
  [1, Encodable.encode (1 / ε : ℚ), 1, Encodable.encode (1 / ε : ℚ), 0]

def emitConstC : List ℕ := [3, 5, 3, 3, 3, 4, 3, 8]

lemma rpnConditionEmit_eq (blk : List ℕ) (ε : ℚ) (buf : List ℕ) (D : ℕ) :
    rpnConditionEmit blk ε buf D
      = [D] ++ emitConstA ++ buf ++ blk ++ [D] ++ emitConstB ε ++ blk
          ++ [D] ++ emitConstC := by
  rw [rpnConditionEmit, emitConstA, emitConstB, emitConstC]
  simp

/-- The incoming token, re-emitted as its own complete block. -/
def dayBits (tok : List Bool) : List Bool := tok ++ digitBits 4

/-- The price rewrite, on words. -/
def condEmitOf (ε : ℚ) (blkW bufW tok : List Bool) : List Bool :=
  dayBits tok ++ tokBits emitConstA ++ bufW ++ blkW
    ++ dayBits tok ++ tokBits (emitConstB ε) ++ blkW
    ++ dayBits tok ++ tokBits emitConstC

/-- The parameter slot of a step argument: the trading day, in unary. -/
def cvW (v : List Bool) : List Bool := fstBlock v

/-- The day the oracle is called at: the incoming token, clamped by the trading day.  The
clamp is not optional — an unbounded day would name an unbounded block — and on the guarded
path, where every price day is within the trading day, it is invisible. -/
def dayClamp (v : List Bool) : List Bool :=
  List.replicate (min (digitVal (bitsToDigits (cvTok v))) (cvW v).length) true

/-- The price pass's word-level emitter. -/
def condEmitW (ε : ℚ) (B : List Bool → List Bool) (v : List Bool) : List Bool :=
  if (csMode (cvCli v)).length = 2 then
    condEmitOf ε (B (dayClamp v)) (csBuf (cvCli v)) (cvTok v)
  else dayBits (cvTok v)

/-- Its block-level reading. -/
def condEmitR (ε : ℚ) (B : List Bool → List Bool) (n : ℕ)
    (cli : List Bool) (cur : List ℕ) : List Bool :=
  if (csMode cli).length = 2 then
    condEmitOf ε (B (unaryDay (min (digitVal cur) n))) (csBuf cli) (digitsToBits cur)
  else dayBits (digitsToBits cur)

lemma condEmitW_eq (ε : ℚ) (B : List Bool → List Bool) (W cli : List Bool)
    (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    condEmitW ε B (pair W (pair cli (digitsToBits cur)))
      = condEmitR ε B W.length cli cur := by
  rw [condEmitW, condEmitR, dayClamp]
  simp only [cvCli, cvTok, cvW, sndBlock_pair, fstBlock_pair,
    bitsToDigits_digitsToBits cur (fun d hd => lt_trans (hcur d hd) (by norm_num))]
  rfl

/-! ### What the emitter emits -/

lemma blockWF_condEmitR (ε : ℚ) (B : List Bool → List Bool) (n : ℕ) (cli : List Bool)
    (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) (hwf : BlockWF (csBuf cli))
    (hB : ∀ d, BlockWF (B (unaryDay d))) : BlockWF (condEmitR ε B n cli cur) := by
  have hday : BlockWF (dayBits (digitsToBits cur)) := blockWF_run cur hcur
  rw [condEmitR]
  split_ifs
  · exact ((((((((hday.append (blockWF_tokBits _)).append hwf).append (hB _)).append hday).append
      (blockWF_tokBits _)).append (hB _)).append hday).append (blockWF_tokBits _))
  · exact hday

lemma decodeBits_condEmitR (ε : ℚ) (B : List Bool → List Bool) (n : ℕ) (cli : List Bool)
    (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) (hwf : BlockWF (csBuf cli))
    (hB : ∀ d, BlockWF (B (unaryDay d))) :
    decodeBits (condEmitR ε B n cli cur)
      = if rcMode (csPack cli) = 2 then
          rpnConditionEmit (decodeBits (B (unaryDay (min (digitVal cur) n)))) ε
            (csTokens cli) (digitVal cur)
        else [digitVal cur] := by
  have hday : BlockWF (dayBits (digitsToBits cur)) := blockWF_run cur hcur
  have hdayd : decodeBits (dayBits (digitsToBits cur)) = [digitVal cur] :=
    decodeBits_run cur hcur
  have hmode : rcMode (csPack cli) = (csMode cli).length := by
    rw [csPack, rcMode_pack]
  rw [condEmitR, hmode]
  split_ifs
  · rw [condEmitOf, rpnConditionEmit_eq]
    rw [decodeBits_append (((((((hday.append (blockWF_tokBits _)).append hwf).append
        (hB _)).append hday).append (blockWF_tokBits _)).append (hB _)).append hday)
        (blockWF_tokBits _),
      decodeBits_append ((((((hday.append (blockWF_tokBits _)).append hwf).append
        (hB _)).append hday).append (blockWF_tokBits _)).append (hB _)) hday,
      decodeBits_append (((((hday.append (blockWF_tokBits _)).append hwf).append
        (hB _)).append hday).append (blockWF_tokBits _)) (hB _),
      decodeBits_append ((((hday.append (blockWF_tokBits _)).append hwf).append
        (hB _)).append hday) (blockWF_tokBits _),
      decodeBits_append (((hday.append (blockWF_tokBits _)).append hwf).append (hB _)) hday,
      decodeBits_append ((hday.append (blockWF_tokBits _)).append hwf) (hB _),
      decodeBits_append (hday.append (blockWF_tokBits _)) hwf,
      decodeBits_append hday (blockWF_tokBits _),
      hdayd, decodeBits_tokBits, decodeBits_tokBits, decodeBits_tokBits, csTokens]
  · exact hdayd

/-! ### Membership and the emission bound -/

lemma condEmitW_mem_FP (ε : ℚ) {B : List Bool → List Bool} (hB : B ∈ FP) :
    condEmitW ε B ∈ FP := by
  have hW : cvW ∈ FP := fstBlock_mem_FP
  have hcli : cvCli ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have htok : cvTok ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
  have hff : (fun v => fstBlock (cvCli v)) ∈ FP := mem_FP_comp hcli fstBlock_mem_FP
  have hsf : (fun v => sndBlock (cvCli v)) ∈ FP := mem_FP_comp hcli sndBlock_mem_FP
  have hm : (fun v => csMode (cvCli v)) ∈ FP := mem_FP_comp hff fstBlock_mem_FP
  have hbuf : (fun v => csBuf (cvCli v)) ∈ FP := mem_FP_comp hsf sndBlock_mem_FP
  have hclamp : dayClamp ∈ FP := LEUnary.unaryOfDigitsLE_le_mem_FP htok hW
  have hblk : (fun v => B (dayClamp v)) ∈ FP := mem_FP_comp hclamp hB
  have hday : (fun v => dayBits (cvTok v)) ∈ FP :=
    appendFn_mem_FP htok (constFn_mem_FP (digitBits 4))
  refine ifEqLen_mem_FP hm 2 ?_ hday
  exact appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
    (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
      (appendFn_mem_FP hday (constFn_mem_FP (tokBits emitConstA))) hbuf) hblk) hday)
        (constFn_mem_FP (tokBits (emitConstB ε)))) hblk) hday)
    (constFn_mem_FP (tokBits emitConstC))

/-- The scaffolding constant: the fixed part of one emission. -/
def emitConstLen (ε : ℚ) : ℕ :=
  9 + (tokBits emitConstA).length + (tokBits (emitConstB ε)).length
    + (tokBits emitConstC).length

lemma condEmitW_length_le (ε : ℚ) {B : List Bool → List Bool} {pB : Polynomial ℕ}
    (hBlen : ∀ w, (B w).length ≤ pB.eval w.length) (W cli tok : List Bool) :
    (condEmitW ε B (pair W (pair cli tok))).length
      ≤ (2 * pB + Polynomial.C (emitConstLen ε)).eval W.length
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
    Polynomial.eval_ofNat, emitConstLen]
  rw [condEmitW, hcli, htok]
  split_ifs
  · rw [condEmitOf, dayBits]
    simp only [List.length_append, length_digitBits]
    omega
  · rw [dayBits]
    simp only [List.length_append, length_digitBits]
    omega

/-! ## The price pass, decoded

The three pieces fit: folding `condStepR`/`condEmitR` over the blocks of a stream and
decoding the result is the paper-level price rewrite over the tokens that stream denotes.

The emitter is the *clamped* one — the condition block is drawn at `min D n` rather than at
`D` — because a word-level emitter cannot call an oracle at an unbounded day.  On the
guarded path the two agree, since the guard is exactly that every price day is within the
trading day; closing that gap is the guard pass's job. -/

/-- The price emitter with its oracle clamped to the trading day. -/
def clampedEmit (ε : ℚ) (B : List Bool → List Bool) (n : ℕ) : List ℕ → ℕ → List ℕ :=
  fun buf D => rpnConditionEmit (decodeBits (B (unaryDay (min D n)))) ε buf D

lemma decodeBits_runFold_condition (ε : ℚ) (B : List Bool → List Bool) (n : ℕ)
    (hB : ∀ d, BlockWF (B (unaryDay d))) :
    ∀ (rs : List (List ℕ)) (cli out : List Bool),
      (∀ r ∈ rs, ∀ d ∈ r, d < 4) → BlockWF (csBuf cli) → BlockWF out →
      decodeBits (runFold condStepR (condEmitR ε B n) cli out rs).2
        = decodeBits out
          ++ (rpnConditionRun (clampedEmit ε B n) (csPack cli, csTokens cli)
                (rs.map digitVal)).2
  | [], cli, out, _, _, _ => by
      rw [runFold, List.map_nil, rpnConditionRun_nil]
      simp
  | r :: rs, cli, out, hrs, hbuf, hout => by
      have hr : ∀ d ∈ r, d < 4 := hrs r (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rs, ∀ d ∈ q, d < 4 :=
        fun q hq => hrs q (List.mem_cons_of_mem _ hq)
      have hbuf' : BlockWF (csBuf (condStepR cli r)) := bufWF_condStepR cli r hr hbuf
      have hemit : BlockWF (condEmitR ε B n cli r) :=
        blockWF_condEmitR ε B n cli r hr hbuf hB
      rw [runFold, decodeBits_runFold_condition ε B n hB rs _ _ hrest hbuf'
          (hout.append hemit),
        decodeBits_append hout hemit, csPack_condStepR, csTokens_condStepR cli r hr hbuf,
        decodeBits_condEmitR ε B n cli r hr hbuf hB, List.map_cons]
      rw [show (csPack cli, csTokens cli) = ((csPack cli, csTokens cli).1,
            (csPack cli, csTokens cli).2) from rfl, rpnConditionRun]
      simp only [List.append_assoc]
      congr 1

/-! ## The price pass -/

/-- The initial client state: base mode, both counters zero, empty buffer. -/
def condInit : List Bool := condSt [] [] [] []

@[simp] lemma csPack_condInit : csPack condInit = rcPack 0 0 0 := by
  simp [csPack, condInit]

@[simp] lemma csTokens_condInit : csTokens condInit = [] := by
  simp [csTokens, condInit]

@[simp] lemma csBuf_condInit : csBuf condInit = [] := by simp [condInit]

/-- **The price pass is polynomial time.**  `Wf` carries the trading day (the machine's own
input, through `FPFold.mem_FP_withInput`), `Sf` the trader's serialized stream, and `B` the
condition-block oracle. -/
lemma condPass_mem_FP (ε : ℚ) {B Wf Sf : List Bool → List Bool}
    (hB : B ∈ FP) (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) :
    (fun z => (runFold condStepR (condEmitR ε B (Wf z).length) condInit []
        (blockSplit (bitsToDigits (Sf z))).1).2) ∈ FP := by
  obtain ⟨pB, hBlen⟩ := output_length_poly_of_mem_FP hB
  exact runFold_mem_FP (STEPr := fun _ => condStepR)
    (EMITr := fun W => condEmitR ε B W.length)
    (c := 51) (k := 3) (qQ := 2 * pB + Polynomial.C (emitConstLen ε))
    condStepW_mem_FP (condEmitW_mem_FP ε hB) hWf hSf
    condStepW_length_le (condEmitW_length_le ε hBlen)
    (fun W cli cur h => condStepW_eq W cli cur h)
    (fun W cli cur h => condEmitW_eq ε B W cli cur h) condInit []

/-- **And it computes the price rewrite.**  Decoding the pass's output word gives the
paper-level `rpnConditionRun` over the tokens the input stream denotes. -/
lemma decodeBits_condPass (ε : ℚ) (B : List Bool → List Bool) (n : ℕ)
    (hB : ∀ d, BlockWF (B (unaryDay d))) (rs : List (List ℕ))
    (hrs : ∀ r ∈ rs, ∀ d ∈ r, d < 4) :
    decodeBits (runFold condStepR (condEmitR ε B n) condInit [] rs).2
      = (rpnConditionRun (clampedEmit ε B n) (rcPack 0 0 0, []) (rs.map digitVal)).2 := by
  have h := decodeBits_runFold_condition ε B n hB rs condInit [] hrs
    (by simpa using BlockWF.nil) BlockWF.nil
  simpa using h

/-- The same, read against the trader's own token stream: the pass computes the price
rewrite of `undigitize (bitsToDigits ·)`, which is exactly what `strategyOfOutput` decodes. -/
lemma decodeBits_condPass_stream (ε : ℚ) (B : List Bool → List Bool) (n : ℕ)
    (hB : ∀ d, BlockWF (B (unaryDay d))) (ds : List ℕ) :
    decodeBits (runFold condStepR (condEmitR ε B n) condInit [] (blockSplit ds).1).2
      = (rpnConditionRun (clampedEmit ε B n) (rcPack 0 0 0, []) (undigitize ds)).2 := by
  rw [decodeBits_condPass ε B n hB _ (fun r hr => (blockSplit_digits_lt ds).1 r hr),
    ← undigitize_eq_blockSplit]


/-! ## The day guard

`rpnGuardedConditionTokens` emits the rewrite only when every price-day token is within the
trading day, and the empty stream otherwise.  That test is a second fold over the same
automaton — the state is `condStepR` again, so there is one word-level automaton, not two —
whose emitter drops a single mark at each violating position.  The guard holds exactly when
the pass emits nothing.

This is also what closes the clamp gap left by the price pass: `condEmitR` draws its
condition block at `min D n`, and on a stream the guard accepts, `min D n = D`. -/

/-- The number of price-day positions whose day token exceeds `n`.  Zero is exactly the
guard `rpnGuardedConditionTokens` tests.

This is the list-level form of `RpnConditioning.rpnBigDayFlagAt`, which the fuel model
scans positionally; the two characterizations (`guardMarks_eq_zero_iff` here,
`rpnBigDayFlagAt_eq_zero_iff` there) land on the same predicate.  A count rather than a
flag, because the fold's emitter accumulates a word and its length is what the count is. -/
def guardMarks (n : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | st, t :: ts =>
      (if rcMode st = 2 ∧ n < t then 1 else 0) + guardMarks n (rpnCondStep st t) ts

private lemma take_succ_foldl (st t : ℕ) (ts : List ℕ) (k : ℕ) :
    (((t :: ts).take (k + 1)).foldl rpnCondStep st)
      = (ts.take k).foldl rpnCondStep (rpnCondStep st t) := by
  rw [List.take_succ_cons, List.foldl_cons]

/-- The counter is zero exactly on the positional guard `rpnGuardedConditionTokens` uses. -/
lemma guardMarks_eq_zero_iff (n : ℕ) : ∀ (ts : List ℕ) (st : ℕ),
    guardMarks n st ts = 0 ↔
      ∀ j < ts.length, rcMode ((ts.take j).foldl rpnCondStep st) = 2 → ts.getD j 0 ≤ n
  | [], st => by simp [guardMarks]
  | t :: ts, st => by
      have ih := guardMarks_eq_zero_iff n ts (rpnCondStep st t)
      rw [guardMarks]
      constructor
      · rintro h j hj hm
        have hA : ¬ (rcMode st = 2 ∧ n < t) := by
          by_contra hc
          rw [if_pos hc] at h
          omega
        have hB : ∀ k < ts.length,
            rcMode ((ts.take k).foldl rpnCondStep (rpnCondStep st t)) = 2 →
              ts.getD k 0 ≤ n := by
          rw [if_neg hA, Nat.zero_add] at h
          exact ih.mp h
        cases j with
        | zero =>
            simp only [List.take_zero, List.foldl_nil, List.getD_cons_zero] at hm ⊢
            by_contra hlt
            exact hA ⟨hm, by omega⟩
        | succ k =>
            rw [take_succ_foldl] at hm
            simp only [List.length_cons] at hj
            simpa using hB k (by omega) hm
      · intro h
        have hA : ¬ (rcMode st = 2 ∧ n < t) := by
          rintro ⟨hm, hlt⟩
          have := h 0 (by simp) (by simpa using hm)
          simp only [List.getD_cons_zero] at this
          omega
        rw [if_neg hA, Nat.zero_add]
        refine ih.mpr ?_
        intro k hk hmk
        have := h (k + 1) (by simp; omega) (by rw [take_succ_foldl]; exact hmk)
        simpa using this

/-- **Emitters that agree on days within the guard give the same rewrite.**  This is the
closure of the clamp gap: on a stream the guard accepts, the clamped emitter and the true
one are called only at days `D ≤ n`, where `min D n = D`. -/
lemma rpnConditionRun_congr_of_guard (n : ℕ) {emit₁ emit₂ : List ℕ → ℕ → List ℕ}
    (h : ∀ (buf : List ℕ) (D : ℕ), D ≤ n → emit₁ buf D = emit₂ buf D) :
    ∀ (ts : List ℕ) (st : ℕ) (buf : List ℕ), guardMarks n st ts = 0 →
      rpnConditionRun emit₁ (st, buf) ts = rpnConditionRun emit₂ (st, buf) ts
  | [], st, buf, _ => rfl
  | t :: ts, st, buf, hg => by
      rw [guardMarks] at hg
      have hA : ¬ (rcMode st = 2 ∧ n < t) := by
        by_contra hc
        rw [if_pos hc] at hg
        omega
      have hB : guardMarks n (rpnCondStep st t) ts = 0 := by
        rw [if_neg hA, Nat.zero_add] at hg
        exact hg
      rw [rpnConditionRun, rpnConditionRun,
        rpnConditionRun_congr_of_guard n h ts (rpnCondStep st t) (rpnCondBuf st buf t) hB]
      by_cases hm : rcMode st = 2
      · rw [if_pos hm, if_pos hm, h buf t (by omega)]
      · rw [if_neg hm, if_neg hm]

/-! ### The guard emitter -/

/-- The day, clamped one *past* the trading day.  Clamping at `n` could not distinguish
`D = n` from `D > n`; clamping at `n + 1` makes `D ≤ n` a length comparison. -/
def dayClampSucc (v : List Bool) : List Bool :=
  List.replicate (min (digitVal (bitsToDigits (cvTok v))) (cvW v ++ [true]).length) true

/-- The guard pass's word-level emitter: one mark per violating price day. -/
def guardEmitW (v : List Bool) : List Bool :=
  if (csMode (cvCli v)).length = 2 then
    (if (dayClampSucc v).length ≤ (cvW v).length then [] else [true])
  else []

/-- Its block-level reading. -/
def guardEmitR (n : ℕ) (cli : List Bool) (cur : List ℕ) : List Bool :=
  if (csMode cli).length = 2 then (if digitVal cur ≤ n then [] else [true]) else []

lemma guardEmitW_eq (W cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    guardEmitW (pair W (pair cli (digitsToBits cur))) = guardEmitR W.length cli cur := by
  have hlen : (dayClampSucc (pair W (pair cli (digitsToBits cur)))).length
      = min (digitVal cur) (W.length + 1) := by
    rw [dayClampSucc, List.length_replicate]
    simp only [cvTok, cvW, sndBlock_pair, fstBlock_pair, List.length_append,
      List.length_cons, List.length_nil,
      bitsToDigits_digitsToBits cur (fun d hd => lt_trans (hcur d hd) (by norm_num))]
  rw [guardEmitW, guardEmitR, hlen]
  simp only [cvCli, cvW, sndBlock_pair, fstBlock_pair]
  by_cases hm : (csMode cli).length = 2
  · rw [if_pos hm, if_pos hm]
    by_cases h : digitVal cur ≤ W.length
    · rw [if_pos h,
        if_pos (by omega : min (digitVal cur) (W.length + 1) ≤ W.length)]
    · rw [if_neg h,
        if_neg (by omega : ¬ (min (digitVal cur) (W.length + 1) ≤ W.length))]
  · rw [if_neg hm, if_neg hm]

lemma guardEmitW_mem_FP : guardEmitW ∈ FP := by
  have hW : cvW ∈ FP := fstBlock_mem_FP
  have hcli : cvCli ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have htok : cvTok ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
  have hff : (fun v => fstBlock (cvCli v)) ∈ FP := mem_FP_comp hcli fstBlock_mem_FP
  have hm : (fun v => csMode (cvCli v)) ∈ FP := mem_FP_comp hff fstBlock_mem_FP
  have hsucc : dayClampSucc ∈ FP :=
    LEUnary.unaryOfDigitsLE_le_mem_FP htok
      (appendFn_mem_FP hW (constFn_mem_FP [true]))
  exact ifEqLen_mem_FP hm 2
    (selectHeadFn_leFlag_mem_FP hW hsucc (constFn_mem_FP []) (constFn_mem_FP [true]))
    (constFn_mem_FP [])

lemma guardEmitW_length_le (W cli tok : List Bool) :
    (guardEmitW (pair W (pair cli tok))).length
      ≤ (Polynomial.C 1 : Polynomial ℕ).eval W.length + 0 * (cli.length + tok.length) := by
  simp only [Polynomial.eval_C, Nat.zero_mul, Nat.add_zero]
  rw [guardEmitW]
  split_ifs <;> simp

/-! ### What the guard pass counts -/

lemma guardOut_length (n : ℕ) : ∀ (rs : List (List ℕ)) (cli out : List Bool),
    (runFold condStepR (guardEmitR n) cli out rs).2.length
      = out.length + guardMarks n (csPack cli) (rs.map digitVal)
  | [], cli, out => by rw [runFold, List.map_nil, guardMarks]; simp
  | r :: rs, cli, out => by
      have hmode : rcMode (csPack cli) = (csMode cli).length := by rw [csPack, rcMode_pack]
      rw [runFold, guardOut_length n rs (condStepR cli r) (out ++ guardEmitR n cli r),
        csPack_condStepR, List.map_cons, guardMarks, List.length_append, hmode]
      rw [guardEmitR]
      by_cases hm : (csMode cli).length = 2
      · rw [if_pos hm]
        by_cases hd : digitVal r ≤ n
        · rw [if_pos hd, if_neg (by omega)]
          simp
        · rw [if_neg hd, if_pos ⟨hm, by omega⟩]
          simp
          omega
      · rw [if_neg hm, if_neg (by tauto)]
        simp

lemma guardOut_eq_nil_iff (n : ℕ) (rs : List (List ℕ)) :
    (runFold condStepR (guardEmitR n) condInit [] rs).2 = []
      ↔ guardMarks n (rcPack 0 0 0) (rs.map digitVal) = 0 := by
  rw [← List.length_eq_zero_iff, guardOut_length n rs condInit [], csPack_condInit]
  simp

/-! ## The guarded price pass

The two folds run over the same blocks; the guard's output is empty exactly when the
rewrite is the one `rpnGuardedConditionTokens` asks for, and `selectHead` picks between
them.  The clamped emitter disappears here: on an accepted stream the congruence lemma
above replaces it by the true one. -/

/-- The condition-block sequence an oracle denotes. -/
def blocksOf (B : List Bool → List Bool) (d : ℕ) : List ℕ := decodeBits (B (unaryDay d))

/-- **The guard pass is polynomial time.** -/
lemma guardPass_mem_FP {Wf Sf : List Bool → List Bool} (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) :
    (fun z => (runFold condStepR (guardEmitR (Wf z).length) condInit []
        (blockSplit (bitsToDigits (Sf z))).1).2) ∈ FP :=
  runFold_mem_FP (STEPr := fun _ => condStepR) (EMITr := fun W => guardEmitR W.length)
    (c := 51) (k := 0) (qQ := Polynomial.C 1)
    condStepW_mem_FP guardEmitW_mem_FP hWf hSf
    condStepW_length_le guardEmitW_length_le
    (fun W cli cur h => condStepW_eq W cli cur h)
    (fun W cli cur h => guardEmitW_eq W cli cur h) condInit []

/-- The guarded price pass, on words. -/
def guardedPassW (ε : ℚ) (B Wf Sf : List Bool → List Bool) (z : List Bool) : List Bool :=
  selectHead
    (emptyFlag (runFold condStepR (guardEmitR (Wf z).length) condInit []
      (blockSplit (bitsToDigits (Sf z))).1).2)
    (runFold condStepR (condEmitR ε B (Wf z).length) condInit []
      (blockSplit (bitsToDigits (Sf z))).1).2
    []

/-- **The guarded price pass is polynomial time.** -/
lemma guardedPassW_mem_FP (ε : ℚ) {B Wf Sf : List Bool → List Bool}
    (hB : B ∈ FP) (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) :
    guardedPassW ε B Wf Sf ∈ FP :=
  selectHeadFn_mem_FP (emptyFlag_mem_FP (guardPass_mem_FP hWf hSf))
    (condPass_mem_FP ε hB hWf hSf) (constFn_mem_FP [])

/-- **And it computes the guarded rewrite** — with the true emitter, not the clamped one.
The clamp survives only inside the accepted branch, where `min D n = D`. -/
lemma decodeBits_guardedPass (ε : ℚ) (B : List Bool → List Bool) (n : ℕ)
    (hB : ∀ d, BlockWF (B (unaryDay d))) (ds : List ℕ) :
    decodeBits (selectHead
        (emptyFlag (runFold condStepR (guardEmitR n) condInit [] (blockSplit ds).1).2)
        (runFold condStepR (condEmitR ε B n) condInit [] (blockSplit ds).1).2 [])
      = rpnGuardedConditionTokens (rpnPriceEmit (blocksOf B) ε) n (undigitize ds) := by
  have hmap : (blockSplit ds).1.map digitVal = undigitize ds :=
    (undigitize_eq_blockSplit ds).symm
  by_cases hg : (runFold condStepR (guardEmitR n) condInit [] (blockSplit ds).1).2 = []
  · have hzero : guardMarks n (rcPack 0 0 0) (undigitize ds) = 0 := by
      rw [← hmap]
      exact (guardOut_eq_nil_iff n _).mp hg
    rw [hg, selectHead_emptyFlag_nil, decodeBits_condPass_stream ε B n hB ds,
      rpnGuardedConditionTokens,
      if_pos ((guardMarks_eq_zero_iff n (undigitize ds) (rcPack 0 0 0)).mp hzero)]
    exact congrArg Prod.snd
      (rpnConditionRun_congr_of_guard n
        (fun buf D hD => by
          rw [clampedEmit, rpnPriceEmit, blocksOf, Nat.min_eq_left hD])
        (undigitize ds) (rcPack 0 0 0) [] hzero)
  · obtain ⟨b, bs, hbs⟩ : ∃ b bs,
        (runFold condStepR (guardEmitR n) condInit [] (blockSplit ds).1).2 = b :: bs := by
      cases hc : (runFold condStepR (guardEmitR n) condInit [] (blockSplit ds).1).2 with
      | nil => exact absurd hc hg
      | cons b bs => exact ⟨b, bs, rfl⟩
    have hne : guardMarks n (rcPack 0 0 0) (undigitize ds) ≠ 0 := by
      rw [← hmap]
      intro hc
      exact hg ((guardOut_eq_nil_iff n _).mpr hc)
    rw [hbs, selectHead_emptyFlag_cons, decodeBits_nil, rpnGuardedConditionTokens,
      if_neg (fun hc => hne
        ((guardMarks_eq_zero_iff n (undigitize ds) (rcPack 0 0 0)).mpr hc))]

/-- **The guarded price pass, end to end.**  Decoding the pass's output word gives exactly
`rpnGuardedConditionTokens` over the token stream `strategyOfOutput` reads off `Sf z`, with
the trading day taken from `Wf z`.  This is the first of the four passes of
`rpnConditionOutput`, and the only one whose emitter needed a clamp. -/
lemma decodeBits_guardedPassW (ε : ℚ) (B Wf Sf : List Bool → List Bool)
    (hB : ∀ d, BlockWF (B (unaryDay d))) (z : List Bool) :
    decodeBits (guardedPassW ε B Wf Sf z)
      = rpnGuardedConditionTokens (rpnPriceEmit (blocksOf B) ε) (Wf z).length
          (undigitize (bitsToDigits (Sf z))) :=
  decodeBits_guardedPass ε B (Wf z).length hB (bitsToDigits (Sf z))

/-! ## The trade-run count pass

`rpnTradeRuns` runs on `rpnCondStep` too, so the count is a fourth client of the same
word-level automaton: its emitter drops one mark wherever the automaton was inside a trade
sentence and the step returns it to base.  The pass's output *length* is the count, which is
the form the budget rendering below needs it in. -/

/-- The clamped token at a well-formed block, once and for all. -/
lemma clampTok_pair (W cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    clampTok (pair W (pair cli (digitsToBits cur)))
      = List.replicate (min (digitVal cur) 20) true := by
  rw [clampTok]
  simp only [cvTok, sndBlock_pair,
    bitsToDigits_digitsToBits cur (fun d hd => lt_trans (hcur d hd) (by norm_num))]

/-- The mode the step lands in, as the paper automaton sees it. -/
lemma length_csModeStep (cli : List Bool) (cur : List ℕ) :
    (csModeStep cli (List.replicate (min (digitVal cur) 20) true)).length
      = rcMode (rpnCondStep (csPack cli) (digitVal cur)) := by
  rw [csModeStep, length_rcModeW, List.length_replicate, rcModeF_clamp, rcMode_step_eq,
    csPack]
  simp [rcMode_pack, rcCnt_pack]

/-- One mark per completed trade run. -/
def countEmitOf (cli tw : List Bool) : List Bool :=
  if (csModeStep cli tw).length = 0 then
    (if (csMode cli).length = 4 then [true]
     else if (csMode cli).length = 7 then [true]
     else if (csMode cli).length = 9 then [true]
     else [])
  else []

/-- The count pass's word-level emitter. -/
def countEmitW (v : List Bool) : List Bool := countEmitOf (cvCli v) (clampTok v)

/-- Its block-level reading. -/
def countEmitR (cli : List Bool) (cur : List ℕ) : List Bool :=
  countEmitOf cli (List.replicate (min (digitVal cur) 20) true)

lemma countEmitW_eq (W cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    countEmitW (pair W (pair cli (digitsToBits cur))) = countEmitR cli cur := by
  rw [countEmitW, countEmitR, clampTok_pair W cli cur hcur]
  simp only [cvCli, sndBlock_pair, fstBlock_pair]

lemma countEmitW_mem_FP : countEmitW ∈ FP := by
  have hcli : cvCli ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have htok : cvTok ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
  have hclamp : clampTok ∈ FP := by
    have h := LEUnary.unaryOfDigitsLE_le_mem_FP htok (constFn_mem_FP (uw 20))
    simp only [length_uw] at h
    exact h
  have hff : (fun v => fstBlock (cvCli v)) ∈ FP := mem_FP_comp hcli fstBlock_mem_FP
  have hsf : (fun v => sndBlock (cvCli v)) ∈ FP := mem_FP_comp hcli sndBlock_mem_FP
  have hm : (fun v => csMode (cvCli v)) ∈ FP := mem_FP_comp hff fstBlock_mem_FP
  have hc : (fun v => csCnt (cvCli v)) ∈ FP := mem_FP_comp hff sndBlock_mem_FP
  have hstep : (fun v => csModeStep (cvCli v) (clampTok v)) ∈ FP :=
    rcModeW_mem_FP hm hc hclamp
  exact ifEqLen_mem_FP hstep 0
    (ifEqLen_mem_FP hm 4 (constFn_mem_FP [true])
      (ifEqLen_mem_FP hm 7 (constFn_mem_FP [true])
        (ifEqLen_mem_FP hm 9 (constFn_mem_FP [true]) (constFn_mem_FP []))))
    (constFn_mem_FP [])

lemma countEmitW_length_le (W cli tok : List Bool) :
    (countEmitW (pair W (pair cli tok))).length
      ≤ (Polynomial.C 1 : Polynomial ℕ).eval W.length + 0 * (cli.length + tok.length) := by
  simp only [Polynomial.eval_C, Nat.zero_mul, Nat.add_zero]
  rw [countEmitW, countEmitOf]
  split_ifs <;> simp

lemma countOut_length : ∀ (rs : List (List ℕ)) (cli out : List Bool),
    (runFold condStepR countEmitR cli out rs).2.length
      = out.length + rpnTradeRuns (csPack cli) (rs.map digitVal)
  | [], cli, out => by rw [runFold, List.map_nil, rpnTradeRuns]; simp
  | r :: rs, cli, out => by
      have hmode : rcMode (csPack cli) = (csMode cli).length := by rw [csPack, rcMode_pack]
      rw [runFold, countOut_length rs (condStepR cli r) (out ++ countEmitR cli r),
        csPack_condStepR, List.map_cons, rpnTradeRuns, List.length_append,
        countEmitR, countEmitOf, ← length_csModeStep cli r, hmode]
      by_cases hz : (csModeStep cli (List.replicate (min (digitVal r) 20) true)).length = 0
      · rw [if_pos hz]
        by_cases h4 : (csMode cli).length = 4
        · rw [if_pos h4, if_pos (by tauto)]; simp; omega
        · by_cases h7 : (csMode cli).length = 7
          · rw [if_neg h4, if_pos h7, if_pos (by tauto)]; simp; omega
          · by_cases h9 : (csMode cli).length = 9
            · rw [if_neg h4, if_neg h7, if_pos h9, if_pos (by tauto)]; simp; omega
            · rw [if_neg h4, if_neg h7, if_neg h9, if_neg (by tauto)]; simp
      · rw [if_neg hz, if_neg (by tauto)]; simp

/-- **The count pass is polynomial time.** -/
lemma countPass_mem_FP {Wf Sf : List Bool → List Bool} (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) :
    (fun z => (runFold condStepR countEmitR condInit []
        (blockSplit (bitsToDigits (Sf z))).1).2) ∈ FP :=
  runFold_mem_FP (STEPr := fun _ => condStepR) (EMITr := fun _ => countEmitR)
    (c := 51) (k := 0) (qQ := Polynomial.C 1)
    condStepW_mem_FP countEmitW_mem_FP hWf hSf
    condStepW_length_le countEmitW_length_le
    (fun W cli cur h => condStepW_eq W cli cur h)
    (fun W cli cur h => countEmitW_eq W cli cur h) condInit []

/-- The count the pass reports, on the tokens its input denotes. -/
lemma countOut_length_stream (ds : List ℕ) :
    (runFold condStepR countEmitR condInit [] (blockSplit ds).1).2.length
      = rpnTradeRuns (rcPack 0 0 0) (undigitize ds) := by
  rw [countOut_length _ condInit [], csPack_condInit, ← undigitize_eq_blockSplit]
  simp

/-! ## The budget codes

The frame pass's budget is a rational whose code is an arithmetic function of the trading
day and the trade-run count — the first thing in this development that the machine must
*compute* rather than copy or splice.  Both inputs are lengths, so the arithmetic is unary
(`++` for sums, `TokenFold.uMul` for products), and `TokenFold.unaryBlock` renders the
result into the stream.  The run it renders is deliberately not `natDigits4`'s: `undigitize`
reads a block's value, and that is what `decodeBits_unaryBlock` fixes.

**Unary intermediates are the deliberate choice here.**  `Nat.pair 2 den` has magnitude
`den ^ 2`, so `uPair` builds a word of that many marks before `unaryBlock` renders it back
down to `O(log den)` digits.  With the day `n` and the count both bounded by the input
length `L`, that intermediate is `O(L ^ 6)` — large, but polynomial, which is all `FP`
asks.  A binary implementation would be smaller and is *not* available: the fork's
`binaryMulAddTM` is repeated addition, linear in the value of its right operand rather than
in its width, so routing this through the machine layer would have been asymptotically
worse than the unary route despite looking tighter. -/

/-- `Nat.pair` on unary numerals. -/
def uPair (aW bW : List Bool) : List Bool :=
  if aW.length < bW.length then uMul bW bW ++ aW else uMul aW aW ++ aW ++ bW

@[simp] lemma length_uPair (aW bW : List Bool) :
    (uPair aW bW).length = Nat.pair aW.length bW.length := by
  rw [uPair, Nat.pair]
  split_ifs with h
  · simp
  · simp
    omega

lemma uPair_mem_FP {A B : List Bool → List Bool} (hA : A ∈ FP) (hB : B ∈ FP) :
    (fun z => uPair (A z) (B z)) ∈ FP := by
  have h := selectHeadFn_leFlag_mem_FP hA hB
    (appendFn_mem_FP (appendFn_mem_FP (uMul_mem_FP hA hA) hA) hB)
    (appendFn_mem_FP (uMul_mem_FP hB hB) hA)
  have heq : (fun z => if (B z).length ≤ (A z).length then
        uMul (A z) (A z) ++ A z ++ B z else uMul (B z) (B z) ++ A z)
      = fun z => uPair (A z) (B z) := by
    funext z
    rw [uPair]
    by_cases hc : (A z).length < (B z).length
    · rw [if_pos hc, if_neg (by omega)]
    · rw [if_neg hc, if_pos (by omega)]
  rwa [heq] at h

/-- The budget denominator `(n + 1)(n + 2)·count`, as a unary numeral. -/
def denW (nW cntW : List Bool) : List Bool :=
  uMul (nW ++ [true]) (uMul (nW ++ [true, true]) cntW)

@[simp] lemma length_denW (nW cntW : List Bool) :
    (denW nW cntW).length = frameBudgetDenominator nW.length cntW.length := by
  simp only [denW, length_uMul, List.length_append, List.length_cons, List.length_nil,
    frameBudgetDenominator]
  ring

lemma denW_mem_FP {N C : List Bool → List Bool} (hN : N ∈ FP) (hC : C ∈ FP) :
    (fun z => denW (N z) (C z)) ∈ FP :=
  uMul_mem_FP (appendFn_mem_FP hN (constFn_mem_FP [true]))
    (uMul_mem_FP (appendFn_mem_FP hN (constFn_mem_FP [true, true])) hC)

/-- The frame budget's code, as one complete token block. -/
def budgetCodeW (nW cntW : List Bool) : List Bool :=
  selectHead (emptyFlag cntW) (tokBits [Encodable.encode (0 : ℚ)])
    (unaryBlock (uPair (uw 2) (denW nW cntW)))

/-- The inverse budget's code, as one complete token block. -/
def invBudgetCodeW (nW cntW : List Bool) : List Bool :=
  selectHead (emptyFlag cntW) (tokBits [Encodable.encode (0 : ℚ)])
    (unaryBlock (uPair (denW nW cntW ++ denW nW cntW) (uw 1)))

lemma budgetCodeW_mem_FP {N C : List Bool → List Bool} (hN : N ∈ FP) (hC : C ∈ FP) :
    (fun z => budgetCodeW (N z) (C z)) ∈ FP :=
  selectHeadFn_mem_FP (emptyFlag_mem_FP hC)
    (constFn_mem_FP (tokBits [Encodable.encode (0 : ℚ)]))
    (unaryBlock_mem_FP (uPair_mem_FP (constFn_mem_FP (uw 2)) (denW_mem_FP hN hC)))

lemma invBudgetCodeW_mem_FP {N C : List Bool → List Bool} (hN : N ∈ FP) (hC : C ∈ FP) :
    (fun z => invBudgetCodeW (N z) (C z)) ∈ FP :=
  selectHeadFn_mem_FP (emptyFlag_mem_FP hC)
    (constFn_mem_FP (tokBits [Encodable.encode (0 : ℚ)]))
    (unaryBlock_mem_FP (uPair_mem_FP
      (appendFn_mem_FP (denW_mem_FP hN hC) (denW_mem_FP hN hC)) (constFn_mem_FP (uw 1))))

lemma blockWF_budgetCodeW (nW cntW : List Bool) : BlockWF (budgetCodeW nW cntW) := by
  rw [budgetCodeW]
  cases cntW with
  | nil => rw [selectHead_emptyFlag_nil]; exact blockWF_tokBits _
  | cons b bs => rw [selectHead_emptyFlag_cons]; exact blockWF_unaryBlock _

lemma blockWF_invBudgetCodeW (nW cntW : List Bool) : BlockWF (invBudgetCodeW nW cntW) := by
  rw [invBudgetCodeW]
  cases cntW with
  | nil => rw [selectHead_emptyFlag_nil]; exact blockWF_tokBits _
  | cons b bs => rw [selectHead_emptyFlag_cons]; exact blockWF_unaryBlock _

@[simp] lemma decodeBits_budgetCodeW (nW cntW : List Bool) :
    decodeBits (budgetCodeW nW cntW) = [frameBudgetCode nW.length cntW.length] := by
  rw [budgetCodeW, frameBudgetCode]
  cases cntW with
  | nil =>
      rw [selectHead_emptyFlag_nil, decodeBits_tokBits, if_pos (by simp)]
  | cons b bs =>
      rw [selectHead_emptyFlag_cons, decodeBits_unaryBlock, if_neg (by simp),
        length_uPair, length_denW, length_uw]

@[simp] lemma decodeBits_invBudgetCodeW (nW cntW : List Bool) :
    decodeBits (invBudgetCodeW nW cntW) = [frameInverseBudgetCode nW.length cntW.length] := by
  rw [invBudgetCodeW, frameInverseBudgetCode]
  cases cntW with
  | nil =>
      rw [selectHead_emptyFlag_nil, decodeBits_tokBits, if_pos (by simp)]
  | cons b bs =>
      rw [selectHead_emptyFlag_cons, decodeBits_unaryBlock, if_neg (by simp),
        length_uPair, List.length_append, length_denW, length_uw]
      ring_nf

/-! ## The three passes composed

`rpnConditionOutput` takes the trade-run count *of the priced stream* and turns it into the
frame budget's two codes.  Composing the passes reproduces exactly that: the count runs over
the guarded pass's own output word, and the codes are rendered from it. -/

/-- The trade-run count of the priced stream, as a unary word. -/
def countW (ε : ℚ) (B Wf Sf : List Bool → List Bool) (z : List Bool) : List Bool :=
  (runFold condStepR countEmitR condInit []
    (blockSplit (bitsToDigits (guardedPassW ε B Wf Sf z))).1).2

/-- The frame budget's code, and its inverse's, at the day and count of the passes. -/
def budgetW (ε : ℚ) (B Wf Sf : List Bool → List Bool) (z : List Bool) : List Bool :=
  budgetCodeW (Wf z) (countW ε B Wf Sf z)

def invBudgetW (ε : ℚ) (B Wf Sf : List Bool → List Bool) (z : List Bool) : List Bool :=
  invBudgetCodeW (Wf z) (countW ε B Wf Sf z)

lemma countW_mem_FP (ε : ℚ) {B Wf Sf : List Bool → List Bool}
    (hB : B ∈ FP) (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) : countW ε B Wf Sf ∈ FP :=
  countPass_mem_FP hWf (guardedPassW_mem_FP ε hB hWf hSf)

lemma budgetW_mem_FP (ε : ℚ) {B Wf Sf : List Bool → List Bool}
    (hB : B ∈ FP) (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) : budgetW ε B Wf Sf ∈ FP :=
  budgetCodeW_mem_FP hWf (countW_mem_FP ε hB hWf hSf)

lemma invBudgetW_mem_FP (ε : ℚ) {B Wf Sf : List Bool → List Bool}
    (hB : B ∈ FP) (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) : invBudgetW ε B Wf Sf ∈ FP :=
  invBudgetCodeW_mem_FP hWf (countW_mem_FP ε hB hWf hSf)

/-- **The count is the paper's.** -/
lemma countW_length (ε : ℚ) (B Wf Sf : List Bool → List Bool)
    (hB : ∀ d, BlockWF (B (unaryDay d))) (z : List Bool) :
    (countW ε B Wf Sf z).length
      = rpnTradeRuns (rcPack 0 0 0)
          (rpnGuardedConditionTokens (rpnPriceEmit (blocksOf B) ε) (Wf z).length
            (undigitize (bitsToDigits (Sf z)))) := by
  rw [countW, countOut_length_stream, ← decodeBits, decodeBits_guardedPassW ε B Wf Sf hB z]

/-- **And the codes are the paper's**, at that count.
These are the two budget arguments `rpnConditionOutput` hands the frame pass. -/
lemma decodeBits_budgetW (ε : ℚ) (B Wf Sf : List Bool → List Bool)
    (hB : ∀ d, BlockWF (B (unaryDay d))) (z : List Bool) :
    decodeBits (budgetW ε B Wf Sf z)
      = [frameBudgetCode (Wf z).length
          (rpnTradeRuns (rcPack 0 0 0)
            (rpnGuardedConditionTokens (rpnPriceEmit (blocksOf B) ε) (Wf z).length
              (undigitize (bitsToDigits (Sf z)))))] := by
  rw [budgetW, decodeBits_budgetCodeW, countW_length ε B Wf Sf hB z]

lemma decodeBits_invBudgetW (ε : ℚ) (B Wf Sf : List Bool → List Bool)
    (hB : ∀ d, BlockWF (B (unaryDay d))) (z : List Bool) :
    decodeBits (invBudgetW ε B Wf Sf z)
      = [frameInverseBudgetCode (Wf z).length
          (rpnTradeRuns (rcPack 0 0 0)
            (rpnGuardedConditionTokens (rpnPriceEmit (blocksOf B) ε) (Wf z).length
              (undigitize (bitsToDigits (Sf z)))))] := by
  rw [invBudgetW, decodeBits_invBudgetCodeW, countW_length ε B Wf Sf hB z]

/-! ## The acceptance test

`rpnAcceptsRuns` asks two questions of the *finished* run — did the automaton return to
base, and did the parser depth return to zero — so this client reads `runFold`'s final
client state rather than its output, and emits nothing at all.  Its state wraps
`condStepR`'s with one more unary counter, the depth.

**Component order in the packed state is load-bearing.**  `pair` doubles its first
component, and the cond-state is the one that grows with the incoming token (its buffer
splices the block in).  Putting it second keeps the step's bound additive in `tok`; putting
it first would give coefficient two there, and a coefficient-two bound on `tok` compounds
across the fold exactly as one on `cli` does.  So the depth goes first. -/

/-- The parser depth's update, `rpnDepthNext` on words.  Written to mirror it branch for
branch; `depthNextW_eq_nested` is the same function as a nest of single comparisons, which
is the form the membership proof needs. -/
def depthNextW (cs tw dW : List Bool) : List Bool :=
  if (csMode cs).length = 0 then
    (if tw.length = 2 then dW.tail
     else if tw.length = 3 then dW.tail
     else if tw.length = 4 then dW.tail
     else if tw.length = 8 then dW.tail
     else dW)
  else if (csMode cs).length = 2 then dW ++ [true]
  else if (csMode cs).length = 3 then dW ++ [true]
  else if (csMode cs).length = 5 then dW ++ [true]
  else if ((csMode cs).length = 4 ∨ (csMode cs).length = 7 ∨ (csMode cs).length = 9)
      ∧ (csModeStep cs tw).length = 0 then dW.tail
  else dW

lemma length_depthNextW (cs dW : List Bool) (cur : List ℕ) :
    (depthNextW cs (List.replicate (min (digitVal cur) 20) true) dW).length
      = rpnDepthNext (csPack cs) (rpnCondStep (csPack cs) (digitVal cur)) (digitVal cur)
          dW.length := by
  have hm : (csMode cs).length = rcMode (csPack cs) := by rw [csPack, rcMode_pack]
  have hstep := length_csModeStep cs cur
  have e2 : (min (digitVal cur) 20 = 2) ↔ (digitVal cur = 2) := by omega
  have e3 : (min (digitVal cur) 20 = 3) ↔ (digitVal cur = 3) := by omega
  have e4 : (min (digitVal cur) 20 = 4) ↔ (digitVal cur = 4) := by omega
  have e8 : (min (digitVal cur) 20 = 8) ↔ (digitVal cur = 8) := by omega
  rw [depthNextW, rpnDepthNext, parserDepthNext, hm, hstep]
  simp only [apply_ite List.length, List.length_tail, List.length_append,
    List.length_cons, List.length_nil, List.length_replicate, e2, e3, e4, e8,
    if_true, Nat.pred_eq_sub_one]

private lemma ifMode479_mem_FP {A B X Y : List Bool → List Bool}
    (hA : A ∈ FP) (hB : B ∈ FP) (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if ((A z).length = 4 ∨ (A z).length = 7 ∨ (A z).length = 9)
        ∧ (B z).length = 0 then X z else Y z) ∈ FP := by
  have h := ifEqLen_mem_FP hA 4 (ifEqLen_mem_FP hB 0 hX hY)
    (ifEqLen_mem_FP hA 7 (ifEqLen_mem_FP hB 0 hX hY)
      (ifEqLen_mem_FP hA 9 (ifEqLen_mem_FP hB 0 hX hY) hY))
  have heq : (fun z => if (A z).length = 4 then (if (B z).length = 0 then X z else Y z)
        else if (A z).length = 7 then (if (B z).length = 0 then X z else Y z)
        else if (A z).length = 9 then (if (B z).length = 0 then X z else Y z) else Y z)
      = fun z => if ((A z).length = 4 ∨ (A z).length = 7 ∨ (A z).length = 9)
          ∧ (B z).length = 0 then X z else Y z := by
    funext z
    split_ifs <;> tauto
  rwa [heq] at h

lemma depthNextW_length_le (cs tw dW : List Bool) :
    (depthNextW cs tw dW).length ≤ dW.length + 1 := by
  rw [depthNextW]
  split_ifs <;> simp <;> omega

lemma depthNextW_mem_FP {C TW D : List Bool → List Bool}
    (hC : C ∈ FP) (hTW : TW ∈ FP) (hD : D ∈ FP) :
    (fun v => depthNextW (C v) (TW v) (D v)) ∈ FP := by
  have hff : (fun v => fstBlock (C v)) ∈ FP := mem_FP_comp hC fstBlock_mem_FP
  have hsf : (fun v => sndBlock (C v)) ∈ FP := mem_FP_comp hC sndBlock_mem_FP
  have hm : (fun v => csMode (C v)) ∈ FP := mem_FP_comp hff fstBlock_mem_FP
  have hc : (fun v => csCnt (C v)) ∈ FP := mem_FP_comp hff sndBlock_mem_FP
  have hstep : (fun v => csModeStep (C v) (TW v)) ∈ FP := rcModeW_mem_FP hm hc hTW
  have hpred : (fun v => (D v).tail) ∈ FP := tail_mem_FP hD
  have hsucc : (fun v => D v ++ [true]) ∈ FP := appendFn_mem_FP hD (constFn_mem_FP [true])
  exact ifEqLen_mem_FP hm 0
    (ifEqLen_mem_FP hTW 2 hpred (ifEqLen_mem_FP hTW 3 hpred
      (ifEqLen_mem_FP hTW 4 hpred (ifEqLen_mem_FP hTW 8 hpred hD))))
    (ifEqLen_mem_FP hm 2 hsucc (ifEqLen_mem_FP hm 3 hsucc (ifEqLen_mem_FP hm 5 hsucc
      (ifMode479_mem_FP hm hstep hpred hD))))

/-! ### The acceptance client -/

/-- The acceptance client's state: the parser depth, then the conditioning automaton's. -/
def acceptSt (dW cs : List Bool) : List Bool := pair dW cs

def asDepth (st : List Bool) : List Bool := fstBlock st
def asCond (st : List Bool) : List Bool := sndBlock st

@[simp] lemma asDepth_acceptSt (d c : List Bool) : asDepth (acceptSt d c) = d := by
  simp [asDepth, acceptSt]
@[simp] lemma asCond_acceptSt (d c : List Bool) : asCond (acceptSt d c) = c := by
  simp [asCond, acceptSt]

def acceptStepOf (cli tw tok : List Bool) : List Bool :=
  acceptSt (depthNextW (asCond cli) tw (asDepth cli)) (condStepOf (asCond cli) tw tok)

/-- The acceptance pass's word-level step. -/
def acceptStepW (v : List Bool) : List Bool :=
  acceptStepOf (cvCli v) (clampTok v) (cvTok v)

/-- Its block-level reading. -/
def acceptStepR (cli : List Bool) (cur : List ℕ) : List Bool :=
  acceptStepOf cli (List.replicate (min (digitVal cur) 20) true) (digitsToBits cur)

lemma acceptStepW_eq (W cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    acceptStepW (pair W (pair cli (digitsToBits cur))) = acceptStepR cli cur := by
  rw [acceptStepW, acceptStepR, clampTok_pair W cli cur hcur]
  simp only [cvCli, cvTok, sndBlock_pair, fstBlock_pair]

lemma acceptStepW_mem_FP : acceptStepW ∈ FP := by
  have hcond : (fun v => asCond (cvCli v)) ∈ FP :=
    mem_FP_comp cvCli_mem_FP sndBlock_mem_FP
  have hdep : (fun v => asDepth (cvCli v)) ∈ FP :=
    mem_FP_comp cvCli_mem_FP fstBlock_mem_FP
  exact pairFn_mem_FP (depthNextW_mem_FP hcond clampTok_mem_FP hdep)
    (condStepOf_mem_FP hcond clampTok_mem_FP cvTok_mem_FP)

lemma acceptStepW_length_le (W cli tok : List Bool) :
    (acceptStepW (pair W (pair cli tok))).length ≤ cli.length + tok.length + 55 := by
  have hcli : cvCli (pair W (pair cli tok)) = cli := by simp [cvCli]
  have htok : cvTok (pair W (pair cli tok)) = tok := by simp [cvTok]
  have hd := depthNextW_length_le (asCond cli) (clampTok (pair W (pair cli tok)))
    (asDepth cli)
  have hc := condStepOf_length_le (asCond cli) (clampTok (pair W (pair cli tok))) tok
  have H : 2 * (asDepth cli).length + (asCond cli).length ≤ cli.length :=
    two_fstBlock_add_sndBlock_le cli
  rw [acceptStepW, hcli, htok, acceptStepOf, acceptSt, pair_length]
  omega

/-- The automaton state and the parser depth a client state denotes. -/
def asPack (st : List Bool) : ℕ := csPack (asCond st)
def asDepthVal (st : List Bool) : ℕ := (asDepth st).length

lemma acceptStepR_spec (cli : List Bool) (cur : List ℕ) :
    asPack (acceptStepR cli cur) = rpnCondStep (asPack cli) (digitVal cur) ∧
      asDepthVal (acceptStepR cli cur)
        = rpnDepthNext (asPack cli) (rpnCondStep (asPack cli) (digitVal cur))
            (digitVal cur) (asDepthVal cli) := by
  refine ⟨?_, ?_⟩
  · rw [asPack, acceptStepR, acceptStepOf, asCond_acceptSt,
      show condStepOf (asCond cli) (List.replicate (min (digitVal cur) 20) true)
          (digitsToBits cur) = condStepR (asCond cli) cur from rfl,
      csPack_condStepR, asPack]
  · rw [asDepthVal, acceptStepR, acceptStepOf, asDepth_acceptSt, length_depthNextW,
      asPack, asDepthVal]

/-- The finished run's automaton state and depth. -/
lemma acceptFold_spec : ∀ (rs : List (List ℕ)) (cli out : List Bool),
    asPack (runFold acceptStepR (fun _ _ => []) cli out rs).1
        = (rs.map digitVal).foldl rpnCondStep (asPack cli) ∧
      asDepthVal (runFold acceptStepR (fun _ _ => []) cli out rs).1
        = rpnDepthRuns (asPack cli) (rs.map digitVal) (asDepthVal cli)
  | [], cli, out => by rw [runFold, List.map_nil, rpnDepthRuns]; exact ⟨rfl, rfl⟩
  | r :: rs, cli, out => by
      obtain ⟨h1, h2⟩ := acceptStepR_spec cli r
      obtain ⟨i1, i2⟩ := acceptFold_spec rs (acceptStepR cli r) (out ++ [])
      rw [runFold, List.map_cons, List.foldl_cons, rpnDepthRuns]
      exact ⟨by rw [i1, h1], by rw [i2, h1, h2]⟩

/-- The initial acceptance state: base mode, empty counters, zero depth. -/
def acceptInit : List Bool := acceptSt [] condInit

@[simp] lemma asPack_acceptInit : asPack acceptInit = rcPack 0 0 0 := by
  simp [asPack, acceptInit]

@[simp] lemma asDepthVal_acceptInit : asDepthVal acceptInit = 0 := by
  simp [asDepthVal, acceptInit]

/-- The acceptance flag, read off the finished state: one mark iff the automaton returned
to base and the parser depth returned to zero. -/
def acceptsOf (st : List Bool) : List Bool :=
  if (csMode (asCond st)).length = 0 then
    (if (asDepth st).length = 0 then [true] else [])
  else []

lemma length_acceptsOf (st : List Bool) :
    (acceptsOf st).length =
      (if rcMode (asPack st) = 0 then (if asDepthVal st = 0 then 1 else 0) else 0) := by
  have hm : (csMode (asCond st)).length = rcMode (asPack st) := by
    rw [asPack, csPack, rcMode_pack]
  rw [acceptsOf, hm, asDepthVal]
  split_ifs <;> simp

/-- **The acceptance pass**: the structural acceptance test of `rpnAcceptsRuns`, as a word
whose length is the test's value. -/
def acceptsW (Sf : List Bool → List Bool) (z : List Bool) : List Bool :=
  acceptsOf (runFold acceptStepR (fun _ _ => []) acceptInit []
    (blockSplit (bitsToDigits (Sf z))).1).1

lemma length_acceptsW (Sf : List Bool → List Bool) (z : List Bool) :
    (acceptsW Sf z).length = rpnAcceptsRuns (undigitize (bitsToDigits (Sf z))) := by
  obtain ⟨h1, h2⟩ := acceptFold_spec (blockSplit (bitsToDigits (Sf z))).1 acceptInit []
  rw [acceptsW, length_acceptsOf, h1, h2, asPack_acceptInit, asDepthVal_acceptInit,
    rpnAcceptsRuns, ← undigitize_eq_blockSplit]

lemma acceptsW_mem_FP {Wf Sf : List Bool → List Bool} (hWf : Wf ∈ FP) (hSf : Sf ∈ FP) :
    acceptsW Sf ∈ FP := by
  have hfold : (fun z => (runFold acceptStepR (fun _ _ => []) acceptInit []
      (blockSplit (bitsToDigits (Sf z))).1).1) ∈ FP :=
    runFold_cli_mem_FP (STEPr := fun _ => acceptStepR) (EMITr := fun _ _ _ => [])
      (c := 55) (k := 0) (qQ := Polynomial.C 0)
      acceptStepW_mem_FP (constFn_mem_FP []) hWf hSf
      acceptStepW_length_le (fun W cli tok => by simp)
      (fun W cli cur h => acceptStepW_eq W cli cur h) (fun W cli cur _ => rfl)
      acceptInit []
  have hcond : (fun z => asCond ((runFold acceptStepR (fun _ _ => []) acceptInit []
      (blockSplit (bitsToDigits (Sf z))).1).1)) ∈ FP :=
    mem_FP_comp hfold sndBlock_mem_FP
  have hmode : (fun z => csMode (asCond ((runFold acceptStepR (fun _ _ => []) acceptInit []
      (blockSplit (bitsToDigits (Sf z))).1).1))) ∈ FP :=
    mem_FP_comp (mem_FP_comp hcond fstBlock_mem_FP) fstBlock_mem_FP
  have hdep : (fun z => asDepth ((runFold acceptStepR (fun _ _ => []) acceptInit []
      (blockSplit (bitsToDigits (Sf z))).1).1)) ∈ FP :=
    mem_FP_comp hfold fstBlock_mem_FP
  exact ifEqLen_mem_FP hmode 0
    (ifEqLen_mem_FP hdep 0 (constFn_mem_FP [true]) (constFn_mem_FP []))
    (constFn_mem_FP [])

#print axioms LogicalInduction.CondStep.csPack_condStepR
#print axioms LogicalInduction.CondStep.csTokens_condStepR
#print axioms LogicalInduction.CondStep.condPass_mem_FP
#print axioms LogicalInduction.CondStep.decodeBits_condPass_stream
#print axioms LogicalInduction.CondStep.guardMarks_eq_zero_iff
#print axioms LogicalInduction.CondStep.guardedPassW_mem_FP
#print axioms LogicalInduction.CondStep.decodeBits_guardedPassW
#print axioms LogicalInduction.CondStep.countW_length
#print axioms LogicalInduction.CondStep.budgetW_mem_FP
#print axioms LogicalInduction.CondStep.decodeBits_budgetW
#print axioms LogicalInduction.CondStep.decodeBits_invBudgetW
#print axioms LogicalInduction.CondStep.length_acceptsW
#print axioms LogicalInduction.CondStep.acceptsW_mem_FP

end LogicalInduction.CondStep
