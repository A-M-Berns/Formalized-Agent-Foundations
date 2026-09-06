import LogicalInduction.Construction.Conditioning.Transduction
import LogicalInduction.Construction.Freeze.Compiler

/-!
# The finite-support freeze as a polynomial-time transduction

`app:ifp` — the freeze pass as a `Complexity.FP` transduction over the flat RPN stream.
`Properties/FinitePerturbations.lean` names the one `Complexity.FP` fact the machine-class
patch requires (`FreezeStreamRewriter`), and `RpnFreeze.freezeStreamRewriter_of_flatPass`
reduces it to a pass over the **flat** stream — the one a machine actually holds, since
contracting would mean re-encoding each parsed sentence.  This file is that pass.

## Objects

`RunOracle` (the run-level lookup interface), `flatEmitW` / `flatEmitR` (the word- and
block-level emitters), and the four lemmas `flatEmitW_mem_FP`, `flatEmitW_length_le`,
`decodeBits_flatEmitR`, `decodeBits_freezePass`.

What the module contributes is exactly one thing: its emitter.  Everything else is reuse —
`Framework/Machine/TokenFold.lean`'s block fold, plus the conditioning track's automaton
wholesale: `CondStep.condStepR` *is* `rpnConditionRun`'s state machine, and
`condStepW_mem_FP`, `condStepW_length_le`, `csPack_condStepR`, `csTokens_condStepR` and
`bufWF_condStepR` are emitter-generic.  Only `CondStep.condPass_mem_FP` bundles a particular
emitter.

## The emitter's lookup

`RunOracle` is the emitter's lookup: given the incoming day's token block and the buffered
sentence run's bits, it returns the bits of `[1, quote, 8]` when the coordinate is selected
and nothing when it is not.  It is inhabited: `Construction/Freeze/Oracle.lean`
builds one for any finite quote table (`runOracleOf`), so `freezeStreamRewriter_of_runOracle`
closes the chain from a finite table to an inhabited `MachineFiniteSupportPatch`.

Deciding whether a buffered run denotes a table sentence is what that construction does, and
`RpnFreeze.parseRpn_iff_mem_spellings` is why it can: under two syntactic side conditions on
the target, the complete spellings of a sentence are a *finite explicit list*, so the
decision is membership in a list of constants rather than the execution of a parser.  The
falsum half of those conditions is `RpnFreeze.matchRun_eq_matchRunCanon`'s ruling, which is
what keeps integer square root out of the lookup.

## The constant output bound is the paper's erratum, not a convenience

`RunOracle.R_length_le` asks the oracle's *output* to be bounded by a constant.
`TokenFold.runFold_mem_FP`'s emission budget is `qQ.eval W.length + k * (cli.length +
tok.length)`: polynomial in the parameter block but only **linear** in the state.  The
oracle is indexed by the buffered sentence code, which lives in the state, so an output that
grew with it would not merely miss the bound once — it would compound.  For a **finite**
quote table the constant bound is free (finitely many entries, hence finitely many quote
codes); for an arbitrary market it is false.  That is `app:ifp`'s own sentence — "only
finitely many constants are needed, and can be hard-coded" — arriving as the side condition
that makes a complexity budget close.

## Why the freeze needs no day clamp, where the conditioning pass does

`CondStep.condEmitR` draws its condition block at `min D n`, because that block's size grows
with the day and a word-level emitter cannot call an oracle at an unbounded day; it discloses
the resulting gap.  The freeze has no such problem: its oracle returns a *bounded* word by
the paragraph above, so it can be handed the day's raw token block instead of a unary day,
and the emission stays polynomial.  `flatEmitR` therefore computes
`RpnFreeze.freezeEmitOn selRun quoteRun` exactly, with no clamp and no gap to close later.

Everything here is construction infrastructure rather than a paper statement, so the
declarations are `lemma`s carrying `app:ifp` as supporting nodes.
-/

namespace LogicalInduction.FreezeStep

open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold
open LogicalInduction.CondStep LogicalInduction.RpnConditioning

private def gvCli (v : List Bool) : List Bool := fstBlock (sndBlock v)
private def gvTok (v : List Bool) : List Bool := sndBlock (sndBlock v)

/-! ## The lookup oracle -/

/-- **The run-level lookup**, as an interface.

Given the incoming day's token block and the buffered sentence run's bits, `R` returns the
bits of `[1, quote, 8]` when the price coordinate is selected and nothing when it is not.
`R_length_le` is the finite-table condition in complexity clothing; see this file's header
for why it is load-bearing rather than convenient.

Inhabited by `FreezeOracle.runOracleOf`, which builds one for any finite quote table. -/
structure RunOracle (selRun : List ℕ → ℕ → Bool) (quoteRun : List ℕ → ℕ → ℕ) where
  /-- The oracle. -/
  R : List Bool → List Bool
  /-- It is polynomial time. -/
  R_FP : R ∈ FP
  /-- Its output is a whole number of complete blocks, so splices decode piecewise. -/
  R_wf : ∀ tokW bufW : List Bool, BlockWF (R (pair tokW bufW))
  /-- The constant output budget: the quote table is finite. -/
  R_len : ℕ
  /-- The constant bound itself. -/
  R_length_le : ∀ v : List Bool, (R v).length ≤ R_len
  /-- And it emits the freeze suffix, on every **well-formed** day block.

  The restriction to `digitsToBits cur` with `cur` a run of digits below four is not a
  convenience: a token's value is recoverable from its block, but *not* from an arbitrary
  word — `bitsToDigits` of a malformed word can carry a terminator digit, and no
  fixed-numeral test agrees with `digitVal` there.  It is also exactly how `flatEmitR`
  calls the oracle, since `runFold` only ever hands it a block. -/
  R_spec : ∀ (cur : List ℕ), (∀ d ∈ cur, d < 4) → ∀ bufW : List Bool,
    decodeBits (R (pair (digitsToBits cur) bufW))
      = if selRun (decodeBits bufW) (digitVal cur) then
          [1, quoteRun (decodeBits bufW) (digitVal cur), 8] else []

/-! ## The emitter -/

/-- The freeze pass's word-level emitter: copy the token through, and at a price-day slot
append the oracle's suffix. -/
def flatEmitW (R : List Bool → List Bool) (v : List Bool) : List Bool :=
  if (csMode (gvCli v)).length = 2 then
    dayBits (gvTok v) ++ R (pair (gvTok v) (csBuf (gvCli v)))
  else dayBits (gvTok v)

/-- Its block-level reading, which is what `TokenFold.runFold` folds. -/
def flatEmitR (R : List Bool → List Bool) (cli : List Bool) (cur : List ℕ) : List Bool :=
  if (csMode cli).length = 2 then
    dayBits (digitsToBits cur) ++ R (pair (digitsToBits cur) (csBuf cli))
  else dayBits (digitsToBits cur)

/-- The word emitter reads a well-formed block exactly as `flatEmitR` does — by definition,
so `runFold_mem_FP`'s hypothesis carries no side condition on the client.  Note it does not
depend on the parameter block at all: the freeze needs no day clamp. -/
lemma flatEmitW_eq (R : List Bool → List Bool) (W cli : List Bool) (cur : List ℕ) :
    flatEmitW R (pair W (pair cli (digitsToBits cur))) = flatEmitR R cli cur := by
  rw [flatEmitW, flatEmitR]
  simp only [gvCli, gvTok, sndBlock_pair, fstBlock_pair]

/-! ## What the emitter emits -/

/-- The emitter's output is a whole number of complete blocks, so the fold's accumulated word
stays decodable. -/
lemma blockWF_flatEmitR {selRun : List ℕ → ℕ → Bool} {quoteRun : List ℕ → ℕ → ℕ}
    (E : RunOracle selRun quoteRun) (cli : List Bool) (cur : List ℕ)
    (hcur : ∀ d ∈ cur, d < 4) : BlockWF (flatEmitR E.R cli cur) := by
  have hday : BlockWF (dayBits (digitsToBits cur)) := blockWF_run cur hcur
  rw [flatEmitR]
  split_ifs
  · exact hday.append (E.R_wf _ _)
  · exact hday

/-- **The emitter computes the symbol-level freeze emission**, unclamped.

Proof kind: `C` composition.  Provenance: (a) `TokenFold.decodeBits_run`,
`TokenFold.decodeBits_append`, `RunOracle.R_spec`.
Paper node: `app:ifp` -/
lemma decodeBits_flatEmitR {selRun : List ℕ → ℕ → Bool} {quoteRun : List ℕ → ℕ → ℕ}
    (E : RunOracle selRun quoteRun) (cli : List Bool) (cur : List ℕ)
    (hcur : ∀ d ∈ cur, d < 4) :
    decodeBits (flatEmitR E.R cli cur)
      = if rcMode (csPack cli) = 2 then
          RpnFreeze.freezeEmitOn selRun quoteRun (csTokens cli) (digitVal cur)
        else [digitVal cur] := by
  have hday : BlockWF (dayBits (digitsToBits cur)) := blockWF_run cur hcur
  have hdayd : decodeBits (dayBits (digitsToBits cur)) = [digitVal cur] :=
    decodeBits_run cur hcur
  have hmode : rcMode (csPack cli) = (csMode cli).length := by
    rw [csPack, rcMode_pack]
  rw [flatEmitR, hmode]
  split_ifs
  · rw [decodeBits_append hday (E.R_wf _ _), hdayd, E.R_spec cur hcur,
      RpnFreeze.freezeEmitOn, csTokens]
    split_ifs <;> simp
  · exact hdayd

/-! ## Membership and the emission bound -/

/-- The word-level emitter is polynomial time, from the oracle's own `FP` membership and
`TokenFold`'s block projections. -/
lemma flatEmitW_mem_FP {selRun : List ℕ → ℕ → Bool} {quoteRun : List ℕ → ℕ → ℕ}
    (E : RunOracle selRun quoteRun) : flatEmitW E.R ∈ FP := by
  have hcli : gvCli ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have htok : gvTok ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
  have hff : (fun v => fstBlock (gvCli v)) ∈ FP := mem_FP_comp hcli fstBlock_mem_FP
  have hsf : (fun v => sndBlock (gvCli v)) ∈ FP := mem_FP_comp hcli sndBlock_mem_FP
  have hm : (fun v => csMode (gvCli v)) ∈ FP := mem_FP_comp hff fstBlock_mem_FP
  have hbuf : (fun v => csBuf (gvCli v)) ∈ FP := mem_FP_comp hsf sndBlock_mem_FP
  have hr : (fun v => E.R (pair (gvTok v) (csBuf (gvCli v)))) ∈ FP :=
    mem_FP_comp (pairFn_mem_FP htok hbuf) E.R_FP
  have hday : (fun v => dayBits (gvTok v)) ∈ FP :=
    appendFn_mem_FP htok (constFn_mem_FP (digitBits 4))
  have h := selectHeadFn_eqLen_mem_FP hm (constFn_mem_FP (uw 2))
    (appendFn_mem_FP hday hr) hday
  simp only [length_uw] at h
  exact h

/-- The emission bound is polynomial in the parameter block and **linear** in the state —
which is all `runFold_mem_FP` allows, and is exactly what `R_length_le` buys. -/
lemma flatEmitW_length_le {selRun : List ℕ → ℕ → Bool} {quoteRun : List ℕ → ℕ → ℕ}
    (E : RunOracle selRun quoteRun) (W cli tok : List Bool) :
    (flatEmitW E.R (pair W (pair cli tok))).length
      ≤ (Polynomial.C (E.R_len + 3)).eval W.length + 1 * (cli.length + tok.length) := by
  have hcli : gvCli (pair W (pair cli tok)) = cli := by simp [gvCli]
  have htok : gvTok (pair W (pair cli tok)) = tok := by simp [gvTok]
  have hr := E.R_length_le (pair tok (csBuf cli))
  simp only [Polynomial.eval_C]
  rw [flatEmitW, hcli, htok]
  split_ifs
  · rw [dayBits]
    simp only [List.length_append, length_digitBits]
    omega
  · rw [dayBits]
    simp only [List.length_append, length_digitBits]
    omega

/-! ## The freeze pass, decoded -/

/-- Folding the emitter over a well-formed block sequence decodes to `rpnConditionRun` applied
to the same tokens — the induction `decodeBits_freezePass` runs on. -/
lemma decodeBits_runFold_freeze {selRun : List ℕ → ℕ → Bool} {quoteRun : List ℕ → ℕ → ℕ}
    (E : RunOracle selRun quoteRun) :
    ∀ (rs : List (List ℕ)) (cli out : List Bool),
      (∀ r ∈ rs, ∀ d ∈ r, d < 4) → BlockWF (csBuf cli) → BlockWF out →
      decodeBits (runFold condStepR (flatEmitR E.R) cli out rs).2
        = decodeBits out
          ++ (rpnConditionRun (RpnFreeze.freezeEmitOn selRun quoteRun)
                (csPack cli, csTokens cli) (rs.map digitVal)).2
  | [], cli, out, _, _, _ => by
      rw [runFold, List.map_nil, rpnConditionRun_nil]
      simp
  | r :: rs, cli, out, hrs, hbuf, hout => by
      have hr : ∀ d ∈ r, d < 4 := hrs r (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rs, ∀ d ∈ q, d < 4 :=
        fun q hq => hrs q (List.mem_cons_of_mem _ hq)
      have hbuf' : BlockWF (csBuf (condStepR cli r)) := bufWF_condStepR cli r hr hbuf
      have hemit : BlockWF (flatEmitR E.R cli r) := blockWF_flatEmitR E cli r hr
      rw [runFold, decodeBits_runFold_freeze E rs _ _ hrest hbuf' (hout.append hemit),
        decodeBits_append hout hemit, csPack_condStepR, csTokens_condStepR cli r hr hbuf,
        decodeBits_flatEmitR E cli r hr, List.map_cons]
      rw [show (csPack cli, csTokens cli) = ((csPack cli, csTokens cli).1,
            (csPack cli, csTokens cli).2) from rfl, rpnConditionRun]
      simp only [List.append_assoc]

/-- **The freeze pass is polynomial time.**  `Sf` is the trader's serialized stream and `E`
the run-level lookup.  There is no parameter block: unlike the conditioning pass, the freeze
emitter needs nothing but the token and the state.

Kind `C`; hypotheses `(a)`.
Paper node: `app:ifp` -/
lemma freezePass_mem_FP {selRun : List ℕ → ℕ → Bool} {quoteRun : List ℕ → ℕ → ℕ}
    (E : RunOracle selRun quoteRun) {Sf : List Bool → List Bool} (hSf : Sf ∈ FP) :
    (fun z => (runFold condStepR (flatEmitR E.R) condInit []
        (blockSplit (bitsToDigits (Sf z))).1).2) ∈ FP :=
  runFold_mem_FP (STEPr := fun _ => condStepR) (EMITr := fun _ => flatEmitR E.R)
    (c := 51) (k := 1) (qQ := Polynomial.C (E.R_len + 3))
    condStepW_mem_FP (flatEmitW_mem_FP E) (constFn_mem_FP []) hSf
    condStepW_length_le (flatEmitW_length_le E)
    (fun W cli cur h => condStepW_eq W cli cur h)
    (fun W cli cur _ => flatEmitW_eq E.R W cli cur) condInit []

/-- **And it computes the symbol-level freeze**, on every stream, well-formed or garbage —
with no clamp, so this is `rpnConditionRun (freezeEmitOn selRun quoteRun)` itself rather than
a clamped stand-in.

Kind `C`; hypotheses `(a)` except `E`.
Paper node: `app:ifp` -/
lemma decodeBits_freezePass {selRun : List ℕ → ℕ → Bool} {quoteRun : List ℕ → ℕ → ℕ}
    (E : RunOracle selRun quoteRun) (ds : List ℕ) :
    decodeBits (runFold condStepR (flatEmitR E.R) condInit [] (blockSplit ds).1).2
      = (rpnConditionRun (RpnFreeze.freezeEmitOn selRun quoteRun) (rcPack 0 0 0, [])
          (undigitize ds)).2 := by
  have h := decodeBits_runFold_freeze E (blockSplit ds).1 condInit []
    (fun r hr => (blockSplit_digits_lt ds).1 r hr) (by simpa using BlockWF.nil) BlockWF.nil
  rw [csPack_condInit, csTokens_condInit] at h
  simpa [← undigitize_eq_blockSplit] using h

/-! ## The end-to-end reduction -/

/-- **`FreezeStreamRewriter` follows from the run-level lookup, and from nothing else.**

Every link between the lookup and `MachineFiniteSupportPatch` is proved: this lemma to
`FreezeStreamRewriter`, `RpnFreeze.freezeStreamRewriter_of_flatPass` and
`RpnFreeze.unRpn_rpnFreezeRunOn` across the contraction,
`MachineEfficientTrader.freezeOn` to `preserves_ec`, and
`machineFiniteSupportPatch_of_rewriter` to the patch.  `FreezeOracle.runOracleOf` closes it
at this end, so the chain runs from a finite table to an inhabited patch.

The fuel-class certificates `FiniteSupportPatch` and `EfficientPrefixPatch` are a separate
matter and remain uninhabited (`dd:fuel`); nothing here bears on them.

Kind `C`; hypotheses `(a)` except `E`.
Paper node: `app:ifp` -/
lemma freezeStreamRewriter_of_runOracle {selRun : List ℕ → ℕ → Bool}
    {quoteRun : List ℕ → ℕ → ℕ} (E : RunOracle selRun quoteRun)
    (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, selRun b D = selCode D (Encodable.encode φ))
    (hq : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, selRun b D = true → quoteRun b D = quoteCode D (Encodable.encode φ)) :
    FreezeStreamRewriter selCode quoteCode := by
  refine RpnFreeze.freezeStreamRewriter_of_flatPass selRun quoteRun selCode quoteCode
    hsel hq ?_
  intro F hF
  exact ⟨_, freezePass_mem_FP E hF, fun x => decodeBits_freezePass E _⟩

end LogicalInduction.FreezeStep
