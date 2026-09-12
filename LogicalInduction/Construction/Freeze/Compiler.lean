import LogicalInduction.Construction.Freeze.CanonicalCodes
import LogicalInduction.Construction.Conditioning.PricePass
import LogicalInduction.Framework.Emission.FreezeTransducer
import LogicalInduction.Framework.Emission.WriteOut

/-!
# Symbol-level finite-prefix freeze compiler

`app:ifp` — the finite-support freeze as a rewrite of the *flat* RPN symbol stream, which is
the stream a `Complexity.FP` machine actually holds.
`Properties/FinitePerturbations.lean` compiles the administrative prefix freeze
`EF.freezeBefore` into a flat streaming transducer over the *contracted* strategy stream
(`EF.freezeTokenRun`): after a price frame `[0, ⌜φ⌝, day]` with `day < cutoff` it appends the
constant-quote suffix `[1, quote, 8]`.  That obligation is stated on the contracted stream,
which a machine never holds — computing `unRpn` would mean re-encoding each parsed sentence —
so this module carries it across.

## Objects

`runMatches` / `runQuoteFromEntries` / `runPrefixQuoteFromStates` (the run-level tables) and
`freezeEmitOn` / `freezeTokensOn` / `freezeBodyOn` (the transducer).  The transducer is an
instance of the emitter-generic run rewriter in `Construction/Conditioning/PricePass.lean`,
so the commutation `unRpn_rpnConditionRun_of` is reused rather than reproved.

## Where the spelling characterization lives

Deciding "does this run denote `ψ`" is pattern matching against a finite list of spellings
rather than the execution of a parser, and that list is exhaustive with no side condition
because the escape leaf's decode obligation sits inside a hole rather than in a numeral: `⊥`'s
decode fibre is infinite (`decode_falsum_noncanonical`), so a list of constant spellings would
need `BotFree`.  The characterization is stated and proved at *segment* granularity in
`Freeze/StructuredPatterns.lean` (`StructPat.segPatterns`, `StructPat.parseRpn_iff_segMatch`),
which is the granularity the recognizer chain compiles into `Complexity.FP` (`SegAuto` and
`SegCtr`, closed by `SegRec.ifParseFull_mem_FP`).  Taking a whole structured block as one
segment is what lets that form carry no `NoReserved` condition either.

## Main results and their consumers

`unRpn_rpnFreezeRunOn` is the contraction-exactness bridge and
`freezeStreamRewriter_of_flatPass` the reduction of `FreezeStreamRewriter` to a flat pass.
`runMatches` decides the target test by running the full block parser, so a structured
paper-prime leaf is matched exactly like every other sentence block.

Where the two side conditions land: both are discharged in the machine class rather than
assumed — `BotFree` by `DigitFP.sqrtRemW_mem_FP` with `FiberTest.fiberW_mem_FP` on top, and
`NoReserved` by the structured-payload recognizer, whose unary length field is an `aⁿbⁿ`
constraint no `RunAuto.BlockAutomaton` expresses and which `CtrAuto.ctrMachine` supplies.

## The fuel-class obstruction (`dd:fuel`)

`BigDigits` is closed under an operation exactly when that operation's base-4 digit
recurrence has a poly-bounded carry (`addCarry4 ≤ 1`, `mulCarry4 x y p ≤ 3(p+1)`,
`ltFlag4 ≤ 1`, …), because the iterated state of `PolyFueled.prec` must be `IsPolyBounded`;
and `evaln`'s guard bounds every sub-code's input by its fuel, so the fuel calculus admits no
large intermediates anywhere.  Square root's carry is the partial remainder, `Θ(len)` digits
wide, which no `O(log)`-bit state holds.  So the calculus is closed under the forward
big-value operations (`add`, `mul`, `natPair`, `ltNat`, `clampVal`) and open under their
inverses (`sqrt`, `unpair`, division by a large divisor).  The one test that does not factor
through a small clamp is the escape leaf, which must decide `Encodable.decode c = some ψ` for
an exponentially large `c`, and Foundation's `Formula.ofNat` ignores the payload at tag `0`,
so that test reduces to `Nat.unpair`.  Hence nothing here yields `liaEfficientPrefixPatch`.

That obstruction binds exactly when the frozen quote table contains a sentence with a `⊥`
subformula: `decode_eq_some_iff_of_botFree` (`CanonicalCodes.lean`) shows the decode
ambiguity is caused entirely by `⊥`, so on a `⊥`-free target every escape test is a
comparison against a fixed numeral and no square root is needed.  In the *machine* class the
square root is built rather than avoided (`DigitFP.sqrtRemW_mem_FP`, `DigitFP.unpairW_spec`,
with `FiberTest.fiberW_mem_FP` the escape-leaf test on top), which is what the recognizer
consumes.  The token-model side of that disclosure is `Prefix.lean`'s
`liaFreezeBefore_preserves_ecTok`.

This module serves the finite-prefix efficiency closure `app:ifp` / `thm:ifp` and the
algorithm `def:lia`; the provenance lines sit on the declarations below, not on this header.
-/

namespace LogicalInduction

namespace RpnFreeze

open PrefixPatchCompile RpnConditioning

/-- Whether a token run denotes the target: the list-level decision runs the full
block parser, so structured paper-prime leaves are matched exactly like every other
sentence block. -/
def runMatches (target : Sentence) (b : List ℕ) : ℕ :=
  if parseRpn b.length b = some (target, []) then 1 else 0

lemma runMatches_eq_one_iff (target : Sentence) (b : List ℕ) :
    runMatches target b = 1 ↔ parseRpn b.length b = some (target, []) := by
  by_cases h : parseRpn b.length b = some (target, [])
  · simp [runMatches, h]
  · simp [runMatches, h]

/-- On a run the target test agrees with the token-model decoder test at the run's
contracted code. -/
lemma runMatches_of_parse {b : List ℕ} {φ target : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) :
    runMatches target b = sentenceMatches target (Encodable.encode φ) := by
  by_cases hteq : target = φ
  · subst hteq
    rw [(runMatches_eq_one_iff target b).mpr hb,
      (sentenceMatches_eq_one_iff target (Encodable.encode target)).mpr
        (Encodable.encodek target)]
  · have hzero : runMatches target b = 0 := by
      rw [runMatches, if_neg fun hp => hteq (by
        rw [hb] at hp
        exact (congrArg Prod.fst (Option.some.inj hp)).symm)]
    rw [hzero]
    refine ((sentenceMatches_eq_zero_iff target (Encodable.encode φ)).mpr ?_).symm
    rw [Encodable.encodek]
    simpa using fun h => hteq h.symm

/-- Run-level form of `PrefixPatchCompile.encodedQuoteFromEntries`. -/
def runQuoteFromEntries : List (Sentence × ℚ) → List ℕ → ℕ
  | [], _ => Encodable.encode (0 : ℚ)
  | (target, q) :: entries, b =>
      if runMatches target b = 0 then runQuoteFromEntries entries b
      else Encodable.encode q

lemma runQuoteFromEntries_exact (entries : List (Sentence × ℚ))
    {b : List ℕ} {φ : Sentence} (hb : parseRpn b.length b = some (φ, [])) :
    runQuoteFromEntries entries b =
      encodedQuoteFromEntries entries (Encodable.encode φ) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨target, q⟩
      rw [runQuoteFromEntries, encodedQuoteFromEntries, runMatches_of_parse hb]
      split
      · exact ih
      · rfl

/-- Run-level form of `PrefixPatchCompile.encodedPrefixQuoteFromStates`. -/
def runPrefixQuoteFromStates : List RationalBeliefState → ℕ → List ℕ → ℕ
  | [], _, _ => Encodable.encode (0 : ℚ)
  | state :: _, 0, b => runQuoteFromEntries state.entries b
  | _ :: states, day + 1, b => runPrefixQuoteFromStates states day b

/-- The run-level prefix quote table agrees with the token-model one at the run's
contracted code.
Paper node: `def:lia` -/
lemma runPrefixQuoteFromStates_exact (states : List RationalBeliefState) (day : ℕ)
    {b : List ℕ} {φ : Sentence} (hb : parseRpn b.length b = some (φ, [])) :
    runPrefixQuoteFromStates states day b =
      encodedPrefixQuoteFromStates states day (Encodable.encode φ) := by
  induction states generalizing day with
  | nil => rfl
  | cons state states ih =>
      cases day with
      | zero =>
          exact runQuoteFromEntries_exact state.entries hb
      | succ day => exact ih day

/-! ### The symbol-level freeze transducer

The transducer is selector-indexed, matching `EF.freezeTokenRunOn`.  At the flat grammar
the selector and the quote table are read **from the buffered sentence run** — `selRun`,
`quoteRun` — because the run is what the transducer has; `hsel`/`hq` bridge them to the
code-level pair the token model uses, exactly as `runQuoteFromEntries_exact` supplies.
The day-cutoff forms at the end are instances. -/

/-- The token-model freeze, as a whole-stream rewrite. -/
def freezeTokensOn (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (L : List ℕ) :
    List ℕ :=
  (EF.freezeTokenRunOn selCode quoteCode (0, 0) L).2

/-- The body the token-model freeze splices at a completed price leaf. -/
def freezeBodyOn (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (fc d : ℕ) : List ℕ :=
  if selCode d fc then [1, quoteCode d fc, 8] else []

lemma freezeTokensOn_nil (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) :
    freezeTokensOn selCode quoteCode [] = [] := rfl

lemma freezeTokensOn_single (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (t : ℕ)
    (L : List ℕ) (h0 : t ≠ 0) (h1 : t ≠ 1) (h6 : t ≠ 6) (h7 : t ≠ 7) :
    freezeTokensOn selCode quoteCode (t :: L)
      = t :: freezeTokensOn selCode quoteCode L := by
  simp [freezeTokensOn, EF.freezeTokenRunOn, EF.freezeTokenEmitOn, EF.freezeTokenNext,
    h0, h1, h6, h7]

lemma freezeTokensOn_one (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (t : ℕ) :
    freezeTokensOn selCode quoteCode [t] = [t] := by
  simp [freezeTokensOn, EF.freezeTokenRunOn, EF.freezeTokenEmitOn]

lemma freezeTokensOn_payload (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (t c : ℕ)
    (ht : t = 1 ∨ t = 7) (L : List ℕ) :
    freezeTokensOn selCode quoteCode (t :: c :: L)
      = t :: c :: freezeTokensOn selCode quoteCode L := by
  rcases ht with rfl | rfl <;>
    simp [freezeTokensOn, EF.freezeTokenRunOn, EF.freezeTokenEmitOn, EF.freezeTokenNext]

lemma freezeTokensOn_price (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (fc d : ℕ)
    (L : List ℕ) :
    freezeTokensOn selCode quoteCode (0 :: fc :: d :: L) =
      0 :: fc :: d :: (freezeBodyOn selCode quoteCode fc d ++
        freezeTokensOn selCode quoteCode L) := by
  simp only [freezeTokensOn, EF.freezeTokenRunOn, EF.freezeTokenEmitOn,
    EF.freezeTokenNext, freezeBodyOn]
  by_cases hd : selCode d fc = true <;> simp [hd]

lemma freezeTokensOn_pricePair (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (fc : ℕ) : freezeTokensOn selCode quoteCode [0, fc] = [0, fc] := by
  simp [freezeTokensOn, EF.freezeTokenRunOn, EF.freezeTokenEmitOn, EF.freezeTokenNext]

lemma freezeTokensOn_trade (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (fc : ℕ)
    (L : List ℕ) :
    freezeTokensOn selCode quoteCode (6 :: fc :: L)
      = 6 :: fc :: freezeTokensOn selCode quoteCode L := by
  simp [freezeTokensOn, EF.freezeTokenRunOn, EF.freezeTokenEmitOn, EF.freezeTokenNext]

/-- **The symbol-level freeze emitter**: at a selected price-day slot, retain the day and
splice the constant quote of the buffered sentence run under the administrative binding. -/
def freezeEmitOn (selRun : List ℕ → ℕ → Bool) (quoteRun : List ℕ → ℕ → ℕ) :
    List ℕ → ℕ → List ℕ :=
  fun buf D => if selRun buf D then [D, 1, quoteRun buf D, 8] else [D]

/-- **The rewritten price chunk contracts to the token-model freeze.** -/
lemma unRpn_freezeOn_rewrite_chunk (selRun : List ℕ → ℕ → Bool)
    (quoteRun : List ℕ → ℕ → ℕ) (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, selRun b D = selCode D (Encodable.encode φ))
    (hq : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, selRun b D = true → quoteRun b D = quoteCode D (Encodable.encode φ))
    {b : List ℕ} {φ : Sentence} (hb : parseRpn b.length b = some (φ, []))
    (D : ℕ) (rest : List ℕ) :
    unRpn (0 :: b ++ freezeEmitOn selRun quoteRun b D ++ rest) =
      0 :: Encodable.encode φ :: D ::
        (freezeBodyOn selCode quoteCode (Encodable.encode φ) D ++ unRpn rest) := by
  have hs := hsel b φ hb D
  rw [freezeEmitOn, freezeBodyOn, hs]
  by_cases hd : selCode D (Encodable.encode φ) = true
  · have hsel' : selRun b D = true := by rw [hs]; exact hd
    rw [if_pos hd, if_pos hd]
    have hshape : 0 :: b ++ [D, 1, quoteRun b D, 8] ++ rest =
        0 :: (b ++ D :: 1 :: quoteRun b D :: 8 :: rest) := by simp
    rw [hshape, unRpn_price_chunk_block hb,
      unRpn_payload_chunk 1 _ (Or.inl rfl), unRpn_single_chunk 8 (by norm_num),
      hq b φ hb D hsel']
    simp
  · rw [if_neg hd, if_neg hd]
    have hshape : 0 :: b ++ [D] ++ rest = 0 :: (b ++ D :: rest) := by simp
    rw [hshape, unRpn_price_chunk_block hb]
    simp

/-- **Whole-stream contraction exactness for the selector-indexed freeze pass**: on every
input stream — well-formed or garbage — the contraction of the symbol-level freeze
transducer's output is the token-model freeze of the contraction.

This is the bridge the machine-class certificate needs: the transducer runs on the *flat*
stream a machine actually holds, while `EF.freezeTokenRunOn` — and hence
`FreezeStreamRewriter` — is stated on the contracted one.
Paper node: `app:ifp` -/
lemma unRpn_rpnFreezeRunOn (selRun : List ℕ → ℕ → Bool) (quoteRun : List ℕ → ℕ → ℕ)
    (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, selRun b D = selCode D (Encodable.encode φ))
    (hq : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, selRun b D = true → quoteRun b D = quoteCode D (Encodable.encode φ)) :
    ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    unRpn ((rpnConditionRun (freezeEmitOn selRun quoteRun) (rcPack 0 0 0, []) ts).2) =
      freezeTokensOn selCode quoteCode (unRpn ts) :=
  unRpn_rpnConditionRun_of (freezeEmitOn selRun quoteRun)
    (freezeTokensOn selCode quoteCode) (freezeBodyOn selCode quoteCode)
    (freezeTokensOn_nil selCode quoteCode)
    (fun t L h0 h1 h6 h7 => freezeTokensOn_single selCode quoteCode t L h0 h1 h6 h7)
    (freezeTokensOn_one selCode quoteCode)
    (fun t c L ht => freezeTokensOn_payload selCode quoteCode t c ht L)
    (freezeTokensOn_price selCode quoteCode)
    (freezeTokensOn_pricePair selCode quoteCode)
    (freezeTokensOn_trade selCode quoteCode)
    (fun _ _ hb D rest => unRpn_freezeOn_rewrite_chunk selRun quoteRun selCode quoteCode
      hsel hq hb D rest)

/-! ### The day-cutoff instances -/

/-- The token-model prefix freeze, as a whole-stream rewrite. -/
def freezeTokens (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) (L : List ℕ) : List ℕ :=
  freezeTokensOn (fun d _ => decide (d < cutoff)) quoteCode L

/-- **The symbol-level freeze emitter**: at a price-day slot before the cutoff, retain
the day and splice the constant quote of the buffered sentence run under the
administrative binding. -/
def freezeEmit (quoteRun : List ℕ → ℕ → ℕ) (cutoff : ℕ) : List ℕ → ℕ → List ℕ :=
  freezeEmitOn (fun _ D => decide (D < cutoff)) quoteRun

/-- **Whole-stream contraction exactness for the freeze pass**: on every input stream —
well-formed or garbage — the contraction of the symbol-level freeze transducer's output
is the token-model prefix freeze of the contraction.
Paper node: `app:ifp` -/
theorem unRpn_rpnFreezeRun (quoteRun : List ℕ → ℕ → ℕ) (quoteCode : ℕ → ℕ → ℕ)
    (cutoff : ℕ)
    (hq : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, quoteRun b D = quoteCode D (Encodable.encode φ)) :
    ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    unRpn ((rpnConditionRun (freezeEmit quoteRun cutoff) (rcPack 0 0 0, []) ts).2) =
      freezeTokens quoteCode cutoff (unRpn ts) :=
  unRpn_rpnFreezeRunOn _ quoteRun _ quoteCode (fun _ _ _ _ => rfl)
    (fun b' φ' hb' D' _ => hq b' φ' hb' D')

/-! ### The machine-class obligation, on the flat stream

`FreezeStreamRewriter` (`Properties/FinitePerturbations.lean`) is stated on the
*contracted* stream, because that is what `strategyOfTokens` parses.  A machine never holds
the contracted stream — computing `unRpn` would mean re-encoding each parsed sentence — so
the pass it can actually run is the flat-grammar one, and `unRpn_rpnFreezeRunOn` is what
carries it across.  The lemma below is that carry, once. -/

/-- **`FreezeStreamRewriter` reduces to a flat-stream pass.**  A polynomial-time rewrite of
the machine's own output word that computes the *symbol-level* freeze transducer discharges
the contracted-stream obligation, because contraction commutes with the pass.

What remains after this is a single `Complexity.FP` statement about
`rpnConditionRun (freezeEmitOn selRun quoteRun)` — the flat automaton with a freeze
emitter — and its emitter is the run-level table lookup.

Kind `C`; hypotheses `(a)` except `hflat`, which is the residual obligation.
Paper node: `app:ifp` -/
lemma freezeStreamRewriter_of_flatPass (selRun : List ℕ → ℕ → Bool)
    (quoteRun : List ℕ → ℕ → ℕ) (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, selRun b D = selCode D (Encodable.encode φ))
    (hq : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, selRun b D = true → quoteRun b D = quoteCode D (Encodable.encode φ))
    (hflat : ∀ F : List Bool → List Bool, F ∈ Complexity.FP →
      ∃ G : List Bool → List Bool, G ∈ Complexity.FP ∧ ∀ x : List Bool,
        undigitize (bitsToDigits (G x))
          = (rpnConditionRun (freezeEmitOn selRun quoteRun) (rcPack 0 0 0, [])
              (undigitize (bitsToDigits (F x)))).2) :
    FreezeStreamRewriter selCode quoteCode := by
  intro F hF
  obtain ⟨G, hG, hGspec⟩ := hflat F hF
  refine ⟨G, hG, fun x => ?_⟩
  rw [hGspec x]
  exact unRpn_rpnFreezeRunOn selRun quoteRun selCode quoteCode hsel hq _ _ le_rfl

end RpnFreeze
end LogicalInduction
