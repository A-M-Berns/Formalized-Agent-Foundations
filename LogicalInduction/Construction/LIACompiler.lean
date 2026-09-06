import LogicalInduction.Construction.LIAComputation
import LogicalInduction.Construction.Primcodable

/-!
# Concrete compiler for the bounded LIA evaluator

§5 defines `MarketMaker`, `Budgeter`, `TradingFirm` and the recursively specified market
`LIA` (`def:lia`) by ordinary mathematics and then asserts that each is computable.  This
file discharges those assertions and states §5's conclusions, `thm:lia` and `thm:li`, the
latter in the paper's `def:belstate` / `def:belseq` form.  The codes and parser certificates
it runs on are not built here: `Construction/Primcodable.lean` is that layer, and this file
is the §5 compiler alone.

## The three components as first-order data

MarketMaker's bounded least-candidate search over proof-erased belief states, the Budgeter's
atom-table world enumeration and scale factor, and the TradingFirm's cutoff through
`EF.absBound`.  The bounded evaluators `liaPrefixAtFuel`, `liaEncodedQuoteNatAtFuel` and
`liaEncodedEntriesAtFuel` assemble them into `liaBoundedEvaluatorCompiler`, the
`LIABoundedEvaluatorCompiler` value the existence theorems consume.

Two encodings the §5 objects need of their own are built here rather than upstream, because
their types are declared in this directory: `Primcodable RationalBeliefState` (the market
maker's proof-erased finite state, revalidated by the decoder so the runtime state stays
first-order) and the exact accessors on it, and the fuel-clocked stage table
`processStageAtFuel_prim` / `quoteAtFuel_prim` the bounded evaluator reads.

## The rational `EF` stack machine

`efRatCompiledEval`, its correctness `efRatCompiledEval_eq` and its certificate
`efRatCompiledEval_prim` — the evaluator that
`Construction/Statistics/SettlementCompiler.lean` runs against the total quote table.

## Main results

`LIA_isMachineLogicalInductor` and `LIA_is_logical_inductor` render `thm:lia`;
`exists_machine_logical_inductor`, `exists_logical_inductor` and
`exists_computable_beliefSequence_logical_inductor` render `thm:li`.  They are inventoried
in `AxiomAudit.lean` and consumed by the `_unconditional` and `_closed` endpoints in
the §4 lanes, chiefly `Construction/Paper/Market.lean`,
`Construction/NonDogmatism/Endpoints.lean` and
`Construction/Conditioning/Endpoints.lean`.
Nothing under `Properties/` imports `Construction/`; the `_closed` lemmas that do live there
(`sumEF_closed`, `PolySequence.gradualRisk_closed`, `dusSignal_closed`) are feature-closure
lemmas, an unrelated sense of the suffix.

`Nat.sqrt` is made locally irreducible around the `Primrec` proofs over the deeply nested
`Primcodable` product types, for the reason given in `Construction/Primcodable.lean`'s
header; the individual sites cite it.

The final section is the public interface a downstream market construction re-uses; anything
not named there is implementation detail of this compiler.
-/

namespace LogicalInduction

open LO.Propositional

/-! ## Proof-erased finite rational belief states -/

private lemma beliefEntryListKeys_prim :
    Primrec fun entries : List (Sentence × ℚ) => entries.map Prod.fst := by
  exact Primrec.list_map Primrec.id
    (Primrec.fst.comp₂ Primrec₂.right)

private lemma beliefEntryBounded_prim :
    PrimrecPred fun p : Sentence × ℚ => 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  have hlo : PrimrecPred fun p : Sentence × ℚ => 0 ≤ p.2 :=
    ratLE_prim.comp (Primrec.const 0) Primrec.snd
  have hhi : PrimrecPred fun p : Sentence × ℚ => p.2 ≤ 1 :=
    ratLE_prim.comp Primrec.snd (Primrec.const 1)
  exact hlo.and hhi

private lemma beliefEntriesBounded_prim :
    PrimrecPred fun entries : List (Sentence × ℚ) =>
      ∀ p ∈ entries, 0 ≤ p.2 ∧ p.2 ≤ 1 :=
  beliefEntryBounded_prim.forall_mem_list

private lemma beliefEntriesValid_prim :
    PrimrecPred fun entries : List (Sentence × ℚ) =>
      (entries.map Prod.fst).Nodup ∧
        ∀ p ∈ entries, 0 ≤ p.2 ∧ p.2 ≤ 1 :=
  (sentenceListNodup_prim.comp beliefEntryListKeys_prim).and beliefEntriesBounded_prim

private def beliefEntriesNorm (entries : List (Sentence × ℚ)) : ℕ :=
  if (entries.map Prod.fst).Nodup ∧
      (∀ p ∈ entries, 0 ≤ p.2 ∧ p.2 ≤ 1) then
    Encodable.encode entries + 1
  else 0

private lemma beliefEntriesNorm_prim : Primrec beliefEntriesNorm := by
  exact (Primrec.ite beliefEntriesValid_prim
    (Primrec.nat_add.comp Primrec.encode (Primrec.const 1))
    (Primrec.const 0)).of_eq fun entries => by simp only [beliefEntriesNorm]

/-- The encoding of a rational belief state erases its proof fields and stores exactly its
validated finite association list. -/
instance rationalBeliefStateEncodable : Encodable RationalBeliefState :=
  Encodable.ofLeftInjection RationalBeliefState.entries
    RationalBeliefState.ofEntries? RationalBeliefState.ofEntries?_self

private lemma beliefEntriesNorm_eq (entries : List (Sentence × ℚ)) :
    beliefEntriesNorm entries =
      Encodable.encode (RationalBeliefState.ofEntries? entries) := by
  by_cases hn : (entries.map Prod.fst).Nodup
  · by_cases hb : ∀ p ∈ entries, 0 ≤ p.2 ∧ p.2 ≤ 1
    · let B : RationalBeliefState := ⟨entries, hn, hb⟩
      have hof : RationalBeliefState.ofEntries? entries = some B := by
        simpa [B] using RationalBeliefState.ofEntries?_self B
      rw [beliefEntriesNorm, if_pos ⟨hn, hb⟩, hof]
      rfl
    · have hof : RationalBeliefState.ofEntries? entries = none := by
        rw [RationalBeliefState.ofEntries?, dif_pos hn, dif_neg hb]
      rw [beliefEntriesNorm, if_neg (by tauto), hof]
      rfl
  · have hof : RationalBeliefState.ofEntries? entries = none := by
      simp [RationalBeliefState.ofEntries?, hn]
    rw [beliefEntriesNorm, if_neg (by tauto), hof]
    rfl

/-- Normalize a raw natural-number candidate to the exact code of the validated belief
state decoded by `rationalBeliefStateEncodable`. -/
private def beliefStateDecodeNorm (n : ℕ) : ℕ :=
  match Encodable.decode (α := List (Sentence × ℚ)) n with
  | none => 0
  | some entries => beliefEntriesNorm entries

private lemma beliefStateDecodeNorm_prim : Primrec beliefStateDecodeNorm := by
  exact (Primrec.option_casesOn
    (Primrec.decode : Primrec fun n : ℕ =>
      Encodable.decode (α := List (Sentence × ℚ)) n)
    (Primrec.const 0)
    (beliefEntriesNorm_prim.comp₂ Primrec₂.right)).of_eq fun n => by
      cases h : Encodable.decode (α := List (Sentence × ℚ)) n <;>
        simp [beliefStateDecodeNorm, h]

private lemma beliefStateDecodeNorm_eq (n : ℕ) :
    beliefStateDecodeNorm n =
      Encodable.encode
        (@Encodable.decode RationalBeliefState rationalBeliefStateEncodable n) := by
  change beliefStateDecodeNorm n = Encodable.encode
    ((Encodable.decode (α := List (Sentence × ℚ)) n).bind
      RationalBeliefState.ofEntries?)
  cases h : Encodable.decode (α := List (Sentence × ℚ)) n with
  | none => simp [beliefStateDecodeNorm, h]
  | some entries => simp [beliefStateDecodeNorm, h, beliefEntriesNorm_eq]

/-- The validated finite-state representation used by MarketMaker is primitive-recursive;
its proof fields carry no runtime information. -/
instance rationalBeliefStatePrimcodable : Primcodable RationalBeliefState where
  prim := Primrec.nat_iff.mp
    (beliefStateDecodeNorm_prim.of_eq beliefStateDecodeNorm_eq)

/-! ## Exact finite-state accessors -/

/-- Association-list quotation is primitive recursive.  `List.lookup` has exactly the
first-key-wins behavior used by `quoteFromEntries`. -/
private lemma quoteFromEntries_prim : Primrec₂ quoteFromEntries := by
  have hlookup : Primrec₂ fun entries : List (Sentence × ℚ) => fun φ =>
      entries.lookup φ := Primrec₂.swap Primrec.listLookup
  exact (Primrec.option_getD.comp₂ hlookup (Primrec₂.const 0)).of_eq fun entries φ => by
    induction entries with
    | nil => rfl
    | cons entry entries ih =>
        rcases entry with ⟨ψ, q⟩
        simp only [quoteFromEntries, List.lookup]
        split <;> simp_all

/-- Quoting a proof-erased rational belief state is primitive recursive. -/
private lemma rationalBeliefStateEntries_prim :
    Primrec RationalBeliefState.entries := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode : Primrec fun B : RationalBeliefState =>
    Encodable.encode B).of_eq fun B => by rfl

private lemma rationalBeliefStateQuote_prim :
    Primrec₂ RationalBeliefState.quote := by
  exact (quoteFromEntries_prim.comp₂
    (rationalBeliefStateEntries_prim.comp₂ Primrec₂.left)
    Primrec₂.right).of_eq fun B φ => by
    rfl

/-- The finite chronological rational history is primitive recursive in the state list,
day, and queried sentence. -/
private lemma rationalHistory_prim :
    Primrec fun p : (List RationalBeliefState × ℕ) × Sentence =>
      rationalHistory p.1.1 p.1.2 p.2 := by
  let stateAt : (List RationalBeliefState × ℕ) × Sentence →
      Option RationalBeliefState := fun p => p.1.1[p.1.2]?
  have hstateAt : Primrec stateAt :=
    Primrec.list_getElem?.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)
  have hquote : Primrec₂ fun
      (p : (List RationalBeliefState × ℕ) × Sentence)
      (B : RationalBeliefState) => B.quote p.2 :=
    rationalBeliefStateQuote_prim.comp₂ Primrec₂.right
      (Primrec.snd.comp₂ Primrec₂.left)
  exact (Primrec.option_casesOn hstateAt (Primrec.const 0)
    hquote).of_eq fun p => by
        rcases p with ⟨⟨past, day⟩, φ⟩
        cases h : past[day]? <;> simp [stateAt, rationalHistory, h]

/-- The candidate enumeration searched by MarketMaker is precisely the decoder of the
proof-erased belief-state representation, hence primitive recursive. -/
private lemma marketMakerCandidate_prim : Primrec marketMakerCandidate := by
  exact (Primrec.decode : Primrec fun k : ℕ =>
    Encodable.decode (α := RationalBeliefState) k).of_eq fun k => by rfl

/-- A fixed deductive-process program, run for a supplied clock, is primitive recursive in
the clock and requested day, including exact decoding of its finite sentence set. -/
lemma processStageAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Primrec₂ fun fuel n => process.stageAtFuel fuel n := by
  have heval : Primrec fun p : ℕ × ℕ =>
      Nat.Partrec.Code.evaln p.1 process.code p.2 :=
    Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.fst.pair (Primrec.const process.code)).pair Primrec.snd)
  have hdecode : Primrec fun out : ℕ =>
      Encodable.decode (α := Finset Sentence) out := Primrec.decode
  exact (Primrec.option_bind heval
    ((hdecode.comp Primrec.snd).to₂)).to₂.of_eq fun fuel n => by
      rfl

/-- A fixed market program, run for a supplied clock, is primitive recursive in the clock,
day and sentence, including exact decoding of its rational output. -/
lemma quoteAtFuel_prim {P : History} (market : MarketComputation P) :
    Primrec fun p : ℕ × ℕ × Sentence => market.quoteAtFuel p.1 p.2.1 p.2.2 := by
  have hz : Primrec fun p : ℕ × ℕ × Sentence =>
      Nat.pair p.2.1 (Encodable.encode p.2.2) :=
    Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))
  have heval : Primrec fun p : ℕ × ℕ × Sentence =>
      Nat.Partrec.Code.evaln p.1 market.code
        (Nat.pair p.2.1 (Encodable.encode p.2.2)) :=
    Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.fst.pair (Primrec.const market.code)).pair hz)
  have hdecode : Primrec fun out : ℕ =>
      Encodable.decode (α := ℚ) out := Primrec.decode
  exact (Primrec.option_bind heval
    ((hdecode.comp Primrec.snd).to₂)).of_eq fun p => rfl

/-- Decoding the entire finite deductive-stage prefix under one common clock is primitive
recursive. -/
private lemma processStagePrefixAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Primrec₂ fun fuel n => processStagePrefixAtFuel process fuel n := by
  have hbase : Primrec fun _fuel : ℕ =>
      (some [] : Option (List (Finset Sentence))) := Primrec.const (some [])
  have hstep : Primrec₂ fun fuel
      (ni : ℕ × Option (List (Finset Sentence))) =>
      ni.2.bind fun accumulated =>
        (process.stageAtFuel fuel ni.1).bind fun stage =>
          some (accumulated ++ [stage]) := by
    let X := ℕ × (ℕ × Option (List (Finset Sentence)))
    have hstage : Primrec fun x : X =>
        process.stageAtFuel x.1 x.2.1 :=
      processStageAtFuel_prim process |>.comp Primrec.fst
        (Primrec.fst.comp Primrec.snd)
    have hout : Primrec₂ fun
        (y : X × List (Finset Sentence)) (stage : Finset Sentence) =>
        some (y.2 ++ [stage]) :=
      Primrec₂.option_some_iff.mpr
        (Primrec.list_concat.comp₂
          (Primrec.snd.comp₂ Primrec₂.left)
          Primrec₂.right)
    have hinner : Primrec₂ fun (x : X)
        (accumulated : List (Finset Sentence)) =>
        (process.stageAtFuel x.1 x.2.1).bind fun stage =>
          some (accumulated ++ [stage]) := by
      exact (Primrec.option_bind
        (hstage.comp Primrec.fst) hout).to₂
    exact (Primrec.option_bind
      (Primrec.snd.comp Primrec.snd) hinner).to₂
  exact (Primrec.nat_rec hbase hstep).of_eq fun fuel n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [processStagePrefixAtFuel, ih]

/-- Lookup in a successfully decoded stage prefix, with the empty theory as the
out-of-range default, is primitive recursive. -/
private lemma decodedStageTable_prim : Primrec₂ decodedStageTable := by
  exact (Primrec.list_getD (∅ : Finset Sentence)).of_eq fun stages n => by
    rfl


/-- The canonical enumeration's day strategies are primitive recursive.

The token producer is `MachineExec.machineTokens` — the budgeted execution of the finite
description an index names — so the effective construction runs the same machine the
enumeration's soundness proof reasons about, not a second simulator. -/
private lemma enumeratedTraderTrades_prim : Primrec₂ fun j n =>
    ((enumeratedTrader j).strat n).trades := by
  let P := ℕ × ℕ
  have hn : Primrec fun p : P => p.2 := Primrec.snd
  have htoks : Primrec fun p : P => MachineExec.machineTokens p.1 p.2 :=
    MachineExec.primrec_machineTokens
  exact ((strategyOfTokensTrades_prim.comp hn
    (unRpn_prim.comp (undigitize_prim.comp htoks))).to₂).of_eq fun j n => rfl

private lemma firmRawTraderTrades_prim : Primrec₂ fun j n =>
    ((firmRawTrader j).strat n).trades := by
  have hbefore : PrimrecRel fun j n => n < j :=
    PrimrecRel.comp₂ Primrec.nat_lt Primrec₂.right Primrec₂.left
  exact (Primrec.ite hbefore (Primrec.const [])
    enumeratedTraderTrades_prim).of_eq fun p => by
      rcases p with ⟨j, n⟩
      unfold firmRawTrader Trader.gate
      by_cases h : n < j
      · have hle : ¬j ≤ n := by omega
        simp [h, hle, Trader.zero]
      · have hle : j ≤ n := by omega
        simp [h, hle]

/-! ## First-order finite-operation compiler -/

private lemma allBoolLists_prim : Primrec allBoolLists := by
  have hprepend (b : Bool) : Primrec fun xs : List (List Bool) =>
      xs.map (List.cons b) :=
    Primrec.list_map Primrec.id
      (Primrec.list_cons.comp₂ (Primrec₂.const b) Primrec₂.right)
  have hstep : Primrec₂ fun (_ : Unit)
      (ni : ℕ × List (List Bool)) =>
      ni.2.map (false :: ·) ++ ni.2.map (true :: ·) :=
    Primrec.list_append.comp₂
      ((hprepend false).comp₂ (Primrec.snd.comp₂ Primrec₂.right))
      ((hprepend true).comp₂ (Primrec.snd.comp₂ Primrec₂.right))
  have hrec : Primrec₂ fun (_ : Unit) n => allBoolLists n :=
    (Primrec.nat_rec (Primrec.const [[]]) hstep).of_eq fun _ n => by
      induction n with
      | zero => rfl
      | succ n ih => simp [allBoolLists, ih]
  exact hrec.comp (Primrec.const ()) Primrec.id

private lemma efNeg_prim : Primrec EF.neg := by
  exact (efMul_prim.comp
    (efConst_prim.comp (Primrec.const (-1 : ℚ))) Primrec.id).of_eq fun e => by
      rfl

private lemma efMin_prim : Primrec₂ EF.min := by
  have hinner : Primrec₂ fun a b : EF => EF.max (EF.neg a) (EF.neg b) :=
    efMax_prim.comp (efNeg_prim.comp Primrec.fst) (efNeg_prim.comp Primrec.snd)
  exact (efNeg_prim.comp hinner).to₂.of_eq fun a b => by rfl

private lemma efListMin_prim : Primrec EF.listMin := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const (EF.const 1))
    (efMin_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right))).of_eq fun es => by
        rfl

private lemma sumFeatures_prim : Primrec ROIBudget.sumFeatures := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const (EF.const 0))
    (efAdd_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right))).of_eq fun es => by
        rfl

private lemma scaleConstTradeList_prim : Primrec₂ scaleConstTradeList := by
  let P := ℚ × List (EF × Sentence)
  have htrade : Primrec₂ fun (p : P) (trade : EF × Sentence) =>
      (EF.mul (EF.const p.1) trade.1, trade.2) :=
    (efMul_prim.comp
      (efConst_prim.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd) |>.to₂
  exact (Primrec.list_map Primrec.snd htrade).to₂.of_eq fun q trades => by
    rfl

private lemma tradingFirmWeight_prim : Primrec₂ tradingFirmWeight := by
  let P := ℕ × ℕ
  have hexponent : Primrec fun p : P => p.1 + 1 + p.2 :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp Primrec.fst (Primrec.const 1)) Primrec.snd
  have hpow : Primrec fun p : P => (2 : ℚ) ^ (p.1 + 1 + p.2) :=
    ratPow_prim.comp (Primrec.const 2) hexponent
  exact (ratDiv_prim.comp (Primrec.const 1) hpow).to₂.of_eq fun j b => by
    rfl

private lemma tradeListSupportSentenceList_prim :
    Primrec fun trades : List (EF × Sentence) =>
      supportSentenceList (tradeListSupport trades) := by
  let r : Sentence → Sentence → Prop := fun φ ψ =>
    Encodable.encode φ ≤ Encodable.encode ψ
  have hsentences : Primrec fun trades : List (EF × Sentence) =>
      trades.map Prod.snd :=
    Primrec.list_map Primrec.id (Primrec.snd.comp₂ Primrec₂.right)
  have hcanonical : Primrec fun trades : List (EF × Sentence) =>
      (sentenceDedup (trades.map Prod.snd)).insertionSort r :=
    sentenceInsertionSort_prim.comp (sentenceDedup_prim.comp hsentences)
  exact hcanonical.of_eq fun trades => by
    letI : IsTrans Sentence r :=
      ⟨fun _ _ _ hab hbc => hab.trans hbc⟩
    letI : Std.Antisymm r :=
      ⟨fun _ _ hab hba => Encodable.encode_injective (le_antisymm hab hba)⟩
    letI : Std.Total r :=
      ⟨fun φ ψ => le_total (Encodable.encode φ) (Encodable.encode ψ)⟩
    let l := (sentenceDedup (trades.map Prod.snd)).insertionSort r
    have hnodup : l.Nodup :=
      (List.perm_insertionSort r _).nodup_iff.mpr
        (sentenceDedup_nodup (trades.map Prod.snd))
    have hsorted : l.Pairwise r := List.pairwise_insertionSort r _
    have htoFinset : l.toFinset = tradeListSupport trades := by
      ext φ
      simp [l, tradeListSupport]
    have hsort : (tradeListSupport trades).sort r = l := by
      rw [← htoFinset]
      exact (List.toFinset_sort (r := r) hnodup).mpr hsorted
    simpa [supportSentenceList, r] using hsort.symm

private lemma sentenceFinsetEncode_eq_supportSentenceList
    (S : Finset Sentence) :
    Encodable.encode S = Encodable.encode (supportSentenceList S) := by
  rw [sentenceFinsetEncode_eq]
  rfl

private lemma tradeListSupport_prim : Primrec tradeListSupport := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode.comp tradeListSupportSentenceList_prim).of_eq fun trades => by
    rw [sentenceFinsetEncode_eq_supportSentenceList]

private lemma tradeListSupportCard_prim :
    Primrec fun trades : List (EF × Sentence) => (tradeListSupport trades).card := by
  exact (Primrec.list_length.comp tradeListSupportSentenceList_prim).of_eq fun trades => by
    simp [supportSentenceList]

/-- The canonical code-sorted presentation of an arbitrary finite sentence set is
primitive recursive in the proof-erased finite-set encoding. -/
private lemma supportSentenceList_prim : Primrec supportSentenceList := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode : Primrec fun S : Finset Sentence => Encodable.encode S).of_eq
    fun S => by
      rw [sentenceFinsetEncode_eq_supportSentenceList]

/-- Membership in a finite sentence set is primitive recursive, through the set's
canonical sentence list. -/
lemma sentenceMemSupport_prim :
    PrimrecRel fun (S : Finset Sentence) (φ : Sentence) => φ ∈ S := by
  have hmem : PrimrecRel fun (l : List Sentence) (φ : Sentence) => φ ∈ l :=
    (Primrec.eq.exists_mem_list).of_eq fun l φ => by simp
  exact (hmem.comp₂
    (supportSentenceList_prim.comp₂ Primrec₂.left) Primrec₂.right).of_eq fun S φ => by
    simp [supportSentenceList]

private lemma sentenceMemTradeListSupport_prim :
    PrimrecRel fun (trades : List (EF × Sentence)) (φ : Sentence) =>
      φ ∈ tradeListSupport trades := by
  exact sentenceMemSupport_prim.comp₂
    (tradeListSupport_prim.comp₂ Primrec₂.left) Primrec₂.right

/-- The support side-condition in first-order MarketMaker acceptance is an exact
primitive-recursive predicate on the raw trades and candidate entries. -/
private lemma rationalBeliefStateSupportSubsetTradeList_prim :
    PrimrecPred fun p : List (EF × Sentence) × RationalBeliefState =>
      p.2.support ⊆ tradeListSupport p.1 := by
  have hentry : PrimrecRel
      (fun (trades : List (EF × Sentence)) (entry : Sentence × ℚ) =>
        entry.1 ∈ tradeListSupport trades) :=
    sentenceMemTradeListSupport_prim.comp₂ Primrec₂.left
      (Primrec.fst.comp₂ Primrec₂.right)
  have hall : PrimrecRel
      (fun (trades : List (EF × Sentence)) (entries : List (Sentence × ℚ)) =>
        ∀ entry ∈ entries, entry.1 ∈ tradeListSupport trades) :=
    hentry.swap.forall_mem_list.swap
  exact (hall.comp Primrec.fst
    (rationalBeliefStateEntries_prim.comp Primrec.snd)).of_eq fun p => by
      rcases p with ⟨trades, B⟩
      constructor
      · intro hall φ hφ
        have hlist : φ ∈ B.entries.map Prod.fst := by
          exact List.mem_toFinset.mp hφ
        obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hlist
        rw [← heq]
        exact hall entry hentry
      · intro hsubset entry hentry
        apply hsubset
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry, hentry, rfl⟩)

/-- Exact quotation from the candidate-updated rational history is primitive recursive
when all five inputs are packed as first-order data. -/
private lemma candidateRationalHistoryQuote_prim :
    Primrec fun p :
      ((((List RationalBeliefState × ℕ) × RationalBeliefState) × ℕ) × Sentence) =>
        candidateRationalHistory p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 := by
  have hday : PrimrecPred fun p :
      ((((List RationalBeliefState × ℕ) × RationalBeliefState) × ℕ) × Sentence) =>
        p.1.2 = p.1.1.1.2 :=
    Primrec.eq.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hcandidate : Primrec fun p :
      ((((List RationalBeliefState × ℕ) × RationalBeliefState) × ℕ) × Sentence) =>
        p.1.1.2.quote p.2 :=
    rationalBeliefStateQuote_prim.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have hpastInput : Primrec fun p :
      ((((List RationalBeliefState × ℕ) × RationalBeliefState) × ℕ) × Sentence) =>
        ((p.1.1.1.1, p.1.2), p.2) :=
    (Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd)
  have hpast : Primrec fun p :
      ((((List RationalBeliefState × ℕ) × RationalBeliefState) × ℕ) × Sentence) =>
        rationalHistory p.1.1.1.1 p.1.2 p.2 :=
    rationalHistory_prim.comp hpastInput
  exact (Primrec.ite hday hcandidate hpast).of_eq fun p => by
    rcases p with ⟨⟨⟨⟨past, n⟩, B⟩, day⟩, φ⟩
    by_cases h : day = n <;>
      simp [candidateRationalHistory, Function.update, h]

/-- The raw support-world lookup used by first-order MarketMaker acceptance is
primitive recursive in the trade list, Boolean table, and queried sentence. -/
private lemma tradeListSupportBitWorldRatFromList_prim :
    Primrec fun p : ((List (EF × Sentence) × List Bool) × Sentence) =>
      tradeListSupportBitWorldRatFromList p.1.1 p.1.2 p.2 := by
  let P := ((List (EF × Sentence) × List Bool) × Sentence)
  have htrades : Primrec fun p : P => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hbits : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hsentence : Primrec fun p : P => p.2 := Primrec.snd
  have hsupport : Primrec (fun p : P =>
      supportSentenceList (tradeListSupport p.1.1)) :=
    tradeListSupportSentenceList_prim.comp htrades
  have hmem : PrimrecPred fun p :
      P =>
        p.2 ∈ tradeListSupport p.1.1 :=
    sentenceMemTradeListSupport_prim.comp htrades hsentence
  have hidx : Primrec (fun p : P =>
      (supportSentenceList (tradeListSupport p.1.1)).idxOf p.2) :=
    Primrec.list_idxOf.comp hsentence hsupport
  have hbit : Primrec (fun p : P =>
      p.1.2.getD ((supportSentenceList (tradeListSupport p.1.1)).idxOf p.2) false) :=
    (Primrec.list_getD false).comp hbits hidx
  have hvalue : Primrec (fun p : P =>
      if p.1.2.getD ((supportSentenceList (tradeListSupport p.1.1)).idxOf p.2) false
      then (1 : ℚ) else 0) :=
    (Primrec.cond hbit (Primrec.const 1) (Primrec.const 0)).of_eq fun p => by
      cases p.1.2.getD
          ((supportSentenceList (tradeListSupport p.1.1)).idxOf p.2) false <;> rfl
  exact (Primrec.ite hmem hvalue (Primrec.const 0)).of_eq fun p => by
    rcases p with ⟨⟨trades, xs⟩, φ⟩
    rfl

/-! ## Exact stack-machine semantics for rational `EF` evaluation -/

/-- A command is `(kind, payload, environment)`.  Kind `0` evaluates the raw `EF.toNat`
payload; kinds `1`--`4` combine values; kind `5` enters a saved `letE` body.  Using only
products and lists keeps the runtime state first-order and automatically `Primcodable`. -/
private abbrev EFRatCommand := ℕ × (ℕ × List ℚ)

private abbrev EFRatMachineState := List EFRatCommand × List ℚ

private def efRatRawEvalCommand (code : ℕ) (rho : List ℚ) : EFRatCommand :=
  (0, code, rho)

private def efRatEvalCommand (e : EF) (rho : List ℚ) : EFRatCommand :=
  efRatRawEvalCommand e.toNat rho

private def efRatOpCommand (kind : ℕ) : EFRatCommand := (kind, 0, [])

private def efRatLetBodyCommand (bodyCode : ℕ) (rho : List ℚ) : EFRatCommand :=
  (5, bodyCode, rho)

/-- One deterministic evaluator instruction.  Malformed raw syntax and malformed stacks
are totalized with zero or by dropping the bad instruction; reachable states from an `EF`
never use those fallback branches. -/
private def efRatMachineStep {C : Type*} (V : C → ℕ → Sentence → ℚ) (ctx : C) :
    EFRatMachineState → EFRatMachineState
  | ([], values) => ([], values)
  | ((kind, payload, rho) :: commands, values) =>
      match kind with
      | 0 =>
          let code := payload
          let efPayload := code.unpair.2
          match code.unpair.1 with
          | 0 =>
              (commands,
                (Encodable.decode (α := ℚ) efPayload).getD 0 :: values)
          | 1 =>
              let q := match Encodable.decode (α := Sentence) efPayload.unpair.1 with
                | some φ => V ctx efPayload.unpair.2 φ
                | none => 0
              (commands, q :: values)
          | 2 =>
              (efRatRawEvalCommand efPayload.unpair.1 rho ::
                efRatRawEvalCommand efPayload.unpair.2 rho ::
                efRatOpCommand 1 :: commands, values)
          | 3 =>
              (efRatRawEvalCommand efPayload.unpair.1 rho ::
                efRatRawEvalCommand efPayload.unpair.2 rho ::
                efRatOpCommand 2 :: commands, values)
          | 4 =>
              (efRatRawEvalCommand efPayload.unpair.1 rho ::
                efRatRawEvalCommand efPayload.unpair.2 rho ::
                efRatOpCommand 3 :: commands, values)
          | 5 =>
              (efRatRawEvalCommand efPayload rho :: efRatOpCommand 4 :: commands,
                values)
          | 6 => (commands, rho.getD efPayload 0 :: values)
          | 7 =>
              (efRatRawEvalCommand efPayload.unpair.1 rho ::
                efRatLetBodyCommand efPayload.unpair.2 rho :: commands, values)
          | _ => (commands, 0 :: values)
      | 1 =>
          match values with
          | b :: a :: rest => (commands, (a + b) :: rest)
          | _ => (commands, values)
      | 2 =>
          match values with
          | b :: a :: rest => (commands, (a * b) :: rest)
          | _ => (commands, values)
      | 3 =>
          match values with
          | b :: a :: rest => (commands, max a b :: rest)
          | _ => (commands, values)
      | 4 =>
          match values with
          | a :: rest => (commands, (max 1 a)⁻¹ :: rest)
          | _ => (commands, values)
      | 5 =>
          match values with
          | q :: rest =>
              (efRatRawEvalCommand payload (q :: rho) :: commands, rest)
          | _ => (commands, values)
      | _ => (commands, values)

/-- Exact instruction count needed by the evaluator. -/
private def efRatMachineSteps : EF → ℕ
  | .price _ _ => 1
  | .const _ => 1
  | .add a b => efRatMachineSteps a + efRatMachineSteps b + 2
  | .mul a b => efRatMachineSteps a + efRatMachineSteps b + 2
  | .max a b => efRatMachineSteps a + efRatMachineSteps b + 2
  | .safeRecip a => efRatMachineSteps a + 2
  | .var _ => 1
  | .letE x body => efRatMachineSteps x + efRatMachineSteps body + 2

private lemma efRatMachineSteps_le (e : EF) :
    efRatMachineSteps e ≤ 2 * e.cost := by
  induction e with
  | price => simp [efRatMachineSteps, EF.cost]
  | const => simp [efRatMachineSteps, EF.cost]
  | add a b iha ihb => simp only [efRatMachineSteps, EF.cost]; omega
  | mul a b iha ihb => simp only [efRatMachineSteps, EF.cost]; omega
  | max a b iha ihb => simp only [efRatMachineSteps, EF.cost]; omega
  | safeRecip a iha => simp only [efRatMachineSteps, EF.cost]; omega
  | var => simp [efRatMachineSteps, EF.cost]
  | letE x body ihx ihbody => simp only [efRatMachineSteps, EF.cost]; omega

private lemma iterate_add_forward {α : Type*} (f : α → α) (m n : ℕ) (x : α) :
    f^[m + n] x = f^[n] (f^[m] x) := by
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- Running exactly the structural instruction count evaluates one feature and preserves
the surrounding continuation/value stack. -/
private lemma efRatMachine_correct {C : Type*} (V : C → ℕ → Sentence → ℚ)
    (ctx : C) (e : EF) (rho : List ℚ) (commands : List EFRatCommand)
    (values : List ℚ) :
    (efRatMachineStep V ctx)^[efRatMachineSteps e]
        (efRatEvalCommand e rho :: commands, values) =
      (commands, e.denoteRatWith rho (V ctx) :: values) := by
  induction e generalizing rho commands values with
  | price φ day =>
      simp [efRatMachineSteps, efRatEvalCommand, efRatRawEvalCommand,
        efRatMachineStep, EF.toNat, EF.denoteRatWith, Encodable.encodek]
  | const q =>
      simp [efRatMachineSteps, efRatEvalCommand, efRatRawEvalCommand,
        efRatMachineStep, EF.toNat, EF.denoteRatWith, Encodable.encodek]
  | var i =>
      simp [efRatMachineSteps, efRatEvalCommand, efRatRawEvalCommand,
        efRatMachineStep, EF.toNat, EF.denoteRatWith]
  | add a b iha ihb =>
      let f := efRatMachineStep V ctx
      rw [show efRatMachineSteps (EF.add a b) =
          1 + efRatMachineSteps a + efRatMachineSteps b + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + efRatMachineSteps b + 1 =
          1 + (efRatMachineSteps a + efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + efRatMachineSteps b + 1]
          (f (efRatEvalCommand (EF.add a b) rho :: commands, values)) = _
      simp only [f, efRatEvalCommand, efRatRawEvalCommand, efRatMachineStep,
        EF.toNat, Nat.unpair_pair]
      rw [show efRatMachineSteps a + efRatMachineSteps b + 1 =
          efRatMachineSteps a + (efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f (efRatMachineSteps a)]
      rw [show f^[efRatMachineSteps a]
          ((0, a.toNat, rho) :: (0, b.toNat, rho) :: efRatOpCommand 1 :: commands, values) =
          ((0, b.toNat, rho) :: efRatOpCommand 1 :: commands,
            a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          iha rho (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands) values]
      rw [iterate_add_forward f (efRatMachineSteps b) 1]
      rw [show f^[efRatMachineSteps b]
          ((0, b.toNat, rho) :: efRatOpCommand 1 :: commands,
            a.denoteRatWith rho (V ctx) :: values) =
          (efRatOpCommand 1 :: commands,
            b.denoteRatWith rho (V ctx) :: a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          ihb rho (efRatOpCommand 1 :: commands) (a.denoteRatWith rho (V ctx) :: values)]
      simp [f, efRatMachineStep, efRatOpCommand, EF.denoteRatWith]
  | mul a b iha ihb =>
      let f := efRatMachineStep V ctx
      rw [show efRatMachineSteps (EF.mul a b) =
          1 + efRatMachineSteps a + efRatMachineSteps b + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + efRatMachineSteps b + 1 =
          1 + (efRatMachineSteps a + efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + efRatMachineSteps b + 1]
          (f (efRatEvalCommand (EF.mul a b) rho :: commands, values)) = _
      simp only [f, efRatEvalCommand, efRatRawEvalCommand, efRatMachineStep,
        EF.toNat, Nat.unpair_pair]
      rw [show efRatMachineSteps a + efRatMachineSteps b + 1 =
          efRatMachineSteps a + (efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f (efRatMachineSteps a)]
      rw [show f^[efRatMachineSteps a]
          ((0, a.toNat, rho) :: (0, b.toNat, rho) :: efRatOpCommand 2 :: commands, values) =
          ((0, b.toNat, rho) :: efRatOpCommand 2 :: commands,
            a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          iha rho (efRatEvalCommand b rho :: efRatOpCommand 2 :: commands) values]
      rw [iterate_add_forward f (efRatMachineSteps b) 1]
      rw [show f^[efRatMachineSteps b]
          ((0, b.toNat, rho) :: efRatOpCommand 2 :: commands,
            a.denoteRatWith rho (V ctx) :: values) =
          (efRatOpCommand 2 :: commands,
            b.denoteRatWith rho (V ctx) :: a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          ihb rho (efRatOpCommand 2 :: commands) (a.denoteRatWith rho (V ctx) :: values)]
      simp [f, efRatMachineStep, efRatOpCommand, EF.denoteRatWith]
  | max a b iha ihb =>
      let f := efRatMachineStep V ctx
      rw [show efRatMachineSteps (EF.max a b) =
          1 + efRatMachineSteps a + efRatMachineSteps b + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + efRatMachineSteps b + 1 =
          1 + (efRatMachineSteps a + efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + efRatMachineSteps b + 1]
          (f (efRatEvalCommand (EF.max a b) rho :: commands, values)) = _
      simp only [f, efRatEvalCommand, efRatRawEvalCommand, efRatMachineStep,
        EF.toNat, Nat.unpair_pair]
      rw [show efRatMachineSteps a + efRatMachineSteps b + 1 =
          efRatMachineSteps a + (efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f (efRatMachineSteps a)]
      rw [show f^[efRatMachineSteps a]
          ((0, a.toNat, rho) :: (0, b.toNat, rho) :: efRatOpCommand 3 :: commands, values) =
          ((0, b.toNat, rho) :: efRatOpCommand 3 :: commands,
            a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          iha rho (efRatEvalCommand b rho :: efRatOpCommand 3 :: commands) values]
      rw [iterate_add_forward f (efRatMachineSteps b) 1]
      rw [show f^[efRatMachineSteps b]
          ((0, b.toNat, rho) :: efRatOpCommand 3 :: commands,
            a.denoteRatWith rho (V ctx) :: values) =
          (efRatOpCommand 3 :: commands,
            b.denoteRatWith rho (V ctx) :: a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          ihb rho (efRatOpCommand 3 :: commands) (a.denoteRatWith rho (V ctx) :: values)]
      simp [f, efRatMachineStep, efRatOpCommand, EF.denoteRatWith]
  | safeRecip a iha =>
      let f := efRatMachineStep V ctx
      rw [show efRatMachineSteps (EF.safeRecip a) =
          1 + efRatMachineSteps a + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + 1 =
          1 + (efRatMachineSteps a + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + 1]
          (f (efRatEvalCommand (EF.safeRecip a) rho :: commands, values)) = _
      simp only [f, efRatEvalCommand, efRatRawEvalCommand, efRatMachineStep,
        EF.toNat, Nat.unpair_pair]
      rw [iterate_add_forward f (efRatMachineSteps a) 1]
      rw [show f^[efRatMachineSteps a]
          ((0, a.toNat, rho) :: efRatOpCommand 4 :: commands, values) =
          (efRatOpCommand 4 :: commands, a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          iha rho (efRatOpCommand 4 :: commands) values]
      simp [f, efRatMachineStep, efRatOpCommand, EF.denoteRatWith]
  | letE x body ihx ihbody =>
      let f := efRatMachineStep V ctx
      rw [show efRatMachineSteps (EF.letE x body) =
          1 + efRatMachineSteps x + 1 + efRatMachineSteps body by
        simp [efRatMachineSteps]; omega]
      rw [show 1 + efRatMachineSteps x + 1 + efRatMachineSteps body =
          1 + (efRatMachineSteps x + 1 + efRatMachineSteps body) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps x + 1 + efRatMachineSteps body]
          (f (efRatEvalCommand (EF.letE x body) rho :: commands, values)) = _
      simp only [f, efRatEvalCommand, efRatRawEvalCommand, efRatMachineStep,
        EF.toNat, Nat.unpair_pair]
      rw [show efRatMachineSteps x + 1 + efRatMachineSteps body =
          efRatMachineSteps x + (1 + efRatMachineSteps body) by omega]
      rw [iterate_add_forward f (efRatMachineSteps x)]
      rw [show f^[efRatMachineSteps x]
          ((0, x.toNat, rho) :: efRatLetBodyCommand body.toNat rho :: commands, values) =
          (efRatLetBodyCommand body.toNat rho :: commands,
            x.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          ihx rho (efRatLetBodyCommand body.toNat rho :: commands) values]
      rw [iterate_add_forward f 1 (efRatMachineSteps body)]
      simp only [Function.iterate_one]
      simp only [f, efRatMachineStep, efRatLetBodyCommand]
      rw [show (efRatMachineStep V ctx)^[efRatMachineSteps body]
          (efRatRawEvalCommand body.toNat (x.denoteRatWith rho (V ctx) :: rho) ::
            commands, values) =
          (commands, body.denoteRatWith (x.denoteRatWith rho (V ctx) :: rho) (V ctx) :: values) by
        simpa only [efRatEvalCommand] using
          ihbody (x.denoteRatWith rho (V ctx) :: rho) commands values]
      rfl

/-! ## Primitive-recursive compilation of the evaluator transition -/

private def efRatBinaryValueStep (op : ℚ → ℚ → ℚ) :
    EFRatMachineState → EFRatMachineState
  | (commands, b :: a :: rest) => (commands, op a b :: rest)
  | state => state

private lemma efRatBinaryValueStep_prim (op : ℚ → ℚ → ℚ) (hop : Primrec₂ op) :
    Primrec (efRatBinaryValueStep op) := by
  let S := EFRatMachineState
  let Y := S × (ℚ × List ℚ)
  have htail : Primrec fun y : Y => y.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hresult : Primrec₂ fun (y : Y) (ar : ℚ × List ℚ) =>
      (y.1.1, op ar.1 y.2.1 :: ar.2) := by
    have ha : Primrec fun z : Y × (ℚ × List ℚ) => z.2.1 :=
      Primrec.fst.comp Primrec.snd
    have hb : Primrec fun z : Y × (ℚ × List ℚ) => z.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hrest : Primrec fun z : Y × (ℚ × List ℚ) => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hvalues : Primrec fun z : Y × (ℚ × List ℚ) =>
        op z.2.1 z.1.2.1 :: z.2.2 :=
      Primrec.list_cons.comp (hop.comp ha hb) hrest
    have hcommands : Primrec fun z : Y × (ℚ × List ℚ) => z.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    exact (hcommands.pair hvalues).to₂
  have hsecond : Primrec fun y : Y =>
      match y.2.2 with
      | [] => y.1
      | a :: rest => (y.1.1, op a y.2.1 :: rest) :=
    (Primrec.list_casesOn htail Primrec.fst hresult).of_eq fun y => by
      cases y.2.2 <;> rfl
  exact (Primrec.list_casesOn Primrec.snd Primrec.id hsecond.to₂).of_eq fun state => by
    rcases state with ⟨commands, values⟩
    cases values with
    | nil => rfl
    | cons b tail =>
        cases tail <;> rfl

private def efRatUnaryValueStep (op : ℚ → ℚ) :
    EFRatMachineState → EFRatMachineState
  | (commands, a :: rest) => (commands, op a :: rest)
  | state => state

private lemma efRatUnaryValueStep_prim (op : ℚ → ℚ) (hop : Primrec op) :
    Primrec (efRatUnaryValueStep op) := by
  have hresult : Primrec₂ fun (state : EFRatMachineState) (ar : ℚ × List ℚ) =>
      (state.1, op ar.1 :: ar.2) := by
    have hop' : Primrec fun z : EFRatMachineState × (ℚ × List ℚ) => op z.2.1 :=
      hop.comp (Primrec.fst.comp Primrec.snd)
    have hrest : Primrec fun z : EFRatMachineState × (ℚ × List ℚ) => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hvalues : Primrec fun z : EFRatMachineState × (ℚ × List ℚ) =>
        op z.2.1 :: z.2.2 :=
      Primrec.list_cons.comp hop' hrest
    have hcommands : Primrec fun z : EFRatMachineState × (ℚ × List ℚ) => z.1.1 :=
      Primrec.fst.comp Primrec.fst
    exact (hcommands.pair hvalues).to₂
  exact (Primrec.list_casesOn Primrec.snd Primrec.id hresult).of_eq fun state => by
    rcases state with ⟨commands, values⟩
    cases values <;> rfl

private def efRatLetValueStep (payload : ℕ) (rho : List ℚ) :
    EFRatMachineState → EFRatMachineState
  | (commands, q :: rest) =>
      (efRatRawEvalCommand payload (q :: rho) :: commands, rest)
  | state => state

private lemma efRatLetValueStep_prim :
    Primrec fun p : (ℕ × List ℚ) × EFRatMachineState =>
      efRatLetValueStep p.1.1 p.1.2 p.2 := by
  let P := (ℕ × List ℚ) × EFRatMachineState
  have hvalues : Primrec fun p : P => p.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hresult : Primrec₂ fun (p : P) (qr : ℚ × List ℚ) =>
      (efRatRawEvalCommand p.1.1 (qr.1 :: p.1.2) :: p.2.1, qr.2) := by
    have hq : Primrec fun z : P × (ℚ × List ℚ) => z.2.1 :=
      Primrec.fst.comp Primrec.snd
    have hrho : Primrec fun z : P × (ℚ × List ℚ) => z.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have henv : Primrec fun z : P × (ℚ × List ℚ) => z.2.1 :: z.1.1.2 :=
      Primrec.list_cons.comp hq hrho
    have hpayload : Primrec fun z : P × (ℚ × List ℚ) => z.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hcommand : Primrec fun z : P × (ℚ × List ℚ) =>
        efRatRawEvalCommand z.1.1.1 (z.2.1 :: z.1.1.2) :=
      (Primrec.const 0).pair (hpayload.pair henv)
    have hcommands : Primrec fun z : P × (ℚ × List ℚ) => z.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hnewCommands : Primrec fun z : P × (ℚ × List ℚ) =>
        efRatRawEvalCommand z.1.1.1 (z.2.1 :: z.1.1.2) :: z.1.2.1 :=
      Primrec.list_cons.comp hcommand hcommands
    have hrest : Primrec fun z : P × (ℚ × List ℚ) => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    exact (hnewCommands.pair hrest).to₂
  exact (Primrec.list_casesOn hvalues Primrec.snd hresult).of_eq fun p => by
    rcases p with ⟨⟨payload, rho⟩, commands, values⟩
    cases values <;> rfl

private lemma efRatSafeRecip_prim : Primrec fun q : ℚ => (max 1 q)⁻¹ := by
  have hmax : Primrec fun q : ℚ => max 1 q :=
    ratMax_prim.comp (Primrec.const 1) Primrec.id
  exact ratInv_prim.comp hmax

private abbrev EFRatRawInput (C : Type*) :=
  C × (ℕ × (List ℚ × EFRatMachineState))

private def efRatRawStep {C : Type*} (V : C → ℕ → Sentence → ℚ)
    (p : EFRatRawInput C) : EFRatMachineState :=
  let ctx := p.1
  let code := p.2.1
  let rho := p.2.2.1
  let commands := p.2.2.2.1
  let values := p.2.2.2.2
  let tag := code.unpair.1
  let payload := code.unpair.2
  if tag = 0 then
    (commands, (Encodable.decode (α := ℚ) payload).getD 0 :: values)
  else if tag = 1 then
    let q := match Encodable.decode (α := Sentence) payload.unpair.1 with
      | some φ => V ctx payload.unpair.2 φ
      | none => 0
    (commands, q :: values)
  else if tag = 2 then
    (efRatRawEvalCommand payload.unpair.1 rho ::
      efRatRawEvalCommand payload.unpair.2 rho ::
      efRatOpCommand 1 :: commands, values)
  else if tag = 3 then
    (efRatRawEvalCommand payload.unpair.1 rho ::
      efRatRawEvalCommand payload.unpair.2 rho ::
      efRatOpCommand 2 :: commands, values)
  else if tag = 4 then
    (efRatRawEvalCommand payload.unpair.1 rho ::
      efRatRawEvalCommand payload.unpair.2 rho ::
      efRatOpCommand 3 :: commands, values)
  else if tag = 5 then
    (efRatRawEvalCommand payload rho :: efRatOpCommand 4 :: commands, values)
  else if tag = 6 then
    (commands, rho.getD payload 0 :: values)
  else if tag = 7 then
    (efRatRawEvalCommand payload.unpair.1 rho ::
      efRatLetBodyCommand payload.unpair.2 rho :: commands, values)
  else
    (commands, 0 :: values)

private lemma efRatRawStep_prim {C : Type*} [Primcodable C]
    (V : C → ℕ → Sentence → ℚ)
    (hV : Primrec fun p : C × (ℕ × Sentence) => V p.1 p.2.1 p.2.2) :
    Primrec (efRatRawStep V) := by
  let P := EFRatRawInput C
  have hcode : Primrec fun p : P => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hrho : Primrec fun p : P => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hcommands : Primrec fun p : P => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hvalues : Primrec fun p : P => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have htag : Primrec fun p : P => p.2.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hcode)
  have hpayload : Primrec fun p : P => p.2.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hcode)
  have hpayloadLeft : Primrec fun p : P => p.2.1.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hpayload)
  have hpayloadRight : Primrec fun p : P => p.2.1.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hpayload)
  have hrawLeft : Primrec fun p : P =>
      efRatRawEvalCommand p.2.1.unpair.2.unpair.1 p.2.2.1 :=
    (Primrec.const 0).pair (hpayloadLeft.pair hrho)
  have hrawRight : Primrec fun p : P =>
      efRatRawEvalCommand p.2.1.unpair.2.unpair.2 p.2.2.1 :=
    (Primrec.const 0).pair (hpayloadRight.pair hrho)
  have hrawPayload : Primrec fun p : P =>
      efRatRawEvalCommand p.2.1.unpair.2 p.2.2.1 :=
    (Primrec.const 0).pair (hpayload.pair hrho)
  have hopCommand (kind : ℕ) : Primrec fun _p : P => efRatOpCommand kind :=
    Primrec.const (efRatOpCommand kind)
  have hletCommand : Primrec fun p : P =>
      efRatLetBodyCommand p.2.1.unpair.2.unpair.2 p.2.2.1 :=
    (Primrec.const 5).pair (hpayloadRight.pair hrho)
  have hprepend3 {first second third : P → EFRatCommand}
      (hfirst : Primrec first) (hsecond : Primrec second) (hthird : Primrec third) :
      Primrec fun p : P => first p :: second p :: third p :: p.2.2.2.1 :=
    Primrec.list_cons.comp hfirst
      (Primrec.list_cons.comp hsecond (Primrec.list_cons.comp hthird hcommands))
  have hprepend2 {first second : P → EFRatCommand}
      (hfirst : Primrec first) (hsecond : Primrec second) :
      Primrec fun p : P => first p :: second p :: p.2.2.2.1 :=
    Primrec.list_cons.comp hfirst (Primrec.list_cons.comp hsecond hcommands)
  have hcase0 : Primrec fun p : P =>
      (p.2.2.2.1,
        (Encodable.decode (α := ℚ) p.2.1.unpair.2).getD 0 :: p.2.2.2.2) := by
    have hq : Primrec fun p : P =>
        (Encodable.decode (α := ℚ) p.2.1.unpair.2).getD 0 :=
      Primrec.option_getD.comp
        ((Primrec.decode : Primrec fun n : ℕ => Encodable.decode (α := ℚ) n).comp hpayload)
        (Primrec.const 0)
    exact hcommands.pair (Primrec.list_cons.comp hq hvalues)
  have hcase1 : Primrec fun p : P =>
      (p.2.2.2.1,
        (match Encodable.decode (α := Sentence) p.2.1.unpair.2.unpair.1 with
          | some φ => V p.1 p.2.1.unpair.2.unpair.2 φ
          | none => 0) :: p.2.2.2.2) := by
    have hs : Primrec fun p : P =>
        Encodable.decode (α := Sentence) p.2.1.unpair.2.unpair.1 :=
      (Primrec.decode : Primrec fun n : ℕ => Encodable.decode (α := Sentence) n).comp
        hpayloadLeft
    have hsome : Primrec₂ fun (p : P) (φ : Sentence) =>
        V p.1 p.2.1.unpair.2.unpair.2 φ := by
      have harg : Primrec fun z : P × Sentence =>
          (z.1.1, (z.1.2.1.unpair.2.unpair.2, z.2)) := by
        have hc : Primrec fun z : P × Sentence => z.1.1 :=
          Primrec.fst.comp Primrec.fst
        have hd : Primrec fun z : P × Sentence => z.1.2.1.unpair.2.unpair.2 :=
          hpayloadRight.comp Primrec.fst
        exact hc.pair (hd.pair Primrec.snd)
      exact (hV.comp harg).to₂
    have hq : Primrec fun p : P =>
        match Encodable.decode (α := Sentence) p.2.1.unpair.2.unpair.1 with
        | some φ => V p.1 p.2.1.unpair.2.unpair.2 φ
        | none => 0 :=
      (Primrec.option_casesOn hs (Primrec.const 0) hsome).of_eq fun p => by
        cases h : Encodable.decode (α := Sentence) p.2.1.unpair.2.unpair.1 <;>
          simp
    exact hcommands.pair (Primrec.list_cons.comp hq hvalues)
  have hcommandCase {first second third : P → EFRatCommand}
      (hfirst : Primrec first) (hsecond : Primrec second) (hthird : Primrec third) :
      Primrec fun p : P =>
        (first p :: second p :: third p :: p.2.2.2.1, p.2.2.2.2) :=
    (hprepend3 hfirst hsecond hthird).pair hvalues
  have hcase2 : Primrec fun p : P =>
      (efRatRawEvalCommand p.2.1.unpair.2.unpair.1 p.2.2.1 ::
        efRatRawEvalCommand p.2.1.unpair.2.unpair.2 p.2.2.1 ::
        efRatOpCommand 1 :: p.2.2.2.1, p.2.2.2.2) :=
    hcommandCase hrawLeft hrawRight (hopCommand 1)
  have hcase3 : Primrec fun p : P =>
      (efRatRawEvalCommand p.2.1.unpair.2.unpair.1 p.2.2.1 ::
        efRatRawEvalCommand p.2.1.unpair.2.unpair.2 p.2.2.1 ::
        efRatOpCommand 2 :: p.2.2.2.1, p.2.2.2.2) :=
    hcommandCase hrawLeft hrawRight (hopCommand 2)
  have hcase4 : Primrec fun p : P =>
      (efRatRawEvalCommand p.2.1.unpair.2.unpair.1 p.2.2.1 ::
        efRatRawEvalCommand p.2.1.unpair.2.unpair.2 p.2.2.1 ::
        efRatOpCommand 3 :: p.2.2.2.1, p.2.2.2.2) :=
    hcommandCase hrawLeft hrawRight (hopCommand 3)
  have hcase5 : Primrec fun p : P =>
      (efRatRawEvalCommand p.2.1.unpair.2 p.2.2.1 ::
        efRatOpCommand 4 :: p.2.2.2.1, p.2.2.2.2) :=
    (hprepend2 hrawPayload (hopCommand 4)).pair hvalues
  have hcase6 : Primrec fun p : P =>
      (p.2.2.2.1, p.2.2.1.getD p.2.1.unpair.2 0 :: p.2.2.2.2) := by
    have hq : Primrec fun p : P => p.2.2.1.getD p.2.1.unpair.2 0 :=
      (Primrec.list_getD 0).comp hrho hpayload
    exact hcommands.pair (Primrec.list_cons.comp hq hvalues)
  have hcase7 : Primrec fun p : P =>
      (efRatRawEvalCommand p.2.1.unpair.2.unpair.1 p.2.2.1 ::
        efRatLetBodyCommand p.2.1.unpair.2.unpair.2 p.2.2.1 :: p.2.2.2.1,
        p.2.2.2.2) :=
    (hprepend2 hrawLeft hletCommand).pair hvalues
  have hfallback : Primrec fun p : P =>
      (p.2.2.2.1, (0 : ℚ) :: p.2.2.2.2) :=
    hcommands.pair (Primrec.list_cons.comp (Primrec.const 0) hvalues)
  have htagEq (k : ℕ) : PrimrecPred fun p : P => p.2.1.unpair.1 = k :=
    Primrec.eq.comp htag (Primrec.const k)
  exact (Primrec.ite (htagEq 0) hcase0
    (Primrec.ite (htagEq 1) hcase1
      (Primrec.ite (htagEq 2) hcase2
        (Primrec.ite (htagEq 3) hcase3
          (Primrec.ite (htagEq 4) hcase4
            (Primrec.ite (htagEq 5) hcase5
              (Primrec.ite (htagEq 6) hcase6
                (Primrec.ite (htagEq 7) hcase7 hfallback)))))))).of_eq fun p => by
    rfl

private abbrev EFRatCommandInput (C : Type*) :=
  C × (EFRatCommand × EFRatMachineState)

private def efRatCommandStep {C : Type*} (V : C → ℕ → Sentence → ℚ)
    (p : EFRatCommandInput C) : EFRatMachineState :=
  let ctx := p.1
  let kind := p.2.1.1
  let payload := p.2.1.2.1
  let rho := p.2.1.2.2
  let state := p.2.2
  if kind = 0 then
    efRatRawStep V (ctx, payload, rho, state)
  else if kind = 1 then
    efRatBinaryValueStep (· + ·) state
  else if kind = 2 then
    efRatBinaryValueStep (· * ·) state
  else if kind = 3 then
    efRatBinaryValueStep max state
  else if kind = 4 then
    efRatUnaryValueStep (fun q => (max 1 q)⁻¹) state
  else if kind = 5 then
    efRatLetValueStep payload rho state
  else
    state

private lemma efRatCommandStep_prim {C : Type*} [Primcodable C]
    (V : C → ℕ → Sentence → ℚ)
    (hV : Primrec fun p : C × (ℕ × Sentence) => V p.1 p.2.1 p.2.2) :
    Primrec (efRatCommandStep V) := by
  let P := EFRatCommandInput C
  have hctx : Primrec fun p : P => p.1 := Primrec.fst
  have hkind : Primrec fun p : P => p.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hpayload : Primrec fun p : P => p.2.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hrho : Primrec fun p : P => p.2.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hstate : Primrec fun p : P => p.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hrawArg : Primrec fun p : P =>
      (p.1, (p.2.1.2.1, (p.2.1.2.2, p.2.2))) :=
    hctx.pair (hpayload.pair (hrho.pair hstate))
  have hcase0 : Primrec fun p : P =>
      efRatRawStep V (p.1, p.2.1.2.1, p.2.1.2.2, p.2.2) :=
    (efRatRawStep_prim V hV).comp hrawArg
  have hcase1 : Primrec fun p : P => efRatBinaryValueStep (· + ·) p.2.2 :=
    (efRatBinaryValueStep_prim (· + ·) ratAdd_prim).comp hstate
  have hcase2 : Primrec fun p : P => efRatBinaryValueStep (· * ·) p.2.2 :=
    (efRatBinaryValueStep_prim (· * ·) ratMul_prim).comp hstate
  have hcase3 : Primrec fun p : P => efRatBinaryValueStep max p.2.2 :=
    (efRatBinaryValueStep_prim max ratMax_prim).comp hstate
  have hcase4 : Primrec fun p : P =>
      efRatUnaryValueStep (fun q => (max 1 q)⁻¹) p.2.2 :=
    (efRatUnaryValueStep_prim (fun q => (max 1 q)⁻¹) efRatSafeRecip_prim).comp hstate
  have hletArg : Primrec fun p : P => ((p.2.1.2.1, p.2.1.2.2), p.2.2) :=
    (hpayload.pair hrho).pair hstate
  have hcase5 : Primrec fun p : P =>
      efRatLetValueStep p.2.1.2.1 p.2.1.2.2 p.2.2 :=
    efRatLetValueStep_prim.comp hletArg
  have hkindEq (k : ℕ) : PrimrecPred fun p : P => p.2.1.1 = k :=
    Primrec.eq.comp hkind (Primrec.const k)
  exact (Primrec.ite (hkindEq 0) hcase0
    (Primrec.ite (hkindEq 1) hcase1
      (Primrec.ite (hkindEq 2) hcase2
        (Primrec.ite (hkindEq 3) hcase3
          (Primrec.ite (hkindEq 4) hcase4
            (Primrec.ite (hkindEq 5) hcase5 hstate)))))).of_eq fun p => by
    rfl

private lemma efRatMachineStep_packed_prim {C : Type*} [Primcodable C]
    (V : C → ℕ → Sentence → ℚ)
    (hV : Primrec fun p : C × (ℕ × Sentence) => V p.1 p.2.1 p.2.2) :
    Primrec fun p : C × EFRatMachineState => efRatMachineStep V p.1 p.2 := by
  let P := C × EFRatMachineState
  have hcommands : Primrec fun p : P => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hcons : Primrec₂ fun (p : P) (cr : EFRatCommand × List EFRatCommand) =>
      efRatCommandStep V (p.1, cr.1, cr.2, p.2.2) := by
    have harg : Primrec fun z : P × (EFRatCommand × List EFRatCommand) =>
        (z.1.1, (z.2.1, (z.2.2, z.1.2.2))) := by
      have hctx : Primrec fun z : P × (EFRatCommand × List EFRatCommand) => z.1.1 :=
        Primrec.fst.comp Primrec.fst
      have hcommand : Primrec fun z : P × (EFRatCommand × List EFRatCommand) => z.2.1 :=
        Primrec.fst.comp Primrec.snd
      have hrest : Primrec fun z : P × (EFRatCommand × List EFRatCommand) => z.2.2 :=
        Primrec.snd.comp Primrec.snd
      have hvalues : Primrec fun z : P × (EFRatCommand × List EFRatCommand) => z.1.2.2 :=
        Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
      exact hctx.pair (hcommand.pair (hrest.pair hvalues))
    exact ((efRatCommandStep_prim V hV).comp harg).to₂
  refine (Primrec.list_casesOn hcommands Primrec.snd hcons).of_eq ?_
  intro p
  rcases p with ⟨ctx, commands, values⟩
  cases commands with
  | nil => rfl
  | cons command rest =>
      rcases command with ⟨kind, payload, rho⟩
      simp only [efRatCommandStep]
      by_cases h0 : kind = 0
      · subst kind
        simp only [if_pos]
        generalize ht : payload.unpair.1 = tag
        by_cases hlt : tag < 8
        · interval_cases tag <;> simp [efRatRawStep, efRatMachineStep, ht]
        · have hle : 8 ≤ tag := by omega
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
          cases k with
          | zero => simp [efRatRawStep, efRatMachineStep, ht]
          | succ n =>
              rw [show 8 + (n + 1) = n + 9 by omega] at ht
              simp [efRatRawStep, efRatMachineStep, ht]
      · by_cases h1 : kind = 1
        · subst kind
          simp only [h0, if_false, if_pos]
          rcases values with _ | ⟨b, tail⟩
          · rfl
          · rcases tail with _ | ⟨a, tail⟩ <;> rfl
        · by_cases h2 : kind = 2
          · subst kind
            simp only [h0, h1, if_false, if_pos]
            rcases values with _ | ⟨b, tail⟩
            · rfl
            · rcases tail with _ | ⟨a, tail⟩ <;> rfl
          · by_cases h3 : kind = 3
            · subst kind
              simp only [h0, h1, h2, if_false, if_pos]
              rcases values with _ | ⟨b, tail⟩
              · rfl
              · rcases tail with _ | ⟨a, tail⟩ <;> rfl
            · by_cases h4 : kind = 4
              · subst kind
                simp only [h0, h1, h2, h3, if_false, if_pos]
                cases values <;> rfl
              · by_cases h5 : kind = 5
                · subst kind
                  simp only [h0, h1, h2, h3, h4, if_false, if_pos]
                  cases values <;> rfl
                · simp [h0, h1, h2, h3, h4, h5, efRatMachineStep]

private lemma efCost_le_toNat_succ (e : EF) : e.cost ≤ e.toNat + 1 := by
  induction e with
  | const q => simp [EF.cost, EF.toNat]
  | price φ day => simp [EF.cost, EF.toNat]
  | add a b iha ihb =>
      have hp := Nat.add_le_pair a.toNat b.toNat
      have ho := Nat.add_le_pair 2 (Nat.pair a.toNat b.toNat)
      simp only [EF.cost, EF.toNat]
      omega
  | mul a b iha ihb =>
      have hp := Nat.add_le_pair a.toNat b.toNat
      have ho := Nat.add_le_pair 3 (Nat.pair a.toNat b.toNat)
      simp only [EF.cost, EF.toNat]
      omega
  | max a b iha ihb =>
      have hp := Nat.add_le_pair a.toNat b.toNat
      have ho := Nat.add_le_pair 4 (Nat.pair a.toNat b.toNat)
      simp only [EF.cost, EF.toNat]
      omega
  | safeRecip a iha =>
      have ho := Nat.add_le_pair 5 a.toNat
      simp only [EF.cost, EF.toNat]
      omega
  | var i => simp [EF.cost, EF.toNat]
  | letE x body ihx ihbody =>
      have hp := Nat.add_le_pair x.toNat body.toNat
      have ho := Nat.add_le_pair 7 (Nat.pair x.toNat body.toNat)
      simp only [EF.cost, EF.toNat]
      omega

private def efRatMachineFuel (e : EF) : ℕ := 2 * (e.toNat + 1)

private lemma efRatMachineSteps_le_fuel (e : EF) :
    efRatMachineSteps e ≤ efRatMachineFuel e := by
  exact (efRatMachineSteps_le e).trans
    (Nat.mul_le_mul_left 2 (efCost_le_toNat_succ e))

private lemma efRatMachine_terminal {C : Type*}
    (V : C → ℕ → Sentence → ℚ) (ctx : C) (values : List ℚ) :
    efRatMachineStep V ctx ([], values) = ([], values) := rfl

private lemma efRatMachine_fuel_correct {C : Type*}
    (V : C → ℕ → Sentence → ℚ) (ctx : C) (e : EF) :
    (efRatMachineStep V ctx)^[efRatMachineFuel e]
        ([efRatEvalCommand e []], []) = ([], [e.denoteRat (V ctx)]) := by
  obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le (efRatMachineSteps_le_fuel e)
  rw [hextra, iterate_add_forward]
  rw [efRatMachine_correct V ctx e [] [] []]
  exact Function.iterate_fixed (efRatMachine_terminal V ctx [e.denoteRat (V ctx)]) extra

/-- Evaluate an expressible feature to an exact rational by running the stack machine of
the section above for `efRatMachineFuel e` steps against the context's quote table `V`.
`efRatCompiledEval_eq` identifies it with `EF.denoteRat` and `efRatCompiledEval_prim`
certifies it primitive recursive; `Construction/Statistics/SettlementCompiler.lean` runs
it against the *total* quote table, where `EF.denoteRatWithAtFuel_complete` supplies the guard
that every listed price query was answered (`dd:dsl`). -/
def efRatCompiledEval {C : Type*} (V : C → ℕ → Sentence → ℚ)
    (ctx : C) (e : EF) : ℚ :=
  (((efRatMachineStep V ctx)^[efRatMachineFuel e]
      ([efRatEvalCommand e []], [])).2).getD 0 0

/-- The compiled evaluator agrees with `EF.denoteRat` on the context's quote table. -/
lemma efRatCompiledEval_eq {C : Type*}
    (V : C → ℕ → Sentence → ℚ) (ctx : C) (e : EF) :
    efRatCompiledEval V ctx e = e.denoteRat (V ctx) := by
  rw [efRatCompiledEval, efRatMachine_fuel_correct]
  rfl

/-- The compiled evaluator is primitive recursive whenever the quote table is. -/
lemma efRatCompiledEval_prim {C : Type*} [Primcodable C]
    (V : C → ℕ → Sentence → ℚ)
    (hV : Primrec fun p : C × (ℕ × Sentence) => V p.1 p.2.1 p.2.2) :
    Primrec fun p : C × EF => efRatCompiledEval V p.1 p.2 := by
  let P := C × EF
  have he : Primrec fun p : P => p.2 := Primrec.snd
  have hcode : Primrec fun p : P => p.2.toNat := by
    exact (Primrec.encode.comp he).of_eq fun p => rfl
  have hfuel : Primrec fun p : P => efRatMachineFuel p.2 := by
    have hsucc : Primrec fun p : P => p.2.toNat + 1 :=
      Primrec.nat_add.comp hcode (Primrec.const 1)
    exact (Primrec.nat_mul.comp (Primrec.const 2) hsucc).of_eq fun p => by
      rfl
  have hcommand : Primrec fun p : P => efRatEvalCommand p.2 [] :=
    (Primrec.const 0).pair (hcode.pair (Primrec.const []))
  have hcommands : Primrec fun p : P => [efRatEvalCommand p.2 []] :=
    Primrec.list_cons.comp hcommand (Primrec.const [])
  have hinit : Primrec fun p : P =>
      (([efRatEvalCommand p.2 []], []) : EFRatMachineState) :=
    hcommands.pair (Primrec.const [])
  have hstep : Primrec₂ fun (p : P) (state : EFRatMachineState) =>
      efRatMachineStep V p.1 state := by
    have harg : Primrec fun z : P × EFRatMachineState => (z.1.1, z.2) :=
      (Primrec.fst.comp Primrec.fst).pair Primrec.snd
    exact ((efRatMachineStep_packed_prim V hV).comp harg).to₂
  have hrun : Primrec fun p : P =>
      (efRatMachineStep V p.1)^[efRatMachineFuel p.2]
        ([efRatEvalCommand p.2 []], []) :=
    Primrec.nat_iterate hfuel hinit hstep
  have hresultValues : Primrec fun p : P =>
      ((efRatMachineStep V p.1)^[efRatMachineFuel p.2]
        ([efRatEvalCommand p.2 []], [])).2 :=
    Primrec.snd.comp hrun
  exact (Primrec.list_getD 0).comp hresultValues (Primrec.const 0)

/-! ## MarketMaker: the bounded candidate search

The MarketMaker prices a day by searching for the least candidate belief state that all
of the day's accepted trades value non-positively.  The search runs over proof-erased
rational belief states, so every state it inspects is ordinary first-order data. -/

private abbrev CandidateQuoteContext :=
  (List RationalBeliefState × ℕ) × RationalBeliefState

private def candidateQuote (ctx : CandidateQuoteContext)
    (day : ℕ) (φ : Sentence) : ℚ :=
  candidateRationalHistory ctx.1.1 ctx.1.2 ctx.2 day φ

private lemma candidateQuote_prim :
    Primrec fun p : CandidateQuoteContext × (ℕ × Sentence) =>
      candidateQuote p.1 p.2.1 p.2.2 := by
  have hpack : Primrec fun p : CandidateQuoteContext × (ℕ × Sentence) =>
      ((((p.1.1.1, p.1.1.2), p.1.2), p.2.1), p.2.2) :=
    (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
      (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.fst.comp Primrec.snd) |>.pair
          (Primrec.snd.comp Primrec.snd)
  exact (candidateRationalHistoryQuote_prim.comp hpack).of_eq fun p => by
    rfl

-- `Nat.sqrt` irreducible: see the module header.
attribute [local irreducible] Nat.sqrt in
/-- A generic exact compiler for rational market value.  The context supplies both the
history quotation and the finite world's payout; the trade list itself remains ordinary
first-order data. -/
private lemma tradeListMarketValueRat_prim {C : Type*} [Primcodable C]
    (V : C → ℕ → Sentence → ℚ) (W : C → Sentence → ℚ)
    (hV : Primrec fun p : C × (ℕ × Sentence) => V p.1 p.2.1 p.2.2)
    (hW : Primrec fun p : C × Sentence => W p.1 p.2) :
    Primrec fun p : ((C × ℕ) × List (EF × Sentence)) =>
      tradeListMarketValueRat p.2 p.1.2 (V p.1.1) (W p.1.1) := by
  let P := ((C × ℕ) × List (EF × Sentence))
  let A := ((EF × Sentence) × ℚ)
  have hctx : Primrec fun z : P × A => z.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hday : Primrec fun z : P × A => z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have he : Primrec fun z : P × A => z.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hsentence : Primrec fun z : P × A => z.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hacc : Primrec fun z : P × A => z.2.2 :=
    Primrec.snd.comp Primrec.snd
  have heval : Primrec fun z : P × A =>
      efRatCompiledEval V z.1.1.1 z.2.1.1 :=
    (efRatCompiledEval_prim V hV).comp (hctx.pair he)
  have hworld : Primrec fun z : P × A => W z.1.1.1 z.2.1.2 :=
    hW.comp (hctx.pair hsentence)
  have hprice : Primrec fun z : P × A => V z.1.1.1 z.1.1.2 z.2.1.2 :=
    hV.comp (hctx.pair (hday.pair hsentence))
  have hstep : Primrec₂ fun (p : P) (a : A) =>
      efRatCompiledEval V p.1.1 a.1.1 *
          (W p.1.1 a.1.2 - V p.1.1 p.1.2 a.1.2) + a.2 :=
    (ratAdd_prim.comp
      (ratMul_prim.comp heval (ratSub_prim.comp hworld hprice)) hacc).to₂
  exact (Primrec.list_foldr Primrec.snd (Primrec.const 0) hstep).of_eq fun p => by
    rcases p with ⟨⟨ctx, day⟩, trades⟩
    simp only [tradeListMarketValueRat]
    induction trades with
    | nil => rfl
    | cons trade rest ih =>
        simp only [List.foldr, List.map_cons, List.sum_cons]
        rw [efRatCompiledEval_eq, ih]

private abbrev MarketValueContext :=
  CandidateQuoteContext × (List (EF × Sentence) × List Bool)

private def marketValueHistory (ctx : MarketValueContext)
    (day : ℕ) (φ : Sentence) : ℚ := candidateQuote ctx.1 day φ

private def marketValueWorld (ctx : MarketValueContext) (φ : Sentence) : ℚ :=
  tradeListSupportBitWorldRatFromList ctx.2.1 ctx.2.2 φ

private lemma marketValueHistory_prim :
    Primrec fun p : MarketValueContext × (ℕ × Sentence) =>
      marketValueHistory p.1 p.2.1 p.2.2 := by
  have hinput : Primrec fun p : MarketValueContext × (ℕ × Sentence) =>
      (p.1.1, p.2) :=
    (Primrec.fst.comp Primrec.fst).pair Primrec.snd
  exact (candidateQuote_prim.comp hinput).of_eq fun p => rfl

private lemma marketValueWorld_prim :
    Primrec fun p : MarketValueContext × Sentence =>
      marketValueWorld p.1 p.2 := by
  have hinput : Primrec fun p : MarketValueContext × Sentence =>
      ((p.1.2.1, p.1.2.2), p.2) :=
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd
  exact (tradeListSupportBitWorldRatFromList_prim.comp hinput).of_eq fun p => rfl

private abbrev MarketMakerWorldInput :=
  ((((List (EF × Sentence) × ℕ) × List RationalBeliefState) ×
    RationalBeliefState) × List Bool)

private def marketMakerWorldValue (p : MarketMakerWorldInput) : ℚ :=
  tradeListMarketValueRat p.1.1.1.1 p.1.1.1.2
    (candidateRationalHistory p.1.1.2 p.1.1.1.2 p.1.2)
    (tradeListSupportBitWorldRatFromList p.1.1.1.1 p.2)

-- `Nat.sqrt` irreducible: see the module header.
attribute [local irreducible] Nat.sqrt in
private lemma marketMakerWorldValue_prim :
    Primrec marketMakerWorldValue := by
  have htrades : Primrec fun p : MarketMakerWorldInput => p.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hday : Primrec fun p : MarketMakerWorldInput => p.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hpast : Primrec fun p : MarketMakerWorldInput => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hcandidate : Primrec fun p : MarketMakerWorldInput =>
      ((p.1.1.2, p.1.1.1.2), p.1.2) :=
    (hpast.pair hday).pair (Primrec.snd.comp Primrec.fst)
  have hworld : Primrec fun p : MarketMakerWorldInput =>
      (p.1.1.1.1, p.2) := htrades.pair Primrec.snd
  have hctx : Primrec fun p : MarketMakerWorldInput =>
      (((p.1.1.2, p.1.1.1.2), p.1.2), (p.1.1.1.1, p.2)) :=
    hcandidate.pair hworld
  have hsource : Primrec fun p : MarketMakerWorldInput =>
      (((((p.1.1.2, p.1.1.1.2), p.1.2), (p.1.1.1.1, p.2)),
        p.1.1.1.2), p.1.1.1.1) :=
    (hctx.pair hday).pair htrades
  exact ((tradeListMarketValueRat_prim marketValueHistory marketValueWorld
    marketValueHistory_prim marketValueWorld_prim).comp hsource).of_eq fun p => by
      rfl

private abbrev MarketMakerCoreInput :=
  (((List (EF × Sentence) × ℕ) × List RationalBeliefState) × RationalBeliefState)

private abbrev MarketMakerAcceptInput := MarketMakerCoreInput × ℚ

private def marketMakerAcceptsData (p : MarketMakerAcceptInput) : Prop :=
  p.1.2.support ⊆ tradeListSupport p.1.1.1.1 ∧
    ∀ xs ∈ allBoolLists (tradeListSupport p.1.1.1.1).card,
      marketMakerWorldValue (p.1, xs) ≤ p.2

private lemma marketMakerAcceptsData_iff (p : MarketMakerAcceptInput) :
    marketMakerAcceptsData p ↔
      MarketMakerAcceptsTradeList p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.2 p.1.2 := by
  rfl

private lemma marketMakerAcceptsData_prim :
    PrimrecPred marketMakerAcceptsData := by
  have htrades : Primrec fun p : MarketMakerAcceptInput => p.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hcandidate : Primrec fun p : MarketMakerAcceptInput => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hsubset : PrimrecPred fun p : MarketMakerAcceptInput =>
      p.1.2.support ⊆ tradeListSupport p.1.1.1.1 :=
    rationalBeliefStateSupportSubsetTradeList_prim.comp
      (htrades.pair hcandidate)
  have hworld : Primrec fun z : MarketMakerAcceptInput × List Bool =>
      marketMakerWorldValue (z.1.1, z.2) :=
    marketMakerWorldValue_prim.comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hle : PrimrecRel fun (p : MarketMakerAcceptInput) (xs : List Bool) =>
      marketMakerWorldValue (p.1, xs) ≤ p.2 :=
    ratLE_prim.comp hworld (Primrec.snd.comp Primrec.fst)
  have hall : PrimrecRel fun (p : MarketMakerAcceptInput)
      (xss : List (List Bool)) =>
        ∀ xs ∈ xss, marketMakerWorldValue (p.1, xs) ≤ p.2 :=
    hle.swap.forall_mem_list.swap
  have hassignments : Primrec fun p : MarketMakerAcceptInput =>
      allBoolLists (tradeListSupport p.1.1.1.1).card :=
    allBoolLists_prim.comp (tradeListSupportCard_prim.comp htrades)
  have hworlds : PrimrecPred fun p : MarketMakerAcceptInput =>
      ∀ xs ∈ allBoolLists (tradeListSupport p.1.1.1.1).card,
        marketMakerWorldValue (p.1, xs) ≤ p.2 :=
    hall.comp Primrec.id hassignments
  exact (hsubset.and hworlds).of_eq fun p => by
    rfl

private abbrev MarketMakerSearchInput :=
  (((List (EF × Sentence) × ℕ) × List RationalBeliefState) × ℚ)

/-- The first-order candidate test used by the executable MarketMaker search.  Decoding
failure is rejection; a successful decode is checked by the exact finite Boolean-world
acceptance predicate above. -/
private def marketMakerCandidateAcceptsData
    (p : MarketMakerSearchInput × ℕ) : Prop :=
  match marketMakerCandidate p.2 with
  | none => False
  | some B => marketMakerAcceptsData ((p.1.1, B), p.1.2)

private lemma marketMakerCandidateAcceptsData_iff
    (p : MarketMakerSearchInput × ℕ) :
    marketMakerCandidateAcceptsData p ↔
      MarketMakerCandidateAcceptsTradeList p.1.1.1.1 p.1.1.1.2
        p.1.1.2 p.1.2 p.2 := by
  unfold marketMakerCandidateAcceptsData
  cases hB : marketMakerCandidate p.2 with
  | none =>
      simp [MarketMakerCandidateAcceptsTradeList, hB]
  | some B =>
      simp [MarketMakerCandidateAcceptsTradeList, hB,
        marketMakerAcceptsData_iff]

private instance marketMakerCandidateAcceptsDataDecidable
    (p : MarketMakerSearchInput × ℕ) :
    Decidable (marketMakerCandidateAcceptsData p) :=
  decidable_of_iff
    (MarketMakerCandidateAcceptsTradeList p.1.1.1.1 p.1.1.1.2
      p.1.1.2 p.1.2 p.2)
    (marketMakerCandidateAcceptsData_iff p).symm

-- `Nat.sqrt` irreducible: see the module header.
attribute [local irreducible] Nat.sqrt in
private lemma marketMakerCandidateAcceptsData_prim :
    PrimrecPred marketMakerCandidateAcceptsData := by
  letI : DecidablePred marketMakerAcceptsData :=
    marketMakerAcceptsData_prim.choose
  have hcandidate : Primrec fun p : MarketMakerSearchInput × ℕ =>
      marketMakerCandidate p.2 :=
    marketMakerCandidate_prim.comp Primrec.snd
  have hacceptInput : Primrec₂ fun
      (p : MarketMakerSearchInput × ℕ) (B : RationalBeliefState) =>
      ((p.1.1, B), p.1.2) := by
    have hcore : Primrec₂ fun
        (p : MarketMakerSearchInput × ℕ) (B : RationalBeliefState) =>
        (p.1.1, B) :=
      Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
        Primrec₂.right
    exact Primrec₂.pair.comp₂ hcore
      (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
  have hsome : Primrec₂ fun
      (p : MarketMakerSearchInput × ℕ) (B : RationalBeliefState) =>
      decide (marketMakerAcceptsData ((p.1.1, B), p.1.2)) :=
    marketMakerAcceptsData_prim.decide.comp₂ hacceptInput
  have hdecide : Primrec fun p : MarketMakerSearchInput × ℕ =>
      decide (marketMakerCandidateAcceptsData p) :=
    (Primrec.option_casesOn hcandidate (Primrec.const false) hsome).of_eq fun p => by
      cases hB : marketMakerCandidate p.2 <;>
        simp [marketMakerCandidateAcceptsData, hB]
  exact hdecide.primrecPred

private def marketMakerSearchStepData (ctx : MarketMakerSearchInput)
    (ni : ℕ × Option ℕ) : Option ℕ :=
  match ni.2 with
  | some k => some k
  | none =>
      if marketMakerCandidateAcceptsData (ctx, ni.1) then some ni.1 else none

/-- Packed, first-order form of MarketMaker's bounded least-candidate search. -/
private def marketMakerSearchIndexData (ctx : MarketMakerSearchInput) :
    ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
      marketMakerSearchStepData ctx
        (fuel, marketMakerSearchIndexData ctx fuel)

private lemma marketMakerSearchIndexData_eq
    (ctx : MarketMakerSearchInput) (fuel : ℕ) :
    marketMakerSearchIndexData ctx fuel =
      marketMakerSearchIndexUpToTradeList ctx.1.1.1 ctx.1.1.2
        ctx.1.2 ctx.2 fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [marketMakerSearchIndexData,
        marketMakerSearchStepData, marketMakerSearchIndexUpToTradeList, ih]
      cases hsearch : marketMakerSearchIndexUpToTradeList ctx.1.1.1
          ctx.1.1.2 ctx.1.2 ctx.2 fuel with
      | some k => rfl
      | none =>
          by_cases h : marketMakerCandidateAcceptsData (ctx, fuel)
          · have h' : MarketMakerCandidateAcceptsTradeList ctx.1.1.1
                ctx.1.1.2 ctx.1.2 ctx.2 fuel :=
              (marketMakerCandidateAcceptsData_iff (ctx, fuel)).mp h
            simp [h, h']
          · have h' : ¬MarketMakerCandidateAcceptsTradeList ctx.1.1.1
                ctx.1.1.2 ctx.1.2 ctx.2 fuel := fun hs =>
              h ((marketMakerCandidateAcceptsData_iff (ctx, fuel)).mpr hs)
            simp [h, h']

-- `Nat.sqrt` irreducible: see the module header.
attribute [local irreducible] Nat.sqrt in
private lemma marketMakerSearchStepData_prim :
    Primrec₂ marketMakerSearchStepData := by
  let X := MarketMakerSearchInput × (ℕ × Option ℕ)
  have hfuel : Primrec fun x : X => x.2.1 :=
    Primrec.fst.comp (Primrec.snd)
  have htestInput : Primrec fun x : X => (x.1, x.2.1) :=
    Primrec.fst.pair hfuel
  have htest : PrimrecPred fun x : X =>
      marketMakerCandidateAcceptsData (x.1, x.2.1) :=
    marketMakerCandidateAcceptsData_prim.comp htestInput
  have hnone : Primrec fun x : X =>
      if marketMakerCandidateAcceptsData (x.1, x.2.1) then
        some x.2.1
      else none :=
    Primrec.ite htest
      (Primrec.option_some.comp hfuel)
      (Primrec.const none)
  have hprior : Primrec fun x : X => x.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hsome : Primrec₂ fun (_x : X) (k : ℕ) => (some k : Option ℕ) :=
    Primrec₂.option_some_iff.mpr Primrec₂.right
  have hstepPacked : Primrec fun x : X => marketMakerSearchStepData x.1 x.2 :=
    Primrec.option_casesOn hprior hnone hsome
      |>.of_eq fun x => by
        cases h : x.2.2 <;> simp [marketMakerSearchStepData, h]
  exact hstepPacked.to₂

private lemma marketMakerSearchIndexData_prim :
    Primrec fun p : MarketMakerSearchInput × ℕ =>
      marketMakerSearchIndexData p.1 p.2 := by
  have hrec : Primrec₂ fun (ctx : MarketMakerSearchInput) fuel =>
      marketMakerSearchIndexData ctx fuel :=
    (Primrec.nat_rec (Primrec.const none)
      marketMakerSearchStepData_prim).of_eq fun ctx fuel => by
      induction fuel with
      | zero => rfl
      | succ fuel ih => simp [marketMakerSearchIndexData, ih]
  exact hrec.comp Primrec.fst Primrec.snd

/-- The actual raw-trade-list MarketMaker search is primitive recursive, with no appeal
to the semantic fixed-point witness or to unbounded minimization. -/
private lemma marketMakerSearchIndexUpToTradeList_prim :
    Primrec fun p : MarketMakerSearchInput × ℕ =>
      marketMakerSearchIndexUpToTradeList p.1.1.1.1 p.1.1.1.2
        p.1.1.2 p.1.2 p.2 :=
  marketMakerSearchIndexData_prim.of_eq fun p =>
    marketMakerSearchIndexData_eq p.1 p.2

/-- Decoding the successful bounded-search index is primitive recursive as well. -/
private lemma marketMakerSearchUpToTradeList_prim :
    Primrec fun p : MarketMakerSearchInput × ℕ =>
      marketMakerSearchUpToTradeList p.1.1.1.1 p.1.1.1.2
        p.1.1.2 p.1.2 p.2 := by
  have hdecode : Primrec₂ fun
      (_p : MarketMakerSearchInput × ℕ) (k : ℕ) =>
      marketMakerCandidate k :=
    marketMakerCandidate_prim.comp₂ Primrec₂.right
  exact (Primrec.option_bind marketMakerSearchIndexUpToTradeList_prim
    hdecode).of_eq fun p => by
      rfl

/-! ## First-order Budgeter atom compiler -/

/-- Occurrence list of atoms in a sentence.  Deduplication and sorting are deliberately
kept separate, since the Budgeter atom universe combines many sentences before
canonicalizing. -/
def sentenceAtomOccurrences : Sentence → List ℕ
  | .atom a => [a]
  | .falsum => []
  | .and φ ψ => sentenceAtomOccurrences φ ++ sentenceAtomOccurrences ψ
  | .or φ ψ => sentenceAtomOccurrences φ ++ sentenceAtomOccurrences ψ
  | .imp φ ψ => sentenceAtomOccurrences φ ++ sentenceAtomOccurrences ψ

private def formulaAtomOccurrencesBinary
    (prior : List (Option (List ℕ))) (children : ℕ) : Option (List ℕ) := do
  let left ← prior.getD children.unpair.1 none
  let right ← prior.getD children.unpair.2 none
  some (left ++ right)

private lemma formulaAtomOccurrencesBinary_prim :
    Primrec₂ formulaAtomOccurrencesBinary := by
  let X := List (Option (List ℕ)) × ℕ
  have hleftIndex : Primrec fun p : X => p.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hrightIndex : Primrec fun p : X => p.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hleft : Primrec fun p : X => p.1.getD p.2.unpair.1 none :=
    (Primrec.list_getD none).comp Primrec.fst hleftIndex
  have hright : Primrec fun p : X => p.1.getD p.2.unpair.2 none :=
    (Primrec.list_getD none).comp Primrec.fst hrightIndex
  have hrightBind : Primrec₂ fun (p : X) (left : List ℕ) =>
      (p.1.getD p.2.unpair.2 none).bind fun right =>
        some (left ++ right) := by
    let Y := X × List ℕ
    have hrightY : Primrec fun y : Y =>
        y.1.1.getD y.1.2.unpair.2 none :=
      hright.comp Primrec.fst
    have hout : Primrec₂ fun (y : Y) (right : List ℕ) =>
        some (y.2 ++ right) :=
      Primrec₂.option_some_iff.mpr
        (Primrec.list_append.comp₂
          (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
    exact (Primrec.option_bind hrightY hout).to₂
  exact (Primrec.option_bind hleft hrightBind).to₂.of_eq fun prior children => by
    rfl

private def formulaAtomOccurrencesSucc
    (prior : List (Option (List ℕ))) (e : ℕ) : Option (List ℕ) :=
  let tag := e.unpair.1
  let payload := e.unpair.2
  if tag = 0 then some []
  else if tag = 1 then some [payload]
  else if tag = 2 then formulaAtomOccurrencesBinary prior payload
  else if tag = 3 then formulaAtomOccurrencesBinary prior payload
  else if tag = 4 then formulaAtomOccurrencesBinary prior payload
  else none

private lemma formulaAtomOccurrencesSucc_prim :
    Primrec₂ formulaAtomOccurrencesSucc := by
  let tag : List (Option (List ℕ)) × ℕ → ℕ := fun p => p.2.unpair.1
  let payload : List (Option (List ℕ)) × ℕ → ℕ := fun p => p.2.unpair.2
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hpayload : Primrec payload := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have htagEq (k : ℕ) : PrimrecPred fun p : List (Option (List ℕ)) × ℕ =>
      tag p = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have hbinary : Primrec fun p : List (Option (List ℕ)) × ℕ =>
      formulaAtomOccurrencesBinary p.1 (payload p) :=
    formulaAtomOccurrencesBinary_prim.comp Primrec.fst hpayload
  have hatom : Primrec fun p : List (Option (List ℕ)) × ℕ =>
      (some [payload p] : Option (List ℕ)) :=
    Primrec.option_some.comp
      (Primrec.list_cons.comp hpayload (Primrec.const []))
  exact (Primrec.ite (htagEq 0) (Primrec.const (some []))
    (Primrec.ite (htagEq 1) hatom
      (Primrec.ite (htagEq 2) hbinary
        (Primrec.ite (htagEq 3) hbinary
          (Primrec.ite (htagEq 4) hbinary
            (Primrec.const none)))))).to₂.of_eq
    fun prior e => by simp only [formulaAtomOccurrencesSucc, tag, payload]

private def formulaAtomOccurrencesStep
    (prior : List (Option (List ℕ))) : Option (List ℕ) :=
  prior.length.casesOn none (formulaAtomOccurrencesSucc prior)

private lemma formulaAtomOccurrencesStep_prim :
    Primrec formulaAtomOccurrencesStep := by
  exact (Primrec.nat_casesOn Primrec.list_length (Primrec.const none)
    formulaAtomOccurrencesSucc_prim).of_eq fun prior => by
      simp only [formulaAtomOccurrencesStep]

private def formulaAtomOccurrencesDecoded (n : ℕ) : Option (List ℕ) :=
  (LO.Propositional.Formula.ofNat (α := ℕ) n).map sentenceAtomOccurrences

private lemma formulaAtomOccurrencesHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map formulaAtomOccurrencesDecoded).getD k none =
      formulaAtomOccurrencesDecoded k := by
  have hzero : formulaAtomOccurrencesDecoded 0 = none := by
    simp [formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat]
  rw [← hzero, List.getD_map]
  simp [hk]

private lemma formulaAtomOccurrencesBinary_history
    (payload n : ℕ) (hleft : payload.unpair.1 < n)
    (hright : payload.unpair.2 < n) :
    formulaAtomOccurrencesBinary
        ((List.range n).map formulaAtomOccurrencesDecoded) payload =
      ((LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1).bind fun φ =>
        (LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2).map fun ψ =>
          sentenceAtomOccurrences φ ++ sentenceAtomOccurrences ψ) := by
  unfold formulaAtomOccurrencesBinary
  rw [formulaAtomOccurrencesHistory_getD hleft,
    formulaAtomOccurrencesHistory_getD hright]
  cases hL : LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
    cases hR : LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
    simp [formulaAtomOccurrencesDecoded, hL, hR]

private lemma formulaAtomOccurrencesStep_history (n : ℕ) :
    formulaAtomOccurrencesStep
        ((List.range n).map formulaAtomOccurrencesDecoded) =
      formulaAtomOccurrencesDecoded n := by
  cases n with
  | zero =>
      simp [formulaAtomOccurrencesStep, formulaAtomOccurrencesDecoded,
        LO.Propositional.Formula.ofNat]
  | succ e =>
      let tag := e.unpair.1
      let payload := e.unpair.2
      have hleft : payload.unpair.1 < e + 1 := by
        dsimp [payload]
        exact Nat.lt_succ_iff.mpr <|
          le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have hright : payload.unpair.2 < e + 1 := by
        dsimp [payload]
        exact Nat.lt_succ_iff.mpr <|
          le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      by_cases h0 : tag = 0
      · simp [formulaAtomOccurrencesStep, formulaAtomOccurrencesSucc,
          formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat,
          tag, h0, sentenceAtomOccurrences]
      by_cases h1 : tag = 1
      · simp [formulaAtomOccurrencesStep, formulaAtomOccurrencesSucc,
          formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat,
          tag, h1, sentenceAtomOccurrences]
      by_cases h2 : tag = 2
      · subst tag
        have hb := formulaAtomOccurrencesBinary_history payload (e + 1) hleft hright
        simp only [formulaAtomOccurrencesStep, List.length_map, List.length_range,
          formulaAtomOccurrencesSucc, h2, ↓reduceIte]
        rw [hb]
        simp only [formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat,
          h2]
        cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
          cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
          rfl
      by_cases h3 : tag = 3
      · subst tag
        have hb := formulaAtomOccurrencesBinary_history payload (e + 1) hleft hright
        simp only [formulaAtomOccurrencesStep, List.length_map, List.length_range,
          formulaAtomOccurrencesSucc, h3, ↓reduceIte]
        rw [hb]
        simp only [formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat,
          h3]
        cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
          cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
          rfl
      by_cases h4 : tag = 4
      · subst tag
        have hb := formulaAtomOccurrencesBinary_history payload (e + 1) hleft hright
        simp only [formulaAtomOccurrencesStep, List.length_map, List.length_range,
          formulaAtomOccurrencesSucc, h4, ↓reduceIte]
        rw [hb]
        simp only [formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat,
          h4]
        cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
          cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
          rfl
      · have htag : 5 ≤ tag := by omega
        simp [formulaAtomOccurrencesStep, formulaAtomOccurrencesSucc,
          formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat,
          tag, h0, h1, h2, h3, h4]

private lemma formulaAtomOccurrencesDecoded_prim :
    Primrec formulaAtomOccurrencesDecoded := by
  have hstep : Primrec₂ fun (_ : Unit) (prior : List (Option (List ℕ))) =>
      some (formulaAtomOccurrencesStep prior) :=
    Primrec₂.option_some_iff.mpr
      (formulaAtomOccurrencesStep_prim.comp Primrec₂.right)
  have hrec := Primrec.nat_strong_rec
    (fun (_ : Unit) n => formulaAtomOccurrencesDecoded n)
    hstep (fun _ n => by
      simpa using congrArg some (formulaAtomOccurrencesStep_history n))
  exact hrec.comp (Primrec.const ()) Primrec.id

/-- The atom occurrence list of a sentence is primitive recursive. -/
lemma sentenceAtomOccurrences_prim :
    Primrec sentenceAtomOccurrences := by
  have hdecoded : Primrec fun φ : Sentence =>
      formulaAtomOccurrencesDecoded (Encodable.encode φ) :=
    formulaAtomOccurrencesDecoded_prim.comp Primrec.encode
  have hget : Primrec fun o : Option (List ℕ) => o.getD [] :=
    (Primrec.option_casesOn Primrec.id (Primrec.const [])
      Primrec₂.right).of_eq fun o => by cases o <;> rfl
  exact (hget.comp hdecoded).of_eq fun φ => by
    rw [show Encodable.encode φ =
      LO.Propositional.Formula.toNat φ by rfl]
    simp [formulaAtomOccurrencesDecoded,
      LO.Propositional.Formula.ofNat_toNat]

/-- The occurrence list carries exactly the sentence's atoms. -/
@[simp] lemma mem_sentenceAtomOccurrences :
    ∀ (φ : Sentence) (a : ℕ),
      a ∈ sentenceAtomOccurrences φ ↔ a ∈ φ.atoms := by
  intro φ
  induction φ with
  | atom b => intro a; simp [sentenceAtomOccurrences, Sentence.atoms]
  | falsum => intro a; simp [sentenceAtomOccurrences, Sentence.atoms]
  | imp φ ψ ihφ ihψ =>
      intro a
      simp [sentenceAtomOccurrences, Sentence.atoms, ihφ, ihψ]
  | and φ ψ ihφ ihψ =>
      intro a
      simp [sentenceAtomOccurrences, Sentence.atoms, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      intro a
      simp [sentenceAtomOccurrences, Sentence.atoms, ihφ, ihψ]

/-! ### Canonical finite atom lists

The operational Budgeter only needs a sorted, duplicate-free list of the atoms in its
finite universe.  Keeping that presentation as ordinary data avoids asking the runtime
compiler to inspect the quotient representation of `Finset`. -/

private def canonicalNatList (l : List ℕ) : List ℕ :=
  (listDedup l).insertionSort (fun a b => a ≤ b)

private lemma canonicalNatList_prim : Primrec canonicalNatList :=
  (insertionSort_prim (fun a b : ℕ => a ≤ b) Primrec.nat_le).comp listDedup_prim

private lemma canonicalNatList_eq_sort (l : List ℕ) :
    canonicalNatList l = l.toFinset.sort (fun a b => a ≤ b) := by
  let r : ℕ → ℕ → Prop := fun a b => a ≤ b
  let canonical := canonicalNatList l
  have hnodup : canonical.Nodup :=
    (List.perm_insertionSort r _).nodup_iff.mpr (listDedup_nodup l)
  have hsorted : canonical.Pairwise r := List.pairwise_insertionSort r _
  have htoFinset : canonical.toFinset = l.toFinset := by
    ext a
    simp [canonical, canonicalNatList]
  have hsort : l.toFinset.sort r = canonical := by
    rw [← htoFinset]
    exact (List.toFinset_sort (r := r) hnodup).mpr hsorted
  exact hsort.symm

private def sentenceListAtomOccurrences (sentences : List Sentence) : List ℕ :=
  sentences.flatMap sentenceAtomOccurrences

private lemma sentenceListAtomOccurrences_prim :
    Primrec sentenceListAtomOccurrences := by
  exact Primrec.list_flatMap Primrec.id
    (sentenceAtomOccurrences_prim.comp₂ Primrec₂.right)

@[simp] private lemma mem_sentenceListAtomOccurrences
    (sentences : List Sentence) (a : ℕ) :
    a ∈ sentenceListAtomOccurrences sentences ↔
      ∃ φ ∈ sentences, a ∈ φ.atoms := by
  simp [sentenceListAtomOccurrences]

private def tradeListAtomOccurrences (trades : List (EF × Sentence)) : List ℕ :=
  trades.flatMap fun trade => sentenceAtomOccurrences trade.2

private lemma tradeListAtomOccurrences_prim :
    Primrec tradeListAtomOccurrences := by
  exact Primrec.list_flatMap Primrec.id
    (sentenceAtomOccurrences_prim.comp₂
      (Primrec.snd.comp₂ Primrec₂.right))

@[simp] private lemma mem_tradeListAtomOccurrences
    (trades : List (EF × Sentence)) (a : ℕ) :
    a ∈ tradeListAtomOccurrences trades ↔
      a ∈ tradeListSentenceAtoms trades := by
  simp only [tradeListAtomOccurrences, List.mem_flatMap,
    mem_sentenceAtomOccurrences, tradeListSentenceAtoms, Finset.mem_biUnion,
    tradeListSupport, Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨⟨e, φ⟩, htrade, ha⟩
    exact ⟨φ, ⟨⟨e, φ⟩, htrade, rfl⟩, ha⟩
  · rintro ⟨φ, ⟨trade, htrade, hEq⟩, ha⟩
    exact ⟨trade, htrade, by simpa [hEq] using ha⟩

private def stageAtomOccurrences
    (stages : List (Finset Sentence)) (n : ℕ) : List ℕ :=
  sentenceListAtomOccurrences
    (supportSentenceList (decodedStageTable stages n))

private lemma stageAtomOccurrences_prim : Primrec₂ stageAtomOccurrences := by
  exact (sentenceListAtomOccurrences_prim.comp
    (supportSentenceList_prim.comp
      (decodedStageTable_prim.comp Primrec.fst Primrec.snd))).to₂

@[simp] private lemma mem_stageAtomOccurrences
    (stages : List (Finset Sentence)) (n a : ℕ) :
    a ∈ stageAtomOccurrences stages n ↔
      a ∈ (decodedStageTable stages n).biUnion Sentence.atoms := by
  simp [stageAtomOccurrences, supportSentenceList]

private def firmPrefixAtomOccurrences (j n : ℕ) : List ℕ :=
  (List.range (n + 1)).flatMap fun i =>
    tradeListAtomOccurrences ((firmRawTrader j).strat i).trades

private lemma firmPrefixAtomOccurrences_prim :
    Primrec₂ firmPrefixAtomOccurrences := by
  let P := ℕ × ℕ
  have hrange : Primrec fun p : P => List.range (p.2 + 1) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
  have htrades : Primrec₂ fun (p : P) (i : ℕ) =>
      ((firmRawTrader p.1).strat i).trades :=
    firmRawTraderTrades_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  exact (Primrec.list_flatMap hrange
    (tradeListAtomOccurrences_prim.comp₂ htrades)).to₂

@[simp] private lemma mem_firmPrefixAtomOccurrences (j n a : ℕ) :
    a ∈ firmPrefixAtomOccurrences j n ↔
      a ∈ (Finset.range (n + 1)).biUnion fun i =>
        tradeListSentenceAtoms ((firmRawTrader j).strat i).trades := by
  simp [firmPrefixAtomOccurrences]

private def budgetAtomList
    (stages : List (Finset Sentence)) (j n : ℕ) : List ℕ :=
  canonicalNatList
    (stageAtomOccurrences stages n ++ firmPrefixAtomOccurrences j n)

private lemma budgetAtomList_prim : Primrec fun p :
    (List (Finset Sentence) × ℕ) × ℕ => budgetAtomList p.1.1 p.1.2 p.2 := by
  have hraw : Primrec fun p : (List (Finset Sentence) × ℕ) × ℕ =>
      stageAtomOccurrences p.1.1 p.2 ++ firmPrefixAtomOccurrences p.1.2 p.2 :=
    Primrec.list_append.comp
      (stageAtomOccurrences_prim.comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (firmPrefixAtomOccurrences_prim.comp
        (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact canonicalNatList_prim.comp hraw

private lemma budgetAtomList_eq (stages : List (Finset Sentence)) (j n : ℕ) :
    budgetAtomList stages j n =
      (budgetAtomsFromStageTradeLists (decodedStageTable stages)
        (fun i => ((firmRawTrader j).strat i).trades) n).sort
          (fun a b => a ≤ b) := by
  rw [budgetAtomList, canonicalNatList_eq_sort]
  congr 1
  ext a
  simp [budgetAtomsFromStageTradeLists]

private def atomListTable (atoms : List ℕ) (xs : List Bool) (a : ℕ) : Bool :=
  if a ∈ atoms then xs.getD (atoms.idxOf a) false else false

private lemma atomListTable_prim : Primrec fun p :
    (List ℕ × List Bool) × ℕ => atomListTable p.1.1 p.1.2 p.2 := by
  have hmemList : PrimrecRel fun (atoms : List ℕ) (a : ℕ) => a ∈ atoms :=
    (Primrec.eq.exists_mem_list).of_eq fun atoms a => by simp
  have hmem : PrimrecPred fun p : (List ℕ × List Bool) × ℕ =>
      p.2 ∈ p.1.1 :=
    hmemList.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hidx : Primrec fun p : (List ℕ × List Bool) × ℕ =>
      p.1.1.idxOf p.2 :=
    Primrec.list_idxOf.comp Primrec.snd
      (Primrec.fst.comp Primrec.fst)
  have hbit : Primrec fun p : (List ℕ × List Bool) × ℕ =>
      p.1.2.getD (p.1.1.idxOf p.2) false :=
    (Primrec.list_getD false).comp
      (Primrec.snd.comp Primrec.fst) hidx
  exact (Primrec.ite hmem hbit (Primrec.const false)).of_eq fun p => by
    rfl

private lemma atomListTable_sort_eq (A : Finset ℕ) (xs : List Bool) :
    atomListTable (A.sort (fun a b => a ≤ b)) xs =
      finiteAtomTableFromList A xs := by
  funext a
  simp [atomListTable, finiteAtomTableFromList]

private def sentenceBoolFromAtomList
    (atoms : List ℕ) (xs : List Bool) (φ : Sentence) : Bool :=
  sentenceBool (atomListTable atoms xs) φ

private def formulaBoolBinary (op : Bool → Bool → Bool)
    (prior : List (Option Bool)) (children : ℕ) : Option Bool := do
  let left ← prior.getD children.unpair.1 none
  let right ← prior.getD children.unpair.2 none
  some (op left right)

private lemma formulaBoolBinary_prim (op : Bool → Bool → Bool) :
    Primrec₂ (formulaBoolBinary op) := by
  let X := List (Option Bool) × ℕ
  have hleftIndex : Primrec fun p : X => p.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hrightIndex : Primrec fun p : X => p.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hleft : Primrec fun p : X => p.1.getD p.2.unpair.1 none :=
    (Primrec.list_getD none).comp Primrec.fst hleftIndex
  have hright : Primrec fun p : X => p.1.getD p.2.unpair.2 none :=
    (Primrec.list_getD none).comp Primrec.fst hrightIndex
  have hrightBind : Primrec₂ fun (p : X) (left : Bool) =>
      (p.1.getD p.2.unpair.2 none).bind fun right =>
        some (op left right) := by
    let Y := X × Bool
    have hrightY : Primrec fun y : Y =>
        y.1.1.getD y.1.2.unpair.2 none :=
      hright.comp Primrec.fst
    have hout : Primrec₂ fun (y : Y) (right : Bool) =>
        some (op y.2 right) :=
      Primrec₂.option_some_iff.mpr
        ((Primrec.dom_bool₂ op).comp₂
          (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
    exact (Primrec.option_bind hrightY hout).to₂
  exact (Primrec.option_bind hleft hrightBind).to₂.of_eq fun prior children => by
    rfl

private def formulaBoolSucc
    (env : List ℕ × List Bool) (prior : List (Option Bool))
    (e : ℕ) : Option Bool :=
  let tag := e.unpair.1
  let payload := e.unpair.2
  if tag = 0 then some false
  else if tag = 1 then some (atomListTable env.1 env.2 payload)
  else if tag = 2 then formulaBoolBinary (fun a b => !a || b) prior payload
  else if tag = 3 then formulaBoolBinary (· && ·) prior payload
  else if tag = 4 then formulaBoolBinary (· || ·) prior payload
  else none

private lemma formulaBoolSucc_prim : Primrec₂ fun
    (p : (List ℕ × List Bool) × List (Option Bool)) (e : ℕ) =>
      formulaBoolSucc p.1 p.2 e := by
  let X := ((List ℕ × List Bool) × List (Option Bool)) × ℕ
  let tag : X → ℕ := fun p => p.2.unpair.1
  let payload : X → ℕ := fun p => p.2.unpair.2
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hpayload : Primrec payload :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have htagEq (k : ℕ) : PrimrecPred fun p : X => tag p = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have hatom : Primrec fun p : X =>
      (some (atomListTable p.1.1.1 p.1.1.2 (payload p)) : Option Bool) :=
    Primrec.option_some.comp
      (atomListTable_prim.comp
        (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
            hpayload))
  have hbinary (op : Bool → Bool → Bool) : Primrec fun p : X =>
      formulaBoolBinary op p.1.2 (payload p) :=
    (formulaBoolBinary_prim op).comp
      (Primrec.snd.comp Primrec.fst) hpayload
  have h4 : Primrec fun p : X =>
      if tag p = 4 then
        formulaBoolBinary (· || ·) p.1.2 (payload p)
      else none :=
    Primrec.ite (htagEq 4) (hbinary (· || ·)) (Primrec.const none)
  have h3 : Primrec fun p : X =>
      if tag p = 3 then formulaBoolBinary (· && ·) p.1.2 (payload p)
      else if tag p = 4 then
        formulaBoolBinary (· || ·) p.1.2 (payload p)
      else none :=
    Primrec.ite (htagEq 3) (hbinary (· && ·)) h4
  have h2 : Primrec fun p : X =>
      if tag p = 2 then
        formulaBoolBinary (fun a b => !a || b) p.1.2 (payload p)
      else if tag p = 3 then formulaBoolBinary (· && ·) p.1.2 (payload p)
      else if tag p = 4 then
        formulaBoolBinary (· || ·) p.1.2 (payload p)
      else none :=
    Primrec.ite (htagEq 2) (hbinary fun a b => !a || b) h3
  have h1 : Primrec fun p : X =>
      if tag p = 1 then some (atomListTable p.1.1.1 p.1.1.2 (payload p))
      else if tag p = 2 then
        formulaBoolBinary (fun a b => !a || b) p.1.2 (payload p)
      else if tag p = 3 then formulaBoolBinary (· && ·) p.1.2 (payload p)
      else if tag p = 4 then
        formulaBoolBinary (· || ·) p.1.2 (payload p)
      else none :=
    Primrec.ite (htagEq 1) hatom h2
  exact (Primrec.ite (htagEq 0) (Primrec.const (some false)) h1).to₂.of_eq
    fun p e => by simp only [formulaBoolSucc, tag, payload]

private def formulaBoolStep
    (env : List ℕ × List Bool) (prior : List (Option Bool)) : Option Bool :=
  prior.length.casesOn none (formulaBoolSucc env prior)

private lemma formulaBoolStep_prim : Primrec₂ formulaBoolStep := by
  have hsucc : Primrec₂ fun
      (p : (List ℕ × List Bool) × List (Option Bool)) (e : ℕ) =>
        formulaBoolSucc p.1 p.2 e := formulaBoolSucc_prim
  exact (Primrec.nat_casesOn
    (Primrec.list_length.comp Primrec.snd)
    (Primrec.const none) hsucc).of_eq fun p => by
      simp only [formulaBoolStep]

private def formulaBoolDecoded
    (env : List ℕ × List Bool) (n : ℕ) : Option Bool :=
  (LO.Propositional.Formula.ofNat (α := ℕ) n).map
    (sentenceBoolFromAtomList env.1 env.2)

private lemma formulaBoolHistory_getD
    (env : List ℕ × List Bool) {n k : ℕ} (hk : k < n) :
    ((List.range n).map (formulaBoolDecoded env)).getD k none =
      formulaBoolDecoded env k := by
  have hzero : formulaBoolDecoded env 0 = none := by
    simp [formulaBoolDecoded, LO.Propositional.Formula.ofNat]
  rw [← hzero, List.getD_map]
  simp [hk]

private lemma formulaBoolBinary_history (op : Bool → Bool → Bool)
    (env : List ℕ × List Bool) (payload n : ℕ)
    (hleft : payload.unpair.1 < n) (hright : payload.unpair.2 < n) :
    formulaBoolBinary op ((List.range n).map (formulaBoolDecoded env)) payload =
      ((LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1).bind fun φ =>
        (LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2).map fun ψ =>
          op (sentenceBoolFromAtomList env.1 env.2 φ)
            (sentenceBoolFromAtomList env.1 env.2 ψ)) := by
  unfold formulaBoolBinary
  rw [formulaBoolHistory_getD env hleft, formulaBoolHistory_getD env hright]
  cases hL : LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
    cases hR : LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
    simp [formulaBoolDecoded, hL, hR]

private lemma formulaBoolStep_history
    (env : List ℕ × List Bool) (n : ℕ) :
    formulaBoolStep env ((List.range n).map (formulaBoolDecoded env)) =
      formulaBoolDecoded env n := by
  cases n with
  | zero =>
      simp [formulaBoolStep, formulaBoolDecoded,
        LO.Propositional.Formula.ofNat]
  | succ e =>
      let tag := e.unpair.1
      let payload := e.unpair.2
      have hleft : payload.unpair.1 < e + 1 := by
        dsimp [payload]
        exact Nat.lt_succ_iff.mpr <|
          le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have hright : payload.unpair.2 < e + 1 := by
        dsimp [payload]
        exact Nat.lt_succ_iff.mpr <|
          le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      by_cases h0 : tag = 0
      · simp [formulaBoolStep, formulaBoolSucc, formulaBoolDecoded,
          LO.Propositional.Formula.ofNat, tag, h0,
          sentenceBoolFromAtomList, sentenceBool]
      by_cases h1 : tag = 1
      · simp [formulaBoolStep, formulaBoolSucc, formulaBoolDecoded,
          LO.Propositional.Formula.ofNat, tag, h1,
          sentenceBoolFromAtomList, sentenceBool]
      by_cases h2 : tag = 2
      · subst tag
        have hb := formulaBoolBinary_history (fun a b => !a || b)
          env payload (e + 1)
          hleft hright
        simp only [formulaBoolStep, List.length_map, List.length_range,
          formulaBoolSucc, h2, ↓reduceIte]
        rw [hb]
        simp only [formulaBoolDecoded, LO.Propositional.Formula.ofNat,
          h2]
        cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
          cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
          rfl
      by_cases h3 : tag = 3
      · subst tag
        have hb := formulaBoolBinary_history (· && ·) env payload (e + 1)
          hleft hright
        simp only [formulaBoolStep, List.length_map, List.length_range,
          formulaBoolSucc, h3, ↓reduceIte]
        rw [hb]
        simp only [formulaBoolDecoded, LO.Propositional.Formula.ofNat,
          h3]
        cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
          cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
          rfl
      by_cases h4 : tag = 4
      · subst tag
        have hb := formulaBoolBinary_history (· || ·) env payload (e + 1)
          hleft hright
        simp only [formulaBoolStep, List.length_map, List.length_range,
          formulaBoolSucc, h4, ↓reduceIte]
        rw [hb]
        simp only [formulaBoolDecoded, LO.Propositional.Formula.ofNat,
          h4]
        cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
          cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
          rfl
      · have htag : 5 ≤ tag := by omega
        simp [formulaBoolStep, formulaBoolSucc, formulaBoolDecoded,
          LO.Propositional.Formula.ofNat, tag, h0, h1, h2, h3, h4]

private lemma formulaBoolDecoded_prim : Primrec₂ formulaBoolDecoded := by
  have hstep : Primrec₂ fun (env : List ℕ × List Bool)
      (prior : List (Option Bool)) => some (formulaBoolStep env prior) :=
    Primrec₂.option_some_iff.mpr formulaBoolStep_prim
  exact Primrec.nat_strong_rec formulaBoolDecoded hstep
    (fun env n => by simpa using congrArg some (formulaBoolStep_history env n))

private lemma sentenceBoolFromAtomList_prim : Primrec fun p :
    (List ℕ × List Bool) × Sentence =>
      sentenceBoolFromAtomList p.1.1 p.1.2 p.2 := by
  have hdecoded : Primrec fun p : (List ℕ × List Bool) × Sentence =>
      formulaBoolDecoded p.1 (Encodable.encode p.2) :=
    formulaBoolDecoded_prim.comp Primrec.fst
      (Primrec.encode.comp Primrec.snd)
  have hget : Primrec fun o : Option Bool => o.getD false :=
    (Primrec.option_casesOn Primrec.id (Primrec.const false)
      Primrec₂.right).of_eq fun o => by cases o <;> rfl
  exact (hget.comp hdecoded).of_eq fun p => by
    rcases p with ⟨env, φ⟩
    rw [show Encodable.encode φ =
      LO.Propositional.Formula.toNat φ by rfl]
    simp [formulaBoolDecoded, LO.Propositional.Formula.ofNat_toNat]

private def tableConsistentFromAtomList
    (atoms : List ℕ) (xs : List Bool) (D : Finset Sentence) : Bool :=
  (supportSentenceList D).foldr (fun φ ok =>
    sentenceBoolFromAtomList atoms xs φ && ok) true

private lemma tableConsistentFromAtomList_prim : Primrec fun p :
    (List ℕ × List Bool) × Finset Sentence =>
      tableConsistentFromAtomList p.1.1 p.1.2 p.2 := by
  let P := (List ℕ × List Bool) × Finset Sentence
  have hsentences : Primrec fun p : P => supportSentenceList p.2 :=
    supportSentenceList_prim.comp Primrec.snd
  have heval : Primrec₂ fun (p : P) (φ : Sentence) =>
      sentenceBoolFromAtomList p.1.1 p.1.2 φ :=
    sentenceBoolFromAtomList_prim.to₂.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  have hstep : Primrec₂ fun (p : P) (q : Sentence × Bool) =>
      sentenceBoolFromAtomList p.1.1 p.1.2 q.1 && q.2 :=
    (Primrec.dom_bool₂ (· && ·)).comp₂
      (heval.comp₂ Primrec₂.left
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hsentences (Primrec.const true) hstep).of_eq
    fun p => by rfl

private lemma tableConsistentFromAtomList_sort_eq
    (A : Finset ℕ) (xs : List Bool) (D : Finset Sentence) :
    tableConsistentFromAtomList (A.sort (fun a b => a ≤ b)) xs D =
      tableConsistent (finiteAtomTableFromList A xs) D := by
  rw [← atomListTable_sort_eq A xs]
  have hfold : ∀ l : List Sentence,
      (l.foldr (fun φ ok =>
        sentenceBoolFromAtomList (A.sort fun a b => a ≤ b) xs φ && ok) true = true ↔
        ∀ φ ∈ l,
          sentenceBoolFromAtomList (A.sort fun a b => a ≤ b) xs φ = true) := by
    intro l
    induction l with
    | nil => simp
    | cons φ l ih => simp [ih]
  rw [Bool.eq_iff_iff]
  simp only [tableConsistentFromAtomList, tableConsistent,
    decide_eq_true_eq, hfold]
  simp [supportSentenceList, sentenceBoolFromAtomList]

private abbrev BudgetWorldContext :=
  List RationalBeliefState × (List ℕ × List Bool)

private def budgetWorldHistory (ctx : BudgetWorldContext)
    (day : ℕ) (φ : Sentence) : ℚ :=
  rationalHistory ctx.1 day φ

private def budgetWorldPayout (ctx : BudgetWorldContext)
    (φ : Sentence) : ℚ :=
  boolPayoutRat (atomListTable ctx.2.1 ctx.2.2) φ

private lemma budgetWorldHistory_prim : Primrec fun p :
    BudgetWorldContext × (ℕ × Sentence) =>
      budgetWorldHistory p.1 p.2.1 p.2.2 := by
  have hinput : Primrec fun p : BudgetWorldContext × (ℕ × Sentence) =>
      ((p.1.1, p.2.1), p.2.2) :=
    ((Primrec.fst.comp Primrec.fst).pair
      (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd)
  exact (rationalHistory_prim.comp hinput).of_eq fun p => by rfl

private lemma budgetWorldPayout_prim : Primrec fun p :
    BudgetWorldContext × Sentence => budgetWorldPayout p.1 p.2 := by
  have heval : Primrec fun p : BudgetWorldContext × Sentence =>
      sentenceBoolFromAtomList p.1.2.1 p.1.2.2 p.2 :=
    sentenceBoolFromAtomList_prim.comp
      (((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)
  exact (Primrec.cond heval (Primrec.const (1 : ℚ))
    (Primrec.const 0)).of_eq fun p => by
      cases h : sentenceBoolFromAtomList p.1.2.1 p.1.2.2 p.2 <;>
        simp only [sentenceBoolFromAtomList] at h <;>
        simp [budgetWorldPayout, boolPayoutRat, h]

private def firmDayMarketValueData
    (ctx : BudgetWorldContext) (j i : ℕ) : ℚ :=
  tradeListMarketValueRat ((firmRawTrader j).strat i).trades i
    (budgetWorldHistory ctx) (budgetWorldPayout ctx)

-- `Nat.sqrt` irreducible: see the module header.
attribute [local irreducible] Nat.sqrt in
private lemma firmDayMarketValueData_prim : Primrec fun p :
    (BudgetWorldContext × ℕ) × ℕ =>
      firmDayMarketValueData p.1.1 p.1.2 p.2 := by
  have htrades : Primrec fun p : (BudgetWorldContext × ℕ) × ℕ =>
      ((firmRawTrader p.1.2).strat p.2).trades :=
    firmRawTraderTrades_prim.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hsource : Primrec fun p : (BudgetWorldContext × ℕ) × ℕ =>
      ((p.1.1, p.2), ((firmRawTrader p.1.2).strat p.2).trades) :=
    ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair htrades
  exact ((tradeListMarketValueRat_prim budgetWorldHistory budgetWorldPayout
    budgetWorldHistory_prim budgetWorldPayout_prim).comp hsource).of_eq
      fun p => by rfl

private def firmRawPriorWorthData
    (ctx : BudgetWorldContext) (j n : ℕ) : ℚ :=
  ((List.range n).map fun i => firmDayMarketValueData ctx j i).sum

-- `Nat.sqrt` irreducible: see the module header.
attribute [local irreducible] Nat.sqrt in
private lemma firmRawPriorWorthData_prim : Primrec fun p :
    (BudgetWorldContext × ℕ) × ℕ =>
      firmRawPriorWorthData p.1.1 p.1.2 p.2 := by
  let P := (BudgetWorldContext × ℕ) × ℕ
  have hrange : Primrec fun p : P => List.range p.2 :=
    Primrec.list_range.comp Primrec.snd
  have hday : Primrec₂ fun (p : P) (i : ℕ) =>
      firmDayMarketValueData p.1.1 p.1.2 i :=
    firmDayMarketValueData_prim.to₂.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  have hvalues : Primrec fun p : P =>
      (List.range p.2).map fun i => firmDayMarketValueData p.1.1 p.1.2 i :=
    Primrec.list_map hrange hday
  have hstep : Primrec₂ fun (_p : P) (q : ℚ × ℚ) => q.1 + q.2 :=
    ratAdd_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hvalues (Primrec.const 0) hstep).of_eq
    fun p => by rfl

private lemma firmRawPriorWorthData_eq
    (past : List RationalBeliefState) (atoms : List ℕ) (xs : List Bool)
    (j n : ℕ) :
    firmRawPriorWorthData (past, atoms, xs) j n =
      rawPriorWorthRatTradeLists
        (fun i => ((firmRawTrader j).strat i).trades)
        (rationalHistory past) (atomListTable atoms xs) n := by
  unfold firmRawPriorWorthData rawPriorWorthRatTradeLists
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.sum_range_succ, Finset.sum_range_succ, ih]
      rfl

private lemma natCastRat_prim : Primrec fun n : ℕ => (n : ℚ) := by
  exact (ratMk_prim.comp (intOfNat_prim.comp Primrec.id)
    (Primrec.const 1)).of_eq fun n => by
      rw [Rat.mkRat_eq_divInt]
      simp

private abbrev BudgetCoreInput :=
  (((List (Finset Sentence) × List RationalBeliefState) × ℕ) × ℕ) × ℕ

private def budgetConsistentAtDayData
    (atoms : List ℕ) (xs : List Bool)
    (stages : List (Finset Sentence)) (m : ℕ) : Bool :=
  tableConsistentFromAtomList atoms xs (decodedStageTable stages m)

private lemma budgetConsistentAtDayData_prim : Primrec fun p :
    ((List ℕ × List Bool) × List (Finset Sentence)) × ℕ =>
      budgetConsistentAtDayData p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  have hstage : Primrec fun p :
      ((List ℕ × List Bool) × List (Finset Sentence)) × ℕ =>
        decodedStageTable p.1.2 p.2 :=
    decodedStageTable_prim.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact (tableConsistentFromAtomList_prim.comp
    (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair hstage)).of_eq
        fun p => by rfl

private def budgetWorthBreachedData
    (ctx : BudgetWorldContext) (j b m : ℕ) : Bool :=
  decide (firmRawPriorWorthData ctx j (m + 1) ≤ -(b : ℚ))

-- `Nat.sqrt` irreducible: see the module header.
attribute [local irreducible] Nat.sqrt in
private lemma budgetWorthBreachedData_prim : Primrec fun p :
    ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      budgetWorthBreachedData p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  have hctx : Primrec fun p : ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      p.1.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hj : Primrec fun p : ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      p.1.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hb : Primrec fun p : ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      p.1.2 := Primrec.snd.comp Primrec.fst
  have hm : Primrec fun p : ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      p.2 := Primrec.snd
  have hworth : Primrec fun p : ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      firmRawPriorWorthData p.1.1.1 p.1.1.2 (p.2 + 1) :=
    firmRawPriorWorthData_prim.comp
      ((hctx.pair hj).pair (Primrec.nat_add.comp hm (Primrec.const 1)))
  have hnegBudget : Primrec fun p : ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      -((p.1.2 : ℕ) : ℚ) :=
    ratNeg_prim.comp (natCastRat_prim.comp hb)
  exact ((ratLE_prim.comp hworth hnegBudget).decide).of_eq fun p => by
    rfl

private def firmBudgetBreachAtDayData
    (core : BudgetCoreInput) (xs : List Bool) (m : ℕ) : Bool :=
  budgetConsistentAtDayData
      (budgetAtomList core.1.1.1.1 core.1.1.2 core.2) xs core.1.1.1.1 m &&
    budgetWorthBreachedData
      (core.1.1.1.2, budgetAtomList core.1.1.1.1 core.1.1.2 core.2, xs)
      core.1.1.2 core.1.2 m

-- The closing `exact` below has to check `firmBudgetBreachAtDayData p.1.1 p.1.2 p.2`
-- defeq against the composed Boolean; without the overrides that check unfolds the
-- rational `decide` and `budgetAtomList` leaves eagerly and exhausts the heartbeat budget.
section
-- Scoped so the reducibility overrides do not leak to later declarations.
-- `Nat.sqrt` irreducible: see the module header.  The budget leaves are blocked so the
-- instances and leaves match structurally instead of by reduction.
attribute [local irreducible] Nat.sqrt budgetConsistentAtDayData budgetWorthBreachedData
  budgetAtomList firmRawPriorWorthData decodedStageTable tableConsistentFromAtomList

private lemma firmBudgetBreachAtDayData_prim : Primrec fun p :
    (BudgetCoreInput × List Bool) × ℕ =>
      firmBudgetBreachAtDayData p.1.1 p.1.2 p.2 := by
  let P := (BudgetCoreInput × List Bool) × ℕ
  have hstages : Primrec fun p : P => p.1.1.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have hpast : Primrec fun p : P => p.1.1.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have hj : Primrec fun p : P => p.1.1.1.1.2 :=
    Primrec.snd.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hb : Primrec fun p : P => p.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hn : Primrec fun p : P => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hxs : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hm : Primrec fun p : P => p.2 := Primrec.snd
  have hatoms : Primrec fun p : P =>
      budgetAtomList p.1.1.1.1.1.1 p.1.1.1.1.2 p.1.1.2 :=
    budgetAtomList_prim.comp ((hstages.pair hj).pair hn)
  have hconsistent : Primrec fun p : P =>
      budgetConsistentAtDayData
        (budgetAtomList p.1.1.1.1.1.1 p.1.1.1.1.2 p.1.1.2)
        p.1.2 p.1.1.1.1.1.1 p.2 :=
    budgetConsistentAtDayData_prim.comp
      (((hatoms.pair hxs).pair hstages).pair hm)
  have hctx : Primrec fun p : P =>
      ((p.1.1.1.1.1.2,
          budgetAtomList p.1.1.1.1.1.1 p.1.1.1.1.2 p.1.1.2,
          p.1.2) : BudgetWorldContext) :=
    hpast.pair (hatoms.pair hxs)
  have hbreach : Primrec fun p : P =>
      budgetWorthBreachedData
        (p.1.1.1.1.1.2,
          budgetAtomList p.1.1.1.1.1.1 p.1.1.1.1.2 p.1.1.2,
          p.1.2)
        p.1.1.1.1.2 p.1.1.1.2 p.2 :=
    budgetWorthBreachedData_prim.comp
      (((hctx.pair hj).pair hb).pair hm)
  exact (Primrec.dom_bool₂ (· && ·)).comp hconsistent hbreach

end

/-! ## Exact compiler for the TradingFirm cutoff

The firm cutoff uses `EF.absBound`, whose operations differ slightly from ordinary
rational denotation.  We reuse the verified rational machine's command format and
continuation discipline, changing only constants, prices, `max`, and `safeRecip`. -/

private lemma ratAbs_prim : Primrec fun q : ℚ => |q| := by
  exact (ratMax_prim.comp Primrec.id (ratNeg_prim.comp Primrec.id)).of_eq
    fun q => by simp [abs_eq_max_neg]

private def efBoundRawStep
    (p : ℕ × (List ℚ × EFRatMachineState)) : EFRatMachineState :=
  let code := p.1
  let rho := p.2.1
  let state := p.2.2
  let tag := code.unpair.1
  let payload := code.unpair.2
  if tag = 0 then
    (state.1, |(Encodable.decode (α := ℚ) payload).getD 0| :: state.2)
  else if tag = 1 then
    (state.1, (1 : ℚ) :: state.2)
  else if tag = 4 then
    efRatRawStep (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => 0)
      ((), Nat.pair 2 payload, rho, state)
  else
    efRatRawStep (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => 0)
      ((), code, rho, state)

private lemma efBoundRawStep_prim : Primrec efBoundRawStep := by
  let P := ℕ × (List ℚ × EFRatMachineState)
  have hcode : Primrec fun p : P => p.1 := Primrec.fst
  have hrho : Primrec fun p : P => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hstate : Primrec fun p : P => p.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hcommands : Primrec fun p : P => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hvalues : Primrec fun p : P => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have htag : Primrec fun p : P => p.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hcode)
  have hpayload : Primrec fun p : P => p.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hcode)
  have hzeroQuote : Primrec fun
      _p : Unit × (ℕ × Sentence) => (0 : ℚ) := Primrec.const 0
  have hraw := efRatRawStep_prim
    (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => (0 : ℚ)) hzeroQuote
  have hdefaultArg : Primrec fun p : P =>
      ((), (p.1, (p.2.1, p.2.2))) :=
    (Primrec.const ()).pair (hcode.pair (hrho.pair hstate))
  have hdefault : Primrec fun p : P =>
      efRatRawStep (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => 0)
        ((), p.1, p.2.1, p.2.2) :=
    hraw.comp hdefaultArg
  have hmaxCode : Primrec fun p : P => Nat.pair 2 p.1.unpair.2 :=
    Primrec₂.natPair.comp (Primrec.const 2) hpayload
  have hmaxArg : Primrec fun p : P =>
      ((), (Nat.pair 2 p.1.unpair.2, (p.2.1, p.2.2))) :=
    (Primrec.const ()).pair (hmaxCode.pair (hrho.pair hstate))
  have hmax : Primrec fun p : P =>
      efRatRawStep (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => 0)
        ((), Nat.pair 2 p.1.unpair.2, p.2.1, p.2.2) :=
    hraw.comp hmaxArg
  have hdecoded : Primrec fun p : P =>
      (Encodable.decode (α := ℚ) p.1.unpair.2).getD 0 :=
    Primrec.option_getD.comp
      ((Primrec.decode : Primrec fun n : ℕ => Encodable.decode (α := ℚ) n).comp
        hpayload)
      (Primrec.const 0)
  have hcase0 : Primrec fun p : P =>
      (p.2.2.1, |(Encodable.decode (α := ℚ) p.1.unpair.2).getD 0| ::
        p.2.2.2) :=
    hcommands.pair (Primrec.list_cons.comp
      (ratAbs_prim.comp hdecoded) hvalues)
  have hcase1 : Primrec fun p : P =>
      (p.2.2.1, (1 : ℚ) :: p.2.2.2) :=
    hcommands.pair (Primrec.list_cons.comp (Primrec.const 1) hvalues)
  have htagEq (k : ℕ) : PrimrecPred fun p : P => p.1.unpair.1 = k :=
    Primrec.eq.comp htag (Primrec.const k)
  exact (Primrec.ite (htagEq 0) hcase0
    (Primrec.ite (htagEq 1) hcase1
      (Primrec.ite (htagEq 4) hmax hdefault))).of_eq fun p => by
        simp only [efBoundRawStep]

private def efBoundCommandStep
    (p : EFRatCommand × EFRatMachineState) : EFRatMachineState :=
  let kind := p.1.1
  let payload := p.1.2.1
  let rho := p.1.2.2
  let state := p.2
  if kind = 0 then efBoundRawStep (payload, rho, state)
  else if kind = 4 then efRatUnaryValueStep (fun _ => (1 : ℚ)) state
  else efRatCommandStep (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => 0)
    ((), p.1, state)

private lemma efBoundCommandStep_prim : Primrec efBoundCommandStep := by
  let P := EFRatCommand × EFRatMachineState
  have hkind : Primrec fun p : P => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hpayload : Primrec fun p : P => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hrho : Primrec fun p : P => p.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hstate : Primrec fun p : P => p.2 := Primrec.snd
  have hcase0 : Primrec fun p : P =>
      efBoundRawStep (p.1.2.1, p.1.2.2, p.2) :=
    efBoundRawStep_prim.comp (hpayload.pair (hrho.pair hstate))
  have hcase4 : Primrec fun p : P =>
      efRatUnaryValueStep (fun _ => (1 : ℚ)) p.2 :=
    (efRatUnaryValueStep_prim (fun _ => (1 : ℚ))
      (Primrec.const 1)).comp hstate
  have hzeroQuote : Primrec fun
      _p : Unit × (ℕ × Sentence) => (0 : ℚ) := Primrec.const 0
  have hdefaultArg : Primrec fun p : P => ((), (p.1, p.2)) :=
    (Primrec.const ()).pair (Primrec.fst.pair Primrec.snd)
  have hdefault : Primrec fun p : P =>
      efRatCommandStep (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => 0)
        ((), p.1, p.2) :=
    (efRatCommandStep_prim
      (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => (0 : ℚ))
      hzeroQuote).comp hdefaultArg
  have hkindEq (k : ℕ) : PrimrecPred fun p : P => p.1.1 = k :=
    Primrec.eq.comp hkind (Primrec.const k)
  exact (Primrec.ite (hkindEq 0) hcase0
    (Primrec.ite (hkindEq 4) hcase4 hdefault)).of_eq fun p => by
      simp only [efBoundCommandStep]

private def efBoundMachineStep : EFRatMachineState → EFRatMachineState
  | ([], values) => ([], values)
  | (command :: commands, values) =>
      efBoundCommandStep (command, commands, values)

private lemma efBoundMachineStep_prim : Primrec efBoundMachineStep := by
  have hcommands : Primrec fun state : EFRatMachineState => state.1 :=
    Primrec.fst
  have hcons : Primrec₂ fun (state : EFRatMachineState)
      (cr : EFRatCommand × List EFRatCommand) =>
      efBoundCommandStep (cr.1, cr.2, state.2) := by
    have harg : Primrec fun z :
        EFRatMachineState × (EFRatCommand × List EFRatCommand) =>
        (z.2.1, (z.2.2, z.1.2)) :=
      (Primrec.fst.comp Primrec.snd).pair
        ((Primrec.snd.comp Primrec.snd).pair
          (Primrec.snd.comp Primrec.fst))
    exact (efBoundCommandStep_prim.comp harg).to₂
  exact (Primrec.list_casesOn hcommands Primrec.id hcons).of_eq fun state => by
    rcases state with ⟨commands, values⟩
    cases commands <;> rfl

private lemma efBoundMachineStep_add (a b : EF) (rho : List ℚ)
    (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep
        (efRatEvalCommand (EF.add a b) rho :: commands, values) =
      (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
        efRatOpCommand 1 :: commands, values) := by
  simp [efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
    efRatRawStep, efRatEvalCommand, efRatRawEvalCommand,
    EF.toNat]

private lemma efBoundMachineStep_mul (a b : EF) (rho : List ℚ)
    (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep
        (efRatEvalCommand (EF.mul a b) rho :: commands, values) =
      (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
        efRatOpCommand 2 :: commands, values) := by
  simp [efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
    efRatRawStep, efRatEvalCommand, efRatRawEvalCommand,
    EF.toNat]

private lemma efBoundMachineStep_max (a b : EF) (rho : List ℚ)
    (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep
        (efRatEvalCommand (EF.max a b) rho :: commands, values) =
      (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
        efRatOpCommand 1 :: commands, values) := by
  simp [efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
    efRatRawStep, efRatEvalCommand, efRatRawEvalCommand,
    EF.toNat]

private lemma efBoundMachineStep_safeRecip (a : EF) (rho : List ℚ)
    (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep
        (efRatEvalCommand (EF.safeRecip a) rho :: commands, values) =
      (efRatEvalCommand a rho :: efRatOpCommand 4 :: commands, values) := by
  simp [efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
    efRatRawStep, efRatEvalCommand, efRatRawEvalCommand,
    EF.toNat]

private lemma efBoundMachineStep_letE (x body : EF) (rho : List ℚ)
    (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep
        (efRatEvalCommand (EF.letE x body) rho :: commands, values) =
      (efRatEvalCommand x rho :: efRatLetBodyCommand body.toNat rho :: commands,
        values) := by
  simp [efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
    efRatRawStep, efRatEvalCommand, efRatRawEvalCommand,
    EF.toNat]

private lemma efBoundMachineStep_letBody (payload : ℕ) (rho : List ℚ)
    (q : ℚ) (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep
        (efRatLetBodyCommand payload rho :: commands, q :: values) =
      (efRatRawEvalCommand payload (q :: rho) :: commands, values) := by
  simp [efBoundMachineStep, efBoundCommandStep, efRatCommandStep,
    efRatLetBodyCommand, efRatLetValueStep]

private lemma efBoundMachine_correct (e : EF) (rho : List ℚ)
    (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep^[efRatMachineSteps e]
        (efRatEvalCommand e rho :: commands, values) =
      (commands, e.absBoundWith (rho.getD · 0) :: values) := by
  induction e generalizing rho commands values with
  | price φ day =>
      simp [efRatMachineSteps, efRatEvalCommand, efRatRawEvalCommand,
        efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
        EF.toNat, EF.absBoundWith]
  | const q =>
      simp [efRatMachineSteps, efRatEvalCommand, efRatRawEvalCommand,
        efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
        EF.toNat, EF.absBoundWith, Encodable.encodek]
  | var i =>
      simp [efRatMachineSteps, efRatEvalCommand, efRatRawEvalCommand,
        efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
        efRatRawStep, EF.toNat, EF.absBoundWith]
  | add a b iha ihb =>
      let f := efBoundMachineStep
      rw [show efRatMachineSteps (EF.add a b) =
          1 + efRatMachineSteps a + efRatMachineSteps b + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + efRatMachineSteps b + 1 =
          1 + (efRatMachineSteps a + efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + efRatMachineSteps b + 1]
          (f (efRatEvalCommand (EF.add a b) rho :: commands, values)) = _
      rw [show f (efRatEvalCommand (EF.add a b) rho :: commands, values) =
          (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
            efRatOpCommand 1 :: commands, values) by
        exact efBoundMachineStep_add a b rho commands values]
      rw [show efRatMachineSteps a + efRatMachineSteps b + 1 =
          efRatMachineSteps a + (efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f (efRatMachineSteps a)]
      rw [show f^[efRatMachineSteps a]
          (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
            efRatOpCommand 1 :: commands, values) =
          (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          iha rho (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands) values]
      rw [iterate_add_forward f (efRatMachineSteps b) 1]
      rw [show f^[efRatMachineSteps b]
          (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) =
          (efRatOpCommand 1 :: commands,
            b.absBoundWith (rho.getD · 0) ::
              a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          ihb rho (efRatOpCommand 1 :: commands)
            (a.absBoundWith (rho.getD · 0) :: values)]
      simp [f, efBoundMachineStep, efBoundCommandStep, efRatCommandStep,
        efRatOpCommand, efRatBinaryValueStep, EF.absBoundWith]
  | mul a b iha ihb =>
      let f := efBoundMachineStep
      rw [show efRatMachineSteps (EF.mul a b) =
          1 + efRatMachineSteps a + efRatMachineSteps b + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + efRatMachineSteps b + 1 =
          1 + (efRatMachineSteps a + efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + efRatMachineSteps b + 1]
          (f (efRatEvalCommand (EF.mul a b) rho :: commands, values)) = _
      rw [show f (efRatEvalCommand (EF.mul a b) rho :: commands, values) =
          (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
            efRatOpCommand 2 :: commands, values) by
        exact efBoundMachineStep_mul a b rho commands values]
      rw [show efRatMachineSteps a + efRatMachineSteps b + 1 =
          efRatMachineSteps a + (efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f (efRatMachineSteps a)]
      rw [show f^[efRatMachineSteps a]
          (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
            efRatOpCommand 2 :: commands, values) =
          (efRatEvalCommand b rho :: efRatOpCommand 2 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          iha rho (efRatEvalCommand b rho :: efRatOpCommand 2 :: commands) values]
      rw [iterate_add_forward f (efRatMachineSteps b) 1]
      rw [show f^[efRatMachineSteps b]
          (efRatEvalCommand b rho :: efRatOpCommand 2 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) =
          (efRatOpCommand 2 :: commands,
            b.absBoundWith (rho.getD · 0) ::
              a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          ihb rho (efRatOpCommand 2 :: commands)
            (a.absBoundWith (rho.getD · 0) :: values)]
      simp [f, efBoundMachineStep, efBoundCommandStep, efRatCommandStep,
        efRatOpCommand, efRatBinaryValueStep, EF.absBoundWith]
  | max a b iha ihb =>
      let f := efBoundMachineStep
      rw [show efRatMachineSteps (EF.max a b) =
          1 + efRatMachineSteps a + efRatMachineSteps b + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + efRatMachineSteps b + 1 =
          1 + (efRatMachineSteps a + efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + efRatMachineSteps b + 1]
          (f (efRatEvalCommand (EF.max a b) rho :: commands, values)) = _
      rw [show f (efRatEvalCommand (EF.max a b) rho :: commands, values) =
          (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
            efRatOpCommand 1 :: commands, values) by
        exact efBoundMachineStep_max a b rho commands values]
      rw [show efRatMachineSteps a + efRatMachineSteps b + 1 =
          efRatMachineSteps a + (efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f (efRatMachineSteps a)]
      rw [show f^[efRatMachineSteps a]
          (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
            efRatOpCommand 1 :: commands, values) =
          (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          iha rho (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands) values]
      rw [iterate_add_forward f (efRatMachineSteps b) 1]
      rw [show f^[efRatMachineSteps b]
          (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) =
          (efRatOpCommand 1 :: commands,
            b.absBoundWith (rho.getD · 0) ::
              a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          ihb rho (efRatOpCommand 1 :: commands)
            (a.absBoundWith (rho.getD · 0) :: values)]
      simp [f, efBoundMachineStep, efBoundCommandStep, efRatCommandStep,
        efRatOpCommand, efRatBinaryValueStep, EF.absBoundWith]
  | safeRecip a iha =>
      let f := efBoundMachineStep
      rw [show efRatMachineSteps (EF.safeRecip a) =
          1 + efRatMachineSteps a + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + 1 =
          1 + (efRatMachineSteps a + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + 1]
          (f (efRatEvalCommand (EF.safeRecip a) rho :: commands, values)) = _
      rw [show f (efRatEvalCommand (EF.safeRecip a) rho :: commands, values) =
          (efRatEvalCommand a rho :: efRatOpCommand 4 :: commands, values) by
        exact efBoundMachineStep_safeRecip a rho commands values]
      rw [iterate_add_forward f (efRatMachineSteps a) 1]
      rw [show f^[efRatMachineSteps a]
          (efRatEvalCommand a rho :: efRatOpCommand 4 :: commands, values) =
          (efRatOpCommand 4 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          iha rho (efRatOpCommand 4 :: commands) values]
      simp [f, efBoundMachineStep, efBoundCommandStep,
        efRatOpCommand, efRatUnaryValueStep, EF.absBoundWith]
  | letE x body ihx ihbody =>
      let f := efBoundMachineStep
      rw [show efRatMachineSteps (EF.letE x body) =
          1 + efRatMachineSteps x + 1 + efRatMachineSteps body by
        simp [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps x + 1 + efRatMachineSteps body =
          1 + (efRatMachineSteps x + 1 + efRatMachineSteps body) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps x + 1 + efRatMachineSteps body]
          (f (efRatEvalCommand (EF.letE x body) rho :: commands, values)) = _
      rw [show f (efRatEvalCommand (EF.letE x body) rho :: commands, values) =
          (efRatEvalCommand x rho :: efRatLetBodyCommand body.toNat rho :: commands,
            values) by
        exact efBoundMachineStep_letE x body rho commands values]
      rw [show efRatMachineSteps x + 1 + efRatMachineSteps body =
          efRatMachineSteps x + (1 + efRatMachineSteps body) by omega]
      rw [iterate_add_forward f (efRatMachineSteps x)]
      rw [show f^[efRatMachineSteps x]
          (efRatEvalCommand x rho :: efRatLetBodyCommand body.toNat rho :: commands,
            values) =
          (efRatLetBodyCommand body.toNat rho :: commands,
            x.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand, efRatRawEvalCommand] using
          ihx rho (efRatLetBodyCommand body.toNat rho :: commands) values]
      rw [iterate_add_forward f 1 (efRatMachineSteps body)]
      simp only [Function.iterate_one]
      rw [show f
          (efRatLetBodyCommand body.toNat rho :: commands,
            x.absBoundWith (rho.getD · 0) :: values) =
          (efRatRawEvalCommand body.toNat
            (x.absBoundWith (rho.getD · 0) :: rho) :: commands, values) by
        exact efBoundMachineStep_letBody body.toNat rho
          (x.absBoundWith (rho.getD · 0)) commands values]
      rw [show efBoundMachineStep^[efRatMachineSteps body]
          (efRatRawEvalCommand body.toNat
              (x.absBoundWith (rho.getD · 0) :: rho) :: commands, values) =
          (commands, body.absBoundWith
            ((x.absBoundWith (rho.getD · 0) :: rho).getD · 0) :: values) by
        simpa only [efRatEvalCommand] using
          ihbody (x.absBoundWith (rho.getD · 0) :: rho) commands values]
      congr 2
      apply congrArg body.absBoundWith
      funext i
      cases i <;> rfl

private lemma efBoundMachine_terminal (values : List ℚ) :
    efBoundMachineStep ([], values) = ([], values) := rfl

private lemma efBoundMachine_fuel_correct (e : EF) :
    efBoundMachineStep^[efRatMachineFuel e]
        ([efRatEvalCommand e []], []) = ([], [e.absBound]) := by
  obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le
    (efRatMachineSteps_le_fuel e)
  rw [hextra, iterate_add_forward]
  rw [show efBoundMachineStep^[efRatMachineSteps e]
      ([efRatEvalCommand e []], []) = ([], [e.absBound]) by
    simpa [EF.absBound] using efBoundMachine_correct e [] [] []]
  exact Function.iterate_fixed (efBoundMachine_terminal [e.absBound]) extra

private def efCompiledAbsBound (e : EF) : ℚ :=
  ((efBoundMachineStep^[efRatMachineFuel e]
    ([efRatEvalCommand e []], [])).2).getD 0 0

private lemma efCompiledAbsBound_eq (e : EF) :
    efCompiledAbsBound e = e.absBound := by
  rw [efCompiledAbsBound, efBoundMachine_fuel_correct]
  rfl

private lemma efCompiledAbsBound_prim : Primrec efCompiledAbsBound := by
  have hcode : Primrec fun e : EF => e.toNat := by
    exact Primrec.encode.of_eq fun e => rfl
  have hfuel : Primrec fun e : EF => efRatMachineFuel e := by
    have hsucc : Primrec fun e : EF => e.toNat + 1 :=
      Primrec.nat_add.comp hcode (Primrec.const 1)
    exact (Primrec.nat_mul.comp (Primrec.const 2) hsucc).of_eq fun e => by
      rfl
  have hcommand : Primrec fun e : EF => efRatEvalCommand e [] :=
    (Primrec.const 0).pair (hcode.pair (Primrec.const []))
  have hcommands : Primrec fun e : EF => [efRatEvalCommand e []] :=
    Primrec.list_cons.comp hcommand (Primrec.const [])
  have hinit : Primrec fun e : EF =>
      (([efRatEvalCommand e []], []) : EFRatMachineState) :=
    hcommands.pair (Primrec.const [])
  have hstep : Primrec₂ fun (_e : EF) (state : EFRatMachineState) =>
      efBoundMachineStep state :=
    efBoundMachineStep_prim.comp₂ Primrec₂.right
  have hrun : Primrec fun e : EF =>
      efBoundMachineStep^[efRatMachineFuel e]
        ([efRatEvalCommand e []], []) :=
    Primrec.nat_iterate hfuel hinit hstep
  exact (Primrec.list_getD 0).comp (Primrec.snd.comp hrun)
    (Primrec.const 0)

private lemma efAbsBound_prim : Primrec EF.absBound :=
  efCompiledAbsBound_prim.of_eq efCompiledAbsBound_eq

private lemma tradeListAbsBound_prim :
    Primrec Strategy.tradeListAbsBound := by
  have hbounds : Primrec fun trades : List (EF × Sentence) =>
      trades.map fun trade => trade.1.absBound :=
    Primrec.list_map Primrec.id
      (efAbsBound_prim.comp₂ (Primrec.fst.comp₂ Primrec₂.right))
  have hstep : Primrec₂ fun (_trades : List (EF × Sentence))
      (p : ℚ × ℚ) => p.1 + p.2 :=
    ratAdd_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hbounds (Primrec.const 0) hstep).of_eq
    fun trades => by rfl

private def firmDayAbsBoundData (j i : ℕ) : ℚ :=
  Strategy.tradeListAbsBound ((firmRawTrader j).strat i).trades

private lemma firmDayAbsBoundData_prim :
    Primrec₂ firmDayAbsBoundData := by
  exact (tradeListAbsBound_prim.comp
    (firmRawTraderTrades_prim.comp Primrec.fst Primrec.snd)).to₂

private def firmPrefixTotalBoundData (n j : ℕ) : ℚ :=
  ((List.range (n + 1)).map fun i => firmDayAbsBoundData j i).sum

private lemma firmPrefixTotalBoundData_prim :
    Primrec₂ firmPrefixTotalBoundData := by
  let P := ℕ × ℕ
  have hrange : Primrec fun p : P => List.range (p.1 + 1) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))
  have hday : Primrec₂ fun (p : P) (i : ℕ) =>
      firmDayAbsBoundData p.2 i :=
    firmDayAbsBoundData_prim.comp₂
      (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right
  have hvalues : Primrec fun p : P =>
      (List.range (p.1 + 1)).map fun i => firmDayAbsBoundData p.2 i :=
    Primrec.list_map hrange hday
  have hstep : Primrec₂ fun (_p : P) (q : ℚ × ℚ) => q.1 + q.2 :=
    ratAdd_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hvalues (Primrec.const 0) hstep).to₂.of_eq
    fun n j => by rfl

private lemma firmPrefixTotalBoundData_eq (n j : ℕ) :
    firmPrefixTotalBoundData n j =
      ∑ i ∈ Finset.range (n + 1),
        Strategy.tradeListAbsBound ((firmRawTrader j).strat i).trades := by
  unfold firmPrefixTotalBoundData firmDayAbsBoundData
  have hsum : ∀ k : ℕ,
      ((List.range k).map fun i =>
        Strategy.tradeListAbsBound ((firmRawTrader j).strat i).trades).sum =
      ∑ i ∈ Finset.range k,
        Strategy.tradeListAbsBound ((firmRawTrader j).strat i).trades := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.sum_range_succ, Finset.sum_range_succ, ih]
  exact hsum (n + 1)

private def firmTotalBoundData (n : ℕ) : ℚ :=
  ((List.range (n + 1)).map fun j => firmPrefixTotalBoundData n j).sum

private lemma firmTotalBoundData_prim : Primrec firmTotalBoundData := by
  have hrange : Primrec fun n : ℕ => List.range (n + 1) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
  have hvalue : Primrec₂ fun (n j : ℕ) => firmPrefixTotalBoundData n j :=
    firmPrefixTotalBoundData_prim
  have hvalues : Primrec fun n : ℕ =>
      (List.range (n + 1)).map fun j => firmPrefixTotalBoundData n j :=
    Primrec.list_map hrange hvalue
  have hstep : Primrec₂ fun (_n : ℕ) (q : ℚ × ℚ) => q.1 + q.2 :=
    ratAdd_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hvalues (Primrec.const 0) hstep).of_eq
    fun n => by rfl

private lemma firmTotalBoundData_eq (n : ℕ) :
    firmTotalBoundData n = tradingFirmTotalBoundTradeLists n := by
  unfold firmTotalBoundData tradingFirmTotalBoundTradeLists
  have hsum : ∀ k : ℕ,
      ((List.range k).map fun j => firmPrefixTotalBoundData n j).sum =
      ∑ j ∈ Finset.range k,
        ∑ i ∈ Finset.range (n + 1),
          Strategy.tradeListAbsBound ((firmRawTrader j).strat i).trades := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.sum_range_succ, Finset.sum_range_succ, ih,
          firmPrefixTotalBoundData_eq]
  exact hsum (n + 1)

private def ratNatCeilData (q : ℚ) : ℕ :=
  (-((-q.num) / (q.den : ℤ))).natAbs

private lemma ratNatCeilData_prim : Primrec ratNatCeilData := by
  exact (intNatAbs_prim.comp
    (intNeg_prim.comp
      (intDivNat_prim.comp (intNeg_prim.comp ratNum_prim)
        ratDen_prim))).of_eq fun q => by rfl

private lemma ratNatCeilData_eq (q : ℚ) (hq : 0 ≤ q) :
    ratNatCeilData q = ⌈q⌉₊ := by
  have hceil : (0 : ℤ) ≤ ⌈q⌉ := Int.ceil_nonneg hq
  change (-((-q.num) / (q.den : ℤ))).natAbs = Int.toNat ⌈q⌉
  rw [← Rat.ceil_def']
  apply Int.ofNat_inj.mp
  rw [Int.natAbs_of_nonneg hceil, Int.toNat_of_nonneg hceil]

private lemma tradingFirmTotalBoundTradeLists_prim :
    Primrec tradingFirmTotalBoundTradeLists :=
  firmTotalBoundData_prim.of_eq firmTotalBoundData_eq

private lemma tradingFirmCutoffTradeLists_prim :
    Primrec tradingFirmCutoffTradeLists := by
  have hcompiled : Primrec fun n =>
      ratNatCeilData (tradingFirmTotalBoundTradeLists n) + 1 :=
    Primrec.nat_add.comp
      (ratNatCeilData_prim.comp tradingFirmTotalBoundTradeLists_prim)
      (Primrec.const 1)
  exact hcompiled.of_eq fun n => by
    unfold tradingFirmCutoffTradeLists
    rw [ratNatCeilData_eq]
    simpa using tradingFirmTotalBound_nonneg n

private def firmBudgetAssignmentBreachesData
    (core : BudgetCoreInput) (xs : List Bool) : Bool :=
  (List.range core.2).any fun m => firmBudgetBreachAtDayData core xs m

private lemma firmBudgetAssignmentBreachesData_prim : Primrec fun p :
    BudgetCoreInput × List Bool =>
      firmBudgetAssignmentBreachesData p.1 p.2 := by
  let P := BudgetCoreInput × List Bool
  have hrange : Primrec fun p : P => List.range p.1.2 :=
    Primrec.list_range.comp (Primrec.snd.comp Primrec.fst)
  have hday : Primrec₂ fun (p : P) (m : ℕ) =>
      firmBudgetBreachAtDayData p.1 p.2 m :=
    firmBudgetBreachAtDayData_prim.to₂.comp₂
      Primrec₂.left Primrec₂.right
  have hstep : Primrec₂ fun (p : P) (q : ℕ × Bool) =>
      firmBudgetBreachAtDayData p.1 p.2 q.1 || q.2 :=
    (Primrec.dom_bool₂ (· || ·)).comp₂
      (hday.comp₂ Primrec₂.left
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hrange (Primrec.const false) hstep).of_eq
    fun p => by
      unfold firmBudgetAssignmentBreachesData
      induction List.range p.1.2 with
      | nil => rfl
      | cons m ms ih => simp [List.any, ih]

private def priorBudgetBreachData (core : BudgetCoreInput) : Bool :=
  let atoms := budgetAtomList core.1.1.1.1 core.1.1.2 core.2
  (allBoolLists atoms.length).any fun xs =>
    firmBudgetAssignmentBreachesData core xs

-- Raised budget: this proof threads `Primrec` certificates through the whole nested
-- `BudgetCoreInput` product and the `allBoolLists` search, and exceeds the default at the
-- final composition.
set_option maxHeartbeats 1600000 in
private lemma priorBudgetBreachData_prim : Primrec priorBudgetBreachData := by
  have hstages : Primrec fun core : BudgetCoreInput => core.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hj : Primrec fun core : BudgetCoreInput => core.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun core : BudgetCoreInput => core.2 := Primrec.snd
  have hatoms : Primrec fun core : BudgetCoreInput =>
      budgetAtomList core.1.1.1.1 core.1.1.2 core.2 :=
    budgetAtomList_prim.comp ((hstages.pair hj).pair hn)
  have hassignments : Primrec fun core : BudgetCoreInput =>
      allBoolLists (budgetAtomList core.1.1.1.1 core.1.1.2 core.2).length :=
    allBoolLists_prim.comp (Primrec.list_length.comp hatoms)
  have hassignment : Primrec₂ fun (core : BudgetCoreInput) (xs : List Bool) =>
      firmBudgetAssignmentBreachesData core xs :=
    firmBudgetAssignmentBreachesData_prim.to₂
  have hstep : Primrec₂ fun (core : BudgetCoreInput)
      (q : List Bool × Bool) =>
      firmBudgetAssignmentBreachesData core q.1 || q.2 :=
    (Primrec.dom_bool₂ (· || ·)).comp₂
      (hassignment.comp₂ Primrec₂.left
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hassignments (Primrec.const false) hstep).of_eq
    fun core => by
      unfold priorBudgetBreachData
      let assignments :=
        allBoolLists (budgetAtomList core.1.1.1.1 core.1.1.2 core.2).length
      have hAny : ∀ l : List (List Bool),
          l.foldr (fun xs found =>
            firmBudgetAssignmentBreachesData core xs || found) false =
          l.any (firmBudgetAssignmentBreachesData core) := by
        intro l
        induction l with
        | nil => rfl
        | cons xs xss ih => simp [ih]
      exact hAny assignments

/-! ## The Budgeter's scale factor

The scale factor is the minimum over finitely many worlds of a per-world value feature.
That feature is built here as a standalone proof-erased syntax constructor, so the bridge
back to `Strategy.tradeListWorldValueFeature` stays exact and reusable. -/

private def tradeListWorldValueFeatureData
    (atoms : List ℕ) (xs : List Bool) (trades : List (EF × Sentence))
    (n : ℕ) : EF :=
  ROIBudget.sumFeatures (trades.map fun p =>
    .mul p.1 (.add
      (.const (bif sentenceBoolFromAtomList atoms xs p.2 then 1 else 0))
      (.mul (.const (-1)) (.price p.2 n))))

section
-- `Nat.sqrt` irreducible: see the module header.  The other names are blocked so the
-- defeq bridges match structurally instead of by reduction.
attribute [local irreducible] Nat.sqrt sentenceBoolFromAtomList
  tradeListWorldValueFeatureData

private lemma tradeListWorldValueFeatureData_prim : Primrec fun p :
    ((List ℕ × List Bool) × List (EF × Sentence)) × ℕ =>
      tradeListWorldValueFeatureData p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  let P := ((List ℕ × List Bool) × List (EF × Sentence)) × ℕ
  have htrades : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have heval : Primrec₂ fun (p : P) (trade : EF × Sentence) =>
      sentenceBoolFromAtomList p.1.1.1 p.1.1.2 trade.2 :=
    sentenceBoolFromAtomList_prim.to₂.comp₂
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) |>.comp₂
          Primrec₂.left)
      (Primrec.snd.comp₂ Primrec₂.right)
  have hpayout : Primrec₂ fun (p : P) (trade : EF × Sentence) =>
      (bif sentenceBoolFromAtomList p.1.1.1 p.1.1.2 trade.2 then
        (1 : ℚ) else 0) :=
    Primrec.cond heval (Primrec.const 1) (Primrec.const 0)
  have hprice : Primrec₂ fun (p : P) (trade : EF × Sentence) =>
      EF.price trade.2 p.2 :=
    efPrice_prim.comp₂
      (Primrec.snd.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.left)
  have hdelta : Primrec₂ fun (p : P) (trade : EF × Sentence) =>
      EF.add
        (EF.const (bif sentenceBoolFromAtomList p.1.1.1 p.1.1.2 trade.2 then
          1 else 0))
        (EF.mul (EF.const (-1)) (EF.price trade.2 p.2)) :=
    efAdd_prim.comp₂
      (efConst_prim.comp₂ hpayout)
      (efMul_prim.comp₂
        (efConst_prim.comp₂ (Primrec₂.const (-1 : ℚ))) hprice)
  have htrade : Primrec₂ fun (p : P) (trade : EF × Sentence) =>
      EF.mul trade.1
        (EF.add
          (EF.const (bif sentenceBoolFromAtomList p.1.1.1 p.1.1.2 trade.2 then
            1 else 0))
          (EF.mul (EF.const (-1)) (EF.price trade.2 p.2))) :=
    efMul_prim.comp₂ (Primrec.fst.comp₂ Primrec₂.right) hdelta
  exact (sumFeatures_prim.comp
    (Primrec.list_map htrades htrade)).of_eq fun p => by
      unfold tradeListWorldValueFeatureData
      rfl

end

private lemma tradeListWorldValueFeatureData_eq
    (atoms : List ℕ) (xs : List Bool) (trades : List (EF × Sentence))
    (n : ℕ) :
    tradeListWorldValueFeatureData atoms xs trades n =
      Strategy.tradeListWorldValueFeature trades n (atomListTable atoms xs) := by
  unfold tradeListWorldValueFeatureData Strategy.tradeListWorldValueFeature
  apply congrArg ROIBudget.sumFeatures
  apply List.map_congr_left
  intro trade htrade
  rcases trade with ⟨e, φ⟩
  cases h : sentenceBoolFromAtomList atoms xs φ
  · have h' : sentenceBool (atomListTable atoms xs) φ = false := h
    simp [boolPayoutRat, h']
  · have h' : sentenceBool (atomListTable atoms xs) φ = true := h
    simp [boolPayoutRat, h']

private def budgetWorldScaleData
    (core : BudgetCoreInput) (xs : List Bool) : EF :=
  let atoms := budgetAtomList core.1.1.1.1 core.1.1.2 core.2
  let trades := ((firmRawTrader core.1.1.2).strat core.2).trades
  .safeRecip (.mul
    (.const (((core.1.2 : ℕ) : ℚ) + firmRawPriorWorthData
      (core.1.1.1.2, atoms, xs) core.1.1.2 core.2)⁻¹)
    (EF.neg (tradeListWorldValueFeatureData atoms xs trades core.2)))

section
-- `Nat.sqrt` irreducible: see the module header.  The other names are blocked so the
-- defeq bridges match structurally instead of by reduction.
attribute [local irreducible] Nat.sqrt budgetWorldScaleData budgetAtomList
  firmRawPriorWorthData tradeListWorldValueFeatureData

private lemma budgetWorldScaleData_prim : Primrec fun p :
    BudgetCoreInput × List Bool => budgetWorldScaleData p.1 p.2 := by
  let P := BudgetCoreInput × List Bool
  have hstages : Primrec fun p : P => p.1.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hpast : Primrec fun p : P => p.1.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hj : Primrec fun p : P => p.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hb : Primrec fun p : P => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hxs : Primrec fun p : P => p.2 := Primrec.snd
  have hatoms : Primrec fun p : P =>
      budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2 :=
    budgetAtomList_prim.comp ((hstages.pair hj).pair hn)
  have htrades : Primrec fun p : P =>
      ((firmRawTrader p.1.1.1.2).strat p.1.2).trades :=
    firmRawTraderTrades_prim.comp hj hn
  have hctx : Primrec fun p : P =>
      ((p.1.1.1.1.2,
        budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2,
        p.2) : BudgetWorldContext) :=
    hpast.pair (hatoms.pair hxs)
  have hworth : Primrec fun p : P =>
      firmRawPriorWorthData
        (p.1.1.1.1.2,
          budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2, p.2)
        p.1.1.1.2 p.1.2 :=
    firmRawPriorWorthData_prim.comp ((hctx.pair hj).pair hn)
  have hcoefficient : Primrec fun p : P =>
      (((p.1.1.2 : ℕ) : ℚ) + firmRawPriorWorthData
        (p.1.1.1.1.2,
          budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2, p.2)
        p.1.1.1.2 p.1.2)⁻¹ :=
    ratInv_prim.comp (ratAdd_prim.comp (natCastRat_prim.comp hb) hworth)
  have hvalue : Primrec fun p : P =>
      tradeListWorldValueFeatureData
        (budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2) p.2
        ((firmRawTrader p.1.1.1.2).strat p.1.2).trades p.1.2 :=
    tradeListWorldValueFeatureData_prim.comp
      (((hatoms.pair hxs).pair htrades).pair hn)
  exact (efSafeRecip_prim.comp
    (efMul_prim.comp (efConst_prim.comp hcoefficient)
      (efNeg_prim.comp hvalue))).of_eq fun p => by
        unfold budgetWorldScaleData
        rfl

end

private lemma budgetWorldScaleData_eq
    (stages : List (Finset Sentence)) (past : List RationalBeliefState)
    (j b n : ℕ) (xs : List Bool) :
    budgetWorldScaleData ((((stages, past), j), b), n) xs =
      budgetWorldScaleTradeLists
        (fun i => ((firmRawTrader j).strat i).trades) b
        (rationalHistory past)
        (atomListTable (budgetAtomList stages j n) xs) n := by
  change EF.safeRecip (EF.mul
      (EF.const (((b : ℕ) : ℚ) + firmRawPriorWorthData
        (past, budgetAtomList stages j n, xs) j n)⁻¹)
      (EF.neg (tradeListWorldValueFeatureData
        (budgetAtomList stages j n) xs
        ((firmRawTrader j).strat n).trades n))) =
    EF.safeRecip (EF.mul
      (EF.const (((b : ℕ) : ℚ) + rawPriorWorthRatTradeLists
        (fun i => ((firmRawTrader j).strat i).trades)
        (rationalHistory past) (atomListTable (budgetAtomList stages j n) xs) n)⁻¹)
      (EF.neg (Strategy.tradeListWorldValueFeature
        ((firmRawTrader j).strat n).trades n
        (atomListTable (budgetAtomList stages j n) xs))))
  rw [firmRawPriorWorthData_eq,
    tradeListWorldValueFeatureData_eq]

private def budgetScaleFeaturesData (core : BudgetCoreInput) : List EF :=
  let atoms := budgetAtomList core.1.1.1.1 core.1.1.2 core.2
  (allBoolLists atoms.length).foldr (fun xs acc =>
    bif budgetConsistentAtDayData atoms xs core.1.1.1.1 core.2 then
      budgetWorldScaleData core xs :: acc
    else acc) []

private def budgetScaleFeatureData (core : BudgetCoreInput) : EF :=
  EF.listMin (budgetScaleFeaturesData core)

section
-- `Nat.sqrt` irreducible: see the module header.  The other names are blocked so the
-- defeq bridges match structurally instead of by reduction.
attribute [local irreducible] Nat.sqrt budgetScaleFeaturesData
  budgetScaleFeatureData budgetConsistentAtDayData budgetWorldScaleData
  budgetAtomList decodedStageTable tableConsistentFromAtomList

private lemma budgetScaleFeaturesData_prim :
    Primrec budgetScaleFeaturesData := by
  have hstages : Primrec fun core : BudgetCoreInput => core.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hj : Primrec fun core : BudgetCoreInput => core.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun core : BudgetCoreInput => core.2 := Primrec.snd
  have hatoms : Primrec fun core : BudgetCoreInput =>
      budgetAtomList core.1.1.1.1 core.1.1.2 core.2 :=
    budgetAtomList_prim.comp ((hstages.pair hj).pair hn)
  have hassignments : Primrec fun core : BudgetCoreInput =>
      allBoolLists
        (budgetAtomList core.1.1.1.1 core.1.1.2 core.2).length :=
    allBoolLists_prim.comp (Primrec.list_length.comp hatoms)
  have hconsistent : Primrec fun p : BudgetCoreInput × List Bool =>
      budgetConsistentAtDayData
        (budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2)
        p.2 p.1.1.1.1.1 p.1.2 :=
    budgetConsistentAtDayData_prim.comp
      ((((hatoms.comp Primrec.fst).pair Primrec.snd).pair
        (hstages.comp Primrec.fst)).pair (hn.comp Primrec.fst))
  have hstep : Primrec₂ fun (core : BudgetCoreInput)
      (q : List Bool × List EF) =>
      bif budgetConsistentAtDayData
          (budgetAtomList core.1.1.1.1 core.1.1.2 core.2)
          q.1 core.1.1.1.1 core.2 then
        budgetWorldScaleData core q.1 :: q.2
      else q.2 := by
    have htest : Primrec fun p : BudgetCoreInput × (List Bool × List EF) =>
        budgetConsistentAtDayData
          (budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2)
          p.2.1 p.1.1.1.1.1 p.1.2 :=
      hconsistent.comp ((Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
    have hthen : Primrec fun p : BudgetCoreInput × (List Bool × List EF) =>
        budgetWorldScaleData p.1 p.2.1 :: p.2.2 :=
      Primrec.list_cons.comp
        (budgetWorldScaleData_prim.comp
          (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)
    exact (Primrec.cond htest hthen
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr hassignments (Primrec.const []) hstep).of_eq
    fun core => by
      unfold budgetScaleFeaturesData
      rfl

private lemma budgetScaleFeatureData_prim :
    Primrec budgetScaleFeatureData := by
  exact (efListMin_prim.comp budgetScaleFeaturesData_prim).of_eq fun core => by
    unfold budgetScaleFeatureData
    rfl

end

private lemma firmBudgetBreachAtDayData_eq
    (stages : List (Finset Sentence)) (past : List RationalBeliefState)
    (j b n : ℕ) (xs : List Bool) (m : ℕ) :
    firmBudgetBreachAtDayData ((((stages, past), j), b), n) xs m =
      (tableConsistent
          (finiteAtomTableFromList
            (budgetAtomsFromStageTradeLists (decodedStageTable stages)
              (fun i => ((firmRawTrader j).strat i).trades) n) xs)
          (decodedStageTable stages m) &&
        decide (rawWorthRatTradeLists
          (fun i => ((firmRawTrader j).strat i).trades)
          (rationalHistory past)
          (finiteAtomTableFromList
            (budgetAtomsFromStageTradeLists (decodedStageTable stages)
              (fun i => ((firmRawTrader j).strat i).trades) n) xs)
          m ≤ -(b : ℚ))) := by
  let A := budgetAtomsFromStageTradeLists (decodedStageTable stages)
    (fun i => ((firmRawTrader j).strat i).trades) n
  change
    (tableConsistentFromAtomList (budgetAtomList stages j n) xs
        (decodedStageTable stages m) &&
      decide (firmRawPriorWorthData
        (past, budgetAtomList stages j n, xs) j (m + 1) ≤ -(b : ℚ))) =
    (tableConsistent (finiteAtomTableFromList A xs)
        (decodedStageTable stages m) &&
      decide (rawWorthRatTradeLists
        (fun i => ((firmRawTrader j).strat i).trades)
        (rationalHistory past) (finiteAtomTableFromList A xs) m ≤ -(b : ℚ)))
  rw [budgetAtomList_eq]
  rw [tableConsistentFromAtomList_sort_eq, firmRawPriorWorthData_eq,
    atomListTable_sort_eq]
  rfl

private lemma firmBudgetAssignmentBreachesData_eq
    (stages : List (Finset Sentence)) (past : List RationalBeliefState)
    (j b n : ℕ) (xs : List Bool) :
    firmBudgetAssignmentBreachesData ((((stages, past), j), b), n) xs =
      (List.range n).any fun m =>
        tableConsistent
            (finiteAtomTableFromList
              (budgetAtomsFromStageTradeLists (decodedStageTable stages)
                (fun i => ((firmRawTrader j).strat i).trades) n) xs)
            (decodedStageTable stages m) &&
          decide (rawWorthRatTradeLists
            (fun i => ((firmRawTrader j).strat i).trades)
            (rationalHistory past)
            (finiteAtomTableFromList
              (budgetAtomsFromStageTradeLists (decodedStageTable stages)
                (fun i => ((firmRawTrader j).strat i).trades) n) xs)
            m ≤ -(b : ℚ)) := by
  unfold firmBudgetAssignmentBreachesData
  apply List.any_congr rfl
  intro m
  exact firmBudgetBreachAtDayData_eq stages past j b n xs m

private lemma priorBudgetBreachData_eq
    (stages : List (Finset Sentence)) (past : List RationalBeliefState)
    (j b n : ℕ) :
    priorBudgetBreachData ((((stages, past), j), b), n) =
      priorBudgetBreachFromStageTradeLists (decodedStageTable stages)
        (fun i => ((firmRawTrader j).strat i).trades) b
        (rationalHistory past) n := by
  unfold priorBudgetBreachData priorBudgetBreachFromStageTradeLists
  dsimp only
  rw [budgetAtomList_eq, Finset.length_sort]
  apply List.any_congr rfl
  intro xs
  exact firmBudgetAssignmentBreachesData_eq stages past j b n xs

private lemma budgetScaleFeatureData_eq
    (stages : List (Finset Sentence)) (past : List RationalBeliefState)
    (j b n : ℕ) :
    budgetScaleFeatureData ((((stages, past), j), b), n) =
      budgetScaleFeatureFromStageTradeLists (decodedStageTable stages)
        (fun i => ((firmRawTrader j).strat i).trades) b
        (rationalHistory past) n := by
  let A := budgetAtomsFromStageTradeLists (decodedStageTable stages)
    (fun i => ((firmRawTrader j).strat i).trades) n
  have hatoms : budgetAtomList stages j n = A.sort (fun a b => a ≤ b) :=
    budgetAtomList_eq stages j n
  have hconsistent (xs : List Bool) :
      budgetConsistentAtDayData (A.sort (fun a b => a ≤ b)) xs stages n =
        tableConsistent (finiteAtomTableFromList A xs)
          (decodedStageTable stages n) := by
    unfold budgetConsistentAtDayData
    exact tableConsistentFromAtomList_sort_eq A xs
      (decodedStageTable stages n)
  have hscale (xs : List Bool) :
      budgetWorldScaleData ((((stages, past), j), b), n) xs =
        budgetWorldScaleTradeLists
          (fun i => ((firmRawTrader j).strat i).trades) b
          (rationalHistory past) (finiteAtomTableFromList A xs) n := by
    rw [budgetWorldScaleData_eq, hatoms, atomListTable_sort_eq]
  unfold budgetScaleFeatureData budgetScaleFeaturesData
    budgetScaleFeatureFromStageTradeLists
  rw [hatoms]
  dsimp only
  rw [Finset.length_sort]
  apply congrArg EF.listMin
  generalize allBoolLists A.card = assignments
  induction assignments with
  | nil => rfl
  | cons xs rest ih =>
      rw [List.foldr_cons, hconsistent xs, hscale xs, List.filter_cons]
      cases h : tableConsistent (finiteAtomTableFromList A xs)
          (decodedStageTable stages n)
      · exact ih
      · exact congrArg
          (List.cons (budgetWorldScaleTradeLists
            (fun i => ((firmRawTrader j).strat i).trades) b
            (rationalHistory past) (finiteAtomTableFromList A xs) n)) ih

section
-- `Nat.sqrt` irreducible: see the module header.  The other names are blocked so the
-- defeq bridges match structurally instead of by reduction.
attribute [local irreducible] Nat.sqrt priorBudgetBreachData
  budgetScaleFeatureData

/-! ## Assembling the Trading Firm's day trade list -/

private lemma budgeterTradesFromStageTradeLists_prim : Primrec fun core :
    BudgetCoreInput =>
      budgeterTradesFromStageTradeLists
        (decodedStageTable core.1.1.1.1)
        (fun i => ((firmRawTrader core.1.1.2).strat i).trades)
        core.1.2 (rationalHistory core.1.1.1.2) core.2 := by
  have hj : Primrec fun core : BudgetCoreInput => core.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun core : BudgetCoreInput => core.2 := Primrec.snd
  have hraw : Primrec fun core : BudgetCoreInput =>
      ((firmRawTrader core.1.1.2).strat core.2).trades :=
    firmRawTraderTrades_prim.comp hj hn
  have htrade : Primrec₂ fun (core : BudgetCoreInput)
      (trade : EF × Sentence) =>
      (EF.mul (budgetScaleFeatureData core) trade.1, trade.2) :=
    Primrec₂.pair.comp₂
      (efMul_prim.comp₂
        (budgetScaleFeatureData_prim.comp₂ Primrec₂.left)
        (Primrec.fst.comp₂ Primrec₂.right))
        (Primrec.snd.comp₂ Primrec₂.right)
  have hscaled : Primrec fun core : BudgetCoreInput =>
      (((firmRawTrader core.1.1.2).strat core.2).trades.map fun trade =>
        (EF.mul (budgetScaleFeatureData core) trade.1, trade.2)) :=
    Primrec.list_map hraw htrade
  have hcompiled : Primrec fun core : BudgetCoreInput =>
      bif priorBudgetBreachData core then [] else
        ((firmRawTrader core.1.1.2).strat core.2).trades.map fun trade =>
          (EF.mul (budgetScaleFeatureData core) trade.1, trade.2) :=
    Primrec.cond priorBudgetBreachData_prim (Primrec.const []) hscaled
  exact hcompiled.of_eq fun core => by
    rcases core with ⟨⟨⟨⟨stages, past⟩, j⟩, b⟩, n⟩
    rw [priorBudgetBreachData_eq, budgetScaleFeatureData_eq]
    unfold budgeterTradesFromStageTradeLists
    cases priorBudgetBreachFromStageTradeLists (decodedStageTable stages)
      (fun i => ((firmRawTrader j).strat i).trades) b
      (rationalHistory past) n <;> rfl

end

private abbrev TradingFirmComponentInput :=
  ((List (Finset Sentence) × List RationalBeliefState) × ℕ) × ℕ

section
-- `Nat.sqrt` irreducible: see the module header.  The other names are blocked so the
-- defeq bridges match structurally instead of by reduction.
attribute [local irreducible] Nat.sqrt tradingFirmCutoffTradeLists
  budgeterTradesFromStageTradeLists

private lemma tradingFirmComponentTradesFromStageTradeLists_prim :
    Primrec fun p : TradingFirmComponentInput =>
      tradingFirmComponentTradesFromStageTradeLists
        (decodedStageTable p.1.1.1) (rationalHistory p.1.1.2)
        p.1.2 p.2 := by
  let P := TradingFirmComponentInput
  have hstages : Primrec fun p : P => p.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hpast : Primrec fun p : P => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hj : Primrec fun p : P => p.2 := Primrec.snd
  have hcutoff : Primrec fun p : P =>
      tradingFirmCutoffTradeLists p.1.2 :=
    tradingFirmCutoffTradeLists_prim.comp hn
  have hrange : Primrec fun p : P =>
      List.range (tradingFirmCutoffTradeLists p.1.2) :=
    Primrec.list_range.comp hcutoff
  have hbudget : Primrec₂ fun (p : P) (r : ℕ) =>
      budgeterTradesFromStageTradeLists
        (decodedStageTable p.1.1.1)
        (fun i => ((firmRawTrader p.2).strat i).trades)
        (r + 1) (rationalHistory p.1.1.2) p.1.2 := by
    have hcore : Primrec fun z : P × ℕ =>
        (((((z.1.1.1.1, z.1.1.1.2), z.1.2), z.2 + 1), z.1.1.2) :
          BudgetCoreInput) := by
      have hstages' : Primrec fun z : P × ℕ => z.1.1.1.1 :=
        hstages.comp Primrec.fst
      have hpast' : Primrec fun z : P × ℕ => z.1.1.1.2 :=
        hpast.comp Primrec.fst
      have hj' : Primrec fun z : P × ℕ => z.1.2 :=
        hj.comp Primrec.fst
      have hb' : Primrec fun z : P × ℕ => z.2 + 1 :=
        Primrec.nat_add.comp Primrec.snd (Primrec.const 1)
      have hn' : Primrec fun z : P × ℕ => z.1.1.2 :=
        hn.comp Primrec.fst
      exact (((hstages'.pair hpast').pair hj').pair hb').pair hn'
    exact (budgeterTradesFromStageTradeLists_prim.comp hcore).to₂
  have hweight : Primrec₂ fun (p : P) (r : ℕ) =>
      tradingFirmWeight p.2 (r + 1) :=
    tradingFirmWeight_prim.comp₂
      (hj.comp₂ Primrec₂.left)
      (Primrec.nat_add.comp₂ Primrec₂.right (Primrec₂.const 1))
  have hscaledBudget : Primrec₂ fun (p : P) (r : ℕ) =>
      scaleConstTradeList (tradingFirmWeight p.2 (r + 1))
        (budgeterTradesFromStageTradeLists
          (decodedStageTable p.1.1.1)
          (fun i => ((firmRawTrader p.2).strat i).trades)
          (r + 1) (rationalHistory p.1.1.2) p.1.2) :=
    scaleConstTradeList_prim.comp₂ hweight hbudget
  have hbudgets : Primrec fun p : P =>
      (List.range (tradingFirmCutoffTradeLists p.1.2)).flatMap fun r =>
        scaleConstTradeList (tradingFirmWeight p.2 (r + 1))
          (budgeterTradesFromStageTradeLists
            (decodedStageTable p.1.1.1)
            (fun i => ((firmRawTrader p.2).strat i).trades)
            (r + 1) (rationalHistory p.1.1.2) p.1.2) :=
    Primrec.list_flatMap hrange hscaledBudget
  have htailWeight : Primrec fun p : P =>
      tradingFirmWeight p.2 (tradingFirmCutoffTradeLists p.1.2) :=
    tradingFirmWeight_prim.comp hj hcutoff
  have htailRaw : Primrec fun p : P =>
      ((firmRawTrader p.2).strat p.1.2).trades :=
    firmRawTraderTrades_prim.comp hj hn
  have htail : Primrec fun p : P =>
      scaleConstTradeList
        (tradingFirmWeight p.2 (tradingFirmCutoffTradeLists p.1.2))
        ((firmRawTrader p.2).strat p.1.2).trades :=
    scaleConstTradeList_prim.comp htailWeight htailRaw
  exact (Primrec.list_append.comp hbudgets htail).of_eq fun p => by
    unfold tradingFirmComponentTradesFromStageTradeLists
    rfl

end

private abbrev TradingFirmInput :=
  (List (Finset Sentence) × List RationalBeliefState) × ℕ

section
-- `Nat.sqrt` irreducible: see the module header.  The other name is blocked so the
-- defeq bridge matches structurally instead of by reduction.
attribute [local irreducible] Nat.sqrt
  tradingFirmComponentTradesFromStageTradeLists

private lemma tradingFirmTradesFromStageTradeLists_prim :
    Primrec fun p : TradingFirmInput =>
      tradingFirmTradesFromStageTradeLists
        (decodedStageTable p.1.1) (rationalHistory p.1.2) p.2 := by
  let P := TradingFirmInput
  have hrange : Primrec fun p : P => List.range (p.2 + 1) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
  have hcomponent : Primrec₂ fun (p : P) (j : ℕ) =>
      tradingFirmComponentTradesFromStageTradeLists
        (decodedStageTable p.1.1) (rationalHistory p.1.2) p.2 j := by
    have hinput : Primrec fun z : P × ℕ =>
        ((((z.1.1.1, z.1.1.2), z.1.2), z.2) :
          TradingFirmComponentInput) :=
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.fst)).pair Primrec.snd
    exact (tradingFirmComponentTradesFromStageTradeLists_prim.comp hinput).to₂
  exact (Primrec.list_flatMap hrange hcomponent).of_eq fun p => by
    unfold tradingFirmTradesFromStageTradeLists
    rfl

end

/-! ## The bounded LIA state-prefix evaluator

The day error schedule, the stage-prefix decoder and the three components combine into the
fuel-bounded evaluators of the LIA state prefix, its encoded quote table and its encoded
belief-state entries. -/

private lemma marketMakerError_prim : Primrec marketMakerError := by
  have hexponent : Primrec fun n : ℕ => n + 1 :=
    Primrec.nat_add.comp Primrec.id (Primrec.const 1)
  have hpow : Primrec fun n : ℕ => (2 : ℚ) ^ (n + 1) :=
    ratPow_prim.comp (Primrec.const 2) hexponent
  exact (ratDiv_prim.comp (Primrec.const 1) hpow).of_eq fun n => by
    rfl

section
-- `Nat.sqrt` irreducible: see the module header.  The other names are blocked so the
-- defeq bridges match structurally instead of by reduction.
attribute [local irreducible] Nat.sqrt liaPrefixFromTradeListsAtFuel
  tradingFirmTradesFromStageTradeLists marketMakerSearchUpToTradeList

private lemma liaPrefixFromTradeListsAtFuel_prim : Primrec fun p :
    (List (Finset Sentence) × ℕ) × ℕ =>
      liaPrefixFromTradeListsAtFuel
        (decodedStageTable p.1.1) p.1.2 p.2 := by
  let C := List (Finset Sentence) × ℕ
  have hbase : Primrec fun _ctx : C =>
      (some [] : Option (List RationalBeliefState)) :=
    Primrec.const (some [])
  have hstep : Primrec₂ fun (ctx : C)
      (ni : ℕ × Option (List RationalBeliefState)) =>
      ni.2.bind fun past =>
        (marketMakerSearchUpToTradeList
          (tradingFirmTradesFromStageTradeLists
            (decodedStageTable ctx.1) (rationalHistory past) ni.1)
          ni.1 past (marketMakerError ni.1) ctx.2).bind fun state =>
            some (past ++ [state]) := by
    let X := C × (ℕ × Option (List RationalBeliefState))
    have hfirm : Primrec₂ fun (x : X)
        (past : List RationalBeliefState) =>
        tradingFirmTradesFromStageTradeLists
          (decodedStageTable x.1.1) (rationalHistory past) x.2.1 := by
      have hinput : Primrec fun z : X × List RationalBeliefState =>
          (((z.1.1.1, z.2), z.1.2.1) : TradingFirmInput) :=
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          Primrec.snd).pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      exact (tradingFirmTradesFromStageTradeLists_prim.comp hinput).to₂
    have hsearch : Primrec₂ fun (x : X)
        (past : List RationalBeliefState) =>
        marketMakerSearchUpToTradeList
          (tradingFirmTradesFromStageTradeLists
            (decodedStageTable x.1.1) (rationalHistory past) x.2.1)
          x.2.1 past (marketMakerError x.2.1) x.1.2 := by
      have htrades : Primrec fun z : X × List RationalBeliefState =>
          tradingFirmTradesFromStageTradeLists
            (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1 :=
        hfirm.comp Primrec.fst Primrec.snd
      have hn : Primrec fun z : X × List RationalBeliefState => z.1.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
      have hpast : Primrec fun z : X × List RationalBeliefState => z.2 :=
        Primrec.snd
      have hepsilon : Primrec fun z : X × List RationalBeliefState =>
          marketMakerError z.1.2.1 :=
        marketMakerError_prim.comp hn
      have hfuel : Primrec fun z : X × List RationalBeliefState => z.1.1.2 :=
        Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
      have hinput : Primrec fun z : X × List RationalBeliefState =>
          (((((tradingFirmTradesFromStageTradeLists
              (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1,
            z.1.2.1), z.2), marketMakerError z.1.2.1),
              z.1.1.2) : MarketMakerSearchInput × ℕ) :=
        (((htrades.pair hn).pair hpast).pair hepsilon).pair hfuel
      exact (marketMakerSearchUpToTradeList_prim.comp hinput).to₂
    have hout : Primrec₂ fun
        (y : (X × List RationalBeliefState))
        (state : RationalBeliefState) =>
        some (y.2 ++ [state]) :=
      Primrec₂.option_some_iff.mpr
        (Primrec.list_concat.comp₂
          (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
    have hinner : Primrec₂ fun (x : X)
        (past : List RationalBeliefState) =>
        (marketMakerSearchUpToTradeList
          (tradingFirmTradesFromStageTradeLists
            (decodedStageTable x.1.1) (rationalHistory past) x.2.1)
          x.2.1 past (marketMakerError x.2.1) x.1.2).bind fun state =>
            some (past ++ [state]) :=
      (Primrec.option_bind
        (hsearch.comp Primrec.fst Primrec.snd) hout).to₂
    exact (Primrec.option_bind
      (Primrec.snd.comp Primrec.snd) hinner).to₂
  have hrec : Primrec₂ fun (ctx : C) n =>
      liaPrefixFromTradeListsAtFuel
        (decodedStageTable ctx.1) ctx.2 n := by
    exact (Primrec.nat_rec hbase hstep).of_eq fun ctx n => by
      induction n with
      | zero => simp [liaPrefixFromTradeListsAtFuel]
      | succ n ih => simp [liaPrefixFromTradeListsAtFuel, ih]
  exact hrec.comp Primrec.fst Primrec.snd

end

/-- The proof-carrying finite-stage recurrence has the same primitive-recursive
first-order implementation as its fully erased trade-list presentation. -/
private lemma liaPrefixFromStagesAtFuel_prim : Primrec fun p :
    (List (Finset Sentence) × ℕ) × ℕ =>
      liaPrefixFromStagesAtFuel
        (decodedStageTable p.1.1) p.1.2 p.2 := by
  exact liaPrefixFromTradeListsAtFuel_prim.of_eq fun p => by
    rw [liaPrefixFromTradeListsAtFuel_eq,
      liaPrefixFromStageListsAtFuel_eq]

/-- The complete common-clock LIA state-prefix evaluator is primitive recursive. -/
private lemma liaPrefixAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Primrec₂ fun fuel n => liaPrefixAtFuel process fuel n := by
  let X := ℕ × ℕ
  have hstages : Primrec fun x : X =>
      processStagePrefixAtFuel process x.1 x.2 :=
    (processStagePrefixAtFuel_prim process).comp Primrec.fst Primrec.snd
  have hrun : Primrec₂ fun (x : X) (stages : List (Finset Sentence)) =>
      liaPrefixFromStagesAtFuel
        (decodedStageTable stages) x.1 x.2 := by
    have hinput : Primrec fun z : X × List (Finset Sentence) =>
        (((z.2, z.1.1), z.1.2) :
          (List (Finset Sentence) × ℕ) × ℕ) :=
      ((Primrec.snd.pair
        (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.snd.comp Primrec.fst))
    exact (liaPrefixFromStagesAtFuel_prim.comp hinput).to₂
  exact ((Primrec.option_bind hstages hrun).to₂).of_eq fun fuel n => by
    rfl

section
-- `Nat.sqrt` irreducible: see the module header.  The other name is blocked so the
-- defeq bridge matches structurally instead of by reduction.
attribute [local irreducible] Nat.sqrt liaEncodedQuoteAtFuel

/-- The bounded exact rational quote evaluator is primitive recursive in its common
clock, day, and external sentence code. -/
private lemma liaEncodedQuoteAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) : Primrec fun p :
    (ℕ × ℕ) × ℕ =>
      liaEncodedQuoteAtFuel process p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have hfuel : Primrec fun p : P => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hday : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hdaySucc : Primrec fun p : P => p.1.2 + 1 :=
    Primrec.nat_add.comp hday (Primrec.const 1)
  have hprefix : Primrec fun p : P =>
      liaPrefixAtFuel process p.1.1 (p.1.2 + 1) :=
    (liaPrefixAtFuel_prim process).comp hfuel hdaySucc
  let Y := P × List RationalBeliefState
  have hlookup : Primrec fun y : Y => y.2[y.1.1.2]? :=
    Primrec.list_getElem?.comp Primrec.snd
      (hday.comp Primrec.fst)
  have hfinish : Primrec₂ fun (y : Y) (state : RationalBeliefState) =>
      some (match Encodable.decode (α := Sentence) y.1.2 with
        | some phi => state.quote phi
        | none => 0) := by
    let Z := Y × RationalBeliefState
    have hdecode : Primrec fun z : Z =>
        Encodable.decode (α := Sentence) z.1.1.2 :=
      (Primrec.decode : Primrec fun n : ℕ =>
        Encodable.decode (α := Sentence) n).comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hquote : Primrec₂ fun (z : Z) (phi : Sentence) =>
        z.2.quote phi :=
      rationalBeliefStateQuote_prim.comp₂
        (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right
    let valueCompiled : Z → ℚ := fun z =>
      Option.casesOn (Encodable.decode (α := Sentence) z.1.1.2)
        (0 : ℚ) fun phi => z.2.quote phi
    have hvalueCompiled : Primrec valueCompiled :=
      Primrec.option_casesOn hdecode (Primrec.const 0) hquote
    have hvalue : Primrec fun z : Z =>
        match Encodable.decode (α := Sentence) z.1.1.2 with
        | some phi => z.2.quote phi
        | none => 0 := hvalueCompiled.of_eq fun z => by
      unfold valueCompiled
      cases Encodable.decode (α := Sentence) z.1.1.2 <;> rfl
    exact Primrec₂.option_some_iff.mpr hvalue.to₂
  have hinner : Primrec₂ fun (p : P)
      (states : List RationalBeliefState) =>
      states[p.1.2]?.bind fun state =>
        some (match Encodable.decode (α := Sentence) p.2 with
          | some phi => state.quote phi
          | none => 0) :=
    (Primrec.option_bind hlookup hfinish).to₂
  exact (Primrec.option_bind hprefix hinner).of_eq fun p => by
    unfold liaEncodedQuoteAtFuel
    rfl

end

section
-- `Nat.sqrt` irreducible: see the module header.  The other name is blocked so the
-- defeq bridge matches structurally instead of by reduction.
attribute [local irreducible] Nat.sqrt liaEncodedQuoteNatAtFuel

/-- The natural-coded bounded evaluator is primitive recursive in the paired
day/sentence input and its common fuel clock. -/
private lemma liaEncodedQuoteNatAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Primrec₂ (liaEncodedQuoteNatAtFuel process) := by
  let X := ℕ × ℕ
  have hleft : Primrec fun p : X => p.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hright : Primrec fun p : X => p.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hinput : Primrec fun p : X =>
      (((p.2, p.1.unpair.1), p.1.unpair.2) : (ℕ × ℕ) × ℕ) :=
    (Primrec.snd.pair hleft).pair hright
  have hquote : Primrec fun p : X =>
      liaEncodedQuoteAtFuel process p.2 p.1.unpair.1 p.1.unpair.2 :=
    liaEncodedQuoteAtFuel_prim process |>.comp hinput
  have hencode : Primrec₂ fun (_p : X) (q : ℚ) =>
      Encodable.encode q :=
    Primrec.encode.comp₂ Primrec₂.right
  exact ((Primrec.option_map hquote hencode).to₂).of_eq fun z fuel => by
    unfold liaEncodedQuoteNatAtFuel
    rfl

end

/-- Concrete computability certificate for the sole bounded-evaluator boundary in the
core LIA construction. -/
lemma liaEncodedQuoteNatAtFuel_computable {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Computable₂ (liaEncodedQuoteNatAtFuel process) :=
  (liaEncodedQuoteNatAtFuel_prim process).to_comp

section
-- `Nat.sqrt` irreducible: see the module header.  The other name is blocked so the
-- defeq bridge matches structurally instead of by reduction.
attribute [local irreducible] Nat.sqrt liaEncodedEntriesAtFuel

/-- The bounded belief-state evaluator is primitive recursive in its day input and its
common fuel clock. -/
private lemma liaEncodedEntriesAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Primrec₂ (liaEncodedEntriesAtFuel process) := by
  let X := ℕ × ℕ
  have hday : Primrec fun p : X => p.1 := Primrec.fst
  have hdaySucc : Primrec fun p : X => p.1 + 1 :=
    Primrec.nat_add.comp hday (Primrec.const 1)
  have hprefix : Primrec fun p : X =>
      liaPrefixAtFuel process p.2 (p.1 + 1) :=
    (liaPrefixAtFuel_prim process).comp Primrec.snd hdaySucc
  let Y := X × List RationalBeliefState
  have hlookup : Primrec fun y : Y => y.2[y.1.1]? :=
    Primrec.list_getElem?.comp Primrec.snd (hday.comp Primrec.fst)
  have hfinish : Primrec₂ fun (_y : Y) (state : RationalBeliefState) =>
      some (Encodable.encode state.entries) :=
    Primrec₂.option_some_iff.mpr
      (Primrec.encode.comp₂ (rationalBeliefStateEntries_prim.comp₂ Primrec₂.right))
  have hinner : Primrec₂ fun (p : X)
      (states : List RationalBeliefState) =>
      states[p.1]?.bind fun state => some (Encodable.encode state.entries) :=
    (Primrec.option_bind hlookup hfinish).to₂
  exact ((Primrec.option_bind hprefix hinner).to₂).of_eq fun n fuel => by
    unfold liaEncodedEntriesAtFuel
    rfl

end

/-- Concrete computability certificate for the bounded belief-state evaluator. -/
lemma liaEncodedEntriesAtFuel_computable {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Computable₂ (liaEncodedEntriesAtFuel process) :=
  (liaEncodedEntriesAtFuel_prim process).to_comp

/-- Minimizing the bounded belief-state evaluator over its fuel clock gives one total
computable function emitting the exact day-`n` finite association list. -/
lemma liaEntries_computable {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Computable fun n : ℕ => Encodable.encode (liaStates DP n).entries := by
  let search : ℕ → Part ℕ := fun n =>
    Nat.rfindOpt (liaEncodedEntriesAtFuel process n)
  have hsearch : Partrec search :=
    Partrec.rfindOpt (liaEncodedEntriesAtFuel_computable process)
  apply hsearch.of_eq_tot
  intro n
  have hdom : (search n).Dom := by
    rw [Nat.rfindOpt_dom]
    obtain ⟨fuel, hfuel⟩ := exists_liaEncodedEntriesAtFuel process n
    exact ⟨fuel, _, hfuel⟩
  let out := (search n).get hdom
  have hout : out ∈ search n := Part.get_mem hdom
  obtain ⟨fuel, hfuel⟩ := Nat.rfindOpt_spec hout
  have houtEq := liaEncodedEntriesAtFuel_sound process hfuel
  rw [← houtEq]
  exact hout

/-- The single program promised by `def:belseq`: on input `n` it emits the code of the
day-`n` finite belief-state association list. -/
lemma exists_liaEntries_code {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    ∃ code : Nat.Partrec.Code, ∀ n : ℕ,
      Encodable.encode (liaStates DP n).entries ∈ code.eval n := by
  have hpart : Nat.Partrec (fun n : ℕ =>
      Part.some (Encodable.encode (liaStates DP n).entries)) :=
    Partrec.nat_iff.mp (liaEntries_computable process).partrec
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hpart
  refine ⟨code, ?_⟩
  intro n
  rw [hcode]
  simp

/-! ## `thm:lia` and `thm:li`: the existence theorems -/

/-- The concrete bounded evaluator compiler assembled from the primitive-recursive
first-order implementation above. -/
def liaBoundedEvaluatorCompiler {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    LIABoundedEvaluatorCompiler process where
  computable := liaEncodedQuoteNatAtFuel_computable process

/-- `thm:lia`: the recursively constructed rational LIA market is a logical inductor
over every computable deductive process, **at the paper's own quantifier** — no trader in
ordinary machine polynomial time exploits it.

`ComputableDeductiveProcess` is the paper's own condition on `def:dedproc`, which
`DeductiveProcess` (`Framework/Criterion.lean`) carries as a separate predicate rather than
as a field, so the hypothesis is not a hypothesis beyond the paper.  The three theorems
below take it for the same reason.
Paper node: `thm:lia` -/
theorem LIA_isMachineLogicalInductor (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) :
    IsMachineLogicalInductor (liaHistory DP) DP := by
  obtain ⟨process⟩ := hDP.nonemptyComputation
  exact lia_isMachineLogicalInductor_of_compiler process
    (liaBoundedEvaluatorCompiler process)

/-- `thm:lia` at the fuel-class compatibility predicate, by the bridge. This is the form the
property tail consumes.
Paper node: `thm:lia` -/
theorem LIA_is_logical_inductor (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) :
    IsLogicalInductor (liaHistory DP) DP :=
  @IsMachineLogicalInductor.toIsLogicalInductor _ _ (LIA_isMachineLogicalInductor DP hDP)

/-- `thm:li` at the paper's own quantifier: every computable deductive process admits a
market no machine-polynomial-time trader exploits.

This is the bare-market projection; the paper's own computable-belief-sequence form
(`def:belseq`) is `exists_computable_beliefSequence_logical_inductor` below.
Paper node: `thm:li` -/
theorem exists_machine_logical_inductor (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) :
    ∃ P : History, IsMachineLogicalInductor P DP :=
  ⟨liaHistory DP, LIA_isMachineLogicalInductor DP hDP⟩

/-- `thm:li`: every computable deductive process admits a logical inductor.

This is the fuel-class (`dd:fuel`) projection of `exists_machine_logical_inductor` above,
which is the paper-quantifier form: `IsMachineLogicalInductor.toIsLogicalInductor` makes
`IsLogicalInductor` the weaker conclusion.  The paper's own computable-belief-sequence form
(`def:belseq`) is `exists_computable_beliefSequence_logical_inductor` below.
Paper node: `thm:li` -/
theorem exists_logical_inductor (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) :
    ∃ P : History, IsLogicalInductor P DP :=
  ⟨liaHistory DP, LIA_is_logical_inductor DP hDP⟩

/-- **`thm:li`, full belief-sequence form.**  The paper's main theorem concludes existence
of a *computable belief sequence* (`def:belseq`) of finite-support `[0,1]`-rational belief
states (`def:belstate`) whose induced pricing satisfies the criterion.  The witness is the
recursive rational belief sequence `liaStates DP : ℕ → RationalBeliefState`, and

* `IsMachineLogicalInductor (fun n => (𝔹 n).toValuation) DP` — the induced real pricing is a
  logical inductor **at the paper's own quantifier**: no trader in ordinary machine
  polynomial time exploits it.  The fuel-class reading follows by
  `IsMachineLogicalInductor.toIsLogicalInductor`.  This class bundles the paper's
  *computable exact-rational market* certificate (`marketComputable : ComputableMarket` —
  one fixed program computes the rational quote table), the computable deductive process,
  and the no-exploitation criterion;
* **one program emits the belief states themselves**: a single `Nat.Partrec.Code` that on
  input `n` outputs the code of the day-`n` finite association list `(𝔹 n).entries`.  This
  is the conjunct that makes `𝔹` a *computable belief sequence* in the paper's sense; it is
  strictly stronger than the quote-table computability carried by `marketComputable`, since
  a uniformly computable finite-support quote table need not have a computable support
  listing;
* each day's belief state has **finite support** — only the finitely many sentences in
  `(𝔹 n).support` are priced nonzero;
* each priced value is an **exact rational in `[0,1]`**; and
* the induced real pricing is the rational quote cast to `ℝ`.

`exists_logical_inductor` above is the projection to the bare existence statement.

Proof kind `C` (composition).  Provenance: the criterion conjunct is
`LIA_isMachineLogicalInductor` (a); the emission conjunct is `exists_liaEntries_code` (a) —
minimization of the primitive recursive bounded evaluator `liaEncodedEntriesAtFuel` over
its fuel clock, pinned to the semantic states by `liaEncodedEntriesAtFuel_sound`; the
support/range/cast conjuncts are `RationalBeliefState` facts (a).
Paper node: `thm:li` -/
theorem exists_computable_beliefSequence_logical_inductor (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) :
    ∃ 𝔹 : ℕ → RationalBeliefState,
      IsMachineLogicalInductor (fun n => (𝔹 n).toValuation) DP ∧
        (∃ code : Nat.Partrec.Code, ∀ n : ℕ,
          Encodable.encode (𝔹 n).entries ∈ code.eval n) ∧
        (∀ n φ, φ ∉ (𝔹 n).support → (𝔹 n).quote φ = 0) ∧
        (∀ n φ, 0 ≤ (𝔹 n).quote φ ∧ (𝔹 n).quote φ ≤ 1) ∧
        (∀ n φ, (𝔹 n).toValuation φ = ((𝔹 n).quote φ : ℝ)) := by
  obtain ⟨process⟩ := hDP.nonemptyComputation
  exact ⟨liaStates DP, LIA_isMachineLogicalInductor DP hDP,
    exists_liaEntries_code process,
    fun n φ h => (liaStates DP n).quote_eq_zero_of_not_mem h,
    fun n φ => (liaStates DP n).quote_mem_Icc φ,
    fun _ _ => rfl⟩

/-! ## Public computability interface for downstream market constructions

A construction that prices the Trading Firm **together with a further trader** — a
privileged enforcement trader, say — runs the same erased recurrence with one extra trade
list in the day's aggregate, and needs the same first-order ingredients to show its own
bounded evaluator computable.  This section is the supported list of those ingredients:
the expressible-feature constructors and `EF.absBound`; the two erased steps of the day
recurrence (the firm's trade list, and the MarketMaker search over a raw trade list); the
day error schedule; the deductive-stage prefix decoder; and the belief state's exact
rational quote.  The exact rational evaluator `efRatCompiledEval`, together with
`efRatCompiledEval_eq` and `efRatCompiledEval_prim`, belongs to the same interface and
stays where it is proved, in the exact stack-machine section above.

`_prim` is this file's uniform suffix for a computability certificate; the `_primrec`
names here are the interface spellings of the same facts.

What the interface deliberately withholds is the recurrence itself: a downstream
construction states and proves its own, which is where its own soundness obligation
belongs.
-/

/-- `EF.const` is primitive recursive. -/
lemma efConst_primrec : Primrec EF.const := efConst_prim

/-- `EF.price` is primitive recursive in the sentence and the day. -/
lemma efPrice_primrec : Primrec₂ EF.price := efPrice_prim

/-- `EF.add` is primitive recursive in both arguments. -/
lemma efAdd_primrec : Primrec₂ EF.add := efAdd_prim

/-- `EF.mul` is primitive recursive in both arguments. -/
lemma efMul_primrec : Primrec₂ EF.mul := efMul_prim

/-- `EF.max` is primitive recursive in both arguments. -/
lemma efMax_primrec : Primrec₂ EF.max := efMax_prim

/-- `EF.absBound` is primitive recursive.  A downstream trader that sizes its position
against the ordinary aggregate's syntactic bound needs this. -/
lemma efAbsBound_primrec : Primrec EF.absBound := efAbsBound_prim

/-- The day error schedule is primitive recursive. -/
lemma marketMakerError_primrec : Primrec marketMakerError := marketMakerError_prim

/-- A belief state's exact rational quote is primitive recursive. -/
lemma rationalBeliefStateQuote_primrec : Primrec₂ RationalBeliefState.quote :=
  rationalBeliefStateQuote_prim

/-- The bounded deductive-stage prefix decoder is primitive recursive. -/
lemma processStagePrefixAtFuel_primrec {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Primrec₂ fun fuel n => processStagePrefixAtFuel process fuel n :=
  processStagePrefixAtFuel_prim process

/-- The Trading Firm's day-`n` trade list is primitive recursive in the decoded stage
prefix, the prior belief states and the day. -/
lemma tradingFirmTradesFromStageTradeLists_primrec :
    Primrec fun p : (List (Finset Sentence) × List RationalBeliefState) × ℕ =>
      tradingFirmTradesFromStageTradeLists
        (decodedStageTable p.1.1) (rationalHistory p.1.2) p.2 :=
  tradingFirmTradesFromStageTradeLists_prim

/-- The bounded MarketMaker search over a raw trade list is primitive recursive in the
trade list, the day, the prior states, the tolerance and the fuel. -/
lemma marketMakerSearchUpToTradeList_primrec :
    Primrec fun p : (((List (EF × Sentence) × ℕ) × List RationalBeliefState) × ℚ) × ℕ =>
      marketMakerSearchUpToTradeList p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 :=
  marketMakerSearchUpToTradeList_prim

/-! ### Finite propositional evaluation on an atom list

A downstream development that builds a *region of credences* from the deductive stage has
to decide, as a primitive recursive function of finite data, which Boolean assignments to
the atoms occurring in a stage satisfy that stage.  The Budgeter's own compiler settles
exactly that, in erased atom-list form; this block states the same facts against the
public `Sentence.atoms` / `sentenceBool` / `tableConsistent` vocabulary (all three from
`Budgeter`, with `supportSentenceList` from `MarketMaker`), so that a caller need not
rebuild the strong-recursion tower over the formula encoding.  The two definitions below
name the erased forms; the computability facts are the erased lemmas at those names. -/

/-- **The canonical sentence list of a finite sentence set is primitive recursive.** -/
lemma supportSentenceList_primrec : Primrec supportSentenceList :=
  supportSentenceList_prim

/-- The atoms occurring in a list of sentences, as a list rather than a `Finset`, so that
a computability statement can mention it. -/
def sentenceListAtoms (sentences : List Sentence) : List ℕ :=
  sentenceListAtomOccurrences sentences

@[simp] lemma mem_sentenceListAtoms (sentences : List Sentence) (a : ℕ) :
    a ∈ sentenceListAtoms sentences ↔ ∃ φ ∈ sentences, a ∈ φ.atoms :=
  mem_sentenceListAtomOccurrences sentences a

/-- The atom list of a list of sentences is primitive recursive. -/
lemma sentenceListAtoms_primrec : Primrec sentenceListAtoms :=
  sentenceListAtomOccurrences_prim

/-- The Boolean atom table that a list of atoms and a list of bits determine: the `i`-th
bit is the value of the `i`-th listed atom, and an unlisted atom is `false`. -/
def atomTableFromList (atoms : List ℕ) (xs : List Bool) : ℕ → Bool :=
  atomListTable atoms xs

/-- The table reads the bit at the atom's position, and `false` off the list. -/
lemma atomTableFromList_apply (atoms : List ℕ) (xs : List Bool) (a : ℕ) :
    atomTableFromList atoms xs a =
      if a ∈ atoms then xs.getD (atoms.idxOf a) false else false := rfl

private lemma tableConsistent_atomTableFromList_eq (atoms : List ℕ) (xs : List Bool)
    (D : Finset Sentence) :
    tableConsistentFromAtomList atoms xs D = tableConsistent (atomTableFromList atoms xs) D := by
  have hfold : ∀ l : List Sentence,
      (l.foldr (fun φ ok => sentenceBoolFromAtomList atoms xs φ && ok) true = true ↔
        ∀ φ ∈ l, sentenceBoolFromAtomList atoms xs φ = true) := by
    intro l
    induction l with
    | nil => simp
    | cons φ l ih => simp [ih]
  rw [Bool.eq_iff_iff]
  simp only [tableConsistentFromAtomList, tableConsistent, decide_eq_true_eq, hfold]
  simp [supportSentenceList, sentenceBoolFromAtomList, atomTableFromList]

/-- Propositional evaluation against an atom-list table is primitive recursive.  With
`boolPayoutRat u φ = if sentenceBool u φ then 1 else 0` this also settles the payout a
Boolean assignment gives a sentence. -/
lemma sentenceBool_atomTableFromList_primrec :
    Primrec fun p : (List ℕ × List Bool) × Sentence =>
      sentenceBool (atomTableFromList p.1.1 p.1.2) p.2 :=
  sentenceBoolFromAtomList_prim

/-- The enumeration of all Boolean lists of a given length is primitive recursive.  A
downstream construction enumerating the assignments to a stage's atoms needs it. -/
lemma allBoolLists_primrec : Primrec allBoolLists :=
  allBoolLists_prim

/-- **Finite consistency against an atom-list table is primitive recursive.**  This is what
lets a downstream construction enumerate the Boolean assignments a deductive stage admits,
uniformly in the stage. -/
lemma tableConsistent_atomTableFromList_primrec :
    Primrec fun p : (List ℕ × List Bool) × Finset Sentence =>
      tableConsistent (atomTableFromList p.1.1 p.1.2) p.2 :=
  tableConsistentFromAtomList_prim.of_eq fun p =>
    tableConsistent_atomTableFromList_eq p.1.1 p.1.2 p.2

end LogicalInduction
