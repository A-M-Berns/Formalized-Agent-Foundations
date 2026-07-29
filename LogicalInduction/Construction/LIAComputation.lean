import LogicalInduction.Construction.LIA

/-!
# Bounded executable presentation of LIA

This file separates the finite, total evaluator used by the eventual partial-recursive
market code from the noncomputable stopping clocks used to prove that it terminates.  A
single fuel bound first decodes the required deductive stages and then runs the exact
finite TradingFirm/MarketMaker recursion.
-/

namespace LogicalInduction

/-- Decode stages `0,…,n-1` using one common interpreter bound. -/
def processStagePrefixAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (fuel : ℕ) :
    ℕ → Option (List (Finset Sentence))
  | 0 => some []
  | n + 1 => do
      let accumulated ← processStagePrefixAtFuel process fuel n
      let stage ← process.stageAtFuel fuel n
      some (accumulated ++ [stage])

/-- Read a decoded finite stage prefix, returning the empty set outside the prefix. -/
def decodedStageTable (stages : List (Finset Sentence)) : ℕ → Finset Sentence :=
  fun n => stages.getD n ∅

lemma processStagePrefixAtFuel_sound {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (fuel n : ℕ)
    {stages : List (Finset Sentence)}
    (h : processStagePrefixAtFuel process fuel n = some stages) :
    stages.length = n ∧
      ∀ m, m < n → decodedStageTable stages m = DP.D m := by
  induction n generalizing stages with
  | zero =>
      simp [processStagePrefixAtFuel] at h
      subst stages
      simp [decodedStageTable]
  | succ n ih =>
      simp only [processStagePrefixAtFuel] at h
      change Option.bind (processStagePrefixAtFuel process fuel n)
        (fun accumulated => Option.bind (process.stageAtFuel fuel n)
          (fun stage => some (accumulated ++ [stage]))) = some stages at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨accumulated, haccumulated, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨stage, hstage, hout⟩ := h
      cases hout
      have hp := ih haccumulated
      have hs := process.stageAtFuel_sound hstage
      subst stage
      constructor
      · simp [hp.1]
      · intro m hm
        by_cases hmn : m < n
        · unfold decodedStageTable
          rw [List.getD_append _ _ _ _ (by simpa [hp.1] using hmn)]
          exact hp.2 m hmn
        · have hmeq : m = n := by omega
          subst m
          simp [decodedStageTable, hp.1]

lemma processStagePrefixAtFuel_mono_success {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (n : ℕ)
    {fuel fuel' : ℕ} {stages : List (Finset Sentence)}
    (hff : fuel ≤ fuel')
    (h : processStagePrefixAtFuel process fuel n = some stages) :
    processStagePrefixAtFuel process fuel' n = some stages := by
  induction n generalizing stages with
  | zero => simpa [processStagePrefixAtFuel] using h
  | succ n ih =>
      simp only [processStagePrefixAtFuel] at h ⊢
      change Option.bind (processStagePrefixAtFuel process fuel n)
        (fun accumulated => Option.bind (process.stageAtFuel fuel n)
          (fun stage => some (accumulated ++ [stage]))) = some stages at h
      change Option.bind (processStagePrefixAtFuel process fuel' n)
        (fun accumulated => Option.bind (process.stageAtFuel fuel' n)
          (fun stage => some (accumulated ++ [stage]))) = some stages
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨accumulated, haccumulated, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨stage, hstage, hout⟩ := h
      cases hout
      rw [ih haccumulated]
      rw [process.stageAtFuel_mono hff hstage]
      rfl

lemma exists_processStagePrefixAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (n : ℕ) :
    ∃ fuel stages, processStagePrefixAtFuel process fuel n = some stages := by
  induction n with
  | zero => exact ⟨0, [], rfl⟩
  | succ n ih =>
      obtain ⟨fuel₁, stages, hstages⟩ := ih
      obtain ⟨fuel₂, hstage⟩ := process.stageAtFuel_complete n
      let fuel := max fuel₁ fuel₂
      refine ⟨fuel, stages ++ [DP.D n], ?_⟩
      simp only [processStagePrefixAtFuel]
      rw [processStagePrefixAtFuel_mono_success process n
        (Nat.le_max_left fuel₁ fuel₂) hstages]
      rw [process.stageAtFuel_mono (Nat.le_max_right fuel₁ fuel₂) hstage]
      rfl

/-- Run `n` days of the exact finite LIA recurrence using an explicit stage table and one
common MarketMaker search bound. -/
def liaPrefixFromStagesAtFuel (D : ℕ → Finset Sentence) (fuel : ℕ) :
    ℕ → Option (List RationalBeliefState)
  | 0 => some []
  | n + 1 => do
      let past ← liaPrefixFromStagesAtFuel D fuel n
      let state ← marketMakerSearchUpTo
        (TradingFirmAtFromStages D (rationalHistory past) n) past
        (marketMakerError n) fuel
      some (past ++ [state])

/-- First-order Boolean-list presentation of the same bounded recurrence. -/
def liaPrefixFromStageListsAtFuel (D : ℕ → Finset Sentence) (fuel : ℕ) :
    ℕ → Option (List RationalBeliefState)
  | 0 => some []
  | n + 1 => do
      let past ← liaPrefixFromStageListsAtFuel D fuel n
      let state ← marketMakerSearchUpToFromLists
        (TradingFirmAtFromStageLists D (rationalHistory past) n) past
        (marketMakerError n) fuel
      some (past ++ [state])

lemma liaPrefixFromStageListsAtFuel_eq (D : ℕ → Finset Sentence)
    (fuel n : ℕ) :
    liaPrefixFromStageListsAtFuel D fuel n = liaPrefixFromStagesAtFuel D fuel n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [liaPrefixFromStageListsAtFuel, liaPrefixFromStagesAtFuel, ih]
      apply Option.bind_congr
      intro past hpast
      rw [TradingFirmAtFromStageLists_eq, marketMakerSearchUpToFromLists_eq]

/-- Fully erased bounded LIA recurrence.  Its recursive state, firm action, and
MarketMaker search all use fixed first-order data types. -/
def liaPrefixFromTradeListsAtFuel (D : ℕ → Finset Sentence) (fuel : ℕ) :
    ℕ → Option (List RationalBeliefState)
  | 0 => some []
  | n + 1 => do
      let past ← liaPrefixFromTradeListsAtFuel D fuel n
      let state ← marketMakerSearchUpToTradeList
        (tradingFirmTradesFromStageTradeLists D (rationalHistory past) n) n past
        (marketMakerError n) fuel
      some (past ++ [state])

lemma liaPrefixFromTradeListsAtFuel_eq (D : ℕ → Finset Sentence)
    (fuel n : ℕ) :
    liaPrefixFromTradeListsAtFuel D fuel n =
      liaPrefixFromStageListsAtFuel D fuel n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [liaPrefixFromTradeListsAtFuel, liaPrefixFromStageListsAtFuel, ih]
      apply Option.bind_congr
      intro past hpast
      rw [tradingFirmTradesFromStageTradeLists_eq,
        marketMakerSearchUpToTradeList_eq]

/-- Canonical append-form prefix of the semantic LIA states. -/
noncomputable def liaStatePrefix (DP : DeductiveProcess) :
    ℕ → List RationalBeliefState
  | 0 => []
  | n + 1 => liaStatePrefix DP n ++ [liaStates DP n]

@[simp] theorem liaStatePrefix_length (DP : DeductiveProcess) (n : ℕ) :
    (liaStatePrefix DP n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [liaStatePrefix, ih]

lemma liaStatePrefix_getD (DP : DeductiveProcess) {n m : ℕ}
    (hm : m < n) :
    (liaStatePrefix DP n).getD m (liaStates DP 0) = liaStates DP m := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [liaStatePrefix]
      by_cases hmn : m < n
      · rw [List.getD_append _ _ _ _ (by simpa using hmn)]
        exact ih hmn
      · have hmeq : m = n := by omega
        subst m
        simp [liaStatePrefix_length]

lemma liaStatePrefix_eq_ofFn (DP : DeductiveProcess) (n : ℕ) :
    liaStatePrefix DP n = List.ofFn fun i : Fin n => liaStates DP i := by
  apply List.ext_getElem
  · simp [liaStatePrefix_length]
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn]
    rw [← List.getD_eq_getElem (liaStatePrefix DP n) (liaStates DP 0) hi₁]
    apply liaStatePrefix_getD DP
    simpa [liaStatePrefix_length] using hi₁

lemma liaPrefixFromStagesAtFuel_mono_success
    (D : ℕ → Finset Sentence) (n : ℕ)
    {fuel fuel' : ℕ} {states : List RationalBeliefState}
    (hff : fuel ≤ fuel')
    (h : liaPrefixFromStagesAtFuel D fuel n = some states) :
    liaPrefixFromStagesAtFuel D fuel' n = some states := by
  induction n generalizing states with
  | zero => simpa [liaPrefixFromStagesAtFuel] using h
  | succ n ih =>
      simp only [liaPrefixFromStagesAtFuel] at h ⊢
      change Option.bind (liaPrefixFromStagesAtFuel D fuel n)
        (fun past => Option.bind
          (marketMakerSearchUpTo
            (TradingFirmAtFromStages D (rationalHistory past) n) past
            (marketMakerError n) fuel)
          (fun state => some (past ++ [state]))) = some states at h
      change Option.bind (liaPrefixFromStagesAtFuel D fuel' n)
        (fun past => Option.bind
          (marketMakerSearchUpTo
            (TradingFirmAtFromStages D (rationalHistory past) n) past
            (marketMakerError n) fuel')
          (fun state => some (past ++ [state]))) = some states
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨past, hpast, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨state, hstate, hout⟩ := h
      cases hout
      rw [ih hpast]
      simp only [Option.bind_some]
      rw [marketMakerSearchUpTo_mono_success _ _ _ hff hstate]
      rfl

lemma exists_liaPrefixFromStagesAtFuel
    (D : ℕ → Finset Sentence) (n : ℕ) :
    ∃ fuel states, liaPrefixFromStagesAtFuel D fuel n = some states := by
  induction n with
  | zero => exact ⟨0, [], rfl⟩
  | succ n ih =>
      obtain ⟨fuel₁, past, hpast⟩ := ih
      let T := TradingFirmAtFromStages D (rationalHistory past) n
      let fuel₂ := marketMakerIndex T past (marketMakerError n)
        (marketMakerError_pos n) + 1
      let fuel := max fuel₁ fuel₂
      refine ⟨fuel, past ++ [MarketMaker T past (marketMakerError n)
        (marketMakerError_pos n)], ?_⟩
      simp only [liaPrefixFromStagesAtFuel]
      change Option.bind (liaPrefixFromStagesAtFuel D fuel n)
        (fun prior => Option.bind
          (marketMakerSearchUpTo
            (TradingFirmAtFromStages D (rationalHistory prior) n) prior
            (marketMakerError n) fuel)
          (fun state => some (prior ++ [state]))) = _
      rw [liaPrefixFromStagesAtFuel_mono_success D n
        (Nat.le_max_left fuel₁ fuel₂) hpast]
      change Option.bind (marketMakerSearchUpTo T past (marketMakerError n) fuel)
        (fun state => some (past ++ [state])) = _
      rw [MarketMaker_search_of_clock_le T past (marketMakerError n)
        (marketMakerError_pos n) (Nat.le_max_right fuel₁ fuel₂)]
      rfl

/-- Every successful bounded state-prefix computation is the unique semantic LIA prefix. -/
lemma liaPrefixFromStagesAtFuel_sound (DP : DeductiveProcess)
    (D : ℕ → Finset Sentence) (fuel n : ℕ)
    (hD : ∀ m, m < n → D m = DP.D m)
    {states : List RationalBeliefState}
    (h : liaPrefixFromStagesAtFuel D fuel n = some states) :
    states = liaStatePrefix DP n := by
  induction n generalizing states with
  | zero =>
      simp [liaPrefixFromStagesAtFuel] at h
      subst states
      rfl
  | succ n ih =>
      simp only [liaPrefixFromStagesAtFuel] at h
      change Option.bind (liaPrefixFromStagesAtFuel D fuel n)
        (fun past => Option.bind
          (marketMakerSearchUpTo
            (TradingFirmAtFromStages D (rationalHistory past) n) past
            (marketMakerError n) fuel)
          (fun state => some (past ++ [state]))) = some states at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨past, hpast, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨state, hstate, hout⟩ := h
      cases hout
      have hpastEq := ih (fun m hm => hD m (by omega)) hpast
      subst past
      have hfirm :
          TradingFirmAtFromStages D
              (rationalHistory (liaStatePrefix DP n)) n =
            TradingFirmAt DP (rationalHistory (liaStatePrefix DP n)) n :=
        TradingFirmAtFromStages_eq_of_eq_prefix DP D _ n
          (fun m hm => hD m (by omega))
      have hstateEq := MarketMaker_searchUpTo_sound
        (TradingFirmAtFromStages D
          (rationalHistory (liaStatePrefix DP n)) n)
        (liaStatePrefix DP n) (marketMakerError n) (marketMakerError_pos n) hstate
      rw [hfirm, liaStatePrefix_eq_ofFn] at hstateEq
      have hlia : state = liaStates DP n := by
        rw [liaStates]
        exact hstateEq
      rw [hlia]
      rfl

/-- One bounded end-to-end run: decode the required deductive stages, then execute the
finite LIA recurrence with the same common fuel bound. -/
def liaPrefixAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (fuel n : ℕ) :
    Option (List RationalBeliefState) := do
  let stages ← processStagePrefixAtFuel process fuel n
  liaPrefixFromStagesAtFuel (decodedStageTable stages) fuel n

lemma liaPrefixAtFuel_mono_success {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (n : ℕ)
    {fuel fuel' : ℕ} {states : List RationalBeliefState}
    (hff : fuel ≤ fuel') (h : liaPrefixAtFuel process fuel n = some states) :
    liaPrefixAtFuel process fuel' n = some states := by
  unfold liaPrefixAtFuel at h ⊢
  change Option.bind (processStagePrefixAtFuel process fuel n)
    (fun stages => liaPrefixFromStagesAtFuel (decodedStageTable stages) fuel n) =
      some states at h
  change Option.bind (processStagePrefixAtFuel process fuel' n)
    (fun stages => liaPrefixFromStagesAtFuel (decodedStageTable stages) fuel' n) =
      some states
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨stages, hstages, hstates⟩ := h
  rw [processStagePrefixAtFuel_mono_success process n hff hstages]
  exact liaPrefixFromStagesAtFuel_mono_success
    (decodedStageTable stages) n hff hstates

lemma liaPrefixAtFuel_sound {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (fuel n : ℕ)
    {states : List RationalBeliefState}
    (h : liaPrefixAtFuel process fuel n = some states) :
    states = liaStatePrefix DP n := by
  unfold liaPrefixAtFuel at h
  change Option.bind (processStagePrefixAtFuel process fuel n)
    (fun stages => liaPrefixFromStagesAtFuel (decodedStageTable stages) fuel n) =
      some states at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨stages, hstages, hstates⟩ := h
  have hstageSound := processStagePrefixAtFuel_sound process fuel n hstages
  exact liaPrefixFromStagesAtFuel_sound DP (decodedStageTable stages) fuel n
    hstageSound.2 hstates

lemma exists_liaPrefixAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (n : ℕ) :
    ∃ fuel states, liaPrefixAtFuel process fuel n = some states := by
  obtain ⟨fuel₁, stages, hstages⟩ := exists_processStagePrefixAtFuel process n
  obtain ⟨fuel₂, states, hstates⟩ :=
    exists_liaPrefixFromStagesAtFuel (decodedStageTable stages) n
  let fuel := max fuel₁ fuel₂
  refine ⟨fuel, states, ?_⟩
  unfold liaPrefixAtFuel
  change Option.bind (processStagePrefixAtFuel process fuel n)
    (fun decoded => liaPrefixFromStagesAtFuel (decodedStageTable decoded) fuel n) =
      some states
  rw [processStagePrefixAtFuel_mono_success process n
    (Nat.le_max_left fuel₁ fuel₂) hstages]
  exact liaPrefixFromStagesAtFuel_mono_success
    (decodedStageTable stages) n (Nat.le_max_right fuel₁ fuel₂) hstates

/-- Bounded evaluator for the day-`n` belief state itself.  It returns the exact finite
association list of `liaStates DP n`, and `none` only while the common process/MM clock is
too small.  The argument order is the one used by `Partrec.rfindOpt`: the day is the input
and the fuel is the search variable. -/
def liaEncodedEntriesAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (n fuel : ℕ) : Option ℕ := do
  let states ← liaPrefixAtFuel process fuel (n + 1)
  let state ← states[n]?
  some (Encodable.encode state.entries)

lemma liaEncodedEntriesAtFuel_sound {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) {n fuel out : ℕ}
    (h : liaEncodedEntriesAtFuel process n fuel = some out) :
    out = Encodable.encode (liaStates DP n).entries := by
  unfold liaEncodedEntriesAtFuel at h
  change Option.bind (liaPrefixAtFuel process fuel (n + 1))
    (fun states => Option.bind states[n]?
      (fun state => some (Encodable.encode state.entries))) = some out at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨states, hstates, h⟩ := h
  have hstatesEq := liaPrefixAtFuel_sound process fuel (n + 1) hstates
  subst states
  rw [liaStatePrefix_eq_ofFn] at h
  simp only [List.getElem?_ofFn] at h
  simpa using h.symm

lemma exists_liaEncodedEntriesAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (n : ℕ) :
    ∃ fuel, liaEncodedEntriesAtFuel process n fuel =
      some (Encodable.encode (liaStates DP n).entries) := by
  obtain ⟨fuel, states, hstates⟩ := exists_liaPrefixAtFuel process (n + 1)
  have hstatesEq := liaPrefixAtFuel_sound process fuel (n + 1) hstates
  subst states
  refine ⟨fuel, ?_⟩
  unfold liaEncodedEntriesAtFuel
  rw [hstates]
  change Option.bind (some (liaStatePrefix DP (n + 1)))
    (fun states => Option.bind states[n]?
      (fun state => some (Encodable.encode state.entries))) = _
  simp only [Option.bind_some]
  have hn : n < (liaStatePrefix DP (n + 1)).length := by
    simp [liaStatePrefix_length]
  rw [List.getElem?_eq_getElem hn]
  have hget : (liaStatePrefix DP (n + 1))[n] = liaStates DP n := by
    rw [← List.getD_eq_getElem (liaStatePrefix DP (n + 1))
      (liaStates DP 0) hn]
    exact liaStatePrefix_getD DP (by omega)
  rw [hget]
  rfl

/-- Exact rational quote on arbitrary natural sentence codes; malformed codes are assigned
zero, as permitted by `ComputableMarket`'s total external table. -/
noncomputable def liaEncodedQuote (DP : DeductiveProcess)
    (day sentenceCode : ℕ) : ℚ :=
  match Encodable.decode (α := Sentence) sentenceCode with
  | some phi => liaQuote DP day phi
  | none => 0

/-- Bounded exact quote evaluator.  It returns `none` only while the common process/MM
clock is too small. -/
def liaEncodedQuoteAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (fuel day sentenceCode : ℕ) :
    Option ℚ := do
  let states ← liaPrefixAtFuel process fuel (day + 1)
  let state ← states[day]?
  some <| match Encodable.decode (α := Sentence) sentenceCode with
    | some phi => state.quote phi
    | none => 0

lemma liaEncodedQuoteAtFuel_sound {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) {fuel day sentenceCode : ℕ} {q : ℚ}
    (h : liaEncodedQuoteAtFuel process fuel day sentenceCode = some q) :
    q = liaEncodedQuote DP day sentenceCode := by
  unfold liaEncodedQuoteAtFuel at h
  change Option.bind (liaPrefixAtFuel process fuel (day + 1))
    (fun states => Option.bind states[day]? (fun state => some <|
      match Encodable.decode (α := Sentence) sentenceCode with
      | some phi => state.quote phi
      | none => 0)) = some q at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨states, hstates, h⟩ := h
  have hstatesEq := liaPrefixAtFuel_sound process fuel (day + 1) hstates
  subst states
  rw [liaStatePrefix_eq_ofFn] at h
  simp only [List.getElem?_ofFn] at h
  cases hdecode : Encodable.decode (α := Sentence) sentenceCode with
  | none => simpa [liaEncodedQuote, hdecode] using h.symm
  | some phi =>
      simpa [liaEncodedQuote, liaQuote, hdecode] using h.symm

lemma exists_liaEncodedQuoteAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (day sentenceCode : ℕ) :
    ∃ fuel, liaEncodedQuoteAtFuel process fuel day sentenceCode =
      some (liaEncodedQuote DP day sentenceCode) := by
  obtain ⟨fuel, states, hstates⟩ := exists_liaPrefixAtFuel process (day + 1)
  have hstatesEq := liaPrefixAtFuel_sound process fuel (day + 1) hstates
  subst states
  refine ⟨fuel, ?_⟩
  unfold liaEncodedQuoteAtFuel
  rw [hstates]
  change Option.bind (some (liaStatePrefix DP (day + 1)))
    (fun states => Option.bind states[day]? (fun state => some <|
      match Encodable.decode (α := Sentence) sentenceCode with
      | some phi => state.quote phi
      | none => 0)) = some (liaEncodedQuote DP day sentenceCode)
  simp only [Option.bind_some]
  have hday : day < (liaStatePrefix DP (day + 1)).length := by
    simp [liaStatePrefix_length]
  rw [List.getElem?_eq_getElem hday]
  have hget : (liaStatePrefix DP (day + 1))[day] = liaStates DP day := by
    rw [← List.getD_eq_getElem (liaStatePrefix DP (day + 1))
      (liaStates DP 0) hday]
    exact liaStatePrefix_getD DP (by omega)
  rw [hget]
  cases hdecode : Encodable.decode (α := Sentence) sentenceCode with
  | none => simp [liaEncodedQuote, hdecode]
  | some phi => simp [liaEncodedQuote, liaQuote, hdecode]

/-- Certified stopping clock for the bounded exact quote evaluator. -/
noncomputable def liaEncodedQuoteClock {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (day sentenceCode : ℕ) : ℕ :=
  Nat.find (exists_liaEncodedQuoteAtFuel process day sentenceCode)

lemma liaEncodedQuote_clock {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (day sentenceCode : ℕ) :
    liaEncodedQuoteAtFuel process
      (liaEncodedQuoteClock process day sentenceCode) day sentenceCode =
        some (liaEncodedQuote DP day sentenceCode) :=
  Nat.find_spec (exists_liaEncodedQuoteAtFuel process day sentenceCode)

/-- Natural-coded bounded evaluator in the argument order used by `Partrec.rfindOpt`.
The paired input is `(day,sentenceCode)` and the search variable is fuel. -/
def liaEncodedQuoteNatAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (z fuel : ℕ) : Option ℕ :=
  (liaEncodedQuoteAtFuel process fuel z.unpair.1 z.unpair.2).map Encodable.encode

/-- The sole remaining compiler boundary for the core LIA construction.  It says only
that the already-defined bounded evaluator is a computable two-argument natural function;
it carries no market correctness, range, exploitation, or logical-inductor conclusion. -/
structure LIABoundedEvaluatorCompiler {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) where
  computable : Computable₂ (liaEncodedQuoteNatAtFuel process)

lemma liaEncodedQuoteNatAtFuel_sound {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) {z fuel out : ℕ}
    (h : liaEncodedQuoteNatAtFuel process z fuel = some out) :
    out = Encodable.encode (liaEncodedQuote DP z.unpair.1 z.unpair.2) := by
  unfold liaEncodedQuoteNatAtFuel at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨q, hq, rfl⟩ := h
  rw [liaEncodedQuoteAtFuel_sound process hq]

lemma exists_liaEncodedQuoteNatAtFuel {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (z : ℕ) :
    ∃ fuel, liaEncodedQuoteNatAtFuel process z fuel =
      some (Encodable.encode (liaEncodedQuote DP z.unpair.1 z.unpair.2)) := by
  obtain ⟨fuel, hfuel⟩ := exists_liaEncodedQuoteAtFuel
    process z.unpair.1 z.unpair.2
  refine ⟨fuel, ?_⟩
  unfold liaEncodedQuoteNatAtFuel
  rw [hfuel]
  rfl

/-- Generic minimization turns a compiler for the bounded evaluator into one total
partial-recursive exact quote function. -/
lemma LIABoundedEvaluatorCompiler.quote_computable
    {DP : DeductiveProcess} {process : DeductiveProcessComputation DP}
    (compiler : LIABoundedEvaluatorCompiler process) :
    Computable (fun z : ℕ =>
      Encodable.encode (liaEncodedQuote DP z.unpair.1 z.unpair.2)) := by
  let search : ℕ → Part ℕ := fun z =>
    Nat.rfindOpt (liaEncodedQuoteNatAtFuel process z)
  have hsearch : Partrec search := Partrec.rfindOpt compiler.computable
  apply hsearch.of_eq_tot
  intro z
  have hdom : (search z).Dom := by
    rw [Nat.rfindOpt_dom]
    obtain ⟨fuel, hfuel⟩ := exists_liaEncodedQuoteNatAtFuel process z
    exact ⟨fuel, _, hfuel⟩
  let out := (search z).get hdom
  have hout : out ∈ search z := Part.get_mem hdom
  obtain ⟨fuel, hfuel⟩ := Nat.rfindOpt_spec hout
  have houtEq := liaEncodedQuoteNatAtFuel_sound process hfuel
  rw [← houtEq]
  exact hout

/-- Extract the actual partial-recursive quote program promised by `ComputableMarket`. -/
lemma LIABoundedEvaluatorCompiler.exists_quote_code
    {DP : DeductiveProcess} {process : DeductiveProcessComputation DP}
    (compiler : LIABoundedEvaluatorCompiler process) :
    ∃ code : Nat.Partrec.Code, ∀ z : ℕ,
      Encodable.encode (liaEncodedQuote DP z.unpair.1 z.unpair.2) ∈ code.eval z := by
  have hcomp := compiler.quote_computable
  have hpart : Nat.Partrec (fun z : ℕ =>
      Part.some (Encodable.encode (liaEncodedQuote DP z.unpair.1 z.unpair.2))) :=
    Partrec.nat_iff.mp hcomp.partrec
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hpart
  refine ⟨code, ?_⟩
  intro z
  rw [hcode]
  simp

/-- Once the bounded evaluator compiler is instantiated, the recursive LIA history has
the exact paper-facing rational market program. -/
lemma LIABoundedEvaluatorCompiler.toComputableMarket
    {DP : DeductiveProcess} {process : DeductiveProcessComputation DP}
    (compiler : LIABoundedEvaluatorCompiler process) :
    ComputableMarket (liaHistory DP) := by
  obtain ⟨code, hcode⟩ := compiler.exists_quote_code
  refine ⟨liaHistory_range DP, liaEncodedQuote DP, code, ?_, ?_⟩
  · intro n phi
    simp [liaHistory, liaEncodedQuote, liaQuote,
      RationalBeliefState.toValuation]
  · exact hcode

/-- Exact criterion assembly from the bounded evaluator compiler.  The final M7 theorem
will instantiate `compiler`; this lemma makes clear that no further semantic premise is
missing. -/
lemma lia_isLogicalInductor_of_compiler
    {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (compiler : LIABoundedEvaluatorCompiler process) :
    IsLogicalInductor (liaHistory DP) DP :=
  lia_isLogicalInductor_of_computableMarket DP process.toComputable
    compiler.toComputableMarket

#print axioms processStagePrefixAtFuel_sound
#print axioms liaPrefixAtFuel_sound
#print axioms liaEncodedQuoteAtFuel_sound
#print axioms liaEncodedQuote_clock
#print axioms LIABoundedEvaluatorCompiler.quote_computable
#print axioms LIABoundedEvaluatorCompiler.toComputableMarket
#print axioms lia_isLogicalInductor_of_compiler

end LogicalInduction
