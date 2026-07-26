/-
# Digit-model conditioning translation (Tranche 2, B1)

The conditioning price rewrite (`conditionPriceTokenRun`, ConditioningCompiler) is a
token transducer whose emitted rewrite applies `ψCode` to the price-*day* token.  In the
digit-metered emission model (`EfficientlyComputableTok₂`) token values may be
exponential in the day, held only as digit blocks, so the transducer must **guard**:
price-day tokens are compared against the trading day `n` by digit clamp, and an
oversized day aborts the emission.  This file provides

* the correspondence between the standalone digit-side mode automaton (`freezeMode4`,
  Framework/DigitArith) and the token-side freeze control (`EF.freezeTokenNext`),
  including pending-payload recovery *by position*;
* the **guard honesty** lemma: a price-day token exceeding `n` at a mode-2 position
  forces the day-`n` validated strategy of the stream to be empty (the parser either
  rejects, or records a trade whose rank exceeds `n`) — so the empty emission realizes
  the translation on guarded days;
* the digit-model transducer itself and its `PolySegStream` certificate (the
  `conjunctionCode` bignum block is the one segment rendered from `BigDigits`).

Paper node: `thm:scon` (digit-model residual of the conditioning translation).
-/
import LogicalInduction.Construction.Witnesses.ConditioningCompiler
import LogicalInduction.Framework.DigitArith

namespace LogicalInduction

namespace ConditioningCompile

open Nat.Partrec (Code)
open Nat.Partrec.Code

-- Deep `Primrec`/`PolyFueled` compositions over paired inputs loop `whnf` on `Nat.sqrt`
-- (pair/unpair unfolding); keep it opaque throughout (the standard `dd:fuel` safeguard).
attribute [local irreducible] Nat.sqrt

/-! ## Mode-automaton correspondence

`freezeMode4` (DigitArith) is the mode component of `EF.freezeTokenNext`; the pending
payload of a mode-2 control is always the immediately preceding token. -/

lemma freezeTokenNext_fst (st : EF.FreezeTokenState) (t : ℕ) :
    (EF.freezeTokenNext st t).1 = freezeMode4Step st.1 t := by
  rcases st with ⟨m, p⟩
  match m with
  | 0 =>
      simp only [EF.freezeTokenNext, freezeMode4Step]
      split_ifs <;> rfl
  | 1 => rfl
  | (_ + 2) => rfl

lemma foldl_freezeTokenNext_fst (ts : List ℕ) :
    ∀ st : EF.FreezeTokenState,
      (ts.foldl EF.freezeTokenNext st).1 = ts.foldl freezeMode4Step st.1 := by
  induction ts with
  | nil => intro st; rfl
  | cons t rest ih =>
      intro st
      rw [List.foldl_cons, List.foldl_cons, ih, freezeTokenNext_fst]

/-- The standalone digit-side automaton computes the freeze control's mode. -/
lemma freezeMode4_eq_foldl (ts : List ℕ) :
    freezeMode4 ts = (ts.foldl EF.freezeTokenNext ((0, 0) : EF.FreezeTokenState)).1 :=
  (foldl_freezeTokenNext_fst ts (0, 0)).symm

/-- Mode `2` always stores the immediately preceding token as its pending payload. -/
lemma foldl_freezeTokenNext_snoc_mode2 (ts : List ℕ) (t : ℕ)
    (st : EF.FreezeTokenState)
    (h : ((ts ++ [t]).foldl EF.freezeTokenNext st).1 = 2) :
    (ts ++ [t]).foldl EF.freezeTokenNext st = (2, t) := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at h ⊢
  rcases hprev : ts.foldl EF.freezeTokenNext st with ⟨m, p⟩
  rw [hprev] at h
  match m with
  | 0 =>
      exfalso
      simp only [EF.freezeTokenNext] at h
      split_ifs at h <;> simp_all
  | 1 => rfl
  | (_ + 2) => exact absurd h (by simp [EF.freezeTokenNext])

/-! ## The run-level `Matches` transport

`EF.streamReadFrom_freezeTokenRun` (FinitePerturbations) proves, bundled with its
emission equations, that the freeze control tracks the parser state along every
successful run.  Instantiating its quote data trivially extracts the pure transport. -/

lemma freezeTokenRun_fst (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (st : EF.FreezeTokenState) (ts : List ℕ) :
    (EF.freezeTokenRun quoteCode cutoff st ts).1 = ts.foldl EF.freezeTokenNext st := by
  induction ts generalizing st with
  | nil => rfl
  | cons t rest ih => simp only [EF.freezeTokenRun, List.foldl_cons]; exact ih _

/-- The freeze control matches the parser state after any successful run. -/
lemma matches_streamReadFrom (ts : List ℕ) (control : EF.FreezeTokenState)
    (state next : EF.StreamState) (hmatch : control.Matches state)
    (hread : EF.streamReadFrom ts (some state) = some next) :
    (ts.foldl EF.freezeTokenNext control).Matches next := by
  have h := (EF.streamReadFrom_freezeTokenRun (fun _ _ => (0 : ℚ))
    (fun _ _ => Encodable.encode (0 : ℚ)) 0 (fun _ _ _ _ => rfl)
    control state ts hmatch).2 next hread
  rwa [freezeTokenRun_fst] at h

/-! ## Guard honesty

A price-day token `D` consumed at a mode-2 position pushes `EF.price φ D` onto the
parser stack; every later step embeds that feature (rank ≥ `D`) into the surviving
stack or the recorded trades.  A validated day-`n` strategy caps every trade rank at
`n`, so `n < D` forces the empty strategy. -/

/-- Some pending or recorded feature inspects day `D` or later. -/
def HasDay (D : ℕ) (state : EF.StreamState) : Prop :=
  (∃ e ∈ state.2.1, D ≤ EF.rank e) ∨ (∃ tr ∈ state.2.2, D ≤ tr.1.rank)

lemma HasDay.streamStep {D : ℕ} {state next : EF.StreamState} {token : ℕ}
    (h : EF.streamStep (some state) token = some next)
    (hd : HasDay D state) : HasDay D next := by
  rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
  by_cases h0 : mode = 0
  · subst mode
    simp only [EF.streamStep, if_pos] at h
    by_cases ht0 : token = 0
    · simp only [ht0, if_pos] at h
      obtain rfl := Option.some.inj h
      exact hd
    rw [if_neg ht0] at h
    by_cases ht1 : token = 1
    · simp only [ht1, if_pos] at h
      obtain rfl := Option.some.inj h
      exact hd
    rw [if_neg ht1] at h
    by_cases ht2 : token = 2
    · simp only [ht2, if_pos] at h
      rcases stack with _ | ⟨b, stack⟩
      · simp at h
      rcases stack with _ | ⟨a, rest⟩
      · simp at h
      obtain rfl := Option.some.inj h
      rcases hd with ⟨e, he, hrk⟩ | htr
      · rcases List.mem_cons.mp he with heq | he
        · exact Or.inl ⟨EF.add a b, List.mem_cons_self ..,
            le_trans (heq ▸ hrk) (le_max_right _ _)⟩
        rcases List.mem_cons.mp he with heq | he
        · exact Or.inl ⟨EF.add a b, List.mem_cons_self ..,
            le_trans (heq ▸ hrk) (le_max_left _ _)⟩
        · exact Or.inl ⟨e, List.mem_cons_of_mem _ he, hrk⟩
      · exact Or.inr htr
    rw [if_neg ht2] at h
    by_cases ht3 : token = 3
    · simp only [ht3, if_pos] at h
      rcases stack with _ | ⟨b, stack⟩
      · simp at h
      rcases stack with _ | ⟨a, rest⟩
      · simp at h
      obtain rfl := Option.some.inj h
      rcases hd with ⟨e, he, hrk⟩ | htr
      · rcases List.mem_cons.mp he with heq | he
        · exact Or.inl ⟨EF.mul a b, List.mem_cons_self ..,
            le_trans (heq ▸ hrk) (le_max_right _ _)⟩
        rcases List.mem_cons.mp he with heq | he
        · exact Or.inl ⟨EF.mul a b, List.mem_cons_self ..,
            le_trans (heq ▸ hrk) (le_max_left _ _)⟩
        · exact Or.inl ⟨e, List.mem_cons_of_mem _ he, hrk⟩
      · exact Or.inr htr
    rw [if_neg ht3] at h
    by_cases ht4 : token = 4
    · simp only [ht4, if_pos] at h
      rcases stack with _ | ⟨b, stack⟩
      · simp at h
      rcases stack with _ | ⟨a, rest⟩
      · simp at h
      obtain rfl := Option.some.inj h
      rcases hd with ⟨e, he, hrk⟩ | htr
      · rcases List.mem_cons.mp he with heq | he
        · exact Or.inl ⟨EF.max a b, List.mem_cons_self ..,
            le_trans (heq ▸ hrk) (le_max_right _ _)⟩
        rcases List.mem_cons.mp he with heq | he
        · exact Or.inl ⟨EF.max a b, List.mem_cons_self ..,
            le_trans (heq ▸ hrk) (le_max_left _ _)⟩
        · exact Or.inl ⟨e, List.mem_cons_of_mem _ he, hrk⟩
      · exact Or.inr htr
    rw [if_neg ht4] at h
    by_cases ht5 : token = 5
    · simp only [ht5, if_pos] at h
      rcases stack with _ | ⟨a, rest⟩
      · simp at h
      obtain rfl := Option.some.inj h
      rcases hd with ⟨e, he, hrk⟩ | htr
      · rcases List.mem_cons.mp he with heq | he
        · exact Or.inl ⟨EF.safeRecip a, List.mem_cons_self .., heq ▸ hrk⟩
        · exact Or.inl ⟨e, List.mem_cons_of_mem _ he, hrk⟩
      · exact Or.inr htr
    rw [if_neg ht5] at h
    by_cases ht6 : token = 6
    · simp only [ht6, if_pos] at h
      obtain rfl := Option.some.inj h
      exact hd
    rw [if_neg ht6] at h
    by_cases ht7 : token = 7
    · simp only [ht7, if_pos] at h
      obtain rfl := Option.some.inj h
      exact hd
    rw [if_neg ht7] at h
    by_cases ht8 : token = 8
    · simp only [ht8, if_pos] at h
      rcases stack with _ | ⟨body, stack⟩
      · simp at h
      rcases stack with _ | ⟨x, rest⟩
      · simp at h
      obtain rfl := Option.some.inj h
      rcases hd with ⟨e, he, hrk⟩ | htr
      · rcases List.mem_cons.mp he with heq | he
        · exact Or.inl ⟨EF.letE x body, List.mem_cons_self ..,
            le_trans (heq ▸ hrk) (le_max_right _ _)⟩
        rcases List.mem_cons.mp he with heq | he
        · exact Or.inl ⟨EF.letE x body, List.mem_cons_self ..,
            le_trans (heq ▸ hrk) (le_max_left _ _)⟩
        · exact Or.inl ⟨e, List.mem_cons_of_mem _ he, hrk⟩
      · exact Or.inr htr
    rw [if_neg ht8] at h
    exact absurd h (by simp)
  simp only [EF.streamStep] at h
  rw [if_neg h0] at h
  by_cases h1 : mode = 1
  · rw [if_pos h1] at h
    rcases hdec : Encodable.decode (α := Sentence) token with _ | φ <;>
      rw [hdec] at h
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h
      exact hd
  rw [if_neg h1] at h
  by_cases h2 : mode = 2
  · rw [if_pos h2] at h
    rcases pending with _ | φ
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h
      rcases hd with ⟨e, he, hrk⟩ | htr
      · exact Or.inl ⟨e, List.mem_cons_of_mem _ he, hrk⟩
      · exact Or.inr htr
  rw [if_neg h2] at h
  by_cases h3 : mode = 3
  · rw [if_pos h3] at h
    rcases hdec : Encodable.decode (α := ℚ) token with _ | q <;> rw [hdec] at h
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h
      rcases hd with ⟨e, he, hrk⟩ | htr
      · exact Or.inl ⟨e, List.mem_cons_of_mem _ he, hrk⟩
      · exact Or.inr htr
  rw [if_neg h3] at h
  by_cases h4 : mode = 4
  · rw [if_pos h4] at h
    rcases stack with _ | ⟨e, rest⟩
    · simp at h
    rcases hdec : Encodable.decode (α := Sentence) token with _ | φ <;>
      rw [hdec] at h
    · simp at h
    obtain rfl := Option.some.inj h
    rcases hd with ⟨e', he', hrk⟩ | ⟨tr, htr, hrk⟩
    · rcases List.mem_cons.mp he' with heq | he'
      · exact Or.inr ⟨(e, φ), List.mem_append_right _ (List.mem_singleton.mpr rfl),
          heq ▸ hrk⟩
      · exact Or.inl ⟨e', he', hrk⟩
    · exact Or.inr ⟨tr, List.mem_append_left _ htr, hrk⟩
  rw [if_neg h4] at h
  by_cases h5 : mode = 5
  · rw [if_pos h5] at h
    obtain rfl := Option.some.inj h
    rcases hd with ⟨e, he, hrk⟩ | htr
    · exact Or.inl ⟨e, List.mem_cons_of_mem _ he, hrk⟩
    · exact Or.inr htr
  rw [if_neg h5] at h
  exact absurd h (by simp)

/-- A mode-2 step captures its day token into the state. -/
lemma hasDay_of_mode2_step {state next : EF.StreamState} {token : ℕ}
    (hmode : state.1.1 = 2)
    (h : EF.streamStep (some state) token = some next) :
    HasDay token next := by
  rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
  simp only at hmode
  subst hmode
  simp only [EF.streamStep] at h
  simp only [if_neg (by norm_num : ¬ (2:ℕ) = 0), if_neg (by norm_num : ¬ (2:ℕ) = 1),
    if_pos rfl] at h
  rcases pending with _ | φ
  · exact absurd h (by simp)
  · obtain rfl := Option.some.inj h
    exact Or.inl ⟨EF.price φ token, List.mem_cons_self .., le_refl _⟩

lemma HasDay.streamReadFrom {D : ℕ} (ts : List ℕ) :
    ∀ {state next : EF.StreamState},
      EF.streamReadFrom ts (some state) = some next →
      HasDay D state → HasDay D next := by
  induction ts with
  | nil =>
      intro state next h hd
      obtain rfl := Option.some.inj h
      exact hd
  | cons t rest ih =>
      intro state next h hd
      change EF.streamReadFrom rest (EF.streamStep (some state) t) = some next at h
      cases hstep : EF.streamStep (some state) t with
      | none => rw [hstep, EF.streamReadFrom_none] at h; exact absurd h (by simp)
      | some mid =>
          rw [hstep] at h
          exact ih h (hd.streamStep hstep)

/-- **Guard honesty**: a price-day token exceeding the trading day at a mode-2 position
forces the empty validated strategy.
Paper node: `thm:scon` -/
lemma strategyOfTokens_trades_eq_nil_of_bigDay (n : ℕ) (ts : List ℕ) (j : ℕ)
    (hj : j < ts.length)
    (hmode : freezeMode4 (ts.take j) = 2)
    (hday : n < ts.getD j 0) :
    (strategyOfTokens n ts).trades = [] := by
  by_contra hne
  have hdec := deserializeTrades_eq_some_of_strategyOfTokens_trades_ne_nil n ts hne
  have hval := (strategyOfTokens n ts).rank_le
  have hready := streamReadFrom_eq_ready_of_deserializeTrades_eq_some ts
    (strategyOfTokens n ts).trades hdec
  have hsplit : ts = ts.take j ++ ts.getD j 0 :: ts.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j ts]
    congr 1
    rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem ts 0 hj]
  rw [hsplit, EF.streamReadFrom_append] at hready
  cases hmid : EF.streamReadFrom (ts.take j) (some EF.streamInitial) with
  | none =>
      rw [hmid, EF.streamReadFrom_none] at hready
      exact absurd hready (by simp)
  | some mid =>
      rw [hmid] at hready
      have hmatch := matches_streamReadFrom (ts.take j) (0, 0) EF.streamInitial mid
        EF.freezeToken_initial_matches hmid
      have hmidmode : mid.1.1 = 2 := by
        have h1 := hmatch.1
        rw [← h1, ← freezeMode4_eq_foldl]
        exact hmode
      change EF.streamReadFrom (ts.drop (j + 1))
        (EF.streamStep (some mid) (ts.getD j 0)) = _ at hready
      cases hstep : EF.streamStep (some mid) (ts.getD j 0) with
      | none =>
          rw [hstep, EF.streamReadFrom_none] at hready
          exact absurd hready (by simp)
      | some st' =>
          rw [hstep, ← hsplit] at hready
          have hfin : HasDay (ts.getD j 0) ((0, none),
              ([], (strategyOfTokens n ts).trades)) :=
            HasDay.streamReadFrom (ts.drop (j + 1)) hready
              (hasDay_of_mode2_step hmidmode hstep)
          rcases hfin with ⟨e, he, -⟩ | ⟨tr, htr, hrk⟩
          · simp at he
          · exact absurd (hval tr htr) (by omega)

/-! ## The day-guard flag

`1` iff some mode-2 position below the cursor carries a day token exceeding `n`.  The
digit transducer emits nothing on flagged days; guard honesty (above) shows the empty
emission still realizes the translation there. -/

/-- Guard flag over the virtual token stream. -/
def bigDayFlagAt (tf : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      if freezeMode4 (vpre tf n j) = 2 ∧ n < tf (Nat.pair n j) then 1
      else bigDayFlagAt tf n j

lemma bigDayFlagAt_le_one (tf : ℕ → ℕ) (n : ℕ) : ∀ j, bigDayFlagAt tf n j ≤ 1
  | 0 => by simp [bigDayFlagAt]
  | j + 1 => by
      rw [bigDayFlagAt]
      split
      · exact le_refl 1
      · exact bigDayFlagAt_le_one tf n j

lemma bigDayFlagAt_eq_zero_iff (tf : ℕ → ℕ) (n J : ℕ) :
    bigDayFlagAt tf n J = 0 ↔
      ∀ j < J, freezeMode4 (vpre tf n j) = 2 → tf (Nat.pair n j) ≤ n := by
  induction J with
  | zero => simp [bigDayFlagAt]
  | succ J ih =>
      rw [bigDayFlagAt]
      by_cases hc : freezeMode4 (vpre tf n J) = 2 ∧ n < tf (Nat.pair n J)
      · rw [if_pos hc]
        constructor
        · omega
        · intro hall
          exact absurd (hall J (by omega) hc.1) (by omega)
      · rw [if_neg hc, ih]
        constructor
        · intro hall j hj hm
          rcases Nat.lt_or_ge j J with h | h
          · exact hall j h hm
          · have hjJ : j = J := by omega
            subst hjJ
            by_contra hlt
            exact hc ⟨hm, by omega⟩
        · intro hall j hj hm
          exact hall j (by omega) hm

/-- The virtual prefix of a list's `getD` view is its `take`. -/
lemma vpre_eq_take {ts : List ℕ} {tf : ℕ → ℕ} {n : ℕ}
    (hget : ∀ i, i < ts.length → tf (Nat.pair n i) = ts.getD i 0)
    {j : ℕ} (hj : j ≤ ts.length) :
    vpre tf n j = ts.take j := by
  apply List.ext_getElem
  · simp only [vpre, List.length_map, List.length_range, List.length_take]
    omega
  · intro i h1 h2
    simp only [vpre, List.getElem_map, List.getElem_range, List.getElem_take]
    have hi : i < j := by
      simpa only [vpre, List.length_map, List.length_range] using h1
    rw [hget i (by omega)]
    exact List.getD_eq_getElem ts 0 (by omega)

/-- The guard flag is poly-fueled over any digit `PolySegStream` (input `⟨n, j⟩`):
the mode comes from the freeze scan and the day comparison from the bounded clamp. -/
lemma PolySegStream.bigDayFlagScan {s : ℕ → List ℕ} (h : PolySegStream s) :
    ∃ c, PolyFueled c (fun z =>
      bigDayFlagAt (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0)
        z.unpair.1 z.unpair.2) := by
  obtain ⟨cm, hmode⟩ := h.freezeModeScan
  obtain ⟨cd, hclamp⟩ := h.dayClampTokens
  obtain ⟨cad, had⟩ := addc_polyFueled
  -- Step input `⟨n, ⟨j, prev⟩⟩`.
  have hn := PolyFueled.left
  have hj := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hmz := hmode.comp (hn.pair hj)
  have hdz := hclamp.comp (hn.pair hj)
  have heq2 := had.comp ((subc_polyFueled.comp (hmz.pair (PolyFueled.const 2))).pair
    (subc_polyFueled.comp ((PolyFueled.const 2).pair hmz)))
  have hexcess := subc_polyFueled.comp (hdz.pair hn)
  have hinner := ifzSel_polyFueled.comp ((hexcess.pair (PolyFueled.const 0)).pair heq2)
  have hstep := ifzSel_polyFueled.comp ((hprev.pair (PolyFueled.const 1)).pair hinner)
  refine ⟨_, PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun n j => bigDayFlagAt
      (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0) n j)
    (fun n => rfl)
    (fun n j => ?_)
    ((IsPolyBounded.linear 1).of_le fun z =>
      le_trans (bigDayFlagAt_le_one _ _ _) (by omega))⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  rw [bigDayFlagAt]
  set tf : ℕ → ℕ := fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0 with htf
  have htfj : tf (Nat.pair n j) = (undigitize (s n)).getD j 0 := by
    rw [htf]
    simp only [Nat.unpair_pair]
  rw [← htfj]
  by_cases hm : freezeMode4 (vpre tf n j) = 2
  · have heq2z : freezeMode4 (vpre tf n j) - 2 + (2 - freezeMode4 (vpre tf n j)) = 0 := by
      omega
    rw [if_pos heq2z]
    by_cases hd : n < tf (Nat.pair n j)
    · rw [if_pos ⟨hm, hd⟩, Nat.min_eq_right (by omega : n + 1 ≤ tf (Nat.pair n j)),
        if_neg (by omega : ¬ n + 1 - n = 0)]
    · rw [if_neg (by tauto : ¬ (freezeMode4 (vpre tf n j) = 2 ∧ n < tf (Nat.pair n j))),
        Nat.min_eq_left (by omega : tf (Nat.pair n j) ≤ n + 1),
        if_pos (by omega : tf (Nat.pair n j) - n = 0)]
  · rw [if_neg (by tauto : ¬ (freezeMode4 (vpre tf n j) = 2 ∧ n < tf (Nat.pair n j))),
      if_neg (by omega : ¬ freezeMode4 (vpre tf n j) - 2 +
        (2 - freezeMode4 (vpre tf n j)) = 0),
      if_pos rfl]

/-! ## Segment identities

The token-model segment (`conditionPriceTokenSegment`) branches on the freeze control;
re-expressed through `freezeMode4` and position-recovered pending, its digitization
splits around the single bignum token `conjunctionCode pending ψc`. -/

lemma freezeTokenControlAt_eq_foldl (tf : ℕ → ℕ) (n : ℕ) : ∀ j,
    EF.freezeTokenControlAt tf n j = (vpre tf n j).foldl EF.freezeTokenNext (0, 0)
  | 0 => rfl
  | j + 1 => by
      rw [EF.freezeTokenControlAt, freezeTokenControlAt_eq_foldl tf n j, vpre_succ,
        List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma freezeTokenControlAt_fst (tf : ℕ → ℕ) (n j : ℕ) :
    (EF.freezeTokenControlAt tf n j).1 = freezeMode4 (vpre tf n j) := by
  rw [freezeTokenControlAt_eq_foldl, freezeMode4_eq_foldl]

/-- Position recovery: a mode-2 control at `j + 1` pends exactly the token at `j`. -/
lemma freezeTokenControlAt_mode2 (tf : ℕ → ℕ) (n j : ℕ)
    (h : (EF.freezeTokenControlAt tf n (j + 1)).1 = 2) :
    EF.freezeTokenControlAt tf n (j + 1) = (2, tf (Nat.pair n j)) := by
  rw [freezeTokenControlAt_eq_foldl] at h ⊢
  rw [vpre_succ] at h ⊢
  exact foldl_freezeTokenNext_snoc_mode2 _ _ _ h

/-- The token-model segment through the digit-side control view. -/
lemma conditionPriceTokenSegment_eq (tf ψCode : ℕ → ℕ) (ε : ℚ) (n j : ℕ) :
    conditionPriceTokenSegment tf ψCode ε (Nat.pair n j) =
      if freezeMode4 (vpre tf n j) = 2 then
        [tf (Nat.pair n j)] ++ rawConditionalPriceTokens (tf (Nat.pair n (j - 1)))
          (ψCode (tf (Nat.pair n j))) (tf (Nat.pair n j)) ε ++ [8]
      else [tf (Nat.pair n j)] := by
  have hfst : (PrefixPatchCompile.freezeControlNat tf (Nat.pair n j)).unpair.1 =
      freezeMode4 (vpre tf n j) := by
    rw [PrefixPatchCompile.freezeControlNat]
    simp only [Nat.unpair_pair]
    exact freezeTokenControlAt_fst tf n j
  by_cases hm : freezeMode4 (vpre tf n j) = 2
  · rw [if_pos hm]
    match j with
    | 0 => exact absurd hm (by simp [vpre, freezeMode4])
    | j + 1 =>
        have hctrl := freezeTokenControlAt_mode2 tf n j (by
          have := freezeTokenControlAt_fst tf n (j + 1)
          omega)
        simp only [conditionPriceTokenSegment, PrefixPatchCompile.freezeControlNat,
          Nat.unpair_pair]
        rw [hctrl]
        norm_num
  · rw [if_neg hm]
    simp only [conditionPriceTokenSegment]
    rw [hfst]
    by_cases h0 : freezeMode4 (vpre tf n j) = 0
    · rw [if_pos h0]
    rw [if_neg h0]
    by_cases h1 : freezeMode4 (vpre tf n j) = 1
    · rw [if_pos h1]
    rw [if_neg h1, if_neg hm]

/-- The digitized long segment splits around its one bignum token
(`conjunctionCode pending ψc`); every other token is either the (clampable) day, a
fixed rational literal, or the poly condition code. -/
lemma longSegment_tokens (P ψc D : ℕ) (ε : ℚ) :
    [D] ++ rawConditionalPriceTokens P ψc D ε ++ [8] =
      ([D, 1, Encodable.encode (-1 : ℚ), 1, Encodable.encode (-1 : ℚ),
          1, Encodable.encode (1 : ℚ), 3, 1, Encodable.encode (-1 : ℚ), 0] ++
        [conjunctionCode P ψc]) ++
        [D, 1, Encodable.encode (1 / ε : ℚ), 1, Encodable.encode (1 / ε : ℚ),
          0, ψc, D, 3, 5, 3, 3, 3, 4, 3, 8] := by
  simp [rawConditionalPriceTokens, rawMinTokens, rawMulTokens, rawMaxTokens,
    rawSafeRecipTokens, rawConstTokens, rawPriceTokens, rawLowerSafeRecipTokens]

@[simp] lemma digitize_append (xs ys : List ℕ) :
    digitize (xs ++ ys) = digitize xs ++ digitize ys := by
  simp [digitize]

@[simp] lemma digitize_singleton (t : ℕ) : digitize [t] = tokenBlock t := by
  simp [digitize]

/-! ## The guarded rewrite (specification) -/

/-- The guarded token-level price rewrite: the ordinary conditioning rewrite when every
price-day token is within the trading day, the empty stream otherwise. -/
def guardedConditionTokens (ψCode : ℕ → ℕ) (ε : ℚ) (n : ℕ) (ts : List ℕ) : List ℕ :=
  if ∀ j < ts.length, freezeMode4 (ts.take j) = 2 → ts.getD j 0 ≤ n
  then (conditionPriceTokenRun ψCode ε (0, 0) ts).2
  else []

/-! ## The digit-model emitters -/

/-- The digitized long segment is a `PolySegStream` given poly day/condition emitters
and digit access to the pending code: the conjunction shell
`conjunctionCode pending ψc` is the one bignum block, rendered by `BigDigits`. -/
lemma longEmit_polySegStream {cD cC : Code} {pnd D ψc : ℕ → ℕ}
    (hpnd : BigDigits pnd) (hD : PolyFueled cD D) (hψc : PolyFueled cC ψc) (ε : ℚ) :
    PolySegStream (fun z =>
      digitize ([D z] ++ rawConditionalPriceTokens (pnd z) (ψc z) (D z) ε ++ [8])) := by
  have hconj : BigDigits (fun z => conjunctionCode (pnd z) (ψc z)) := by
    have hshell :=
      ((BigDigits.const 3).natPair (hpnd.natPair (BigDigits.of_polyFueled hψc))).succ
    exact hshell.of_eq fun z => by rw [conjunctionCode]
  have hA : PolyTokenStream (fun z =>
      [D z, 1, Encodable.encode (-1 : ℚ), 1, Encodable.encode (-1 : ℚ),
        1, Encodable.encode (1 : ℚ), 3, 1, Encodable.encode (-1 : ℚ), 0]) := by
    refine ⟨[D, fun _ => 1, fun _ => Encodable.encode (-1 : ℚ), fun _ => 1,
      fun _ => Encodable.encode (-1 : ℚ), fun _ => 1,
      fun _ => Encodable.encode (1 : ℚ), fun _ => 3, fun _ => 1,
      fun _ => Encodable.encode (-1 : ℚ), fun _ => 0],
      fun n => rfl, fun t ht => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, hD⟩
    all_goals exact ⟨_, PolyFueled.const _⟩
  have hB : PolyTokenStream (fun z =>
      [D z, 1, Encodable.encode (1 / ε : ℚ), 1, Encodable.encode (1 / ε : ℚ),
        0, ψc z, D z, 3, 5, 3, 3, 3, 4, 3, 8]) := by
    refine ⟨[D, fun _ => 1, fun _ => Encodable.encode (1 / ε : ℚ), fun _ => 1,
      fun _ => Encodable.encode (1 / ε : ℚ), fun _ => 0, ψc, D, fun _ => 3,
      fun _ => 5, fun _ => 3, fun _ => 3, fun _ => 3, fun _ => 4, fun _ => 3,
      fun _ => 8],
      fun n => rfl, fun t ht => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, hD⟩
    · exact ⟨_, PolyFueled.const _⟩
    · exact ⟨_, PolyFueled.const _⟩
    · exact ⟨_, PolyFueled.const _⟩
    · exact ⟨_, PolyFueled.const _⟩
    · exact ⟨_, PolyFueled.const _⟩
    · exact ⟨_, hψc⟩
    · exact ⟨_, hD⟩
    all_goals exact ⟨_, PolyFueled.const _⟩
  have hpart1 := (PolySegStream.ofTokenStream hA).digitizeStream
  have hpart2 := hconj.blockSeg
  have hpart3 := (PolySegStream.ofTokenStream hB).digitizeStream
  refine ((hpart1.append hpart2).append hpart3).of_eq fun z => ?_
  rw [longSegment_tokens (pnd z) (ψc z) (D z) ε, digitize_append, digitize_append,
    digitize_singleton]

/-- **B1 capstone**: the digit stream of the guarded price rewrite of any digit
`PolySegStream` is itself a `PolySegStream`.  Copied tokens are re-rendered digit
blocks; the rewrite's single bignum token (`conjunctionCode pending ψc`) is rendered
from digit access to the pending code; price days are materialized by clamp, exact
whenever the guard passes; flagged days emit nothing.
Paper node: `thm:scon` -/
lemma guardedConditionRun_polySegStream {s : ℕ → List ℕ} (h : PolySegStream s)
    (ψ : ℕ → Sentence) (hψ : PolySentenceCodes ψ) (ε : ℚ) :
    PolySegStream (fun n => digitize (guardedConditionTokens
      (fun day => Encodable.encode (ψ day)) ε n (undigitize (s n)))) := by
  obtain ⟨hcount, hbig⟩ := h.undigitizeTokens
  obtain ⟨cc, hcnt⟩ := hcount
  obtain ⟨cm, hmode⟩ := h.freezeModeScan
  obtain ⟨cd, hclamp⟩ := h.dayClampTokens
  obtain ⟨cf, hflag⟩ := PolySegStream.bigDayFlagScan h
  obtain ⟨cψc, hψPoly⟩ := hψ
  obtain ⟨cad, had⟩ := addc_polyFueled
  -- Pending-code digit access (position `j - 1`).
  have hreidx : PolyFueled _ (fun z => Nat.pair z.unpair.1 (z.unpair.2 - 1)) :=
    (PolyFueled.left.pair (subc_polyFueled.comp (PolyFueled.right.pair
      (PolyFueled.const 1)))).of_eq fun z => by simp only [Nat.unpair_pair]
  have hpnd : BigDigits (fun z =>
      (undigitize (s z.unpair.1)).getD (z.unpair.2 - 1) 0) :=
    (hbig.comp hreidx).of_eq fun z => by simp only [Nat.unpair_pair]
  -- Day (clamped) and condition code of the clamped day.
  have hψc := hψPoly.comp hclamp
  -- The two segment branches and the mode dispatch.
  have hlong := longEmit_polySegStream hpnd hclamp hψc ε
  have hcopy := hbig.blockSeg
  have heq2 := had.comp ((subc_polyFueled.comp (hmode.pair (PolyFueled.const 2))).pair
    (subc_polyFueled.comp ((PolyFueled.const 2).pair hmode)))
  have hseg := hlong.ifZero hcopy heq2
  have hassembled := hseg.concatVar hcnt
  have hflagEnd := hflag.comp (PolyFueled.id.pair hcnt)
  have hempty : PolySegStream (fun _ : ℕ => ([] : List ℕ)) :=
    PolySegStream.ofTokenStream PolyTokenStream.nil
  refine (hassembled.ifZero hempty hflagEnd).of_eq fun n => ?_
  simp only [Nat.unpair_pair]
  set tf : ℕ → ℕ := fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0 with htf
  have hget : ∀ i, i < (undigitize (s n)).length →
      tf (Nat.pair n i) = (undigitize (s n)).getD i 0 := fun i _ => by
    rw [htf]
    simp only [Nat.unpair_pair]
  -- Guard equivalence between the flag and the list-level predicate.
  have hguardIff : bigDayFlagAt tf n (undigitize (s n)).length = 0 ↔
      ∀ j < (undigitize (s n)).length,
        freezeMode4 ((undigitize (s n)).take j) = 2 →
          (undigitize (s n)).getD j 0 ≤ n := by
    rw [bigDayFlagAt_eq_zero_iff]
    constructor
    · intro hall j hj hm
      rw [← hget j hj]
      exact hall j hj (by rwa [vpre_eq_take hget (le_of_lt hj)])
    · intro hall j hj hm
      rw [hget j hj]
      exact hall j hj (by rwa [vpre_eq_take hget (le_of_lt hj)] at hm)
  by_cases hflagn : bigDayFlagAt tf n (undigitize (s n)).length = 0
  · rw [if_pos hflagn, guardedConditionTokens, if_pos (hguardIff.mp hflagn)]
    have hts : undigitize (s n) =
        (List.range (undigitize (s n)).length).map fun j => tf (Nat.pair n j) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        rw [hget i (by simpa using h2)]
        exact (List.getD_eq_getElem (undigitize (s n)) 0 (by simpa using h2)).symm
    have hrun : (conditionPriceTokenRun (fun day => Encodable.encode (ψ day)) ε
        (0, 0) (undigitize (s n))).2 =
        (List.range (undigitize (s n)).length).flatMap fun j =>
          conditionPriceTokenSegment tf (fun day => Encodable.encode (ψ day)) ε
            (Nat.pair n j) := by
      conv_lhs => rw [hts]
      exact congrArg Prod.snd (conditionPriceTokenRun_range tf
        (fun day => Encodable.encode (ψ day)) ε n (undigitize (s n)).length)
    rw [hrun, digitize_flatMap]
    refine List.flatMap_congr fun j hj => ?_
    rw [List.mem_range] at hj
    rw [conditionPriceTokenSegment_eq]
    by_cases hm : freezeMode4 (vpre tf n j) = 2
    · rw [if_pos (by omega : freezeMode4 (vpre tf n j) - 2 +
        (2 - freezeMode4 (vpre tf n j)) = 0), if_pos hm]
      have hdle : tf (Nat.pair n j) ≤ n :=
        (bigDayFlagAt_eq_zero_iff tf n _).mp hflagn j hj hm
      have hclampEq : min (tf (Nat.pair n j)) (n + 1) = tf (Nat.pair n j) :=
        Nat.min_eq_left (by omega)
      have htfj : tf (Nat.pair n j) = (undigitize (s n)).getD j 0 := hget j hj
      have htfj1 : tf (Nat.pair n (j - 1)) = (undigitize (s n)).getD (j - 1) 0 := by
        rw [htf]
        simp only [Nat.unpair_pair]
      rw [← htfj, ← htfj1, hclampEq]
    · rw [if_neg (by omega : ¬ freezeMode4 (vpre tf n j) - 2 +
        (2 - freezeMode4 (vpre tf n j)) = 0), if_neg hm, digitize_singleton]
      rw [htf]
      simp only [Nat.unpair_pair]
  · rw [if_neg hflagn, guardedConditionTokens,
      if_neg (fun hguard => hflagn (hguardIff.mpr hguard))]
    simp [digitize]

/-! ## Digit-side frame scans

The frame pass needs three more shallow scans over the (possibly huge-token) priced
stream: the completed-trade count, the parser stack depth, and the structural
acceptance test.  All three have small position-indexed states, and their token tests
are tag tests (`≤ 8`), so they factor through the digit clamp exactly like the
freeze-mode scan. -/

lemma freezeControlNat_fst (tf : ℕ → ℕ) (n j : ℕ) :
    (PrefixPatchCompile.freezeControlNat tf (Nat.pair n j)).unpair.1 =
      freezeMode4 (vpre tf n j) := by
  rw [PrefixPatchCompile.freezeControlNat]
  simp only [Nat.unpair_pair]
  exact freezeTokenControlAt_fst tf n j

/-- The completed-trade count is poly-fueled over any digit `PolySegStream`. -/
lemma PolySegStream.tradeCountScan {s : ℕ → List ℕ} (h : PolySegStream s) :
    ∃ c, PolyFueled c (fun z =>
      (tradeScanAt (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0)
        z.unpair.1 z.unpair.2).2) := by
  obtain ⟨cm, hmode⟩ := h.freezeModeScan
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hn := PolyFueled.left
  have hj := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hmz := hmode.comp (hn.pair hj)
  have heq4 := had.comp ((subc_polyFueled.comp (hmz.pair (PolyFueled.const 4))).pair
    (subc_polyFueled.comp ((PolyFueled.const 4).pair hmz)))
  have hstep := ifzSel_polyFueled.comp ((hprev.succ_comp.pair hprev).pair heq4)
  refine ⟨_, PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun n j => (tradeScanAt
      (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0) n j).2)
    (fun n => rfl)
    (fun n j => ?_)
    ((IsPolyBounded.linear 0).of_le fun z =>
      le_trans (tradeScanAt_snd_le _ _ _) (Nat.unpair_right_le z))⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  simp only [tradeScanAt, freezeControlNat_fst]
  by_cases hm : freezeMode4 (vpre
      (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0) n j) = 4
  · rw [if_pos hm, if_pos (by omega)]
  · rw [if_neg hm, if_neg (by omega)]

lemma parserDepthNext_clamp (m t d : ℕ) :
    parserDepthNext m (min t 9) d = parserDepthNext m t d := by
  by_cases h : t ≤ 9
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega : 9 ≤ t)]
    rw [parserDepthNext, parserDepthNext]
    split_ifs <;> omega

/-- The shallow parser-depth scan is poly-fueled over any digit `PolySegStream`. -/
lemma PolySegStream.depthScan {s : ℕ → List ℕ} (h : PolySegStream s) :
    ∃ c, PolyFueled c (fun z =>
      parserDepthScanAt (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0)
        z.unpair.1 z.unpair.2) := by
  obtain ⟨hcount, hbig⟩ := h.undigitizeTokens
  obtain ⟨cm, hmode⟩ := h.freezeModeScan
  obtain ⟨ctc, htagclamp⟩ := hbig.clampVal (PolyFueled.const 8)
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hn := PolyFueled.left
  have hj := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hmz := hmode.comp (hn.pair hj)
  have htz := htagclamp.comp (hn.pair hj)
  have heq (K : ℕ) {cf : Code} {f : ℕ → ℕ} (hf : PolyFueled cf f) :
      ∃ c, PolyFueled c (fun z => f z - K + (K - f z)) :=
    ⟨_, (had.comp ((subc_polyFueled.comp (hf.pair (PolyFueled.const K))).pair
      (subc_polyFueled.comp ((PolyFueled.const K).pair hf)))).of_eq
      (fun z => by simp only [Nat.unpair_pair])⟩
  obtain ⟨c2, ht2⟩ := heq 2 htz
  obtain ⟨c3, ht3⟩ := heq 3 htz
  obtain ⟨c4t, ht4⟩ := heq 4 htz
  obtain ⟨c8, ht8⟩ := heq 8 htz
  obtain ⟨cm2, hm2⟩ := heq 2 hmz
  obtain ⟨cm3, hm3⟩ := heq 3 hmz
  obtain ⟨cm4, hm4⟩ := heq 4 hmz
  obtain ⟨cm5, hm5⟩ := heq 5 hmz
  have hpred := subc_polyFueled.comp (hprev.pair (PolyFueled.const 1))
  -- Mode-0 branch: tag tests `2/3/4/8` all pop.
  have hA := ifzSel_polyFueled.comp ((hpred.pair
    (ifzSel_polyFueled.comp ((hpred.pair
      (ifzSel_polyFueled.comp ((hpred.pair
        (ifzSel_polyFueled.comp ((hpred.pair hprev).pair ht8))).pair ht4))).pair
      ht3))).pair ht2)
  -- Other modes: `2/3/5` push, `4` pops, rest holds.
  have hC3 := ifzSel_polyFueled.comp ((hprev.succ_comp.pair hprev).pair hm5)
  have hC2 := ifzSel_polyFueled.comp ((hpred.pair hC3).pair hm4)
  have hC1 := ifzSel_polyFueled.comp ((hprev.succ_comp.pair hC2).pair hm3)
  have hB := ifzSel_polyFueled.comp ((hprev.succ_comp.pair hC1).pair hm2)
  have hstep := ifzSel_polyFueled.comp ((hA.pair hB).pair hmz)
  refine ⟨_, PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun n j => parserDepthScanAt
      (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0) n j)
    (fun n => rfl)
    (fun n j => ?_)
    ((IsPolyBounded.linear 0).of_le fun z =>
      le_trans (parserDepthScanAt_le _ _ _) (Nat.unpair_right_le z))⟩
  simp only [Nat.unpair_pair, ifzSelFn, Nat.reduceAdd]
  simp only [parserDepthScanAt, freezeControlNat_fst]
  rw [← parserDepthNext_clamp]
  simp only [Nat.unpair_pair]
  rw [parserDepthNext]
  simp only [Nat.pred_eq_sub_one]
  split_ifs <;> omega

/-- The structural-acceptance test is poly-fueled over any digit `PolySegStream`
(with its own undigitized token count as the length function). -/
lemma PolySegStream.acceptsScan {s : ℕ → List ℕ} (h : PolySegStream s) :
    ∃ c, PolyFueled c (fun n => parserStructurallyAccepts
      (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0)
      (fun m => (undigitize (s m)).length) n) := by
  obtain ⟨⟨cc, hcnt⟩, -⟩ := h.undigitizeTokens
  obtain ⟨cm, hmode⟩ := h.freezeModeScan
  obtain ⟨cdp, hdepth⟩ := PolySegStream.depthScan h
  have hend := PolyFueled.id.pair hcnt
  have hmodeEnd := hmode.comp hend
  have hdepthEnd := hdepth.comp hend
  have hstep := ifzSel_polyFueled.comp
    (((ifzSel_polyFueled.comp (((PolyFueled.const 1).pair
      (PolyFueled.const 0)).pair hdepthEnd)).pair (PolyFueled.const 0)).pair hmodeEnd)
  refine ⟨_, hstep.of_eq fun n => ?_⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  rw [parserStructurallyAccepts, parserDepthScanNat]
  simp only [Nat.unpair_pair, freezeControlNat_fst]

/-! ## Digit-model frame emitters

The frame pass emits, at each trade-sentence position (`mode = 4`, token = the trade's
sentence code `φc`, possibly huge), a fixed template whose only huge tokens are `φc`'s
conjunction shell `conjunctionCode φc ψc` — once inside the ratio, and (first leg only)
once as the frame sentence.  Everything between is a poly token list. -/

lemma _root_.LogicalInduction.PolyTokenStream.of_eq {s s' : ℕ → List ℕ}
    (h : PolyTokenStream s) (he : ∀ n, s n = s' n) : PolyTokenStream s' := by
  rwa [funext he] at h

/-- The all-poly middle of the first (β) frame leg emission. -/
def frameMidBeta (ψc day bc ibc : ℕ) (ε : ℚ) : List ℕ :=
  [day] ++ rawLowerSafeRecipTokens (rawPriceTokens ψc day) ε ++ [3] ++
    rawMinTokens [7, 1] (rawMulTokens [7, 1]
      (rawConditioningGateTokens [7, 0] (rawAbsTokens [7, 1]) bc ibc)) ++ [8, 8, 6]

/-- The all-poly middle-plus-tail of the second frame leg emission. -/
def frameMidSecond (ψc day bc ibc : ℕ) (ε : ℚ) : List ℕ :=
  [day] ++ rawLowerSafeRecipTokens (rawPriceTokens ψc day) ε ++ [3] ++
    rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ)))
      (rawMulTokens (rawMinTokens [7, 1] (rawMulTokens [7, 1]
        (rawConditioningGateTokens [7, 0] (rawAbsTokens [7, 1]) bc ibc))) [7, 0]) ++
    [8, 8, 6, ψc]

lemma frameBody_split_beta (φc ψc day bc ibc : ℕ) (ε : ℚ) :
    rawLocallyGatedBetaBodyTokens φc ψc day bc ibc ε ++
        [8, 6, conjunctionCode φc ψc] =
      ([0] ++ [conjunctionCode φc ψc]) ++ frameMidBeta ψc day bc ibc ε ++
        [conjunctionCode φc ψc] := by
  simp [rawLocallyGatedBetaBodyTokens, rawConditioningRatioTokens, frameMidBeta,
    rawPriceTokens, rawMulTokens, rawLowerSafeRecipTokens, rawConstTokens,
    rawSafeRecipTokens]

lemma frameBody_split_second (φc ψc day bc ibc : ℕ) (ε : ℚ) :
    rawLocallyGatedSecondBodyTokens φc ψc day bc ibc ε ++ [8, 6, ψc] =
      ([0] ++ [conjunctionCode φc ψc]) ++ frameMidSecond ψc day bc ibc ε := by
  simp [rawLocallyGatedSecondBodyTokens, rawConditioningRatioTokens, frameMidSecond,
    rawPriceTokens, rawMulTokens, rawLowerSafeRecipTokens, rawConstTokens,
    rawSafeRecipTokens]

/-- Both frame middles are poly token streams of their (poly) parameter emitters. -/
lemma frameMid_polyTokenStream (second : Bool)
    {cψ cD cb ci : Code} {ψc day bc ibc : ℕ → ℕ}
    (hψc : PolyFueled cψ ψc) (hday : PolyFueled cD day)
    (hbc : PolyFueled cb bc) (hibc : PolyFueled ci ibc) (ε : ℚ) :
    PolyTokenStream (fun z =>
      if second then frameMidSecond (ψc z) (day z) (bc z) (ibc z) ε
      else frameMidBeta (ψc z) (day z) (bc z) (ibc z) ε) := by
  have hRCc : ∀ k : ℕ, PolyTokenStream (fun _ : ℕ => rawConstTokens k) := fun k =>
    (PolyTokenStream.const 1).append (PolyTokenStream.const k)
  have hRCq : ∀ q : ℚ, PolyTokenStream (fun _ : ℕ =>
      rawConstTokens (Encodable.encode q)) := fun q => hRCc _
  have hmul : ∀ {a b : ℕ → List ℕ}, PolyTokenStream a → PolyTokenStream b →
      PolyTokenStream (fun z => rawMulTokens (a z) (b z)) := fun ha hb =>
    (ha.append hb).append (PolyTokenStream.const 3)
  have hadd : ∀ {a b : ℕ → List ℕ}, PolyTokenStream a → PolyTokenStream b →
      PolyTokenStream (fun z => rawAddTokens (a z) (b z)) := fun ha hb =>
    (ha.append hb).append (PolyTokenStream.const 2)
  have hmax : ∀ {a b : ℕ → List ℕ}, PolyTokenStream a → PolyTokenStream b →
      PolyTokenStream (fun z => rawMaxTokens (a z) (b z)) := fun ha hb =>
    (ha.append hb).append (PolyTokenStream.const 4)
  have hsafe : ∀ {a : ℕ → List ℕ}, PolyTokenStream a →
      PolyTokenStream (fun z => rawSafeRecipTokens (a z)) := fun ha =>
    ha.append (PolyTokenStream.const 5)
  have hmin : ∀ {a b : ℕ → List ℕ}, PolyTokenStream a → PolyTokenStream b →
      PolyTokenStream (fun z => rawMinTokens (a z) (b z)) := fun ha hb =>
    hmul (hRCq (-1)) (hmax (hmul (hRCq (-1)) ha) (hmul (hRCq (-1)) hb))
  have hclip : ∀ {a : ℕ → List ℕ}, PolyTokenStream a →
      PolyTokenStream (fun z => rawClip01Tokens (a z)) := fun ha =>
    hmax (hRCq 0) (hmin (hRCq 1) ha)
  have habs : ∀ {a : ℕ → List ℕ}, PolyTokenStream a →
      PolyTokenStream (fun z => rawAbsTokens (a z)) := fun ha =>
    hmax ha (hmul (hRCq (-1)) ha)
  have h70 : PolyTokenStream (fun _ : ℕ => ([7, 0] : List ℕ)) :=
    (PolyTokenStream.const 7).append (PolyTokenStream.const 0)
  have h71 : PolyTokenStream (fun _ : ℕ => ([7, 1] : List ℕ)) :=
    (PolyTokenStream.const 7).append (PolyTokenStream.const 1)
  have hRCbc : PolyTokenStream (fun z => rawConstTokens (bc z)) :=
    (PolyTokenStream.const 1).append (PolyTokenStream.polyTok hbc)
  have hRCibc : PolyTokenStream (fun z => rawConstTokens (ibc z)) :=
    (PolyTokenStream.const 1).append (PolyTokenStream.polyTok hibc)
  have hgate : PolyTokenStream (fun z => rawConditioningGateTokens
      [7, 0] (rawAbsTokens [7, 1]) (bc z) (ibc z)) := by
    have hmag : PolyTokenStream (fun _ : ℕ => rawAbsTokens [7, 1]) := habs h71
    have htol : PolyTokenStream (fun z => rawMulTokens (rawConstTokens (bc z))
        (rawSafeRecipTokens (rawAbsTokens [7, 1]))) := hmul hRCbc (hsafe hmag)
    have hmaxMag : PolyTokenStream (fun _ : ℕ => rawMaxTokens
        (rawConstTokens (Encodable.encode (1 : ℚ))) (rawAbsTokens [7, 1])) :=
      hmax (hRCq 1) hmag
    exact hclip (hmul
      (hadd (hadd (hRCq 1) htol) (hmul (hRCq (-1)) h70))
      (hmul hRCibc hmaxMag))
  have hlower : PolyTokenStream (fun z => rawLowerSafeRecipTokens
      (rawPriceTokens (ψc z) (day z)) ε) := by
    have hden : PolyTokenStream (fun z => rawPriceTokens (ψc z) (day z)) :=
      ((PolyTokenStream.const 0).append (PolyTokenStream.polyTok hψc)).append
        (PolyTokenStream.polyTok hday)
    exact hmul (hRCq (1 / ε)) (hsafe (hmul (hRCq (1 / ε)) hden))
  have hcore : PolyTokenStream (fun z => rawMinTokens [7, 1] (rawMulTokens [7, 1]
      (rawConditioningGateTokens [7, 0] (rawAbsTokens [7, 1]) (bc z) (ibc z)))) :=
    hmin h71 (hmul h71 hgate)
  cases second with
  | false =>
      refine (((((PolyTokenStream.polyTok hday).append hlower).append
        (PolyTokenStream.const 3)).append hcore).append
        (((PolyTokenStream.const 8).append (PolyTokenStream.const 8)).append
          (PolyTokenStream.const 6))).of_eq ?_
      intro z
      simp [frameMidBeta]
  | true =>
      refine (((((PolyTokenStream.polyTok hday).append hlower).append
        (PolyTokenStream.const 3)).append
          (hmul (hRCq (-1)) (hmul hcore h70))).append
        ((((PolyTokenStream.const 8).append (PolyTokenStream.const 8)).append
          (PolyTokenStream.const 6)).append (PolyTokenStream.polyTok hψc))).of_eq ?_
      intro z
      simp [frameMidSecond]

/-- The token-model frame segment through the digit-side control view. -/
lemma conditioningFrameTokenSegment_eq (second : Bool) (tf : ℕ → ℕ)
    (ψc day bc ibc : ℕ) (ε : ℚ) (z : ℕ) :
    conditioningFrameTokenSegment second tf ψc day bc ibc ε z =
      if freezeMode4 (vpre tf z.unpair.1 z.unpair.2) = 0 ∧ tf z = 6 then []
      else if freezeMode4 (vpre tf z.unpair.1 z.unpair.2) = 4 then
        (if second then
          rawLocallyGatedSecondBodyTokens (tf z) ψc day bc ibc ε ++ [8, 6, ψc]
        else
          rawLocallyGatedBetaBodyTokens (tf z) ψc day bc ibc ε ++
            [8, 6, conjunctionCode (tf z) ψc])
      else [tf z] := by
  have hfst : (PrefixPatchCompile.freezeControlNat tf z).unpair.1 =
      freezeMode4 (vpre tf z.unpair.1 z.unpair.2) := by
    rw [PrefixPatchCompile.freezeControlNat]
    simp only [Nat.unpair_pair]
    exact freezeTokenControlAt_fst tf z.unpair.1 z.unpair.2
  simp only [conditioningFrameTokenSegment, conditioningFrameTokenEmit, hfst]

/-- The digitized frame-leg segment stream over any digit `PolySegStream`, with poly
per-day condition-code and budget-code emitters. -/
lemma frameLegEmit_polySegStream (second : Bool) {src : ℕ → List ℕ}
    (hsrc : PolySegStream src)
    {cψ cb ci : Code} {ψcF bcF ibcF : ℕ → ℕ}
    (hψcF : PolyFueled cψ ψcF) (hbcF : PolyFueled cb bcF)
    (hibcF : PolyFueled ci ibcF) (ε : ℚ) :
    PolySegStream (fun z => digitize
      (conditioningFrameTokenSegment second
        (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
        (ψcF z.unpair.1) z.unpair.1 (bcF z.unpair.1) (ibcF z.unpair.1) ε z)) := by
  obtain ⟨hcount, hbig⟩ := hsrc.undigitizeTokens
  obtain ⟨cm, hmode⟩ := hsrc.freezeModeScan
  obtain ⟨ctc, htagclamp⟩ := hbig.clampVal (PolyFueled.const 8)
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hψz := hψcF.comp PolyFueled.left
  have hbz := hbcF.comp PolyFueled.left
  have hiz := hibcF.comp PolyFueled.left
  -- The conjunction shell of the (possibly huge) trade sentence code.
  have hconj : BigDigits (fun z => conjunctionCode
      ((undigitize (src z.unpair.1)).getD z.unpair.2 0) (ψcF z.unpair.1)) := by
    have hshell := ((BigDigits.const 3).natPair
      (hbig.natPair (BigDigits.of_polyFueled hψz))).succ
    exact hshell.of_eq fun z => by simp only [conjunctionCode, Nat.unpair_pair]
  have hmid := frameMid_polyTokenStream second hψz PolyFueled.left hbz hiz ε
  have hblock0 := PolySegStream.block (PolyFueled.const 0)
  have hconjSeg := hconj.blockSeg
  have hmidSeg := (PolySegStream.ofTokenStream hmid).digitizeStream
  have hcopy := hbig.blockSeg
  have hempty : PolySegStream (fun _ : ℕ => ([] : List ℕ)) :=
    PolySegStream.ofTokenStream PolyTokenStream.nil
  have heq6 := had.comp ((subc_polyFueled.comp (htagclamp.pair
    (PolyFueled.const 6))).pair
    (subc_polyFueled.comp ((PolyFueled.const 6).pair htagclamp)))
  have hsel1 := had.comp (hmode.pair heq6)
  have heq4 := had.comp ((subc_polyFueled.comp (hmode.pair
    (PolyFueled.const 4))).pair
    (subc_polyFueled.comp ((PolyFueled.const 4).pair hmode)))
  -- Clamp faithfulness of the tag-6 test.
  have hclampSix : ∀ z : ℕ, (min ((undigitize (src z.unpair.1)).getD z.unpair.2 0) 9
      = 6 ↔ (undigitize (src z.unpair.1)).getD z.unpair.2 0 = 6) := by
    intro z
    by_cases h9 : (undigitize (src z.unpair.1)).getD z.unpair.2 0 ≤ 9
    · rw [Nat.min_eq_left h9]
    · rw [Nat.min_eq_right (by omega : 9 ≤ _)]
      constructor
      · intro h; omega
      · intro h; omega
  cases second with
  | false =>
      have hlong := ((hblock0.append hconjSeg).append hmidSeg).append hconjSeg
      refine (hempty.ifZero (hlong.ifZero hcopy heq4) hsel1).of_eq fun z => ?_
      rw [conditioningFrameTokenSegment_eq]
      simp only [Nat.unpair_pair, Nat.reduceAdd, reduceIte]
      by_cases hc1 : freezeMode4 (vpre
          (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
          z.unpair.1 z.unpair.2) = 0 ∧
          (undigitize (src z.unpair.1)).getD z.unpair.2 0 = 6
      · rw [if_pos (by
          rcases hc1 with ⟨hm0, ht6⟩
          rw [hm0, ht6]
          norm_num), if_pos hc1]
        simp [digitize]
      · rw [if_neg (by
          intro hz0
          apply hc1
          have h1 : freezeMode4 (vpre
              (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
              z.unpair.1 z.unpair.2) = 0 := by omega
          have h2 : min ((undigitize (src z.unpair.1)).getD z.unpair.2 0) 9 = 6 := by
            omega
          exact ⟨h1, (hclampSix z).mp h2⟩), if_neg hc1]
        by_cases hm4 : freezeMode4 (vpre
            (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
            z.unpair.1 z.unpair.2) = 4
        · rw [if_pos (by omega), if_pos hm4, frameBody_split_beta]
          simp [digitize, List.append_assoc]
        · rw [if_neg (by omega), if_neg hm4, digitize_singleton]
  | true =>
      have hlong := (hblock0.append hconjSeg).append hmidSeg
      refine (hempty.ifZero (hlong.ifZero hcopy heq4) hsel1).of_eq fun z => ?_
      rw [conditioningFrameTokenSegment_eq]
      simp only [Nat.unpair_pair, Nat.reduceAdd, reduceIte]
      by_cases hc1 : freezeMode4 (vpre
          (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
          z.unpair.1 z.unpair.2) = 0 ∧
          (undigitize (src z.unpair.1)).getD z.unpair.2 0 = 6
      · rw [if_pos (by
          rcases hc1 with ⟨hm0, ht6⟩
          rw [hm0, ht6]
          norm_num), if_pos hc1]
        simp [digitize]
      · rw [if_neg (by
          intro hz0
          apply hc1
          have h1 : freezeMode4 (vpre
              (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
              z.unpair.1 z.unpair.2) = 0 := by omega
          have h2 : min ((undigitize (src z.unpair.1)).getD z.unpair.2 0) 9 = 6 := by
            omega
          exact ⟨h1, (hclampSix z).mp h2⟩), if_neg hc1]
        by_cases hm4 : freezeMode4 (vpre
            (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
            z.unpair.1 z.unpair.2) = 4
        · rw [if_pos (by omega), if_pos hm4, frameBody_split_second]
          simp [digitize, List.append_assoc]
        · rw [if_neg (by omega), if_neg hm4, digitize_singleton]

/-- Any list is the range-map of its own `getD` view. -/
lemma list_eq_rangeMap_getD (l : List ℕ) :
    l = (List.range l.length).map fun j => l.getD j 0 := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact (List.getD_eq_getElem l 0 (by simpa using h2)).symm

/-- The digitized full frame-leg output (segments plus end-of-stream flush) over any
digit `PolySegStream`. -/
lemma frameLegOutput_polySegStream (second : Bool) {src : ℕ → List ℕ}
    (hsrc : PolySegStream src)
    {cψ cb ci : Code} {ψcF bcF ibcF : ℕ → ℕ}
    (hψcF : PolyFueled cψ ψcF) (hbcF : PolyFueled cb bcF)
    (hibcF : PolyFueled ci ibcF) (ε : ℚ) :
    PolySegStream (fun n => digitize
      (conditioningFrameTokenOutput second (ψcF n) n ε (bcF n) (ibcF n)
        (undigitize (src n)))) := by
  obtain ⟨⟨cc, hcnt⟩, -⟩ := hsrc.undigitizeTokens
  obtain ⟨cm, hmode⟩ := hsrc.freezeModeScan
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hseg := frameLegEmit_polySegStream second hsrc hψcF hbcF hibcF ε
  have hassembled := hseg.concatVar hcnt
  -- End-of-stream flush: re-emit a withheld trade tag.
  have hmodeEnd := hmode.comp (PolyFueled.id.pair hcnt)
  have heq4End := had.comp ((subc_polyFueled.comp (hmodeEnd.pair
    (PolyFueled.const 4))).pair
    (subc_polyFueled.comp ((PolyFueled.const 4).pair hmodeEnd)))
  have hblock6 : PolySegStream (fun _ : ℕ => tokenBlock 6) :=
    PolySegStream.block (PolyFueled.const 6)
  have hempty : PolySegStream (fun _ : ℕ => ([] : List ℕ)) :=
    PolySegStream.ofTokenStream PolyTokenStream.nil
  have hflush := hblock6.ifZero hempty heq4End
  refine (hassembled.append hflush).of_eq fun n => ?_
  simp only [Nat.unpair_pair]
  have hts := list_eq_rangeMap_getD (undigitize (src n))
  have htf : ∀ j, (undigitize (src n)).getD j 0 =
      (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0) (Nat.pair n j) :=
    fun j => by simp only [Nat.unpair_pair]
  have hts' : undigitize (src n) =
      (List.range (undigitize (src n)).length).map fun j =>
        (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0) (Nat.pair n j) := by
    conv_lhs => rw [hts]
    exact List.map_congr_left fun j _ => htf j
  have hrunEq : conditioningFrameTokenRun second (ψcF n) n ε (bcF n) (ibcF n) (0, 0)
      (undigitize (src n)) =
      (EF.freezeTokenControlAt
        (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0) n
        (undigitize (src n)).length,
        (List.range (undigitize (src n)).length).flatMap fun j =>
          conditioningFrameTokenSegment second
            (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
            (ψcF n) n (bcF n) (ibcF n) ε (Nat.pair n j)) := by
    conv_lhs => rw [hts']
    exact conditioningFrameTokenRun_range second
      (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
      (ψcF n) n (bcF n) (ibcF n) ε n ((undigitize (src n)).length)
  simp only [conditioningFrameTokenOutput]
  rw [hrunEq]
  simp only [digitize_append, digitize_flatMap]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · exact List.flatMap_congr fun j hj => by simp only [Nat.unpair_pair]
  · rw [freezeTokenControlAt_fst]
    by_cases hm4 : freezeMode4 (vpre
        (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0) n
        ((undigitize (src n)).length)) = 4
    · rw [if_pos (by omega), if_pos hm4]
      simp [digitize]
    · rw [if_neg (by omega), if_neg hm4]
      simp [digitize]

/-- **The digitized safe two-leg frame join** over any digit `PolySegStream`: the
digit-model analogue of `safeSeparatedFrameTokenOutput_polySegStream`.
Paper node: `thm:scon` -/
lemma safeSeparatedFrameDigitOutput_polySegStream {src : ℕ → List ℕ}
    (hsrc : PolySegStream src) (ψ : ℕ → Sentence) (hψ : PolySentenceCodes ψ)
    (ε : ℚ) :
    PolySegStream (fun n =>
      digitize (safeSeparatedFrameTokenOutput
        (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
        (fun m => (undigitize (src m)).length) (ψ n) ε
        (frameBudget n (frameTradeCount
          (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
          (fun m => (undigitize (src m)).length) n)) n (undigitize (src n)))) := by
  obtain ⟨cψc, hψPoly⟩ := hψ
  obtain ⟨ctcnt, htcnt⟩ := PolySegStream.tradeCountScan hsrc
  obtain ⟨⟨cc, hcnt⟩, -⟩ := hsrc.undigitizeTokens
  have hcountF : PolyFueled _ (fun n => frameTradeCount
      (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
      (fun m => (undigitize (src m)).length) n) :=
    (htcnt.comp (PolyFueled.id.pair hcnt)).of_eq fun n => by
      simp only [Nat.unpair_pair, frameTradeCount, tradeScanNat]
  obtain ⟨⟨cb, hbF⟩, ⟨ci, hiF⟩⟩ :=
    frameBudgetCodes_polyFueled PolyFueled.id hcountF
  have hfirst := frameLegOutput_polySegStream false hsrc hψPoly hbF hiF ε
  have hsecond := frameLegOutput_polySegStream true hsrc hψPoly hbF hiF ε
  obtain ⟨caccept, haccept⟩ := PolySegStream.acceptsScan hsrc
  refine (hfirst.ifZero (hfirst.append hsecond) haccept).of_eq fun n => ?_
  simp only [safeSeparatedFrameTokenOutput]
  rw [frameBudgetCode_exact, frameInverseBudgetCode_exact]
  by_cases hacc : parserStructurallyAccepts
      (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
      (fun m => (undigitize (src m)).length) n = 0
  · rw [if_pos hacc, if_pos hacc]
  · rw [if_neg hacc, if_neg hacc, digitize_append]

/-- Strategies with equal trade lists are equal (the rank certificate is proof
irrelevant). -/
lemma strategy_ext_trades {n : ℕ} {S S' : Strategy n} (h : S.trades = S'.trades) :
    S = S' := by
  cases S
  cases S'
  simpa using h

/-- **The conditioning translation preserves digit-metered efficient computability**
(`EfficientlyComputableTok₂ → EfficientlyComputableTok₂`), via the guarded digit
compiler: price days are materialized by clamp, the conjunction shells are rendered
from digit access, and on guarded days (an oversized price-day token) both the source
strategy and its translation are empty, so the empty emission is exact.
Paper node: `thm:scon` -/
lemma conditionedTranslation_preserves_ec₂
    (ψ : ℕ → Sentence) (hψ : PolySentenceCodes ψ) (ε : ℚ)
    (T : Trader) (hT : EfficientlyComputableTok₂ T) :
    EfficientlyComputableTok₂ (T.conditionedTranslation ψ ε) := by
  obtain ⟨lengthCode, tokenCode, a, k, hcert⟩ := hT
  let source : ℕ → List ℕ := fun n =>
    clockedTokens lengthCode tokenCode (PrefixPatchCompile.ecClock a k n) n
  have hsource : PolySegStream source :=
    PrefixPatchCompile.clockedTokens_polySegStream lengthCode tokenCode a k
  let priced : ℕ → List ℕ := fun n =>
    digitize (guardedConditionTokens (fun d => Encodable.encode (ψ d)) ε n
      (undigitize (source n)))
  have hpriced : PolySegStream priced :=
    guardedConditionRun_polySegStream hsource ψ hψ ε
  let tfP : ℕ → ℕ := fun w => (undigitize (priced w.unpair.1)).getD w.unpair.2 0
  let lenP : ℕ → ℕ := fun m => (undigitize (priced m)).length
  let framed : ℕ → List ℕ := fun n =>
    digitize (safeSeparatedFrameTokenOutput tfP lenP (ψ n) ε
      (frameBudget n (frameTradeCount tfP lenP n)) n (undigitize (priced n)))
  have hframed : PolySegStream framed :=
    safeSeparatedFrameDigitOutput_polySegStream hpriced ψ hψ ε
  apply ecTok₂_of_rawSegStream (T.conditionedTranslation ψ ε) hframed
  intro n
  have horig : strategyOfTokens n (undigitize (source n)) = T.strat n :=
    congrFun (congrArg Trader.strat hcert) n
  have hundig : undigitize (framed n) =
      safeSeparatedFrameTokenOutput tfP lenP (ψ n) ε
        (frameBudget n (frameTradeCount tfP lenP n)) n (undigitize (priced n)) :=
    undigitize_digitize _
  rw [hundig]
  by_cases hguard : ∀ j < (undigitize (source n)).length,
      freezeMode4 ((undigitize (source n)).take j) = 2 →
        (undigitize (source n)).getD j 0 ≤ n
  · -- Good path: the priced digit stream decodes to the token-model rewrite.
    have hpricedTok : undigitize (priced n) =
        (conditionPriceTokenRun (fun d => Encodable.encode (ψ d)) ε (0, 0)
          (undigitize (source n))).2 := by
      show undigitize (digitize _) = _
      rw [undigitize_digitize, guardedConditionTokens, if_pos hguard]
    have hpricedEq : undigitize (priced n) =
        (List.range (lenP n)).map fun i => tfP (Nat.pair n i) := by
      conv_lhs => rw [list_eq_rangeMap_getD (undigitize (priced n))]
      refine List.map_congr_left fun j _ => ?_
      show (undigitize (priced n)).getD j 0 =
        (undigitize (priced (Nat.pair n j).unpair.1)).getD (Nat.pair n j).unpair.2 0
      simp only [Nat.unpair_pair]
    have hframes := strategyOfTokens_safeSeparatedFrameTokenOutput_trades
      tfP lenP (ψ n) ε (frameBudget n (frameTradeCount tfP lenP n)) n
      (undigitize (priced n)) hpricedEq
    have hprice := strategyOfTokens_conditionPriceTokenRun_trades ψ ε n
      (undigitize (source n))
    rw [← hpricedTok] at hprice
    rw [congrArg Strategy.trades horig] at hprice
    refine strategy_ext_trades ?_
    rw [hframes]
    by_cases hempty : (T.strat n).trades = []
    · rw [hprice, hempty]
      simp [Trader.conditionedTranslation,
        Strategy.separatedLocallyGatedConditionalContract]
      exact hempty
    · have hpricedNe : (strategyOfTokens n (undigitize (priced n))).trades ≠ [] := by
        rw [hprice]
        simpa using hempty
      have hdecodePriced :=
        deserializeTrades_eq_some_of_strategyOfTokens_trades_ne_nil
          n (undigitize (priced n)) hpricedNe
      have hreadyPriced := streamReadFrom_eq_ready_of_deserializeTrades_eq_some
        (undigitize (priced n)) (strategyOfTokens n (undigitize (priced n))).trades
        hdecodePriced
      have hreadyPricedTokens :
          EF.streamReadFrom
              ((List.range (lenP n)).map fun i => tfP (Nat.pair n i))
              (some EF.streamInitial) =
            some ((0, none),
              ([], (strategyOfTokens n (undigitize (priced n))).trades)) := by
        rw [← hpricedEq]
        exact hreadyPriced
      have hcount : frameTradeCount tfP lenP n = (T.strat n).trades.length := by
        calc
          frameTradeCount tfP lenP n =
              (strategyOfTokens n (undigitize (priced n))).trades.length :=
            frameTradeCount_eq_length_of_read tfP lenP n
              ((0, none), ([], (strategyOfTokens n (undigitize (priced n))).trades))
              hreadyPricedTokens
          _ = (T.strat n).trades.length := by rw [hprice, List.length_map]
      have hpos : 0 < (T.strat n).trades.length :=
        List.length_pos_iff.mpr hempty
      rw [hprice, hcount, frameBudget_eq n (T.strat n).trades.length hpos]
      simp only [List.map_map]
      change
        ((T.strat n).trades.map fun p =>
          frameLeg false (ψ n) ε
            (Strategy.localConditioningBudget (conditioningBudget n)
              (T.strat n).trades.length) n
            (p.1.retainedConditionPrices ψ ε, p.2)) ++
          ((T.strat n).trades.map fun p =>
            frameLeg true (ψ n) ε
              (Strategy.localConditioningBudget (conditioningBudget n)
                (T.strat n).trades.length) n
              (p.1.retainedConditionPrices ψ ε, p.2)) =
          ((T.conditionedTranslation ψ ε).strat n).trades
      simp only [frameLeg_retained_eq_locallyGatedFirstLeg,
        frameLeg_retained_eq_locallyGatedSecondLeg]
      rfl
  · -- Guarded path: an oversized price-day token empties both sides.
    push_neg at hguard
    obtain ⟨j, hj, hm, hday⟩ := hguard
    have hTempty : (T.strat n).trades = [] := by
      rw [← horig]
      exact strategyOfTokens_trades_eq_nil_of_bigDay n (undigitize (source n))
        j hj hm hday
    have hpricedNil : undigitize (priced n) = [] := by
      show undigitize (digitize _) = _
      rw [undigitize_digitize, guardedConditionTokens,
        if_neg (fun hall => absurd (hall j hj hm) (by omega))]
    rw [hpricedNil]
    have hframedNil : safeSeparatedFrameTokenOutput tfP lenP (ψ n) ε
        (frameBudget n (frameTradeCount tfP lenP n)) n [] = [] := by
      simp [safeSeparatedFrameTokenOutput, conditioningFrameTokenOutput,
        conditioningFrameTokenRun]
    rw [hframedNil]
    refine strategy_ext_trades ?_
    have hnil : (strategyOfTokens n ([] : List ℕ)).trades = [] := by
      have : deserializeTrades ([] : List ℕ) = some [] := rfl
      unfold strategyOfTokens
      split
      · rfl
      · next trades hdecode =>
          rw [this] at hdecode
          obtain rfl := Option.some.inj hdecode
          simp
    rw [hnil]
    show ([] : List (EF × Sentence)) =
      ((T.strat n).separatedLocallyGatedConditionalContract ψ ε
        (conditioningBudget n)).trades
    simp [Strategy.separatedLocallyGatedConditionalContract, hTempty]

/-! ## The zero-aware guarded compiler (for the eventual translation) -/

/-- The zero-aware token-model segment through the digit-side control view. -/
lemma zeroAwareConditionPriceTokenSegment_eq (zeroDays : Finset ℕ)
    (tf ψCode : ℕ → ℕ) (ε : ℚ) (n j : ℕ) :
    zeroAwareConditionPriceTokenSegment zeroDays tf ψCode ε (Nat.pair n j) =
      if freezeMode4 (vpre tf n j) = 2 then
        (if tf (Nat.pair n j) ∈ zeroDays then
          [tf (Nat.pair n j), 1, Encodable.encode (1 : ℚ), 8]
        else [tf (Nat.pair n j)] ++
          rawConditionalPriceTokens (tf (Nat.pair n (j - 1)))
            (ψCode (tf (Nat.pair n j))) (tf (Nat.pair n j)) ε ++ [8])
      else [tf (Nat.pair n j)] := by
  have hfst : (PrefixPatchCompile.freezeControlNat tf (Nat.pair n j)).unpair.1 =
      freezeMode4 (vpre tf n j) := freezeControlNat_fst tf n j
  by_cases hm : freezeMode4 (vpre tf n j) = 2
  · rw [if_pos hm]
    match j with
    | 0 => exact absurd hm (by simp [vpre, freezeMode4])
    | j + 1 =>
        have hctrl := freezeTokenControlAt_mode2 tf n j (by
          have := freezeTokenControlAt_fst tf n (j + 1)
          omega)
        simp only [zeroAwareConditionPriceTokenSegment,
          PrefixPatchCompile.freezeControlNat, Nat.unpair_pair]
        rw [hctrl]
        norm_num
  · rw [if_neg hm]
    simp only [zeroAwareConditionPriceTokenSegment]
    rw [hfst]
    by_cases h0 : freezeMode4 (vpre tf n j) = 0
    · rw [if_pos h0]
    rw [if_neg h0]
    by_cases h1 : freezeMode4 (vpre tf n j) = 1
    · rw [if_pos h1]
    rw [if_neg h1, if_neg hm]

/-- The guarded zero-aware token-level price rewrite. -/
def guardedZeroAwareConditionTokens (zeroDays : Finset ℕ) (ψCode : ℕ → ℕ) (ε : ℚ)
    (n : ℕ) (ts : List ℕ) : List ℕ :=
  if ∀ j < ts.length, freezeMode4 (ts.take j) = 2 → ts.getD j 0 ≤ n
  then (zeroAwareConditionPriceTokenRun zeroDays ψCode ε (0, 0) ts).2
  else []

/-- **Zero-aware B1 capstone**: the digit stream of the guarded zero-aware price
rewrite of any digit `PolySegStream` is itself a `PolySegStream`.  The zero-day
membership test runs on the clamped day, exact whenever the guard passes.
Paper node: `thm:scon` -/
lemma guardedZeroAwareConditionRun_polySegStream (zeroDays : Finset ℕ)
    {s : ℕ → List ℕ} (h : PolySegStream s)
    (ψ : ℕ → Sentence) (hψ : PolySentenceCodes ψ) (ε : ℚ) :
    PolySegStream (fun n => digitize (guardedZeroAwareConditionTokens zeroDays
      (fun day => Encodable.encode (ψ day)) ε n (undigitize (s n)))) := by
  obtain ⟨hcount, hbig⟩ := h.undigitizeTokens
  obtain ⟨cc, hcnt⟩ := hcount
  obtain ⟨cm, hmode⟩ := h.freezeModeScan
  obtain ⟨cd, hclamp⟩ := h.dayClampTokens
  obtain ⟨cf, hflag⟩ := PolySegStream.bigDayFlagScan h
  obtain ⟨cψc, hψPoly⟩ := hψ
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hreidx : PolyFueled _ (fun z => Nat.pair z.unpair.1 (z.unpair.2 - 1)) :=
    (PolyFueled.left.pair (subc_polyFueled.comp (PolyFueled.right.pair
      (PolyFueled.const 1)))).of_eq fun z => by simp only [Nat.unpair_pair]
  have hpnd : BigDigits (fun z =>
      (undigitize (s z.unpair.1)).getD (z.unpair.2 - 1) 0) :=
    (hbig.comp hreidx).of_eq fun z => by simp only [Nat.unpair_pair]
  have hψc := hψPoly.comp hclamp
  have hlong := longEmit_polySegStream hpnd hclamp hψc ε
  -- The zero-day branch: `[day, 1, enc 1, 8]` with the clamped day.
  have hzero : PolySegStream (fun z => digitize
      [min ((undigitize (s z.unpair.1)).getD z.unpair.2 0) (z.unpair.1 + 1),
        1, Encodable.encode (1 : ℚ), 8]) :=
    (PolySegStream.ofTokenStream
      ((((PolyTokenStream.polyTok hclamp).append (PolyTokenStream.const 1)).append
        (PolyTokenStream.const (Encodable.encode (1 : ℚ)))).append
        (PolyTokenStream.const 8))).digitizeStream
  obtain ⟨cmem, hmem⟩ := finsetMembership_polyFueled hclamp zeroDays
  have hmode2Long := hzero.ifZero hlong
    ((ifzSel_polyFueled.comp (((PolyFueled.const 1).pair
      (PolyFueled.const 0)).pair hmem)).of_eq fun z => by
        simp only [Nat.unpair_pair, ifzSelFn]
        rfl)
  have hcopy := hbig.blockSeg
  have heq2 := had.comp ((subc_polyFueled.comp (hmode.pair (PolyFueled.const 2))).pair
    (subc_polyFueled.comp ((PolyFueled.const 2).pair hmode)))
  have hseg := hmode2Long.ifZero hcopy heq2
  have hassembled := hseg.concatVar hcnt
  have hflagEnd := hflag.comp (PolyFueled.id.pair hcnt)
  have hempty : PolySegStream (fun _ : ℕ => ([] : List ℕ)) :=
    PolySegStream.ofTokenStream PolyTokenStream.nil
  refine (hassembled.ifZero hempty hflagEnd).of_eq fun n => ?_
  simp only [Nat.unpair_pair]
  set tf : ℕ → ℕ := fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0 with htf
  have hget : ∀ i, i < (undigitize (s n)).length →
      tf (Nat.pair n i) = (undigitize (s n)).getD i 0 := fun i _ => by
    rw [htf]
    simp only [Nat.unpair_pair]
  have hguardIff : bigDayFlagAt tf n (undigitize (s n)).length = 0 ↔
      ∀ j < (undigitize (s n)).length,
        freezeMode4 ((undigitize (s n)).take j) = 2 →
          (undigitize (s n)).getD j 0 ≤ n := by
    rw [bigDayFlagAt_eq_zero_iff]
    constructor
    · intro hall j hj hm
      rw [← hget j hj]
      exact hall j hj (by rwa [vpre_eq_take hget (le_of_lt hj)])
    · intro hall j hj hm
      rw [hget j hj]
      exact hall j hj (by rwa [vpre_eq_take hget (le_of_lt hj)] at hm)
  by_cases hflagn : bigDayFlagAt tf n (undigitize (s n)).length = 0
  · rw [if_pos hflagn, guardedZeroAwareConditionTokens,
      if_pos (hguardIff.mp hflagn)]
    have hts : undigitize (s n) =
        (List.range (undigitize (s n)).length).map fun j => tf (Nat.pair n j) := by
      conv_lhs => rw [list_eq_rangeMap_getD (undigitize (s n))]
      exact List.map_congr_left fun j _ => (hget j (by
        by_cases hjl : j < (undigitize (s n)).length
        · exact hjl
        · exact absurd (List.mem_range.mp (by assumption)) hjl)).symm
    have hrun : (zeroAwareConditionPriceTokenRun zeroDays
        (fun day => Encodable.encode (ψ day)) ε (0, 0) (undigitize (s n))).2 =
        (List.range (undigitize (s n)).length).flatMap fun j =>
          zeroAwareConditionPriceTokenSegment zeroDays tf
            (fun day => Encodable.encode (ψ day)) ε (Nat.pair n j) := by
      conv_lhs => rw [hts]
      exact congrArg Prod.snd (zeroAwareConditionPriceTokenRun_range zeroDays tf
        (fun day => Encodable.encode (ψ day)) ε n (undigitize (s n)).length)
    rw [hrun, digitize_flatMap]
    refine List.flatMap_congr fun j hj => ?_
    rw [List.mem_range] at hj
    rw [zeroAwareConditionPriceTokenSegment_eq]
    by_cases hm : freezeMode4 (vpre tf n j) = 2
    · rw [if_pos (by omega : freezeMode4 (vpre tf n j) - 2 +
        (2 - freezeMode4 (vpre tf n j)) = 0), if_pos hm]
      have hdle : tf (Nat.pair n j) ≤ n :=
        (bigDayFlagAt_eq_zero_iff tf n _).mp hflagn j hj hm
      have hclampEq : min (tf (Nat.pair n j)) (n + 1) = tf (Nat.pair n j) :=
        Nat.min_eq_left (by omega)
      have htfj : tf (Nat.pair n j) = (undigitize (s n)).getD j 0 := hget j hj
      have htfj1 : tf (Nat.pair n (j - 1)) = (undigitize (s n)).getD (j - 1) 0 := by
        rw [htf]
        simp only [Nat.unpair_pair]
      rw [← htfj, ← htfj1, hclampEq]
      by_cases hzd : tf (Nat.pair n j) ∈ zeroDays
      · rw [if_pos (by simp [hzd]), if_pos hzd]
      · rw [if_neg (by simp [hzd]), if_neg hzd]
    · rw [if_neg (by omega : ¬ freezeMode4 (vpre tf n j) - 2 +
        (2 - freezeMode4 (vpre tf n j)) = 0), if_neg hm, digitize_singleton]
      rw [htf]
      simp only [Nat.unpair_pair]
  · rw [if_neg hflagn, guardedZeroAwareConditionTokens,
      if_neg (fun hguard => hflagn (hguardIff.mpr hguard))]
    simp [digitize]

/-- **The eventual (finite-zero, launch-gated) conditioning translation preserves
digit-metered efficient computability.**
Paper node: `thm:scon` -/
lemma eventualConditionedTranslation_preserves_ec₂
    {P : History} {ψ : ℕ → Sentence}
    (F : EventualConditioningFloor P ψ) (hψ : PolySentenceCodes ψ)
    (T : Trader) (hT : EfficientlyComputableTok₂ T) :
    EfficientlyComputableTok₂ (T.eventualConditionedTranslation F) := by
  obtain ⟨lengthCode, tokenCode, a, k, hcert⟩ := hT
  let source : ℕ → List ℕ := fun n =>
    clockedTokens lengthCode tokenCode (PrefixPatchCompile.ecClock a k n) n
  have hsource : PolySegStream source :=
    PrefixPatchCompile.clockedTokens_polySegStream lengthCode tokenCode a k
  let priced : ℕ → List ℕ := fun n =>
    digitize (guardedZeroAwareConditionTokens F.zeroDays
      (fun d => Encodable.encode (ψ d)) F.epsilon n (undigitize (source n)))
  have hpriced : PolySegStream priced :=
    guardedZeroAwareConditionRun_polySegStream F.zeroDays hsource ψ hψ F.epsilon
  let tfP : ℕ → ℕ := fun w => (undigitize (priced w.unpair.1)).getD w.unpair.2 0
  let lenP : ℕ → ℕ := fun m => (undigitize (priced m)).length
  let framed : ℕ → List ℕ := fun n =>
    digitize (safeSeparatedFrameTokenOutput tfP lenP (ψ n) F.epsilon
      (frameBudget n (frameTradeCount tfP lenP n)) n (undigitize (priced n)))
  have hframed : PolySegStream framed :=
    safeSeparatedFrameDigitOutput_polySegStream hpriced ψ hψ F.epsilon
  let output : ℕ → List ℕ := fun n => if F.cutoff ≤ n then framed n else []
  have hemptyStream : PolySegStream (fun _ : ℕ => ([] : List ℕ)) :=
    PolySegStream.ofTokenStream PolyTokenStream.nil
  have hlaunch : PolyFueled _ (fun n => n + 1 - F.cutoff) :=
    (subc_polyFueled.comp (PolyFueled.id.succ_comp.pair
      (PolyFueled.const F.cutoff))).of_eq fun n => by simp only [Nat.unpair_pair]
  have houtput : PolySegStream output := by
    refine (hemptyStream.ifZero hframed hlaunch).of_eq fun n => ?_
    show _ = if F.cutoff ≤ n then framed n else []
    by_cases hn : F.cutoff ≤ n
    · rw [if_pos hn, if_neg (by omega)]
    · rw [if_neg hn, if_pos (by omega)]
  apply ecTok₂_of_rawSegStream (T.eventualConditionedTranslation F) houtput
  intro n
  by_cases hn : n < F.cutoff
  · have hout : output n = [] := by
      show (if F.cutoff ≤ n then framed n else []) = []
      rw [if_neg (by omega)]
    rw [hout, T.eventualConditionedTranslation_strat_of_lt F hn]
    simp [strategyOfTokens, deserializeTrades,
      EF.streamReadFrom, EF.streamInitial, Trader.zero, undigitize]
  · have hcn : F.cutoff ≤ n := Nat.le_of_not_gt hn
    have hout : output n = framed n := by
      show (if F.cutoff ≤ n then framed n else []) = framed n
      rw [if_pos hcn]
    rw [hout]
    have horig : strategyOfTokens n (undigitize (source n)) = T.strat n :=
      congrFun (congrArg Trader.strat hcert) n
    have hundig : undigitize (framed n) =
        safeSeparatedFrameTokenOutput tfP lenP (ψ n) F.epsilon
          (frameBudget n (frameTradeCount tfP lenP n)) n (undigitize (priced n)) :=
      undigitize_digitize _
    rw [hundig]
    have htarget := T.eventualConditionedTranslation_strat_of_le F hcn
    by_cases hguard : ∀ j < (undigitize (source n)).length,
        freezeMode4 ((undigitize (source n)).take j) = 2 →
          (undigitize (source n)).getD j 0 ≤ n
    · have hpricedTok : undigitize (priced n) =
          (zeroAwareConditionPriceTokenRun F.zeroDays
            (fun d => Encodable.encode (ψ d)) F.epsilon (0, 0)
            (undigitize (source n))).2 := by
        show undigitize (digitize _) = _
        rw [undigitize_digitize, guardedZeroAwareConditionTokens, if_pos hguard]
      have hpricedEq : undigitize (priced n) =
          (List.range (lenP n)).map fun i => tfP (Nat.pair n i) := by
        conv_lhs => rw [list_eq_rangeMap_getD (undigitize (priced n))]
        refine List.map_congr_left fun j _ => ?_
        show (undigitize (priced n)).getD j 0 =
          (undigitize (priced (Nat.pair n j).unpair.1)).getD
            (Nat.pair n j).unpair.2 0
        simp only [Nat.unpair_pair]
      have hframes := strategyOfTokens_safeSeparatedFrameTokenOutput_trades
        tfP lenP (ψ n) F.epsilon (frameBudget n (frameTradeCount tfP lenP n)) n
        (undigitize (priced n)) hpricedEq
      have hprice := strategyOfTokens_zeroAwareConditionPriceTokenRun_trades
        F.zeroDays ψ F.epsilon n (undigitize (source n))
      rw [← hpricedTok] at hprice
      rw [congrArg Strategy.trades horig] at hprice
      refine strategy_ext_trades ?_
      rw [hframes, htarget]
      by_cases hempty : (T.strat n).trades = []
      · rw [hprice, hempty]
        simp [Strategy.separatedExceptZeroConditionalContract]
        exact hempty
      · have hpricedNe : (strategyOfTokens n (undigitize (priced n))).trades ≠ [] := by
          rw [hprice]
          simpa using hempty
        have hdecodePriced :=
          deserializeTrades_eq_some_of_strategyOfTokens_trades_ne_nil
            n (undigitize (priced n)) hpricedNe
        have hreadyPriced := streamReadFrom_eq_ready_of_deserializeTrades_eq_some
          (undigitize (priced n)) (strategyOfTokens n (undigitize (priced n))).trades
          hdecodePriced
        have hreadyPricedTokens :
            EF.streamReadFrom
                ((List.range (lenP n)).map fun i => tfP (Nat.pair n i))
                (some EF.streamInitial) =
              some ((0, none),
                ([], (strategyOfTokens n (undigitize (priced n))).trades)) := by
          rw [← hpricedEq]
          exact hreadyPriced
        have hcount : frameTradeCount tfP lenP n = (T.strat n).trades.length := by
          calc
            frameTradeCount tfP lenP n =
                (strategyOfTokens n (undigitize (priced n))).trades.length :=
              frameTradeCount_eq_length_of_read tfP lenP n
                ((0, none), ([], (strategyOfTokens n (undigitize (priced n))).trades))
                hreadyPricedTokens
            _ = (T.strat n).trades.length := by rw [hprice, List.length_map]
        have hpos : 0 < (T.strat n).trades.length :=
          List.length_pos_iff.mpr hempty
        rw [hprice, hcount, frameBudget_eq n (T.strat n).trades.length hpos]
        simp only [List.map_map]
        change
          ((T.strat n).trades.map fun p =>
            frameLeg false (ψ n) F.epsilon
              (Strategy.localConditioningBudget (conditioningBudget n)
                (T.strat n).trades.length) n
              (p.1.retainedConditionPricesExceptZero F.zeroDays ψ F.epsilon,
                p.2)) ++
            ((T.strat n).trades.map fun p =>
              frameLeg true (ψ n) F.epsilon
                (Strategy.localConditioningBudget (conditioningBudget n)
                  (T.strat n).trades.length) n
                (p.1.retainedConditionPricesExceptZero F.zeroDays ψ F.epsilon,
                  p.2)) =
            ((T.strat n).separatedExceptZeroConditionalContract
              F.zeroDays ψ F.epsilon (conditioningBudget n)).trades
        simp only [frameLeg_exceptZero_eq_locallyGatedFirstLeg,
          frameLeg_exceptZero_eq_locallyGatedSecondLeg]
        rfl
    · push_neg at hguard
      obtain ⟨j, hj, hm, hday⟩ := hguard
      have hTempty : (T.strat n).trades = [] := by
        rw [← horig]
        exact strategyOfTokens_trades_eq_nil_of_bigDay n (undigitize (source n))
          j hj hm hday
      have hpricedNil : undigitize (priced n) = [] := by
        show undigitize (digitize _) = _
        rw [undigitize_digitize, guardedZeroAwareConditionTokens,
          if_neg (fun hall => absurd (hall j hj hm) (by omega))]
      rw [hpricedNil]
      have hframedNil : safeSeparatedFrameTokenOutput tfP lenP (ψ n) F.epsilon
          (frameBudget n (frameTradeCount tfP lenP n)) n [] = [] := by
        simp [safeSeparatedFrameTokenOutput, conditioningFrameTokenOutput,
          conditioningFrameTokenRun]
      rw [hframedNil]
      refine strategy_ext_trades ?_
      have hnil : (strategyOfTokens n ([] : List ℕ)).trades = [] := by
        have hdec : deserializeTrades ([] : List ℕ) = some [] := rfl
        unfold strategyOfTokens
        split
        · rfl
        · next trades hdecode =>
            rw [hdec] at hdecode
            obtain rfl := Option.some.inj hdecode
            simp
      rw [hnil, htarget]
      show ([] : List (EF × Sentence)) =
        ((T.strat n).separatedExceptZeroConditionalContract
          F.zeroDays ψ F.epsilon (conditioningBudget n)).trades
      simp [Strategy.separatedExceptZeroConditionalContract, hTempty]

/-! ## Interim `thm:scon` endpoints (digit-class transfer, pending RPN-5)

With both translation compilers proved `Tok₂ → Tok₂`, conditioning transfers
no-exploitation for every digit-metered trader of the conditioned market back to the
base inductor.  **Interim disclosure (collapse flip):** the collapsed criterion meters
the full symbol class, and the RPN-level conditioning compiler (RPN-5 — sentence-block
conjunction is concatenation in Polish coding) is what will upgrade these to
class-instance closure (`IsLogicalInductor` of the conditioned market).  Until then the
conclusions below quantify over `EfficientlyComputableTok₂` (which contains every
token-model trader via `EfficientlyComputableTok.toTok₂`). -/

/-- Gated closure transfer under conditioning, digit class.
Paper node: `thm:scon` -/
theorem lic_conditioned_gated
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (ε : ℚ) (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d, (ε : ℝ) ≤ P d (C.condition d)) :
    ∀ T : Trader, EfficientlyComputableTok₂ T →
      ¬ T.Exploits (conditionedHistory P C.condition) (DP.union extra) :=
  fun T hTec₂ hTexp =>
    IsLogicalInductor.noExploitDigit (P := P) (DP := DP)
      (T.conditionedTranslation C.condition ε)
      (conditionedTranslation_preserves_ec₂ C.condition C.condition_codes ε T hTec₂)
      (Trader.conditionedTranslation_exploits_base hε hfloor hTexp)

/-- Prefix-safe (finite-zero) closure transfer under conditioning, digit class.
Paper node: `thm:scon` -/
theorem lic_conditioned_eventual
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra)
    (floor : EventualConditioningFloor P C.condition) :
    ∀ T : Trader, EfficientlyComputableTok₂ T →
      ¬ T.Exploits (conditionedHistory P C.condition) (DP.union extra) :=
  fun T hTec₂ hTexp =>
    IsLogicalInductor.noExploitDigit (P := P) (DP := DP)
      (T.eventualConditionedTranslation floor)
      (eventualConditionedTranslation_preserves_ec₂ floor C.condition_codes T hTec₂)
      (Trader.eventualConditionedTranslation_exploits_base floor hTexp)

/-- `thm:scon` transfer from joint consistency and concrete computability data.
Paper node: `thm:scon` -/
theorem lic_conditioned_eventual_ofMarketComputation
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (C.condition i)) :
    ∀ T : Trader, EfficientlyComputableTok₂ T →
      ¬ T.Exploits (conditionedHistory P C.condition) (DP.union extra) :=
  lic_conditioned_eventual P DP extra C
    (eventualConditioningFloorOfJointConsistency
      P DP market C.condition C.condition_codes hjoint)

/-- Fixed-sentence `thm:scon` transfer.
Paper node: `thm:scon` -/
theorem lic_conditioned_fixed_ofComputationAndMarket
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (base : DeductiveProcessComputation DP) (market : MarketComputation P)
    (ψ : Sentence)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ v.Holds ψ) :
    ∀ T : Trader, EfficientlyComputableTok₂ T →
      ¬ T.Exploits (conditionedHistory P (fun _ => ψ))
        (DP.adjoinSentence ψ) := by
  let C := fixedConditioningPresentation base ψ
  have hjointC : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (C.condition i) := by
    intro n
    obtain ⟨v, hv, hψ⟩ := hjoint n
    exact ⟨v, hv, fun _ => hψ⟩
  have hresult :=
    lic_conditioned_eventual_ofMarketComputation
      P DP (fixedConditionProcess ψ) C market hjointC
  simpa [C, fixedConditioningPresentation,
    DeductiveProcess.adjoinSentence] using hresult

/-- Growing finite-prefix `thm:scon` transfer.
Paper node: `thm:scon` -/
theorem lic_conditioned_growing_ofComputationsAndMarket
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (base : DeductiveProcessComputation DP)
    (more : CompactConditioningProcessComputation extra)
    (market : MarketComputation P)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧
        ∀ i, v.ConsistentWith (extra.D i)) :
    ∀ T : Trader, EfficientlyComputableTok₂ T →
      ¬ T.Exploits
        (conditionedHistory P (fun n => deductiveStageCondition (extra.D n)))
        (DP.union extra) := by
  let C := conditioningPresentationOfComputations base more
  have hjointC : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (C.condition i) := by
    intro n
    obtain ⟨v, hv, hextra⟩ := hjoint n
    refine ⟨v, hv, fun i => ?_⟩
    exact (v.holds_deductiveStageCondition (extra.D i)).2 (hextra i)
  exact lic_conditioned_eventual_ofMarketComputation
    P DP extra C market hjointC

/-- Gated `thm:scon` transfer with concrete market data.
Paper node: `thm:scon` -/
theorem lic_conditioned_gated_ofMarketComputation
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (_market : MarketComputation P)
    (ε : ℚ) (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d, (ε : ℝ) ≤ P d (C.condition d)) :
    ∀ T : Trader, EfficientlyComputableTok₂ T →
      ¬ T.Exploits (conditionedHistory P C.condition) (DP.union extra) :=
  lic_conditioned_gated P DP extra C ε hε hfloor

#print axioms lic_conditioned_gated
#print axioms lic_conditioned_eventual
#print axioms lic_conditioned_eventual_ofMarketComputation
#print axioms lic_conditioned_fixed_ofComputationAndMarket
#print axioms lic_conditioned_growing_ofComputationsAndMarket
#print axioms lic_conditioned_gated_ofMarketComputation

#print axioms eventualConditionedTranslation_preserves_ec₂
#print axioms conditionedTranslation_preserves_ec₂
#print axioms strategyOfTokens_trades_eq_nil_of_bigDay
#print axioms guardedConditionRun_polySegStream
#print axioms PolySegStream.tradeCountScan
#print axioms PolySegStream.depthScan
#print axioms PolySegStream.acceptsScan

end ConditioningCompile

end LogicalInduction
