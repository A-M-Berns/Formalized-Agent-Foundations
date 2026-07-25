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
forces the empty validated strategy. -/
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

end ConditioningCompile

end LogicalInduction
