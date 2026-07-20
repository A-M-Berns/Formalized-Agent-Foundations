/-
# Closure under finite perturbations (`thm:ifp`)

The paper transports an exploiting trader across a finite change of market history by
replacing every old price leaf in its feature syntax with the corresponding rational
constant.  This file realizes that semantics with an administrative dead binding which
retains the original price leaf, and proves its rank, size, semantic, net-worth, and
exploitation laws.  Retaining the leaf is what makes the flat rewrite parser-transparent
even on malformed raw trader programs.

## PAPER ERRATUM — the appendix proof of `thm:ifp` has a gap (see PROGRESS.md "Paper errata")

This is **not** a modeling artifact of our substrate.  The paper's proof (`app:ifp`)
transports the trader by hard-coding the old prices, and justifies efficiency thus:

> "Note that `F` is efficiently computable: by the assumption that `pt_n = pt'_n` for all
> `n ≥ N`, only finitely many constants `pt_i(phi)` are needed, and can be hard-coded
> into `F`."

That sentence is false.  Finitely many *days* `i < N` are involved, but `phi` still ranges
over **all** sentences: a day-`n` trade expression may reference `phi^{*i}` for any `phi` of
rank `≤ n`, so the constant set `{pt_i(phi) : i < N, phi ∈ Sentences}` is infinite.  `F`
must therefore *compute* `pt_i(phi)` rather than hard-code it, and `def:marketprocess`
(a market is any computable sequence of pricings — no finite support, no time bound)
guarantees only that this is computable, with no bound on its runtime or on the bit-size of
the resulting rational.  So `F` is not efficiently computable in general, and the paper's
proof does not go through for the class of markets it quantifies over.

The gap is real, not merely pedantic.  Let `P'` agree with `LIA` from day 1 on, with
`P' 0 phi = 1 - 1/2^(2^(encode phi))` — a legal market by `def:marketprocess`.  A trader
whose day-`n` strategy prices a sentence of code `~n` at day 0 freezes to a `.const` whose
numeral is `~2^(2^n)`, which no polynomial clock can emit.  For such a `P'`,
`EfficientPrefixPatch P' 1` is **uninhabited** — the hypothesis is not merely unproved but
unsatisfiable.  (This argument is *not* formalized; see the "Paper errata" entry for the
one unformalized fact it rests on, and for what remains open.)

Note the paper is aware `LIA` itself has finite support per day (`sec:construct`, remark
following the belief-sequence definition) and *deliberately* generalizes the property tail
to arbitrary markets.  Finite support is exactly what would rescue the hard-coding step, so
the gap is a genuine cost of that generalization, not an oversight about `LIA`.

**What this file does about it.**  We keep the theorem to what is actually provable:
`EfficientPrefixPatch` states the missing closure fact for the concrete syntax
transformation, and `lic_iff_of_finitePerturbation` takes it as a hypothesis for each
market.  The structure contains no trading, exploitation, or logical-inductor conclusion.
Consequently `lic_iff_of_finitePerturbation` is **strictly weaker than the paper's
`thm:ifp`**: it does not cover every finite perturbation of a computable market, only those
whose frozen prefix admits an efficient presentation.  It is not vacuous — for `LIA` the
per-day quote table is a finite entry list (`RationalBeliefState`, `MarketMaker.lean`), so
the patch is a hardcodable finite lookup and `liaEfficientPrefixPatch` discharges
`M7-PREFIX-PATCH` — but the restriction must be stated whenever this theorem is cited as
the paper's.
-/
import LogicalInduction.Framework.Affine
import LogicalInduction.Framework.Computable

namespace LogicalInduction

open scoped BigOperators

namespace EF

/-- Freeze every price leaf strictly before `cutoff` at its exact rational quote.

The administrative `letE` deliberately retains the dead original price leaf.  Its body is
the constant quote, so the denotation is independent of that leaf, while retaining it makes
the flat-token rewrite parser-transparent and preserves the feature's original rank.  This
matters for arbitrary clocked trader programs: malformed sentence tokens stay malformed and
a rank-invalid source program cannot become valid merely because an old leaf was frozen. -/
def freezeBefore (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) : EF → EF
  | .price φ day =>
      if day < cutoff then .letE (.price φ day) (.const (quote day φ)) else .price φ day
  | .const q => .const q
  | .add a b => .add (a.freezeBefore quote cutoff) (b.freezeBefore quote cutoff)
  | .mul a b => .mul (a.freezeBefore quote cutoff) (b.freezeBefore quote cutoff)
  | .max a b => .max (a.freezeBefore quote cutoff) (b.freezeBefore quote cutoff)
  | .safeRecip a => .safeRecip (a.freezeBefore quote cutoff)
  | .var i => .var i
  | .letE value body =>
      .letE (value.freezeBefore quote cutoff) (body.freezeBefore quote cutoff)

/-- The retained dead leaf makes the administrative freeze rank-preserving. -/
@[simp] theorem freezeBefore_rank (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    (e.freezeBefore quote cutoff).rank = e.rank := by
  induction e with
  | price φ day =>
      simp only [freezeBefore]
      split <;> simp
  | const q => simp [freezeBefore]
  | add a b iha ihb => simp [freezeBefore, iha, ihb]
  | mul a b iha ihb => simp [freezeBefore, iha, ihb]
  | max a b iha ihb => simp [freezeBefore, iha, ihb]
  | safeRecip a iha => simp [freezeBefore, iha]
  | var i => simp [freezeBefore]
  | letE value body ihv ihb => simp [freezeBefore, ihv, ihb]

lemma freezeBefore_rank_le (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    (e.freezeBefore quote cutoff).rank ≤ e.rank := by
  rw [freezeBefore_rank]

/-- The administrative binding makes the literal rewrite at most three times larger. -/
lemma freezeBefore_cost_le (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    (e.freezeBefore quote cutoff).cost ≤ 3 * e.cost := by
  induction e with
  | price φ day => simp only [freezeBefore]; split <;> simp [cost]
  | const q => norm_num [freezeBefore, cost]
  | add a b iha ihb => simp only [freezeBefore, cost]; omega
  | mul a b iha ihb => simp only [freezeBefore, cost]; omega
  | max a b iha ihb => simp only [freezeBefore, cost]; omega
  | safeRecip a iha => simp only [freezeBefore, cost]; omega
  | var i => norm_num [freezeBefore, cost]
  | letE value body ihv ihb => simp only [freezeBefore, cost]; omega

/-! #### Flat-token presentation of the prefix freeze

The retained price leaf makes the compiler a bounded streaming transducer.  It copies every
input token and, immediately after an old price frame `[0, phi, day]`, appends the constant
and administrative-binding suffix `[1, quote, 8]`. -/

/-- Parser control needed by the flat-token prefix transducer: `(mode, pendingSentenceCode)`.
The modes agree with `EF.streamStep`; only mode `2` uses the pending code. -/
abbrev FreezeTokenState := ℕ × ℕ

def freezeTokenNext (state : FreezeTokenState) (token : ℕ) : FreezeTokenState :=
  match state.1 with
  | 0 =>
      if token = 0 then (1, 0)
      else if token = 1 then (3, 0)
      else if token = 6 then (4, 0)
      else if token = 7 then (5, 0)
      else (0, 0)
  | 1 => (2, token)
  | _ => (0, 0)

/-- Tokens emitted while consuming one source token. -/
def freezeTokenEmit (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (state : FreezeTokenState) (token : ℕ) : List ℕ :=
  if state.1 = 2 ∧ token < cutoff then
    [token, 1, quoteCode token state.2, 8]
  else
    [token]

/-- Run the prefix transducer, returning its final parser control and emitted stream. -/
def freezeTokenRun (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) :
    FreezeTokenState → List ℕ → FreezeTokenState × List ℕ
  | state, [] => (state, [])
  | state, token :: tokens =>
      let rest := freezeTokenRun quoteCode cutoff (freezeTokenNext state token) tokens
      (rest.1, freezeTokenEmit quoteCode cutoff state token ++ rest.2)

/-- Control state before source-token index `j`. -/
def freezeTokenControlAt (tokenFn : ℕ → ℕ) (n : ℕ) : ℕ → FreezeTokenState
  | 0 => (0, 0)
  | j + 1 => freezeTokenNext (freezeTokenControlAt tokenFn n j)
      (tokenFn (Nat.pair n j))

@[simp] theorem freezeTokenRun_nil (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (state : FreezeTokenState) :
    freezeTokenRun quoteCode cutoff state [] = (state, []) := rfl

lemma freezeTokenRun_append (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (state : FreezeTokenState) (xs ys : List ℕ) :
    freezeTokenRun quoteCode cutoff state (xs ++ ys) =
      let first := freezeTokenRun quoteCode cutoff state xs
      let second := freezeTokenRun quoteCode cutoff first.1 ys
      (second.1, first.2 ++ second.2) := by
  induction xs generalizing state with
  | nil => rfl
  | cons token tokens ih =>
      simp only [List.cons_append, freezeTokenRun]
      rw [ih]
      simp [List.append_assoc]

lemma freezeTokenRun_range (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (tokenFn : ℕ → ℕ) (n count : ℕ) :
    freezeTokenRun quoteCode cutoff (0, 0)
        ((List.range count).map fun j => tokenFn (Nat.pair n j)) =
      (freezeTokenControlAt tokenFn n count,
        (List.range count).flatMap fun j =>
          freezeTokenEmit quoteCode cutoff (freezeTokenControlAt tokenFn n j)
            (tokenFn (Nat.pair n j))) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.range_succ, List.map_append, List.flatMap_append,
        freezeTokenRun_append, ih]
      simp [freezeTokenRun, freezeTokenControlAt]

/-- On a canonical feature serialization the streaming rewrite is exactly
`EF.freezeBefore`. -/
lemma freezeTokenRun_serialize (quote : ℕ → Sentence → ℚ)
    (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (hquote : ∀ day φ, quoteCode day (Encodable.encode φ) =
      Encodable.encode (quote day φ)) (e : EF) :
    freezeTokenRun quoteCode cutoff (0, 0) e.serialize =
      ((0, 0), (e.freezeBefore quote cutoff).serialize) := by
  induction e with
  | price φ day =>
      simp only [serialize, freezeTokenRun, freezeTokenNext, freezeTokenEmit]
      by_cases hday : day < cutoff
      · simp [hday, hquote, freezeBefore, serialize]
      · simp [hday, freezeBefore, serialize]
  | const q => simp [serialize, freezeTokenRun, freezeTokenNext, freezeTokenEmit, freezeBefore]
  | add a b iha ihb =>
      simp only [serialize, freezeBefore, freezeTokenRun_append]
      rw [iha, ihb]
      simp [freezeTokenRun, freezeTokenNext, freezeTokenEmit, List.append_assoc]
  | mul a b iha ihb =>
      simp only [serialize, freezeBefore, freezeTokenRun_append]
      rw [iha, ihb]
      simp [freezeTokenRun, freezeTokenNext, freezeTokenEmit, List.append_assoc]
  | max a b iha ihb =>
      simp only [serialize, freezeBefore, freezeTokenRun_append]
      rw [iha, ihb]
      simp [freezeTokenRun, freezeTokenNext, freezeTokenEmit, List.append_assoc]
  | safeRecip a iha =>
      simp only [serialize, freezeBefore, freezeTokenRun_append]
      rw [iha]
      simp [freezeTokenRun, freezeTokenNext, freezeTokenEmit]
  | var i => simp [serialize, freezeTokenRun, freezeTokenNext, freezeTokenEmit, freezeBefore]
  | letE value body ihv ihb =>
      simp only [serialize, freezeBefore, freezeTokenRun_append]
      rw [ihv, ihb]
      simp [freezeTokenRun, freezeTokenNext, freezeTokenEmit, List.append_assoc]

lemma freezeTokenRun_serializeTrades (quote : ℕ → Sentence → ℚ)
    (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (hquote : ∀ day φ, quoteCode day (Encodable.encode φ) =
      Encodable.encode (quote day φ)) (trades : List (EF × Sentence)) :
    freezeTokenRun quoteCode cutoff (0, 0) (serializeTrades trades) =
      ((0, 0), serializeTrades
        (trades.map fun trade => (trade.1.freezeBefore quote cutoff, trade.2))) := by
  induction trades with
  | nil => rfl
  | cons trade trades ih =>
      rcases trade with ⟨e, φ⟩
      simp only [serializeTrades, List.map_cons, freezeTokenRun_append]
      rw [freezeTokenRun_serialize quote quoteCode cutoff hquote e]
      simp [freezeTokenRun, freezeTokenNext, freezeTokenEmit, ih]

/-- Apply the feature freeze to every feature currently held by the streaming decoder. -/
def freezeStreamState (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    EF.StreamState → EF.StreamState
  | (control, stack, trades) =>
      (control,
        stack.map fun e => e.freezeBefore quote cutoff,
        trades.map fun trade => (trade.1.freezeBefore quote cutoff, trade.2))

/-- The small transducer control agrees with the real decoder control.  In the price-day
mode it additionally remembers the raw code which decoded to the pending sentence. -/
def FreezeTokenState.Matches (control : FreezeTokenState) (state : EF.StreamState) : Prop :=
  control.1 = state.1.1 ∧
    (state.1.1 = 2 → ∃ φ, state.1.2 = some φ ∧
      Encodable.decode (α := Sentence) control.2 = some φ)

lemma freezeToken_initial_matches :
    FreezeTokenState.Matches (0, 0) EF.streamInitial := by
  simp [FreezeTokenState.Matches, EF.streamInitial]

/-- One source token and the bounded suffix emitted for it commute with the actual streaming
decoder.  This includes malformed inputs: the copied offending token fails before an inserted
suffix could repair it. -/
lemma streamReadFrom_freezeTokenEmit
    (quote : ℕ → Sentence → ℚ) (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ))
    (control : FreezeTokenState) (state : EF.StreamState) (token : ℕ)
    (hmatch : control.Matches state) :
    EF.streamReadFrom (freezeTokenEmit quoteCode cutoff control token)
        (some (freezeStreamState quote cutoff state)) =
      (EF.streamStep (some state) token).map (freezeStreamState quote cutoff) ∧
    ∀ next, EF.streamStep (some state) token = some next →
      (freezeTokenNext control token).Matches next := by
  rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
  simp only [FreezeTokenState.Matches] at hmatch ⊢
  rcases hmatch with ⟨hmode, hpending⟩
  rcases control with ⟨controlMode, code⟩
  simp only at hmode
  subst controlMode
  cases mode with
  | zero =>
      by_cases h0 : token = 0
      · subst token
        simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
          EF.streamReadFrom, EF.streamStep]
      by_cases h1 : token = 1
      · subst token
        simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
          EF.streamReadFrom, EF.streamStep]
      by_cases h2 : token = 2
      · subst token
        cases stack with
        | nil => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
            EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
              EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
              EF.streamReadFrom, EF.streamStep, freezeBefore]
      by_cases h3 : token = 3
      · subst token
        cases stack with
        | nil => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
            EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
              EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
              EF.streamReadFrom, EF.streamStep, freezeBefore]
      by_cases h4 : token = 4
      · subst token
        cases stack with
        | nil => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
            EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
              EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
              EF.streamReadFrom, EF.streamStep, freezeBefore]
      by_cases h5 : token = 5
      · subst token
        cases stack <;> simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
          EF.streamReadFrom, EF.streamStep, freezeBefore]
      by_cases h6 : token = 6
      · subst token
        simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
          EF.streamReadFrom, EF.streamStep]
      by_cases h7 : token = 7
      · subst token
        simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
          EF.streamReadFrom, EF.streamStep]
      by_cases h8 : token = 8
      · subst token
        cases stack with
        | nil => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
            EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
              EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
              EF.streamReadFrom, EF.streamStep, freezeBefore]
      · simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
          EF.streamReadFrom, EF.streamStep, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  | succ mode =>
      cases mode with
      | zero =>
          cases hdecode : Encodable.decode (α := Sentence) token <;>
            simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
              EF.streamReadFrom, EF.streamStep, hdecode]
      | succ mode =>
          cases mode with
          | zero =>
              obtain ⟨φ, hpendingEq, hdecode⟩ := hpending rfl
              subst pending
              by_cases hday : token < cutoff
              · simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
                  EF.streamReadFrom, EF.streamStep, hday,
                  hquote token code φ hdecode, freezeBefore]
              · simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
                  EF.streamReadFrom, EF.streamStep, hday, freezeBefore]
          | succ mode =>
              cases mode with
              | zero =>
                  cases hdecode : Encodable.decode (α := ℚ) token <;>
                    simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
                      EF.streamReadFrom, EF.streamStep, hdecode, freezeBefore]
              | succ mode =>
                  cases mode with
                  | zero =>
                      cases stack with
                      | nil => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
                          EF.streamReadFrom, EF.streamStep]
                      | cons e stack =>
                        cases hdecode : Encodable.decode (α := Sentence) token <;>
                          simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
                            EF.streamReadFrom, EF.streamStep, hdecode]
                  | succ mode =>
                      cases mode with
                      | zero => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
                          EF.streamReadFrom, EF.streamStep, freezeBefore]
                      | succ mode => simp [freezeTokenEmit, freezeTokenNext, freezeStreamState,
                          EF.streamReadFrom, EF.streamStep]

@[simp] theorem streamReadFrom_none (tokens : List ℕ) :
    EF.streamReadFrom tokens none = none := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      simp only [EF.streamReadFrom, List.foldl_cons, EF.streamStep]
      simpa [EF.streamReadFrom] using ih

lemma streamReadFrom_freezeTokenRun
    (quote : ℕ → Sentence → ℚ) (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ))
    (control : FreezeTokenState) (state : EF.StreamState) (tokens : List ℕ)
    (hmatch : control.Matches state) :
    let run := freezeTokenRun quoteCode cutoff control tokens
    EF.streamReadFrom run.2 (some (freezeStreamState quote cutoff state)) =
        (EF.streamReadFrom tokens (some state)).map (freezeStreamState quote cutoff) ∧
      ∀ next, EF.streamReadFrom tokens (some state) = some next → run.1.Matches next := by
  induction tokens generalizing control state with
  | nil =>
      simp [freezeTokenRun, EF.streamReadFrom, hmatch]
  | cons token tokens ih =>
      simp only [freezeTokenRun]
      have hstep := streamReadFrom_freezeTokenEmit quote quoteCode cutoff hquote
        control state token hmatch
      rcases hstep with ⟨hstep, hnext⟩
      cases hs : EF.streamStep (some state) token with
      | none =>
          constructor
          · rw [EF.streamReadFrom_append, hstep]
            rw [hs]
            simp only [Option.map_none]
            rw [streamReadFrom_none]
            change none = (EF.streamReadFrom tokens
              (EF.streamStep (some state) token)).map (freezeStreamState quote cutoff)
            rw [hs, streamReadFrom_none]
            rfl
          · intro final hfinalSource
            change EF.streamReadFrom tokens (EF.streamStep (some state) token) =
              some final at hfinalSource
            rw [hs, streamReadFrom_none] at hfinalSource
            contradiction
      | some next =>
          have hmatches := hnext next hs
          have hrest := ih (freezeTokenNext control token) next hmatches
          simp only at hrest
          rcases hrest with ⟨hrest, hfinal⟩
          constructor
          · rw [EF.streamReadFrom_append, hstep, hs]
            simp only [Option.map_some]
            rw [hrest]
            simp [EF.streamReadFrom, hs]
          · intro final hfinalSource
            apply hfinal final
            simpa [EF.streamReadFrom, hs] using hfinalSource

lemma deserializeTrades_freezeTokenRun
    (quote : ℕ → Sentence → ℚ) (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ)) (tokens : List ℕ) :
    let run := freezeTokenRun quoteCode cutoff (0, 0) tokens
    deserializeTrades run.2 =
      (deserializeTrades tokens).map fun trades =>
        trades.map fun trade => (trade.1.freezeBefore quote cutoff, trade.2) := by
  have hrun := (streamReadFrom_freezeTokenRun quote quoteCode cutoff hquote
    (0, 0) EF.streamInitial tokens freezeToken_initial_matches).1
  simp only at hrun ⊢
  have hinitial : freezeStreamState quote cutoff EF.streamInitial = EF.streamInitial := rfl
  rw [hinitial] at hrun
  unfold deserializeTrades
  rw [hrun]
  cases hread : EF.streamReadFrom tokens (some EF.streamInitial) with
  | none => rfl
  | some state =>
      rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
      cases mode <;> cases pending <;> cases stack <;>
        simp [freezeStreamState]

private def validatedTrades (n : ℕ) (trades : List (EF × Sentence)) :
    List (EF × Sentence) :=
  if ∀ trade ∈ trades, trade.1.rank ≤ n then trades else []

private lemma strategyOfTokens_trades_eq (n : ℕ) (tokens : List ℕ) :
    (strategyOfTokens n tokens).trades =
      match deserializeTrades tokens with
      | none => []
      | some trades => validatedTrades n trades := by
  unfold strategyOfTokens validatedTrades
  split <;> rename_i hdecode
  · simp [hdecode]
  · split <;> simp_all

lemma strategyOfTokens_freezeTokenRun_trades
    (quote : ℕ → Sentence → ℚ) (quoteCode : ℕ → ℕ → ℕ) (cutoff n : ℕ)
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ)) (tokens : List ℕ) :
    let run := freezeTokenRun quoteCode cutoff (0, 0) tokens
    (strategyOfTokens n run.2).trades =
      (strategyOfTokens n tokens).trades.map fun trade =>
        (trade.1.freezeBefore quote cutoff, trade.2) := by
  have hdecode := deserializeTrades_freezeTokenRun quote quoteCode cutoff hquote tokens
  simp only at hdecode ⊢
  rw [strategyOfTokens_trades_eq, strategyOfTokens_trades_eq, hdecode]
  cases hs : deserializeTrades tokens with
  | none => simp
  | some trades =>
      simp only [Option.map_some]
      have hrank :
          (∀ trade ∈ trades.map (fun trade =>
              (trade.1.freezeBefore quote cutoff, trade.2)), trade.1.rank ≤ n) ↔
            ∀ trade ∈ trades, trade.1.rank ≤ n := by
        constructor
        · intro h trade hmem
          have hmapped : (trade.1.freezeBefore quote cutoff, trade.2) ∈
              trades.map (fun trade =>
                (trade.1.freezeBefore quote cutoff, trade.2)) :=
            List.mem_map_of_mem hmem
          simpa using h _ hmapped
        · intro h trade hmem
          simp only [List.mem_map] at hmem
          obtain ⟨source, hsource, rfl⟩ := hmem
          simpa using h source hsource
      by_cases hvalid : ∀ trade ∈ trades, trade.1.rank ≤ n
      · have hfrozenValid := hrank.mpr hvalid
        unfold validatedTrades
        rw [if_pos hfrozenValid, if_pos hvalid]
      · have hfrozenInvalid : ¬∀ trade ∈ trades.map (fun trade =>
            (trade.1.freezeBefore quote cutoff, trade.2)), trade.1.rank ≤ n :=
          fun h => hvalid (hrank.mp h)
        unfold validatedTrades
        rw [if_neg hfrozenInvalid, if_neg hvalid]
        rfl

/-- If `quote` is the old prefix of `P` and `P'` agrees with `P` after the cutoff,
the frozen feature sees exactly what the original feature saw against `P`. -/
lemma freezeBefore_denoteWith
    (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (P P' : History)
    (hprefix : ∀ day < cutoff, ∀ φ, P day φ = (quote day φ : ℝ))
    (htail : ∀ day, cutoff ≤ day → ∀ φ, P day φ = P' day φ) :
    ∀ ρ : List ℝ,
      (e.freezeBefore quote cutoff).denoteWith ρ P' = e.denoteWith ρ P := by
  induction e with
  | price φ day =>
      intro ρ
      simp only [freezeBefore]
      by_cases hday : day < cutoff
      · simp [hday, hprefix day hday φ]
      · simp [hday, htail day (Nat.le_of_not_gt hday) φ]
  | const q => intro ρ; rfl
  | add a b iha ihb => intro ρ; simp [freezeBefore, iha ρ, ihb ρ]
  | mul a b iha ihb => intro ρ; simp [freezeBefore, iha ρ, ihb ρ]
  | max a b iha ihb => intro ρ; simp [freezeBefore, iha ρ, ihb ρ]
  | safeRecip a iha => intro ρ; simp [freezeBefore, iha ρ]
  | var i => intro ρ; rfl
  | letE value body ihv ihb =>
      intro ρ
      simp only [freezeBefore, denoteWith_letE]
      rw [ihv ρ, ihb]

lemma freezeBefore_denote
    (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (P P' : History)
    (hprefix : ∀ day < cutoff, ∀ φ, P day φ = (quote day φ : ℝ))
    (htail : ∀ day, cutoff ≤ day → ∀ φ, P day φ = P' day φ) :
    (e.freezeBefore quote cutoff).denote P' = e.denote P := by
  exact e.freezeBefore_denoteWith quote cutoff P P' hprefix htail []

end EF

namespace Strategy

/-- Apply the old-price freeze to every coefficient of a strategy. -/
def freezeBefore {day : ℕ} (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (T : Strategy day) : Strategy day where
  trades := T.trades.map fun p => (p.1.freezeBefore quote cutoff, p.2)
  rank_le := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (q.1.freezeBefore_rank_le quote cutoff).trans (T.rank_le q hq)

/-- On an unchanged tail day, a frozen strategy against `P'` has exactly the value of the
original strategy against `P`. -/
lemma freezeBefore_value
    {day : ℕ} (T : Strategy day) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (P P' : History) (w : Valuation)
    (hprefix : ∀ d < cutoff, ∀ φ, P d φ = (quote d φ : ℝ))
    (htail : ∀ d, cutoff ≤ d → ∀ φ, P d φ = P' d φ)
    (hday : cutoff ≤ day) :
    (T.freezeBefore quote cutoff).value P' w = T.value P w := by
  simp only [Strategy.value, freezeBefore, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply]
  rw [p.1.freezeBefore_denote quote cutoff P P' hprefix htail]
  rw [← htail day hday p.2]

end Strategy

namespace Trader

/-- The paper's false-report trader: coefficients see the frozen old prefix. -/
def freezeBefore (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (Tr : Trader) : Trader where
  strat day := (Tr.strat day).freezeBefore quote cutoff

lemma freezeBefore_value_tail
    (Tr : Trader) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (P P' : History) (w : Valuation)
    (hprefix : ∀ d < cutoff, ∀ φ, P d φ = (quote d φ : ℝ))
    (htail : ∀ d, cutoff ≤ d → ∀ φ, P d φ = P' d φ)
    {day : ℕ} (hday : cutoff ≤ day) :
    ((Tr.freezeBefore quote cutoff).strat day).value P' w =
      (Tr.strat day).value P w := by
  exact (Tr.strat day).freezeBefore_value quote cutoff P P' w hprefix htail hday

/-- A concrete finite bound for the discrepancy contributed by the finitely many days
before `cutoff`. -/
noncomputable def freezeBeforeErrorBound
    (Tr : Trader) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (P P' : History) : ℝ :=
  ∑ day ∈ Finset.range cutoff,
    ((Tr.strat day).magnitude P +
      (((Tr.freezeBefore quote cutoff).strat day).magnitude P'))

/-- The original and frozen traders' net worths differ by at most the explicit finite
prefix bound.  Every tail summand cancels exactly; the only estimate is the standard
`|strategy value| ≤ magnitude` bound on the finitely many early days. -/
lemma freezeBefore_netWorth_difference_le
    (Tr : Trader) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (P P' : History)
    (hprefix : ∀ d < cutoff, ∀ φ, P d φ = (quote d φ : ℝ))
    (htail : ∀ d, cutoff ≤ d → ∀ φ, P d φ = P' d φ)
    (hP : ∀ d φ, 0 ≤ P d φ ∧ P d φ ≤ 1)
    (hP' : ∀ d φ, 0 ≤ P' d φ ∧ P' d φ ≤ 1)
    (v : PCWorld) (n : ℕ) :
    |Tr.netWorth P v n - (Tr.freezeBefore quote cutoff).netWorth P' v n| ≤
      Tr.freezeBeforeErrorBound quote cutoff P P' := by
  let g : ℕ → ℝ := fun day ↦
    (Tr.strat day).magnitude P +
      (((Tr.freezeBefore quote cutoff).strat day).magnitude P')
  have hw : ∀ φ, v.payout φ = 0 ∨ v.payout φ = 1 := by
    intro φ
    by_cases hφ : v.Holds φ
    · exact Or.inr (by simp [PCWorld.payout, hφ])
    · exact Or.inl (by simp [PCWorld.payout, hφ])
  have hterm : ∀ day,
      |(Tr.strat day).value P v.payout -
          ((Tr.freezeBefore quote cutoff).strat day).value P' v.payout| ≤
        if day < cutoff then g day else 0 := by
    intro day
    by_cases hday : day < cutoff
    · rw [if_pos hday]
      exact (abs_sub _ _).trans (add_le_add
        (Strategy.abs_value_le_magnitude (Tr.strat day) P v.payout hw (hP day))
        (Strategy.abs_value_le_magnitude
          ((Tr.freezeBefore quote cutoff).strat day) P' v.payout hw (hP' day)))
    · rw [if_neg hday]
      have heq := Tr.freezeBefore_value_tail quote cutoff P P' v.payout
        hprefix htail (Nat.le_of_not_gt hday)
      rw [heq]
      simp
  have hg : ∀ day, 0 ≤ g day := by
    intro day
    exact add_nonneg (Strategy.magnitude_nonneg _ _) (Strategy.magnitude_nonneg _ _)
  calc
    |Tr.netWorth P v n - (Tr.freezeBefore quote cutoff).netWorth P' v n| =
        |∑ day ∈ Finset.range (n + 1),
          ((Tr.strat day).value P v.payout -
            ((Tr.freezeBefore quote cutoff).strat day).value P' v.payout)| := by
          simp only [Trader.netWorth]
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ day ∈ Finset.range (n + 1),
          |(Tr.strat day).value P v.payout -
            ((Tr.freezeBefore quote cutoff).strat day).value P' v.payout| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ day ∈ Finset.range (n + 1),
          if day < cutoff then g day else 0 :=
          Finset.sum_le_sum (fun day _ ↦ hterm day)
    _ = ∑ day ∈ (Finset.range (n + 1)).filter (fun day ↦ day < cutoff),
          g day := by rw [Finset.sum_filter]
    _ ≤ ∑ day ∈ Finset.range cutoff, g day := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro day hday
            simp only [Finset.mem_filter, Finset.mem_range] at hday ⊢
            exact hday.2
          · intro day _ _
            exact hg day
    _ = Tr.freezeBeforeErrorBound quote cutoff P P' := rfl

end Trader

/-- Uniform bounded net-worth error preserves exploitation.  This is the abstract finite-
prefix accounting step used in both directions of `thm:ifp`. -/
theorem Trader.Exploits.of_boundedDifference
    {Tr Tr' : Trader} {P P' : History} {DP : DeductiveProcess}
    (h : Tr.Exploits P DP) (C : ℝ)
    (hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
      |Tr.netWorth P v n - Tr'.netWorth P' v n| ≤ C) :
    Tr'.Exploits P' DP := by
  rcases h with ⟨⟨L, hL⟩, hnotAbove⟩
  refine ⟨⟨L - C, ?_⟩, ?_⟩
  · rintro x ⟨n, v, hv, rfl⟩
    have hbase := hL ⟨n, v, hv, rfl⟩
    have herr := hdiff n v hv
    rw [abs_le] at herr
    linarith
  · intro hUpper
    apply hnotAbove
    rcases hUpper with ⟨U, hU⟩
    refine ⟨U + C, ?_⟩
    rintro x ⟨n, v, hv, rfl⟩
    have hpatched := hU ⟨n, v, hv, rfl⟩
    have herr := hdiff n v hv
    rw [abs_le] at herr
    linarith

/-- The narrowly computational boundary in finite-prefix closure: the administrative syntax
freeze above preserves token-indexed polynomial emission.  It contains no semantic market
claim and no exploitation or convergence conclusion.

**This is a paper erratum, not a modeling substitution** (see the file header and
PROGRESS.md "Paper errata").  `app:ifp` asserts this closure is immediate because "only
finitely many constants are needed"; that is false — finitely many *days*, but unboundedly
many sentences.  This structure is **not inhabited for every `ComputableMarket P`**: a
market with huge-encoding day-`0` quotes admits no such patch at all.  Do not read it as a
routine obligation awaiting labor; instantiating it is a real claim about `P`.

For `LIA` it *is* inhabitable — each day's quote table is a finite `RationalBeliefState`
entry list, so the freeze is a hardcodable finite lookup with constant-size tokens.  That
is `M7-PREFIX-PATCH`.
Paper node: `app:ifp` -/
structure EfficientPrefixPatch (P : History) (cutoff : ℕ) where
  quote : ℕ → Sentence → ℚ
  quote_exact : ∀ day < cutoff, ∀ φ, P day φ = (quote day φ : ℝ)
  preserves_ec : ∀ Tr : Trader, EfficientlyComputableTok Tr →
    EfficientlyComputableTok (Tr.freezeBefore quote cutoff)

/-- **Closure under Finite Perturbations** (`thm:ifp`), with the exact computational
qualification forced by this repository's clocked model.  The two histories agree from
`cutoff` onward, and each finite prefix supplies the concrete efficient-freeze certificate
above.  The conclusion is the paper's biconditional, not merely one direction.
Paper node: `thm:ifp` -/
theorem lic_iff_of_finitePerturbation
    (P P' : History) (DP : DeductiveProcess) (cutoff : ℕ)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1)
    (hP' : ∀ day φ, 0 ≤ P' day φ ∧ P' day φ ≤ 1)
    (htail : ∀ day, cutoff ≤ day → ∀ φ, P day φ = P' day φ)
    (patchP : EfficientPrefixPatch P cutoff)
    (patchP' : EfficientPrefixPatch P' cutoff) :
    IsLogicalInductor P DP ↔ IsLogicalInductor P' DP := by
  constructor
  · intro hLI
    exact {
      marketComputable := hP'comp
      processComputable := hLI.processComputable
      noExploit := by
        intro Tr hTr hExploits
        let frozen := Tr.freezeBefore patchP'.quote cutoff
        have hfrozenEC : EfficientlyComputableTok frozen :=
          patchP'.preserves_ec Tr hTr
        have hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
            |Tr.netWorth P' v n - frozen.netWorth P v n| ≤
              Tr.freezeBeforeErrorBound patchP'.quote cutoff P' P := by
          intro n v hv
          exact Tr.freezeBefore_netWorth_difference_le patchP'.quote cutoff P' P
            patchP'.quote_exact
            (fun day hday φ ↦ (htail day hday φ).symm)
            hP' hP v n
        have hfrozenExploits : frozen.Exploits P DP :=
          hExploits.of_boundedDifference
            (Tr.freezeBeforeErrorBound patchP'.quote cutoff P' P) hdiff
        exact hLI.noExploit frozen hfrozenEC hfrozenExploits }
  · intro hLI'
    exact {
      marketComputable := hPcomp
      processComputable := hLI'.processComputable
      noExploit := by
        intro Tr hTr hExploits
        let frozen := Tr.freezeBefore patchP.quote cutoff
        have hfrozenEC : EfficientlyComputableTok frozen :=
          patchP.preserves_ec Tr hTr
        have hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
            |Tr.netWorth P v n - frozen.netWorth P' v n| ≤
              Tr.freezeBeforeErrorBound patchP.quote cutoff P P' := by
          intro n v hv
          exact Tr.freezeBefore_netWorth_difference_le patchP.quote cutoff P P'
            patchP.quote_exact htail hP hP' v n
        have hfrozenExploits : frozen.Exploits P' DP :=
          hExploits.of_boundedDifference
            (Tr.freezeBeforeErrorBound patchP.quote cutoff P P') hdiff
        exact hLI'.noExploit frozen hfrozenEC hfrozenExploits }

end LogicalInduction

#print axioms LogicalInduction.EF.freezeBefore_denote
#print axioms LogicalInduction.Strategy.freezeBefore_value
#print axioms LogicalInduction.Trader.freezeBefore_netWorth_difference_le
#print axioms LogicalInduction.Trader.Exploits.of_boundedDifference
#print axioms LogicalInduction.lic_iff_of_finitePerturbation
