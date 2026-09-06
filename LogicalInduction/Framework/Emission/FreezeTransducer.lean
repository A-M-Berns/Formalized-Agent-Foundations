import LogicalInduction.Framework.Criterion

/-!
# The price freeze and its streaming transducer

The syntactic operation §4.6 transports a trader with, together with the flat-token model of
it that a machine-class trader must run. Both are operations on the feature syntax `EF` and
on its token serialization, so they live beside the rest of the emission vocabulary; the
§4.6 theorems that consume them are `Properties/FinitePerturbations.lean`.

## The selector-indexed freeze

`EF.freezeOn quote sel` is the single freeze recursion: it replaces each selected price leaf
by `letE (price φ day) (const (quote day φ))`, keeping the original leaf as an administrative
dead binding for the parser-transparency and rank reasons recorded at that declaration.
`EF.freezeBefore` is its `day < cutoff` instance, so `freezeBefore_eq_freezeOn` is `rfl` and
every day-cutoff law is a transport rather than a parallel induction.

The laws proved of it are rank preservation (`EF.freezeOn_rank`), the size bound
`cost ≤ 3 * cost` (`EF.freezeOn_cost_le`) and exact denotational transport
(`EF.freezeOn_denoteWith`).

## The flat-token model

`EF.freezeTokenRunOn` is a bounded streaming transducer over a *code-level* selector
`selCode : ℕ → ℕ → Bool`, since the day and the pending sentence code are all the transducer
has. `EF.strategyOfTokens_freezeTokenRunOn_trades` transports the decoded strategy across it
on every token stream, well-formed or garbage, given the bridge `hsel` from `selCode` to the
sentence-level selector `EF.freezeOn` reads. `EF.freezeTokenRunOn_serialize` and
`EF.freezeTokenRunOn_serializeTrades` specify the transducer on canonical input: on a
canonical feature serialization the streaming rewrite is exactly `EF.freezeOn`.

`EF.freezeTokenRun` and `EF.cutoffSel_bridge` are the day-cutoff instance of the token model.

Consumers are `Properties/FinitePerturbations.lean` and the §4.6/§4.7 compilers
`Construction/Freeze/{Compiler,Prefix}.lean` and
`Construction/Conditioning/{Compiler,PricePass,FramePass}.lean`.
-/

namespace LogicalInduction

open scoped BigOperators

namespace EF

/-! ## The selector-indexed freeze

`EF.freezeOn` freezes exactly the price coordinates a `Bool`-valued selector picks out;
`freezeBefore` below is its `day < cutoff` instance. -/

/-- Freeze exactly the price leaves whose coordinate is selected.

The administrative `letE` deliberately keeps the dead original price leaf.  Its body is
the constant quote, so the denotation is independent of that leaf, while keeping it makes
the flat-token rewrite parser-transparent and preserves the feature's original rank.  This
matters for arbitrary clocked trader programs: malformed sentence tokens stay malformed and
a rank-invalid source program cannot become valid merely because an old leaf was frozen.

With `sel = fun d _ => decide (d < cutoff)` this is `EF.freezeBefore`; with
`sel = fun d φ => decide ((d, φ) ∈ S)` it is the finite-support freeze. -/
def freezeOn (quote : ℕ → Sentence → ℚ) (sel : ℕ → Sentence → Bool) : EF → EF
  | .price φ day =>
      if sel day φ then .letE (.price φ day) (.const (quote day φ)) else .price φ day
  | .const q => .const q
  | .add a b => .add (a.freezeOn quote sel) (b.freezeOn quote sel)
  | .mul a b => .mul (a.freezeOn quote sel) (b.freezeOn quote sel)
  | .max a b => .max (a.freezeOn quote sel) (b.freezeOn quote sel)
  | .safeRecip a => .safeRecip (a.freezeOn quote sel)
  | .var i => .var i
  | .letE value body =>
      .letE (value.freezeOn quote sel) (body.freezeOn quote sel)

@[simp] lemma freezeOn_rank (e : EF) (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) : (e.freezeOn quote sel).rank = e.rank := by
  induction e with
  | price φ day => simp only [freezeOn]; split <;> simp
  | const q => simp [freezeOn]
  | add a b iha ihb => simp [freezeOn, iha, ihb]
  | mul a b iha ihb => simp [freezeOn, iha, ihb]
  | max a b iha ihb => simp [freezeOn, iha, ihb]
  | safeRecip a iha => simp [freezeOn, iha]
  | var i => simp [freezeOn]
  | letE value body ihv ihb => simp [freezeOn, ihv, ihb]

lemma freezeOn_rank_le (e : EF) (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) : (e.freezeOn quote sel).rank ≤ e.rank := by
  rw [freezeOn_rank]

/-- **Size law.**  The administrative binding makes the literal rewrite at most three times
larger, which is what justifies keeping the dead original leaf: the freeze stays a
constant-factor syntax transformation. -/
lemma freezeOn_cost_le (e : EF) (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) : (e.freezeOn quote sel).cost ≤ 3 * e.cost := by
  induction e with
  | price φ day => simp only [freezeOn]; split <;> simp [cost]
  | const q => norm_num [freezeOn, cost]
  | add a b iha ihb => simp only [freezeOn, cost]; omega
  | mul a b iha ihb => simp only [freezeOn, cost]; omega
  | max a b iha ihb => simp only [freezeOn, cost]; omega
  | safeRecip a iha => simp only [freezeOn, cost]; omega
  | var i => norm_num [freezeOn, cost]
  | letE value body ihv ihb => simp only [freezeOn, cost]; omega

/-- **Exact denotational transport.**  Every selected leaf reads its frozen constant,
which is the `P`-price; every unselected leaf reads the `P'`-price, which *is* the
`P`-price.  So the frozen feature against `P'` denotes exactly what the original feature
denoted against `P` — no error term, and no constraint on the day. -/
lemma freezeOn_denoteWith (e : EF) (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) (P P' : History)
    (hin : ∀ d φ, sel d φ = true → P d φ = (quote d φ : ℝ))
    (hout : ∀ d φ, sel d φ = false → P d φ = P' d φ) :
    ∀ ρ : List ℝ, (e.freezeOn quote sel).denoteWith ρ P' = e.denoteWith ρ P := by
  induction e with
  | price φ day =>
      intro ρ
      simp only [freezeOn]
      cases hsel : sel day φ with
      | true => simp [hsel, hin day φ hsel]
      | false => simp [hsel, hout day φ hsel]
  | const q => intro ρ; rfl
  | add a b iha ihb => intro ρ; simp [freezeOn, iha ρ, ihb ρ]
  | mul a b iha ihb => intro ρ; simp [freezeOn, iha ρ, ihb ρ]
  | max a b iha ihb => intro ρ; simp [freezeOn, iha ρ, ihb ρ]
  | safeRecip a iha => intro ρ; simp [freezeOn, iha ρ]
  | var i => intro ρ; rfl
  | letE value body ihv ihb =>
      intro ρ
      simp only [freezeOn, denoteWith_letE]
      rw [ihv ρ, ihb]

lemma freezeOn_denote (e : EF) (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) (P P' : History)
    (hin : ∀ d φ, sel d φ = true → P d φ = (quote d φ : ℝ))
    (hout : ∀ d φ, sel d φ = false → P d φ = P' d φ) :
    (e.freezeOn quote sel).denote P' = e.denote P :=
  e.freezeOn_denoteWith quote sel P P' hin hout []

/-! ### The day-cutoff instance

`freezeBefore` freezes every price leaf strictly before `cutoff` at its exact rational
quote.  It is *defined* as the `day < cutoff` instance of `freezeOn`, so
`freezeBefore_eq_freezeOn` is `rfl` and every law below is a transport rather than a
parallel induction. -/

/-- The day-cutoff freeze, as the `day < cutoff` instance of `EF.freezeOn`. -/
def freezeBefore (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (e : EF) : EF :=
  e.freezeOn quote (fun d _ => decide (d < cutoff))

/-- The day-cutoff freeze *is* the selector freeze at the day-cutoff selector. -/
lemma freezeBefore_eq_freezeOn (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    e.freezeBefore quote cutoff = e.freezeOn quote (fun d _ => decide (d < cutoff)) := rfl

/-- Defining equation at a price leaf, in the `Prop`-valued day test. -/
@[simp] lemma freezeBefore_price (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (φ : Sentence) (day : ℕ) :
    (EF.price φ day).freezeBefore quote cutoff =
      if day < cutoff then .letE (.price φ day) (.const (quote day φ))
      else .price φ day := by
  simp only [freezeBefore, freezeOn, decide_eq_true_eq]

@[simp] lemma freezeBefore_const (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (q : ℚ) :
    (EF.const q).freezeBefore quote cutoff = .const q := rfl

@[simp] lemma freezeBefore_var (quote : ℕ → Sentence → ℚ) (cutoff i : ℕ) :
    (EF.var i).freezeBefore quote cutoff = .var i := rfl

@[simp] lemma freezeBefore_add (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (a b : EF) :
    (EF.add a b).freezeBefore quote cutoff =
      .add (a.freezeBefore quote cutoff) (b.freezeBefore quote cutoff) := rfl

@[simp] lemma freezeBefore_mul (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (a b : EF) :
    (EF.mul a b).freezeBefore quote cutoff =
      .mul (a.freezeBefore quote cutoff) (b.freezeBefore quote cutoff) := rfl

@[simp] lemma freezeBefore_max (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (a b : EF) :
    (EF.max a b).freezeBefore quote cutoff =
      .max (a.freezeBefore quote cutoff) (b.freezeBefore quote cutoff) := rfl

@[simp] lemma freezeBefore_safeRecip (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (a : EF) :
    (EF.safeRecip a).freezeBefore quote cutoff =
      .safeRecip (a.freezeBefore quote cutoff) := rfl

@[simp] lemma freezeBefore_letE (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (v b : EF) :
    (EF.letE v b).freezeBefore quote cutoff =
      .letE (v.freezeBefore quote cutoff) (b.freezeBefore quote cutoff) := rfl

/-- The dead leaf the binding keeps makes the administrative freeze rank-preserving. -/
@[simp] lemma freezeBefore_rank (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    (e.freezeBefore quote cutoff).rank = e.rank :=
  e.freezeOn_rank quote _

/-- If `quote` is the old prefix of `P` and `P'` agrees with `P` after the cutoff,
the frozen feature sees exactly what the original feature saw against `P`.  A transport of
`freezeOn_denoteWith` along the day-cutoff selector. -/
lemma freezeBefore_denoteWith
    (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (P P' : History)
    (hprefix : ∀ day < cutoff, ∀ φ, P day φ = (quote day φ : ℝ))
    (htail : ∀ day, cutoff ≤ day → ∀ φ, P day φ = P' day φ) :
    ∀ ρ : List ℝ,
      (e.freezeBefore quote cutoff).denoteWith ρ P' = e.denoteWith ρ P :=
  e.freezeOn_denoteWith quote _ P P'
    (fun d φ h => hprefix d (by simpa using h) φ)
    (fun d φ h => htail d (by simpa using h) φ)

lemma freezeBefore_denote
    (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (P P' : History)
    (hprefix : ∀ day < cutoff, ∀ φ, P day φ = (quote day φ : ℝ))
    (htail : ∀ day, cutoff ≤ day → ∀ φ, P day φ = P' day φ) :
    (e.freezeBefore quote cutoff).denote P' = e.denote P :=
  e.freezeBefore_denoteWith quote cutoff P P' hprefix htail []

/-! ## The flat-token model of the freeze

The price leaf the binding keeps makes the compiler a bounded streaming transducer.  It copies every
input token and, immediately after an old price frame `[0, phi, day]`, appends the constant
and administrative-binding suffix `[1, quote, 8]`.  `freezeTokenRunOn_serialize` and
`freezeTokenRunOn_serializeTrades` specify it on canonical input;
`strategyOfTokens_freezeTokenRunOn_trades` is the corresponding statement about the decoded
trades of an arbitrary stream. -/

/-- Parser control needed by the flat-token prefix transducer: `(mode, pendingSentenceCode)`.
The modes agree with `EF.streamStep`; only mode `2` uses the pending code. -/
abbrev FreezeTokenState := ℕ × ℕ

/-- The transducer's parser-control transition, on the modes described at
`FreezeTokenState`.  Shared infrastructure: the `Construction/Freeze/` and
`Construction/Conditioning/` compilers reuse this same automaton, so it is not private to
the laws below. -/
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

/-- Tokens emitted while consuming one source token.

`selCode` is the **code-level** selector: at a price-day slot it is applied to the day just
read and to the pending sentence *code* buffered by the parser control, because that is all
the transducer has.  The hypothesis `hsel` carried by the laws below is the bridge to the
sentence-level `sel` that `EF.freezeOn` uses. -/
def freezeTokenEmitOn (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (state : FreezeTokenState) (token : ℕ) : List ℕ :=
  if state.1 = 2 ∧ selCode token state.2 = true then
    [token, 1, quoteCode token state.2, 8]
  else
    [token]

/-- Run the prefix transducer, returning its final parser control and emitted stream. -/
def freezeTokenRunOn (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) :
    FreezeTokenState → List ℕ → FreezeTokenState × List ℕ
  | state, [] => (state, [])
  | state, token :: tokens =>
      let rest := freezeTokenRunOn selCode quoteCode (freezeTokenNext state token) tokens
      (rest.1, freezeTokenEmitOn selCode quoteCode state token ++ rest.2)

/-- Control state before source-token index `j`. -/
def freezeTokenControlAt (tokenFn : ℕ → ℕ) (n : ℕ) : ℕ → FreezeTokenState
  | 0 => (0, 0)
  | j + 1 => freezeTokenNext (freezeTokenControlAt tokenFn n j)
      (tokenFn (Nat.pair n j))

@[simp] lemma freezeTokenRunOn_nil (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (state : FreezeTokenState) :
    freezeTokenRunOn selCode quoteCode state [] = (state, []) := rfl

lemma freezeTokenRunOn_append (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (state : FreezeTokenState) (xs ys : List ℕ) :
    freezeTokenRunOn selCode quoteCode state (xs ++ ys) =
      let first := freezeTokenRunOn selCode quoteCode state xs
      let second := freezeTokenRunOn selCode quoteCode first.1 ys
      (second.1, first.2 ++ second.2) := by
  induction xs generalizing state with
  | nil => rfl
  | cons token tokens ih =>
      simp only [List.cons_append, freezeTokenRunOn]
      rw [ih]
      simp [List.append_assoc]

lemma freezeTokenRunOn_range (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (tokenFn : ℕ → ℕ) (n count : ℕ) :
    freezeTokenRunOn selCode quoteCode (0, 0)
        ((List.range count).map fun j => tokenFn (Nat.pair n j)) =
      (freezeTokenControlAt tokenFn n count,
        (List.range count).flatMap fun j =>
          freezeTokenEmitOn selCode quoteCode (freezeTokenControlAt tokenFn n j)
            (tokenFn (Nat.pair n j))) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.range_succ, List.map_append, List.flatMap_append,
        freezeTokenRunOn_append, ih]
      simp [freezeTokenRunOn, freezeTokenControlAt]

/-- On a canonical feature serialization the streaming rewrite is exactly
`EF.freezeOn`. -/
lemma freezeTokenRunOn_serialize (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ day φ, selCode day (Encodable.encode φ) = sel day φ)
    (hquote : ∀ day φ, quoteCode day (Encodable.encode φ) =
      Encodable.encode (quote day φ)) (e : EF) :
    freezeTokenRunOn selCode quoteCode (0, 0) e.serialize =
      ((0, 0), (e.freezeOn quote sel).serialize) := by
  induction e with
  | price φ day =>
      simp only [serialize, freezeTokenRunOn, freezeTokenNext, freezeTokenEmitOn]
      by_cases hday : sel day φ = true
      · simp [hsel, hday, hquote, freezeOn, serialize]
      · simp [hsel, hday, freezeOn, serialize]
  | const q => simp [serialize, freezeTokenRunOn, freezeTokenNext, freezeTokenEmitOn, freezeOn]
  | add a b iha ihb =>
      simp only [serialize, freezeOn, freezeTokenRunOn_append]
      rw [iha, ihb]
      simp [freezeTokenRunOn, freezeTokenNext, freezeTokenEmitOn, List.append_assoc]
  | mul a b iha ihb =>
      simp only [serialize, freezeOn, freezeTokenRunOn_append]
      rw [iha, ihb]
      simp [freezeTokenRunOn, freezeTokenNext, freezeTokenEmitOn, List.append_assoc]
  | max a b iha ihb =>
      simp only [serialize, freezeOn, freezeTokenRunOn_append]
      rw [iha, ihb]
      simp [freezeTokenRunOn, freezeTokenNext, freezeTokenEmitOn, List.append_assoc]
  | safeRecip a iha =>
      simp only [serialize, freezeOn, freezeTokenRunOn_append]
      rw [iha]
      simp [freezeTokenRunOn, freezeTokenNext, freezeTokenEmitOn]
  | var i => simp [serialize, freezeTokenRunOn, freezeTokenNext, freezeTokenEmitOn, freezeOn]
  | letE value body ihv ihb =>
      simp only [serialize, freezeOn, freezeTokenRunOn_append]
      rw [ihv, ihb]
      simp [freezeTokenRunOn, freezeTokenNext, freezeTokenEmitOn, List.append_assoc]

lemma freezeTokenRunOn_serializeTrades (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ day φ, selCode day (Encodable.encode φ) = sel day φ)
    (hquote : ∀ day φ, quoteCode day (Encodable.encode φ) =
      Encodable.encode (quote day φ)) (trades : List (EF × Sentence)) :
    freezeTokenRunOn selCode quoteCode (0, 0) (serializeTrades trades) =
      ((0, 0), serializeTrades
        (trades.map fun trade => (trade.1.freezeOn quote sel, trade.2))) := by
  induction trades with
  | nil => rfl
  | cons trade trades ih =>
      rcases trade with ⟨e, φ⟩
      simp only [serializeTrades, List.map_cons, freezeTokenRunOn_append]
      rw [freezeTokenRunOn_serialize quote sel selCode quoteCode hsel hquote e]
      simp [freezeTokenRunOn, freezeTokenNext, freezeTokenEmitOn, ih]

/-- Apply the feature freeze to every feature currently held by the streaming decoder. -/
def freezeStreamStateOn (quote : ℕ → Sentence → ℚ) (sel : ℕ → Sentence → Bool) :
    EF.StreamState → EF.StreamState
  | (control, stack, trades) =>
      (control,
        stack.map fun e => e.freezeOn quote sel,
        trades.map fun trade => (trade.1.freezeOn quote sel, trade.2))

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
lemma streamReadFrom_freezeTokenEmitOn
    (quote : ℕ → Sentence → ℚ) (sel : ℕ → Sentence → Bool)
    (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      selCode day code = sel day φ)
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ))
    (control : FreezeTokenState) (state : EF.StreamState) (token : ℕ)
    (hmatch : control.Matches state) :
    EF.streamReadFrom (freezeTokenEmitOn selCode quoteCode control token)
        (some (freezeStreamStateOn quote sel state)) =
      (EF.streamStep (some state) token).map (freezeStreamStateOn quote sel) ∧
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
        simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
          EF.streamReadFrom, EF.streamStep]
      by_cases h1 : token = 1
      · subst token
        simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
          EF.streamReadFrom, EF.streamStep]
      by_cases h2 : token = 2
      · subst token
        cases stack with
        | nil => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
            EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
              EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
              EF.streamReadFrom, EF.streamStep, freezeOn]
      by_cases h3 : token = 3
      · subst token
        cases stack with
        | nil => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
            EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
              EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
              EF.streamReadFrom, EF.streamStep, freezeOn]
      by_cases h4 : token = 4
      · subst token
        cases stack with
        | nil => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
            EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
              EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
              EF.streamReadFrom, EF.streamStep, freezeOn]
      by_cases h5 : token = 5
      · subst token
        cases stack <;> simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
          EF.streamReadFrom, EF.streamStep, freezeOn]
      by_cases h6 : token = 6
      · subst token
        simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
          EF.streamReadFrom, EF.streamStep]
      by_cases h7 : token = 7
      · subst token
        simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
          EF.streamReadFrom, EF.streamStep]
      by_cases h8 : token = 8
      · subst token
        cases stack with
        | nil => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
            EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
              EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
              EF.streamReadFrom, EF.streamStep, freezeOn]
      · simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
          EF.streamReadFrom, EF.streamStep, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  | succ mode =>
      cases mode with
      | zero =>
          cases hdecode : Encodable.decode (α := Sentence) token <;>
            simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
              EF.streamReadFrom, EF.streamStep, hdecode]
      | succ mode =>
          cases mode with
          | zero =>
              obtain ⟨φ, hpendingEq, hdecode⟩ := hpending rfl
              subst pending
              have hcode := hsel token code φ hdecode
              by_cases hday : sel token φ = true
              · simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
                  EF.streamReadFrom, EF.streamStep, hcode, hday,
                  hquote token code φ hdecode, freezeOn]
              · simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
                  EF.streamReadFrom, EF.streamStep, hcode, hday, freezeOn]
          | succ mode =>
              cases mode with
              | zero =>
                  cases hdecode : Encodable.decode (α := ℚ) token <;>
                    simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
                      EF.streamReadFrom, EF.streamStep, hdecode, freezeOn]
              | succ mode =>
                  cases mode with
                  | zero =>
                      cases stack with
                      | nil => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
                          EF.streamReadFrom, EF.streamStep]
                      | cons e stack =>
                        cases hdecode : Encodable.decode (α := Sentence) token <;>
                          simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
                            EF.streamReadFrom, EF.streamStep, hdecode]
                  | succ mode =>
                      cases mode with
                      | zero => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
                          EF.streamReadFrom, EF.streamStep, freezeOn]
                      | succ mode => simp [freezeTokenEmitOn, freezeTokenNext, freezeStreamStateOn,
                          EF.streamReadFrom, EF.streamStep]

lemma streamReadFrom_freezeTokenRunOn
    (quote : ℕ → Sentence → ℚ) (sel : ℕ → Sentence → Bool)
    (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      selCode day code = sel day φ)
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ))
    (control : FreezeTokenState) (state : EF.StreamState) (tokens : List ℕ)
    (hmatch : control.Matches state) :
    let run := freezeTokenRunOn selCode quoteCode control tokens
    EF.streamReadFrom run.2 (some (freezeStreamStateOn quote sel state)) =
        (EF.streamReadFrom tokens (some state)).map (freezeStreamStateOn quote sel) ∧
      ∀ next, EF.streamReadFrom tokens (some state) = some next → run.1.Matches next := by
  induction tokens generalizing control state with
  | nil =>
      simp [freezeTokenRunOn, EF.streamReadFrom, hmatch]
  | cons token tokens ih =>
      simp only [freezeTokenRunOn]
      have hstep := streamReadFrom_freezeTokenEmitOn quote sel selCode quoteCode hsel hquote
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
              (EF.streamStep (some state) token)).map (freezeStreamStateOn quote sel)
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

lemma deserializeTrades_freezeTokenRunOn
    (quote : ℕ → Sentence → ℚ) (sel : ℕ → Sentence → Bool)
    (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      selCode day code = sel day φ)
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ)) (tokens : List ℕ) :
    let run := freezeTokenRunOn selCode quoteCode (0, 0) tokens
    deserializeTrades run.2 =
      (deserializeTrades tokens).map fun trades =>
        trades.map fun trade => (trade.1.freezeOn quote sel, trade.2) := by
  have hrun := (streamReadFrom_freezeTokenRunOn quote sel selCode quoteCode hsel hquote
    (0, 0) EF.streamInitial tokens freezeToken_initial_matches).1
  simp only at hrun ⊢
  have hinitial : freezeStreamStateOn quote sel EF.streamInitial = EF.streamInitial := rfl
  rw [hinitial] at hrun
  unfold deserializeTrades
  rw [hrun]
  cases hread : EF.streamReadFrom tokens (some EF.streamInitial) with
  | none => rfl
  | some state =>
      rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
      cases mode <;> cases pending <;> cases stack <;>
        simp [freezeStreamStateOn]

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

/-- **The selector-indexed token model of the freeze.**  Decoding the transducer's output
gives exactly the `EF.freezeOn`-rewritten trades of the decoded source — on *every* token
stream, well-formed or garbage.  `hsel` is the bridge from the code-level selector the
transducer can test to the sentence-level selector `EF.freezeOn` reads; `hquote` is the
same bridge for the quote table.

This is the finite-support freeze's token model.  It is not an efficiency certificate:
exhibiting `freezeTokenRunOn` as a `Complexity.FP` rewrite is the separate
`FreezeStreamRewriter` obligation, discharged by
`FreezeStep.freezeStreamRewriter_of_runOracle`.

Proof kind: `C` composition.  Provenance: (a) `deserializeTrades_freezeTokenRunOn`.
Paper node: `app:ifp` -/
lemma strategyOfTokens_freezeTokenRunOn_trades
    (quote : ℕ → Sentence → ℚ) (sel : ℕ → Sentence → Bool)
    (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (n : ℕ)
    (hsel : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      selCode day code = sel day φ)
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ)) (tokens : List ℕ) :
    let run := freezeTokenRunOn selCode quoteCode (0, 0) tokens
    (strategyOfTokens n run.2).trades =
      (strategyOfTokens n tokens).trades.map fun trade =>
        (trade.1.freezeOn quote sel, trade.2) := by
  have hdecode := deserializeTrades_freezeTokenRunOn quote sel selCode quoteCode hsel hquote tokens
  simp only at hdecode ⊢
  rw [strategyOfTokens_trades_eq, strategyOfTokens_trades_eq, hdecode]
  cases hs : deserializeTrades tokens with
  | none => simp
  | some trades =>
      simp only [Option.map_some]
      have hrank :
          (∀ trade ∈ trades.map (fun trade =>
              (trade.1.freezeOn quote sel, trade.2)), trade.1.rank ≤ n) ↔
            ∀ trade ∈ trades, trade.1.rank ≤ n := by
        constructor
        · intro h trade hmem
          have hmapped : (trade.1.freezeOn quote sel, trade.2) ∈
              trades.map (fun trade =>
                (trade.1.freezeOn quote sel, trade.2)) :=
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
            (trade.1.freezeOn quote sel, trade.2)), trade.1.rank ≤ n :=
          fun h => hvalid (hrank.mp h)
        unfold validatedTrades
        rw [if_neg hfrozenInvalid, if_neg hvalid]
        rfl

/-! ### The day-cutoff instance of the token model

Every declaration below is the `day < cutoff` instance of the selector-indexed transducer
above; none of them re-runs an induction.  The bridge hypothesis `hsel` is discharged by
`rfl`, because the day-cutoff selector ignores the sentence slot entirely. -/

/-- The day-cutoff emission, as the `day < cutoff` instance of `freezeTokenEmitOn`. -/
def freezeTokenEmit (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) :
    FreezeTokenState → ℕ → List ℕ :=
  freezeTokenEmitOn (fun d _ => decide (d < cutoff)) quoteCode

/-- The day-cutoff transducer, as the `day < cutoff` instance of `freezeTokenRunOn`. -/
def freezeTokenRun (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) :
    FreezeTokenState → List ℕ → FreezeTokenState × List ℕ :=
  freezeTokenRunOn (fun d _ => decide (d < cutoff)) quoteCode

lemma freezeTokenEmit_eq (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (state : FreezeTokenState) (token : ℕ) :
    freezeTokenEmit quoteCode cutoff state token =
      if state.1 = 2 ∧ token < cutoff then
        [token, 1, quoteCode token state.2, 8]
      else [token] := by
  simp only [freezeTokenEmit, freezeTokenEmitOn, decide_eq_true_eq]

@[simp] lemma freezeTokenRun_nil (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (state : FreezeTokenState) :
    freezeTokenRun quoteCode cutoff state [] = (state, []) := rfl

lemma freezeTokenRun_range (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (tokenFn : ℕ → ℕ) (n count : ℕ) :
    freezeTokenRun quoteCode cutoff (0, 0)
        ((List.range count).map fun j => tokenFn (Nat.pair n j)) =
      (freezeTokenControlAt tokenFn n count,
        (List.range count).flatMap fun j =>
          freezeTokenEmit quoteCode cutoff (freezeTokenControlAt tokenFn n j)
            (tokenFn (Nat.pair n j))) :=
  freezeTokenRunOn_range _ quoteCode tokenFn n count

/-- The day-cutoff selector ignores the sentence slot, so the code-level and
sentence-level selectors agree definitionally. -/
lemma cutoffSel_bridge (cutoff : ℕ) :
    ∀ day code (φ : Sentence), Encodable.decode (α := Sentence) code = some φ →
      (fun (d : ℕ) (_ : ℕ) => decide (d < cutoff)) day code
        = (fun (d : ℕ) (_ : Sentence) => decide (d < cutoff)) day φ :=
  fun _ _ _ _ => rfl

lemma streamReadFrom_freezeTokenRun
    (quote : ℕ → Sentence → ℚ) (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ))
    (control : FreezeTokenState) (state : EF.StreamState) (tokens : List ℕ)
    (hmatch : control.Matches state) :
    let run := freezeTokenRun quoteCode cutoff control tokens
    EF.streamReadFrom run.2
          (some (freezeStreamStateOn quote (fun d _ => decide (d < cutoff)) state)) =
        (EF.streamReadFrom tokens (some state)).map
          (freezeStreamStateOn quote (fun d _ => decide (d < cutoff))) ∧
      ∀ next, EF.streamReadFrom tokens (some state) = some next → run.1.Matches next :=
  streamReadFrom_freezeTokenRunOn quote _ _ quoteCode (cutoffSel_bridge cutoff) hquote
    control state tokens hmatch

lemma strategyOfTokens_freezeTokenRun_trades
    (quote : ℕ → Sentence → ℚ) (quoteCode : ℕ → ℕ → ℕ) (cutoff n : ℕ)
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ)) (tokens : List ℕ) :
    let run := freezeTokenRun quoteCode cutoff (0, 0) tokens
    (strategyOfTokens n run.2).trades =
      (strategyOfTokens n tokens).trades.map fun trade =>
        (trade.1.freezeBefore quote cutoff, trade.2) :=
  strategyOfTokens_freezeTokenRunOn_trades quote _ _ quoteCode n
    (cutoffSel_bridge cutoff) hquote tokens

end EF

end LogicalInduction
