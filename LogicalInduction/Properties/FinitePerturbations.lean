/-
# §4.6 Closure under finite perturbations (`thm:ifp`, appendix `app:ifp`)

The paper transports an exploiting trader across a finite change of market history by
replacing every old price leaf in its feature syntax with the corresponding rational
constant.  This file realizes that semantics with an administrative dead binding which
retains the original price leaf, and proves its rank, size, semantic, net-worth, and
exploitation laws.  Retaining the leaf is what makes the flat rewrite parser-transparent
even on malformed raw trader programs.

## PAPER ERRATUM — the appendix proof of `thm:ifp` has a gap

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
numeral is `~2^(2^n)`, which no polynomial clock can emit (`codeEvaln_result_le` and
`codeEvalBound_poly` give the relevant fixed-code polynomial output bound, not an
output-`≤`-fuel bound).  For such a `P'`,
`EfficientPrefixPatch P' 1` is **uninhabited** — the hypothesis is not merely unproved but
unsatisfiable.  (This counterexample is *not* formalized, and neither is the step it rests
on: that no polynomial clock can emit a numeral of magnitude `2^(2^n)`.)

Note the paper is aware `LIA` itself has finite support per day (`sec:construct`, remark
following the belief-sequence definition) and *deliberately* generalizes the property tail
to arbitrary markets.  Finite support is exactly what would rescue the hard-coding step, so
the gap is a genuine cost of that generalization, not an oversight about `LIA`.

## The correction

Finite support is exactly what rescues the hard-coding step, so this file also proves the
**corrected** theorem, at both classes: `lic_iff_of_finiteSupportPerturbation` and
`machine_lic_iff_of_finiteSupportPerturbation` quantify over perturbations that move only
finitely many `(day, sentence)` price *coordinates*, where the constant table really is
finite and the appendix's own justification is literally valid.  That hypothesis is
**strictly stronger** than the paper's `∀ n ≥ N, pt_n = pt'_n`
(`FiniteSupportPerturbation.tail_agree` proves one direction; the day-`0` huge-numeral
market below refutes the other), so the corrected theorem is a proper restriction of
`thm:ifp`, not a restatement of it.  The published unrestricted theorem remains
unresolved, and its published proof remains invalid.

The freeze itself is not duplicated, at any layer.  `EF.freezeOn` takes a per-coordinate
selector and is the only freeze recursion in the source; `EF.freezeBefore`,
`Strategy.freezeBefore` and `Trader.freezeBefore` are *defined* as its `day < cutoff`
instance, so each `freezeBefore_eq_freezeOn` is `rfl` and every day-cutoff law below is a
transport rather than a parallel induction.  (The previously scheduled demolition of the
second recursion is done; nothing here is layered scaffolding.)

The **flat-token** presentation is selector-indexed in the same way.
`EF.freezeTokenRunOn` runs the transducer against a *code-level* selector
`selCode : ℕ → ℕ → Bool` — day and pending sentence code, which is all the transducer
has — and `EF.strategyOfTokens_freezeTokenRunOn_trades` transports the decoded strategy
across it, given the bridge `hsel` from `selCode` to the sentence-level `sel` that
`EF.freezeOn` reads.  `EF.freezeTokenRun` and its laws are the `day < cutoff` instance,
where the bridge is discharged by `rfl` because the day-cutoff selector ignores the
sentence slot.  This is the token model the finite-support freeze needs; what it does
*not* yet supply is a `Complexity.FP` certificate for the transducer, which is the
remaining obligation on `MachineFiniteSupportPatch`.

One thing the corrected theorem does **not** buy: an inhabitant.  Both
`FiniteSupportPatch` and `MachineFiniteSupportPatch` are uninhabited in this repo, exactly
as `EfficientPrefixPatch` is.  Finite support makes the argument sound in principle;
discharging the certificate is a separate `Complexity.FP` transport result.

**What this file does about it.**  We keep the theorem to what is actually provable:
`EfficientPrefixPatch` states the missing closure fact for the concrete syntax
transformation, and `lic_iff_of_finitePerturbation` takes it as a hypothesis for each
market.  The structure contains no trading, exploitation, or logical-inductor conclusion.
Consequently `lic_iff_of_finitePerturbation` is **strictly weaker than the paper's
`thm:ifp`**: it does not cover every finite perturbation of a computable market, only those
whose frozen prefix admits an efficient presentation.  For `LIA` the obstruction above is
absent — the per-day quote table is a finite entry list (`RationalBeliefState`,
`MarketMaker.lean`), so the freeze is a finite lookup rather than an unbounded computation
— but the efficiency certificate for the emitted stream is not discharged, so no `LIA`
instance of `EfficientPrefixPatch` exists at present.  The restriction must be stated
whenever this theorem is cited as the paper's.
-/
import LogicalInduction.Framework.Affine
import LogicalInduction.Framework.Computable
import LogicalInduction.Framework.MachineEfficiency

namespace LogicalInduction

open scoped BigOperators

namespace EF

/-! ## The selector-indexed freeze

`EF.freezeOn` is **the** freeze in this file: `freezeBefore` below is literally its
`day < cutoff` instance, not a second recursion. -/

/-- Freeze exactly the price leaves whose coordinate is selected.

The administrative `letE` deliberately retains the dead original price leaf.  Its body is
the constant quote, so the denotation is independent of that leaf, while retaining it makes
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

/-- The retained dead leaf makes the administrative freeze rank-preserving. -/
@[simp] theorem freezeBefore_rank (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    (e.freezeBefore quote cutoff).rank = e.rank :=
  e.freezeOn_rank quote _

lemma freezeBefore_rank_le (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    (e.freezeBefore quote cutoff).rank ≤ e.rank :=
  e.freezeOn_rank_le quote _

/-- The administrative binding makes the literal rewrite at most three times larger. -/
lemma freezeBefore_cost_le (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    (e.freezeBefore quote cutoff).cost ≤ 3 * e.cost :=
  e.freezeOn_cost_le quote _


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

/-- Tokens emitted while consuming one source token.

`selCode` is the **code-level** selector: at a price-day slot it is applied to the day just
read and to the pending sentence *code* buffered by the parser control, because that is all
the transducer has.  `hselCode` below is the bridge to the sentence-level `sel` that
`EF.freezeOn` uses. -/
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

@[simp] theorem freezeTokenRunOn_nil (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
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

@[simp] theorem streamReadFrom_none (tokens : List ℕ) :
    EF.streamReadFrom tokens none = none := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      simp only [EF.streamReadFrom, List.foldl_cons, EF.streamStep]
      simpa [EF.streamReadFrom] using ih

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
exhibiting `freezeTokenRunOn` as a `Complexity.FP` function is the separate obligation
that `MachineFiniteSupportPatch` still waits on.

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

@[simp] theorem freezeTokenRun_nil (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (state : FreezeTokenState) :
    freezeTokenRun quoteCode cutoff state [] = (state, []) := rfl

lemma freezeTokenRun_append (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (state : FreezeTokenState) (xs ys : List ℕ) :
    freezeTokenRun quoteCode cutoff state (xs ++ ys) =
      let first := freezeTokenRun quoteCode cutoff state xs
      let second := freezeTokenRun quoteCode cutoff first.1 ys
      (second.1, first.2 ++ second.2) :=
  freezeTokenRunOn_append _ quoteCode state xs ys

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

/-- On a canonical feature serialization the day-cutoff rewrite is exactly
`EF.freezeBefore`. -/
lemma freezeTokenRun_serialize (quote : ℕ → Sentence → ℚ)
    (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (hquote : ∀ day φ, quoteCode day (Encodable.encode φ) =
      Encodable.encode (quote day φ)) (e : EF) :
    freezeTokenRun quoteCode cutoff (0, 0) e.serialize =
      ((0, 0), (e.freezeBefore quote cutoff).serialize) :=
  freezeTokenRunOn_serialize quote _ _ quoteCode (fun _ _ => rfl) hquote e

lemma freezeTokenRun_serializeTrades (quote : ℕ → Sentence → ℚ)
    (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (hquote : ∀ day φ, quoteCode day (Encodable.encode φ) =
      Encodable.encode (quote day φ)) (trades : List (EF × Sentence)) :
    freezeTokenRun quoteCode cutoff (0, 0) (serializeTrades trades) =
      ((0, 0), serializeTrades
        (trades.map fun trade => (trade.1.freezeBefore quote cutoff, trade.2))) :=
  freezeTokenRunOn_serializeTrades quote _ _ quoteCode (fun _ _ => rfl) hquote trades


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

end EF

namespace Strategy

/-- Apply the selector freeze to every coefficient of a strategy. -/
def freezeOn {day : ℕ} (quote : ℕ → Sentence → ℚ) (sel : ℕ → Sentence → Bool)
    (T : Strategy day) : Strategy day where
  trades := T.trades.map fun p => (p.1.freezeOn quote sel, p.2)
  rank_le := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (q.1.freezeOn_rank_le quote sel).trans (T.rank_le q hq)

/-- Apply the old-price freeze to every coefficient of a strategy: the `day < cutoff`
instance of `Strategy.freezeOn`. -/
def freezeBefore {day : ℕ} (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (T : Strategy day) : Strategy day :=
  T.freezeOn quote (fun d _ => decide (d < cutoff))

lemma freezeBefore_eq_freezeOn {day : ℕ} (T : Strategy day)
    (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    T.freezeBefore quote cutoff = T.freezeOn quote (fun d _ => decide (d < cutoff)) := rfl

/-- On an unchanged tail day, a frozen strategy against `P'` has exactly the value of the
original strategy against `P`. -/
lemma freezeBefore_value
    {day : ℕ} (T : Strategy day) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (P P' : History) (w : Valuation)
    (hprefix : ∀ d < cutoff, ∀ φ, P d φ = (quote d φ : ℝ))
    (htail : ∀ d, cutoff ≤ d → ∀ φ, P d φ = P' d φ)
    (hday : cutoff ≤ day) :
    (T.freezeBefore quote cutoff).value P' w = T.value P w := by
  simp only [Strategy.value, freezeBefore, freezeOn, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply]
  rw [show (EF.freezeOn quote (fun d _ => decide (d < cutoff)) p.1).denote P'
        = p.1.denote P from p.1.freezeBefore_denote quote cutoff P P' hprefix htail]
  rw [← htail day hday p.2]

end Strategy

namespace Trader

def freezeOn (quote : ℕ → Sentence → ℚ) (sel : ℕ → Sentence → Bool) (Tr : Trader) :
    Trader where
  strat day := (Tr.strat day).freezeOn quote sel

/-- The paper's false-report trader: coefficients see the frozen old prefix.  The
`day < cutoff` instance of `Trader.freezeOn`. -/
def freezeBefore (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (Tr : Trader) : Trader :=
  Tr.freezeOn quote (fun d _ => decide (d < cutoff))

lemma freezeBefore_eq_freezeOn (Tr : Trader) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    Tr.freezeBefore quote cutoff = Tr.freezeOn quote (fun d _ => decide (d < cutoff)) :=
  rfl

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

**This is a paper erratum, not a modeling substitution** (see the file header).  `app:ifp`
asserts this closure is immediate because "only finitely many constants are needed"; that
is false — finitely many *days*, but unboundedly many sentences.  This structure is **not
inhabited for every `ComputableMarket P`**: a market with huge-encoding day-`0` quotes
admits no such patch at all.  Do not read it as a routine obligation awaiting labor;
instantiating it is a real claim about `P`.

For `LIA` that obstruction is absent — each day's quote table is a finite
`RationalBeliefState` entry list, so the freeze is a finite lookup with constant-size
tokens — but the fuel certificate for the emitted stream is not discharged, so no `LIA`
instance of this structure exists at present.
Paper node: `app:ifp` -/
structure EfficientPrefixPatch (P : History) (cutoff : ℕ) where
  quote : ℕ → Sentence → ℚ
  quote_exact : ∀ day < cutoff, ∀ φ, P day φ = (quote day φ : ℝ)
  preserves_ec : ∀ Tr : Trader, EfficientlyComputable Tr →
    EfficientlyComputable (Tr.freezeBefore quote cutoff)

/-- **Closure under Finite Perturbations** (`thm:ifp`), with the computational
qualification forced by the clocked efficiency model (`dd:fuel`).  The two histories agree
from `cutoff` onward, and each supplies the efficient-freeze certificate above.  The
conclusion is the paper's biconditional, not merely one direction.
Paper node: `thm:ifp` -/
theorem lic_iff_of_finitePerturbation
    (P P' : History) (DP : DeductiveProcess) (cutoff : ℕ)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (htail : ∀ day, cutoff ≤ day → ∀ φ, P day φ = P' day φ)
    (patchP : EfficientPrefixPatch P cutoff)
    (patchP' : EfficientPrefixPatch P' cutoff) :
    IsLogicalInductor P DP ↔ IsLogicalInductor P' DP := by
  have hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1 := hPcomp.price_mem_Icc
  have hP' : ∀ day φ, 0 ≤ P' day φ ∧ P' day φ ≤ 1 := hP'comp.price_mem_Icc
  constructor
  · intro hLI
    exact {
      marketComputable := hP'comp
      processComputable := hLI.processComputable
      noExploit := by
        intro Tr hTr hExploits
        let frozen := Tr.freezeBefore patchP'.quote cutoff
        have hfrozenEC : EfficientlyComputable frozen :=
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
        have hfrozenEC : EfficientlyComputable frozen :=
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

/-! ## The public predicate -/

/-- `P` and `P'` differ on only finitely many `(day, sentence)` price coordinates. -/
def FiniteSupportPerturbation (P P' : History) : Prop :=
  ∃ S : Finset (ℕ × Sentence), ∀ d φ, (d, φ) ∉ S → P d φ = P' d φ

/-- Finite support is *strictly stronger* than the paper's tail-agreement hypothesis. -/
lemma FiniteSupportPerturbation.tail_agree {P P' : History}
    (h : FiniteSupportPerturbation P P') :
    ∃ N : ℕ, ∀ d, N ≤ d → ∀ φ, P d φ = P' d φ := by
  obtain ⟨S, hS⟩ := h
  refine ⟨(S.image Prod.fst).sup id + 1, ?_⟩
  intro d hd φ
  refine hS d φ (fun hmem => ?_)
  have : d ≤ (S.image Prod.fst).sup id :=
    Finset.le_sup (f := id) (Finset.mem_image.2 ⟨(d, φ), hmem, rfl⟩)
  omega

namespace Strategy

/-- **The settlement term is the obstruction to exact transport at strategy level.**
`Strategy.value` contains `- V day p.2`, which is *not* a syntactic leaf and so cannot be
frozen.  Exact equality therefore needs the whole day-`day` fiber to be unselected. -/
lemma freezeOn_value {day : ℕ} (T : Strategy day) (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) (P P' : History) (w : Valuation)
    (hin : ∀ d φ, sel d φ = true → P d φ = (quote d φ : ℝ))
    (hout : ∀ d φ, sel d φ = false → P d φ = P' d φ)
    (hday : ∀ φ, sel day φ = false) :
    (T.freezeOn quote sel).value P' w = T.value P w := by
  simp only [Strategy.value, freezeOn, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply]
  rw [p.1.freezeOn_denote quote sel P P' hin hout]
  rw [← hout day p.2 (hday p.2)]

end Strategy

namespace Trader

/-- The finite set of days on which the perturbation is felt. -/
def freezeDays (S : Finset (ℕ × Sentence)) : Finset ℕ := S.image Prod.fst

noncomputable def freezeOnErrorBound (Tr : Trader) (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) (D : Finset ℕ) (P P' : History) : ℝ :=
  ∑ day ∈ D, ((Tr.strat day).magnitude P +
    ((Tr.freezeOn quote sel).strat day).magnitude P')

/-- Net worths differ by at most an explicit bound supported on the finitely many
*affected days*.  Every unaffected day cancels exactly. -/
lemma freezeOn_netWorth_difference_le (Tr : Trader) (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) (D : Finset ℕ) (P P' : History)
    (hin : ∀ d φ, sel d φ = true → P d φ = (quote d φ : ℝ))
    (hout : ∀ d φ, sel d φ = false → P d φ = P' d φ)
    (hD : ∀ d, d ∉ D → ∀ φ, sel d φ = false)
    (hP : ∀ d φ, 0 ≤ P d φ ∧ P d φ ≤ 1)
    (hP' : ∀ d φ, 0 ≤ P' d φ ∧ P' d φ ≤ 1)
    (v : PCWorld) (n : ℕ) :
    |Tr.netWorth P v n - (Tr.freezeOn quote sel).netWorth P' v n| ≤
      Tr.freezeOnErrorBound quote sel D P P' := by
  classical
  let g : ℕ → ℝ := fun day ↦
    (Tr.strat day).magnitude P + ((Tr.freezeOn quote sel).strat day).magnitude P'
  have hw : ∀ φ, v.payout φ = 0 ∨ v.payout φ = 1 := by
    intro φ
    by_cases hφ : v.Holds φ
    · exact Or.inr (by simp [PCWorld.payout, hφ])
    · exact Or.inl (by simp [PCWorld.payout, hφ])
  have hterm : ∀ day,
      |(Tr.strat day).value P v.payout -
          ((Tr.freezeOn quote sel).strat day).value P' v.payout| ≤
        if day ∈ D then g day else 0 := by
    intro day
    by_cases hday : day ∈ D
    · rw [if_pos hday]
      exact (abs_sub _ _).trans (add_le_add
        (Strategy.abs_value_le_magnitude (Tr.strat day) P v.payout hw (hP day))
        (Strategy.abs_value_le_magnitude
          ((Tr.freezeOn quote sel).strat day) P' v.payout hw (hP' day)))
    · rw [if_neg hday]
      have heq := (Tr.strat day).freezeOn_value quote sel P P' v.payout hin hout
        (hD day hday)
      change |(Tr.strat day).value P v.payout -
        ((Tr.strat day).freezeOn quote sel).value P' v.payout| ≤ 0
      rw [heq]
      simp
  have hg : ∀ day, 0 ≤ g day := fun day ↦
    add_nonneg (Strategy.magnitude_nonneg _ _) (Strategy.magnitude_nonneg _ _)
  calc
    |Tr.netWorth P v n - (Tr.freezeOn quote sel).netWorth P' v n| =
        |∑ day ∈ Finset.range (n + 1),
          ((Tr.strat day).value P v.payout -
            ((Tr.freezeOn quote sel).strat day).value P' v.payout)| := by
          simp only [Trader.netWorth]
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ day ∈ Finset.range (n + 1),
          |(Tr.strat day).value P v.payout -
            ((Tr.freezeOn quote sel).strat day).value P' v.payout| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ day ∈ Finset.range (n + 1), if day ∈ D then g day else 0 :=
          Finset.sum_le_sum (fun day _ ↦ hterm day)
    _ = ∑ day ∈ (Finset.range (n + 1)).filter (fun day ↦ day ∈ D), g day := by
          rw [Finset.sum_filter]
    _ ≤ ∑ day ∈ D, g day := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro day hday
            simp only [Finset.mem_filter] at hday
            exact hday.2
          · intro day _ _
            exact hg day
    _ = Tr.freezeOnErrorBound quote sel D P P' := rfl

end Trader

/-! ## The corrected theorem -/

/-- The efficiency certificate for the **finite-support** freeze.  Unlike
`EfficientPrefixPatch`, the quote table here is genuinely finite: `quote` is only read at
the finitely many coordinates in `S`, so the paper's "hard-code the constants" step is
literally valid.  It is nevertheless **uninhabited in this repo**: soundness of the
argument is not the same as having built the compiler.
Paper node: `app:ifp` -/
structure FiniteSupportPatch (P : History) (S : Finset (ℕ × Sentence)) where
  quote : ℕ → Sentence → ℚ
  quote_exact : ∀ d φ, (d, φ) ∈ S → P d φ = (quote d φ : ℝ)
  preserves_ec : ∀ Tr : Trader, EfficientlyComputable Tr →
    EfficientlyComputable (Tr.freezeOn quote (fun d φ => decide ((d, φ) ∈ S)))

/-- **Closure under finite-support perturbations** — the *corrected* `thm:ifp`, at the
fuel class.

**This is not the paper's `thm:ifp`.**  Its hypothesis is **strictly stronger**: finite
support of the price difference implies the paper's tail agreement
(`FiniteSupportPerturbation.tail_agree`) and is not implied by it — the day-`0`
huge-numeral market in this file's header agrees with `LIA` from day `1` and is not
finitely supported.  What this repairs is the appendix's efficiency step, which is valid
exactly when the constant table is finite: `quote` is read only at the finitely many
coordinates in `S`, so "hard-code the constants" is literally true here and false in
general.  `lic_iff_of_finitePerturbation` below keeps the paper's own hypothesis shape and
its unresolved qualification; neither theorem reaches the unrestricted node.

Kind `C`; hypotheses `(a)` except `preserves_ec`, which is the appendix's own obligation.
Paper node: `thm:ifp` -/
theorem lic_iff_of_finiteSupportPerturbation
    (P P' : History) (DP : DeductiveProcess) (S : Finset (ℕ × Sentence))
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hagree : ∀ d φ, (d, φ) ∉ S → P d φ = P' d φ)
    (patchP : FiniteSupportPatch P S) (patchP' : FiniteSupportPatch P' S) :
    IsLogicalInductor P DP ↔ IsLogicalInductor P' DP := by
  classical
  have hP : ∀ d φ, 0 ≤ P d φ ∧ P d φ ≤ 1 := hPcomp.price_mem_Icc
  have hP' : ∀ d φ, 0 ≤ P' d φ ∧ P' d φ ≤ 1 := hP'comp.price_mem_Icc
  set sel : ℕ → Sentence → Bool := fun d φ => decide ((d, φ) ∈ S) with hsel
  have hselF : ∀ d φ, sel d φ = false ↔ (d, φ) ∉ S := by
    intro d φ; simp [hsel]
  have hselT : ∀ d φ, sel d φ = true ↔ (d, φ) ∈ S := by
    intro d φ; simp [hsel]
  set D : Finset ℕ := Trader.freezeDays S with hD
  have hDays : ∀ d, d ∉ D → ∀ φ, sel d φ = false := by
    intro d hd φ
    rw [hselF]
    intro hmem
    refine hd ?_
    rw [hD, Trader.freezeDays, Finset.mem_image]
    exact ⟨(d, φ), hmem, rfl⟩
  constructor
  · intro hLI
    exact {
      marketComputable := hP'comp
      processComputable := hLI.processComputable
      noExploit := by
        intro Tr hTr hExploits
        have hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
            |Tr.netWorth P' v n - (Tr.freezeOn patchP'.quote sel).netWorth P v n| ≤
              Tr.freezeOnErrorBound patchP'.quote sel D P' P := by
          intro n v _
          exact Tr.freezeOn_netWorth_difference_le patchP'.quote sel D P' P
            (fun d φ h => patchP'.quote_exact d φ ((hselT d φ).1 h))
            (fun d φ h => (hagree d φ ((hselF d φ).1 h)).symm)
            hDays hP' hP v n
        exact hLI.noExploit _ (patchP'.preserves_ec Tr hTr)
          (hExploits.of_boundedDifference _ hdiff) }
  · intro hLI'
    exact {
      marketComputable := hPcomp
      processComputable := hLI'.processComputable
      noExploit := by
        intro Tr hTr hExploits
        have hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
            |Tr.netWorth P v n - (Tr.freezeOn patchP.quote sel).netWorth P' v n| ≤
              Tr.freezeOnErrorBound patchP.quote sel D P P' := by
          intro n v _
          exact Tr.freezeOn_netWorth_difference_le patchP.quote sel D P P'
            (fun d φ h => patchP.quote_exact d φ ((hselT d φ).1 h))
            (fun d φ h => hagree d φ ((hselF d φ).1 h))
            hDays hP hP' v n
        exact hLI'.noExploit _ (patchP.preserves_ec Tr hTr)
          (hExploits.of_boundedDifference _ hdiff) }

/-! ## Refutation of the exact-net-worth claim -/

/-- The settlement term `- V day φ` in `Strategy.value` is not syntax, so the frozen
strategy's value on an *affected* day differs from the original's by exactly
`coefficient * (P' day φ - P day φ)`.  Concretely, with a single unit trade the
discrepancy is the price gap itself. -/
lemma freezeOn_value_gap_on_selected_day
    (day : ℕ) (φ : Sentence) (P P' : History) (w : Valuation)
    (quote : ℕ → Sentence → ℚ) (sel : ℕ → Sentence → Bool)
    (T : Strategy day) (hT : T.trades = [(EF.const 1, φ)]) :
    (T.freezeOn quote sel).value P' w - T.value P w = P day φ - P' day φ := by
  simp [Strategy.value, Strategy.freezeOn, hT, EF.freezeOn, EF.denote, EF.denoteWith]

/-! ## The same theorem at the machine class (the recommended home) -/

/-- The machine-class efficiency certificate for the finite-support freeze.  This is the
version whose obligation is dischargeable: `Nat.unpair` is polynomial time, so the
escape-leaf decode that blocks the fuel model is available here.

Like `EfficientPrefixPatch`, this structure has **no inhabitant anywhere in the repo**.
Finite support makes the appendix's argument sound *in principle* — the constant table is
genuinely finite — but discharging the certificate is a separate `Complexity.FP` transport
result that is not proved here.  Do not read the corrected theorem as non-vacuous.

`machineFiniteSupportPatch_of_rewriter` below reduces the whole certificate to one named
`Complexity.FP` fact, `FreezeStreamRewriter`.  That is a *narrowing of the obligation, not
a discharge of it*: `FreezeStreamRewriter` has no instance either, so the reduction
produces no inhabitant and this structure remains uninhabited.
Paper node: `app:ifp` -/
structure MachineFiniteSupportPatch (P : History) (S : Finset (ℕ × Sentence)) where
  quote : ℕ → Sentence → ℚ
  quote_exact : ∀ d φ, (d, φ) ∈ S → P d φ = (quote d φ : ℝ)
  preserves_ec : ∀ Tr : Trader, MachineEfficientTrader Tr →
    MachineEfficientTrader (Tr.freezeOn quote (fun d φ => decide ((d, φ) ∈ S)))

/-! ### The remaining obligation, named

Everything between the token model and `MachineFiniteSupportPatch` is discharged below.
What is left is a *single* `Complexity.FP` statement — exhibit the freeze transducer as a
polynomial-time rewrite of the machine's own output word — and `FreezeStreamRewriter` is
that statement.  It is deliberately phrased over the **contracted** stream `unRpn` reads,
because that is the granularity `strategyOfTokens` parses; discharging it means running
`EF.freezeTokenRunOn` through `TokenFold.runFold_mem_FP` and commuting the result with
`unRpn` (`RpnFreeze.unRpn_rpnFreezeRun` is the day-cutoff precedent).

No instance of `FreezeStreamRewriter` exists in this repo.  It is not a weaker hypothesis
smuggled in: it says exactly "the transducer is polynomial time", with no reference to the
market, the trader, or exploitation. -/

/-- **The one `Complexity.FP` fact the machine-class patch still needs.**  Every
polynomial-time output word can be rewritten, in polynomial time, into one whose contracted
token stream is the freeze transducer's output on the original's. -/
def FreezeStreamRewriter (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) : Prop :=
  ∀ F : List Bool → List Bool, F ∈ Complexity.FP →
    ∃ G : List Bool → List Bool, G ∈ Complexity.FP ∧ ∀ x : List Bool,
      unRpn (undigitize (bitsToDigits (G x)))
        = (EF.freezeTokenRunOn selCode quoteCode (0, 0)
            (unRpn (undigitize (bitsToDigits (F x))))).2

/-- **The freeze preserves machine efficiency, given the stream rewriter.**  This is the
whole of `preserves_ec` except the `FP` fact: the token model transports the decoded
strategy (`EF.strategyOfTokens_freezeTokenRunOn_trades`), `Strategy.ext` upgrades the trade
list to the strategy, and `Trader.freezeOn` is that strategy-wise.

Kind `C`; hypotheses `(a)` except `hrewrite`, which is the named obligation above.
Paper node: `app:ifp` -/
lemma MachineEfficientTrader.freezeOn
    {quote : ℕ → Sentence → ℚ} {sel : ℕ → Sentence → Bool}
    {selCode : ℕ → ℕ → Bool} {quoteCode : ℕ → ℕ → ℕ}
    (hsel : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      selCode day code = sel day φ)
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ))
    (hrewrite : FreezeStreamRewriter selCode quoteCode)
    {Tr : Trader} (hTr : MachineEfficientTrader Tr) :
    MachineEfficientTrader (Tr.freezeOn quote sel) := by
  obtain ⟨F, hF, hFspec⟩ := hTr
  obtain ⟨G, hG, hGspec⟩ := hrewrite F hF
  refine ⟨G, hG, fun n => ?_⟩
  apply Strategy.ext
  have htok := EF.strategyOfTokens_freezeTokenRunOn_trades quote sel selCode quoteCode n
    hsel hquote (unRpn (undigitize (bitsToDigits (F (unaryDay n)))))
  simp only at htok
  have hFtok : strategyOfTokens n (unRpn (undigitize (bitsToDigits (F (unaryDay n)))))
      = Tr.strat n := hFspec n
  show (strategyOfTokens n (unRpn (undigitize (bitsToDigits (G (unaryDay n)))))).trades = _
  rw [hGspec (unaryDay n), htok, hFtok]
  rfl

/-- **The machine-class patch, reduced to the stream rewriter.**  Given the finite quote
table, its code-level presentation, and the one `FP` fact, the patch exists.  Nothing here
assumes anything about the market beyond `quote_exact`.

Kind `C`; hypotheses `(a)` except `hrewrite`.
Paper node: `app:ifp` -/
def machineFiniteSupportPatch_of_rewriter
    (P : History) (S : Finset (ℕ × Sentence)) (quote : ℕ → Sentence → ℚ)
    (hexact : ∀ d φ, (d, φ) ∈ S → P d φ = (quote d φ : ℝ))
    (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      selCode day code = decide ((day, φ) ∈ S))
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ))
    (hrewrite : FreezeStreamRewriter selCode quoteCode) :
    MachineFiniteSupportPatch P S where
  quote := quote
  quote_exact := hexact
  preserves_ec := fun _ hTr =>
    MachineEfficientTrader.freezeOn hsel hquote hrewrite hTr

/-- **Closure under finite-support perturbations, at the paper's own quantifier.**  The
same corrected statement as `lic_iff_of_finiteSupportPerturbation`, over
`MachineEfficientTrader` rather than the fuel-certified class, and it is the primary one:
the whole economic argument is class-agnostic, so only the freeze certificate changes.
Read that theorem's docstring for what "corrected" means here — the hypothesis is strictly
stronger than the paper's, and this is not the unrestricted `thm:ifp`.

Kind `C`; hypotheses `(a)` except `preserves_ec`.
Paper node: `thm:ifp` -/
theorem machine_lic_iff_of_finiteSupportPerturbation
    (P P' : History) (DP : DeductiveProcess) (S : Finset (ℕ × Sentence))
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hagree : ∀ d φ, (d, φ) ∉ S → P d φ = P' d φ)
    (patchP : MachineFiniteSupportPatch P S) (patchP' : MachineFiniteSupportPatch P' S) :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP := by
  classical
  have hP : ∀ d φ, 0 ≤ P d φ ∧ P d φ ≤ 1 := hPcomp.price_mem_Icc
  have hP' : ∀ d φ, 0 ≤ P' d φ ∧ P' d φ ≤ 1 := hP'comp.price_mem_Icc
  set sel : ℕ → Sentence → Bool := fun d φ => decide ((d, φ) ∈ S) with hsel
  have hselF : ∀ d φ, sel d φ = false ↔ (d, φ) ∉ S := by intro d φ; simp [hsel]
  have hselT : ∀ d φ, sel d φ = true ↔ (d, φ) ∈ S := by intro d φ; simp [hsel]
  set D : Finset ℕ := Trader.freezeDays S with hD
  have hDays : ∀ d, d ∉ D → ∀ φ, sel d φ = false := by
    intro d hd φ
    rw [hselF]
    intro hmem
    refine hd ?_
    rw [hD, Trader.freezeDays, Finset.mem_image]
    exact ⟨(d, φ), hmem, rfl⟩
  constructor
  · intro hLI
    exact {
      marketComputable := hP'comp
      processComputable := hLI.processComputable
      noExploit := by
        intro Tr hTr hExploits
        have hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
            |Tr.netWorth P' v n - (Tr.freezeOn patchP'.quote sel).netWorth P v n| ≤
              Tr.freezeOnErrorBound patchP'.quote sel D P' P := by
          intro n v _
          exact Tr.freezeOn_netWorth_difference_le patchP'.quote sel D P' P
            (fun d φ h => patchP'.quote_exact d φ ((hselT d φ).1 h))
            (fun d φ h => (hagree d φ ((hselF d φ).1 h)).symm)
            hDays hP' hP v n
        exact hLI.noExploit _ (patchP'.preserves_ec Tr hTr)
          (hExploits.of_boundedDifference _ hdiff) }
  · intro hLI'
    exact {
      marketComputable := hPcomp
      processComputable := hLI'.processComputable
      noExploit := by
        intro Tr hTr hExploits
        have hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
            |Tr.netWorth P v n - (Tr.freezeOn patchP.quote sel).netWorth P' v n| ≤
              Tr.freezeOnErrorBound patchP.quote sel D P P' := by
          intro n v _
          exact Tr.freezeOn_netWorth_difference_le patchP.quote sel D P P'
            (fun d φ h => patchP.quote_exact d φ ((hselT d φ).1 h))
            (fun d φ h => hagree d φ ((hselF d φ).1 h))
            hDays hP hP' v n
        exact hLI'.noExploit _ (patchP.preserves_ec Tr hTr)
          (hExploits.of_boundedDifference _ hdiff) }

end LogicalInduction

#print axioms LogicalInduction.EF.strategyOfTokens_freezeTokenRunOn_trades
#print axioms LogicalInduction.MachineEfficientTrader.freezeOn
#print axioms LogicalInduction.EF.freezeTokenRunOn_serialize
#print axioms LogicalInduction.EF.freezeBefore_denote
#print axioms LogicalInduction.Strategy.freezeBefore_value
#print axioms LogicalInduction.Trader.freezeBefore_netWorth_difference_le
#print axioms LogicalInduction.Trader.Exploits.of_boundedDifference
#print axioms LogicalInduction.lic_iff_of_finitePerturbation
#print axioms LogicalInduction.FiniteSupportPerturbation.tail_agree
#print axioms LogicalInduction.EF.freezeBefore_eq_freezeOn
#print axioms LogicalInduction.Trader.freezeOn_netWorth_difference_le
#print axioms LogicalInduction.lic_iff_of_finiteSupportPerturbation
#print axioms LogicalInduction.machine_lic_iff_of_finiteSupportPerturbation
