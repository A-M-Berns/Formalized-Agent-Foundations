import LogicalInduction.Framework.Affine
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.Computable
import Mathlib.Algebra.BigOperators.Fin
import LogicalInduction.Framework.WriteOut

/-!
# Repeatable return on investment

This module renders the paper's Return on Investment appendix `app:roi`: the lemma
`lem:type3` (No Repeatable ε-ROI) and the trader-construction machinery its proof needs.
That lemma is one of the paper results carried without a `Paper node` line — `lem:type3`
is listed in `UNANNOTATED_PAPER_RESULTS` in `scripts/check_endpoint_coverage.py` — so this
header is where the coverage gate expects its citation.

## Emulatable families

`EfficientlyEmulatable` renders `def:emulatabletraders` (`app:emulatable`) clause for
clause: uniformly polynomial emission of member `k` on day `n`, and the zero trade before
day `k`. The development builds against the structured refinement `PolyTradeEmulatable`,
which additionally exposes trade counts, coefficient segments and sentence codes, so that
a uniform syntax transformation can scale every trade. `LaunchGated` isolates the single
economic clause the net-worth and budget chain consumes, and is metering-agnostic, so
token-metered families inhabit it too.

## The adaptive budget

`weight active α n` is the paper's `βₙ = 1 - ∑_{i<n} open(i,n) βᵢ αᵢ` (tex:3659), by
well-founded recursion; `outstanding` is the capital those earlier components tie up.
`fractionalWeight` is the continuous-occupancy analogue, reading a real occupancy in
`[0,1]` instead of a Boolean open bit. The unit-capital invariants are `weight_nonneg`,
`weight_le_one` and `activeAllocation_le_one`, with fractional counterparts.

Because features are reified syntax (`dd:dsl`), the coefficient must be *emitted*, not
merely computed. Reifying either recurrence directly would inline every earlier `β` as
syntax and make the index-`n` expression exponential in `n`. `letChain` and `sharedOf`
instead bind each earlier value once with `EF.letE` and refer back to it by a
constant-size `EF.var`, keeping the index-`n` expression polynomial; they are proved once
(serialization, uniform emission, rank, denotation, closedness) at an arbitrary body
family. `sharedFeatureWeight` and `fractionalSharedFeatureWeight` are the two instances,
and their `_denote`, `_rank_le` and `_polySeg` specifications follow from the generic
ones — the last of them uniform emission as a `BigSpliceStream` (`dd:fuel`).

`scaledFamilyTrader` likewise bundles a trader family at an arbitrary coefficient family,
and `sharedBudgetedTrader` and `fractionalBudgetedTrader` are its two instances; the
`_value`, `_magnitude`, `_netWorth` (the rectangular component view `LaunchGated` buys)
and `_ec` specifications are proved once and transported.
`allocationPrefix_not_bddAbove_of_frequently` and its fractional twin supply the recycling
half: if every position eventually closes and launch sizes are frequently bounded away
from zero, cumulative allocation is unbounded.

## Bounded verification

The paper does not ask for the first maturity day to be computable, only for each finite
maturity claim to be checkable (tex:3648). `VerifiedMaturitySchedule` carries a uniformly
polynomial, sound, eventually successful checker; `HistoricalVerifiedMaturitySchedule` is
the form concrete market and process code can supply — a fixed budget certifies some
`m ≤ n` — and `toVerified` promotes it, charging one extra tolerance for the post-`m`
trading tail. `polyFueled_boundedNone` turns the bounded prefix scan into the openness
table the shared trader consumes. The exact rational finite-prefix evaluators
(`Strategy.magnitudeRat`, `Strategy.valueRat` and the `…AtFuel` sound/complete pairs) are
what let such a checker *decide* the maturity conditions against a `MarketComputation`.

## Main results

`noRepeatableROI` states `lem:type3`; `noRepeatableROI_of_verifiedMaturity` is the client
form, discharging the closing days, the semantic maturity schedule and the polynomial
openness table from a single checker. `noFractionalRepeatableReturn` is the
continuous-occupancy analogue. Limits are stated with `ConvergesTo` (`dd:asymp`).

Four hypotheses go beyond the printed `lem:type3`, and are named at `noRepeatableROI`
itself: the WLOG normalisation `αₖ ≤ 1`, the summable tolerance family, the explicit
plausible-world clause, and the polynomial maturity verifier.

Consumers: `Properties/AffinePreemptiveLearning.lean`, `Properties/Calibration.lean`,
`Properties/Pseudorandomness.lean`, `Properties/UniversalSemimeasure.lean`,
`Construction/Budgeter.lean`, `Construction/LIACompiler.lean`,
`Construction/Witnesses/HistoricalMaturity.lean` (the heaviest client of the maturity
interfaces) and `Construction/Witnesses/FeedbackEmission.lean`; `API.lean` presents the
emulatability and budget vocabulary on the consumer surface.
-/

namespace LogicalInduction

open scoped BigOperators

/-! ## Emulatable trader families -/

/-- The paper's efficiently emulatable sequence of traders (`def:emulatabletraders`,
`app:emulatable`) in operational form. A single uniform token program emits member `k` on
day `n` within a polynomial bound independent of `k` (for `k ≤ n`), and member `k` is
identically zero before day `k`. The paper phrases this as an efficiently generated
sequence of uniformly bounded programs; pairing `k` into the input is the equivalent
universal-program presentation our token emitter uses.

This is the reference rendering of the paper's definition. The development builds against
the structured refinement `PolyTradeEmulatable`, and reaches the one clause it needs from
here through `EfficientlyEmulatable.launchGated`. -/
def EfficientlyEmulatable (Ts : ℕ → Trader) : Prop :=
  ∃ (code : Nat.Partrec.Code) (a d : ℕ),
    (∀ k n, n < k → ((Ts k).strat n).trades = []) ∧
    (∀ k n, k ≤ n →
      (serializeTrades ((Ts k).strat n).trades).length ≤ a * (n + 1) ^ d + a) ∧
    ∀ k n i, k ≤ n → i < (serializeTrades ((Ts k).strat n).trades).length →
      Nat.Partrec.Code.evaln (a * (n + 1) ^ d + a) code
          (Nat.pair k (Nat.pair n i)) =
        some ((serializeTrades ((Ts k).strat n).trades).getD i 0)

/-- The economic half of family emulation: members trade nothing before launch.
This is the only clause the netWorth/budget chain consumes, and — unlike the
universal-program token emission — it is metering-agnostic, so token-metered
(spliced) families inhabit it too. -/
def LaunchGated (Ts : ℕ → Trader) : Prop :=
  ∀ k n, n < k → ((Ts k).strat n).trades = []

/-- The bridge from the paper's definition to the clause the budget chain consumes. -/
lemma EfficientlyEmulatable.launchGated {Ts : ℕ → Trader}
    (h : EfficientlyEmulatable Ts) : LaunchGated Ts := by
  obtain ⟨_, _, _, hz, _, _⟩ := h
  exact hz

lemma LaunchGated.zero_before {Ts : ℕ → Trader}
    (h : LaunchGated Ts) {k n : ℕ} (hnk : n < k) :
    ((Ts k).strat n).trades = [] := h k n hnk

lemma Trader.netWorth_succ (Tr : Trader) (V : History) (v : PCWorld) (n : ℕ) :
    Tr.netWorth V v (n + 1) =
      Tr.netWorth V v n + (Tr.strat (n + 1)).value V v.payout := by
  simp [Trader.netWorth, Finset.sum_range_succ]

/-- A family member contributes no pre-launch value, so its net worth on launch day is
exactly that day's strategy value. -/
lemma LaunchGated.netWorth_launch {Ts : ℕ → Trader}
    (h : LaunchGated Ts) (V : History) (v : PCWorld) (k : ℕ) :
    (Ts k).netWorth V v k = ((Ts k).strat k).value V v.payout := by
  rw [Trader.netWorth]
  apply Finset.sum_eq_single k
  · intro i hi hik
    have hil : i < k := by
      simp only [Finset.mem_range] at hi
      omega
    rw [Strategy.value]
    rw [show ((Ts k).strat i).trades = [] from h.zero_before hil]
    simp
  · intro hk
    simp at hk

/-- Structured operational witness for an emulatable trader family. Where
`EfficientlyEmulatable` only certifies the paper-facing token semantics, this witness also
exposes polynomially computable trade boundaries, coefficient segments, and sentence
codes. That boundary data is exactly what a uniform syntax transformation (such as scaling
every trade by a generated feature) needs. Indices are
`z = ⟨⟨k,n⟩,j⟩`: family member, day, then trade number. -/
structure PolyTradeEmulatable (Ts : ℕ → Trader) where
  launchGated : LaunchGated Ts
  tradeCount : ℕ → ℕ
  coefficient : ℕ → EF
  sentence : ℕ → Sentence
  tradeCount_poly : ∃ c, PolyFueled c tradeCount
  coefficient_poly : BigSpliceStream (fun z => (coefficient z).serialize)
  sentence_poly : BigSentenceCodes sentence
  trades_eq : ∀ k n,
    ((Ts k).strat n).trades =
      (List.range (tradeCount (Nat.pair k n))).map (fun j =>
        let z := Nat.pair (Nat.pair k n) j
        (coefficient z, sentence z))

/-- A paired segment emitter supplies the raw universal-program witness for an emulatable
family.  This is the family analogue of `ecTok_of_segStream`; the proof converts polynomial
bounds in the paired input `⟨k,n⟩` to bounds in `n` using the side condition `k ≤ n`. -/
lemma EfficientlyEmulatable.of_polySeg {Ts : ℕ → Trader}
    (hzero : ∀ k n, n < k → ((Ts k).strat n).trades = [])
    (hs : PolySegStream (fun z =>
      serializeTrades ((Ts z.unpair.1).strat z.unpair.2).trades)) :
    EfficientlyEmulatable Ts := by
  obtain ⟨ct, cl, tokenFn, lenFn, htok, hlen, hlens, hspec⟩ := hs
  -- Reassociate `⟨k,⟨n,i⟩⟩` to the segment emitter's `⟨⟨k,n⟩,i⟩`.
  let canonicalCode : Nat.Partrec.Code :=
    ((Nat.Partrec.Code.left.pair
      (Nat.Partrec.Code.left.comp Nat.Partrec.Code.right)).pair
        (Nat.Partrec.Code.right.comp Nat.Partrec.Code.right))
  have hcanonical : PolyFueled canonicalCode (fun x =>
      Nat.pair (Nat.pair x.unpair.1 x.unpair.2.unpair.1) x.unpair.2.unpair.2) := by
    exact (PolyFueled.left.pair (PolyFueled.left.comp PolyFueled.right)).pair
      (PolyFueled.right.comp PolyFueled.right)
  have htoken : PolyFueled (ct.comp canonicalCode) (fun x =>
      tokenFn (Nat.pair (Nat.pair x.unpair.1 x.unpair.2.unpair.1)
        x.unpair.2.unpair.2)) := htok.comp hcanonical
  obtain ⟨bc, hfc, _, aT, kT, hkT⟩ := htoken
  obtain ⟨_, _, hlenPoly, _⟩ := hlen
  obtain ⟨aL, kL, hkL⟩ := hlenPoly
  let lenBound : ℕ → ℕ := fun n => aL * (Nat.pair n n + 1) ^ kL + aL
  have hdiagPair : IsPolyBounded (fun n => Nat.pair n n) :=
    (IsPolyBounded.linear 0).pair (IsPolyBounded.linear 0)
  have hlenBound : IsPolyBounded lenBound := by
    exact (show IsPolyBounded (fun x => aL * (x + 1) ^ kL + aL) from
      ⟨aL, kL, fun _ => le_rfl⟩).comp hdiagPair
  let inputBound : ℕ → ℕ := fun n => Nat.pair n (Nat.pair n (lenBound n))
  have hinputBound : IsPolyBounded inputBound :=
    (IsPolyBounded.linear 0).pair ((IsPolyBounded.linear 0).pair hlenBound)
  let fuelBound : ℕ → ℕ := fun n => aT * (inputBound n + 1) ^ kT + aT
  have hfuelBound : IsPolyBounded fuelBound := by
    exact (show IsPolyBounded (fun x => aT * (x + 1) ^ kT + aT) from
      ⟨aT, kT, fun _ => le_rfl⟩).comp hinputBound
  obtain ⟨A, K, hAK⟩ := hlenBound.max hfuelBound
  refine ⟨ct.comp canonicalCode, A, K, hzero, ?_, ?_⟩
  · intro k n hkn
    have hstreamLen :
        (serializeTrades ((Ts k).strat n).trades).length = lenFn (Nat.pair k n) := by
      have raw := hlens (Nat.pair k n)
      dsimp only at raw
      rw [Nat.unpair_pair k n] at raw
      exact raw
    rw [hstreamLen]
    have hpair : Nat.pair k n ≤ Nat.pair n n := pair_le_pair_left' n hkn
    calc
      lenFn (Nat.pair k n) ≤ aL * (Nat.pair k n + 1) ^ kL + aL := hkL _
      _ ≤ lenBound n := by dsimp only [lenBound]; gcongr
      _ ≤ A * (n + 1) ^ K + A := (le_max_left _ _).trans (hAK n)
  · intro k n i hkn hi
    have hstreamLen :
        (serializeTrades ((Ts k).strat n).trades).length = lenFn (Nat.pair k n) := by
      have raw := hlens (Nat.pair k n)
      dsimp only at raw
      rw [Nat.unpair_pair k n] at raw
      exact raw
    have hpair : Nat.pair k n ≤ Nat.pair n n := pair_le_pair_left' n hkn
    have hlenLe : lenFn (Nat.pair k n) ≤ lenBound n :=
      (hkL _).trans (by dsimp only [lenBound]; gcongr)
    have hiLe : i ≤ lenBound n := by rw [hstreamLen] at hi; omega
    have hinner : Nat.pair n i ≤ Nat.pair n (lenBound n) :=
      pair_le_pair_right' n hiLe
    have hx : Nat.pair k (Nat.pair n i) ≤ inputBound n := by
      dsimp only [inputBound]
      exact (pair_le_pair_left' (Nat.pair n i) hkn).trans
        (pair_le_pair_right' n hinner)
    have hbc : bc (Nat.pair k (Nat.pair n i)) ≤ A * (n + 1) ^ K + A := by
      calc
        bc (Nat.pair k (Nat.pair n i)) ≤
            aT * (Nat.pair k (Nat.pair n i) + 1) ^ kT + aT := hkT _
        _ ≤ fuelBound n := by dsimp only [fuelBound]; gcongr
        _ ≤ A * (n + 1) ^ K + A := (le_max_right _ _).trans (hAK n)
    have key := hfc (Nat.pair k (Nat.pair n i))
    simp only [Nat.unpair_pair] at key
    have hspec' : tokenFn (Nat.pair (Nat.pair k n) i) =
        (serializeTrades ((Ts k).strat n).trades).getD i 0 := by
      have raw := hspec (Nat.pair k n) i (by rw [← hstreamLen]; exact hi)
      dsimp only at raw
      rw [Nat.unpair_pair k n] at raw
      exact raw
    rw [hspec'] at key
    simpa [Nat.unpair_pair] using Nat.Partrec.Code.evaln_mono hbc key

/-- Drop the finite prefix of a trader family, replacing early members by the zero trader. -/
def gateTraderFamily (start : ℕ) (Ts : ℕ → Trader) (i : ℕ) : Trader :=
  if start ≤ i then Ts i else Trader.zero

/-- The zero trader has every ROI rate vacuously.  This is the harmless finite-prefix
padding used when a repeatable profitable family only starts after some day. -/
lemma Trader.zero_hasROI (V : History) (DP : DeductiveProcess) (ε : ℝ) :
    HasROI Trader.zero V DP ε := by
  constructor
  · simp [Trader.zero, Strategy.magnitude]
  · intro η hη
    refine ⟨0, fun n _ v _ => ?_⟩
    have hmag : Trader.zero.magnitude V = 0 := by
      simp [Trader.magnitude, Trader.zero, Strategy.magnitude]
    rw [hmag, mul_zero, Trader.zero_netWorth]

/-! ## Exact rational finite-prefix evaluation

A bounded verifier decides the maturity conditions by evaluating magnitude and net worth
exactly, over the rationals, on a finite prefix of days, against a `MarketComputation`.
Each `…AtFuel` evaluator comes with a soundness lemma (a successful answer is the exact
value) and a completeness lemma (enough fuel makes it succeed). -/

/-- Executable rational share magnitude for one strategy. -/
def Strategy.magnitudeRat {n : ℕ} (T : Strategy n)
    (Q : ℕ → Sentence → ℚ) : ℚ :=
  (T.trades.map (fun p => |p.1.denoteRat Q|)).sum

/-- Executable rational value for one strategy under a rational payout table. -/
def Strategy.valueRat {n : ℕ} (T : Strategy n)
    (Q : ℕ → Sentence → ℚ) (w : Sentence → ℚ) : ℚ :=
  (T.trades.map (fun p => p.1.denoteRat Q * (w p.2 - Q n p.2))).sum

/-- Market cells needed to compute the rational magnitude of a trade list. -/
def Strategy.magnitudeRatQueries : List (EF × Sentence) → List (ℕ × Sentence)
  | [] => []
  | p :: rest => p.1.priceQueries ++ magnitudeRatQueries rest

/-- Market cells needed to compute the rational value of a day-`n` trade list.  Besides
coefficient features, this includes the day-`n` purchase quote of every traded sentence. -/
def Strategy.valueRatQueries (n : ℕ) : List (EF × Sentence) → List (ℕ × Sentence)
  | [] => []
  | p :: rest => p.1.priceQueries ++ (n, p.2) :: valueRatQueries n rest

/-- Bounded exact magnitude evaluator for a raw trade list. -/
def Strategy.magnitudeRatListAtFuel {P : History} (market : MarketComputation P)
    (fuel : ℕ) : List (EF × Sentence) → Option ℚ
  | [] => some 0
  | p :: rest => do
      let coefficient ← p.1.denoteRatWithAtFuel market fuel []
      let tail ← magnitudeRatListAtFuel market fuel rest
      pure (|coefficient| + tail)

/-- Bounded exact value evaluator for a raw day-`n` trade list. -/
def Strategy.valueRatListAtFuel {P : History} (market : MarketComputation P)
    (fuel n : ℕ) (w : Sentence → ℚ) : List (EF × Sentence) → Option ℚ
  | [] => some 0
  | p :: rest => do
      let coefficient ← p.1.denoteRatWithAtFuel market fuel []
      let price ← market.quoteAtFuel fuel n p.2
      let tail ← valueRatListAtFuel market fuel n w rest
      pure (coefficient * (w p.2 - price) + tail)

/-- Bounded rational magnitude of one strategy. -/
def Strategy.magnitudeRatAtFuel {n : ℕ} (T : Strategy n)
    {P : History} (market : MarketComputation P) (fuel : ℕ) : Option ℚ :=
  magnitudeRatListAtFuel market fuel T.trades

/-- Bounded rational value of one strategy under a rational payout table. -/
def Strategy.valueRatAtFuel {n : ℕ} (T : Strategy n)
    {P : History} (market : MarketComputation P) (fuel : ℕ)
    (w : Sentence → ℚ) : Option ℚ :=
  valueRatListAtFuel market fuel n w T.trades

lemma Strategy.magnitudeRatListAtFuel_sound
    {P : History} (market : MarketComputation P) (fuel : ℕ)
    (trades : List (EF × Sentence)) {q : ℚ}
    (h : magnitudeRatListAtFuel market fuel trades = some q) :
    q = (trades.map (fun p =>
      |p.1.denoteRat (fun d φ => market.quote d (Encodable.encode φ))|)).sum := by
  induction trades generalizing q with
  | nil => simpa [magnitudeRatListAtFuel] using h.symm
  | cons p rest ih =>
      simp only [magnitudeRatListAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨coefficient, hcoefficient, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨tail, htail, hq⟩ := h
      change some (|coefficient| + tail) = some q at hq
      injection hq with hq
      subst q
      simp only [List.map_cons, List.sum_cons, EF.denoteRat]
      rw [p.1.denoteRatWithAtFuel_sound market fuel [] hcoefficient, ih htail]
      rfl

lemma Strategy.valueRatListAtFuel_sound
    {P : History} (market : MarketComputation P) (fuel n : ℕ)
    (w : Sentence → ℚ) (trades : List (EF × Sentence)) {q : ℚ}
    (h : valueRatListAtFuel market fuel n w trades = some q) :
    q = (trades.map (fun p =>
      p.1.denoteRat (fun d φ => market.quote d (Encodable.encode φ)) *
        (w p.2 - market.quote n (Encodable.encode p.2)))).sum := by
  induction trades generalizing q with
  | nil => simpa [valueRatListAtFuel] using h.symm
  | cons p rest ih =>
      simp only [valueRatListAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨coefficient, hcoefficient, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨price, hprice, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨tail, htail, hq⟩ := h
      change some (coefficient * (w p.2 - price) + tail) = some q at hq
      injection hq with hq
      subst q
      simp only [List.map_cons, List.sum_cons, EF.denoteRat]
      rw [p.1.denoteRatWithAtFuel_sound market fuel [] hcoefficient,
        market.quoteAtFuel_sound hprice, ih htail]
      rfl

lemma Strategy.magnitudeRatListAtFuel_complete
    {P : History} (market : MarketComputation P) (fuel : ℕ)
    (trades : List (EF × Sentence))
    (hready : ∀ query ∈ magnitudeRatQueries trades,
      market.quoteAtFuel fuel query.1 query.2 =
        some (market.quote query.1 (Encodable.encode query.2))) :
    magnitudeRatListAtFuel market fuel trades = some
      (trades.map (fun p =>
        |p.1.denoteRat (fun d φ => market.quote d (Encodable.encode φ))|)).sum := by
  induction trades with
  | nil => rfl
  | cons p rest ih =>
      have hcoefficient := p.1.denoteRatWithAtFuel_complete market fuel []
        (fun query hquery => hready query (by
          simp only [magnitudeRatQueries, List.mem_append]
          exact Or.inl hquery))
      have htail := ih (fun query hquery => hready query (by
        simp only [magnitudeRatQueries, List.mem_append]
        exact Or.inr hquery))
      simp [magnitudeRatListAtFuel, hcoefficient, htail, EF.denoteRat]

lemma Strategy.valueRatListAtFuel_complete
    {P : History} (market : MarketComputation P) (fuel n : ℕ)
    (w : Sentence → ℚ) (trades : List (EF × Sentence))
    (hready : ∀ query ∈ valueRatQueries n trades,
      market.quoteAtFuel fuel query.1 query.2 =
        some (market.quote query.1 (Encodable.encode query.2))) :
    valueRatListAtFuel market fuel n w trades = some
      (trades.map (fun p =>
        p.1.denoteRat (fun d φ => market.quote d (Encodable.encode φ)) *
          (w p.2 - market.quote n (Encodable.encode p.2)))).sum := by
  induction trades with
  | nil => rfl
  | cons p rest ih =>
      have hcoefficient := p.1.denoteRatWithAtFuel_complete market fuel []
        (fun query hquery => hready query (by
          simp only [valueRatQueries, List.mem_append, List.mem_cons]
          exact Or.inl hquery))
      have hprice := hready (n, p.2) (by
        simp only [valueRatQueries, List.mem_append, List.mem_cons]
        exact Or.inr (Or.inl trivial))
      have htail := ih (fun query hquery => hready query (by
        simp only [valueRatQueries, List.mem_append, List.mem_cons]
        exact Or.inr (Or.inr hquery)))
      simp [valueRatListAtFuel, hcoefficient, hprice, htail, EF.denoteRat]

/-- A successful bounded strategy-magnitude computation is exact. -/
lemma Strategy.magnitudeRatAtFuel_sound
    {n : ℕ} (T : Strategy n) {P : History} (market : MarketComputation P)
    (fuel : ℕ) {q : ℚ} (h : T.magnitudeRatAtFuel market fuel = some q) :
    q = T.magnitudeRat
      (fun d φ => market.quote d (Encodable.encode φ)) := by
  exact magnitudeRatListAtFuel_sound market fuel T.trades h

/-- A successful bounded strategy-value computation is exact. -/
lemma Strategy.valueRatAtFuel_sound
    {n : ℕ} (T : Strategy n) {P : History} (market : MarketComputation P)
    (fuel : ℕ) (w : Sentence → ℚ) {q : ℚ}
    (h : T.valueRatAtFuel market fuel w = some q) :
    q = T.valueRat (fun d φ => market.quote d (Encodable.encode φ)) w := by
  exact valueRatListAtFuel_sound market fuel n w T.trades h

/-- Exact rational `{0,1}` payout associated with a Boolean world. -/
noncomputable def PCWorld.payoutRat (v : PCWorld) (φ : Sentence) : ℚ :=
  by
    classical
    exact if v.Holds φ then 1 else 0

lemma PCWorld.payout_eq_ratCast (v : PCWorld) (φ : Sentence) :
    v.payout φ = (v.payoutRat φ : ℝ) := by
  classical
  by_cases h : v.Holds φ <;> simp [PCWorld.payout, PCWorld.payoutRat, h]

/-- Rational strategy magnitude agrees exactly with the real semantics of an exact
rational market table. -/
lemma Strategy.magnitude_eq_ratCast {n : ℕ} (T : Strategy n)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ d φ, P d φ = (Q d φ : ℝ)) :
    T.magnitude P = (T.magnitudeRat Q : ℝ) := by
  unfold Strategy.magnitude Strategy.magnitudeRat
  induction T.trades with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_abs]
      rw [EF.denote_eq_ratCast p.1 P Q hQ, ih]

/-- Rational strategy value agrees exactly with real value whenever the payout tables
agree pointwise. -/
lemma Strategy.value_eq_ratCast {n : ℕ} (T : Strategy n)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (wR : Sentence → ℝ) (wQ : Sentence → ℚ)
    (hw : ∀ φ, wR φ = (wQ φ : ℝ)) :
    T.value P wR = (T.valueRat Q wQ : ℝ) := by
  unfold Strategy.value Strategy.valueRat
  induction T.trades with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul,
        Rat.cast_sub]
      rw [EF.denote_eq_ratCast p.1 P Q hQ, hw p.2, hQ n p.2, ih]

/-- Exact rational magnitude traded through day `n`. -/
def Trader.partialMagnitudeRat (Tr : Trader) (Q : ℕ → Sentence → ℚ)
    (n : ℕ) : ℚ :=
  ∑ d ∈ Finset.range (n + 1), (Tr.strat d).magnitudeRat Q

/-- Exact rational net worth through day `n` under a rational payout table. -/
def Trader.partialNetWorthRat (Tr : Trader) (Q : ℕ → Sentence → ℚ)
    (w : Sentence → ℚ) (n : ℕ) : ℚ :=
  ∑ d ∈ Finset.range (n + 1), (Tr.strat d).valueRat Q w

/-- Market queries needed by rational magnitude across a finite list of trading days. -/
def Trader.partialMagnitudeRatQueriesDays (Tr : Trader) :
    List ℕ → List (ℕ × Sentence)
  | [] => []
  | d :: rest => Strategy.magnitudeRatQueries (Tr.strat d).trades ++
      partialMagnitudeRatQueriesDays Tr rest

/-- Market queries needed by rational net worth across a finite list of trading days. -/
def Trader.partialNetWorthRatQueriesDays (Tr : Trader) :
    List ℕ → List (ℕ × Sentence)
  | [] => []
  | d :: rest => Strategy.valueRatQueries d (Tr.strat d).trades ++
      partialNetWorthRatQueriesDays Tr rest

/-- Market cells needed by rational magnitude through day `n`. -/
def Trader.partialMagnitudeRatQueries (Tr : Trader) (n : ℕ) :
    List (ℕ × Sentence) :=
  partialMagnitudeRatQueriesDays Tr (List.range (n + 1))

/-- Market cells needed by rational net worth through day `n`. -/
def Trader.partialNetWorthRatQueries (Tr : Trader) (n : ℕ) :
    List (ℕ × Sentence) :=
  partialNetWorthRatQueriesDays Tr (List.range (n + 1))

/-- Bounded exact magnitude computation across a finite list of days. -/
def Trader.partialMagnitudeRatDaysAtFuel (Tr : Trader)
    {P : History} (market : MarketComputation P) (fuel : ℕ) :
    List ℕ → Option ℚ
  | [] => some 0
  | d :: rest => do
      let today ← (Tr.strat d).magnitudeRatAtFuel market fuel
      let tail ← partialMagnitudeRatDaysAtFuel Tr market fuel rest
      pure (today + tail)

/-- Bounded exact net-worth computation across a finite list of days. -/
def Trader.partialNetWorthRatDaysAtFuel (Tr : Trader)
    {P : History} (market : MarketComputation P) (fuel : ℕ)
    (w : Sentence → ℚ) : List ℕ → Option ℚ
  | [] => some 0
  | d :: rest => do
      let today ← (Tr.strat d).valueRatAtFuel market fuel w
      let tail ← partialNetWorthRatDaysAtFuel Tr market fuel w rest
      pure (today + tail)

/-- Bounded exact magnitude traded through day `n`. -/
def Trader.partialMagnitudeRatAtFuel (Tr : Trader)
    {P : History} (market : MarketComputation P) (fuel n : ℕ) : Option ℚ :=
  partialMagnitudeRatDaysAtFuel Tr market fuel (List.range (n + 1))

/-- Bounded exact net worth through day `n`. -/
def Trader.partialNetWorthRatAtFuel (Tr : Trader)
    {P : History} (market : MarketComputation P) (fuel : ℕ)
    (w : Sentence → ℚ) (n : ℕ) : Option ℚ :=
  partialNetWorthRatDaysAtFuel Tr market fuel w (List.range (n + 1))

lemma Trader.partialMagnitudeRatDaysAtFuel_sound
    (Tr : Trader) {P : History} (market : MarketComputation P) (fuel : ℕ)
    (days : List ℕ) {q : ℚ}
    (h : partialMagnitudeRatDaysAtFuel Tr market fuel days = some q) :
    q = (days.map (fun d => (Tr.strat d).magnitudeRat
      (fun j φ => market.quote j (Encodable.encode φ)))).sum := by
  induction days generalizing q with
  | nil => simpa [partialMagnitudeRatDaysAtFuel] using h.symm
  | cons d rest ih =>
      simp only [partialMagnitudeRatDaysAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨today, htoday, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨tail, htail, hq⟩ := h
      change some (today + tail) = some q at hq
      injection hq with hq
      subst q
      simp only [List.map_cons, List.sum_cons]
      rw [(Tr.strat d).magnitudeRatAtFuel_sound market fuel htoday, ih htail]

lemma Trader.partialNetWorthRatDaysAtFuel_sound
    (Tr : Trader) {P : History} (market : MarketComputation P) (fuel : ℕ)
    (w : Sentence → ℚ) (days : List ℕ) {q : ℚ}
    (h : partialNetWorthRatDaysAtFuel Tr market fuel w days = some q) :
    q = (days.map (fun d => (Tr.strat d).valueRat
      (fun j φ => market.quote j (Encodable.encode φ)) w)).sum := by
  induction days generalizing q with
  | nil => simpa [partialNetWorthRatDaysAtFuel] using h.symm
  | cons d rest ih =>
      simp only [partialNetWorthRatDaysAtFuel, Option.bind_eq_bind] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨today, htoday, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨tail, htail, hq⟩ := h
      change some (today + tail) = some q at hq
      injection hq with hq
      subst q
      simp only [List.map_cons, List.sum_cons]
      rw [(Tr.strat d).valueRatAtFuel_sound market fuel w htoday, ih htail]

lemma Trader.partialMagnitudeRatDaysAtFuel_complete
    (Tr : Trader) {P : History} (market : MarketComputation P) (fuel : ℕ)
    (days : List ℕ)
    (hready : ∀ query ∈ partialMagnitudeRatQueriesDays Tr days,
      market.quoteAtFuel fuel query.1 query.2 =
        some (market.quote query.1 (Encodable.encode query.2))) :
    partialMagnitudeRatDaysAtFuel Tr market fuel days = some
      (days.map (fun d => (Tr.strat d).magnitudeRat
        (fun j φ => market.quote j (Encodable.encode φ)))).sum := by
  induction days with
  | nil => rfl
  | cons d rest ih =>
      have htoday := Strategy.magnitudeRatListAtFuel_complete market fuel
        (Tr.strat d).trades (fun query hquery => hready query (by
          simp only [partialMagnitudeRatQueriesDays, List.mem_append]
          exact Or.inl hquery))
      have htail := ih (fun query hquery => hready query (by
        simp only [partialMagnitudeRatQueriesDays, List.mem_append]
        exact Or.inr hquery))
      simp [partialMagnitudeRatDaysAtFuel, Strategy.magnitudeRatAtFuel,
        Strategy.magnitudeRat, htoday, htail]

lemma Trader.partialNetWorthRatDaysAtFuel_complete
    (Tr : Trader) {P : History} (market : MarketComputation P) (fuel : ℕ)
    (w : Sentence → ℚ) (days : List ℕ)
    (hready : ∀ query ∈ partialNetWorthRatQueriesDays Tr days,
      market.quoteAtFuel fuel query.1 query.2 =
        some (market.quote query.1 (Encodable.encode query.2))) :
    partialNetWorthRatDaysAtFuel Tr market fuel w days = some
      (days.map (fun d => (Tr.strat d).valueRat
        (fun j φ => market.quote j (Encodable.encode φ)) w)).sum := by
  induction days with
  | nil => rfl
  | cons d rest ih =>
      have htoday := Strategy.valueRatListAtFuel_complete market fuel d w
        (Tr.strat d).trades (fun query hquery => hready query (by
          simp only [partialNetWorthRatQueriesDays, List.mem_append]
          exact Or.inl hquery))
      have htail := ih (fun query hquery => hready query (by
        simp only [partialNetWorthRatQueriesDays, List.mem_append]
        exact Or.inr hquery))
      simp [partialNetWorthRatDaysAtFuel, Strategy.valueRatAtFuel,
        Strategy.valueRat, htoday, htail]

private lemma sum_map_list_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ d ∈ Finset.range n, f d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

lemma Trader.partialMagnitudeRatAtFuel_sound
    (Tr : Trader) {P : History} (market : MarketComputation P) (fuel n : ℕ)
    {q : ℚ} (h : Tr.partialMagnitudeRatAtFuel market fuel n = some q) :
    q = Tr.partialMagnitudeRat
      (fun d φ => market.quote d (Encodable.encode φ)) n := by
  simpa [partialMagnitudeRatAtFuel, partialMagnitudeRat, sum_map_list_range] using
    Tr.partialMagnitudeRatDaysAtFuel_sound market fuel (List.range (n + 1)) h

lemma Trader.partialNetWorthRatAtFuel_sound
    (Tr : Trader) {P : History} (market : MarketComputation P) (fuel : ℕ)
    (w : Sentence → ℚ) (n : ℕ) {q : ℚ}
    (h : Tr.partialNetWorthRatAtFuel market fuel w n = some q) :
    q = Tr.partialNetWorthRat
      (fun d φ => market.quote d (Encodable.encode φ)) w n := by
  simpa [partialNetWorthRatAtFuel, partialNetWorthRat, sum_map_list_range] using
    Tr.partialNetWorthRatDaysAtFuel_sound market fuel w (List.range (n + 1)) h

lemma Trader.partialMagnitudeRatAtFuel_complete
    (Tr : Trader) {P : History} (market : MarketComputation P) (fuel n : ℕ)
    (hready : ∀ query ∈ Tr.partialMagnitudeRatQueries n,
      market.quoteAtFuel fuel query.1 query.2 =
        some (market.quote query.1 (Encodable.encode query.2))) :
    Tr.partialMagnitudeRatAtFuel market fuel n = some
      (Tr.partialMagnitudeRat
        (fun d φ => market.quote d (Encodable.encode φ)) n) := by
  simpa [partialMagnitudeRatAtFuel, partialMagnitudeRat,
    partialMagnitudeRatQueries, sum_map_list_range] using
      Tr.partialMagnitudeRatDaysAtFuel_complete market fuel
        (List.range (n + 1)) hready

lemma Trader.partialNetWorthRatAtFuel_complete
    (Tr : Trader) {P : History} (market : MarketComputation P) (fuel : ℕ)
    (w : Sentence → ℚ) (n : ℕ)
    (hready : ∀ query ∈ Tr.partialNetWorthRatQueries n,
      market.quoteAtFuel fuel query.1 query.2 =
        some (market.quote query.1 (Encodable.encode query.2))) :
    Tr.partialNetWorthRatAtFuel market fuel w n = some
      (Tr.partialNetWorthRat
        (fun d φ => market.quote d (Encodable.encode φ)) w n) := by
  simpa [partialNetWorthRatAtFuel, partialNetWorthRat,
    partialNetWorthRatQueries, sum_map_list_range] using
      Tr.partialNetWorthRatDaysAtFuel_complete market fuel w
        (List.range (n + 1)) hready

/-- Rational partial net worth only depends on payouts of sentences actually traded
through the requested day. -/
lemma Trader.partialNetWorthRat_congr (Tr : Trader)
    (Q : ℕ → Sentence → ℚ) (w w' : Sentence → ℚ) (n : ℕ)
    (hw : ∀ d ≤ n, ∀ p ∈ (Tr.strat d).trades, w p.2 = w' p.2) :
    Tr.partialNetWorthRat Q w n = Tr.partialNetWorthRat Q w' n := by
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.mem_range] at hd
  unfold Strategy.valueRat
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  rw [hw d (by omega) x hx]

lemma Trader.partialMagnitude_eq_ratCast (Tr : Trader)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ d φ, P d φ = (Q d φ : ℝ)) (n : ℕ) :
    (∑ d ∈ Finset.range (n + 1), (Tr.strat d).magnitude P) =
      (Tr.partialMagnitudeRat Q n : ℝ) := by
  simp only [Trader.partialMagnitudeRat, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact (Tr.strat d).magnitude_eq_ratCast P Q hQ

lemma Trader.netWorth_eq_ratCast (Tr : Trader)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (v : PCWorld) (wQ : Sentence → ℚ)
    (hw : ∀ φ, v.payout φ = (wQ φ : ℝ)) (n : ℕ) :
    Tr.netWorth P v n = (Tr.partialNetWorthRat Q wQ n : ℝ) := by
  simp only [Trader.netWorth, Trader.partialNetWorthRat, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact (Tr.strat d).value_eq_ratCast P Q hQ v.payout wQ hw

/-! ## Segment emission for emulatable families -/

/-- Serialization distributes over trade-list concatenation. This is the normal form every
segment-emitter proof rewrites with. -/
@[simp] lemma serializeTrades_append (xs ys : List (EF × Sentence)) :
    serializeTrades (xs ++ ys) = serializeTrades xs ++ serializeTrades ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, serializeTrades, ih, List.append_assoc]

lemma serializeTrades_flatMap {α : Type} (xs : List α) (f : α → List (EF × Sentence)) :
    serializeTrades (xs.flatMap f) = xs.flatMap (fun x => serializeTrades (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma serializeTrades_map_singleton {α : Type} (xs : List α)
    (f : α → EF × Sentence) :
    serializeTrades (xs.map f) = xs.flatMap (fun x => serializeTrades [f x]) := by
  rw [← serializeTrades_flatMap]
  congr 1
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The structured witness gives a compositional segment emitter for each component/day
trade list. This is the reusable bridge from trade-level boundary data back to the faithful
`serializeTrades` representation. -/
lemma PolyTradeEmulatable.polySeg {Ts : ℕ → Trader} (h : PolyTradeEmulatable Ts) :
    BigSpliceStream (fun z =>
      serializeTrades ((Ts z.unpair.1).strat z.unpair.2).trades) := by
  obtain ⟨ccount, hcount⟩ := h.tradeCount_poly
  have hframe := BigSpliceStream.tradeSlot h.sentence_poly PolyFueled.id
  have hone : BigSpliceStream (fun z =>
      serializeTrades [(h.coefficient z, h.sentence z)]) := by
    refine BigSpliceStream.of_eq (h.coefficient_poly.append hframe) ?_
    intro z
    simp [serializeTrades]
  have hall := hone.concatVar hcount
  refine BigSpliceStream.of_eq hall ?_
  intro z
  rw [h.trades_eq]
  rw [serializeTrades_map_singleton]
  simp only [Nat.pair_unpair]

/-- Structured emulatability is closed under a fixed finite-prefix gate. -/
noncomputable def PolyTradeEmulatable.gateBefore {Ts : ℕ → Trader}
    (h : PolyTradeEmulatable Ts) (start : ℕ) :
    PolyTradeEmulatable (gateTraderFamily start Ts) := by
  let ccount := Classical.choose h.tradeCount_poly
  have hcount := Classical.choose_spec h.tradeCount_poly
  have htest := subc_polyFueled.comp
    (PolyFueled.left.succ_comp.pair (PolyFueled.const start))
  have hcountRaw := ifzSel_polyFueled.comp
    (((PolyFueled.const 0).pair hcount).pair htest)
  let count : ℕ → ℕ := fun z => if start ≤ z.unpair.1 then h.tradeCount z else 0
  let countCode : Nat.Partrec.Code := ifzSel.comp
    (((Nat.Partrec.Code.const 0).pair ccount).pair
      (subc.comp ((Nat.Partrec.Code.succ.comp Nat.Partrec.Code.left).pair
        (Nat.Partrec.Code.const start))))
  have hcountGate : PolyFueled countCode count := by
    apply PolyFueled.of_eq hcountRaw
    intro z
    simp only [Nat.unpair_pair, ifzSelFn, count]
    by_cases hs : start ≤ z.unpair.1
    · rw [if_pos hs, if_neg (by omega)]
    · rw [if_neg hs, if_pos (by omega)]
  have hzeroSeg : BigSpliceStream (fun _ => []) :=
    BigSpliceStream.ofTransparent
      (BigTokenStream.ofPolySegStream (PolySegStream.ofTokenStream PolyTokenStream.nil))
      (fun _ => UnRpnTransparent.nil)
  have hmemberTestRaw := subc_polyFueled.comp
    (PolyFueled.left.succ_comp.pair (PolyFueled.const start))
  have hmemberTest : PolyFueled
      (subc.comp ((Nat.Partrec.Code.succ.comp Nat.Partrec.Code.left).pair
        (Nat.Partrec.Code.const start)))
      (fun z => z.unpair.1 + 1 - start) := by
    apply PolyFueled.of_eq hmemberTestRaw
    intro z
    simp only [Nat.unpair_pair]
  have hstream : BigSpliceStream (fun z => serializeTrades
      (((gateTraderFamily start Ts) z.unpair.1).strat z.unpair.2).trades) := by
    refine BigSpliceStream.of_eq
      (BigSpliceStream.ifZero hzeroSeg h.polySeg hmemberTest) ?_
    intro z
    simp only [gateTraderFamily]
    by_cases hs : start ≤ z.unpair.1
    · rw [if_pos hs, if_neg (by omega)]
    · rw [if_neg hs, if_pos (by omega)]
      simp [Trader.zero, serializeTrades]
  have hzero : ∀ k n, n < k →
      (((gateTraderFamily start Ts) k).strat n).trades = [] := by
    intro k n hnk
    by_cases hs : start ≤ k
    · rw [gateTraderFamily, if_pos hs]
      exact h.launchGated.zero_before hnk
    · simp [gateTraderFamily, hs, Trader.zero]
  refine
    { launchGated := hzero
      tradeCount := count
      coefficient := h.coefficient
      sentence := h.sentence
      tradeCount_poly := ⟨countCode, hcountGate⟩
      coefficient_poly := h.coefficient_poly
      sentence_poly := h.sentence_poly
      trades_eq := ?_ }
  intro k n
  by_cases hs : start ≤ k
  · rw [gateTraderFamily, if_pos hs, h.trades_eq]
    simp [count, hs]
  · simp [gateTraderFamily, hs, Trader.zero, count]

/-! ## Scaling and joining strategies

General `Strategy` algebra: the budgeted trader is a join of components, each scaled by one
expressible feature. -/

namespace Strategy

/-- Multiply every share coefficient in a strategy by one legal feature. -/
def scaleBy {n : ℕ} (e : EF) (he : e.rank ≤ n) (T : Strategy n) : Strategy n where
  trades := T.trades.map (fun p => (EF.mul e p.1, p.2))
  rank_le := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact Nat.max_le.mpr ⟨he, T.rank_le q hq⟩

lemma scaleBy_value {n : ℕ} (e : EF) (he : e.rank ≤ n) (T : Strategy n)
    (V : History) (w : Valuation) :
    (T.scaleBy e he).value V w = e.denote V * T.value V w := by
  simp only [scaleBy, Strategy.value, List.map_map]
  induction T.trades with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, EF.denote_mul,
        Pi.mul_apply] at ih ⊢
      rw [ih]
      ring

lemma scaleBy_magnitude {n : ℕ} (e : EF) (he : e.rank ≤ n) (T : Strategy n)
    (V : History) :
    (T.scaleBy e he).magnitude V = |e.denote V| * T.magnitude V := by
  simp only [scaleBy, Strategy.magnitude, List.map_map]
  induction T.trades with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, EF.denote_mul,
        Pi.mul_apply, abs_mul] at ih ⊢
      rw [ih]
      ring

/-- Concatenate a finite collection of same-day strategies. -/
def join {n : ℕ} (ts : List (Strategy n)) : Strategy n where
  trades := ts.flatMap Strategy.trades
  rank_le := by
    intro p hp
    simp only [List.mem_flatMap] at hp
    obtain ⟨T, hT, hp⟩ := hp
    exact T.rank_le p hp

lemma join_value {n : ℕ} (ts : List (Strategy n)) (V : History) (w : Valuation) :
    (Strategy.join ts).value V w = (ts.map (fun T => T.value V w)).sum := by
  induction ts with
  | nil => simp [join, Strategy.value]
  | cons T ts ih =>
      calc
        (Strategy.join (T :: ts)).value V w =
            T.value V w + (Strategy.join ts).value V w := by
              simp [Strategy.join, Strategy.value]
        _ = ((T :: ts).map (fun S => S.value V w)).sum := by
              rw [ih]
              rfl

lemma join_magnitude {n : ℕ} (ts : List (Strategy n)) (V : History) :
    (Strategy.join ts).magnitude V = (ts.map (fun T => T.magnitude V)).sum := by
  induction ts with
  | nil => simp [join, Strategy.magnitude]
  | cons T ts ih =>
      calc
        (Strategy.join (T :: ts)).magnitude V =
            T.magnitude V + (Strategy.join ts).magnitude V := by
              simp [Strategy.join, Strategy.magnitude]
        _ = ((T :: ts).map (fun S => S.magnitude V)).sum := by
              rw [ih]
              rfl

end Strategy

namespace ROIBudget

/-! ## Feature sums and the openness table -/

/-- The openness table is efficiently available to the syntax emitter. Inputs are paired
as `⟨k,i⟩`; output `1` means component `i` is active at budget stage `k`. -/
def PolyActiveSchedule (active : ℕ → ℕ → Bool) : Prop :=
  ∃ c : Nat.Partrec.Code, PolyFueled c (fun z => if active z.unpair.2 z.unpair.1 then 1 else 0)

/-- Sum a finite list of expressible features inside the feature DSL. -/
def sumFeatures : List EF → EF :=
  List.foldr EF.add (EF.const 0)

lemma serialize_sumFeatures (es : List EF) :
    (sumFeatures es).serialize = es.flatMap EF.serialize ++
      (EF.const 0).serialize ++ List.replicate es.length 2 := by
  induction es with
  | nil => simp [sumFeatures, EF.serialize]
  | cons e es ih =>
      change e.serialize ++ (sumFeatures es).serialize ++ [2] = _
      rw [ih]
      simp only [List.flatMap_cons, List.length_cons]
      rw [List.replicate_succ']
      simp only [List.append_assoc]

lemma sumFeatures_denote (es : List EF) (V : History) :
    (sumFeatures es).denote V = (es.map (fun e => e.denote V)).sum := by
  induction es with
  | nil => simp [sumFeatures]
  | cons e es ih =>
      change e.denote V + (sumFeatures es).denote V =
        e.denote V + (es.map (fun e => e.denote V)).sum
      rw [ih]

lemma sumFeatures_denoteWith (es : List EF) (ρ : List ℝ) (V : History) :
    (sumFeatures es).denoteWith ρ V =
      (es.map (fun e => e.denoteWith ρ V)).sum := by
  induction es with
  | nil => simp [sumFeatures]
  | cons e es ih =>
      change e.denoteWith ρ V + (sumFeatures es).denoteWith ρ V =
        e.denoteWith ρ V + (es.map (fun e => e.denoteWith ρ V)).sum
      rw [ih]

lemma sumFeatures_rank_le (es : List EF) (n : ℕ)
    (h : ∀ e ∈ es, e.rank ≤ n) : (sumFeatures es).rank ≤ n := by
  induction es with
  | nil => change 0 ≤ n; omega
  | cons e es ih =>
      change Nat.max e.rank (sumFeatures es).rank ≤ n
      exact Nat.max_le.mpr ⟨h e (by simp), ih (fun x hx => h x (by simp [hx]))⟩

/-! ## The adaptive budget: Boolean closing schedules -/

/-- Capital currently tied up by components with index below `n`. -/
noncomputable def outstanding (active : ℕ → ℕ → Bool) (α β : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin n, if active i n then β i * α i else 0

/-- The paper's adaptive scaling coefficient
`βₙ = 1 - ∑_{i<n, open(i,n)} βᵢ αᵢ`.

Well-founded recursion is appropriate here: the right hand side only asks for weights
with index strictly below `n`. -/
noncomputable def weight (active : ℕ → ℕ → Bool) (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - ∑ i : Fin n,
    if active i n then weight active α i * α i else 0
termination_by n
decreasing_by exact i.isLt

/-! ### Shared straight-line chains

A budget coefficient is defined by a recurrence in the earlier coefficients. Since features
are reified syntax (`dd:dsl`), reifying that recurrence directly would inline every earlier
value and make the index-`n` expression exponential in `n`. A `letChain` instead binds the
consecutive recurrence bodies with `EF.letE`, so each earlier value is written once and
referred to by a constant-size `EF.var`. Both budgets in this module are instances: they
differ only in the body family they chain. -/

/-- Bind `count` consecutive recurrence bodies starting at index `k`, then return the last
one. Body `j` is interpreted in an environment holding `[βⱼ₋₁, …, β₀]`. -/
def letChain (body : ℕ → EF) (k : ℕ) : ℕ → EF
  | 0 => EF.var 0
  | count + 1 => EF.letE (body k) (letChain body (k + 1) count)

/-- The chain computing the index-`n` value of a recurrence. -/
def sharedOf (body : ℕ → EF) (n : ℕ) : EF := letChain body 0 (n + 1)

/-- The postfix stream of a chain consists of its consecutive binding bodies, the terminal
reference to the newest binding, and one `letE` tag per binding. -/
lemma letChain_serialize (body : ℕ → EF) (k count : ℕ) :
    (letChain body k count).serialize =
      (List.range' k count).flatMap (fun j => (body j).serialize) ++
        (EF.var 0).serialize ++ List.replicate count 8 := by
  induction count generalizing k with
  | zero => simp [letChain, EF.serialize]
  | succ count ih =>
      rw [letChain]
      change (body k).serialize ++ (letChain body (k + 1) count).serialize ++ [8] = _
      rw [ih (k + 1)]
      simp [List.range'_succ, List.replicate_succ', List.append_assoc]

/-- Uniform polynomial-time emission of a whole chain, from uniform emission of its
recurrence bodies. -/
lemma sharedOf_polySeg (body : ℕ → EF)
    (hbody : BigSpliceStream (fun k => (body k).serialize)) :
    BigSpliceStream (fun n => (sharedOf body n).serialize) := by
  have hbodies : BigSpliceStream (fun n =>
      (List.range (n + 1)).flatMap (fun j => (body j).serialize)) := by
    refine BigSpliceStream.of_eq
      (BigSpliceStream.concatVar (hbody.comp PolyFueled.right)
        PolyFueled.id.succ_comp) ?_
    intro n
    simp only [Nat.unpair_pair]
  have hvar : BigSpliceStream (fun _ => (EF.var 0).serialize) :=
    BigSpliceStream.serialize_var (PolyFueled.const 0)
  have htags : BigSpliceStream (fun n => List.replicate (n + 1) 8) :=
    BigSpliceStream.repeatTag 8 (by norm_num) PolyFueled.id.succ_comp
  refine BigSpliceStream.of_eq ((hbodies.append hvar).append htags) ?_
  intro n
  rw [sharedOf, letChain_serialize]
  rw [List.range_eq_range']

/-- Bodies of rank at most their own index give a chain of rank at most its last index. -/
lemma letChain_rank_le (body : ℕ → EF) (hbody : ∀ k, (body k).rank ≤ k) (k count : ℕ) :
    (letChain body k count).rank ≤ if count = 0 then 0 else k + count - 1 := by
  induction count generalizing k with
  | zero => simp [letChain]
  | succ count ih =>
      rw [letChain, EF.rank]
      apply Nat.max_le.mpr
      constructor
      · exact (hbody k).trans (by cases count <;> simp)
      · have H := ih (k + 1)
        cases count with
        | zero => simp [letChain]
        | succ count =>
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H

/-- The index-`n` chain is legal on day `n`. -/
lemma sharedOf_rank_le (body : ℕ → EF) (hbody : ∀ k, (body k).rank ≤ k) (n : ℕ) :
    (sharedOf body n).rank ≤ n := by
  rw [sharedOf]
  simpa using letChain_rank_le body hbody 0 (n + 1)

/-- The environment invariant a chain maintains: slot `k - 1 - i` holds the value of the
recurrence at index `i`. -/
private def PriorEnv (w : ℕ → ℝ) (k : ℕ) (ρ : List ℝ) : Prop :=
  ∀ i : Fin k, ρ.getD (k - 1 - i) 0 = w i

private lemma priorEnv_cons (w : ℕ → ℝ) (k : ℕ) (ρ : List ℝ) (hρ : PriorEnv w k ρ) :
    PriorEnv w (k + 1) (w k :: ρ) := by
  intro i
  by_cases hi : (i : ℕ) = k
  · have hilast : i = Fin.last k := Fin.ext hi
    subst i
    simp
  · have hik : (i : ℕ) < k := by omega
    have hidx : k + 1 - 1 - (i : ℕ) = (k - 1 - (i : ℕ)) + 1 := by omega
    rw [hidx]
    simp only [List.getD_cons_succ]
    exact hρ ⟨i, hik⟩

private lemma letChain_denoteWith (body : ℕ → EF) (w : ℕ → ℝ) (V : History)
    (hbody : ∀ k ρ, PriorEnv w k ρ → (body k).denoteWith ρ V = w k)
    (k count : ℕ) (ρ : List ℝ) (hρ : PriorEnv w k ρ) :
    (letChain body k count).denoteWith ρ V =
      if count = 0 then ρ.getD 0 0 else w (k + count - 1) := by
  induction count generalizing k ρ with
  | zero => simp [letChain]
  | succ count ih =>
      rw [letChain, EF.denoteWith, hbody k ρ hρ]
      rw [ih (k := k + 1) (ρ := w k :: ρ) (priorEnv_cons w k ρ hρ)]
      cases count with
      | zero => simp
      | succ count =>
          simp
          congr 1
          omega

/-- A chain denotes the recurrence it encodes. -/
private lemma sharedOf_denote (body : ℕ → EF) (w : ℕ → ℝ) (V : History)
    (hbody : ∀ k ρ, PriorEnv w k ρ → (body k).denoteWith ρ V = w k) (n : ℕ) :
    (sharedOf body n).denote V = w n := by
  rw [sharedOf, EF.denote]
  simpa using letChain_denoteWith body w V hbody 0 (n + 1) [] (fun i => Fin.elim0 i)

/-- A chain is closed with respect to any surrounding `letE` environment: its internal
bindings shadow and discharge every variable the recurrence uses. -/
private lemma sharedOf_closed (body : ℕ → EF) (w : ℕ → ℝ) (V : History)
    (hbody : ∀ k ρ, PriorEnv w k ρ → (body k).denoteWith ρ V = w k) (n : ℕ)
    (ρ : List ℝ) :
    (sharedOf body n).denoteWith ρ V = (sharedOf body n).denote V := by
  rw [sharedOf, EF.denote]
  have hleft := letChain_denoteWith body w V hbody 0 (n + 1) ρ (fun i => Fin.elim0 i)
  have hright := letChain_denoteWith body w V hbody 0 (n + 1) [] (fun i => Fin.elim0 i)
  simpa using hleft.trans hright.symm

/-! ### Shared straight-line budget expression -/

/-- The right-hand side defining `βₖ`, interpreted in an environment containing
`[βₖ₋₁, …, β₀]`. -/
def featureWeightBody (active : ℕ → ℕ → Bool) (α : ℕ → EF) (k : ℕ) : EF :=
  EF.add (EF.const 1) (EF.mul (EF.const (-1))
    (sumFeatures (List.ofFn (fun i : Fin k =>
      if active i k then EF.mul (EF.var (k - 1 - i)) (α i) else EF.const 0))))

/-- Uniform variable-length emission of the recurrence bodies. This is the triangular
`i < k` use of `BigSpliceStream.concatVar`: each term conditionally emits either
`var(k-1-i) * αᵢ` or zero, and the fold's postfix `add` tags form a second linear run. -/
lemma featureWeightBody_polySeg (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : BigSpliceStream (fun i => (α i).serialize))
    (hactive : PolyActiveSchedule active) :
    BigSpliceStream (fun k => (featureWeightBody active α k).serialize) := by
  obtain ⟨cactive, hactivePF⟩ := hactive
  let term : ℕ → EF := fun z =>
    if active z.unpair.2 z.unpair.1 then
      EF.mul (EF.var (z.unpair.1 - 1 - z.unpair.2)) (α z.unpair.2)
    else EF.const 0
  have idxPF := subc_polyFueled.comp
    ((predc_polyFueled.comp PolyFueled.left).pair PolyFueled.right)
  have idxPF' := idxPF.of_eq (f' := fun z => z.unpair.1 - 1 - z.unpair.2)
    (fun z => by simp [Nat.pred_eq_sub_one])
  have hvar : BigSpliceStream
      (fun z => (EF.var (z.unpair.1 - 1 - z.unpair.2)).serialize) :=
    BigSpliceStream.serialize_var idxPF'
  have hαright : BigSpliceStream (fun z => (α z.unpair.2).serialize) :=
    hα.comp PolyFueled.right
  have hmul : BigSpliceStream (fun z =>
      (EF.mul (EF.var (z.unpair.1 - 1 - z.unpair.2)) (α z.unpair.2)).serialize) :=
    BigSpliceStream.serialize_mul hvar hαright
  have hzero : BigSpliceStream (fun _ => (EF.const 0).serialize) :=
    BigSpliceStream.serialize_const 0
  have hterm : BigSpliceStream (fun z => (term z).serialize) := by
    have hchoose := BigSpliceStream.ifZero hzero hmul hactivePF
    refine BigSpliceStream.of_eq hchoose ?_
    intro z
    simp only [term]
    by_cases h : active z.unpair.2 z.unpair.1 = true
    · simp [h]
    · have hf : active z.unpair.2 z.unpair.1 = false := Bool.eq_false_of_not_eq_true h
      simp [hf]
  have hterms : BigSpliceStream (fun k =>
      (List.range k).flatMap (fun i => (term (Nat.pair k i)).serialize)) :=
    BigSpliceStream.concatVar hterm PolyFueled.id
  have haddTags : BigSpliceStream (fun k => List.replicate k 2) :=
    BigSpliceStream.repeatTag 2 (by norm_num) PolyFueled.id
  have hsumRaw := (hterms.append hzero).append haddTags
  have hsum : BigSpliceStream (fun k =>
      (sumFeatures (List.ofFn (fun i : Fin k => term (Nat.pair k i)))).serialize) := by
    refine BigSpliceStream.of_eq hsumRaw ?_
    intro k
    rw [serialize_sumFeatures]
    simp only [List.length_ofFn]
    congr 2
    rw [← List.map_coe_finRange_eq_range]
    rw [List.flatMap_map]
    simp only [List.ofFn_eq_map, List.flatMap_map]
  have hone : BigSpliceStream (fun _ => (EF.const 1).serialize) :=
    BigSpliceStream.serialize_const 1
  have hnegone : BigSpliceStream (fun _ => (EF.const (-1)).serialize) :=
    BigSpliceStream.serialize_const (-1)
  have hbody := BigSpliceStream.serialize_add hone
    (BigSpliceStream.serialize_mul hnegone hsum)
  refine BigSpliceStream.of_eq hbody ?_
  intro k
  simp only [featureWeightBody, term]
  congr 4
  congr 1
  funext i
  simp

/-- Bind `count` consecutive budget variables starting at `k`, then return the last one.
Each earlier `β` is represented once and referenced by a constant-size `EF.var`. -/
def sharedWeights (active : ℕ → ℕ → Bool) (α : ℕ → EF) (k : ℕ) : ℕ → EF :=
  letChain (featureWeightBody active α) k

/-- Polynomial-sharing version of the day-`n` budget coefficient. Definitionally
`sharedOf (featureWeightBody active α) n`; it is spelled through `sharedWeights` because
downstream emission proofs unfold it to a chain and then rewrite with
`sharedWeights_serialize`. -/
def sharedFeatureWeight (active : ℕ → ℕ → Bool) (α : ℕ → EF) (n : ℕ) : EF :=
  sharedWeights active α 0 (n + 1)

/-- The postfix stream of a shared chain consists of its consecutive binding bodies,
the terminal reference to the newest binding, and one `letE` tag per binding. -/
lemma sharedWeights_serialize (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (k count : ℕ) :
    (sharedWeights active α k count).serialize =
      (List.range' k count).flatMap
          (fun j => (featureWeightBody active α j).serialize) ++
        (EF.var 0).serialize ++ List.replicate count 8 :=
  letChain_serialize _ k count

/-- Uniform polynomial-time emission of the complete day-`n` shared budget coefficient.
This is the representation-level companion to `sharedFeatureWeight_denote` and
`sharedFeatureWeight_rank_le`. -/
lemma sharedFeatureWeight_polySeg (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : BigSpliceStream (fun i => (α i).serialize))
    (hactive : PolyActiveSchedule active) :
    BigSpliceStream (fun n => (sharedFeatureWeight active α n).serialize) :=
  sharedOf_polySeg _ (featureWeightBody_polySeg active α hα hactive)

private lemma featureWeightBody_denoteWith (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (V : History) (k : ℕ) (ρ : List ℝ)
    (hρ : PriorEnv (weight active (fun j => (α j).denote V)) k ρ) :
    (featureWeightBody active α k).denoteWith ρ V =
      weight active (fun j => (α j).denote V) k := by
  rw [featureWeightBody, weight]
  simp only [EF.denoteWith, Rat.cast_one, Rat.cast_neg, neg_mul, one_mul]
  have hsum :
      (sumFeatures (List.ofFn (fun i : Fin k =>
        if active i k then EF.mul (EF.var (k - 1 - i)) (α i) else EF.const 0))).denoteWith ρ V =
      ∑ i : Fin k, if active i k then
        weight active (fun j => (α j).denote V) i * (α i).denote V else 0 := by
    rw [sumFeatures_denoteWith]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hop : active i k = true
    · simp only [hop, if_true, EF.denoteWith]
      rw [hρ i]
      rw [hαc i ρ V]
    · simp [hop]
  rw [hsum]
  ring

/-- The shared straight-line expression denotes exactly the same adaptive coefficient as
the semantic recurrence. -/
lemma sharedFeatureWeight_denote (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (V : History) (n : ℕ) :
    (sharedFeatureWeight active α n).denote V =
      weight active (fun i => (α i).denote V) n :=
  sharedOf_denote _ _ V (featureWeightBody_denoteWith active α hαc V) n

private lemma featureWeightBody_rank_le (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i) (k : ℕ) :
    (featureWeightBody active α k).rank ≤ k := by
  rw [featureWeightBody]
  simp only [EF.rank]
  apply Nat.max_le.mpr
  constructor
  · omega
  · apply Nat.max_le.mpr
    constructor
    · omega
    · apply sumFeatures_rank_le
      intro e he
      simp only [List.mem_ofFn] at he
      obtain ⟨i, rfl⟩ := he
      split
      · exact Nat.max_le.mpr ⟨by simp, (hα i).trans (Nat.le_of_lt i.isLt)⟩
      · simp

lemma sharedFeatureWeight_rank_le (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i) (n : ℕ) :
    (sharedFeatureWeight active α n).rank ≤ n :=
  sharedOf_rank_le _ (featureWeightBody_rank_le active α hα) n

/-! ### Budgeted component sums

Both budgets — the Boolean closing schedule and the continuous occupancy one — bundle a
trader family by scaling each launched component by a coefficient family `β` subject to
`(β i).rank ≤ i`. The construction and its four specifications — segment emission, value,
magnitude, net worth — are proved once, at an arbitrary such family, and each budget
instantiates them. -/

/-- The day-`n` sum of every component launched by day `n`, each scaled by its own
coefficient `β i`. The rank hypothesis is what makes `β i` legal to use on day `n ≥ i`. -/
def scaledFamilyTrader (Ts : ℕ → Trader) (β : ℕ → EF)
    (hβ : ∀ i, (β i).rank ≤ i) : Trader where
  strat n := Strategy.join (List.ofFn (fun i : Fin (n + 1) =>
    Strategy.scaleBy (β i) ((hβ i).trans (by omega)) ((Ts i).strat n)))

/-- A uniformly emitted coefficient family bundles a structured emulatable family into a
uniformly emitted trader. The proof performs two variable-width concatenations: trades
within one component, then all components launched by day `n`. -/
lemma scaledFamilyTrader_polySeg (Ts : ℕ → Trader) (β : ℕ → EF)
    (hβ : ∀ i, (β i).rank ≤ i)
    (hβseg : BigSpliceStream (fun i => (β i).serialize))
    (hTs : PolyTradeEmulatable Ts) :
    BigSpliceStream (fun n =>
      serializeTrades ((scaledFamilyTrader Ts β hβ).strat n).trades) := by
  obtain ⟨ccount, hcount⟩ := hTs.tradeCount_poly
  -- Input to an individual scaled trade is `q = ⟨⟨n,k⟩,j⟩`.
  have hday := PolyFueled.left.comp PolyFueled.left
  have hmember := PolyFueled.right.comp PolyFueled.left
  have htradeNo := PolyFueled.right
  have hcanonical := (hmember.pair hday).pair htradeNo
  have hcoefficient := hβseg.comp hmember
  have hcoeff := hTs.coefficient_poly.comp hcanonical
  have hscaled := BigSpliceStream.serialize_mul hcoefficient hcoeff
  have hframe := BigSpliceStream.tradeSlot hTs.sentence_poly hcanonical
  have hone : BigSpliceStream (fun q =>
      let n := q.unpair.1.unpair.1
      let k := q.unpair.1.unpair.2
      let j := q.unpair.2
      let z := Nat.pair (Nat.pair k n) j
      serializeTrades [(EF.mul (β k) (hTs.coefficient z), hTs.sentence z)]) := by
    refine BigSpliceStream.of_eq (hscaled.append hframe) ?_
    intro q
    simp [serializeTrades]
  have hcountReindexed := hcount.comp (PolyFueled.right.pair PolyFueled.left)
  have hcomponent := BigSpliceStream.concatVar hone hcountReindexed
  have hall := BigSpliceStream.concatVar hcomponent PolyFueled.id.succ_comp
  refine BigSpliceStream.of_eq hall ?_
  intro n
  rw [scaledFamilyTrader]
  simp only [Strategy.join, Strategy.scaleBy]
  rw [serializeTrades_flatMap]
  simp only [List.ofFn_eq_map]
  rw [← List.map_coe_finRange_eq_range]
  rw [List.flatMap_map, List.flatMap_map]
  apply List.flatMap_congr
  intro k hk
  simp only [Nat.unpair_pair]
  rw [hTs.trades_eq, List.map_map, serializeTrades_map_singleton]
  simp only [Function.comp_apply]

/-- Day-`n` value is the finite `β`-weighted sum of component values. -/
lemma scaledFamilyTrader_value (Ts : ℕ → Trader) (β : ℕ → EF)
    (hβ : ∀ i, (β i).rank ≤ i) (V : History) (w : Valuation) (n : ℕ) :
    ((scaledFamilyTrader Ts β hβ).strat n).value V w =
      ∑ i : Fin (n + 1), (β i).denote V * ((Ts i).strat n).value V w := by
  rw [scaledFamilyTrader, Strategy.join_value]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  exact Finset.sum_congr rfl (fun i _ => Strategy.scaleBy_value _ _ _ _ _)

/-- Day-`n` magnitude is the finite `|β|`-weighted sum of component magnitudes. -/
lemma scaledFamilyTrader_magnitude (Ts : ℕ → Trader) (β : ℕ → EF)
    (hβ : ∀ i, (β i).rank ≤ i) (V : History) (n : ℕ) :
    ((scaledFamilyTrader Ts β hβ).strat n).magnitude V =
      ∑ i : Fin (n + 1), |(β i).denote V| * ((Ts i).strat n).magnitude V := by
  rw [scaledFamilyTrader, Strategy.join_magnitude]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  exact Finset.sum_congr rfl (fun i _ => Strategy.scaleBy_magnitude _ _ _ _)

/-- Net worth of the bundle is the finite `β`-weighted sum of component net worths.
`LaunchGated` — components trade nothing before their launch day — is what turns the
triangular daily bundle into this rectangular component view. -/
lemma scaledFamilyTrader_netWorth (Ts : ℕ → Trader) (β : ℕ → EF)
    (hβ : ∀ i, (β i).rank ≤ i) (hTs : LaunchGated Ts) (V : History) (v : PCWorld) :
    ∀ n, (scaledFamilyTrader Ts β hβ).netWorth V v n =
      ∑ i : Fin (n + 1), (β i).denote V * (Ts i).netWorth V v n := by
  intro n
  induction n with
  | zero =>
      simpa [Trader.netWorth] using scaledFamilyTrader_value Ts β hβ V v.payout 0
  | succ n ih =>
      have hday := scaledFamilyTrader_value Ts β hβ V v.payout (n + 1)
      have hlaunch := hTs.netWorth_launch V v (n + 1)
      rw [Trader.netWorth_succ, hday, ih]
      conv_lhs =>
        rhs
        rw [Fin.sum_univ_castSucc]
      conv_rhs => rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [hlaunch]
      simp_rw [Trader.netWorth_succ, mul_add]
      rw [Finset.sum_add_distrib]
      ring

/-- Budgeted component sum using the shared straight-line `β` representation. -/
def sharedBudgetedTrader (Ts : ℕ → Trader) (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i) : Trader :=
  scaledFamilyTrader Ts (sharedFeatureWeight active α)
    (sharedFeatureWeight_rank_le active α hα)

/-- The shared budget construction preserves uniform segment emission for a structured
emulatable family. -/
lemma sharedBudgetedTrader_polySeg (Ts : ℕ → Trader)
    (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hαrank : ∀ i, (α i).rank ≤ i)
    (hαseg : BigSpliceStream (fun i => (α i).serialize))
    (hactive : PolyActiveSchedule active)
    (hTs : PolyTradeEmulatable Ts) :
    BigSpliceStream (fun n =>
      serializeTrades ((sharedBudgetedTrader Ts active α hαrank).strat n).trades) :=
  scaledFamilyTrader_polySeg Ts _ _
    (sharedFeatureWeight_polySeg active α hαseg hactive) hTs

lemma sharedBudgetedTrader_ec (Ts : ℕ → Trader)
    (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hαrank : ∀ i, (α i).rank ≤ i)
    (hαseg : BigSpliceStream (fun i => (α i).serialize))
    (hactive : PolyActiveSchedule active)
    (hTs : PolyTradeEmulatable Ts) :
    EfficientlyComputable (sharedBudgetedTrader Ts active α hαrank) :=
  BigSpliceStream.ec _
    (sharedBudgetedTrader_polySeg Ts active α hαrank hαseg hactive hTs)

lemma sharedBudgetedTrader_value (Ts : ℕ → Trader) (active : ℕ → ℕ → Bool)
    (α : ℕ → EF) (hα : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (V : History) (w : Valuation) (n : ℕ) :
    ((sharedBudgetedTrader Ts active α hα).strat n).value V w =
      ∑ i : Fin (n + 1), weight active (fun k => (α k).denote V) i *
        ((Ts i).strat n).value V w := by
  rw [sharedBudgetedTrader, scaledFamilyTrader_value]
  exact Finset.sum_congr rfl
    (fun i _ => by rw [sharedFeatureWeight_denote active α hαc])

lemma sharedBudgetedTrader_magnitude (Ts : ℕ → Trader) (active : ℕ → ℕ → Bool)
    (α : ℕ → EF) (hα : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (V : History) (n : ℕ) :
    ((sharedBudgetedTrader Ts active α hα).strat n).magnitude V =
      ∑ i : Fin (n + 1), |weight active (fun k => (α k).denote V) i| *
        ((Ts i).strat n).magnitude V := by
  rw [sharedBudgetedTrader, scaledFamilyTrader_magnitude]
  exact Finset.sum_congr rfl
    (fun i _ => by rw [sharedFeatureWeight_denote active α hαc])

/-- Net worth of the shared sum is the finite weighted sum of component net worths. -/
lemma sharedBudgetedTrader_netWorth (Ts : ℕ → Trader)
    (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hαrank : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (hTs : LaunchGated Ts) (V : History) (v : PCWorld) :
    ∀ n,
      (sharedBudgetedTrader Ts active α hαrank).netWorth V v n =
        ∑ i : Fin (n + 1), weight active (fun k => (α k).denote V) i *
          (Ts i).netWorth V v n := by
  intro n
  rw [sharedBudgetedTrader, scaledFamilyTrader_netWorth Ts _ _ hTs]
  exact Finset.sum_congr rfl
    (fun i _ => by rw [sharedFeatureWeight_denote active α hαc])

/-! ### Closing schedules and the unit-capital invariant -/

/-- The budget recurrence in the form the invariant proofs use. -/
lemma weight_eq (active : ℕ → ℕ → Bool) (α : ℕ → ℝ) (n : ℕ) :
    weight active α n = 1 - outstanding active α (weight active α) n := by
  rw [weight]
  rfl

/-- Once a component closes it stays closed.  Equivalently, openness at a later day
implies openness at every earlier day after the component was introduced. -/
def ClosingSchedule (active : ℕ → ℕ → Bool) : Prop :=
  ∀ i n, active i (n + 1) = true → active i n = true

/-- The central budgeting invariant.  If component magnitudes lie in `[0,1]` and open
positions only disappear, every adaptive coefficient is in `[0,1]`, and the capital
tied up after adding the current component is at most one unit. -/
lemma weight_nonneg_and_postAllocation_le
    (active : ℕ → ℕ → Bool) (α : ℕ → ℝ)
    (hclose : ClosingSchedule active)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1) :
    ∀ n, 0 ≤ weight active α n ∧
      outstanding active α (weight active α) n + weight active α n * α n ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hw0 : ∀ i < n, 0 ≤ weight active α i := fun i hi => (ih i hi).1
      have hterm0 : ∀ i : Fin n,
          0 ≤ (if active i n then weight active α i * α i else 0) := by
        intro i
        split <;> simp_all only [le_refl]
        exact mul_nonneg (hw0 i i.isLt) (hα0 i)
      have hout0 : 0 ≤ outstanding active α (weight active α) n := by
        exact Finset.sum_nonneg (fun i hi => hterm0 i)
      have hout1 : outstanding active α (weight active α) n ≤ 1 := by
        cases n with
        | zero => simp [outstanding]
        | succ k =>
            have hprev := (ih k (by omega)).2
            rw [outstanding, Fin.sum_univ_castSucc]
            have hsum :
                (∑ i : Fin k, if active (Fin.castSucc i) (k + 1) then
                    weight active α (Fin.castSucc i) * α (Fin.castSucc i) else 0) ≤
                  outstanding active α (weight active α) k := by
              rw [outstanding]
              apply Finset.sum_le_sum
              intro i hi
              by_cases hop : active i (k + 1) = true
              · have hop' : active i k = true := hclose i k hop
                simp [hop, hop']
              · simp [hop]
                by_cases hop' : active i k = true
                · simp [hop', mul_nonneg (hw0 i (by omega)) (hα0 i)]
                · simp [hop']
            have hlast :
                (if active (Fin.last k) (k + 1) then
                    weight active α (Fin.last k) * α (Fin.last k) else 0) ≤
                  weight active α k * α k := by
              simp only [Fin.val_last]
              split
              · exact le_rfl
              · exact mul_nonneg (hw0 k (by omega)) (hα0 k)
            exact le_trans (add_le_add hsum hlast) hprev
      have hw : weight active α n = 1 - outstanding active α (weight active α) n :=
        weight_eq active α n
      constructor
      · rw [hw]
        linarith
      · rw [hw]
        nlinarith [hα0 n, hα1 n]

lemma weight_nonneg
    (active : ℕ → ℕ → Bool) (α : ℕ → ℝ)
    (hclose : ClosingSchedule active)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1) (n : ℕ) :
    0 ≤ weight active α n :=
  (weight_nonneg_and_postAllocation_le active α hclose hα0 hα1 n).1

lemma weight_le_one
    (active : ℕ → ℕ → Bool) (α : ℕ → ℝ)
    (hclose : ClosingSchedule active)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1) (n : ℕ) :
    weight active α n ≤ 1 := by
  rw [weight_eq]
  exact sub_le_self _ (Finset.sum_nonneg (fun i hi => by
    split
    · exact mul_nonneg (weight_nonneg active α hclose hα0 hα1 i) (hα0 i)
    · exact le_rfl))

/-! ## The adaptive budget: continuous occupancy

The affine gradual-sale construction exposes its still-risky fraction as an expressible
feature in `[0,1]`.  The following semantic budget is the fractional analogue of the
Boolean `active` scheduler above.  It needs no externally computed maturity day. -/

/-- Capital tied up by earlier components, weighted by their current fractional
occupancy. -/
noncomputable def fractionalOutstanding (occupancy : ℕ → ℕ → ℝ)
    (α β : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin n, β i * α i * occupancy i n

/-- Adaptive launch weight with fractional rather than Boolean capital occupancy. -/
noncomputable def fractionalWeight (occupancy : ℕ → ℕ → ℝ)
    (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - ∑ i : Fin n, fractionalWeight occupancy α i * α i * occupancy i n
termination_by n
decreasing_by exact i.isLt

lemma fractionalWeight_eq (occupancy : ℕ → ℕ → ℝ) (α : ℕ → ℝ)
    (n : ℕ) :
    fractionalWeight occupancy α n =
      1 - fractionalOutstanding occupancy α (fractionalWeight occupancy α) n := by
  rw [fractionalWeight, fractionalOutstanding]

/-- Fractional capital occupancy stays in `[0,1]` and can only decrease with time. -/
structure DecreasingOccupancy (occupancy : ℕ → ℕ → ℝ) : Prop where
  nonneg : ∀ i n, 0 ≤ occupancy i n
  le_one : ∀ i n, occupancy i n ≤ 1
  antitone : ∀ i n, occupancy i (n + 1) ≤ occupancy i n

/-- Fractional occupancy preserves the unit-capital invariant: every launch weight is
nonnegative, and outstanding capital plus the new allocation is at most one. -/
lemma fractionalWeight_nonneg_and_postAllocation_le
    (occupancy : ℕ → ℕ → ℝ) (α : ℕ → ℝ)
    (hocc : DecreasingOccupancy occupancy)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1) :
    ∀ n, 0 ≤ fractionalWeight occupancy α n ∧
      fractionalOutstanding occupancy α (fractionalWeight occupancy α) n +
        fractionalWeight occupancy α n * α n ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hw0 : ∀ i < n, 0 ≤ fractionalWeight occupancy α i :=
        fun i hi => (ih i hi).1
      have hout0 : 0 ≤
          fractionalOutstanding occupancy α (fractionalWeight occupancy α) n := by
        rw [fractionalOutstanding]
        exact Finset.sum_nonneg (fun i _ =>
          mul_nonneg (mul_nonneg (hw0 i i.isLt) (hα0 i)) (hocc.nonneg i n))
      have hout1 :
          fractionalOutstanding occupancy α (fractionalWeight occupancy α) n ≤ 1 := by
        cases n with
        | zero => simp [fractionalOutstanding]
        | succ k =>
            have hprev := (ih k (by omega)).2
            rw [fractionalOutstanding, Fin.sum_univ_castSucc]
            have hprior :
                (∑ i : Fin k, fractionalWeight occupancy α (Fin.castSucc i) *
                    α (Fin.castSucc i) * occupancy (Fin.castSucc i) (k + 1)) ≤
                  fractionalOutstanding occupancy α
                    (fractionalWeight occupancy α) k := by
              rw [fractionalOutstanding]
              apply Finset.sum_le_sum
              intro i hi
              exact mul_le_mul_of_nonneg_left (hocc.antitone i k)
                (mul_nonneg (hw0 i (by omega)) (hα0 i))
            have hlast :
                fractionalWeight occupancy α (Fin.last k) * α (Fin.last k) *
                    occupancy (Fin.last k) (k + 1) ≤
                  fractionalWeight occupancy α k * α k := by
              simp only [Fin.val_last]
              exact mul_le_of_le_one_right
                (mul_nonneg (hw0 k (by omega)) (hα0 k)) (hocc.le_one k (k + 1))
            exact le_trans (add_le_add hprior hlast) hprev
      have hw := fractionalWeight_eq occupancy α n
      constructor
      · rw [hw]
        linarith
      · rw [hw]
        nlinarith [hα0 n, hα1 n]

lemma fractionalWeight_nonneg
    (occupancy : ℕ → ℕ → ℝ) (α : ℕ → ℝ)
    (hocc : DecreasingOccupancy occupancy)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1) (n : ℕ) :
    0 ≤ fractionalWeight occupancy α n :=
  (fractionalWeight_nonneg_and_postAllocation_le occupancy α hocc hα0 hα1 n).1

lemma fractionalWeight_le_one
    (occupancy : ℕ → ℕ → ℝ) (α : ℕ → ℝ)
    (hocc : DecreasingOccupancy occupancy)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1) (n : ℕ) :
    fractionalWeight occupancy α n ≤ 1 := by
  rw [fractionalWeight_eq]
  exact sub_le_self _ (Finset.sum_nonneg (fun i _ =>
    mul_nonneg
      (mul_nonneg (fractionalWeight_nonneg occupancy α hocc hα0 hα1 i) (hα0 i))
      (hocc.nonneg i n)))

/-- Any collection of launches through day `n` which is still fully occupied at day
`n` (apart from the current launch itself) has total allocation at most one.  This is
the finite-set form of the fractional capital invariant used by patient selectors. -/
lemma fractional_allocations_finset_le_one
    (occupancy : ℕ → ℕ → ℝ) (α : ℕ → ℝ)
    (hocc : DecreasingOccupancy occupancy)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    (s : Finset ℕ) (n : ℕ)
    (hs : ∀ i ∈ s, i ≤ n)
    (hfull : ∀ i ∈ s, i < n → occupancy i n = 1) :
    ∑ i ∈ s, fractionalWeight occupancy α i * α i ≤ 1 := by
  classical
  let β : ℕ → ℝ := fractionalWeight occupancy α
  let q : ℕ → ℝ := fun i ↦ β i * α i
  let r : ℕ → ℝ := fun i ↦ if i = n then q i else q i * occupancy i n
  have hβ0 : ∀ i, 0 ≤ β i := fun i ↦
    fractionalWeight_nonneg occupancy α hocc hα0 hα1 i
  have hsubset : s ⊆ Finset.range (n + 1) := by
    intro i hi
    simp only [Finset.mem_range]
    have hil := hs i hi
    omega
  have hqr : ∀ i ∈ s, q i = r i := by
    intro i hi
    by_cases hin : i = n
    · simp [r, hin]
    · have hil : i < n := by
        have hle := hs i hi
        omega
      simp [r, hin, hfull i hi hil]
  have hr0 : ∀ i ∈ Finset.range (n + 1), i ∉ s → 0 ≤ r i := by
    intro i _ _
    by_cases hin : i = n
    · change 0 ≤ if i = n then β i * α i else
          β i * α i * occupancy i n
      rw [if_pos hin]
      exact mul_nonneg (hβ0 i) (hα0 i)
    · change 0 ≤ if i = n then β i * α i else
          β i * α i * occupancy i n
      rw [if_neg hin]
      exact mul_nonneg (mul_nonneg (hβ0 i) (hα0 i)) (hocc.nonneg i n)
  have hbudget :=
    (fractionalWeight_nonneg_and_postAllocation_le occupancy α hocc hα0 hα1 n).2
  calc
    ∑ i ∈ s, fractionalWeight occupancy α i * α i = ∑ i ∈ s, q i := by
      rfl
    _ = ∑ i ∈ s, r i := Finset.sum_congr rfl hqr
    _ ≤ ∑ i ∈ Finset.range (n + 1), r i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset hr0
    _ = fractionalOutstanding occupancy α (fractionalWeight occupancy α) n +
        fractionalWeight occupancy α n * α n := by
      rw [Finset.sum_range_succ]
      simp only [r, q, β, if_pos]
      congr 1
      rw [fractionalOutstanding, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      have hin : (i : ℕ) ≠ n := by omega
      simp [hin]
    _ ≤ 1 := hbudget

/-! ### Shared expressible-feature representation -/

/-- The fractional-weight recurrence body in an environment
`[βₖ₋₁, …, β₀]`. -/
def fractionalWeightBody (occupancy : ℕ → ℕ → EF) (α : ℕ → EF) (k : ℕ) : EF :=
  EF.add (EF.const 1) (EF.mul (EF.const (-1))
    (sumFeatures (List.ofFn (fun i : Fin k =>
      EF.mul (EF.mul (EF.var (k - 1 - i)) (α i)) (occupancy i k)))))

/-- Shared straight-line chain for consecutive fractional launch weights. -/
def fractionalSharedWeights (occupancy : ℕ → ℕ → EF) (α : ℕ → EF)
    (k : ℕ) : ℕ → EF :=
  letChain (fractionalWeightBody occupancy α) k

/-- Polynomial-sharing feature for the day-`n` fractional budget coefficient. Spelled
through `fractionalSharedWeights` for the same reason as `sharedFeatureWeight`. -/
def fractionalSharedFeatureWeight (occupancy : ℕ → ℕ → EF)
    (α : ℕ → EF) (n : ℕ) : EF :=
  fractionalSharedWeights occupancy α 0 (n + 1)

/-- The postfix stream of a fractional chain, in the same shape as
`sharedWeights_serialize`. -/
lemma fractionalSharedWeights_serialize (occupancy : ℕ → ℕ → EF)
    (α : ℕ → EF) (k count : ℕ) :
    (fractionalSharedWeights occupancy α k count).serialize =
      (List.range' k count).flatMap
          (fun j => (fractionalWeightBody occupancy α j).serialize) ++
        (EF.var 0).serialize ++ List.replicate count 8 :=
  letChain_serialize _ k count

/-- Uniform segment emitter for the fractional recurrence bodies. The occupancy stream is
indexed by `⟨day, component⟩`. -/
lemma fractionalWeightBody_polySeg (occupancy : ℕ → ℕ → EF)
    (α : ℕ → EF) (hα : BigSpliceStream (fun i => (α i).serialize))
    (hocc : BigSpliceStream (fun z =>
      (occupancy z.unpair.2 z.unpair.1).serialize)) :
    BigSpliceStream (fun k => (fractionalWeightBody occupancy α k).serialize) := by
  let term : ℕ → EF := fun z =>
    EF.mul (EF.mul (EF.var (z.unpair.1 - 1 - z.unpair.2)) (α z.unpair.2))
      (occupancy z.unpair.2 z.unpair.1)
  have idxPF := subc_polyFueled.comp
    ((predc_polyFueled.comp PolyFueled.left).pair PolyFueled.right)
  have idxPF' := idxPF.of_eq (f' := fun z => z.unpair.1 - 1 - z.unpair.2)
    (fun z => by simp [Nat.pred_eq_sub_one])
  have hvar : BigSpliceStream
      (fun z => (EF.var (z.unpair.1 - 1 - z.unpair.2)).serialize) :=
    BigSpliceStream.serialize_var idxPF'
  have hαright : BigSpliceStream (fun z => (α z.unpair.2).serialize) :=
    hα.comp PolyFueled.right
  have hterm : BigSpliceStream (fun z => (term z).serialize) :=
    BigSpliceStream.serialize_mul (BigSpliceStream.serialize_mul hvar hαright) hocc
  have hterms : BigSpliceStream (fun k =>
      (List.range k).flatMap (fun i => (term (Nat.pair k i)).serialize)) :=
    BigSpliceStream.concatVar hterm PolyFueled.id
  have hzero : BigSpliceStream (fun _ => (EF.const 0).serialize) :=
    BigSpliceStream.serialize_const 0
  have haddTags : BigSpliceStream (fun k => List.replicate k 2) :=
    BigSpliceStream.repeatTag 2 (by norm_num) PolyFueled.id
  have hsumRaw := (hterms.append hzero).append haddTags
  have hsum : BigSpliceStream (fun k =>
      (sumFeatures (List.ofFn (fun i : Fin k => term (Nat.pair k i)))).serialize) := by
    refine BigSpliceStream.of_eq hsumRaw ?_
    intro k
    rw [serialize_sumFeatures]
    simp only [List.length_ofFn]
    congr 2
    rw [← List.map_coe_finRange_eq_range]
    rw [List.flatMap_map]
    simp only [List.ofFn_eq_map, List.flatMap_map]
  have hone : BigSpliceStream (fun _ => (EF.const 1).serialize) :=
    BigSpliceStream.serialize_const 1
  have hnegone : BigSpliceStream (fun _ => (EF.const (-1)).serialize) :=
    BigSpliceStream.serialize_const (-1)
  have hbody := BigSpliceStream.serialize_add hone
    (BigSpliceStream.serialize_mul hnegone hsum)
  refine BigSpliceStream.of_eq hbody ?_
  intro k
  simp only [fractionalWeightBody, term]
  congr 4
  congr 1
  funext i
  simp

/-- Uniform polynomial-time emission of the day-`n` fractional budget coefficient. -/
lemma fractionalSharedFeatureWeight_polySeg (occupancy : ℕ → ℕ → EF)
    (α : ℕ → EF) (hα : BigSpliceStream (fun i => (α i).serialize))
    (hocc : BigSpliceStream (fun z =>
      (occupancy z.unpair.2 z.unpair.1).serialize)) :
    BigSpliceStream (fun n => (fractionalSharedFeatureWeight occupancy α n).serialize) :=
  sharedOf_polySeg _ (fractionalWeightBody_polySeg occupancy α hα hocc)

private lemma fractionalWeightBody_denoteWith
    (occupancy : ℕ → ℕ → EF) (α : ℕ → EF)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (hoccc : ∀ i n ρ V, (occupancy i n).denoteWith ρ V = (occupancy i n).denote V)
    (V : History) (k : ℕ) (ρ : List ℝ)
    (hρ : PriorEnv (fractionalWeight (fun j n => (occupancy j n).denote V)
      (fun j => (α j).denote V)) k ρ) :
    (fractionalWeightBody occupancy α k).denoteWith ρ V =
      fractionalWeight (fun i n => (occupancy i n).denote V)
        (fun i => (α i).denote V) k := by
  rw [fractionalWeightBody, fractionalWeight]
  simp only [EF.denoteWith, Rat.cast_one, Rat.cast_neg, neg_mul, one_mul]
  rw [sumFeatures_denoteWith]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, EF.denoteWith]
  apply congrArg (fun x : ℝ => 1 - x)
  apply Finset.sum_congr rfl
  intro i hi
  rw [hρ i, hαc i ρ V, hoccc i k ρ V]

/-- The shared fractional chain denotes the fractional recurrence. -/
lemma fractionalSharedFeatureWeight_denote
    (occupancy : ℕ → ℕ → EF) (α : ℕ → EF)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (hoccc : ∀ i n ρ V, (occupancy i n).denoteWith ρ V = (occupancy i n).denote V)
    (V : History) (n : ℕ) :
    (fractionalSharedFeatureWeight occupancy α n).denote V =
      fractionalWeight (fun i n => (occupancy i n).denote V)
        (fun i => (α i).denote V) n :=
  sharedOf_denote _ _ V
    (fractionalWeightBody_denoteWith occupancy α hαc hoccc V) n

/-- A shared fractional-weight feature is closed with respect to any surrounding `letE`
environment whenever its attempted-weight and occupancy inputs are closed.  The internal
straight-line bindings shadow and discharge every variable used by the recurrence. -/
lemma fractionalSharedFeatureWeight_closed
    (occupancy : ℕ → ℕ → EF) (α : ℕ → EF)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (hoccc : ∀ i n ρ V, (occupancy i n).denoteWith ρ V =
      (occupancy i n).denote V)
    (n : ℕ) (ρ : List ℝ) (V : History) :
    (fractionalSharedFeatureWeight occupancy α n).denoteWith ρ V =
      (fractionalSharedFeatureWeight occupancy α n).denote V :=
  sharedOf_closed _ _ V
    (fractionalWeightBody_denoteWith occupancy α hαc hoccc V) n ρ

private lemma fractionalWeightBody_rank_le
    (occupancy : ℕ → ℕ → EF) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i)
    (hocc : ∀ i n, i ≤ n → (occupancy i n).rank ≤ n) (k : ℕ) :
    (fractionalWeightBody occupancy α k).rank ≤ k := by
  rw [fractionalWeightBody]
  simp only [EF.rank]
  apply Nat.max_le.mpr
  constructor
  · omega
  · apply Nat.max_le.mpr
    constructor
    · omega
    · apply sumFeatures_rank_le
      intro e he
      simp only [List.mem_ofFn] at he
      obtain ⟨i, rfl⟩ := he
      exact Nat.max_le.mpr ⟨Nat.max_le.mpr
        ⟨by simp, (hα i).trans (Nat.le_of_lt i.isLt)⟩,
        hocc i k (Nat.le_of_lt i.isLt)⟩

/-- The day-`n` fractional chain is legal on day `n`. -/
lemma fractionalSharedFeatureWeight_rank_le
    (occupancy : ℕ → ℕ → EF) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i)
    (hocc : ∀ i n, i ≤ n → (occupancy i n).rank ≤ n) (n : ℕ) :
    (fractionalSharedFeatureWeight occupancy α n).rank ≤ n :=
  sharedOf_rank_le _ (fractionalWeightBody_rank_le occupancy α hα hocc) n

/-! ### Fractional budgeted component sums -/

/-- Component-family sum scaled by shared fractional launch weights. -/
def fractionalBudgetedTrader (Ts : ℕ → Trader) (occupancy : ℕ → ℕ → EF)
    (α : ℕ → EF) (hα : ∀ i, (α i).rank ≤ i)
    (hocc : ∀ i n, i ≤ n → (occupancy i n).rank ≤ n) : Trader :=
  scaledFamilyTrader Ts (fractionalSharedFeatureWeight occupancy α)
    (fractionalSharedFeatureWeight_rank_le occupancy α hα hocc)

lemma fractionalBudgetedTrader_polySeg (Ts : ℕ → Trader)
    (occupancy : ℕ → ℕ → EF) (α : ℕ → EF)
    (hαrank : ∀ i, (α i).rank ≤ i)
    (hoccRank : ∀ i n, i ≤ n → (occupancy i n).rank ≤ n)
    (hαseg : BigSpliceStream (fun i => (α i).serialize))
    (hoccSeg : BigSpliceStream (fun z =>
      (occupancy z.unpair.2 z.unpair.1).serialize))
    (hTs : PolyTradeEmulatable Ts) :
    BigSpliceStream (fun n => serializeTrades
      ((fractionalBudgetedTrader Ts occupancy α hαrank hoccRank).strat n).trades) :=
  scaledFamilyTrader_polySeg Ts _ _
    (fractionalSharedFeatureWeight_polySeg occupancy α hαseg hoccSeg) hTs

lemma fractionalBudgetedTrader_ec (Ts : ℕ → Trader)
    (occupancy : ℕ → ℕ → EF) (α : ℕ → EF)
    (hαrank : ∀ i, (α i).rank ≤ i)
    (hoccRank : ∀ i n, i ≤ n → (occupancy i n).rank ≤ n)
    (hαseg : BigSpliceStream (fun i => (α i).serialize))
    (hoccSeg : BigSpliceStream (fun z =>
      (occupancy z.unpair.2 z.unpair.1).serialize))
    (hTs : PolyTradeEmulatable Ts) :
    EfficientlyComputable
      (fractionalBudgetedTrader Ts occupancy α hαrank hoccRank) :=
  BigSpliceStream.ec _
    (fractionalBudgetedTrader_polySeg Ts occupancy α hαrank hoccRank
      hαseg hoccSeg hTs)

lemma fractionalBudgetedTrader_value (Ts : ℕ → Trader)
    (occupancy : ℕ → ℕ → EF) (α : ℕ → EF)
    (hαrank : ∀ i, (α i).rank ≤ i)
    (hoccRank : ∀ i n, i ≤ n → (occupancy i n).rank ≤ n)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (hoccc : ∀ i n ρ V, (occupancy i n).denoteWith ρ V = (occupancy i n).denote V)
    (V : History) (w : Valuation) (n : ℕ) :
    ((fractionalBudgetedTrader Ts occupancy α hαrank hoccRank).strat n).value V w =
      ∑ i : Fin (n + 1),
        fractionalWeight (fun j d => (occupancy j d).denote V)
            (fun j => (α j).denote V) i *
          ((Ts i).strat n).value V w := by
  rw [fractionalBudgetedTrader, scaledFamilyTrader_value]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [fractionalSharedFeatureWeight_denote occupancy α hαc hoccc])

lemma fractionalBudgetedTrader_netWorth (Ts : ℕ → Trader)
    (occupancy : ℕ → ℕ → EF) (α : ℕ → EF)
    (hαrank : ∀ i, (α i).rank ≤ i)
    (hoccRank : ∀ i n, i ≤ n → (occupancy i n).rank ≤ n)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (hoccc : ∀ i n ρ V, (occupancy i n).denoteWith ρ V = (occupancy i n).denote V)
    (hTs : LaunchGated Ts) (V : History) (v : PCWorld) : ∀ n,
    (fractionalBudgetedTrader Ts occupancy α hαrank hoccRank).netWorth V v n =
      ∑ i : Fin (n + 1),
        fractionalWeight (fun j d => (occupancy j d).denote V)
            (fun j => (α j).denote V) i * (Ts i).netWorth V v n := by
  intro n
  rw [fractionalBudgetedTrader, scaledFamilyTrader_netWorth Ts _ _ hTs]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [fractionalSharedFeatureWeight_denote occupancy α hαc hoccc])

/-! ### Recycling the fractional budget -/

/-- Finite tails of a nonnegative summable real series are uniformly small. Both recycling
arguments — fractional and Boolean — use this to bound the still-outstanding capital. -/
lemma summable_tail_Ico_lt {f : ℕ → ℝ} (hf0 : ∀ i, 0 ≤ f i)
    (hf : Summable f) {r : ℝ} (hr : 0 < r) :
    ∃ K, ∀ n, K ≤ n → ∑ i ∈ Finset.Ico K n, f i < r := by
  have htend := hf.hasSum.tendsto_sum_nat
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp htend r hr
  refine ⟨K, fun n hKn => ?_⟩
  have hnear := hK K le_rfl
  rw [Real.dist_eq, abs_lt] at hnear
  have hnle : (∑ i ∈ Finset.range n, f i) ≤ ∑' i, f i :=
    hf.sum_le_tsum _ (fun i _ => hf0 i)
  have hsplit := Finset.sum_range_add_sum_Ico f hKn
  linarith

/-- Capital allocated at the launch of fractional component `i`. -/
noncomputable def fractionalAllocation (occupancy : ℕ → ℕ → ℝ)
    (α : ℕ → ℝ) (i : ℕ) : ℝ :=
  fractionalWeight occupancy α i * α i

/-- Total capital launched through component `n`. -/
noncomputable def fractionalAllocationPrefix (occupancy : ℕ → ℕ → ℝ)
    (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), fractionalAllocation occupancy α i

/-- Capital launched through component `n` that is still occupied on day `n`. -/
noncomputable def fractionalActiveAllocation
    (occupancy : ℕ → ℕ → ℝ) (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), fractionalAllocation occupancy α i * occupancy i n

lemma fractionalAllocation_nonneg (occupancy : ℕ → ℕ → ℝ)
    (α : ℕ → ℝ) (hocc : DecreasingOccupancy occupancy)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1) (i : ℕ) :
    0 ≤ fractionalAllocation occupancy α i :=
  mul_nonneg (fractionalWeight_nonneg occupancy α hocc hα0 hα1 i) (hα0 i)

lemma fractionalActiveAllocation_le_one (occupancy : ℕ → ℕ → ℝ)
    (α : ℕ → ℝ) (hocc : DecreasingOccupancy occupancy)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1) (n : ℕ) :
    fractionalActiveAllocation occupancy α n ≤ 1 := by
  rw [fractionalActiveAllocation, Fin.sum_univ_castSucc]
  have hbudget :=
    (fractionalWeight_nonneg_and_postAllocation_le occupancy α hocc hα0 hα1 n).2
  have hprior :
      (∑ i : Fin n, fractionalAllocation occupancy α (Fin.castSucc i) *
          occupancy (Fin.castSucc i) n) =
        fractionalOutstanding occupancy α (fractionalWeight occupancy α) n := by
    rw [fractionalOutstanding]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [fractionalAllocation, Fin.val_castSucc]
  rw [hprior]
  simp only [Fin.val_last]
  have hlast : fractionalAllocation occupancy α n * occupancy n n ≤
      fractionalWeight occupancy α n * α n := by
    exact mul_le_of_le_one_right
      (fractionalAllocation_nonneg occupancy α hocc hα0 hα1 n) (hocc.le_one n n)
  exact le_trans (add_le_add (le_refl _) hlast) hbudget

/-- If every nonzero fractional position eventually reaches zero, frequent positive launch
sizes force unbounded cumulative allocation. Zero-size positions need no closing day, and
no polynomial closing-day oracle is involved. -/
lemma fractionalAllocationPrefix_not_bddAbove_of_frequently
    (occupancy : ℕ → ℕ → ℝ) (α : ℕ → ℝ)
    (hocc : DecreasingOccupancy occupancy)
    (hzero : ∀ i, α i = 0 ∨ ∃ N, ∀ n, N ≤ n → occupancy i n = 0)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδα : ∃ᶠ i in Filter.atTop, δ ≤ α i) :
    ¬ BddAbove (Set.range (fractionalAllocationPrefix occupancy α)) := by
  have ha0 : ∀ i, 0 ≤ fractionalAllocation occupancy α i :=
    fractionalAllocation_nonneg occupancy α hocc hα0 hα1
  intro hbdd
  obtain ⟨B, hB⟩ := hbdd
  have hsumRange : ∀ n,
      (∑ i ∈ Finset.range n, fractionalAllocation occupancy α i) ≤ B := by
    intro n
    cases n with
    | zero =>
        have hbase := hB (show fractionalAllocationPrefix occupancy α 0 ∈
          Set.range (fractionalAllocationPrefix occupancy α) from ⟨0, rfl⟩)
        have hbase0 : 0 ≤ fractionalAllocationPrefix occupancy α 0 :=
          Finset.sum_nonneg (fun i _ => ha0 i)
        simp only [Finset.sum_range_zero]
        linarith
    | succ n =>
        have hn := hB (show fractionalAllocationPrefix occupancy α n ∈
          Set.range (fractionalAllocationPrefix occupancy α) from ⟨n, rfl⟩)
        rw [fractionalAllocationPrefix, Fin.sum_univ_eq_sum_range] at hn
        exact hn
  have haSum : Summable (fractionalAllocation occupancy α) :=
    summable_of_sum_range_le ha0 hsumRange
  let r : ℝ := min (1 / 2 : ℝ) (δ / 2)
  have hr : 0 < r := lt_min (by norm_num) (half_pos hδ)
  obtain ⟨K, htail⟩ := summable_tail_Ico_lt ha0 haSum hr
  have hweightedZero : ∀ i, ∃ N, ∀ n, N ≤ n →
      fractionalWeight occupancy α i * α i * occupancy i n = 0 := by
    intro i
    rcases hzero i with hα | ⟨N, hN⟩
    · exact ⟨0, fun n _ => by simp [hα]⟩
    · exact ⟨N, fun n hn => by rw [hN n hn, mul_zero]⟩
  choose close hclose using hweightedZero
  let N := K + ∑ i ∈ Finset.range K, close i
  have hKN : K ≤ N := by simp [N]
  obtain ⟨J, hNJ, hαJ⟩ := (Filter.frequently_atTop.mp hδα) N
  have hKJ : K ≤ J := hKN.trans hNJ
  have hcloseBefore : ∀ i < K, close i ≤ N := by
    intro i hi
    have himem : i ∈ Finset.range K := Finset.mem_range.mpr hi
    have hile : close i ≤ ∑ j ∈ Finset.range K, close j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (close j)) himem
    dsimp [N]
    omega
  have hout : fractionalOutstanding occupancy α
      (fractionalWeight occupancy α) J < r := by
    have houtLe : fractionalOutstanding occupancy α
        (fractionalWeight occupancy α) J ≤
        ∑ i ∈ Finset.Ico K J, fractionalAllocation occupancy α i := by
      rw [fractionalOutstanding]
      calc
        (∑ i : Fin J, fractionalWeight occupancy α i * α i * occupancy i J) ≤
            ∑ i : Fin J, if K ≤ i then fractionalAllocation occupancy α i else 0 := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hKi : K ≤ i
          · simp only [hKi, if_true, fractionalAllocation]
            exact mul_le_of_le_one_right
              (mul_nonneg
                (fractionalWeight_nonneg occupancy α hocc hα0 hα1 i) (hα0 i))
              (hocc.le_one i J)
          · have hiK : (i : ℕ) < K := by omega
            have hz := hclose i J ((hcloseBefore i hiK).trans hNJ)
            simp [hKi, hz]
        _ = ∑ i ∈ Finset.Ico K J, fractionalAllocation occupancy α i := by
          rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
            if K ≤ i then fractionalAllocation occupancy α i else 0)]
          rw [← Finset.sum_filter]
          congr 1
          ext i
          simp [Finset.mem_Ico]
          omega
    exact lt_of_le_of_lt houtLe (htail J hKJ)
  have hβhalf : (1 / 2 : ℝ) < fractionalWeight occupancy α J := by
    rw [fractionalWeight_eq]
    have hrhalf : r ≤ (1 / 2 : ℝ) := min_le_left _ _
    linarith
  have haJlower : δ / 2 < fractionalAllocation occupancy α J := by
    dsimp [fractionalAllocation]
    calc
      δ / 2 = (1 / 2 : ℝ) * δ := by ring
      _ < fractionalWeight occupancy α J * δ :=
        mul_lt_mul_of_pos_right hβhalf hδ
      _ ≤ fractionalWeight occupancy α J * α J :=
        mul_le_mul_of_nonneg_left hαJ
          (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_of_lt hβhalf))
  have htailNext := htail (J + 1) (by omega)
  have haJtail : fractionalAllocation occupancy α J ≤
      ∑ i ∈ Finset.Ico K (J + 1), fractionalAllocation occupancy α i := by
    apply Finset.single_le_sum (fun i _ => ha0 i)
    simp [Finset.mem_Ico, hKJ]
  have hrδ : r ≤ δ / 2 := min_le_right _ _
  linarith

/-- Continuous repeatable-return theorem. Each component earns `ε` on the released
fraction and risks at most the still-occupied fraction. Fractional budgeting then gives
bounded downside and, when launch sizes recur and occupancies vanish, unbounded upside. -/
lemma fractionalBudgetedTrader_exploits
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (occupancy : ℕ → ℕ → EF) (α : ℕ → EF)
    (hαrank : ∀ i, (α i).rank ≤ i)
    (hoccRank : ∀ i n, i ≤ n → (occupancy i n).rank ≤ n)
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hoccc : ∀ i n ρ W, (occupancy i n).denoteWith ρ W = (occupancy i n).denote W)
    (hocc : DecreasingOccupancy (fun i n => (occupancy i n).denote V))
    (hzero : ∀ i, (α i).denote V = 0 ∨
      ∃ N, ∀ n, N ≤ n → (occupancy i n).denote V = 0)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hfreq : ∃ᶠ i in Filter.atTop, δ ≤ (α i).denote V)
    (hTs : LaunchGated Ts)
    (hworth : ∀ i n, i ≤ n → ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      ε * (α i).denote V * (1 - (occupancy i n).denote V) -
          (α i).denote V * (occupancy i n).denote V ≤
        (Ts i).netWorth V v n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fractionalBudgetedTrader Ts occupancy α hαrank hoccRank).Exploits V DP := by
  let O : ℕ → ℕ → ℝ := fun i n => (occupancy i n).denote V
  let M : ℕ → ℝ := fun i => (α i).denote V
  let Tr := fractionalBudgetedTrader Ts occupancy α hαrank hoccRank
  have hunbounded : ¬ BddAbove (Set.range (fractionalAllocationPrefix O M)) :=
    fractionalAllocationPrefix_not_bddAbove_of_frequently O M hocc hzero hα0 hα1 hδ hfreq
  have hlower : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      ε * fractionalAllocationPrefix O M n - (ε + 1) ≤ Tr.netWorth V v n := by
    intro n v hv
    have hβ0 : ∀ i, 0 ≤ fractionalWeight O M i :=
      fractionalWeight_nonneg O M hocc hα0 hα1
    have hpoint : ∀ i : Fin (n + 1),
        ε * fractionalAllocation O M i -
            (ε + 1) * (fractionalAllocation O M i * O i n) ≤
          fractionalWeight O M i * (Ts i).netWorth V v n := by
      intro i
      have hiworth := hworth i n (by omega) v hv
      have hscaled := mul_le_mul_of_nonneg_left hiworth (hβ0 i)
      calc
        ε * fractionalAllocation O M i -
              (ε + 1) * (fractionalAllocation O M i * O i n) =
            fractionalWeight O M i *
              (ε * M i * (1 - O i n) - M i * O i n) := by
                simp only [fractionalAllocation]
                ring
        _ ≤ fractionalWeight O M i * (Ts i).netWorth V v n := hscaled
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    have hcoarse :
        (∑ i : Fin (n + 1),
          (ε * fractionalAllocation O M i -
            (ε + 1) * (fractionalAllocation O M i * O i n))) =
          ε * fractionalAllocationPrefix O M n -
            (ε + 1) * fractionalActiveAllocation O M n := by
      simp only [Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rfl
    rw [hcoarse] at hsum
    have hnet := fractionalBudgetedTrader_netWorth Ts occupancy α hαrank hoccRank
      hαc hoccc hTs V v n
    change Tr.netWorth V v n = _ at hnet
    rw [hnet]
    have hactive := fractionalActiveAllocation_le_one O M hocc hα0 hα1 n
    nlinarith
  constructor
  · refine ⟨-(ε + 1), ?_⟩
    rintro x ⟨n, v, hv, rfl⟩
    have hlo := hlower n v hv
    have hpref0 : 0 ≤ fractionalAllocationPrefix O M n :=
      Finset.sum_nonneg (fun i _ => fractionalAllocation_nonneg O M hocc hα0 hα1 i)
    nlinarith
  · intro hbdd
    obtain ⟨B, hB⟩ := hbdd
    obtain ⟨A, ⟨n, rfl⟩, hA⟩ := not_bddAbove_iff.mp hunbounded ((B + ε + 1) / ε)
    obtain ⟨v, hv⟩ := hworld n
    have hlo := hlower n v hv
    have hmem : Tr.netWorth V v n ∈ Tr.plausibleAssessments V DP := ⟨n, v, hv, rfl⟩
    have hup := hB hmem
    have hεne : ε ≠ 0 := ne_of_gt hε
    field_simp [hεne] at hA
    nlinarith

/-- A logical inductor admits no uniformly emulatable continuous-return family with
eventually vanishing occupancies unless its launch-risk sizes converge to zero. -/
lemma noFractionalRepeatableReturn
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor V DP]
    (ε : ℝ) (hε : 0 < ε) (occupancy : ℕ → ℕ → EF) (α : ℕ → EF)
    (hαrank : ∀ i, (α i).rank ≤ i)
    (hoccRank : ∀ i n, i ≤ n → (occupancy i n).rank ≤ n)
    (hαseg : BigSpliceStream (fun i => (α i).serialize))
    (hoccSeg : BigSpliceStream (fun z =>
      (occupancy z.unpair.2 z.unpair.1).serialize))
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hoccc : ∀ i n ρ W, (occupancy i n).denoteWith ρ W = (occupancy i n).denote W)
    (hocc : DecreasingOccupancy (fun i n => (occupancy i n).denote V))
    (hzero : ∀ i, (α i).denote V = 0 ∨
      ∃ N, ∀ n, N ≤ n → (occupancy i n).denote V = 0)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    (hTs : PolyTradeEmulatable Ts)
    (hworth : ∀ i n, i ≤ n → ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      ε * (α i).denote V * (1 - (occupancy i n).denote V) -
          (α i).denote V * (occupancy i n).denote V ≤
        (Ts i).netWorth V v n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun i => (α i).denote V) 0 := by
  refine Metric.tendsto_atTop.mpr (fun δ hδ => ?_)
  have hnotfreq : ¬ ∃ᶠ i in Filter.atTop, δ ≤ (α i).denote V := by
    intro hfreq
    have hec := fractionalBudgetedTrader_ec Ts occupancy α hαrank hoccRank
      hαseg hoccSeg hTs
    have hex := fractionalBudgetedTrader_exploits Ts V DP ε hε occupancy α
      hαrank hoccRank hαc hoccc hocc hzero hα0 hα1 hδ hfreq hTs.launchGated
      hworth hworld
    exact hLI.noExploit _ hec hex
  rw [Filter.not_frequently] at hnotfreq
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnotfreq
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hα0 n)]
  exact lt_of_not_ge (hN n hn)

/-! ## Recycling the Boolean unit budget -/

/-- Capital allocated to component `i`. -/
noncomputable def allocation (active : ℕ → ℕ → Bool) (α : ℕ → ℝ) (i : ℕ) : ℝ :=
  weight active α i * α i

/-- Total allocation launched through component `n`. -/
noncomputable def allocationPrefix (active : ℕ → ℕ → Bool) (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), allocation active α i

/-- Allocation still open on day `n`, including the newly launched component when active. -/
noncomputable def activeAllocation (active : ℕ → ℕ → Bool) (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), if active i n then allocation active α i else 0

lemma allocation_nonneg (active : ℕ → ℕ → Bool) (α : ℕ → ℝ)
    (hclose : ClosingSchedule active) (hα0 : ∀ i, 0 ≤ α i)
    (hα1 : ∀ i, α i ≤ 1) (i : ℕ) :
    0 ≤ allocation active α i :=
  mul_nonneg (weight_nonneg active α hclose hα0 hα1 i) (hα0 i)

/-- At most one unit of allocation is active at a time. -/
lemma activeAllocation_le_one (active : ℕ → ℕ → Bool) (α : ℕ → ℝ)
    (hclose : ClosingSchedule active) (hα0 : ∀ i, 0 ≤ α i)
    (hα1 : ∀ i, α i ≤ 1) (n : ℕ) :
    activeAllocation active α n ≤ 1 := by
  rw [activeAllocation, Fin.sum_univ_castSucc]
  have hbudget := (weight_nonneg_and_postAllocation_le active α hclose hα0 hα1 n).2
  have hprior :
      (∑ i : Fin n, if active (Fin.castSucc i) n then
          allocation active α (Fin.castSucc i) else 0) =
        outstanding active α (weight active α) n := by
    rw [outstanding]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Fin.val_castSucc, allocation]
  rw [hprior]
  simp only [Fin.val_last]
  by_cases h : active n n = true
  · simp [h, allocation] at hbudget ⊢
    exact hbudget
  · simp [h]
    exact le_trans (le_add_of_nonneg_right
      (allocation_nonneg active α hclose hα0 hα1 n)) hbudget

/-- If every component eventually closes and component magnitudes are frequently bounded
away from zero, the unit budget is recycled infinitely often: cumulative allocation is not
bounded above. This is the sparse-opportunity form needed by the paper's repeatable-ROI
lemma; components with zero magnitude on non-opportunity days are harmless. -/
lemma allocationPrefix_not_bddAbove_of_frequently
    (close : ℕ → ℕ) (active : ℕ → ℕ → Bool)
    (hclosing : ClosingSchedule active)
    (hclosed : ∀ i n, close i ≤ n → active i n = false) (α : ℕ → ℝ)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδα : ∃ᶠ i in Filter.atTop, δ ≤ α i) :
    ¬ BddAbove (Set.range (allocationPrefix active α)) := by
  have ha0 : ∀ i, 0 ≤ allocation active α i :=
    fun i => allocation_nonneg active α hclosing hα0 hα1 i
  intro hbdd
  obtain ⟨B, hB⟩ := hbdd
  have hsumRange : ∀ n, (∑ i ∈ Finset.range n, allocation active α i) ≤ B := by
    intro n
    cases n with
    | zero =>
        have hbase := hB (show allocationPrefix active α 0 ∈
          Set.range (allocationPrefix active α) from ⟨0, rfl⟩)
        have hbase0 : 0 ≤ allocationPrefix active α 0 :=
          Finset.sum_nonneg (fun i _ => ha0 i)
        simp only [Finset.sum_range_zero]
        linarith
    | succ n =>
        have hn := hB (show allocationPrefix active α n ∈
          Set.range (allocationPrefix active α) from ⟨n, rfl⟩)
        rw [allocationPrefix, Fin.sum_univ_eq_sum_range] at hn
        exact hn
  have haSum : Summable (allocation active α) :=
    summable_of_sum_range_le ha0 hsumRange
  let r : ℝ := min (1 / 2 : ℝ) (δ / 2)
  have hr : 0 < r := lt_min (by norm_num) (half_pos hδ)
  obtain ⟨K, htail⟩ := summable_tail_Ico_lt ha0 haSum hr
  let N := K + ∑ i ∈ Finset.range K, close i
  have hKN : K ≤ N := by simp [N]
  obtain ⟨J, hNJ, hαJ⟩ := (Filter.frequently_atTop.mp hδα) N
  have hKJ : K ≤ J := hKN.trans hNJ
  have hcloseBefore : ∀ i < K, close i ≤ N := by
    intro i hi
    have himem : i ∈ Finset.range K := Finset.mem_range.mpr hi
    have hile : close i ≤ ∑ j ∈ Finset.range K, close j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (close j)) himem
    dsimp [N]
    omega
  have hout : outstanding active α (weight active α) J < r := by
    have houtLe : outstanding active α (weight active α) J ≤
        ∑ i ∈ Finset.Ico K J, allocation active α i := by
      rw [outstanding]
      calc
        (∑ i : Fin J,
            if active i J then weight active α i * α i else 0) ≤
            ∑ i : Fin J,
              if K ≤ i then allocation active α i else 0 := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hop : active i J = true
          · have hKi : K ≤ i := by
              by_contra hnot
              have hiK : i < K := Nat.lt_of_not_ge hnot
              have hci := hcloseBefore i hiK
              have hf := hclosed i J (hci.trans hNJ)
              rw [hf] at hop
              contradiction
            simp [hop, hKi, allocation]
          · have hfalse := Bool.eq_false_of_not_eq_true hop
            simp [hfalse]
            split
            · exact ha0 i
            · exact le_rfl
        _ = ∑ i ∈ Finset.Ico K J, allocation active α i := by
          rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
            if K ≤ i then allocation active α i else 0)]
          rw [← Finset.sum_filter]
          congr 1
          ext i
          simp [Finset.mem_Ico]
          omega
    exact lt_of_le_of_lt houtLe (htail J hKJ)
  have hβhalf : (1 / 2 : ℝ) < weight active α J := by
    rw [weight_eq]
    have hrhalf : r ≤ (1 / 2 : ℝ) := min_le_left _ _
    linarith
  have haJlower : δ / 2 < allocation active α J := by
    dsimp [allocation]
    calc
      δ / 2 = (1 / 2 : ℝ) * δ := by ring
      _ < weight active α J * δ :=
        mul_lt_mul_of_pos_right hβhalf hδ
      _ ≤ weight active α J * α J :=
        mul_le_mul_of_nonneg_left hαJ
          (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_of_lt hβhalf))
  have htailNext := htail (J + 1) (by omega)
  have haJtail : allocation active α J ≤
      ∑ i ∈ Finset.Ico K (J + 1), allocation active α i := by
    apply Finset.single_le_sum (fun i _ => ha0 i)
    simp [Finset.mem_Ico, hKJ]
  have hrδ : r ≤ δ / 2 := min_le_right _ _
  linarith

/-- Uniformly positive magnitudes are the immediate special case of sparse recycling. -/
lemma allocationPrefix_not_bddAbove (close : ℕ → ℕ) (active : ℕ → ℕ → Bool)
    (hclosing : ClosingSchedule active)
    (hclosed : ∀ i n, close i ≤ n → active i n = false) (α : ℕ → ℝ)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδα : ∀ i, δ ≤ α i) :
    ¬ BddAbove (Set.range (allocationPrefix active α)) := by
  apply allocationPrefix_not_bddAbove_of_frequently close active hclosing hclosed α
    hα0 hα1 hδ
  exact Filter.frequently_atTop.mpr (fun N => ⟨N, le_rfl, hδα N⟩)

/-! ## From ROI maturity to a closing schedule -/

/-- Keep component `i` active strictly before its selected closing day. -/
def activeUntil (close : ℕ → ℕ) (i n : ℕ) : Bool := decide (n < close i)

lemma activeUntil_closing (close : ℕ → ℕ) : ClosingSchedule (activeUntil close) := by
  intro i n h
  simp [activeUntil] at h ⊢
  omega

/-- Every component of an `activeUntil` schedule does eventually close. The companion to
`activeUntil_closing`: together they say the schedule is a closing one whose positions all
terminate, which is what the recycling argument needs of any schedule a client builds. -/
lemma activeUntil_eventually_closed (close : ℕ → ℕ) (i : ℕ) :
    ∃ N, ∀ n, N ≤ n → activeUntil close i n = false := by
  refine ⟨close i, fun n hn => ?_⟩
  simp [activeUntil]
  omega

/-- After a maturity day, at most an `η` fraction of the component's total magnitude
remains to be traded. -/
lemma tail_magnitude_le_of_matured (Tr : Trader) (V : History)
    (DP : DeductiveProcess) (ε η : ℝ) (m n : ℕ)
    (hroi : HasROI Tr V DP ε) (hm : Tr.Matured V DP ε η m) (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico (m + 1) (n + 1), (Tr.strat i).magnitude V) ≤
      η * Tr.magnitude V := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i => (Tr.strat i).magnitude V) (show m + 1 ≤ n + 1 by omega)
  have hpartial := Tr.partial_magnitude_le V hroi.1 n
  have hmagnitude := hm.1
  linarith

/-- A matured positive-ROI component remains profitable at every later plausible day,
up to one additional `η` fraction for its post-maturity trading tail. -/
lemma netWorth_lower_of_matured (Tr : Trader) (V : History)
    (DP : DeductiveProcess) (ε η : ℝ) (m n : ℕ)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hroi : HasROI Tr V DP ε) (hm : Tr.Matured V DP ε η m)
    (hmn : m ≤ n) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    (ε - 2 * η) * Tr.magnitude V ≤ Tr.netWorth V v n := by
  have hsub : DP.D m ⊆ DP.D n := Finset.le_iff_subset.mp
    (monotone_nat_of_le_succ (fun k => Finset.le_iff_subset.mpr (DP.mono k)) hmn)
  have hvm : v.ConsistentWith (DP.D m) := fun φ hφ => hv φ (hsub hφ)
  have hprofit := hm.2 v hvm
  have htailMag := tail_magnitude_le_of_matured Tr V DP ε η m n hroi hm hmn
  have htailValue :
      -(∑ i ∈ Finset.Ico (m + 1) (n + 1), (Tr.strat i).magnitude V) ≤
        ∑ i ∈ Finset.Ico (m + 1) (n + 1),
          (Tr.strat i).value V v.payout := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i hi =>
      neg_le_of_abs_le (Strategy.abs_value_le_magnitude
        (Tr.strat i) V v.payout (fun φ => by
          by_cases hφ : v.Holds φ
          · exact Or.inr (by simp [PCWorld.payout, hφ])
          · exact Or.inl (by simp [PCWorld.payout, hφ])) (hP i)))
  have hsplitWorth := Finset.sum_range_add_sum_Ico
    (fun i => (Tr.strat i).value V v.payout) (show m + 1 ≤ n + 1 by omega)
  rw [← Trader.netWorth] at hsplitWorth
  rw [← Trader.netWorth] at hsplitWorth
  nlinarith [Trader.magnitude_nonneg Tr V]

/-- A selected closing day and tolerance for every component. -/
def MaturitySchedule (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (η : ℕ → ℝ) (close : ℕ → ℕ) : Prop :=
  ∀ i, (Ts i).Matured V DP ε (η i) (close i)

/-! ## Bounded verification of maturity

The paper does not require the first maturity day itself to be polynomially computable.
It requires each finite maturity claim to be checkable efficiently.  On budget day `k` we
therefore scan only the prefix `m ≤ k`; `polyFueled_boundedNone` turns that bounded scan into
the openness table consumed by the shared trader.
-/

/-- A uniformly polynomial, sound, eventually successful verifier for component maturity.
The checker input is `⟨component, day⟩`. -/
structure VerifiedMaturitySchedule (Ts : ℕ → Trader) (V : History)
    (DP : DeductiveProcess) (ε : ℝ) (η : ℕ → ℝ) where
  check : ℕ → ℕ → Bool
  check_poly : ∃ c, PolyFueled c
    (fun z => if check z.unpair.1 z.unpair.2 then 1 else 0)
  sound : ∀ i m, check i m = true → (Ts i).Matured V DP ε (η i) m
  complete : ∀ i, ∃ m, check i m = true

/-- A bounded verifier may finish checking an *earlier* maturity witness long after that
witness day.  This is the form used in the paper: on outer day `n`, a fixed computation
budget can certify some `m ≤ n`.  The witness uses half the requested tolerance so that
the post-`m` trading tail can be absorbed when it is promoted to maturity at day `n`.

Keeping this structure separate from `VerifiedMaturitySchedule` makes the computational
boundary explicit: concrete market/process code only has to enumerate finite historical
certificates; the semantic persistence argument below is generic. -/
structure HistoricalVerifiedMaturitySchedule (Ts : ℕ → Trader) (V : History)
    (DP : DeductiveProcess) (ε : ℝ) (η : ℕ → ℝ) where
  check : ℕ → ℕ → Bool
  check_poly : ∃ c, PolyFueled c
    (fun z => if check z.unpair.1 z.unpair.2 then 1 else 0)
  sound : ∀ i n, check i n = true →
    ∃ m ≤ n, (Ts i).Matured V DP ε (η i / 2) m
  complete : ∀ i, ∃ n, check i n = true

/-- Historical maturity persists to the day on which its bounded verification finishes.
The already-traded magnitude only increases, while `netWorth_lower_of_matured` charges at
most one further copy of the historical tolerance for the remaining trading tail. -/
def HistoricalVerifiedMaturitySchedule.toVerified
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : HistoricalVerifiedMaturitySchedule Ts V DP ε η)
    (hη0 : ∀ i, 0 ≤ η i)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hroi : ∀ i, HasROI (Ts i) V DP ε) :
    VerifiedMaturitySchedule Ts V DP ε η where
  check := h.check
  check_poly := h.check_poly
  complete := h.complete
  sound i n hcheck := by
    obtain ⟨m, hmn, hm⟩ := h.sound i n hcheck
    constructor
    · calc
        (1 - η i) * (Ts i).magnitude V ≤
            (1 - η i / 2) * (Ts i).magnitude V := by
              have hmag0 := Trader.magnitude_nonneg (Ts i) V
              nlinarith [hη0 i]
        _ ≤ ∑ d ∈ Finset.range (m + 1), ((Ts i).strat d).magnitude V := hm.1
        _ ≤ ∑ d ∈ Finset.range (n + 1), ((Ts i).strat d).magnitude V :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega))
            (fun d _ _ => Strategy.magnitude_nonneg ((Ts i).strat d) V)
    · intro v hv
      have hworth := netWorth_lower_of_matured (Ts i) V DP ε (η i / 2)
        m n hP (hroi i) hm hmn v hv
      simpa only [show 2 * (η i / 2) = η i by ring] using hworth

/-- The first verified maturity day.  This value may be selected noncomputably; queries of
the form “is it after day `k`?” are nevertheless polynomial by bounded verification. -/
noncomputable def VerifiedMaturitySchedule.close
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : VerifiedMaturitySchedule Ts V DP ε η) (i : ℕ) : ℕ :=
  Nat.find (h.complete i)

/-- The checker does succeed on the day `close` selects. -/
lemma VerifiedMaturitySchedule.check_close
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : VerifiedMaturitySchedule Ts V DP ε η) (i : ℕ) :
    h.check i (h.close i) = true :=
  Nat.find_spec (h.complete i)

/-- `close` is the *first* successful day: the checker fails strictly before it. -/
lemma VerifiedMaturitySchedule.check_false_of_lt_close
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : VerifiedMaturitySchedule Ts V DP ε η) {i m : ℕ} (hm : m < h.close i) :
    h.check i m = false := by
  apply Bool.eq_false_of_not_eq_true
  exact Nat.find_min (h.complete i) hm

/-- The bounded prefix scan "no day `m ≤ k` passes the checker" is exactly the openness
bit "component `i` is still open on day `k`". This is the step that makes the openness
table polynomial without asking for the closing day itself to be computable. -/
lemma VerifiedMaturitySchedule.boundedNone_eq_activeUntil
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : VerifiedMaturitySchedule Ts V DP ε η) (i k : ℕ) :
    boundedNone h.check i k = activeUntil h.close i k := by
  apply Bool.eq_iff_iff.mpr
  rw [boundedNone_eq_true_iff]
  simp only [activeUntil, decide_eq_true_eq]
  constructor
  · intro hall
    by_contra hnot
    have hle : h.close i ≤ k := by omega
    have := hall (h.close i) hle
    rw [h.check_close i] at this
    contradiction
  · intro hlt m hm
    exact h.check_false_of_lt_close (lt_of_le_of_lt hm hlt)

/-- The openness table the shared budget emitter consumes is polynomial. One of the two
facts the paper-facing bridge takes from a verified schedule. -/
lemma VerifiedMaturitySchedule.polyActive
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : VerifiedMaturitySchedule Ts V DP ε η) :
    PolyActiveSchedule (activeUntil h.close) := by
  obtain ⟨c, hc⟩ := polyFueled_boundedNone h.check h.check_poly
  have hswap := hc.comp (PolyFueled.right.pair PolyFueled.left)
  refine ⟨_, hswap.of_eq (fun z => ?_)⟩
  simp only [Nat.unpair_pair]
  rw [h.boundedNone_eq_activeUntil]

/-- Soundness at the selected day gives the semantic maturity schedule. The other fact the
paper-facing bridge takes from a verified schedule. -/
lemma VerifiedMaturitySchedule.maturity
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : VerifiedMaturitySchedule Ts V DP ε η) :
    MaturitySchedule Ts V DP ε η h.close :=
  fun i => h.sound i (h.close i) (h.check_close i)

/-! ## No repeatable ε-ROI (`lem:type3`) -/

/-- Quantitative lower bound for the repeatable-ROI bundle. Total launched allocation earns
`ε`; at most one unit remains active, and the summable maturity tolerances pay for every
closed component's post-maturity tail. -/
lemma sharedBudgetedTrader_netWorth_lower
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hemul : LaunchGated Ts)
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    ε * allocationPrefix (activeUntil close) (fun i => (α i).denote V) n -
        (ε + 1) - 2 * ∑' i, η i ≤
      (sharedBudgetedTrader Ts (activeUntil close) α hαrank).netWorth V v n := by
  let M : ℕ → ℝ := fun i => (α i).denote V
  let active := activeUntil close
  have hclosing : ClosingSchedule active := activeUntil_closing close
  have hβ0 : ∀ i, 0 ≤ weight active M i :=
    fun i => weight_nonneg active M hclosing hα0 hα1 i
  have halloc0 : ∀ i, 0 ≤ allocation active M i :=
    fun i => allocation_nonneg active M hclosing hα0 hα1 i
  have halloc1 : ∀ i, allocation active M i ≤ 1 := by
    intro i
    dsimp [allocation]
    calc
      weight active M i * M i ≤ 1 * M i :=
        mul_le_mul_of_nonneg_right
          (weight_le_one active M hclosing hα0 hα1 i) (hα0 i)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (hα1 i) zero_le_one
      _ = 1 := one_mul 1
  have hactive : activeAllocation active M n ≤ 1 :=
    activeAllocation_le_one active M hclosing hα0 hα1 n
  have htol : (∑ i : Fin (n + 1), η i * allocation active M i) ≤ ∑' i, η i := by
    calc
      (∑ i : Fin (n + 1), η i * allocation active M i) ≤
          ∑ i : Fin (n + 1), η i := Finset.sum_le_sum (fun i _ => by
            exact mul_le_of_le_one_right (hη0 i) (halloc1 i))
      _ = ∑ i ∈ Finset.range (n + 1), η i := by
        rw [Fin.sum_univ_eq_sum_range]
      _ ≤ ∑' i, η i := hηsum.sum_le_tsum _ (fun i _ => hη0 i)
  have hpoint : ∀ i : Fin (n + 1),
      ε * allocation active M i -
          (ε + 1) * (if active i n then allocation active M i else 0) -
          2 * (η i * allocation active M i) ≤
        weight active M i * (Ts i).netWorth V v n := by
    intro i
    by_cases hop : active i n = true
    · have hnw : -M i ≤ (Ts i).netWorth V v n := by
        change -(α i).denote V ≤ (Ts i).netWorth V v n
        rw [hmag i]
        exact neg_le_of_abs_le
          ((Ts i).abs_netWorth_le_magnitude V v hP (hroi i).1 n)
      have hscaled := mul_le_mul_of_nonneg_left hnw (hβ0 i)
      simp only [hop, if_true]
      have htol0 := mul_nonneg (hη0 i) (halloc0 i)
      calc
        ε * allocation active M i - (ε + 1) * allocation active M i -
              2 * (η i * allocation active M i) ≤ -allocation active M i := by
            nlinarith
        _ = weight active M i * -M i := by simp [allocation]
        _ ≤ weight active M i * (Ts i).netWorth V v n := hscaled
    · have hclosed : close i ≤ n := by
        change ¬activeUntil close i n = true at hop
        simp [activeUntil] at hop
        omega
      have hnw := netWorth_lower_of_matured (Ts i) V DP ε (η i) (close i) n
        hP (hroi i) (hmature i) hclosed v hv
      rw [← hmag i] at hnw
      have hscaled := mul_le_mul_of_nonneg_left hnw (hβ0 i)
      have hfalse : active i n = false := Bool.eq_false_of_not_eq_true hop
      simp only [hfalse]
      calc
        ε * allocation active M i - (ε + 1) * 0 -
              2 * (η i * allocation active M i) =
            weight active M i * ((ε - 2 * η i) * M i) := by
              simp [allocation]
              ring
        _ ≤ weight active M i * (Ts i).netWorth V v n := hscaled
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hcoarse :
      (∑ i : Fin (n + 1),
        (ε * allocation active M i -
          (ε + 1) * (if active i n then allocation active M i else 0) -
          2 * (η i * allocation active M i))) =
        ε * allocationPrefix active M n -
          (ε + 1) * activeAllocation active M n -
          2 * (∑ i : Fin (n + 1), η i * allocation active M i) := by
    simp only [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  rw [hcoarse] at hsum
  have hnet := sharedBudgetedTrader_netWorth Ts active α hαrank hαc hemul
  rw [hnet V v n]
  dsimp [active, M] at hsum ⊢
  nlinarith

/-- Semantic repeatable-ROI capstone once the allocation process is known to be unbounded.
The same quantitative estimate supplies both halves of exploitation: bounded downside from
the unit active budget and summable tails, and unbounded upside from recycled allocation. -/
lemma sharedBudgetedTrader_exploits_of_unboundedAllocation
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hemul : LaunchGated Ts)
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hunbounded : ¬ BddAbove (Set.range
      (allocationPrefix (activeUntil close) (fun i => (α i).denote V)))) :
    (sharedBudgetedTrader Ts (activeUntil close) α hαrank).Exploits V DP := by
  let Tr := sharedBudgetedTrader Ts (activeUntil close) α hαrank
  have hlower := sharedBudgetedTrader_netWorth_lower Ts V DP ε hε η close α
    hαrank hαc hmag hα0 hα1 hP hemul hroi hη0 hηsum hmature
  constructor
  · refine ⟨-(ε + 1) - 2 * ∑' i, η i, ?_⟩
    rintro x ⟨n, v, hv, rfl⟩
    have h := hlower n v hv
    have ha0 : 0 ≤ allocationPrefix (activeUntil close)
        (fun i => (α i).denote V) n := by
      exact Finset.sum_nonneg (fun i _ => allocation_nonneg
        (activeUntil close) (fun i => (α i).denote V)
        (activeUntil_closing close) hα0 hα1 i)
    nlinarith
  · intro hbdd
    obtain ⟨B, hB⟩ := hbdd
    obtain ⟨A, ⟨n, rfl⟩, hA⟩ := not_bddAbove_iff.mp hunbounded
      ((B + (ε + 1) + 2 * ∑' i, η i) / ε)
    obtain ⟨v, hv⟩ := hworld n
    have hlo := hlower n v hv
    have hmem : Tr.netWorth V v n ∈ Tr.plausibleAssessments V DP :=
      ⟨n, v, hv, rfl⟩
    have hup := hB hmem
    dsimp [Tr] at hlo hmem hup
    have hεne : ε ≠ 0 := ne_of_gt hε
    field_simp [hεne] at hA
    nlinarith

/-- Repeatable positive ROI is exploitable: eventual closure recycles the unit budget, and
a uniform positive magnitude floor makes cumulative allocation unbounded. -/
lemma sharedBudgetedTrader_exploits
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδα : ∀ i, δ ≤ (α i).denote V)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hemul : LaunchGated Ts)
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (sharedBudgetedTrader Ts (activeUntil close) α hαrank).Exploits V DP := by
  apply sharedBudgetedTrader_exploits_of_unboundedAllocation Ts V DP ε hε η close α
    hαrank hαc hmag hα0 hα1 hP hemul hroi hη0 hηsum hmature hworld
  exact allocationPrefix_not_bddAbove close (activeUntil close)
    (activeUntil_closing close) (fun i n hn => by
      simp [activeUntil]
      omega) (fun i => (α i).denote V) hα0 hα1 hδ hδα

/-- Sparse repeatable positive ROI is exploitable: it is enough that component magnitudes
are bounded away from zero infinitely often. Zero-magnitude components between profitable
opportunities consume no allocation and do not obstruct recycling. -/
lemma sharedBudgetedTrader_exploits_of_frequently
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hδα : ∃ᶠ i in Filter.atTop, δ ≤ (α i).denote V)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hemul : LaunchGated Ts)
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (sharedBudgetedTrader Ts (activeUntil close) α hαrank).Exploits V DP := by
  apply sharedBudgetedTrader_exploits_of_unboundedAllocation Ts V DP ε hε η close α
    hαrank hαc hmag hα0 hα1 hP hemul hroi hη0 hηsum hmature hworld
  exact allocationPrefix_not_bddAbove_of_frequently close (activeUntil close)
    (activeUntil_closing close) (fun i n hn => by
      simp [activeUntil]
      omega) (fun i => (α i).denote V) hα0 hα1 hδ hδα

/-- Full repeatable-ROI conclusion: the shared budget trader is both efficiently
computable and exploiting. -/
lemma repeatableROI
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαseg : BigSpliceStream (fun i => (α i).serialize))
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδα : ∀ i, δ ≤ (α i).denote V)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hTs : PolyTradeEmulatable Ts)
    (hactive : PolyActiveSchedule (activeUntil close))
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    EfficientlyComputable
        (sharedBudgetedTrader Ts (activeUntil close) α hαrank) ∧
      (sharedBudgetedTrader Ts (activeUntil close) α hαrank).Exploits V DP := by
  constructor
  · exact sharedBudgetedTrader_ec Ts (activeUntil close) α hαrank hαseg hactive hTs
  · exact sharedBudgetedTrader_exploits Ts V DP ε hε η close α hαrank hαc hmag
      hα0 hα1 hδ hδα hP hTs.launchGated hroi hη0 hηsum hmature hworld

/-- Sparse form of the full repeatable-ROI construction. -/
lemma repeatableROI_of_frequently
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαseg : BigSpliceStream (fun i => (α i).serialize))
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hδα : ∃ᶠ i in Filter.atTop, δ ≤ (α i).denote V)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hTs : PolyTradeEmulatable Ts)
    (hactive : PolyActiveSchedule (activeUntil close))
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    EfficientlyComputable
        (sharedBudgetedTrader Ts (activeUntil close) α hαrank) ∧
      (sharedBudgetedTrader Ts (activeUntil close) α hαrank).Exploits V DP := by
  constructor
  · exact sharedBudgetedTrader_ec Ts (activeUntil close) α hαrank hαseg hactive hTs
  · exact sharedBudgetedTrader_exploits_of_frequently Ts V DP ε hε η close α hαrank
      hαc hmag hα0 hα1 hδ hδα hP hTs.launchGated hroi hη0 hηsum hmature hworld

/-- No Repeatable ε-ROI, `lem:type3`: a logical inductor admits no efficiently emulatable
family of traders that all have ε-ROI for one fixed `ε > 0`, unless the `ℙ`-generable
magnitudes `αₖ = |T^k(ℙ)|` converge to zero.

Four hypotheses go beyond the printed lemma.

* `hα1 : (α i).denote V ≤ 1` — the paper derives this WLOG inside the proof (tex:3612), by
  dividing `T^k`'s trades by `max(1, αₖ)`. That renormalisation is not formalized, so the
  normalisation is a caller obligation.
* `hη0` / `hηsum : Summable η` — a summable family of maturity tolerances in place of the
  paper's single `ε/3`. This is a generalization: the constant family is summable only in
  the trivial case, so the Lean form covers strictly more schedules.
* `hworld` — some world is consistent with every stage of `DP`. `DeductiveProcess`
  (`Framework/Criterion.lean`) carries only `D` and `mono`, and fixes no consistency, so
  the clause the paper reads off its deductive process is carried explicitly.
* `hactive` / `hmature` / `close` — the polynomial openness table and the semantic maturity
  schedule. The paper builds both inside the proof from ε-ROI plus computability of `DP`
  (tex:3645-3650). `exists_maturitySchedule` shows the semantic half is free;
  `noRepeatableROI_of_verifiedMaturity` is the form clients should apply, discharging all
  three from one polynomial checker.

This result is deliberately carried without a `Paper node` line: `lem:type3` is listed in
`UNANNOTATED_PAPER_RESULTS` in `scripts/check_endpoint_coverage.py`, and is cited from this
module's header instead. Do not add the annotation — it would put the label under the
per-declaration axiom gate, which this statement does not answer to. -/
theorem noRepeatableROI
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor V DP]
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαseg : BigSpliceStream (fun i => (α i).serialize))
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hTs : PolyTradeEmulatable Ts)
    (hactive : PolyActiveSchedule (activeUntil close))
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun i => (α i).denote V) 0 := by
  refine Metric.tendsto_atTop.mpr (fun δ hδ => ?_)
  have hnotfreq : ¬ ∃ᶠ i in Filter.atTop, δ ≤ (α i).denote V := by
    intro hfreq
    obtain ⟨hec, hex⟩ := repeatableROI_of_frequently Ts V DP ε hε η close α hαrank
      hαseg hαc hmag hα0 hα1 hδ hfreq hP hTs hactive hroi hη0 hηsum hmature hworld
    exact hLI.noExploit _ hec hex
  rw [Filter.not_frequently] at hnotfreq
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnotfreq
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hα0 n)]
  exact lt_of_not_ge (hN n hn)

/-- Paper-facing verifier form of `noRepeatableROI`.  Callers provide only a polynomial,
sound, eventually successful maturity checker; the bounded-verification bridge constructs
the closing days, semantic maturity schedule, and polynomial openness table. -/
lemma noRepeatableROI_of_verifiedMaturity
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor V DP]
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαseg : BigSpliceStream (fun i => (α i).serialize))
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hTs : PolyTradeEmulatable Ts)
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hver : VerifiedMaturitySchedule Ts V DP ε η)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun i => (α i).denote V) 0 :=
  noRepeatableROI Ts V DP ε hε η hver.close α hαrank hαseg hαc hmag hα0 hα1
    hP hTs hver.polyActive hroi hη0 hηsum hver.maturity hworld

/-- A `MaturitySchedule` at a constant tolerance always exists: `HasROI.exists_matured`
supplies a maturity day for each component, and the schedule is their choice function.
This records which half of `noRepeatableROI`'s maturity input is a real obligation — only
the *polynomial verifier* of `VerifiedMaturitySchedule` is, the semantic schedule is free.
It is deliberately noncomputable; the paper-facing route builds closing days by bounded
verification instead. -/
lemma exists_maturitySchedule (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε η : ℝ) (hroi : ∀ i, HasROI (Ts i) V DP ε) (hη : 0 < η) :
    ∃ close, MaturitySchedule Ts V DP ε (fun _ => η) close :=
  ⟨fun i => Classical.choose ((hroi i).exists_matured hη),
    fun i => Classical.choose_spec ((hroi i).exists_matured hη)⟩

end ROIBudget

end LogicalInduction
