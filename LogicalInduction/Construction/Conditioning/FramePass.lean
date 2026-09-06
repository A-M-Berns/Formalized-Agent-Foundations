import LogicalInduction.Construction.Conditioning.PricePass

/-!
# The conditioning frame pass in the RPN symbol model

The second half of the RPN symbol-model rendering of `thm:scon`.
`Construction/Conditioning/PricePass.lean` builds the run-aware automaton `rpnCondStep` and
the price rewrite `rpnConditionRun` on it; this module adds the trader's *frame* — the two
locally gated legs that carry the conditioned trade — and assembles both passes into the
class-preservation endpoints.  Both halves are in namespace `RpnConditioning`.

## Budget exactness

The frame budget reads its trade count off the **contracted** stream, so the symbol-level
count `rpnTradeRuns` must be exact rather than an over-approximation:
`rpnTradeCountAt_eq_frameTradeCount`.  It is exact except on streams whose contraction is
unreadable, where both validated strategies are empty and the budget never reaches a trade.

## Structural acceptance

`rpnStructurallyAccepts` is the symbol-level gate the two-leg join tests, with
`rpnStructurallyAccepts_agree` the agreement with the contracted stream's own acceptance
scan, and the position-indexed scan below it the certified form.

## The frame pass

`rpnFrameEmit` splices the buffered trade run into the locally gated leg body,
`rpnFrameRun` / `rpnFrameOutput` stream it, and `rpnSafeSeparatedFrameOutput` joins the
two legs at a structurally accepting boundary.

## The poison algebra

`UnRpnStops`, `FrameAgree` and `FrameContract` are here; `Unreadable`, the poison predicate
they are stated against, is declared in the other half of the cut,
`Construction/Conditioning/PricePass.lean`.  Design fact, stated once
here: `unRpn` does **not** distribute over an append — a poisoned chunk in the left
factor stops the contraction before the right factor is read, so in general
`unRpn (A ++ B) ≠ unRpn A ++ unRpn B`.  The two-leg join therefore consumes the prefix
form `FrameContract` rather than the plain agreement `FrameAgree`, and `unRpn_split`
carries a base-mode hypothesis.  `FrameContract` is available exactly when the source
returns the run automaton to base mode — the condition the structural-acceptance gate
tests — together with the observation that a readable source excludes both legs' poison
branches, since a poisoned leg's token image fails to deserialize.

## The zero-aware price pass and the whole transduction

`rpnZeroAwareEmit` is the price emitter of the eventual translation, constant `1` on a
finite set of days; `rpnConditionOutput` and `rpnZeroAwareOutput` assemble price pass,
guard and frame legs into the class-agnostic conditioning transduction, whose strategy-level
cores are `strategyOfTokens_rpnConditionOutput` and `strategyOfTokens_rpnZeroAwareOutput`.

## Main results

All annotated `thm:scon`: the frame-pass master commutation
`frameJoint_unRpn_rpnFrameOutput`; budget exactness
`rpnTradeCountAt_eq_frameTradeCount`; gate agreement `rpnStructurallyAccepts_agree`; the
chunk-boundary split `unRpn_split`; and the two strategy-level cores above.

## Emission certificates

`rpnGuardedZeroAwareConditionRun_polySegStream`, `rpnFrameOutput_polySegStream` and
`rpnSafeSeparatedFrameOutput_polySegStream` carry a digit `PolySegStream` to a digit
`PolySegStream`, at the same digit metering as the price pass.

## Endpoints and consumers

`conditionedTranslation_preserves_ecRpn` and
`eventualConditionedTranslation_preserves_ecRpn` preserve the `dd:fuel` certificate
`EfficientlyComputable`; `Construction/Conditioning/Endpoints.lean` assembles them with
the machine transports into the criterion-level `lic_conditioned*` endpoints, which are
this module's only paper-facing consumers.  `LogicalInduction/API.lean` lists this
compiler as implementation, not interface.

This module renders `thm:scon` in the RPN symbol model; the provenance lines sit on the
declarations below, not on this header.
-/

namespace LogicalInduction

namespace RpnConditioning

open Nat.Partrec (Code)
open Nat.Partrec.Code
open ConditioningCompile

-- `Primrec`/`PolyFueled` elaboration over deep product types unfolds `Nat.sqrt`'s
-- well-founded definition during `whnf` (through `Nat.pair`/`unpair`) and loops; making
-- it locally irreducible stops that.
attribute [local irreducible] Nat.sqrt

/-! ## Budget exactness: symbol-level trade counting

The frame pass's budget is `frameBudget n (frameTradeCount …)`, and the digit model
reads that count off the **contracted** stream, so the symbol-level count must be
*exact*, not merely an over-approximation.  It is — except on streams whose
contraction is unreadable, where both validated strategies are empty and the budget
never reaches a trade.  The invariant is therefore the same disjunctive shape as
`FrameAgree`, and every poison branch discharges it immediately (a poisoned chunk
contracts to `[0, 0]` / `[6, 0]`, which are `Unreadable`). -/

/-- Trade-run exits along a stream, from a given control state. -/
def rpnTradeRuns (st : ℕ) : List ℕ → ℕ
  | [] => 0
  | t :: ts =>
      (if (rcMode st = 4 ∨ rcMode st = 7 ∨ rcMode st = 9) ∧
          rcMode (rpnCondStep st t) = 0
        then 1 else 0) + rpnTradeRuns (rpnCondStep st t) ts

/-- Completed trades along a contracted stream, from a given freeze mode. -/
def tokTradeRuns (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | t :: L => (if m = 4 then 1 else 0) + tokTradeRuns (freezeMode4Step m t) L

lemma rpnTradeRuns_append (st : ℕ) (xs ys : List ℕ) :
    rpnTradeRuns st (xs ++ ys) =
      rpnTradeRuns st xs + rpnTradeRuns (List.foldl rpnCondStep st xs) ys := by
  induction xs generalizing st with
  | nil => simp [rpnTradeRuns]
  | cons t ts ih => simp only [List.cons_append, rpnTradeRuns, ih, List.foldl_cons]
                    omega

lemma tokTradeRuns_append (m : ℕ) (xs ys : List ℕ) :
    tokTradeRuns m (xs ++ ys) =
      tokTradeRuns m xs + tokTradeRuns (List.foldl freezeMode4Step m xs) ys := by
  induction xs generalizing m with
  | nil => simp [tokTradeRuns]
  | cons t ts ih => simp only [List.cons_append, tokTradeRuns, ih, List.foldl_cons]
                    omega

/-- No exit fires along a stretch whose positions never complete a trade run. -/
lemma rpnTradeRuns_eq_zero (st : ℕ) (ts : List ℕ)
    (h : ∀ k < ts.length,
      ¬((rcMode (List.foldl rpnCondStep st (ts.take k)) = 4 ∨
          rcMode (List.foldl rpnCondStep st (ts.take k)) = 7 ∨
          rcMode (List.foldl rpnCondStep st (ts.take k)) = 9) ∧
        rcMode (List.foldl rpnCondStep st (ts.take (k + 1))) = 0)) :
    rpnTradeRuns st ts = 0 := by
  induction ts generalizing st with
  | nil => rfl
  | cons t ts ih =>
      have h0 := h 0 (by simp)
      simp only [List.take_zero, List.foldl_nil, List.take_succ_cons,
        List.foldl_cons] at h0
      rw [rpnTradeRuns, if_neg h0,
        ih (rpnCondStep st t) (fun k hk => by
          have := h (k + 1) (by simp only [List.length_cons]; omega)
          rwa [List.take_succ_cons, List.foldl_cons, List.take_succ_cons,
            List.foldl_cons] at this)]

/-- A complete price block contains no trade-run exit. -/
lemma rpnTradeRuns_price_block {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) :
    rpnTradeRuns (rcPack 1 1 0) b = 0 := by
  obtain ⟨-, hinv⟩ := foldl_rpnCondStep_price_block hb
  exact rpnTradeRuns_eq_zero _ _ fun k hk => by
    have := hinv k hk
    omega

/-- A complete trade block contains exactly one trade-run exit. -/
lemma rpnTradeRuns_trade_block {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) :
    rpnTradeRuns (rcPack 4 1 0) b = 1 := by
  obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_trade_block hb
  have hne : b ≠ [] := by
    intro hnil
    have := parseRpn_length_lt b.length b φ [] hb
    rw [hnil] at this
    simp at this
  rcases List.eq_nil_or_concat' b with rfl | ⟨init, last, rfl⟩
  · exact absurd rfl hne
  · have hlen : (init ++ [last]).length = init.length + 1 := by simp
    have hzero : rpnTradeRuns (rcPack 4 1 0) init = 0 :=
      rpnTradeRuns_eq_zero _ _ fun k hk => by
        have hk2 : k + 1 < (init ++ [last]).length := by rw [hlen]; omega
        have := hinv (k + 1) hk2
        rw [List.take_append_of_le_length (by omega)] at this
        omega
    have hmodeInit : rcMode (List.foldl rpnCondStep (rcPack 4 1 0) init) = 4 ∨
        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) init) = 7 ∨
        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) init) = 9 := by
      have := hinv init.length (by rw [hlen]; omega)
      rwa [List.take_append_of_le_length le_rfl, List.take_length] at this
    have hstepLast :
        rpnCondStep (List.foldl rpnCondStep (rcPack 4 1 0) init) last =
          rcPack 0 0 0 := by
      have hw := hwalk
      rw [List.foldl_append] at hw
      simpa using hw
    rw [rpnTradeRuns_append, hzero, rpnTradeRuns, rpnTradeRuns, hstepLast,
      if_pos ⟨hmodeInit, by simp [rcMode, rcPack]⟩]

/-- **Symbol-level trade counting is exact on readable streams**: the trade-run exits
of a stream and the completed trades of its contraction agree, unless the contraction
is unreadable (in which case the validated strategy — and hence the frame budget — is
empty on both sides).
Paper node: `thm:scon` -/
lemma tradeRuns_unRpn_agree : ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    rpnTradeRuns (rcPack 0 0 0) ts = tokTradeRuns 0 (unRpn ts) ∨
      Unreadable (unRpn ts) := by
  intro N
  induction N with
  | zero =>
      intro ts hts
      obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact Or.inl rfl
  | succ N ih =>
      intro ts hts
      match ts with
      | [] => exact Or.inl rfl
      | t :: rest =>
          simp only [List.length_cons] at hts
          by_cases ht0 : t = 0
          · subst ht0
            cases hp : parseRpn rest.length rest with
            | none =>
                refine Or.inr ?_
                rw [show unRpn (0 :: rest) = [0, 0] by
                  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl, hp]]
                exact unreadable_price_poison
            | some pr =>
                obtain ⟨φ, r1⟩ := pr
                obtain ⟨blk, heq, hblk⟩ := parseRpn_strip rest.length rest hp
                obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_price_block hblk
                match r1 with
                | [] =>
                    rw [List.append_nil] at heq
                    subst heq
                    refine Or.inl ?_
                    rw [show unRpn (0 :: rest) = [0, Encodable.encode φ] by
                      rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
                        hblk]]
                    rw [rpnTradeRuns, rpnCondStep_base_price,
                      if_neg (by simp [rcMode, rcPack]),
                      rpnTradeRuns_price_block hblk]
                    simp [tokTradeRuns, freezeMode4Step]
                | d :: r2 =>
                    subst heq
                    have hr2 : r2.length ≤ N := by
                      have hlt := parseRpn_length_lt _ _ _ _ hp
                      simp only [List.length_cons] at hlt
                      omega
                    have hcount : rpnTradeRuns (rcPack 0 0 0)
                        (0 :: (blk ++ d :: r2)) =
                        rpnTradeRuns (rcPack 0 0 0) r2 := by
                      rw [rpnTradeRuns, rpnCondStep_base_price,
                        if_neg (by simp [rcMode, rcPack]),
                        rpnTradeRuns_append, rpnTradeRuns_price_block hblk, hwalk,
                        rpnTradeRuns,
                        rpnCondStep_day blk.length d,
                        if_neg (by simp [rcMode, rcPack])]
                      omega
                    rw [unRpn_price_chunk_block hblk d r2, hcount]
                    have hchunk : List.foldl freezeMode4Step 0
                        [0, Encodable.encode φ, d] = 0 := by
                      simp [freezeMode4Step]
                    rcases ih r2 hr2 with hEq | hU
                    · refine Or.inl ?_
                      rw [show (0 :: Encodable.encode φ :: d :: unRpn r2) =
                        [0, Encodable.encode φ, d] ++ unRpn r2 from rfl,
                        tokTradeRuns_append, hchunk, hEq]
                      simp [tokTradeRuns, freezeMode4Step]
                    · refine Or.inr ?_
                      rw [show (0 :: Encodable.encode φ :: d :: unRpn r2) =
                        [0, Encodable.encode φ, d] ++ unRpn r2 from rfl]
                      exact hU.cons_chunk hchunk
          · by_cases ht6 : t = 6
            · subst ht6
              cases hp : parseRpn rest.length rest with
              | none =>
                  refine Or.inr ?_
                  rw [show unRpn (6 :: rest) = [6, 0] by
                    rw [unRpn, List.length_cons, unRpnTokens_cons,
                      if_neg (by norm_num), if_pos rfl, hp]]
                  exact unreadable_trade_poison
              | some pr =>
                  obtain ⟨φ, r1⟩ := pr
                  obtain ⟨blk, heq, hblk⟩ := parseRpn_strip rest.length rest hp
                  subst heq
                  obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_trade_block hblk
                  have hr1 : r1.length ≤ N := by
                    have hlt := parseRpn_length_lt _ _ _ _ hp
                    simp only [List.length_append] at hts
                    omega
                  have hcount : rpnTradeRuns (rcPack 0 0 0) (6 :: (blk ++ r1)) =
                      1 + rpnTradeRuns (rcPack 0 0 0) r1 := by
                    rw [rpnTradeRuns, rpnCondStep_base_trade,
                      if_neg (by simp [rcMode, rcPack]),
                      rpnTradeRuns_append, rpnTradeRuns_trade_block hblk, hwalk]
                    omega
                  rw [unRpn_trade_chunk_block hblk r1, hcount]
                  have hchunk : List.foldl freezeMode4Step 0
                      [6, Encodable.encode φ] = 0 := by
                    simp [freezeMode4Step]
                  rcases ih r1 hr1 with hEq | hU
                  · refine Or.inl ?_
                    rw [show (6 :: Encodable.encode φ :: unRpn r1) =
                      [6, Encodable.encode φ] ++ unRpn r1 from rfl,
                      tokTradeRuns_append, hchunk, hEq]
                    simp [tokTradeRuns, freezeMode4Step]
                  · refine Or.inr ?_
                    rw [show (6 :: Encodable.encode φ :: unRpn r1) =
                      [6, Encodable.encode φ] ++ unRpn r1 from rfl]
                    exact hU.cons_chunk hchunk
            · by_cases ht1 : t = 1 ∨ t = 7
              · match rest with
                | [] =>
                    refine Or.inl ?_
                    rcases ht1 with rfl | rfl <;>
                      simp [unRpn, unRpnTokens, rpnTradeRuns, tokTradeRuns,
                        rcMode, rcPack]
                | c :: r =>
                    have hr : r.length ≤ N := by
                      simp only [List.length_cons] at hts
                      omega
                    have hstep1 : rpnCondStep (rcPack 0 0 0) t =
                        rcPack (if t = 1 then 3 else 5) 0 0 := by
                      rcases ht1 with rfl | rfl <;>
                        simp [rpnCondStep_base]
                    have hcount : rpnTradeRuns (rcPack 0 0 0) (t :: c :: r) =
                        rpnTradeRuns (rcPack 0 0 0) r := by
                      rw [rpnTradeRuns, hstep1, if_neg (by
                        rcases ht1 with rfl | rfl <;> simp [rcMode, rcPack]),
                        rpnTradeRuns,
                        rpnCondStep_opaque (by split <;> simp) 0 0 c,
                        if_neg (by split <;> simp [rcMode, rcPack])]
                      omega
                    rw [unRpn_payload_chunk t c ht1 r, hcount]
                    have hchunk : List.foldl freezeMode4Step 0 [t, c] = 0 := by
                      rcases ht1 with rfl | rfl <;> simp [freezeMode4Step]
                    rcases ih r hr with hEq | hU
                    · refine Or.inl ?_
                      rw [show (t :: c :: unRpn r) = [t, c] ++ unRpn r from rfl,
                        tokTradeRuns_append, hchunk, hEq]
                      rcases ht1 with rfl | rfl <;>
                        simp [tokTradeRuns, freezeMode4Step]
                    · refine Or.inr ?_
                      rw [show (t :: c :: unRpn r) = [t, c] ++ unRpn r from rfl]
                      exact hU.cons_chunk hchunk
              · push_neg at ht1
                have hrest : rest.length ≤ N := by omega
                have hcount : rpnTradeRuns (rcPack 0 0 0) (t :: rest) =
                    rpnTradeRuns (rcPack 0 0 0) rest := by
                  rw [rpnTradeRuns,
                    rpnCondStep_base_other t ht0 ht1.1 ht6 ht1.2,
                    if_neg (by simp [rcMode, rcPack])]
                  omega
                rw [unRpn_single_chunk t ⟨ht0, ht1.1, ht6, ht1.2⟩ rest, hcount]
                have hchunk : List.foldl freezeMode4Step 0 [t] = 0 := by
                  simp [freezeMode4Step, ht0, ht1.1, ht6, ht1.2]
                rcases ih rest hrest with hEq | hU
                · refine Or.inl ?_
                  rw [show (t :: unRpn rest) = [t] ++ unRpn rest from rfl,
                    tokTradeRuns_append, hchunk, hEq]
                  simp [tokTradeRuns]
                · refine Or.inr ?_
                  rw [show (t :: unRpn rest) = [t] ++ unRpn rest from rfl]
                  exact hU.cons_chunk hchunk

/-- The position-indexed exit count is the list-level one over the position view. -/
lemma rpnTradeCountAt_eq_runs (tf : ℕ → ℕ) (n : ℕ) : ∀ J,
    rpnTradeCountAt tf n J = rpnTradeRuns (rcPack 0 0 0) (vpre tf n J)
  | 0 => rfl
  | J + 1 => by
      rw [rpnTradeCountAt, vpre_succ, rpnTradeRuns_append,
        rpnTradeCountAt_eq_runs tf n J,
        ← rpnCondControlAt_eq_foldl,
        rpnTradeRuns, rpnTradeRuns,
        show rpnCondStep (rpnCondControlAt tf n J) (tf (Nat.pair n J)) =
          rpnCondControlAt tf n (J + 1) from rfl]
      split <;> omega

/-- The token-model trade scan is the list-level count over the position view. -/
lemma tradeScanAt_eq_runs (tokenFn : ℕ → ℕ) (n : ℕ) : ∀ J,
    (tradeScanAt tokenFn n J).2 = tokTradeRuns 0 (vpre tokenFn n J)
  | 0 => rfl
  | J + 1 => by
      rw [tradeScanAt, vpre_succ, tokTradeRuns_append,
        tradeScanAt_eq_runs tokenFn n J, freezeControlNat_fst,
        show List.foldl freezeMode4Step 0 (vpre tokenFn n J) =
          freezeMode4 (vpre tokenFn n J) from rfl,
        tokTradeRuns, tokTradeRuns]
      split <;> simp [tradeScanAt_eq_runs tokenFn n J]

/-- **The frame budget is exact at symbol level**: the trade-run exit count of a
symbol-level stream equals the completed-trade count the digit-model frame pass reads
off the contraction — unless the contraction is unreadable, in which case both
validated strategies are empty and the budget is irrelevant.
Paper node: `thm:scon` -/
lemma rpnTradeCountAt_eq_frameTradeCount (tf tokenFn lenFn : ℕ → ℕ) (n : ℕ)
    (ts : List ℕ) (hts : vpre tf n ts.length = ts)
    (hL : vpre tokenFn n (lenFn n) = unRpn ts) :
    rpnTradeCountAt tf n ts.length = frameTradeCount tokenFn lenFn n ∨
      Unreadable (unRpn ts) := by
  rw [rpnTradeCountAt_eq_runs, hts, frameTradeCount, tradeScanNat]
  simp only [Nat.unpair_pair]
  rw [tradeScanAt_eq_runs, hL]
  exact tradeRuns_unRpn_agree ts.length ts le_rfl

/-! ## Symbol-level structural acceptance (the two-leg join gate)

The token model joins the two frame legs only at a structurally accepting boundary
(`safeSeparatedFrameTokenOutput` gates on `parserStructurallyAccepts`).  The symbol
side needs the same test computed from the run automaton: the trajectory must end in
base mode with an empty feature stack.  Depth is a pure function of the mode
trajectory — base-mode tokens act exactly as in the token model, the price-day and
payload slots push, a trade-run exit pops, and a sentence run is depth-neutral — so
its agreement with the contraction has the same disjunctive shape as
`tradeRuns_unRpn_agree`, and every poison branch discharges immediately. -/

/-- Depth update at one symbol position: base-mode tokens act as in the token model,
the price-day / payload slots push, and a trade-run exit pops. -/
def rpnDepthNext (st st' t d : ℕ) : ℕ :=
  if rcMode st = 0 then parserDepthNext 0 t d
  else if rcMode st = 2 then d + 1
  else if rcMode st = 3 then d + 1
  else if rcMode st = 5 then d + 1
  else if (rcMode st = 4 ∨ rcMode st = 7 ∨ rcMode st = 9) ∧ rcMode st' = 0
    then d.pred
  else d

/-- Symbol-level depth along a stream, from a control state and a starting depth. -/
def rpnDepthRuns (st : ℕ) : List ℕ → ℕ → ℕ
  | [], d => d
  | t :: ts, d =>
      rpnDepthRuns (rpnCondStep st t) ts (rpnDepthNext st (rpnCondStep st t) t d)

/-- Token-model depth along a contracted stream, from a freeze mode. -/
def tokDepthRuns (m : ℕ) : List ℕ → ℕ → ℕ
  | [], d => d
  | t :: L, d => tokDepthRuns (freezeMode4Step m t) L (parserDepthNext m t d)

lemma rpnDepthRuns_append (st : ℕ) (xs ys : List ℕ) (d : ℕ) :
    rpnDepthRuns st (xs ++ ys) d =
      rpnDepthRuns (List.foldl rpnCondStep st xs) ys (rpnDepthRuns st xs d) := by
  induction xs generalizing st d with
  | nil => simp [rpnDepthRuns]
  | cons t ts ih => simp only [List.cons_append, rpnDepthRuns, ih, List.foldl_cons]

lemma tokDepthRuns_append (m : ℕ) (xs ys : List ℕ) (d : ℕ) :
    tokDepthRuns m (xs ++ ys) d =
      tokDepthRuns (List.foldl freezeMode4Step m xs) ys (tokDepthRuns m xs d) := by
  induction xs generalizing m d with
  | nil => simp [tokDepthRuns]
  | cons t ts ih => simp only [List.cons_append, tokDepthRuns, ih, List.foldl_cons]

/-- No depth change along a stretch that stays inside a sentence run without exiting. -/
lemma rpnDepthRuns_eq_of_run (st : ℕ) (ts : List ℕ) (d : ℕ)
    (h : ∀ k < ts.length,
      (rcMode (List.foldl rpnCondStep st (ts.take k)) = 1 ∨
        rcMode (List.foldl rpnCondStep st (ts.take k)) = 6 ∨
        rcMode (List.foldl rpnCondStep st (ts.take k)) = 8 ∨
        rcMode (List.foldl rpnCondStep st (ts.take k)) = 4 ∨
        rcMode (List.foldl rpnCondStep st (ts.take k)) = 7 ∨
        rcMode (List.foldl rpnCondStep st (ts.take k)) = 9) ∧
      ¬((rcMode (List.foldl rpnCondStep st (ts.take k)) = 4 ∨
          rcMode (List.foldl rpnCondStep st (ts.take k)) = 7 ∨
          rcMode (List.foldl rpnCondStep st (ts.take k)) = 9) ∧
        rcMode (List.foldl rpnCondStep st (ts.take (k + 1))) = 0)) :
    rpnDepthRuns st ts d = d := by
  induction ts generalizing st d with
  | nil => rfl
  | cons t ts ih =>
      have h0 := h 0 (by simp)
      simp only [List.take_zero, List.foldl_nil, List.take_succ_cons,
        List.foldl_cons] at h0
      rw [rpnDepthRuns,
        show rpnDepthNext st (rpnCondStep st t) t d = d by
          rw [rpnDepthNext]
          rcases h0 with ⟨hm, hex⟩
          rcases hm with hm | hm | hm | hm | hm | hm <;>
            simp only [hm] <;> norm_num <;> tauto,
        ih (rpnCondStep st t) d (fun k hk => by
          have := h (k + 1) (by simp only [List.length_cons]; omega)
          rwa [List.take_succ_cons, List.foldl_cons, List.take_succ_cons,
            List.foldl_cons] at this)]

/-- A complete price block leaves the depth unchanged. -/
lemma rpnDepthRuns_price_block {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) (d : ℕ) :
    rpnDepthRuns (rcPack 1 1 0) b d = d := by
  obtain ⟨-, hinv⟩ := foldl_rpnCondStep_price_block hb
  refine rpnDepthRuns_eq_of_run _ _ _ fun k hk => ?_
  have := hinv k hk
  constructor
  · omega
  · rintro ⟨h4, -⟩; omega

/-- A complete trade block pops exactly one feature. -/
lemma rpnDepthRuns_trade_block {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) (d : ℕ) :
    rpnDepthRuns (rcPack 4 1 0) b d = d.pred := by
  obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_trade_block hb
  have hne : b ≠ [] := by
    intro hnil
    have := parseRpn_length_lt b.length b φ [] hb
    rw [hnil] at this
    simp at this
  rcases List.eq_nil_or_concat' b with rfl | ⟨init, last, rfl⟩
  · exact absurd rfl hne
  · have hlen : (init ++ [last]).length = init.length + 1 := by simp
    have hzero : ∀ e, rpnDepthRuns (rcPack 4 1 0) init e = e := fun e =>
      rpnDepthRuns_eq_of_run _ _ _ fun k hk => by
        have hk2 : k + 1 < (init ++ [last]).length := by rw [hlen]; omega
        have h1 := hinv k (by rw [hlen]; omega)
        have h2 := hinv (k + 1) hk2
        rw [List.take_append_of_le_length (by omega)] at h1 h2
        constructor
        · omega
        · rintro ⟨-, h0⟩; omega
    have hmodeInit : rcMode (List.foldl rpnCondStep (rcPack 4 1 0) init) = 4 ∨
        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) init) = 7 ∨
        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) init) = 9 := by
      have := hinv init.length (by rw [hlen]; omega)
      rwa [List.take_append_of_le_length le_rfl, List.take_length] at this
    have hstepLast :
        rpnCondStep (List.foldl rpnCondStep (rcPack 4 1 0) init) last =
          rcPack 0 0 0 := by
      have hw := hwalk
      rw [List.foldl_append] at hw
      simpa using hw
    rw [rpnDepthRuns_append, hzero, rpnDepthRuns, rpnDepthRuns, hstepLast,
      rpnDepthNext]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos ⟨hmodeInit, by simp [rcMode, rcPack]⟩]

/-- **Symbol-level depth and mode agree with the contraction** unless the contraction
is unreadable. Paper node: `thm:scon` -/
lemma depthMode_unRpn_agree : ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    ((∀ d, rpnDepthRuns (rcPack 0 0 0) ts d = tokDepthRuns 0 (unRpn ts) d) ∧
      rcMode (List.foldl rpnCondStep (rcPack 0 0 0) ts) = freezeMode4 (unRpn ts)) ∨
    Unreadable (unRpn ts) := by
  intro N
  induction N with
  | zero =>
      intro ts hts
      obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact Or.inl ⟨fun d => rfl, by rw [List.foldl_nil, rcMode_pack, unRpn_nil]; rfl⟩
  | succ N ih =>
      intro ts hts
      match ts with
      | [] => exact Or.inl ⟨fun d => rfl, by rw [List.foldl_nil, rcMode_pack, unRpn_nil]; rfl⟩
      | t :: rest =>
          simp only [List.length_cons] at hts
          by_cases ht0 : t = 0
          · subst ht0
            cases hp : parseRpn rest.length rest with
            | none =>
                refine Or.inr ?_
                rw [show unRpn (0 :: rest) = [0, 0] by
                  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl, hp]]
                exact unreadable_price_poison
            | some pr =>
                obtain ⟨φ, r1⟩ := pr
                obtain ⟨blk, heq, hblk⟩ := parseRpn_strip rest.length rest hp
                obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_price_block hblk
                match r1 with
                | [] =>
                    rw [List.append_nil] at heq
                    subst heq
                    have hun0 : unRpn (0 :: rest) = [0, Encodable.encode φ] := by
                      rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
                        hblk]
                    refine Or.inl ⟨fun d => ?_, ?_⟩
                    · rw [hun0, rpnDepthRuns, rpnCondStep_base_price,
                        show rpnDepthNext (rcPack 0 0 0) (rcPack 1 1 0) 0 d = d by
                          simp [rpnDepthNext, rcMode, rcPack, parserDepthNext],
                        rpnDepthRuns_price_block hblk]
                      simp [tokDepthRuns, freezeMode4Step, parserDepthNext]
                    · rw [hun0, List.foldl_cons, rpnCondStep_base_price, hwalk]
                      simp [freezeMode4, freezeMode4Step, rcMode, rcPack]
                | d0 :: r2 =>
                    subst heq
                    have hr2 : r2.length ≤ N := by
                      have hlt := parseRpn_length_lt _ _ _ _ hp
                      simp only [List.length_cons] at hlt
                      omega
                    have hstD : rpnCondStep (rcPack 2 0 blk.length) d0 =
                        rcPack 0 0 0 := rpnCondStep_day blk.length d0
                    have hstate : List.foldl rpnCondStep (rcPack 0 0 0)
                        (0 :: (blk ++ d0 :: r2)) =
                        List.foldl rpnCondStep (rcPack 0 0 0) r2 := by
                      rw [List.foldl_cons, rpnCondStep_base_price,
                        List.foldl_append, hwalk, List.foldl_cons, hstD]
                    have hdepth : ∀ d, rpnDepthRuns (rcPack 0 0 0)
                        (0 :: (blk ++ d0 :: r2)) d =
                        rpnDepthRuns (rcPack 0 0 0) r2 (d + 1) := by
                      intro d
                      rw [rpnDepthRuns, rpnCondStep_base_price,
                        show rpnDepthNext (rcPack 0 0 0) (rcPack 1 1 0) 0 d = d by
                          simp [rpnDepthNext, rcMode, rcPack, parserDepthNext],
                        rpnDepthRuns_append, rpnDepthRuns_price_block hblk, hwalk,
                        rpnDepthRuns, hstD,
                        show rpnDepthNext (rcPack 2 0 blk.length) (rcPack 0 0 0) d0 d
                            = d + 1 by
                          rw [rpnDepthNext, if_neg (by simp [rcMode, rcPack]),
                            if_pos (by simp [rcMode, rcPack])]]
                    have hchunk : List.foldl freezeMode4Step 0
                        [0, Encodable.encode φ, d0] = 0 := by
                      simp [freezeMode4Step]
                    have hun := unRpn_price_chunk_block hblk d0 r2
                    rcases ih r2 hr2 with ⟨hEq, hM⟩ | hU
                    · refine Or.inl ⟨fun d => ?_, ?_⟩
                      · rw [hun, hdepth,
                          show (0 :: Encodable.encode φ :: d0 :: unRpn r2) =
                            [0, Encodable.encode φ, d0] ++ unRpn r2 from rfl,
                          tokDepthRuns_append, hchunk, hEq]
                        congr 1
                      · rw [hun, hstate,
                          show (0 :: Encodable.encode φ :: d0 :: unRpn r2) =
                            [0, Encodable.encode φ, d0] ++ unRpn r2 from rfl,
                          freezeMode4, List.foldl_append, hchunk]
                        exact hM
                    · refine Or.inr ?_
                      rw [hun,
                        show (0 :: Encodable.encode φ :: d0 :: unRpn r2) =
                          [0, Encodable.encode φ, d0] ++ unRpn r2 from rfl]
                      exact hU.cons_chunk hchunk
          · by_cases ht6 : t = 6
            · subst ht6
              cases hp : parseRpn rest.length rest with
              | none =>
                  refine Or.inr ?_
                  rw [show unRpn (6 :: rest) = [6, 0] by
                    rw [unRpn, List.length_cons, unRpnTokens_cons,
                      if_neg (by norm_num), if_pos rfl, hp]]
                  exact unreadable_trade_poison
              | some pr =>
                  obtain ⟨φ, r1⟩ := pr
                  obtain ⟨blk, heq, hblk⟩ := parseRpn_strip rest.length rest hp
                  subst heq
                  obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_trade_block hblk
                  have hr1 : r1.length ≤ N := by
                    have hlt := parseRpn_length_lt _ _ _ _ hp
                    simp only [List.length_append] at hts
                    omega
                  have hstate : List.foldl rpnCondStep (rcPack 0 0 0)
                      (6 :: (blk ++ r1)) =
                      List.foldl rpnCondStep (rcPack 0 0 0) r1 := by
                    rw [List.foldl_cons, rpnCondStep_base_trade,
                      List.foldl_append, hwalk]
                  have hdepth : ∀ d, rpnDepthRuns (rcPack 0 0 0) (6 :: (blk ++ r1)) d =
                      rpnDepthRuns (rcPack 0 0 0) r1 d.pred := by
                    intro d
                    rw [rpnDepthRuns, rpnCondStep_base_trade,
                      show rpnDepthNext (rcPack 0 0 0) (rcPack 4 1 0) 6 d = d by
                        simp [rpnDepthNext, rcMode, rcPack, parserDepthNext],
                      rpnDepthRuns_append, rpnDepthRuns_trade_block hblk, hwalk]
                  have hchunk : List.foldl freezeMode4Step 0
                      [6, Encodable.encode φ] = 0 := by
                    simp [freezeMode4Step]
                  have hun := unRpn_trade_chunk_block hblk r1
                  rcases ih r1 hr1 with ⟨hEq, hM⟩ | hU
                  · refine Or.inl ⟨fun d => ?_, ?_⟩
                    · rw [hun, hdepth,
                        show (6 :: Encodable.encode φ :: unRpn r1) =
                          [6, Encodable.encode φ] ++ unRpn r1 from rfl,
                        tokDepthRuns_append, hchunk, hEq]
                      congr 1
                    · rw [hun, hstate,
                        show (6 :: Encodable.encode φ :: unRpn r1) =
                          [6, Encodable.encode φ] ++ unRpn r1 from rfl,
                        freezeMode4, List.foldl_append, hchunk]
                      exact hM
                  · refine Or.inr ?_
                    rw [hun,
                      show (6 :: Encodable.encode φ :: unRpn r1) =
                        [6, Encodable.encode φ] ++ unRpn r1 from rfl]
                    exact hU.cons_chunk hchunk
            · by_cases ht1 : t = 1 ∨ t = 7
              · match rest with
                | [] =>
                    refine Or.inl ⟨fun d => ?_, ?_⟩
                    · rcases ht1 with rfl | rfl <;>
                        simp [unRpn, unRpnTokens, rpnDepthRuns, tokDepthRuns,
                          rpnDepthNext, parserDepthNext, rcMode,
                          rcPack]
                    · rcases ht1 with rfl | rfl
                      · rw [List.foldl_cons, List.foldl_nil, rpnCondStep_base_one]
                        simp [unRpn, unRpnTokens, freezeMode4, freezeMode4Step,
                          rcMode, rcPack]
                      · rw [List.foldl_cons, List.foldl_nil, rpnCondStep_base_seven]
                        simp [unRpn, unRpnTokens, freezeMode4, freezeMode4Step,
                          rcMode, rcPack]
                | c :: r =>
                    have hr : r.length ≤ N := by
                      simp only [List.length_cons] at hts
                      omega
                    have hstep1 : rpnCondStep (rcPack 0 0 0) t =
                        rcPack (if t = 1 then 3 else 5) 0 0 := by
                      rcases ht1 with rfl | rfl <;> simp [rpnCondStep_base]
                    have hstep2 :
                        rpnCondStep (rcPack (if t = 1 then 3 else 5) 0 0) c =
                          rcPack 0 0 0 :=
                      rpnCondStep_opaque (by split <;> simp) 0 0 c
                    have hstate : List.foldl rpnCondStep (rcPack 0 0 0)
                        (t :: c :: r) = List.foldl rpnCondStep (rcPack 0 0 0) r := by
                      rw [List.foldl_cons, hstep1, List.foldl_cons, hstep2]
                    have hdepth : ∀ d, rpnDepthRuns (rcPack 0 0 0) (t :: c :: r) d =
                        rpnDepthRuns (rcPack 0 0 0) r (d + 1) := by
                      intro d
                      rw [rpnDepthRuns, hstep1,
                        show rpnDepthNext (rcPack 0 0 0)
                            (rcPack (if t = 1 then 3 else 5) 0 0) t d = d by
                          rcases ht1 with rfl | rfl <;>
                            simp [rpnDepthNext, rcMode, rcPack, parserDepthNext],
                        rpnDepthRuns, hstep2,
                        show rpnDepthNext (rcPack (if t = 1 then 3 else 5) 0 0)
                            (rcPack 0 0 0) c d = d + 1 by
                          rcases ht1 with rfl | rfl <;>
                            simp [rpnDepthNext, rcMode, rcPack]]
                    have hchunk : List.foldl freezeMode4Step 0 [t, c] = 0 := by
                      rcases ht1 with rfl | rfl <;> simp [freezeMode4Step]
                    have hun := unRpn_payload_chunk t c ht1 r
                    rcases ih r hr with ⟨hEq, hM⟩ | hU
                    · refine Or.inl ⟨fun d => ?_, ?_⟩
                      · rw [hun, hdepth,
                          show (t :: c :: unRpn r) = [t, c] ++ unRpn r from rfl,
                          tokDepthRuns_append, hchunk, hEq]
                        congr 1
                        rcases ht1 with rfl | rfl <;>
                          simp [tokDepthRuns, freezeMode4Step, parserDepthNext]
                      · rw [hun, hstate,
                          show (t :: c :: unRpn r) = [t, c] ++ unRpn r from rfl,
                          freezeMode4, List.foldl_append, hchunk]
                        exact hM
                    · refine Or.inr ?_
                      rw [hun,
                        show (t :: c :: unRpn r) = [t, c] ++ unRpn r from rfl]
                      exact hU.cons_chunk hchunk
              · push_neg at ht1
                have hrest : rest.length ≤ N := by omega
                have hstep := rpnCondStep_base_other t ht0 ht1.1 ht6 ht1.2
                have hstate : List.foldl rpnCondStep (rcPack 0 0 0) (t :: rest) =
                    List.foldl rpnCondStep (rcPack 0 0 0) rest := by
                  rw [List.foldl_cons, hstep]
                have hdepth : ∀ d, rpnDepthRuns (rcPack 0 0 0) (t :: rest) d =
                    rpnDepthRuns (rcPack 0 0 0) rest (parserDepthNext 0 t d) := by
                  intro d
                  rw [rpnDepthRuns, hstep,
                    show rpnDepthNext (rcPack 0 0 0) (rcPack 0 0 0) t d =
                      parserDepthNext 0 t d by simp [rpnDepthNext, rcMode, rcPack]]
                have hchunk : List.foldl freezeMode4Step 0 [t] = 0 := by
                  simp [freezeMode4Step, ht0, ht1.1, ht6, ht1.2]
                have hun := unRpn_single_chunk t ⟨ht0, ht1.1, ht6, ht1.2⟩ rest
                rcases ih rest hrest with ⟨hEq, hM⟩ | hU
                · refine Or.inl ⟨fun d => ?_, ?_⟩
                  · rw [hun, hdepth,
                      show (t :: unRpn rest) = [t] ++ unRpn rest from rfl,
                      tokDepthRuns_append, hchunk, hEq]
                    congr 1
                  · rw [hun, hstate,
                      show (t :: unRpn rest) = [t] ++ unRpn rest from rfl,
                      freezeMode4, List.foldl_append, hchunk]
                    exact hM
                · refine Or.inr ?_
                  rw [hun,
                    show (t :: unRpn rest) = [t] ++ unRpn rest from rfl]
                  exact hU.cons_chunk hchunk

/-! ## The position-indexed acceptance scan -/

/-- Feature-stack depth strictly before source position `j`. -/
def rpnDepthAt (tf : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      rpnDepthNext (rpnCondControlAt tf n j) (rpnCondControlAt tf n (j + 1))
        (tf (Nat.pair n j)) (rpnDepthAt tf n j)

lemma rpnDepthNext_le (st st' t d : ℕ) : rpnDepthNext st st' t d ≤ d + 1 := by
  rw [rpnDepthNext, parserDepthNext]
  have := Nat.pred_le d
  split_ifs <;> omega

lemma rpnDepthAt_le (tf : ℕ → ℕ) (n : ℕ) : ∀ j, rpnDepthAt tf n j ≤ j
  | 0 => by simp [rpnDepthAt]
  | j + 1 => by
      rw [rpnDepthAt]
      have h1 := rpnDepthNext_le (rpnCondControlAt tf n j)
        (rpnCondControlAt tf n (j + 1)) (tf (Nat.pair n j)) (rpnDepthAt tf n j)
      have h2 := rpnDepthAt_le tf n j
      omega

/-- The position-indexed depth is the list-level one over the position view. -/
lemma rpnDepthAt_eq_runs (tf : ℕ → ℕ) (n : ℕ) : ∀ J,
    rpnDepthAt tf n J = rpnDepthRuns (rcPack 0 0 0) (vpre tf n J) 0
  | 0 => rfl
  | J + 1 => by
      rw [rpnDepthAt, vpre_succ, rpnDepthRuns_append, rpnDepthAt_eq_runs tf n J,
        ← rpnCondControlAt_eq_foldl, rpnDepthRuns,
        show rpnCondStep (rpnCondControlAt tf n J) (tf (Nat.pair n J)) =
          rpnCondControlAt tf n (J + 1) from rfl, rpnDepthRuns]

/-- The token-model depth scan is the list-level one over the position view. -/
lemma parserDepthScanAt_eq_runs (tokenFn : ℕ → ℕ) (n : ℕ) : ∀ J,
    parserDepthScanAt tokenFn n J = tokDepthRuns 0 (vpre tokenFn n J) 0
  | 0 => rfl
  | J + 1 => by
      rw [parserDepthScanAt, vpre_succ, tokDepthRuns_append,
        parserDepthScanAt_eq_runs tokenFn n J, freezeControlNat_fst,
        show List.foldl freezeMode4Step 0 (vpre tokenFn n J) =
          freezeMode4 (vpre tokenFn n J) from rfl, tokDepthRuns, tokDepthRuns]

/-- Symbol-side structural acceptance: the run automaton ends in base mode with an
empty feature stack (mirror of `parserStructurallyAccepts`). -/
def rpnStructurallyAccepts (tf lenF : ℕ → ℕ) (n : ℕ) : ℕ :=
  if rcMode (rpnCondControlAt tf n (lenF n)) = 0 then
    (if rpnDepthAt tf n (lenF n) = 0 then 1 else 0)
  else 0

/-- **Gate agreement**: the symbol-side acceptance test agrees with the token-model
test on the contraction, unless the contraction is unreadable. Paper node: `thm:scon` -/
lemma rpnStructurallyAccepts_agree (tf tokenFn lenF lenFn : ℕ → ℕ) (n : ℕ)
    (ts : List ℕ) (hts : vpre tf n (lenF n) = ts)
    (hL : vpre tokenFn n (lenFn n) = unRpn ts) :
    rpnStructurallyAccepts tf lenF n = parserStructurallyAccepts tokenFn lenFn n ∨
      Unreadable (unRpn ts) := by
  rcases depthMode_unRpn_agree ts.length ts le_rfl with ⟨hD, hM⟩ | hU
  · refine Or.inl ?_
    rw [rpnStructurallyAccepts, parserStructurallyAccepts, parserDepthScanNat]
    simp only [Nat.unpair_pair]
    rw [freezeControlNat_fst, parserDepthScanAt_eq_runs, hL, rpnDepthAt_eq_runs,
      hts, rpnCondControlAt_eq_foldl, hts, hM, hD]
  · exact Or.inr hU

/-- The feature-stack depth scan is poly-fueled over any digit `PolySegStream`. -/
lemma rpnDepthScan {s : ℕ → List ℕ} (h : PolySegStream s) :
    ∃ c, PolyFueled c (fun z =>
      rpnDepthAt (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0)
        z.unpair.1 z.unpair.2) := by
  obtain ⟨cs, hscan⟩ := rpnCondScan h
  obtain ⟨-, hbig⟩ := h.undigitizeTokens
  obtain ⟨ctc, htc⟩ := hbig.clampVal (PolyFueled.const 8)
  obtain ⟨cad, had⟩ := addc_polyFueled
  -- Step input `⟨n, ⟨j, prev⟩⟩`.
  have hn := PolyFueled.left
  have hj := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hj1 : PolyFueled _ (fun z : ℕ => z.unpair.2.unpair.1 + 1) :=
    (had.comp (hj.pair (PolyFueled.const 1))).of_eq fun z => by
      simp only [Nat.unpair_pair]
  have hmz := PolyFueled.left.comp (hscan.comp (hn.pair hj))
  have hmz1 := PolyFueled.left.comp (hscan.comp (hn.pair hj1))
  have htok := htc.comp (hn.pair hj)
  have hsucc : PolyFueled _ (fun z : ℕ => z.unpair.2.unpair.2 + 1) :=
    (had.comp (hprev.pair (PolyFueled.const 1))).of_eq fun z => by
      simp only [Nat.unpair_pair]
  have hpred : PolyFueled _ (fun z : ℕ => z.unpair.2.unpair.2 - 1) :=
    (subc_polyFueled.comp (hprev.pair (PolyFueled.const 1))).of_eq fun z => by
      simp only [Nat.unpair_pair]
  obtain ⟨_, hb8⟩ := polyFueled_ifEq htok 8 hpred hprev
  obtain ⟨_, hb4⟩ := polyFueled_ifEq htok 4 hpred hb8
  obtain ⟨_, hb3⟩ := polyFueled_ifEq htok 3 hpred hb4
  obtain ⟨_, hbase⟩ := polyFueled_ifEq htok 2 hpred hb3
  obtain ⟨_, hexit⟩ := polyFueled_ifEq hmz1 0 hpred hprev
  obtain ⟨_, hA9⟩ := polyFueled_ifEq hmz 9 hexit hprev
  obtain ⟨_, hA7⟩ := polyFueled_ifEq hmz 7 hexit hA9
  obtain ⟨_, hA4⟩ := polyFueled_ifEq hmz 4 hexit hA7
  obtain ⟨_, hA5⟩ := polyFueled_ifEq hmz 5 hsucc hA4
  obtain ⟨_, hA3⟩ := polyFueled_ifEq hmz 3 hsucc hA5
  obtain ⟨_, hA2⟩ := polyFueled_ifEq hmz 2 hsucc hA3
  obtain ⟨_, hstep⟩ := polyFueled_ifEq hmz 0 hbase hA2
  set tf : ℕ → ℕ := fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0 with htf
  refine ⟨_, PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun n j => rpnDepthAt tf n j)
    (fun n => rfl)
    (fun n j => ?_)
    ((IsPolyBounded.linear 0).of_le fun z =>
      le_trans (rpnDepthAt_le _ _ _) (Nat.unpair_right_le z))⟩
  simp only [Nat.unpair_pair]
  have htfj : tf (Nat.pair n j) = (undigitize (s n)).getD j 0 := by
    rw [htf]; simp only [Nat.unpair_pair]
  rw [rpnDepthAt,
    show (Nat.unpair (rpnCondControlAt tf n j)).1 =
      rcMode (rpnCondControlAt tf n j) from rfl,
    show (Nat.unpair (rpnCondControlAt tf n (j + 1))).1 =
      rcMode (rpnCondControlAt tf n (j + 1)) from rfl,
    ← htfj, rpnDepthNext]
  simp only [Nat.pred_eq_sub_one]
  have hclamp : ∀ k, k ≤ 8 →
      (min (tf (Nat.pair n j)) (8 + 1) = k ↔ tf (Nat.pair n j) = k) := by
    intro k hk
    by_cases h9 : tf (Nat.pair n j) ≤ 9
    · rw [Nat.min_eq_left h9]
    · rw [Nat.min_eq_right (by omega : 8 + 1 ≤ _)]
      constructor <;> intro h <;> omega
  by_cases hm0 : rcMode (rpnCondControlAt tf n j) = 0
  · rw [if_pos hm0, if_pos hm0, parserDepthNext, if_pos rfl]
    simp only [Nat.pred_eq_sub_one]
    by_cases h2 : tf (Nat.pair n j) = 2
    · rw [if_pos ((hclamp 2 (by norm_num)).mpr h2), if_pos h2]
    · rw [if_neg (fun hc => h2 ((hclamp 2 (by norm_num)).mp hc)), if_neg h2]
      by_cases h3 : tf (Nat.pair n j) = 3
      · rw [if_pos ((hclamp 3 (by norm_num)).mpr h3), if_pos h3]
      · rw [if_neg (fun hc => h3 ((hclamp 3 (by norm_num)).mp hc)), if_neg h3]
        by_cases h4 : tf (Nat.pair n j) = 4
        · rw [if_pos ((hclamp 4 (by norm_num)).mpr h4), if_pos h4]
        · rw [if_neg (fun hc => h4 ((hclamp 4 (by norm_num)).mp hc)), if_neg h4]
          by_cases h8 : tf (Nat.pair n j) = 8
          · rw [if_pos ((hclamp 8 (by norm_num)).mpr h8), if_pos h8]
          · rw [if_neg (fun hc => h8 ((hclamp 8 (by norm_num)).mp hc)), if_neg h8]
  · rw [if_neg hm0, if_neg hm0]
    by_cases hm2 : rcMode (rpnCondControlAt tf n j) = 2
    · rw [if_pos hm2, if_pos hm2]
    · rw [if_neg hm2, if_neg hm2]
      by_cases hm3 : rcMode (rpnCondControlAt tf n j) = 3
      · rw [if_pos hm3, if_pos hm3]
      · rw [if_neg hm3, if_neg hm3]
        by_cases hm5 : rcMode (rpnCondControlAt tf n j) = 5
        · rw [if_pos hm5, if_pos hm5]
        · rw [if_neg hm5, if_neg hm5]
          by_cases hm4 : rcMode (rpnCondControlAt tf n j) = 4
          · rw [if_pos hm4]
            by_cases hnext : rcMode (rpnCondControlAt tf n (j + 1)) = 0
            · rw [if_pos hnext, if_pos ⟨Or.inl hm4, hnext⟩]
            · rw [if_neg hnext, if_neg (by tauto)]
          · rw [if_neg hm4]
            by_cases hm7 : rcMode (rpnCondControlAt tf n j) = 7
            · rw [if_pos hm7]
              by_cases hnext : rcMode (rpnCondControlAt tf n (j + 1)) = 0
              · rw [if_pos hnext, if_pos ⟨Or.inr (Or.inl hm7), hnext⟩]
              · rw [if_neg hnext, if_neg (by tauto)]
            · rw [if_neg hm7]
              by_cases hm9 : rcMode (rpnCondControlAt tf n j) = 9
              · rw [if_pos hm9]
                by_cases hnext : rcMode (rpnCondControlAt tf n (j + 1)) = 0
                · rw [if_pos hnext, if_pos ⟨Or.inr (Or.inr hm9), hnext⟩]
                · rw [if_neg hnext, if_neg (by tauto)]
              · rw [if_neg hm9, if_neg (by tauto)]

/-! ## The frame pass (symbol level) — emission and contraction anchor

The token-model frame transducer (`conditioningFrameTokenRun`) replaces each trade
chunk `[6, φc]` of the priced stream by a locally gated leg body
(`rawLocallyGated{Beta,Second}BodyTokens`) closing with a re-emitted trade.  At the
symbol level the trade sentence is a run; the mirror emission splices the buffered
run into the two sentence slots of the body — the conjunction block
`3 :: run ++ blockψ` at the ratio's numerator and re-emitted trade, and `blockψ` at
the denominator — leaving the gate arithmetic (constants, `letE` variables,
operators) verbatim.  The contraction anchor below is compositional, through the
prefix-contraction algebra `UnRpnContractsTo` (`Framework/Emission/RpnSentence.lean`) and its
raw-combinator instances (`Construction/Conditioning/Compiler.lean`). -/

/-! ### The frame-leg emission -/

/-- A symbol-level price leaf: the sentence slot holds an expanded block. -/
def rpnFramePriceSym (block : List ℕ) (day : ℕ) : List ℕ := 0 :: block ++ [day]

/-- The (sentence-free) conditioning gate over the two `letE` variables. -/
def rpnFrameGate (bc ibc : ℕ) : List ℕ :=
  rawConditioningGateTokens [7, 0] (rawAbsTokens [7, 1]) bc ibc

/-- The conditional-ratio value with expanded sentence blocks. -/
def rpnFrameRatioSym (conjBlock ψBlock : List ℕ) (day : ℕ) (ε : ℚ) : List ℕ :=
  rawMulTokens (rpnFramePriceSym conjBlock day)
    (rawLowerSafeRecipTokens (rpnFramePriceSym ψBlock day) ε)

/-- **The frame-leg emission at a trade-run exit**: the RPN expansion of the
locally gated leg body, with the buffered trade run `buf` and the condition block
`blk` spliced into the sentence slots, closing with the re-emitted trade. -/
def rpnFrameEmit (second : Bool) (blk : List ℕ) (ε : ℚ) (day bc ibc : ℕ)
    (buf : List ℕ) : List ℕ :=
  (if second then
    rpnFrameRatioSym (3 :: buf ++ blk) blk day ε ++
      rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ)))
        (rawMulTokens
          (rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate bc ibc)))
          [7, 0]) ++ [8]
  else
    rpnFrameRatioSym (3 :: buf ++ blk) blk day ε ++
      rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate bc ibc)) ++ [8]) ++
  8 :: 6 :: (if second then blk else 3 :: buf ++ blk)

/-- **The frame-leg emission contracts to the token-model frame emission** (the
correctness anchor for the frame pass, mirror of `unRpn_price_rewrite_chunk`).
Paper node: `thm:scon` -/
lemma rpnFrameEmit_contractsTo {buf blk : List ℕ} {φ ψn : Sentence}
    (hbuf : parseRpn buf.length buf = some (φ, []))
    (hblk : parseRpn blk.length blk = some (ψn, []))
    (second : Bool) (day bc ibc : ℕ) (ε : ℚ) :
    UnRpnContractsTo (rpnFrameEmit second blk ε day bc ibc buf)
      ((if second then
          rawLocallyGatedSecondBodyTokens (Encodable.encode φ)
            (Encodable.encode ψn) day bc ibc ε
        else
          rawLocallyGatedBetaBodyTokens (Encodable.encode φ)
            (Encodable.encode ψn) day bc ibc ε) ++
        8 :: [6, if second then Encodable.encode ψn
          else conjunctionCode (Encodable.encode φ) (Encodable.encode ψn)]) := by
  have hconj : parseRpn (3 :: buf ++ blk).length (3 :: buf ++ blk) =
      some (φ ⋏ ψn, []) := parseRpn_and_block hbuf hblk
  have hgate : UnRpnContractsTo (rpnFrameGate bc ibc) (rpnFrameGate bc ibc) :=
    UnRpnContractsTo.gateTok (UnRpnContractsTo.varTok 0)
      (UnRpnContractsTo.absTok (UnRpnContractsTo.varTok 1)) bc ibc
  have hratio : UnRpnContractsTo (rpnFrameRatioSym (3 :: buf ++ blk) blk day ε)
      (rawMulTokens (rawPriceTokens (Encodable.encode (φ ⋏ ψn)) day)
        (rawLowerSafeRecipTokens
          (rawPriceTokens (Encodable.encode ψn) day) ε)) :=
    (UnRpnContractsTo.priceChunk hconj day).mulTok
      (UnRpnContractsTo.lowerSafeRecipTok (UnRpnContractsTo.priceChunk hblk day) ε)
  have hmin : UnRpnContractsTo
      (rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate bc ibc)))
      (rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate bc ibc))) :=
    (UnRpnContractsTo.varTok 1).minTok ((UnRpnContractsTo.varTok 1).mulTok hgate)
  have hclose : UnRpnContractsTo [(8 : ℕ)] [8] :=
    UnRpnContractsTo.single 8 (by norm_num)
  cases second with
  | false =>
      have htail : UnRpnContractsTo (6 :: (3 :: buf ++ blk))
          [6, Encodable.encode (φ ⋏ ψn)] := UnRpnContractsTo.tradeChunk hconj
      have hcomp := (((hratio.append hmin).append hclose).append
        (hclose.append htail))
      refine hcomp.of_eq ?_ ?_
      · simp [rpnFrameEmit]
      · simp [rawLocallyGatedBetaBodyTokens, rawConditioningRatioTokens,
          rpnFrameGate, conjunctionCode_exact]
  | true =>
      have htail : UnRpnContractsTo (6 :: blk) [6, Encodable.encode ψn] :=
        UnRpnContractsTo.tradeChunk hblk
      have hsecondBody : UnRpnContractsTo
          (rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ)))
            (rawMulTokens
              (rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate bc ibc)))
              [7, 0]))
          (rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ)))
            (rawMulTokens
              (rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate bc ibc)))
              [7, 0])) :=
        (UnRpnContractsTo.constTok _).mulTok (hmin.mulTok (UnRpnContractsTo.varTok 0))
      have hcomp := (((hratio.append hsecondBody).append hclose).append
        (hclose.append htail))
      refine hcomp.of_eq ?_ ?_
      · simp [rpnFrameEmit]
      · simp [rawLocallyGatedSecondBodyTokens, rawConditioningRatioTokens,
          rpnFrameGate, conjunctionCode_exact]

/-! ### The frame run (streaming, exit-triggered) -/

/-- Tokens emitted at one source position of the frame pass. -/
def rpnFrameEmitAt (second : Bool) (blk : List ℕ) (ε : ℚ) (day bc ibc : ℕ)
    (st : ℕ) (buf : List ℕ) (t : ℕ) : List ℕ :=
  if rcMode st = 0 ∧ t = 6 then []
  else if rcMode st = 4 ∨ rcMode st = 7 ∨ rcMode st = 9 then
    (if rcMode (rpnCondStep st t) = 0 then
      rpnFrameEmit second blk ε day bc ibc (buf ++ [t]) else [])
  else [t]

/-- The streaming frame rewrite: state, run buffer, and emitted output. -/
def rpnFrameRun (second : Bool) (blk : List ℕ) (ε : ℚ) (day bc ibc : ℕ) :
    ℕ × List ℕ → List ℕ → (ℕ × List ℕ) × List ℕ
  | s, [] => (s, [])
  | (st, buf), t :: ts =>
      let rest := rpnFrameRun second blk ε day bc ibc
        (rpnCondStep st t, rpnCondBuf st buf t) ts
      (rest.1, rpnFrameEmitAt second blk ε day bc ibc st buf t ++ rest.2)

@[simp] lemma rpnFrameRun_nil (second : Bool) (blk : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (s : ℕ × List ℕ) :
    rpnFrameRun second blk ε day bc ibc s [] = (s, []) := rfl

lemma rpnFrameRun_cons (second : Bool) (blk : List ℕ) (ε : ℚ) (day bc ibc : ℕ)
    (st : ℕ) (buf : List ℕ) (t : ℕ) (ts : List ℕ) :
    rpnFrameRun second blk ε day bc ibc (st, buf) (t :: ts) =
      ((rpnFrameRun second blk ε day bc ibc
          (rpnCondStep st t, rpnCondBuf st buf t) ts).1,
        rpnFrameEmitAt second blk ε day bc ibc st buf t ++
          (rpnFrameRun second blk ε day bc ibc
            (rpnCondStep st t, rpnCondBuf st buf t) ts).2) := rfl

lemma rpnFrameEmitAt_base_trade (second : Bool) (blk : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (buf : List ℕ) :
    rpnFrameEmitAt second blk ε day bc ibc (rcPack 0 0 0) buf 6 = [] := by
  simp [rpnFrameEmitAt]

lemma rpnFrameRun_append (second : Bool) (blk : List ℕ) (ε : ℚ) (day bc ibc : ℕ)
    (s : ℕ × List ℕ) (xs ys : List ℕ) :
    rpnFrameRun second blk ε day bc ibc s (xs ++ ys) =
      let first := rpnFrameRun second blk ε day bc ibc s xs
      let rest := rpnFrameRun second blk ε day bc ibc first.1 ys
      (rest.1, first.2 ++ rest.2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨st, buf⟩ := s
      simp only [List.cons_append, rpnFrameRun]
      rw [ih]
      simp [List.append_assoc]

/-- **Copy behavior**: outside base mode and the trade run modes the frame pass copies
its input verbatim (the emission tests only the control mode). -/
lemma rpnFrameRun_copy_of_modes (second : Bool) (blk : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (st : ℕ) (buf : List ℕ) (ts : List ℕ)
    (h : ∀ k < ts.length,
      rcMode (List.foldl rpnCondStep st (ts.take k)) ≠ 0 ∧
      rcMode (List.foldl rpnCondStep st (ts.take k)) ≠ 4 ∧
      rcMode (List.foldl rpnCondStep st (ts.take k)) ≠ 7 ∧
      rcMode (List.foldl rpnCondStep st (ts.take k)) ≠ 9) :
    rpnFrameRun second blk ε day bc ibc (st, buf) ts =
      ((List.foldl rpnCondStep st ts, rpnCondBufFold st buf ts), ts) := by
  induction ts generalizing st buf with
  | nil => rfl
  | cons t ts ih =>
      have h0 := h 0 (by simp)
      simp only [List.take_zero, List.foldl_nil] at h0
      have hemit : rpnFrameEmitAt second blk ε day bc ibc st buf t = [t] := by
        rw [rpnFrameEmitAt, if_neg (by tauto), if_neg (by tauto)]
      rw [rpnFrameRun_cons, hemit,
        ih (rpnCondStep st t) (rpnCondBuf st buf t) (fun k hk => by
          have := h (k + 1) (by simp only [List.length_cons]; omega)
          rwa [List.take_succ_cons, List.foldl_cons] at this)]
      simp [rpnCondBufFold]

/-- Inside a trade run that does not exit, the recorded run length grows by one. -/
lemma rcLen_trade_run_step (st t : ℕ)
    (hm : rcMode st = 4 ∨ rcMode st = 7 ∨ rcMode st = 9)
    (hne : rcMode (rpnCondStep st t) ≠ 0) :
    rcLen (rpnCondStep st t) = rcLen st + 1 := by
  rw [rcMode_step_eq] at hne
  rw [rcLen_step_eq]
  rcases hm with hm | hm | hm <;>
    rw [hm] at hne ⊢ <;>
    rw [rcLenF] <;> rw [rcModeF] at hne <;>
    norm_num at hne ⊢ <;>
    first
      | assumption
      | (split_ifs at hne ⊢ <;> simp_all)

/-- **Silent behavior**: inside a trade run that has not yet exited, the frame pass
emits nothing and the buffer accumulates the run. -/
lemma rpnFrameRun_silent (second : Bool) (blk : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (st : ℕ) (buf : List ℕ) (ts : List ℕ)
    (h : ∀ k < ts.length,
      (rcMode (List.foldl rpnCondStep st (ts.take k)) = 4 ∨
        rcMode (List.foldl rpnCondStep st (ts.take k)) = 7 ∨
        rcMode (List.foldl rpnCondStep st (ts.take k)) = 9) ∧
      rcMode (List.foldl rpnCondStep st (ts.take (k + 1))) ≠ 0) :
    rpnFrameRun second blk ε day bc ibc (st, buf) ts =
      ((List.foldl rpnCondStep st ts, buf ++ ts), []) := by
  induction ts generalizing st buf with
  | nil => simp
  | cons t ts ih =>
      have h0 := h 0 (by simp)
      simp only [List.take_zero, List.foldl_nil, List.take_succ_cons,
        List.foldl_cons] at h0
      obtain ⟨hmode, hnext⟩ := h0
      have hemit : rpnFrameEmitAt second blk ε day bc ibc st buf t = [] := by
        rw [rpnFrameEmitAt]
        by_cases hb : rcMode st = 0 ∧ t = 6
        · rw [if_pos hb]
        · rw [if_neg hb, if_pos hmode, if_neg hnext]
      have hbuf : rpnCondBuf st buf t = buf ++ [t] := by
        rw [rpnCondBuf, rcLen_trade_run_step st t hmode hnext, if_neg (by omega)]
      rw [rpnFrameRun_cons, hemit, hbuf,
        ih (rpnCondStep st t) (buf ++ [t]) (fun k hk => by
          have := h (k + 1) (by simp only [List.length_cons]; omega)
          rwa [List.take_succ_cons, List.foldl_cons,
            List.take_succ_cons, List.foldl_cons] at this)]
      simp [List.foldl_cons]

/-- **The trade block instance**: a complete trade sentence run is buffered silently
and discharged by the leg-body emission at its final token. -/
lemma rpnFrameRun_trade_block (second : Bool) (blkψ : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) :
    rpnFrameRun second blkψ ε day bc ibc (rcPack 4 1 0, []) b =
      ((rcPack 0 0 0, []), rpnFrameEmit second blkψ ε day bc ibc b) := by
  obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_trade_block hb
  have hne : b ≠ [] := by
    intro hnil
    have := parseRpn_length_lt b.length b φ [] hb
    rw [hnil] at this
    simp at this
  rcases List.eq_nil_or_concat' b with rfl | ⟨init, last, rfl⟩
  · exact absurd rfl hne
  · have hlen : (init ++ [last]).length = init.length + 1 := by simp
    have hsilent := rpnFrameRun_silent second blkψ ε day bc ibc
      (rcPack 4 1 0) [] init (fun k hk => by
        have hk1 : k < (init ++ [last]).length := by rw [hlen]; omega
        have hk2 : k + 1 < (init ++ [last]).length := by rw [hlen]; omega
        refine ⟨?_, ?_⟩
        · have := hinv k hk1
          rwa [List.take_append_of_le_length (le_of_lt hk)] at this
        · have := hinv (k + 1) hk2
          rw [List.take_append_of_le_length (by omega)] at this
          omega)
    have hinit : List.foldl rpnCondStep (rcPack 4 1 0) init =
        List.foldl rpnCondStep (rcPack 4 1 0)
          ((init ++ [last]).take init.length) := by
      rw [List.take_append_of_le_length le_rfl, List.take_length]
    have hmodeInit : rcMode (List.foldl rpnCondStep (rcPack 4 1 0) init) = 4 ∨
        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) init) = 7 ∨
        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) init) = 9 := by
      rw [hinit]
      exact hinv init.length (by rw [hlen]; omega)
    have hstepLast :
        rpnCondStep (List.foldl rpnCondStep (rcPack 4 1 0) init) last =
          rcPack 0 0 0 := by
      have hw := hwalk
      rw [List.foldl_append] at hw
      simpa using hw
    rw [rpnFrameRun_append, hsilent]
    simp only
    rw [rpnFrameRun_cons, hstepLast]
    have hemit : rpnFrameEmitAt second blkψ ε day bc ibc
        (List.foldl rpnCondStep (rcPack 4 1 0) init) ([] ++ init) last =
        rpnFrameEmit second blkψ ε day bc ibc (init ++ [last]) := by
      rw [rpnFrameEmitAt, if_neg (by rcases hmodeInit with h | h | h <;> simp [h]),
        if_pos hmodeInit, hstepLast]
      simp
    rw [hemit]
    simp [rpnCondBuf, hstepLast]

/-- The frame pass output on a whole stream: the run, plus the end-of-stream flush of
an unfinished trade tag (mirror of `conditioningFrameTokenOutput`). -/
def rpnFrameOutput (second : Bool) (blk : List ℕ) (ε : ℚ) (day bc ibc : ℕ)
    (ts : List ℕ) : List ℕ :=
  (rpnFrameRun second blk ε day bc ibc (rcPack 0 0 0, []) ts).2 ++
    (if rcMode (rpnFrameRun second blk ε day bc ibc (rcPack 0 0 0, []) ts).1.1 = 4 ∨
        rcMode (rpnFrameRun second blk ε day bc ibc (rcPack 0 0 0, []) ts).1.1 = 7 ∨
        rcMode (rpnFrameRun second blk ε day bc ibc (rcPack 0 0 0, []) ts).1.1 = 9
      then [6] else [])

/-- The frame run tracks the price pass's control state and buffer. -/
lemma rpnFrameRun_state (second : Bool) (blk : List ℕ) (ε : ℚ) (day bc ibc : ℕ)
    (st : ℕ) (buf : List ℕ) (ts : List ℕ) :
    (rpnFrameRun second blk ε day bc ibc (st, buf) ts).1 =
      (List.foldl rpnCondStep st ts, rpnCondBufFold st buf ts) := by
  induction ts generalizing st buf with
  | nil => rfl
  | cons t ts ih => rw [rpnFrameRun_cons]; simpa [rpnCondBufFold] using ih _ _

/-- Peel a chunk that returns the frame pass to its initial configuration. -/
lemma rpnFrameOutput_append_base (second : Bool) (blkψ : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (C rest : List ℕ)
    (hstate : List.foldl rpnCondStep (rcPack 0 0 0) C = rcPack 0 0 0)
    (hbuf : rpnCondBufFold (rcPack 0 0 0) [] C = []) :
    rpnFrameOutput second blkψ ε day bc ibc (C ++ rest) =
      (rpnFrameRun second blkψ ε day bc ibc (rcPack 0 0 0, []) C).2 ++
        rpnFrameOutput second blkψ ε day bc ibc rest := by
  have h1 : (rpnFrameRun second blkψ ε day bc ibc (rcPack 0 0 0, []) C).1 =
      (rcPack 0 0 0, []) := by
    rw [rpnFrameRun_state, hstate, hbuf]
  rw [rpnFrameOutput, rpnFrameOutput, rpnFrameRun_append]
  simp only [h1, List.append_assoc]

/-! ### Token-model frame run equations (per contracted chunk)

Chunk-by-chunk characterizations of `ConditioningCompile.conditioningFrameTokenOutput`,
the token-model transducer the frame pass mirrors. -/

section FrameTokenRunEq

variable (second : Bool) (ψCode day : ℕ) (ε : ℚ) (bc ibc : ℕ)

lemma conditioningFrameTokenOutput_single (t : ℕ)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (h6 : t ≠ 6) (h7 : t ≠ 7) (L : List ℕ) :
    conditioningFrameTokenOutput second ψCode day ε bc ibc (t :: L) =
      t :: conditioningFrameTokenOutput second ψCode day ε bc ibc L := by
  simp [conditioningFrameTokenOutput, conditioningFrameTokenRun,
    conditioningFrameTokenEmit, EF.freezeTokenNext, h0, h1, h6, h7]

lemma conditioningFrameTokenOutput_payload (t c : ℕ) (ht : t = 1 ∨ t = 7)
    (L : List ℕ) :
    conditioningFrameTokenOutput second ψCode day ε bc ibc (t :: c :: L) =
      t :: c :: conditioningFrameTokenOutput second ψCode day ε bc ibc L := by
  rcases ht with rfl | rfl <;>
    simp [conditioningFrameTokenOutput, conditioningFrameTokenRun,
      conditioningFrameTokenEmit, EF.freezeTokenNext]

lemma conditioningFrameTokenOutput_one (t : ℕ) (ht : t = 1 ∨ t = 7) :
    conditioningFrameTokenOutput second ψCode day ε bc ibc [t] = [t] := by
  rcases ht with rfl | rfl <;>
    simp [conditioningFrameTokenOutput, conditioningFrameTokenRun,
      conditioningFrameTokenEmit, EF.freezeTokenNext]

lemma conditioningFrameTokenOutput_price (fc d : ℕ) (L : List ℕ) :
    conditioningFrameTokenOutput second ψCode day ε bc ibc (0 :: fc :: d :: L) =
      0 :: fc :: d :: conditioningFrameTokenOutput second ψCode day ε bc ibc L := by
  simp [conditioningFrameTokenOutput, conditioningFrameTokenRun,
    conditioningFrameTokenEmit, EF.freezeTokenNext]

lemma conditioningFrameTokenOutput_price_pair (fc : ℕ) :
    conditioningFrameTokenOutput second ψCode day ε bc ibc [0, fc] = [0, fc] := by
  simp [conditioningFrameTokenOutput, conditioningFrameTokenRun,
    conditioningFrameTokenEmit, EF.freezeTokenNext]

lemma conditioningFrameTokenOutput_trade (fc : ℕ) (L : List ℕ) :
    conditioningFrameTokenOutput second ψCode day ε bc ibc (6 :: fc :: L) =
      (if second then
          rawLocallyGatedSecondBodyTokens fc ψCode day bc ibc ε ++ [8, 6, ψCode]
        else
          rawLocallyGatedBetaBodyTokens fc ψCode day bc ibc ε ++
            [8, 6, conjunctionCode fc ψCode]) ++
        conditioningFrameTokenOutput second ψCode day ε bc ibc L := by
  cases second <;>
    simp [conditioningFrameTokenOutput, conditioningFrameTokenRun,
      conditioningFrameTokenEmit, EF.freezeTokenNext, List.append_assoc]

end FrameTokenRunEq

/-- Price-run instance of the inside invariant (for streams that never exit). -/
lemma priceWalk_inside (v : List ℕ) (j : ℕ) (hj : j ≤ v.length)
    (hmods : ∀ i, i ≤ j →
      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (v.take i)) ≠ 2) :
    (rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (v.take j)) = 1 ∨
      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (v.take j)) = 6 ∨
      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (v.take j)) = 8) ∧
    1 ≤ rcCnt (List.foldl rpnCondStep (rcPack 1 1 0) (v.take j)) ∧
    rcLen (List.foldl rpnCondStep (rcPack 1 1 0) (v.take j)) = j :=
  runWalk_inside (b := 6) (s := 8) (exit := fun r' => rcPack 2 0 r')
    (fun c r t => rpnCondStep_price c r t)
    (fun c r t => rpnCondStep_priceEsc c r t)
    (fun c r t => rpnCondStep_priceStr c r t)
    2 (fun r' => rcMode_pack 2 0 r') v j hj hmods

/-! ### Splitting the contraction at a chunk boundary

By the append fact recorded in the module header, the contraction does not split
unconditionally.  It does split on any stream the run automaton walks back to base
mode: either the stream is `UnRpnContractsTo`-transparent ahead of every continuation,
or its first poisoned chunk stops the contraction outright.  Same chunk induction as
`tradeRuns_unRpn_agree`, with the first-exit localization supplying the
poisons-every-extension branch. -/

/-- A poisoned stream stops the contraction: nothing appended is ever read. -/
def UnRpnStops (A : List ℕ) : Prop := ∀ rest, unRpn (A ++ rest) = unRpn A

lemma UnRpnStops.cons_chunk {C A : List ℕ} {P : List ℕ}
    (hC : UnRpnContractsTo C P) (h : UnRpnStops A) : UnRpnStops (C ++ A) := by
  intro rest
  rw [List.append_assoc, hC (A ++ rest), hC A, h rest]

/-- **The contraction splits at a chunk boundary**: on a stream the run automaton
walks back to base mode, either the whole stream contracts transparently ahead of any
continuation, or a poisoned chunk stops the contraction outright (and the contraction
is unreadable). Paper node: `thm:scon` -/
lemma unRpn_split : ∀ (N : ℕ) (A : List ℕ), A.length ≤ N →
    List.foldl rpnCondStep (rcPack 0 0 0) A = rcPack 0 0 0 →
    UnRpnContractsTo A (unRpn A) ∨ (UnRpnStops A ∧ Unreadable (unRpn A)) := by
  intro N
  induction N with
  | zero =>
      intro A hA _
      obtain rfl : A = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact Or.inl (fun rest => rfl)
  | succ N ih =>
      intro A hA hbase
      match A with
      | [] => exact Or.inl (fun rest => rfl)
      | t :: rest =>
          simp only [List.length_cons] at hA
          by_cases ht0 : t = 0
          · subst ht0
            cases hp : parseRpn rest.length rest with
            | some pr =>
                obtain ⟨φ, r1⟩ := pr
                obtain ⟨blk, heq, hblk⟩ := parseRpn_strip rest.length rest hp
                obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_price_block hblk
                match r1 with
                | [] =>
                    exfalso
                    rw [List.append_nil] at heq
                    subst heq
                    rw [List.foldl_cons, rpnCondStep_base_price, hwalk] at hbase
                    have := congrArg rcMode hbase
                    rw [rcMode_pack, rcMode_pack] at this
                    exact absurd this (by norm_num)
                | d0 :: r2 =>
                    subst heq
                    have hr2 : r2.length ≤ N := by
                      have hlt := parseRpn_length_lt _ _ _ _ hp
                      simp only [List.length_cons] at hlt
                      omega
                    have hstD : rpnCondStep (rcPack 2 0 blk.length) d0 =
                        rcPack 0 0 0 := rpnCondStep_day blk.length d0
                    have hbase2 : List.foldl rpnCondStep (rcPack 0 0 0) r2 =
                        rcPack 0 0 0 := by
                      rw [List.foldl_cons, rpnCondStep_base_price,
                        List.foldl_append, hwalk, List.foldl_cons, hstD] at hbase
                      exact hbase
                    have hA2 : (0 : ℕ) :: (blk ++ d0 :: r2) =
                        (0 :: blk ++ [d0]) ++ r2 := by simp
                    have hC := UnRpnContractsTo.priceChunk hblk d0
                    rcases ih r2 hr2 hbase2 with hIH | ⟨hstop, hU⟩
                    · exact Or.inl (((hC.append hIH).of_eq hA2.symm rfl).self)
                    · refine Or.inr ⟨?_, ?_⟩
                      · rw [hA2]; exact UnRpnStops.cons_chunk hC hstop
                      · rw [unRpn_price_chunk_block hblk d0 r2,
                          show (0 :: Encodable.encode φ :: d0 :: unRpn r2) =
                            [0, Encodable.encode φ, d0] ++ unRpn r2 from rfl]
                        exact hU.cons_chunk (by simp [freezeMode4Step])
            | none =>
                have hun0 : unRpn (0 :: rest) = [0, 0] := by
                  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl, hp]
                by_cases hex : ∃ k, k ≤ rest.length ∧
                    rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (rest.take k)) = 2
                · classical
                  obtain ⟨hk₀le, hk₀mode⟩ := Nat.find_spec hex
                  set k₀ := Nat.find hex with hk₀def
                  have hfirst : ∀ i < k₀,
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                        (rest.take i)) ≠ 2 := fun i hi hmode =>
                    Nat.find_min hex hi ⟨by omega, hmode⟩
                  obtain ⟨hk₀pos, hW, hinside⟩ := priceWalk_first_exit rest k₀
                    hk₀le hfirst hk₀mode
                  have htakelen : (rest.take k₀).length = k₀ := by
                    rw [List.length_take]; omega
                  have hconv := parse_of_priceRunWalk k₀ (rest.take k₀)
                    (le_of_eq htakelen) 0 0
                    (by rw [if_pos rfl, htakelen]; simpa using hW)
                    (by
                      intro k hk
                      rw [htakelen] at hk
                      rw [List.take_take, min_eq_left (le_of_lt hk)]
                      exact ⟨(hinside k hk).1, (hinside k hk).2.1⟩)
                  rcases hconv with ⟨φu, hφu⟩ | hpoison
                  · exfalso
                    rw [← List.take_append_drop k₀ rest] at hp
                    rw [parseRpn_block_head hφu (rest.drop k₀) (by
                      simp only [List.length_append]; omega)] at hp
                    simp at hp
                  · have hunL : ∀ Y, unRpn (0 :: (rest ++ Y)) = [0, 0] := fun Y => by
                      rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
                        show rest ++ Y = rest.take k₀ ++ (rest.drop k₀ ++ Y) by
                          rw [← List.append_assoc, List.take_append_drop],
                        hpoison _ _]
                    refine Or.inr ⟨fun Y => ?_, ?_⟩
                    · rw [show (0 : ℕ) :: rest ++ Y = 0 :: (rest ++ Y) from rfl,
                        hunL Y, hun0]
                    · rw [hun0]; exact unreadable_price_poison
                · exfalso
                  push_neg at hex
                  have hmods : ∀ i, i ≤ rest.length →
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                        (rest.take i)) ≠ 2 := fun i hi => hex i hi
                  have hend := priceWalk_inside rest rest.length le_rfl hmods
                  rw [List.take_length] at hend
                  rw [List.foldl_cons, rpnCondStep_base_price] at hbase
                  rw [hbase, rcMode_pack] at hend
                  omega
          · by_cases ht6 : t = 6
            · subst ht6
              cases hp : parseRpn rest.length rest with
              | some pr =>
                  obtain ⟨φ, r1⟩ := pr
                  obtain ⟨blk, heq, hblk⟩ := parseRpn_strip rest.length rest hp
                  subst heq
                  obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_trade_block hblk
                  have hr1 : r1.length ≤ N := by
                    have hlt := parseRpn_length_lt _ _ _ _ hp
                    simp only [List.length_append] at hA
                    omega
                  have hbase1 : List.foldl rpnCondStep (rcPack 0 0 0) r1 =
                      rcPack 0 0 0 := by
                    rw [List.foldl_cons, rpnCondStep_base_trade,
                      List.foldl_append, hwalk] at hbase
                    exact hbase
                  have hA1 : (6 : ℕ) :: (blk ++ r1) = (6 :: blk) ++ r1 := by simp
                  have hC := UnRpnContractsTo.tradeChunk hblk
                  rcases ih r1 hr1 hbase1 with hIH | ⟨hstop, hU⟩
                  · exact Or.inl (((hC.append hIH).of_eq hA1.symm rfl).self)
                  · refine Or.inr ⟨?_, ?_⟩
                    · rw [hA1]; exact UnRpnStops.cons_chunk hC hstop
                    · rw [unRpn_trade_chunk_block hblk r1,
                        show (6 :: Encodable.encode φ :: unRpn r1) =
                          [6, Encodable.encode φ] ++ unRpn r1 from rfl]
                      exact hU.cons_chunk (by simp [freezeMode4Step])
              | none =>
                  have hun0 : unRpn (6 :: rest) = [6, 0] := by
                    rw [unRpn, List.length_cons, unRpnTokens_cons,
                      if_neg (by norm_num), if_pos rfl, hp]
                  by_cases hex : ∃ k, k ≤ rest.length ∧
                      rcMode (List.foldl rpnCondStep (rcPack 4 1 0)
                        (rest.take k)) = 0
                  · classical
                    obtain ⟨hk₀le, hk₀mode⟩ := Nat.find_spec hex
                    set k₀ := Nat.find hex with hk₀def
                    have hfirst : ∀ i < k₀,
                        rcMode (List.foldl rpnCondStep (rcPack 4 1 0)
                          (rest.take i)) ≠ 0 := fun i hi hmode =>
                      Nat.find_min hex hi ⟨by omega, hmode⟩
                    obtain ⟨hk₀pos, hW, hinside⟩ := tradeWalk_first_exit rest k₀
                      hk₀le hfirst hk₀mode
                    have htakelen : (rest.take k₀).length = k₀ := by
                      rw [List.length_take]; omega
                    have hconv := parse_of_tradeRunWalk k₀ (rest.take k₀)
                      (le_of_eq htakelen) 0 0
                      (by rw [if_pos rfl]; simpa using hW)
                      (by
                        intro k hk
                        rw [htakelen] at hk
                        rw [List.take_take, min_eq_left (le_of_lt hk)]
                        exact ⟨(hinside k hk).1, (hinside k hk).2.1⟩)
                    rcases hconv with ⟨φu, hφu⟩ | hpoison
                    · exfalso
                      rw [← List.take_append_drop k₀ rest] at hp
                      rw [parseRpn_block_head hφu (rest.drop k₀) (by
                        simp only [List.length_append]; omega)] at hp
                      simp at hp
                    · have hunL : ∀ Y, unRpn (6 :: (rest ++ Y)) = [6, 0] := fun Y => by
                        rw [unRpn, List.length_cons, unRpnTokens_cons,
                          if_neg (by norm_num), if_pos rfl,
                          show rest ++ Y = rest.take k₀ ++ (rest.drop k₀ ++ Y) by
                            rw [← List.append_assoc, List.take_append_drop],
                          hpoison _ _]
                      refine Or.inr ⟨fun Y => ?_, ?_⟩
                      · rw [show (6 : ℕ) :: rest ++ Y = 6 :: (rest ++ Y) from rfl,
                          hunL Y, hun0]
                      · rw [hun0]; exact unreadable_trade_poison
                  · exfalso
                    push_neg at hex
                    have hmods : ∀ i, i ≤ rest.length →
                        rcMode (List.foldl rpnCondStep (rcPack 4 1 0)
                          (rest.take i)) ≠ 0 := fun i hi => hex i hi
                    have hend := tradeWalk_inside rest rest.length le_rfl hmods
                    rw [List.take_length] at hend
                    rw [List.foldl_cons, rpnCondStep_base_trade] at hbase
                    rw [hbase, rcMode_pack] at hend
                    omega
            · by_cases ht1 : t = 1 ∨ t = 7
              · match rest with
                | [] =>
                    exfalso
                    rw [List.foldl_cons, List.foldl_nil] at hbase
                    rcases ht1 with rfl | rfl
                    · rw [rpnCondStep_base_one] at hbase
                      have := congrArg rcMode hbase
                      rw [rcMode_pack, rcMode_pack] at this
                      exact absurd this (by norm_num)
                    · rw [rpnCondStep_base_seven] at hbase
                      have := congrArg rcMode hbase
                      rw [rcMode_pack, rcMode_pack] at this
                      exact absurd this (by norm_num)
                | c :: r =>
                    have hr : r.length ≤ N := by
                      simp only [List.length_cons] at hA
                      omega
                    have hstep1 : rpnCondStep (rcPack 0 0 0) t =
                        rcPack (if t = 1 then 3 else 5) 0 0 := by
                      rcases ht1 with rfl | rfl <;> simp [rpnCondStep_base]
                    have hstep2 :
                        rpnCondStep (rcPack (if t = 1 then 3 else 5) 0 0) c =
                          rcPack 0 0 0 :=
                      rpnCondStep_opaque (by split <;> simp) 0 0 c
                    have hbaseR : List.foldl rpnCondStep (rcPack 0 0 0) r =
                        rcPack 0 0 0 := by
                      rw [List.foldl_cons, hstep1, List.foldl_cons, hstep2] at hbase
                      exact hbase
                    have hAp : t :: c :: r = [t, c] ++ r := rfl
                    have hC := UnRpnContractsTo.payload t c ht1
                    rcases ih r hr hbaseR with hIH | ⟨hstop, hU⟩
                    · exact Or.inl (((hC.append hIH).of_eq hAp.symm rfl).self)
                    · refine Or.inr ⟨?_, ?_⟩
                      · rw [hAp]; exact UnRpnStops.cons_chunk hC hstop
                      · rw [unRpn_payload_chunk t c ht1 r,
                          show (t :: c :: unRpn r) = [t, c] ++ unRpn r from rfl]
                        exact hU.cons_chunk (by
                          rcases ht1 with rfl | rfl <;> simp [freezeMode4Step])
              · push_neg at ht1
                have hrest : rest.length ≤ N := by omega
                have hstep := rpnCondStep_base_other t ht0 ht1.1 ht6 ht1.2
                have hbaseR : List.foldl rpnCondStep (rcPack 0 0 0) rest =
                    rcPack 0 0 0 := by
                  rw [List.foldl_cons, hstep] at hbase
                  exact hbase
                have hAs : t :: rest = [t] ++ rest := rfl
                have hC := UnRpnContractsTo.single t ⟨ht0, ht1.1, ht6, ht1.2⟩
                rcases ih rest hrest hbaseR with hIH | ⟨hstop, hU⟩
                · exact Or.inl (((hC.append hIH).of_eq hAs.symm rfl).self)
                · refine Or.inr ⟨?_, ?_⟩
                  · rw [hAs]; exact UnRpnStops.cons_chunk hC hstop
                  · rw [unRpn_single_chunk t ⟨ht0, ht1.1, ht6, ht1.2⟩ rest,
                      show (t :: unRpn rest) = [t] ++ unRpn rest from rfl]
                    exact hU.cons_chunk (by
                      simp [freezeMode4Step, ht0, ht1.1, ht6, ht1.2])

/-! ### Both-poison agreement -/

/-- Outputs agree up to a common unreadable failure. -/
def FrameAgree (a b : List ℕ) : Prop :=
  a = b ∨ (Unreadable a ∧ Unreadable b)

lemma Unreadable.append_right {u : List ℕ} (h : Unreadable u) (v : List ℕ) :
    Unreadable (u ++ v) := by
  intro mp stack trades hmp
  rw [EF.streamReadFrom_append, h mp stack trades hmp, EF.streamReadFrom_none]

lemma FrameAgree.cons_chunk {C a b : List ℕ}
    (hC : List.foldl freezeMode4Step 0 C = 0) (h : FrameAgree a b) :
    FrameAgree (C ++ a) (C ++ b) := by
  rcases h with rfl | ⟨ha, hb⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨ha.cons_chunk hC, hb.cons_chunk hC⟩

lemma strategyOfTokens_of_deserializeTrades_none {a : List ℕ}
    (h : deserializeTrades a = none) (n : ℕ) :
    (strategyOfTokens n a).trades = [] := by
  unfold strategyOfTokens
  split
  · rfl
  · next trades hdecode =>
      rw [h] at hdecode
      exact absurd hdecode (by simp)

lemma FrameAgree.strategyOfTokens_trades_eq {a b : List ℕ} (h : FrameAgree a b)
    (n : ℕ) : (strategyOfTokens n a).trades = (strategyOfTokens n b).trades := by
  rcases h with rfl | ⟨ha, hb⟩
  · rfl
  · rw [strategyOfTokens_of_deserializeTrades_none ha.deserializeTrades_eq_none,
      strategyOfTokens_of_deserializeTrades_none hb.deserializeTrades_eq_none]

/-- An undecodable sentence code poisons a price chunk. -/
lemma unreadable_price_code {c : ℕ}
    (hc : Encodable.decode (α := Sentence) c = none) : Unreadable [0, c] := by
  intro mp stack trades hmp
  obtain ⟨m, pend⟩ := mp
  simp only at hmp
  subst hmp
  simp [EF.streamReadFrom, EF.streamStep, hc]

lemma unreadable_cons_price {c : ℕ}
    (hc : Encodable.decode (α := Sentence) c = none) (v : List ℕ) :
    Unreadable (0 :: c :: v) :=
  (unreadable_price_code hc).append_right v

/-- The conditional-ratio expansion is a price chunk over the conjunction code. -/
lemma rawConditioningRatioTokens_eq_price_head (fc ψc day : ℕ) (ε : ℚ) :
    rawConditioningRatioTokens fc ψc day ε =
      0 :: conjunctionCode fc ψc :: day ::
        (rawLowerSafeRecipTokens (rawPriceTokens ψc day) ε ++ [3]) := by
  simp [rawConditioningRatioTokens, rawMulTokens, rawPriceTokens]

/-- A poisoned run stays poisoned under the conjunction shell. -/
lemma parseRpn_cons_and_poison {u : List ℕ}
    (hu : ∀ fuel tail, parseRpn fuel (u ++ tail) = none) (Z : List ℕ) (fuel : ℕ) :
    parseRpn fuel (3 :: (u ++ Z)) = none := by
  cases fuel with
  | zero => rfl
  | succ f =>
      rw [parseRpn_cons, if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_pos rfl, hu f Z]
      rfl

lemma unRpn_cons_and_poison {u : List ℕ}
    (hu : ∀ fuel tail, parseRpn fuel (u ++ tail) = none) (Z : List ℕ) :
    unRpn (0 :: (3 :: (u ++ Z))) = [0, 0] := by
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
    parseRpn_cons_and_poison hu Z]

/-- The frame emission, exposed as a price chunk over the conjunction shell. -/
lemma rpnFrameEmit_eq_price_head (second : Bool) (blk : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (buf : List ℕ) :
    rpnFrameEmit second blk ε day bc ibc buf =
      0 :: ((3 :: buf ++ blk) ++
        (day :: (rawLowerSafeRecipTokens (rpnFramePriceSym blk day) ε ++ [3] ++
          (if second then
            rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ)))
              (rawMulTokens
                (rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate bc ibc)))
                [7, 0])
          else rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate bc ibc))) ++
          [8] ++ 8 :: 6 :: (if second then blk else 3 :: buf ++ blk)))) := by
  cases second <;>
    simp [rpnFrameEmit, rpnFrameRatioSym, rpnFramePriceSym, rawMulTokens,
      List.append_assoc]

/-- **The symbol side poisons at a malformed trade run.** -/
lemma unRpn_rpnFrameEmit_poison (second : Bool) (blk : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) {u : List ℕ}
    (hu : ∀ fuel tail, parseRpn fuel (u ++ tail) = none) (Y : List ℕ) :
    unRpn (rpnFrameEmit second blk ε day bc ibc u ++ Y) = [0, 0] := by
  obtain ⟨W, hW⟩ : ∃ W, rpnFrameEmit second blk ε day bc ibc u =
      0 :: ((3 :: u ++ blk) ++ W) :=
    ⟨_, rpnFrameEmit_eq_price_head second blk ε day bc ibc u⟩
  rw [hW, show ((0 : ℕ) :: ((3 :: u ++ blk) ++ W)) ++ Y =
    0 :: (3 :: (u ++ (blk ++ (W ++ Y)))) by simp]
  exact unRpn_cons_and_poison hu _

/-- **The token side poisons at a malformed trade run**: the expanded body carries the
undecodable price code `conjunctionCode 0 ⌜ψ⌝`. -/
lemma unreadable_conditioningFrameTokenOutput_poison (second : Bool)
    (ψ : Sentence) (day : ℕ) (ε : ℚ) (bc ibc : ℕ) :
    Unreadable (conditioningFrameTokenOutput second (Encodable.encode ψ) day ε
      bc ibc [6, 0]) := by
  have hnone : Encodable.decode (α := Sentence)
      (conjunctionCode 0 (Encodable.encode ψ)) = none :=
    conjunctionCode_decode_none decode_zero_sentence
  rw [conditioningFrameTokenOutput_trade second (Encodable.encode ψ) day ε bc ibc
    0 []]
  cases second <;>
    · simp only [if_true, rawLocallyGatedBetaBodyTokens,
        rawLocallyGatedSecondBodyTokens, rawConditioningRatioTokens_eq_price_head,
        List.cons_append]
      exact unreadable_cons_price hnone _

/-! ### The prefix-contraction form of the frame agreement -/

/-- The frame pass's **prefix** invariant: the symbol-level output contracts to the
token-model output ahead of *any* continuation, or its first poisoned chunk stops the
contraction outright and both sides are unreadable.  This is the form the two-leg join
needs, by the append fact recorded in the module header. -/
def FrameContract (A B : List ℕ) : Prop :=
  UnRpnContractsTo A B ∨ (UnRpnStops A ∧ Unreadable (unRpn A) ∧ Unreadable B)

lemma FrameContract.frameAgree {A B : List ℕ} (h : FrameContract A B) :
    FrameAgree (unRpn A) B := by
  rcases h with hC | ⟨-, hU, hB⟩
  · refine Or.inl ?_
    have := hC []
    simpa [unRpn_nil] using this
  · exact Or.inr ⟨hU, hB⟩

lemma FrameContract.cons_chunk {C P A B : List ℕ} (hC : UnRpnContractsTo C P)
    (hF : List.foldl freezeMode4Step 0 P = 0) (h : FrameContract A B) :
    FrameContract (C ++ A) (P ++ B) := by
  rcases h with hA | ⟨hstop, hU, hB⟩
  · exact Or.inl (hC.append hA)
  · refine Or.inr ⟨UnRpnStops.cons_chunk hC hstop, ?_, hB.cons_chunk hF⟩
    rw [hC A]
    exact hU.cons_chunk hF

lemma _root_.LogicalInduction.UnRpnContractsTo.frameAgree_chunk {C P A B : List ℕ}
    (hC : UnRpnContractsTo C P) (hF : List.foldl freezeMode4Step 0 P = 0)
    (h : FrameAgree (unRpn A) B) :
    FrameAgree (unRpn (C ++ A)) (P ++ B) := by
  rw [hC A]
  exact h.cons_chunk hF

/-- A stream every extension of which contracts to the price poison stops, unreadably. -/
lemma FrameContract.of_poison {A B : List ℕ}
    (hA : ∀ r, unRpn (A ++ r) = [0, 0]) (hB : Unreadable B) : FrameContract A B := by
  have h0 : unRpn A = [0, 0] := by simpa using hA []
  exact Or.inr ⟨fun r => by rw [hA, h0], by rw [h0]; exact unreadable_price_poison, hB⟩

/-- Mode `0` is reachable only in the fully reset state. -/
lemma rpnCondStep_eq_base_of_mode_zero {st t : ℕ}
    (h : rcMode (rpnCondStep st t) = 0) : rpnCondStep st t = rcPack 0 0 0 := by
  rw [rpnCondStep] at h ⊢
  split_ifs at h ⊢ <;> simp_all

/-- The run automaton is in base mode exactly when its packed state is fully reset. -/
lemma foldl_rpnCondStep_eq_base_of_mode_zero (ts : List ℕ)
    (h : rcMode (List.foldl rpnCondStep (rcPack 0 0 0) ts) = 0) :
    List.foldl rpnCondStep (rcPack 0 0 0) ts = rcPack 0 0 0 := by
  rcases List.eq_nil_or_concat' ts with rfl | ⟨v, x, rfl⟩
  · rfl
  · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at h ⊢
    exact rpnCondStep_eq_base_of_mode_zero h

-- `split_ifs` over `rcModeF`'s two-level branch cascade generates enough goals to
-- exceed the default heartbeat budget.
set_option maxHeartbeats 4000000 in
/-- A price-run mode step never returns to base and never enters a trade run. -/
lemma rcModeF_price_ne {m c t : ℕ} (h : m = 1 ∨ m = 6 ∨ m = 8) :
    rcModeF m c t ≠ 0 ∧ rcModeF m c t ≠ 4 ∧ rcModeF m c t ≠ 7 ∧
      rcModeF m c t ≠ 9 := by
  rcases h with rfl | rfl | rfl <;> rw [rcModeF] <;> split_ifs <;>
    first
      | exact absurd ‹False› not_false
      | refine ⟨by omega, by omega, by omega, by omega⟩

/-- Inside a price run the automaton stays in the run or reaches the day slot; it never
returns to base and never enters a trade run. -/
lemma rcMode_step_of_price_run {st t : ℕ}
    (h : rcMode st = 1 ∨ rcMode st = 6 ∨ rcMode st = 8) :
    rcMode (rpnCondStep st t) ≠ 0 ∧ rcMode (rpnCondStep st t) ≠ 4 ∧
      rcMode (rpnCondStep st t) ≠ 7 ∧ rcMode (rpnCondStep st t) ≠ 9 := by
  rw [rcMode_step_eq]
  exact rcModeF_price_ne h

/-! ### The frame-pass master commutation -/

/-- **Whole-stream agreement for the frame pass**, in joint form: the unconditional
`FrameAgree` statement and — under the source's base-mode invariant, which is what the
acceptance gate tests — the stronger prefix form `FrameContract`.  Stated jointly because
a single chunk induction proves both: every chunk case admitting a prefix contraction is
the one admitting the equality, and the base-mode hypothesis discharges the three that do
not (a truncated price chunk, a run that never exits, a bare payload tag).
Paper node: `thm:scon` -/
lemma frameJoint_unRpn_rpnFrameOutput (second : Bool) (blkψ : List ℕ)
    {ψn : Sentence} (hblkψ : parseRpn blkψ.length blkψ = some (ψn, []))
    (ε : ℚ) (day bc ibc : ℕ) : ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    FrameAgree (unRpn (rpnFrameOutput second blkψ ε day bc ibc ts))
      (conditioningFrameTokenOutput second (Encodable.encode ψn) day ε bc ibc
        (unRpn ts)) ∧
    (List.foldl rpnCondStep (rcPack 0 0 0) ts = rcPack 0 0 0 →
      FrameContract (rpnFrameOutput second blkψ ε day bc ibc ts)
        (conditioningFrameTokenOutput second (Encodable.encode ψn) day ε bc ibc
          (unRpn ts))) := by
  intro N
  induction N with
  | zero =>
      intro ts hts
      obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hA : rpnFrameOutput second blkψ ε day bc ibc [] = [] := by
        simp [rpnFrameOutput, rpnFrameRun]
      have hB : conditioningFrameTokenOutput second (Encodable.encode ψn) day ε bc
          ibc (unRpn []) = [] := by
        simp [conditioningFrameTokenOutput, conditioningFrameTokenRun, unRpn_nil]
      exact ⟨Or.inl (by rw [hA, hB, unRpn_nil]),
        fun _ => Or.inl (by rw [hA, hB]; exact UnRpnContractsTo.nil)⟩
  | succ N ih =>
      intro ts hts
      match ts with
      | [] =>
          have hA : rpnFrameOutput second blkψ ε day bc ibc [] = [] := by
            simp [rpnFrameOutput, rpnFrameRun]
          have hB : conditioningFrameTokenOutput second (Encodable.encode ψn) day ε
              bc ibc (unRpn []) = [] := by
            simp [conditioningFrameTokenOutput, conditioningFrameTokenRun, unRpn_nil]
          exact ⟨Or.inl (by rw [hA, hB, unRpn_nil]),
            fun _ => Or.inl (by rw [hA, hB]; exact UnRpnContractsTo.nil)⟩
      | t :: rest =>
          simp only [List.length_cons] at hts
          by_cases ht0 : t = 0
          · subst ht0
            cases hp : parseRpn rest.length rest with
            | some pr =>
                obtain ⟨φ, r1⟩ := pr
                obtain ⟨blk, heq, hblk⟩ := parseRpn_strip rest.length rest hp
                obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_price_block hblk
                have hcopyBlk := rpnFrameRun_copy_of_modes second blkψ ε day bc ibc
                  (rcPack 1 1 0) [] blk (fun k hk => by
                    have := hinv k hk; omega)
                match r1 with
                | [] =>
                    rw [List.append_nil] at heq
                    subst heq
                    have hrun : rpnFrameRun second blkψ ε day bc ibc
                        (rcPack 0 0 0, []) (0 :: rest) =
                      ((rcPack 2 0 rest.length,
                        rpnCondBufFold (rcPack 1 1 0) [] rest), 0 :: rest) := by
                      rw [rpnFrameRun_cons, rpnCondStep_base_price, rpnCondBuf_base,
                        hcopyBlk, hwalk]
                      simp [rpnFrameEmitAt]
                    have hout : rpnFrameOutput second blkψ ε day bc ibc
                        (0 :: rest) = 0 :: rest := by
                      rw [rpnFrameOutput, hrun]
                      simp
                    have hun : unRpn (0 :: rest) = [0, Encodable.encode φ] := by
                      rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
                        hblk]
                    refine ⟨?_, fun hbase => ?_⟩
                    · rw [hout, hun, conditioningFrameTokenOutput_price_pair]
                      exact Or.inl rfl
                    · exfalso
                      rw [List.foldl_cons, rpnCondStep_base_price, hwalk] at hbase
                      have := congrArg rcMode hbase
                      simp at this
                | d :: r2 =>
                    subst heq
                    have hstD : rpnCondStep (rcPack 2 0 blk.length) d =
                        rcPack 0 0 0 := rpnCondStep_day blk.length d
                    have hCeq : (0 : ℕ) :: (blk ++ d :: r2) =
                        (0 :: (blk ++ [d])) ++ r2 := by simp
                    have hstate : List.foldl rpnCondStep (rcPack 0 0 0)
                        (0 :: (blk ++ [d])) = rcPack 0 0 0 := by
                      rw [List.foldl_cons, rpnCondStep_base_price,
                        List.foldl_append, hwalk]
                      simpa using hstD
                    have hbuf : rpnCondBufFold (rcPack 0 0 0) []
                        (0 :: (blk ++ [d])) = [] :=
                      rpnCondBufFold_reset _ _ _ (by simp) (by rw [hstate]; simp)
                    have hrunC : rpnFrameRun second blkψ ε day bc ibc
                        (rcPack 0 0 0, []) (0 :: (blk ++ [d])) =
                      ((rcPack 0 0 0, []), 0 :: (blk ++ [d])) := by
                      rw [rpnFrameRun_cons, rpnCondStep_base_price,
                        rpnCondBuf_base, rpnFrameRun_append]
                      simp only
                      rw [hcopyBlk, hwalk, rpnFrameRun_cons, hstD]
                      simp [rpnFrameEmitAt, rpnCondBuf, hstD]
                    have hout : rpnFrameOutput second blkψ ε day bc ibc
                        (0 :: (blk ++ d :: r2)) =
                      (0 :: (blk ++ [d])) ++
                        rpnFrameOutput second blkψ ε day bc ibc r2 := by
                      rw [hCeq, rpnFrameOutput_append_base second blkψ ε day bc ibc
                        _ _ hstate hbuf, hrunC]
                    have htok : conditioningFrameTokenOutput second
                        (Encodable.encode ψn) day ε bc ibc
                        (unRpn (0 :: (blk ++ d :: r2))) =
                      [0, Encodable.encode φ, d] ++
                        conditioningFrameTokenOutput second (Encodable.encode ψn)
                          day ε bc ibc (unRpn r2) := by
                      rw [unRpn_price_chunk_block hblk d r2,
                        conditioningFrameTokenOutput_price]
                      rfl
                    have hC : UnRpnContractsTo (0 :: (blk ++ [d]))
                        [0, Encodable.encode φ, d] :=
                      (UnRpnContractsTo.priceChunk hblk d).of_eq (by simp) rfl
                    have hF : List.foldl freezeMode4Step 0
                        [0, Encodable.encode φ, d] = 0 := by
                      simp [freezeMode4Step]
                    have hr2 : r2.length ≤ N := by
                      have hlt := parseRpn_length_lt _ _ _ _ hp
                      simp only [List.length_cons] at hlt
                      omega
                    refine ⟨?_, fun hbase => ?_⟩
                    · rw [hout, htok]
                      exact hC.frameAgree_chunk hF (ih r2 hr2).1
                    · have hbaseR : List.foldl rpnCondStep (rcPack 0 0 0) r2 =
                          rcPack 0 0 0 := by
                        rw [hCeq, List.foldl_append, hstate] at hbase
                        exact hbase
                      rw [hout, htok]
                      exact FrameContract.cons_chunk hC hF ((ih r2 hr2).2 hbaseR)
            | none =>
                have hun0 : unRpn (0 :: rest) = [0, 0] := by
                  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl, hp]
                have htokPoison : Unreadable (conditioningFrameTokenOutput second
                    (Encodable.encode ψn) day ε bc ibc (unRpn (0 :: rest))) := by
                  rw [hun0, conditioningFrameTokenOutput_price_pair]
                  exact unreadable_price_poison
                by_cases hex : ∃ k, k < rest.length ∧
                    rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                      (rest.take k)) = 2
                · classical
                  obtain ⟨hk₀lt, hk₀mode⟩ := Nat.find_spec hex
                  set k₀ := Nat.find hex with hk₀def
                  have hfirst : ∀ i < k₀,
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                        (rest.take i)) ≠ 2 := fun i hi hmode =>
                    Nat.find_min hex hi ⟨by omega, hmode⟩
                  obtain ⟨hk₀pos, hW, hinside⟩ := priceWalk_first_exit rest k₀
                    (le_of_lt hk₀lt) hfirst hk₀mode
                  have htakelen : (rest.take k₀).length = k₀ := by
                    rw [List.length_take]; omega
                  have hconv := parse_of_priceRunWalk k₀ (rest.take k₀)
                    (le_of_eq htakelen) 0 0
                    (by rw [if_pos rfl, htakelen]; simpa using hW)
                    (by
                      intro k hk
                      rw [htakelen] at hk
                      rw [List.take_take, min_eq_left (le_of_lt hk)]
                      exact ⟨(hinside k hk).1, (hinside k hk).2.1⟩)
                  rcases hconv with ⟨φu, hφu⟩ | hpoison
                  · exfalso
                    rw [← List.take_append_drop k₀ rest] at hp
                    rw [parseRpn_block_head hφu (rest.drop k₀) (by
                      simp only [List.length_append]; omega)] at hp
                    simp at hp
                  · have hucopy := rpnFrameRun_copy_of_modes second blkψ ε day bc ibc
                      (rcPack 1 1 0) [] (rest.take k₀) (by
                        intro k hk
                        rw [htakelen] at hk
                        rw [List.take_take, min_eq_left (le_of_lt hk)]
                        have := (hinside k hk).1
                        omega)
                    have hrun2 : (rpnFrameRun second blkψ ε day bc ibc
                        (rcPack 0 0 0, []) (0 :: rest)).2 =
                      0 :: (rest.take k₀ ++
                        (rpnFrameRun second blkψ ε day bc ibc
                          (List.foldl rpnCondStep (rcPack 1 1 0) (rest.take k₀),
                           rpnCondBufFold (rcPack 1 1 0) [] (rest.take k₀))
                          (rest.drop k₀)).2) := by
                      conv_lhs =>
                        rw [show rest = rest.take k₀ ++ rest.drop k₀ from
                          (List.take_append_drop k₀ rest).symm]
                      rw [rpnFrameRun_cons, rpnCondStep_base_price, rpnCondBuf_base,
                        rpnFrameRun_append]
                      simp [hucopy, rpnFrameEmitAt]
                    have hunL : ∀ Y, unRpn (0 :: (rest.take k₀ ++ Y)) =
                        [0, 0] := fun Y => by
                      rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
                        hpoison _ _]
                    have hall : ∀ r, unRpn (rpnFrameOutput second blkψ ε day bc ibc
                        (0 :: rest) ++ r) = [0, 0] := by
                      intro r
                      rw [rpnFrameOutput, hrun2]
                      simpa using hunL _
                    have hcontract := FrameContract.of_poison hall htokPoison
                    exact ⟨hcontract.frameAgree, fun _ => hcontract⟩
                · have hmodes : ∀ k < rest.length,
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                        (rest.take k)) ≠ 0 ∧
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                        (rest.take k)) ≠ 4 ∧
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                        (rest.take k)) ≠ 7 ∧
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                        (rest.take k)) ≠ 9 := by
                    intro k hk
                    have hmods : ∀ i, i ≤ k →
                        rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                          (rest.take i)) ≠ 2 := fun i hi hmode =>
                      hex ⟨i, by omega, hmode⟩
                    have := priceWalk_inside rest k (by omega) hmods
                    omega
                  have hcopy := rpnFrameRun_copy_of_modes second blkψ ε day bc ibc
                    (rcPack 1 1 0) [] rest hmodes
                  have hmodeEnd :
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) rest) ≠ 0 ∧
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) rest) ≠ 4 ∧
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) rest) ≠ 7 ∧
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) rest) ≠ 9 := by
                    rcases List.eq_nil_or_concat' rest with hnil | ⟨v, x, hvx⟩
                    · rw [hnil]; simp
                    · have hlen : rest.length = v.length + 1 := by
                        rw [hvx]; simp
                      have hmods : ∀ i, i ≤ v.length →
                          rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                            (rest.take i)) ≠ 2 := fun i hi hmode =>
                        hex ⟨i, by omega, hmode⟩
                      have hv : rest.take v.length = v := by
                        rw [hvx, List.take_append_of_le_length le_rfl,
                          List.take_length]
                      have hmid := (priceWalk_inside rest v.length
                        (by omega) hmods).1
                      rw [hv] at hmid
                      have hstepv : List.foldl rpnCondStep (rcPack 1 1 0) rest =
                          rpnCondStep (List.foldl rpnCondStep (rcPack 1 1 0) v)
                            x := by
                        rw [hvx, List.foldl_append]; rfl
                      rw [hstepv]
                      have hnext := rcMode_step_of_price_run (t := x) hmid
                      omega
                  have hout : rpnFrameOutput second blkψ ε day bc ibc (0 :: rest) =
                      0 :: rest := by
                    rw [rpnFrameOutput, rpnFrameRun_cons, rpnCondStep_base_price,
                      rpnCondBuf_base, hcopy]
                    simp [rpnFrameEmitAt, hmodeEnd.2.1, hmodeEnd.2.2.1,
                      hmodeEnd.2.2.2]
                  refine ⟨?_, fun hbase => ?_⟩
                  · rw [hout, hun0, conditioningFrameTokenOutput_price_pair]
                    exact Or.inl rfl
                  · exfalso
                    rw [List.foldl_cons, rpnCondStep_base_price] at hbase
                    have := congrArg rcMode hbase
                    simp only [rcMode_pack] at this
                    omega
          · by_cases ht6 : t = 6
            · subst ht6
              cases hp : parseRpn rest.length rest with
              | some pr =>
                  obtain ⟨φ, r1⟩ := pr
                  obtain ⟨blk, heq, hblk⟩ := parseRpn_strip rest.length rest hp
                  subst heq
                  obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_trade_block hblk
                  have hCeq : (6 : ℕ) :: (blk ++ r1) = (6 :: blk) ++ r1 := by simp
                  have hstate : List.foldl rpnCondStep (rcPack 0 0 0) (6 :: blk) =
                      rcPack 0 0 0 := by
                    rw [List.foldl_cons, rpnCondStep_base_trade, hwalk]
                  have hbuf : rpnCondBufFold (rcPack 0 0 0) [] (6 :: blk) = [] :=
                    rpnCondBufFold_reset _ _ _ (by simp) (by rw [hstate]; simp)
                  have hrunC : rpnFrameRun second blkψ ε day bc ibc
                      (rcPack 0 0 0, []) (6 :: blk) =
                    ((rcPack 0 0 0, []),
                      rpnFrameEmit second blkψ ε day bc ibc blk) := by
                    rw [rpnFrameRun_cons, rpnCondStep_base_trade, rpnCondBuf_base,
                      rpnFrameRun_trade_block second blkψ ε day bc ibc hblk]
                    simp [rpnFrameEmitAt]
                  have hout : rpnFrameOutput second blkψ ε day bc ibc
                      (6 :: (blk ++ r1)) =
                    rpnFrameEmit second blkψ ε day bc ibc blk ++
                      rpnFrameOutput second blkψ ε day bc ibc r1 := by
                    rw [hCeq, rpnFrameOutput_append_base second blkψ ε day bc ibc
                      _ _ hstate hbuf, hrunC]
                  have htok : conditioningFrameTokenOutput second
                      (Encodable.encode ψn) day ε bc ibc
                      (unRpn (6 :: (blk ++ r1))) =
                    (if second then
                        rawLocallyGatedSecondBodyTokens (Encodable.encode φ)
                          (Encodable.encode ψn) day bc ibc ε ++
                          [8, 6, Encodable.encode ψn]
                      else
                        rawLocallyGatedBetaBodyTokens (Encodable.encode φ)
                          (Encodable.encode ψn) day bc ibc ε ++
                          [8, 6, conjunctionCode (Encodable.encode φ)
                            (Encodable.encode ψn)]) ++
                      conditioningFrameTokenOutput second (Encodable.encode ψn)
                        day ε bc ibc (unRpn r1) := by
                    rw [unRpn_trade_chunk_block hblk r1,
                      conditioningFrameTokenOutput_trade]
                  have hC : UnRpnContractsTo (rpnFrameEmit second blkψ ε day bc ibc blk)
                      (if second then
                          rawLocallyGatedSecondBodyTokens (Encodable.encode φ)
                            (Encodable.encode ψn) day bc ibc ε ++
                            [8, 6, Encodable.encode ψn]
                        else
                          rawLocallyGatedBetaBodyTokens (Encodable.encode φ)
                            (Encodable.encode ψn) day bc ibc ε ++
                            [8, 6, conjunctionCode (Encodable.encode φ)
                              (Encodable.encode ψn)]) :=
                    (rpnFrameEmit_contractsTo hblk hblkψ second day bc ibc ε).of_eq
                      rfl (by cases second <;> simp)
                  have hF : List.foldl freezeMode4Step 0
                      (if second then
                          rawLocallyGatedSecondBodyTokens (Encodable.encode φ)
                            (Encodable.encode ψn) day bc ibc ε ++
                            [8, 6, Encodable.encode ψn]
                        else
                          rawLocallyGatedBetaBodyTokens (Encodable.encode φ)
                            (Encodable.encode ψn) day bc ibc ε ++
                            [8, 6, conjunctionCode (Encodable.encode φ)
                              (Encodable.encode ψn)]) = 0 := by
                    cases second <;>
                      simp [rawLocallyGatedBetaBodyTokens,
                        rawLocallyGatedSecondBodyTokens,
                        rawConditioningRatioTokens, rawConditioningGateTokens,
                        rawPriceTokens, rawConstTokens, rawMulTokens,
                        rawAddTokens, rawMaxTokens, rawMinTokens,
                        rawSafeRecipTokens, rawAbsTokens, rawClip01Tokens,
                        rawLowerSafeRecipTokens, freezeMode4Step]
                  have hr1 : r1.length ≤ N := by
                    have hlt := parseRpn_length_lt _ _ _ _ hp
                    omega
                  refine ⟨?_, fun hbase => ?_⟩
                  · rw [hout, htok]
                    exact hC.frameAgree_chunk hF (ih r1 hr1).1
                  · have hbaseR : List.foldl rpnCondStep (rcPack 0 0 0) r1 =
                        rcPack 0 0 0 := by
                      rw [hCeq, List.foldl_append, hstate] at hbase
                      exact hbase
                    rw [hout, htok]
                    exact FrameContract.cons_chunk hC hF ((ih r1 hr1).2 hbaseR)
              | none =>
                  have hun0 : unRpn (6 :: rest) = [6, 0] := by
                    rw [unRpn, List.length_cons, unRpnTokens_cons,
                      if_neg (by norm_num), if_pos rfl, hp]
                  have htokenPoison := unreadable_conditioningFrameTokenOutput_poison
                    second ψn day ε bc ibc
                  by_cases hex : ∃ k, k ≤ rest.length ∧
                      rcMode (List.foldl rpnCondStep (rcPack 4 1 0)
                        (rest.take k)) = 0
                  · classical
                    obtain ⟨hk₀le, hk₀mode⟩ := Nat.find_spec hex
                    set k₀ := Nat.find hex with hk₀def
                    have hfirst : ∀ i < k₀,
                        rcMode (List.foldl rpnCondStep (rcPack 4 1 0)
                          (rest.take i)) ≠ 0 := fun i hi hmode =>
                      Nat.find_min hex hi ⟨by omega, hmode⟩
                    obtain ⟨hk₀pos, hW, hinside⟩ := tradeWalk_first_exit rest k₀
                      hk₀le hfirst hk₀mode
                    have htakelen : (rest.take k₀).length = k₀ := by
                      rw [List.length_take]; omega
                    have hconv := parse_of_tradeRunWalk k₀ (rest.take k₀)
                      (le_of_eq htakelen) 0 0
                      (by rw [if_pos rfl]; exact hW)
                      (by
                        intro k hk
                        rw [htakelen] at hk
                        rw [List.take_take, min_eq_left (le_of_lt hk)]
                        exact ⟨(hinside k hk).1, (hinside k hk).2.1⟩)
                    rcases hconv with ⟨φu, hφu⟩ | hpoison
                    · exfalso
                      rw [← List.take_append_drop k₀ rest] at hp
                      rw [parseRpn_block_head hφu (rest.drop k₀) (by
                        simp only [List.length_append]; omega)] at hp
                      simp at hp
                    · rcases List.eq_nil_or_concat' (rest.take k₀) with
                        hnil | ⟨u', last, hcat⟩
                      · exfalso
                        rw [hnil] at htakelen
                        simp at htakelen
                        omega
                      have hsilent := rpnFrameRun_silent second blkψ ε day bc ibc
                        (rcPack 4 1 0) [] u' (by
                          intro k hk
                          have hk' : k < k₀ := by
                            have : u'.length + 1 = k₀ := by
                              rw [← htakelen, hcat]; simp
                            omega
                          have hk1' : k + 1 < k₀ := by
                            have : u'.length + 1 = k₀ := by
                              rw [← htakelen, hcat]; simp
                            omega
                          have e1 : rest.take k = (rest.take k₀).take k := by
                            rw [List.take_take, min_eq_left (le_of_lt hk')]
                          have e2 : rest.take (k + 1) = (rest.take k₀).take (k + 1) := by
                            rw [List.take_take, min_eq_left (by omega)]
                          have hu'k : u'.take k = rest.take k := by
                            rw [e1, hcat, List.take_append_of_le_length (le_of_lt hk)]
                          have hu'k1 : u'.take (k + 1) = rest.take (k + 1) := by
                            rw [e2, hcat, List.take_append_of_le_length (by omega)]
                          rw [hu'k, hu'k1]
                          exact ⟨(hinside k hk').1, hfirst (k + 1) hk1'⟩)
                      have hu'eq : u' = rest.take (k₀ - 1) := by
                        have hlen : u'.length + 1 = k₀ := by
                          rw [← htakelen, hcat]; simp
                        rw [show k₀ - 1 = u'.length by omega,
                          show rest.take u'.length =
                              (rest.take k₀).take u'.length by
                            rw [List.take_take, min_eq_left (by omega)],
                          hcat, List.take_append_of_le_length le_rfl,
                          List.take_length]
                      have hstateU' : List.foldl rpnCondStep (rcPack 4 1 0) u' =
                          List.foldl rpnCondStep (rcPack 4 1 0)
                            (rest.take (k₀ - 1)) := by rw [hu'eq]
                      have hmodeU' :
                          rcMode (List.foldl rpnCondStep (rcPack 4 1 0) u') = 4 ∨
                          rcMode (List.foldl rpnCondStep (rcPack 4 1 0) u') = 7 ∨
                          rcMode (List.foldl rpnCondStep (rcPack 4 1 0) u') = 9 := by
                        rw [hstateU']
                        exact (hinside (k₀ - 1) (by omega)).1
                      have hstepLast :
                          rpnCondStep (List.foldl rpnCondStep (rcPack 4 1 0) u')
                            last = List.foldl rpnCondStep (rcPack 4 1 0)
                              (rest.take k₀) := by
                        conv_rhs => rw [hcat]
                        rw [List.foldl_append]
                        rfl
                      have hemitLast : rpnFrameEmitAt second blkψ ε day bc ibc
                          (List.foldl rpnCondStep (rcPack 4 1 0) u') ([] ++ u')
                          last =
                        rpnFrameEmit second blkψ ε day bc ibc (rest.take k₀) := by
                        rw [rpnFrameEmitAt,
                          if_neg (by rcases hmodeU' with h | h | h <;> simp [h]),
                          if_pos hmodeU', hstepLast, if_pos hk₀mode, hcat]
                        simp
                      have hrun2 : (rpnFrameRun second blkψ ε day bc ibc
                          (rcPack 0 0 0, []) (6 :: rest)).2 =
                        rpnFrameEmit second blkψ ε day bc ibc (rest.take k₀) ++
                          (rpnFrameRun second blkψ ε day bc ibc
                            (List.foldl rpnCondStep (rcPack 4 1 0) (rest.take k₀),
                             rpnCondBuf (List.foldl rpnCondStep (rcPack 4 1 0) u')
                               ([] ++ u') last)
                            (rest.drop k₀)).2 := by
                        conv_lhs =>
                          rw [show rest = rest.take k₀ ++ rest.drop k₀ from
                            (List.take_append_drop k₀ rest).symm]
                        rw [rpnFrameRun_cons, rpnFrameEmitAt_base_trade,
                          rpnCondStep_base_trade, rpnCondBuf_base,
                          rpnFrameRun_append]
                        simp only [List.nil_append]
                        rw [hcat, rpnFrameRun_append, hsilent]
                        simp only
                        rw [rpnFrameRun_cons, hemitLast]
                        simp only [rpnFrameRun_nil, List.nil_append,
                          List.append_assoc, hstepLast, hcat]
                      have hall : ∀ r, unRpn (rpnFrameOutput second blkψ ε day bc
                          ibc (6 :: rest) ++ r) = [0, 0] := by
                        intro r
                        rw [rpnFrameOutput, hrun2]
                        simpa using
                          unRpn_rpnFrameEmit_poison second blkψ ε day bc ibc
                            hpoison _
                      have htokPoison : Unreadable (conditioningFrameTokenOutput
                          second (Encodable.encode ψn) day ε bc ibc
                          (unRpn (6 :: rest))) := by
                        rw [hun0]; exact htokenPoison
                      have hcontract := FrameContract.of_poison hall htokPoison
                      exact ⟨hcontract.frameAgree, fun _ => hcontract⟩
                  · push_neg at hex
                    have hmodes : ∀ k < rest.length,
                        (rcMode (List.foldl rpnCondStep (rcPack 4 1 0)
                          (rest.take k)) = 4 ∨
                        rcMode (List.foldl rpnCondStep (rcPack 4 1 0)
                          (rest.take k)) = 7 ∨
                        rcMode (List.foldl rpnCondStep (rcPack 4 1 0)
                          (rest.take k)) = 9) ∧
                        rcMode (List.foldl rpnCondStep (rcPack 4 1 0)
                          (rest.take (k + 1))) ≠ 0 := by
                      intro k hk
                      have hmods : ∀ i, i ≤ k →
                          rcMode (List.foldl rpnCondStep (rcPack 4 1 0)
                            (rest.take i)) ≠ 0 := fun i hi =>
                        hex i (by omega)
                      exact ⟨(tradeWalk_inside rest k (by omega) hmods).1,
                        hex (k + 1) (by omega)⟩
                    have hsilent := rpnFrameRun_silent second blkψ ε day bc ibc
                      (rcPack 4 1 0) [] rest hmodes
                    have hmodeEnd :
                        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) rest) = 4 ∨
                        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) rest) = 7 ∨
                        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) rest) = 9 := by
                      have hmods : ∀ i, i ≤ rest.length →
                          rcMode (List.foldl rpnCondStep (rcPack 4 1 0)
                            (rest.take i)) ≠ 0 := fun i hi => hex i hi
                      have := (tradeWalk_inside rest rest.length le_rfl hmods).1
                      rwa [List.take_length] at this
                    have hout : rpnFrameOutput second blkψ ε day bc ibc
                        (6 :: rest) = [6] := by
                      rw [rpnFrameOutput, rpnFrameRun_cons,
                        rpnFrameEmitAt_base_trade, rpnCondStep_base_trade,
                        rpnCondBuf_base, hsilent]
                      rcases hmodeEnd with h | h <;> simp [h]
                    refine ⟨?_, fun hbase => ?_⟩
                    · refine Or.inr ⟨?_, ?_⟩
                      · rw [hout]
                        show Unreadable (unRpn [6])
                        rw [show unRpn [6] = [6, 0] from rfl]
                        exact unreadable_trade_poison
                      · rw [hun0]; exact htokenPoison
                    · exfalso
                      rw [List.foldl_cons, rpnCondStep_base_trade] at hbase
                      have := congrArg rcMode hbase
                      simp only [rcMode_pack] at this
                      omega
            · by_cases ht1 : t = 1
              · subst ht1
                match rest with
                | [] =>
                    have hout : rpnFrameOutput second blkψ ε day bc ibc [1] =
                        [1] := by
                      rw [rpnFrameOutput, rpnFrameRun_cons, rpnCondStep_base_one]
                      simp [rpnFrameEmitAt]
                    refine ⟨?_, fun hbase => ?_⟩
                    · rw [hout, show unRpn [1] = [1] from rfl,
                        conditioningFrameTokenOutput_one _ _ _ _ _ _ 1
                          (by norm_num)]
                      exact Or.inl rfl
                    · exfalso
                      rw [List.foldl_cons, rpnCondStep_base_one,
                        List.foldl_nil] at hbase
                      have := congrArg rcMode hbase
                      simp at this
                | c :: rest' =>
                    have hst2 : rpnCondStep (rcPack 3 0 0) c = rcPack 0 0 0 :=
                      rpnCondStep_opaque (Or.inl rfl) 0 0 c
                    have hstate : List.foldl rpnCondStep (rcPack 0 0 0) [1, c] =
                        rcPack 0 0 0 := by
                      rw [List.foldl_cons, rpnCondStep_base_one, List.foldl_cons,
                        hst2, List.foldl_nil]
                    have hbuf : rpnCondBufFold (rcPack 0 0 0) [] [1, c] = [] :=
                      rpnCondBufFold_reset _ _ _ (by simp)
                        (by rw [hstate]; simp)
                    have hrunC : rpnFrameRun second blkψ ε day bc ibc
                        (rcPack 0 0 0, []) [1, c] = ((rcPack 0 0 0, []), [1, c]) := by
                      rw [rpnFrameRun_cons, rpnCondStep_base_one, rpnCondBuf_base,
                        rpnFrameRun_cons, hst2]
                      simp [rpnFrameEmitAt, rpnCondBuf, hst2]
                    have hout : rpnFrameOutput second blkψ ε day bc ibc
                        (1 :: c :: rest') =
                      [1, c] ++ rpnFrameOutput second blkψ ε day bc ibc rest' := by
                      rw [show (1 : ℕ) :: c :: rest' = [1, c] ++ rest' from rfl,
                        rpnFrameOutput_append_base second blkψ ε day bc ibc
                          _ _ hstate hbuf, hrunC]
                    have htok : conditioningFrameTokenOutput second
                        (Encodable.encode ψn) day ε bc ibc (unRpn (1 :: c :: rest')) =
                      [1, c] ++ conditioningFrameTokenOutput second
                        (Encodable.encode ψn) day ε bc ibc (unRpn rest') := by
                      rw [unRpn_payload_chunk 1 c (Or.inl rfl) rest',
                        conditioningFrameTokenOutput_payload _ _ _ _ _ _ 1 c
                          (Or.inl rfl)]
                      rfl
                    have hC : UnRpnContractsTo [1, c] [1, c] :=
                      UnRpnContractsTo.payload 1 c (Or.inl rfl)
                    have hF : List.foldl freezeMode4Step 0 [1, c] = 0 := by
                      simp [freezeMode4Step]
                    have hr : rest'.length ≤ N := by
                      simp only [List.length_cons] at hts; omega
                    refine ⟨?_, fun hbase => ?_⟩
                    · rw [hout, htok]
                      exact hC.frameAgree_chunk hF (ih rest' hr).1
                    · have hbaseR : List.foldl rpnCondStep (rcPack 0 0 0) rest' =
                          rcPack 0 0 0 := by
                        rw [show (1 : ℕ) :: c :: rest' = [1, c] ++ rest' from rfl,
                          List.foldl_append, hstate] at hbase
                        exact hbase
                      rw [hout, htok]
                      exact FrameContract.cons_chunk hC hF ((ih rest' hr).2 hbaseR)
              · by_cases ht7 : t = 7
                · subst ht7
                  match rest with
                  | [] =>
                      have hout : rpnFrameOutput second blkψ ε day bc ibc [7] =
                          [7] := by
                        rw [rpnFrameOutput, rpnFrameRun_cons,
                          rpnCondStep_base_seven]
                        simp [rpnFrameEmitAt]
                      refine ⟨?_, fun hbase => ?_⟩
                      · rw [hout, show unRpn [7] = [7] from rfl,
                          conditioningFrameTokenOutput_one _ _ _ _ _ _ 7
                            (by norm_num)]
                        exact Or.inl rfl
                      · exfalso
                        rw [List.foldl_cons, rpnCondStep_base_seven,
                          List.foldl_nil] at hbase
                        have := congrArg rcMode hbase
                        simp at this
                  | c :: rest' =>
                      have hst2 : rpnCondStep (rcPack 5 0 0) c = rcPack 0 0 0 :=
                        rpnCondStep_opaque (Or.inr rfl) 0 0 c
                      have hstate : List.foldl rpnCondStep (rcPack 0 0 0) [7, c] =
                          rcPack 0 0 0 := by
                        rw [List.foldl_cons, rpnCondStep_base_seven,
                          List.foldl_cons, hst2, List.foldl_nil]
                      have hbuf : rpnCondBufFold (rcPack 0 0 0) [] [7, c] = [] :=
                        rpnCondBufFold_reset _ _ _ (by simp)
                          (by rw [hstate]; simp)
                      have hrunC : rpnFrameRun second blkψ ε day bc ibc
                          (rcPack 0 0 0, []) [7, c] =
                        ((rcPack 0 0 0, []), [7, c]) := by
                        rw [rpnFrameRun_cons, rpnCondStep_base_seven,
                          rpnCondBuf_base, rpnFrameRun_cons, hst2]
                        simp [rpnFrameEmitAt, rpnCondBuf, hst2]
                      have hout : rpnFrameOutput second blkψ ε day bc ibc
                          (7 :: c :: rest') =
                        [7, c] ++ rpnFrameOutput second blkψ ε day bc ibc rest' := by
                        rw [show (7 : ℕ) :: c :: rest' = [7, c] ++ rest' from rfl,
                          rpnFrameOutput_append_base second blkψ ε day bc ibc
                            _ _ hstate hbuf, hrunC]
                      have htok : conditioningFrameTokenOutput second
                          (Encodable.encode ψn) day ε bc ibc
                          (unRpn (7 :: c :: rest')) =
                        [7, c] ++ conditioningFrameTokenOutput second
                          (Encodable.encode ψn) day ε bc ibc (unRpn rest') := by
                        rw [unRpn_payload_chunk 7 c (Or.inr rfl) rest',
                          conditioningFrameTokenOutput_payload _ _ _ _ _ _ 7 c
                            (Or.inr rfl)]
                        rfl
                      have hC : UnRpnContractsTo [7, c] [7, c] :=
                        UnRpnContractsTo.payload 7 c (Or.inr rfl)
                      have hF : List.foldl freezeMode4Step 0 [7, c] = 0 := by
                        simp [freezeMode4Step]
                      have hr : rest'.length ≤ N := by
                        simp only [List.length_cons] at hts; omega
                      refine ⟨?_, fun hbase => ?_⟩
                      · rw [hout, htok]
                        exact hC.frameAgree_chunk hF (ih rest' hr).1
                      · have hbaseR : List.foldl rpnCondStep (rcPack 0 0 0) rest' =
                            rcPack 0 0 0 := by
                          rw [show (7 : ℕ) :: c :: rest' = [7, c] ++ rest' from rfl,
                            List.foldl_append, hstate] at hbase
                          exact hbase
                        rw [hout, htok]
                        exact FrameContract.cons_chunk hC hF ((ih rest' hr).2 hbaseR)
                · have hstep : rpnCondStep (rcPack 0 0 0) t = rcPack 0 0 0 :=
                    rpnCondStep_base_other t ht0 ht1 ht6 ht7
                  have hstate : List.foldl rpnCondStep (rcPack 0 0 0) [t] =
                      rcPack 0 0 0 := by simpa using hstep
                  have hbuf : rpnCondBufFold (rcPack 0 0 0) [] [t] = [] :=
                    rpnCondBufFold_reset _ _ _ (by simp) (by rw [hstate]; simp)
                  have hrunC : rpnFrameRun second blkψ ε day bc ibc
                      (rcPack 0 0 0, []) [t] = ((rcPack 0 0 0, []), [t]) := by
                    rw [rpnFrameRun_cons, hstep]
                    simp [rpnFrameEmitAt, ht6, rpnCondBuf, hstep]
                  have hout : rpnFrameOutput second blkψ ε day bc ibc (t :: rest) =
                      [t] ++ rpnFrameOutput second blkψ ε day bc ibc rest := by
                    rw [show t :: rest = [t] ++ rest from rfl,
                      rpnFrameOutput_append_base second blkψ ε day bc ibc
                        _ _ hstate hbuf, hrunC]
                  have htok : conditioningFrameTokenOutput second
                      (Encodable.encode ψn) day ε bc ibc (unRpn (t :: rest)) =
                    [t] ++ conditioningFrameTokenOutput second
                      (Encodable.encode ψn) day ε bc ibc (unRpn rest) := by
                    rw [unRpn_single_chunk t ⟨ht0, ht1, ht6, ht7⟩ rest,
                      conditioningFrameTokenOutput_single _ _ _ _ _ _ t ht0 ht1 ht6
                        ht7]
                    rfl
                  have hC : UnRpnContractsTo [t] [t] :=
                    UnRpnContractsTo.single t ⟨ht0, ht1, ht6, ht7⟩
                  have hF : List.foldl freezeMode4Step 0 [t] = 0 := by
                    simp [freezeMode4Step, ht0, ht1, ht6, ht7]
                  refine ⟨?_, fun hbase => ?_⟩
                  · rw [hout, htok]
                    exact hC.frameAgree_chunk hF (ih rest (by omega)).1
                  · have hbaseR : List.foldl rpnCondStep (rcPack 0 0 0) rest =
                        rcPack 0 0 0 := by
                      rw [show t :: rest = [t] ++ rest from rfl,
                        List.foldl_append, hstate] at hbase
                      exact hbase
                    rw [hout, htok]
                    exact FrameContract.cons_chunk hC hF
                      ((ih rest (by omega)).2 hbaseR)

/-- **Whole-stream agreement for the frame pass**: on every input stream the
contraction of the symbol-level frame output either *equals* the token-model frame
output of the contraction, or both are unreadable (which happens exactly at a malformed
trade run, where the token model expands a body around the poison code `0` and the
symbol side has no block to splice).  Either way the decoded strategies agree.
Paper node: `thm:scon` -/
lemma frameAgree_unRpn_rpnFrameOutput (second : Bool) (blkψ : List ℕ)
    {ψn : Sentence} (hblkψ : parseRpn blkψ.length blkψ = some (ψn, []))
    (ε : ℚ) (day bc ibc : ℕ) (ts : List ℕ) :
    FrameAgree (unRpn (rpnFrameOutput second blkψ ε day bc ibc ts))
      (conditioningFrameTokenOutput second (Encodable.encode ψn) day ε bc ibc
        (unRpn ts)) :=
  (frameJoint_unRpn_rpnFrameOutput second blkψ hblkψ ε day bc ibc ts.length ts
    le_rfl).1

/-- **The frame pass contracts as a prefix** whenever the source stream returns the run
automaton to base mode — the condition the acceptance gate tests.  This is the
primitive the two-leg join consumes, by the append fact recorded in the module header.
Paper node: `thm:scon` -/
lemma frameContract_rpnFrameOutput (second : Bool) (blkψ : List ℕ)
    {ψn : Sentence} (hblkψ : parseRpn blkψ.length blkψ = some (ψn, []))
    (ε : ℚ) (day bc ibc : ℕ) (ts : List ℕ)
    (hbase : List.foldl rpnCondStep (rcPack 0 0 0) ts = rcPack 0 0 0) :
    FrameContract (rpnFrameOutput second blkψ ε day bc ibc ts)
      (conditioningFrameTokenOutput second (Encodable.encode ψn) day ε bc ibc
        (unRpn ts)) :=
  (frameJoint_unRpn_rpnFrameOutput second blkψ hblkψ ε day bc ibc ts.length ts
    le_rfl).2 hbase

/-- **The frame-pass strategy-level equality**: the contraction of the symbol-level
frame output decodes to the same validated strategy as the token-model frame output of
the contraction — on every stream.
Paper node: `thm:scon` -/
lemma strategyOfTokens_unRpn_rpnFrameOutput_trades (second : Bool) (blkψ : List ℕ)
    {ψn : Sentence} (hblkψ : parseRpn blkψ.length blkψ = some (ψn, []))
    (ε : ℚ) (day bc ibc : ℕ) (n : ℕ) (ts : List ℕ) :
    (strategyOfTokens n
        (unRpn (rpnFrameOutput second blkψ ε day bc ibc ts))).trades =
      (strategyOfTokens n (conditioningFrameTokenOutput second
        (Encodable.encode ψn) day ε bc ibc (unRpn ts))).trades :=
  (frameAgree_unRpn_rpnFrameOutput second blkψ hblkψ ε day bc ibc
    ts).strategyOfTokens_trades_eq n

/-! ### Per-position view of the frame pass

The frame pass drives the price pass's automaton and buffer, so its per-position
views are literally `rpnCondControlAt` / `rpnCondWindow`; only the emission differs. -/

/-- One source-token segment of the frame rewrite. -/
def rpnFrameSegment (tf : ℕ → ℕ) (second : Bool) (blkψ : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (z : ℕ) : List ℕ :=
  rpnFrameEmitAt second blkψ ε day bc ibc
    (rpnCondControlAt tf z.unpair.1 z.unpair.2)
    (rpnCondWindow tf z.unpair.1 z.unpair.2) (tf z)

/-- **Range form of the frame rewrite**: over the per-position view of any stream, the
transducer's final state is the position control, its buffer the position window, and
its output the concatenation of the per-position segments. -/
lemma rpnFrameRun_range (tf : ℕ → ℕ) (second : Bool) (blkψ : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (n count : ℕ) :
    rpnFrameRun second blkψ ε day bc ibc (rcPack 0 0 0, [])
        ((List.range count).map fun j => tf (Nat.pair n j)) =
      ((rpnCondControlAt tf n count, rpnCondWindow tf n count),
        (List.range count).flatMap fun j =>
          rpnFrameSegment tf second blkψ ε day bc ibc (Nat.pair n j)) := by
  induction count with
  | zero => simp [rpnCondControlAt]
  | succ count ih =>
      rw [List.range_succ, List.map_append, rpnFrameRun_append, ih]
      simp only [List.map_cons, List.map_nil,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rw [show rpnFrameRun second blkψ ε day bc ibc
          (rpnCondControlAt tf n count, rpnCondWindow tf n count)
          [tf (Nat.pair n count)] =
        ((rpnCondStep (rpnCondControlAt tf n count) (tf (Nat.pair n count)),
          rpnCondBuf (rpnCondControlAt tf n count) (rpnCondWindow tf n count)
            (tf (Nat.pair n count))),
          rpnFrameEmitAt second blkψ ε day bc ibc (rpnCondControlAt tf n count)
            (rpnCondWindow tf n count) (tf (Nat.pair n count)) ++ []) from rfl]
      rw [rpnCondBuf_window,
        show rpnCondStep (rpnCondControlAt tf n count) (tf (Nat.pair n count)) =
          rpnCondControlAt tf n (count + 1) from rfl]
      simp only [List.append_nil]
      refine congrArg₂ Prod.mk rfl (congrArg₂ (· ++ ·) rfl ?_)
      rw [rpnFrameSegment]
      simp only [Nat.unpair_pair]

/-- The frame segment through the position control, in dispatch form (the shape the
poly-fueled assembly consumes: a three-way branch on the control mode, with the
emission fired at a trade-run exit). -/
lemma rpnFrameSegment_eq (tf : ℕ → ℕ) (second : Bool) (blkψ : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (n j : ℕ) :
    rpnFrameSegment tf second blkψ ε day bc ibc (Nat.pair n j) =
      if rcMode (rpnCondControlAt tf n j) = 0 ∧ tf (Nat.pair n j) = 6 then []
      else if rcMode (rpnCondControlAt tf n j) = 4 ∨
          rcMode (rpnCondControlAt tf n j) = 7 ∨
          rcMode (rpnCondControlAt tf n j) = 9 then
        (if rcMode (rpnCondControlAt tf n (j + 1)) = 0 then
          rpnFrameEmit second blkψ ε day bc ibc
            (rpnCondWindow tf n j ++ [tf (Nat.pair n j)])
        else [])
      else [tf (Nat.pair n j)] := by
  rw [rpnFrameSegment]
  simp only [Nat.unpair_pair, rpnFrameEmitAt]
  rfl

/-! ### The frame-pass emission certificate

Same assembly shape as `rpnGuardedConditionRun_polySegStream`: a mode dispatch off
`rpnCondScan`, the window copy by `concatVar` over `rcLen + 1` (the emission splices
`buf ++ [t]`, i.e. positions `j - rcLen .. j`), condition blocks and budget codes
constant per day, and the end-of-stream flush of a withheld trade tag. -/

/-- The (sentence-free) gated core of the frame-leg emission. -/
def rpnFrameCore (second : Bool) (bc ibc : ℕ) : List ℕ :=
  if second then
    rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ)))
      (rawMulTokens (rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate bc ibc)))
        [7, 0])
  else rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate bc ibc))

/-- The all-poly stretch of the frame-leg emission after its last sentence block. -/
def rpnFrameTailMid (second : Bool) (day bc ibc : ℕ) : List ℕ :=
  [day, 3, 5, 3, 3] ++ rpnFrameCore second bc ibc ++ [8, 8, 6]

lemma rpnFrameEmit_split (second : Bool) (blk : List ℕ) (ε : ℚ) (day bc ibc : ℕ)
    (buf : List ℕ) :
    rpnFrameEmit second blk ε day bc ibc buf =
      [0, 3] ++ buf ++ blk ++
        [day, 1, Encodable.encode (1 / ε : ℚ), 1, Encodable.encode (1 / ε : ℚ), 0] ++
        blk ++ rpnFrameTailMid second day bc ibc ++
        (if second then blk else [3] ++ buf ++ blk) := by
  cases second <;>
    simp [rpnFrameEmit, rpnFrameRatioSym, rpnFramePriceSym, rpnFrameTailMid,
      rpnFrameCore, rawMulTokens, rawLowerSafeRecipTokens, rawConstTokens,
      rawSafeRecipTokens]

lemma digitize_rpnFrameEmit (second : Bool) (blk : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (buf : List ℕ) :
    digitize (rpnFrameEmit second blk ε day bc ibc buf) =
      digitize [0, 3] ++ digitize buf ++ digitize blk ++
        digitize [day, 1, Encodable.encode (1 / ε : ℚ), 1,
          Encodable.encode (1 / ε : ℚ), 0] ++
        digitize blk ++ digitize (rpnFrameTailMid second day bc ibc) ++
        (if second then digitize blk
          else digitize [3] ++ digitize buf ++ digitize blk) := by
  rw [rpnFrameEmit_split]
  cases second <;>
    simp only [Bool.false_eq_true, if_false, if_true, digitize_append,
      List.append_assoc]

/-- The digitized position window extended by the exit token is a run of copied digit
blocks (positions `j - rcLen .. j`). -/
lemma digitize_rpnCondWindow_snoc (tf : ℕ → ℕ) (n j : ℕ) :
    digitize (rpnCondWindow tf n j ++ [tf (Nat.pair n j)]) =
      (List.range (rcLen (rpnCondControlAt tf n j) + 1)).flatMap fun i =>
        tokenBlock (tf (Nat.pair n (j - rcLen (rpnCondControlAt tf n j) + i))) := by
  have hle : rcLen (rpnCondControlAt tf n j) ≤ j := rcLen_controlAt_le tf n j
  rw [digitize_append, List.range_succ, List.flatMap_append]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · rw [rpnCondWindow, digitize, List.flatMap_map]
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      digitize_singleton]
    rw [Nat.sub_add_cancel hle]

/-- The all-poly stretch of the frame-leg emission is a poly token stream. -/
lemma rpnFrameTailMid_polyTokenStream (second : Bool) {cD cb ci : Code}
    {dayF bcF ibcF : ℕ → ℕ} (hdayF : PolyFueled cD dayF) (hbcF : PolyFueled cb bcF)
    (hibcF : PolyFueled ci ibcF) :
    PolyTokenStream (fun z => rpnFrameTailMid second (dayF z) (bcF z) (ibcF z)) := by
  have hgate : PolyTokenStream (fun z => rpnFrameGate (bcF z) (ibcF z)) :=
    PolyTokenStream.rawGate hbcF hibcF
  have hmin : PolyTokenStream (fun z =>
      rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate (bcF z) (ibcF z)))) :=
    PolyTokenStream.rawMin (PolyTokenStream.varTok 1)
      (PolyTokenStream.rawMul (PolyTokenStream.varTok 1) hgate)
  have hcore : PolyTokenStream (fun z => rpnFrameCore second (bcF z) (ibcF z)) := by
    cases second
    · exact hmin.of_eq fun z => by simp [rpnFrameCore]
    · exact (PolyTokenStream.rawMul (PolyTokenStream.rawConstQ (-1))
        (PolyTokenStream.rawMul hmin (PolyTokenStream.varTok 0))).of_eq fun z => by
          simp [rpnFrameCore]
  refine (((((PolyTokenStream.polyTok hdayF).append
    (PolyTokenStream.const 3)).append
    (((PolyTokenStream.const 5).append (PolyTokenStream.const 3)).append
      (PolyTokenStream.const 3))).append hcore).append
    (((PolyTokenStream.const 8).append (PolyTokenStream.const 8)).append
      (PolyTokenStream.const 6))).of_eq fun z => ?_
  simp [rpnFrameTailMid]

/-- **The frame-pass certificate**: the digitized symbol-level frame output of any digit
`PolySegStream` is a `PolySegStream`, over any **written-out** condition block
stream and poly-fueled day/budget codes.
Paper node: `thm:scon` -/
lemma rpnFrameOutput_polySegStream (second : Bool) {src blocks : ℕ → List ℕ}
    (hsrc : PolySegStream src) (hblocks : BigTokenStream blocks)
    {cD cb ci : Code} {dayF bcF ibcF : ℕ → ℕ}
    (hdayF : PolyFueled cD dayF) (hbcF : PolyFueled cb bcF)
    (hibcF : PolyFueled ci ibcF) (ε : ℚ) :
    PolySegStream (fun n => digitize
      (rpnFrameOutput second (blocks n) ε (dayF n) (bcF n) (ibcF n)
        (undigitize (src n)))) := by
  obtain ⟨⟨cc, hcnt⟩, hbig⟩ := hsrc.undigitizeTokens
  obtain ⟨cs, hscan⟩ := rpnCondScan hsrc
  obtain ⟨cad, had⟩ := addc_polyFueled
  set tf : ℕ → ℕ := fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0 with htf
  -- Per-position views (input `z = ⟨n, j⟩`).
  have hmodeZ := PolyFueled.left.comp hscan
  have hlenZ := PolyFueled.right.comp (PolyFueled.right.comp hscan)
  have hnextZ : PolyFueled _ (fun z : ℕ =>
      Nat.pair z.unpair.1 (z.unpair.2 + 1)) :=
    (PolyFueled.left.pair (had.comp (PolyFueled.right.pair
      (PolyFueled.const 1)))).of_eq fun z => by simp only [Nat.unpair_pair]
  have hmodeZ1 := PolyFueled.left.comp (hscan.comp hnextZ)
  have hnZ : PolyFueled _ (fun z : ℕ => z.unpair.1) := PolyFueled.left
  -- Copy branch: one digit block per source token.
  have hcopy := hbig.blockSeg
  -- The window copy, extended by the exit token: `concatVar` over `rcLen + 1`.
  have hidxE : ∃ c, PolyFueled c (fun w : ℕ => Nat.pair w.unpair.1.unpair.1
      (w.unpair.1.unpair.2 - rcLen (rpnCondControlAt tf
        w.unpair.1.unpair.1 w.unpair.1.unpair.2) + w.unpair.2)) := by
    have hz : PolyFueled Code.left (fun m : ℕ => m.unpair.1) := PolyFueled.left
    have hn2 := PolyFueled.left.comp hz
    have hj2 := PolyFueled.right.comp hz
    have hlenW := hlenZ.comp hz
    have hsub := subc_polyFueled.comp (hj2.pair hlenW)
    have hoff := had.comp (hsub.pair PolyFueled.right)
    exact ⟨_, (hn2.pair hoff).of_eq fun w => by
      simp only [Nat.unpair_pair, rcLen]⟩
  obtain ⟨cidx, hidx⟩ := hidxE
  have hlenZ1 : PolyFueled _ (fun z : ℕ =>
      rcLen (rpnCondControlAt tf z.unpair.1 z.unpair.2) + 1) :=
    (had.comp (hlenZ.pair (PolyFueled.const 1))).of_eq fun z => by
      simp only [Nat.unpair_pair, rcLen]
  have hwin := (hbig.comp hidx).blockSeg.concatVar hlenZ1
  -- Condition blocks at the trading day.
  have hblkN := (hblocks.comp hnZ).digitizeStream
  -- Constant and poly frames.
  have hconst03 : PolySegStream (fun _ : ℕ => digitize [0, 3]) :=
    (PolySegStream.ofTokenStream
      ((PolyTokenStream.const 0).append
        (PolyTokenStream.const 3))).digitizeStream.of_eq fun n => by simp
  have hdayFrame : PolySegStream (fun z : ℕ => digitize
      [dayF z.unpair.1, 1, Encodable.encode (1 / ε : ℚ), 1,
        Encodable.encode (1 / ε : ℚ), 0]) :=
    (PolySegStream.ofTokenStream
      (((((PolyTokenStream.polyTok (hdayF.comp hnZ)).append
        (PolyTokenStream.const 1)).append
        (PolyTokenStream.const (Encodable.encode (1 / ε : ℚ)))).append
        (PolyTokenStream.const 1)).append
        ((PolyTokenStream.const (Encodable.encode (1 / ε : ℚ))).append
          (PolyTokenStream.const 0)))).digitizeStream.of_eq fun n => by simp
  have hmid : PolySegStream (fun z : ℕ => digitize
      (rpnFrameTailMid second (dayF z.unpair.1) (bcF z.unpair.1)
        (ibcF z.unpair.1))) :=
    (PolySegStream.ofTokenStream (rpnFrameTailMid_polyTokenStream second
      (hdayF.comp hnZ) (hbcF.comp hnZ) (hibcF.comp hnZ))).digitizeStream
  have hconst3 : PolySegStream (fun _ : ℕ => digitize [3]) :=
    (PolySegStream.ofTokenStream (PolyTokenStream.const 3)).digitizeStream.of_eq
      fun n => by simp
  have hwinD : PolySegStream (fun z : ℕ =>
      digitize (rpnCondWindow tf z.unpair.1 z.unpair.2 ++ [tf (Nat.pair z.unpair.1 z.unpair.2)])) :=
    hwin.of_eq fun z => by
      simp only [Nat.unpair_pair]
      exact (digitize_rpnCondWindow_snoc tf z.unpair.1 z.unpair.2).symm
  have hlast : PolySegStream (fun z : ℕ =>
      if second then digitize (blocks z.unpair.1)
      else digitize [3] ++ digitize (rpnCondWindow tf z.unpair.1 z.unpair.2 ++
        [tf (Nat.pair z.unpair.1 z.unpair.2)]) ++ digitize (blocks z.unpair.1)) := by
    cases second
    · exact ((hconst3.append hwinD).append hblkN).of_eq fun z => by simp
    · exact hblkN.of_eq fun z => by simp
  have hEmit : PolySegStream (fun z : ℕ => digitize
      (rpnFrameEmit second (blocks z.unpair.1) ε (dayF z.unpair.1) (bcF z.unpair.1)
        (ibcF z.unpair.1) (rpnCondWindow tf z.unpair.1 z.unpair.2 ++
          [tf (Nat.pair z.unpair.1 z.unpair.2)]))) := by
    refine ((((((hconst03.append hwinD).append hblkN).append hdayFrame).append
      hblkN).append hmid).append hlast).of_eq fun z => ?_
    rw [digitize_rpnFrameEmit]
  have hempty : PolySegStream (fun _ : ℕ => ([] : List ℕ)) :=
    PolySegStream.ofTokenStream PolyTokenStream.nil
  -- The emission fires only when the successor control mode is base.
  have hExit := hEmit.ifZero hempty hmodeZ1
  have heqTest (K : ℕ) {cf : Code} {f : ℕ → ℕ} (hf : PolyFueled cf f) :
      ∃ c, PolyFueled c (fun z => f z - K + (K - f z)) :=
    ⟨_, (had.comp ((subc_polyFueled.comp (hf.pair (PolyFueled.const K))).pair
      (subc_polyFueled.comp ((PolyFueled.const K).pair hf)))).of_eq
      (fun z => by simp only [Nat.unpair_pair])⟩
  obtain ⟨_, heq4⟩ := heqTest 4 hmodeZ
  obtain ⟨_, heq7⟩ := heqTest 7 hmodeZ
  obtain ⟨_, heq9⟩ := heqTest 9 hmodeZ
  have hseg9 := hExit.ifZero hcopy heq9
  have hseg7 := hExit.ifZero hseg9 heq7
  have hseg4 := hExit.ifZero hseg7 heq4
  -- The withheld base-mode trade tag.
  obtain ⟨ctc, htagclamp⟩ := hbig.clampVal (PolyFueled.const 8)
  have heq6 := had.comp ((subc_polyFueled.comp (htagclamp.pair
    (PolyFueled.const 6))).pair
    (subc_polyFueled.comp ((PolyFueled.const 6).pair htagclamp)))
  have hsel1 := had.comp (hmodeZ.pair heq6)
  have hseg := hempty.ifZero hseg4 hsel1
  have hassembled := hseg.concatVar hcnt
  -- End-of-stream flush of an unfinished trade run.
  have hmodeEnd := hmodeZ.comp (PolyFueled.id.pair hcnt)
  obtain ⟨_, heq4End⟩ := heqTest 4 hmodeEnd
  obtain ⟨_, heq7End⟩ := heqTest 7 hmodeEnd
  obtain ⟨_, heq9End⟩ := heqTest 9 hmodeEnd
  have hblock6 : PolySegStream (fun _ : ℕ => tokenBlock 6) :=
    PolySegStream.block (PolyFueled.const 6)
  have hflush := hblock6.ifZero
    (hblock6.ifZero (hblock6.ifZero hempty heq9End) heq7End) heq4End
  refine (hassembled.append hflush).of_eq fun n => ?_
  simp only [Nat.unpair_pair]
  have hget : ∀ i, tf (Nat.pair n i) = (undigitize (src n)).getD i 0 := fun i => by
    rw [htf]
    simp only [Nat.unpair_pair]
  have hts : undigitize (src n) =
      (List.range (undigitize (src n)).length).map fun j => tf (Nat.pair n j) := by
    conv_lhs => rw [list_eq_rangeMap_getD (undigitize (src n))]
    exact List.map_congr_left fun j _ => (hget j).symm
  have hrun : rpnFrameRun second (blocks n) ε (dayF n) (bcF n) (ibcF n)
      (rcPack 0 0 0, []) (undigitize (src n)) =
      ((rpnCondControlAt tf n (undigitize (src n)).length,
        rpnCondWindow tf n (undigitize (src n)).length),
        (List.range (undigitize (src n)).length).flatMap fun j =>
          rpnFrameSegment tf second (blocks n) ε (dayF n) (bcF n) (ibcF n)
            (Nat.pair n j)) := by
    conv_lhs => rw [hts]
    exact rpnFrameRun_range tf second (blocks n) ε (dayF n) (bcF n) (ibcF n) n
      (undigitize (src n)).length
  rw [rpnFrameOutput, hrun]
  simp only [digitize_append, digitize_flatMap]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine List.flatMap_congr fun j hj => ?_
    rw [rpnFrameSegment_eq]
    rw [show (Nat.unpair (rpnCondControlAt tf n j)).1 =
        rcMode (rpnCondControlAt tf n j) from rfl,
      show (Nat.unpair (rpnCondControlAt tf n (j + 1))).1 =
        rcMode (rpnCondControlAt tf n (j + 1)) from rfl]
    have hclampSix : min (tf (Nat.pair n j)) 9 = 6 ↔ tf (Nat.pair n j) = 6 := by
      by_cases h9 : tf (Nat.pair n j) ≤ 9
      · rw [Nat.min_eq_left h9]
      · rw [Nat.min_eq_right (by omega : 9 ≤ _)]
        constructor
        · intro h; omega
        · intro h; omega
    by_cases hc1 : rcMode (rpnCondControlAt tf n j) = 0 ∧ tf (Nat.pair n j) = 6
    · rw [if_pos (by
        rcases hc1 with ⟨hm0, ht6⟩
        rw [hm0, ht6]
        norm_num), if_pos hc1]
      simp [digitize]
    · rw [if_neg (by
        intro hz0
        exact hc1 ⟨by omega, hclampSix.mp (by omega)⟩), if_neg hc1]
      by_cases hm4 : rcMode (rpnCondControlAt tf n j) = 4
      · rw [if_pos (by omega), if_pos (Or.inl hm4)]
        by_cases hnext : rcMode (rpnCondControlAt tf n (j + 1)) = 0
        · rw [if_pos hnext, if_pos hnext]
        · rw [if_neg hnext, if_neg hnext]
          simp [digitize]
      · rw [if_neg (by omega)]
        by_cases hm7 : rcMode (rpnCondControlAt tf n j) = 7
        · rw [if_pos (by omega), if_pos (Or.inr (Or.inl hm7))]
          by_cases hnext : rcMode (rpnCondControlAt tf n (j + 1)) = 0
          · rw [if_pos hnext, if_pos hnext]
          · rw [if_neg hnext, if_neg hnext]
            simp [digitize]
        · rw [if_neg (by omega)]
          by_cases hm9 : rcMode (rpnCondControlAt tf n j) = 9
          · rw [if_pos (by omega), if_pos (Or.inr (Or.inr hm9))]
            by_cases hnext : rcMode (rpnCondControlAt tf n (j + 1)) = 0
            · rw [if_pos hnext, if_pos hnext]
            · rw [if_neg hnext, if_neg hnext]
              simp [digitize]
          · rw [if_neg (by omega), if_neg (by tauto)]
            simp [digitize]
  · rw [show (Nat.unpair (rpnCondControlAt tf n (undigitize (src n)).length)).1 =
        rcMode (rpnCondControlAt tf n (undigitize (src n)).length) from rfl]
    by_cases hm4 : rcMode (rpnCondControlAt tf n (undigitize (src n)).length) = 4
    · rw [if_pos (by omega), if_pos (Or.inl hm4)]
      simp [digitize]
    · rw [if_neg (by omega)]
      by_cases hm7 : rcMode (rpnCondControlAt tf n (undigitize (src n)).length) = 7
      · rw [if_pos (by omega), if_pos (Or.inr (Or.inl hm7))]
        simp [digitize]
      · rw [if_neg (by omega)]
        by_cases hm9 : rcMode
            (rpnCondControlAt tf n (undigitize (src n)).length) = 9
        · rw [if_pos (by omega), if_pos (Or.inr (Or.inr hm9))]
          simp [digitize]
        · rw [if_neg (by omega), if_neg (by tauto)]
          simp [digitize]

/-! ### The gated two-leg join

`safeSeparatedFrameTokenOutput` emits the first frame leg alone unless the source is
structurally accepting, in which case it emits both.  The symbol side mirrors that shape
off `rpnStructurallyAccepts`.  Because the join appends two frame outputs, its agreement
with the token model runs through the prefix form `FrameContract` of the frame agreement
rather than `FrameAgree`, which does not survive an append. -/

/-- The symbol-side acceptance test is poly-fueled over any digit `PolySegStream`. -/
lemma rpnAcceptScan {s : ℕ → List ℕ} (h : PolySegStream s) :
    ∃ c, PolyFueled c (fun n =>
      rpnStructurallyAccepts (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0)
        (fun m => (undigitize (s m)).length) n) := by
  obtain ⟨cs, hscan⟩ := rpnCondScan h
  obtain ⟨cd, hdepth⟩ := rpnDepthScan h
  obtain ⟨⟨cc, hcnt⟩, -⟩ := h.undigitizeTokens
  set tf : ℕ → ℕ := fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0 with htf
  have hend : PolyFueled _ (fun n : ℕ => Nat.pair n (undigitize (s n)).length) :=
    PolyFueled.id.pair hcnt
  have hmode : PolyFueled _ (fun n : ℕ =>
      rcMode (rpnCondControlAt tf n (undigitize (s n)).length)) :=
    (PolyFueled.left.comp (hscan.comp hend)).of_eq fun n => by
      simp only [Nat.unpair_pair, rcMode]
  have hdep : PolyFueled _ (fun n : ℕ =>
      rpnDepthAt tf n (undigitize (s n)).length) :=
    (hdepth.comp hend).of_eq fun n => by simp only [Nat.unpair_pair]
  obtain ⟨_, hinner⟩ :=
    polyFueled_ifEq hdep 0 (PolyFueled.const 1) (PolyFueled.const 0)
  obtain ⟨c, hall⟩ := polyFueled_ifEq hmode 0 hinner (PolyFueled.const 0)
  exact ⟨c, hall.of_eq fun n => by rw [rpnStructurallyAccepts]⟩

/-- **The gated two-leg join at symbol level** (mirror of
`safeSeparatedFrameTokenOutput`): both frame legs are emitted only at a structurally
accepting source boundary. -/
def rpnSafeSeparatedFrameOutput (tf lenF : ℕ → ℕ) (blkψ : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (ts : List ℕ) : List ℕ :=
  let first := rpnFrameOutput false blkψ ε day bc ibc ts
  let second := rpnFrameOutput true blkψ ε day bc ibc ts
  if rpnStructurallyAccepts tf lenF day = 0 then first else first ++ second

/-- **The gated join's certificate**: the digitized two-leg join of any digit
`PolySegStream` is a `PolySegStream`.
Paper node: `thm:scon` -/
lemma rpnSafeSeparatedFrameOutput_polySegStream {src blocks : ℕ → List ℕ}
    (hsrc : PolySegStream src) (hblocks : BigTokenStream blocks)
    {cb ci : Code} {bcF ibcF : ℕ → ℕ} (hbcF : PolyFueled cb bcF)
    (hibcF : PolyFueled ci ibcF) (ε : ℚ) :
    PolySegStream (fun n => digitize
      (rpnSafeSeparatedFrameOutput
        (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
        (fun m => (undigitize (src m)).length)
        (blocks n) ε n (bcF n) (ibcF n) (undigitize (src n)))) := by
  have hfirst := rpnFrameOutput_polySegStream false hsrc hblocks
    (PolyFueled.id) hbcF hibcF ε
  have hsecond := rpnFrameOutput_polySegStream true hsrc hblocks
    (PolyFueled.id) hbcF hibcF ε
  obtain ⟨caccept, haccept⟩ := rpnAcceptScan hsrc
  refine (hfirst.ifZero (hfirst.append hsecond) haccept).of_eq fun n => ?_
  simp only [rpnSafeSeparatedFrameOutput]
  by_cases hacc : rpnStructurallyAccepts
      (fun w => (undigitize (src w.unpair.1)).getD w.unpair.2 0)
      (fun m => (undigitize (src m)).length) n = 0
  · rw [if_pos hacc, if_pos hacc]
  · rw [if_neg hacc, if_neg hacc, digitize_append]

/-- **The gated two-leg join agrees with the token model**: the contraction of the
symbol-level gated join decodes to the same validated strategy as the token-model
gated join of the contraction.
Paper node: `thm:scon` -/
lemma strategyOfTokens_unRpn_rpnSafeSeparatedFrameOutput_trades
    (tf tokenFn lenF lenFn : ℕ → ℕ) (blkψ : List ℕ) {ψn : Sentence}
    (hblkψ : parseRpn blkψ.length blkψ = some (ψn, [])) (ε q : ℚ) (n : ℕ)
    (ts : List ℕ) (hts : vpre tf n (lenF n) = ts)
    (hL : vpre tokenFn n (lenFn n) = unRpn ts) :
    (strategyOfTokens n (unRpn (rpnSafeSeparatedFrameOutput tf lenF blkψ ε n
        (Encodable.encode q) (Encodable.encode q⁻¹) ts))).trades =
      (strategyOfTokens n
        (safeSeparatedFrameTokenOutput tokenFn lenFn ψn ε q n (unRpn ts))).trades := by
  have hgate := rpnStructurallyAccepts_agree tf tokenFn lenF lenFn n ts hts hL
  have hB1 := deserializeTrades_conditioningFrameTokenRun false ψn ε q n (unRpn ts)
  have hB2 := deserializeTrades_conditioningFrameTokenRun true ψn ε q n (unRpn ts)
  have hjoinTok := deserializeTrades_safeSeparatedFrameTokenOutput tokenFn lenFn ψn ε
    q n (unRpn ts) hL.symm
  -- the base-mode invariant delivered by an accepting symbol-side gate
  have hbaseOf : rpnStructurallyAccepts tf lenF n ≠ 0 →
      List.foldl rpnCondStep (rcPack 0 0 0) ts = rcPack 0 0 0 := by
    intro hacc
    have hmode : rcMode (rpnCondControlAt tf n (lenF n)) = 0 := by
      unfold rpnStructurallyAccepts at hacc
      split_ifs at hacc with h1 h2 <;> simp_all
    rw [rpnCondControlAt_eq_foldl, hts] at hmode
    exact foldl_rpnCondStep_eq_base_of_mode_zero ts hmode
  cases hsrc : deserializeTrades (unRpn ts) with
  | some trades =>
      -- readable source: the poison branches are impossible on both legs.
      rw [hsrc] at hB1 hB2
      simp only [Option.map_some] at hB1 hB2
      have hne1 : ¬ Unreadable (conditioningFrameTokenOutput false
          (Encodable.encode ψn) n ε (Encodable.encode q) (Encodable.encode q⁻¹)
          (unRpn ts)) := by
        intro hU
        rw [hU.deserializeTrades_eq_none] at hB1
        simp at hB1
      have hne2 : ¬ Unreadable (conditioningFrameTokenOutput true
          (Encodable.encode ψn) n ε (Encodable.encode q) (Encodable.encode q⁻¹)
          (unRpn ts)) := by
        intro hU
        rw [hU.deserializeTrades_eq_none] at hB2
        simp at hB2
      have hgateEq : rpnStructurallyAccepts tf lenF n =
          parserStructurallyAccepts tokenFn lenFn n := by
        rcases hgate with h | hU
        · exact h
        · rw [hU.deserializeTrades_eq_none] at hsrc
          exact absurd hsrc (by simp)
      by_cases hacc : rpnStructurallyAccepts tf lenF n = 0
      · have hacc' : parserStructurallyAccepts tokenFn lenFn n = 0 := by
          rw [← hgateEq]; exact hacc
        unfold rpnSafeSeparatedFrameOutput safeSeparatedFrameTokenOutput
        simp only [hacc, hacc', if_true]
        exact strategyOfTokens_unRpn_rpnFrameOutput_trades false blkψ hblkψ ε n _ _ n ts
      · have hacc' : parserStructurallyAccepts tokenFn lenFn n ≠ 0 := by
          rw [← hgateEq]; exact hacc
        have hbase := hbaseOf hacc
        have hC1 := frameContract_rpnFrameOutput false blkψ hblkψ ε n
          (Encodable.encode q) (Encodable.encode q⁻¹) ts hbase
        have hC2 := frameContract_rpnFrameOutput true blkψ hblkψ ε n
          (Encodable.encode q) (Encodable.encode q⁻¹) ts hbase
        rcases hC1 with hT1 | ⟨-, -, hU1⟩
        · rcases hC2 with hT2 | ⟨-, -, hU2⟩
          · have hjoin := (hT1.append hT2) []
            rw [List.append_nil, unRpn_nil, List.append_nil] at hjoin
            unfold rpnSafeSeparatedFrameOutput safeSeparatedFrameTokenOutput
            simp only [hacc, hacc', if_false]
            rw [hjoin]
          · exact absurd hU2 hne2
        · exact absurd hU1 hne1
  | none =>
      -- unreadable source: neither side produces trades.
      have htokNil : (strategyOfTokens n
          (safeSeparatedFrameTokenOutput tokenFn lenFn ψn ε q n (unRpn ts))).trades =
          [] := by
        refine strategyOfTokens_of_deserializeTrades_none ?_ n
        rw [hjoinTok, hsrc]
        rfl
      rw [htokNil]
      refine strategyOfTokens_of_deserializeTrades_none ?_ n
      rw [hsrc] at hB1
      simp only [Option.map_none] at hB1
      by_cases hacc : rpnStructurallyAccepts tf lenF n = 0
      · unfold rpnSafeSeparatedFrameOutput
        simp only [hacc, if_true]
        rcases frameAgree_unRpn_rpnFrameOutput false blkψ hblkψ ε n
          (Encodable.encode q) (Encodable.encode q⁻¹) ts with heq | ⟨hU, -⟩
        · rw [heq]; exact hB1
        · exact hU.deserializeTrades_eq_none
      · have hbase := hbaseOf hacc
        have hreadNone : EF.streamReadFrom (unRpn ts) (some EF.streamInitial) =
            none := by
          rcases hgate with h | hU
          · refine streamReadFrom_eq_none_of_accepts_of_deserializeTrades_none
              tokenFn lenFn n (unRpn ts) hL.symm ?_ hsrc
            exact parserStructurallyAccepts_eq_one_of_ne_zero (by rw [← h]; exact hacc)
          · exact hU (0, none) [] [] rfl
        have hB1read := streamReadFrom_conditioningFrameTokenOutput_none false ψn ε q
          n (unRpn ts) hreadNone
        have hC1 := frameContract_rpnFrameOutput false blkψ hblkψ ε n
          (Encodable.encode q) (Encodable.encode q⁻¹) ts hbase
        unfold rpnSafeSeparatedFrameOutput
        simp only [hacc, if_false]
        rcases hC1 with hT1 | ⟨hstop, hU1, -⟩
        · rw [hT1 _]
          unfold deserializeTrades
          rw [EF.streamReadFrom_append, hB1read, EF.streamReadFrom_none]
        · rw [hstop _]
          exact hU1.deserializeTrades_eq_none

/-! ## The zero-aware price pass (for the eventual translation)

The eventual translation prices a *finite* set of days at the constant `1` instead of
the conditional-price body.  At symbol level that is a second emitter for the same
transducer, so the master commutation and the emission certificate are obtained by
instantiating their emitter-generic forms. -/

section ZeroAwareTokenRunEq

variable (zeroDays : Finset ℕ) (ψc : ℕ → ℕ) (ε : ℚ)

lemma zeroAwareConditionPriceTokenRun_single (t : ℕ)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (h6 : t ≠ 6) (h7 : t ≠ 7) (L : List ℕ) :
    (zeroAwareConditionPriceTokenRun zeroDays ψc ε (0, 0) (t :: L)).2 =
      t :: (zeroAwareConditionPriceTokenRun zeroDays ψc ε (0, 0) L).2 := by
  simp [zeroAwareConditionPriceTokenRun, zeroAwareConditionPriceTokenEmit,
    EF.freezeTokenNext, h0, h1, h6, h7]

lemma zeroAwareConditionPriceTokenRun_one (t : ℕ) :
    (zeroAwareConditionPriceTokenRun zeroDays ψc ε (0, 0) [t]).2 = [t] := by
  simp [zeroAwareConditionPriceTokenRun, zeroAwareConditionPriceTokenEmit]

lemma zeroAwareConditionPriceTokenRun_payload (t c : ℕ) (ht : t = 1 ∨ t = 7)
    (L : List ℕ) :
    (zeroAwareConditionPriceTokenRun zeroDays ψc ε (0, 0) (t :: c :: L)).2 =
      t :: c :: (zeroAwareConditionPriceTokenRun zeroDays ψc ε (0, 0) L).2 := by
  rcases ht with rfl | rfl <;>
    simp [zeroAwareConditionPriceTokenRun, zeroAwareConditionPriceTokenEmit,
      EF.freezeTokenNext]

lemma zeroAwareConditionPriceTokenRun_price (fc d : ℕ) (L : List ℕ) :
    (zeroAwareConditionPriceTokenRun zeroDays ψc ε (0, 0)
        (0 :: fc :: d :: L)).2 =
      0 :: fc :: d ::
        ((if d ∈ zeroDays then [1, Encodable.encode (1 : ℚ), 8]
          else rawConditionalPriceTokens fc (ψc d) d ε ++ [8]) ++
          (zeroAwareConditionPriceTokenRun zeroDays ψc ε (0, 0) L).2) := by
  by_cases hd : d ∈ zeroDays <;>
    simp [zeroAwareConditionPriceTokenRun, zeroAwareConditionPriceTokenEmit,
      EF.freezeTokenNext, hd]

lemma zeroAwareConditionPriceTokenRun_price_pair (fc : ℕ) :
    (zeroAwareConditionPriceTokenRun zeroDays ψc ε (0, 0) [0, fc]).2 = [0, fc] := by
  simp [zeroAwareConditionPriceTokenRun, zeroAwareConditionPriceTokenEmit,
    EF.freezeTokenNext]

lemma zeroAwareConditionPriceTokenRun_trade (fc : ℕ) (L : List ℕ) :
    (zeroAwareConditionPriceTokenRun zeroDays ψc ε (0, 0) (6 :: fc :: L)).2 =
      6 :: fc :: (zeroAwareConditionPriceTokenRun zeroDays ψc ε (0, 0) L).2 := by
  simp [zeroAwareConditionPriceTokenRun, zeroAwareConditionPriceTokenEmit,
    EF.freezeTokenNext]

end ZeroAwareTokenRunEq

/-- The zero-aware price emitter: a price day in `zeroDays` binds the constant `1`
instead of the conditional-price body. -/
def rpnZeroAwareEmit (zeroDays : Finset ℕ) (blocks : ℕ → List ℕ) (ε : ℚ) :
    List ℕ → ℕ → List ℕ :=
  fun buf D =>
    if D ∈ zeroDays then [D, 1, Encodable.encode (1 : ℚ), 8]
    else rpnConditionEmit (blocks D) ε buf D

/-- The zero-day chunk contracts to the token-model zero-day emission. -/
lemma unRpn_zero_rewrite_chunk {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) (D : ℕ) (rest : List ℕ) :
    unRpn (0 :: b ++ [D, 1, Encodable.encode (1 : ℚ), 8] ++ rest) =
      0 :: Encodable.encode φ :: D ::
        (1 :: Encodable.encode (1 : ℚ) :: 8 :: unRpn rest) := by
  have hshape : 0 :: b ++ [D, 1, Encodable.encode (1 : ℚ), 8] ++ rest =
      0 :: (b ++ D :: 1 :: Encodable.encode (1 : ℚ) :: 8 :: rest) := by
    simp
  rw [hshape, unRpn_price_chunk_block hb,
    unRpn_payload_chunk 1 _ (Or.inl rfl), unRpn_single_chunk 8 (by norm_num)]

/-- **Whole-stream contraction exactness for the zero-aware price pass.**
Paper node: `thm:scon` -/
lemma unRpn_rpnZeroAwareConditionRun (zeroDays : Finset ℕ) (blocks : ℕ → List ℕ)
    (ψ : ℕ → Sentence)
    (hblocks : ∀ D, parseRpn (blocks D).length (blocks D) = some (ψ D, []))
    (ε : ℚ) : ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    unRpn ((rpnConditionRun (rpnZeroAwareEmit zeroDays blocks ε)
        (rcPack 0 0 0, []) ts).2) =
      (zeroAwareConditionPriceTokenRun zeroDays (fun D => Encodable.encode (ψ D)) ε
        (0, 0) (unRpn ts)).2 :=
  unRpn_rpnConditionRun_of (rpnZeroAwareEmit zeroDays blocks ε)
    (fun L => (zeroAwareConditionPriceTokenRun zeroDays
      (fun D => Encodable.encode (ψ D)) ε (0, 0) L).2)
    (fun fc d => if d ∈ zeroDays then [1, Encodable.encode (1 : ℚ), 8]
      else rawConditionalPriceTokens fc (Encodable.encode (ψ d)) d ε ++ [8])
    rfl
    (fun t L h0 h1 h6 h7 =>
      zeroAwareConditionPriceTokenRun_single zeroDays _ ε t h0 h1 h6 h7 L)
    (fun t => zeroAwareConditionPriceTokenRun_one zeroDays _ ε t)
    (fun t c L ht => zeroAwareConditionPriceTokenRun_payload zeroDays _ ε t c ht L)
    (fun fc d L => by
      rw [zeroAwareConditionPriceTokenRun_price])
    (fun fc => zeroAwareConditionPriceTokenRun_price_pair zeroDays _ ε fc)
    (fun fc L => zeroAwareConditionPriceTokenRun_trade zeroDays _ ε fc L)
    (fun b φ hb D rest => by
      rw [rpnZeroAwareEmit]
      by_cases hD : D ∈ zeroDays
      · rw [if_pos hD, unRpn_zero_rewrite_chunk hb D rest, if_pos hD]
        simp
      · rw [if_neg hD, unRpn_price_rewrite_chunk hb (hblocks D) D ε rest, if_neg hD]
        simp [List.append_assoc])

/-- **The zero-aware guarded price-pass strategy-level equality.**
Paper node: `thm:scon` -/
lemma strategyOfTokens_rpnGuardedZeroAwareConditionTokens_trades
    (zeroDays : Finset ℕ) (blocks : ℕ → List ℕ) (ψ : ℕ → Sentence)
    (hblocks : ∀ D, parseRpn (blocks D).length (blocks D) = some (ψ D, []))
    (ε : ℚ) (n : ℕ) (ts : List ℕ) :
    (strategyOfTokens n
        (unRpn (rpnGuardedConditionTokens (rpnZeroAwareEmit zeroDays blocks ε)
          n ts))).trades =
      (strategyOfTokens n (unRpn ts)).trades.map fun trade =>
        (trade.1.retainedConditionPricesExceptZero zeroDays ψ ε, trade.2) := by
  rw [rpnGuardedConditionTokens]
  split_ifs with hguard
  · rw [unRpn_rpnZeroAwareConditionRun zeroDays blocks ψ hblocks ε ts.length ts
      le_rfl]
    exact strategyOfTokens_zeroAwareConditionPriceTokenRun_trades zeroDays ψ ε n
      (unRpn ts)
  · push_neg at hguard
    obtain ⟨j, hj, hm, hday⟩ := hguard
    rw [unRpn_nil, strategyOfTokens_nil_trades,
      strategyOfTokens_unRpn_trades_eq_nil_of_rpnBigDay n ts j hj hm hday]
    rfl

/-- **The zero-aware price-pass certificate.**
Paper node: `thm:scon` -/
lemma rpnGuardedZeroAwareConditionRun_polySegStream (zeroDays : Finset ℕ)
    {s blocks : ℕ → List ℕ} (h : PolySegStream s) (hb : BigTokenStream blocks)
    (ε : ℚ) :
    PolySegStream (fun n => digitize
      (rpnGuardedConditionTokens (rpnZeroAwareEmit zeroDays blocks ε) n
        (undigitize (s n)))) := by
  obtain ⟨⟨cc, hcnt⟩, hbig⟩ := h.undigitizeTokens
  obtain ⟨cs, hscan⟩ := rpnCondScan h
  obtain ⟨cd, hclamp⟩ := h.dayClampTokens
  obtain ⟨cad, had⟩ := addc_polyFueled
  set tf : ℕ → ℕ := fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0 with htf
  have hlenZ := PolyFueled.right.comp (PolyFueled.right.comp hscan)
  refine rpnGuardedConditionRun_polySegStream_of h _ ?_
  have hD := PolySegStream.block hclamp
  have hA : PolySegStream (fun _ : ℕ => digitize
      [1, Encodable.encode (-1 : ℚ), 1, Encodable.encode (-1 : ℚ),
        1, Encodable.encode (1 : ℚ), 3, 1, Encodable.encode (-1 : ℚ), 0, 3]) :=
    (PolySegStream.ofTokenStream
      (((((((((((PolyTokenStream.const 1).append
        (PolyTokenStream.const (Encodable.encode (-1 : ℚ)))).append
        (PolyTokenStream.const 1)).append
        (PolyTokenStream.const (Encodable.encode (-1 : ℚ)))).append
        (PolyTokenStream.const 1)).append
        (PolyTokenStream.const (Encodable.encode (1 : ℚ)))).append
        (PolyTokenStream.const 3)).append
        (PolyTokenStream.const 1)).append
        (PolyTokenStream.const (Encodable.encode (-1 : ℚ)))).append
        (PolyTokenStream.const 0)).append
        (PolyTokenStream.const 3))).digitizeStream.of_eq fun n => by
      simp
  have hB : PolySegStream (fun _ : ℕ => digitize
      [1, Encodable.encode (1 / ε : ℚ), 1, Encodable.encode (1 / ε : ℚ), 0]) :=
    (PolySegStream.ofTokenStream
      (((((PolyTokenStream.const 1).append
        (PolyTokenStream.const (Encodable.encode (1 / ε : ℚ)))).append
        (PolyTokenStream.const 1)).append
        (PolyTokenStream.const (Encodable.encode (1 / ε : ℚ)))).append
        (PolyTokenStream.const 0))).digitizeStream.of_eq fun n => by
      simp
  have hC : PolySegStream (fun _ : ℕ => digitize [3, 5, 3, 3, 3, 4, 3, 8]) :=
    (PolySegStream.ofTokenStream
      ((((((((PolyTokenStream.const 3).append
        (PolyTokenStream.const 5)).append
        (PolyTokenStream.const 3)).append
        (PolyTokenStream.const 3)).append
        (PolyTokenStream.const 3)).append
        (PolyTokenStream.const 4)).append
        (PolyTokenStream.const 3)).append
        (PolyTokenStream.const 8))).digitizeStream.of_eq fun n => by
      simp
  have hidxE : ∃ c, PolyFueled c (fun w : ℕ => Nat.pair w.unpair.1.unpair.1
      (w.unpair.1.unpair.2 - rcLen (rpnCondControlAt tf
        w.unpair.1.unpair.1 w.unpair.1.unpair.2) + w.unpair.2)) := by
    obtain ⟨cad', had'⟩ := addc_polyFueled
    have hz : PolyFueled Code.left (fun m : ℕ => m.unpair.1) := PolyFueled.left
    have hn2 := PolyFueled.left.comp hz
    have hj2 := PolyFueled.right.comp hz
    have hlenW := hlenZ.comp hz
    have hsub := subc_polyFueled.comp (hj2.pair hlenW)
    have hoff := had'.comp (hsub.pair PolyFueled.right)
    exact ⟨_, (hn2.pair hoff).of_eq fun w => by
      simp only [Nat.unpair_pair, rcLen]⟩
  obtain ⟨cidx, hidx⟩ := hidxE
  have hwin := (hbig.comp hidx).blockSeg.concatVar hlenZ
  have hblkD := (hb.comp hclamp).digitizeStream
  have hlong := ((((((((hD.append hA).append hwin).append hblkD).append
    hD).append hB).append hblkD).append hD).append hC)
  -- The zero-day branch: `[D, 1, enc 1, 8]` at the clamped day.
  have hzero : PolySegStream (fun z : ℕ => digitize
      [min ((undigitize (s z.unpair.1)).getD z.unpair.2 0) (z.unpair.1 + 1),
        1, Encodable.encode (1 : ℚ), 8]) :=
    (PolySegStream.ofTokenStream
      ((((PolyTokenStream.polyTok hclamp).append (PolyTokenStream.const 1)).append
        (PolyTokenStream.const (Encodable.encode (1 : ℚ)))).append
        (PolyTokenStream.const 8))).digitizeStream
  obtain ⟨cmem, hmem⟩ := finsetMembership_polyFueled hclamp zeroDays
  refine (hzero.ifZero hlong
    ((ifzSel_polyFueled.comp (((PolyFueled.const 1).pair
      (PolyFueled.const 0)).pair hmem)).of_eq fun z => by
        simp only [Nat.unpair_pair, ifzSelFn]
        rfl)).of_eq fun z => ?_
  rw [rpnZeroAwareEmit]
  by_cases hz : min ((undigitize (s z.unpair.1)).getD z.unpair.2 0)
      (z.unpair.1 + 1) ∈ zeroDays
  · rw [if_pos (by simpa using hz), if_pos hz]
  · rw [if_neg (by simpa using hz), if_neg hz]
    rw [digitize_rpnConditionEmit, digitize_rpnCondWindow]
    simp only [Nat.unpair_pair, htf, rcLen, List.append_assoc]

/-! ## The class-agnostic conditioning transduction

The two conditioning passes compose into a single list-level transduction,
`rpnConditionOutput`, carrying a day's source token stream to that day's conditioned
stream without mentioning any efficiency class.  Its correctness on an arbitrary stream
(`strategyOfTokens_rpnConditionOutput`) is the whole mathematical content of closure
under conditioning; a class-preservation endpoint adds only the emission certificates
that place the transduction inside the class. -/

/-- Structural acceptance read off a stream directly (the list-level form of
`rpnStructurallyAccepts`). -/
def rpnAcceptsRuns (ts : List ℕ) : ℕ :=
  if rcMode (ts.foldl rpnCondStep (rcPack 0 0 0)) = 0 then
    (if rpnDepthRuns (rcPack 0 0 0) ts 0 = 0 then 1 else 0)
  else 0

/-- The position-indexed acceptance test is the list-level one over the position view. -/
lemma rpnStructurallyAccepts_eq_runs (tf lenF : ℕ → ℕ) (n : ℕ) :
    rpnStructurallyAccepts tf lenF n = rpnAcceptsRuns (vpre tf n (lenF n)) := by
  rw [rpnStructurallyAccepts, rpnAcceptsRuns, rpnCondControlAt_eq_foldl,
    rpnDepthAt_eq_runs]

/-- The gated two-leg join read off a stream directly (the list-level form of
`rpnSafeSeparatedFrameOutput`). -/
def rpnSafeSeparatedFrameRuns (blkψ : List ℕ) (ε : ℚ) (day bc ibc : ℕ)
    (ts : List ℕ) : List ℕ :=
  if rpnAcceptsRuns ts = 0 then rpnFrameOutput false blkψ ε day bc ibc ts
  else rpnFrameOutput false blkψ ε day bc ibc ts ++
    rpnFrameOutput true blkψ ε day bc ibc ts

/-- The position-indexed gated join is the list-level one over the position view. -/
lemma rpnSafeSeparatedFrameOutput_eq_runs (tf lenF : ℕ → ℕ) (blkψ : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (ts : List ℕ) (hts : vpre tf day (lenF day) = ts) :
    rpnSafeSeparatedFrameOutput tf lenF blkψ ε day bc ibc ts =
      rpnSafeSeparatedFrameRuns blkψ ε day bc ibc ts := by
  rw [rpnSafeSeparatedFrameOutput, rpnSafeSeparatedFrameRuns,
    rpnStructurallyAccepts_eq_runs, hts]

/-- **The conditioning transduction**: the guarded price pass followed by the gated
two-leg frame pass, whose budget is set by the priced stream's own trade-run count. -/
def rpnConditionOutput (blocks : ℕ → List ℕ) (ε : ℚ) (n : ℕ) (ts : List ℕ) : List ℕ :=
  rpnSafeSeparatedFrameRuns (blocks n) ε n
    (frameBudgetCode n (rpnTradeRuns (rcPack 0 0 0)
      (rpnGuardedConditionTokens (rpnPriceEmit blocks ε) n ts)))
    (frameInverseBudgetCode n (rpnTradeRuns (rcPack 0 0 0)
      (rpnGuardedConditionTokens (rpnPriceEmit blocks ε) n ts)))
    (rpnGuardedConditionTokens (rpnPriceEmit blocks ε) n ts)

/-- The assembly step shared by the three class-preservation endpoints: once the priced
stream's trades are the source trades under a per-position price map `g`, the two frame
legs of the gated join are that map composed with `frameLeg`, at the budget the source's
own trade count sets.  The trade-run count is exact here because a nonempty priced
strategy makes the contraction readable, which rules out the poison branch of
`rpnTradeCountAt_eq_frameTradeCount`. -/
private lemma frameLegs_of_priced_trades (tfP tokP lenP lenT : ℕ → ℕ) (n : ℕ)
    (ts : List ℕ) (hvts : vpre tfP n (lenP n) = ts)
    (hvL : vpre tokP n (lenT n) = unRpn ts) (hlen : ts.length = lenP n)
    (ψn : Sentence) (ε : ℚ) (g : EF → EF) (L : List (EF × Sentence)) (hL : L ≠ [])
    (hprice : (strategyOfTokens n (unRpn ts)).trades =
      L.map fun tr => (g tr.1, tr.2)) :
    (strategyOfTokens n (unRpn ts)).trades.map
        (frameLeg false ψn ε (frameBudget n (rpnTradeCountAt tfP n (lenP n))) n) ++
      (strategyOfTokens n (unRpn ts)).trades.map
        (frameLeg true ψn ε (frameBudget n (rpnTradeCountAt tfP n (lenP n))) n) =
      L.map (fun p => frameLeg false ψn ε
          (Strategy.localConditioningBudget (conditioningBudget n) L.length) n
          (g p.1, p.2)) ++
        L.map (fun p => frameLeg true ψn ε
          (Strategy.localConditioningBudget (conditioningBudget n) L.length) n
          (g p.1, p.2)) := by
  have hpricedNe : (strategyOfTokens n (unRpn ts)).trades ≠ [] := by
    rw [hprice]
    simpa using hL
  have hdecodePriced :=
    deserializeTrades_eq_some_of_strategyOfTokens_trades_ne_nil n (unRpn ts) hpricedNe
  have hreadyPriced := streamReadFrom_eq_ready_of_deserializeTrades_eq_some
    (unRpn ts) (strategyOfTokens n (unRpn ts)).trades hdecodePriced
  have hreadyTokens :
      EF.streamReadFrom ((List.range (lenT n)).map fun i => tokP (Nat.pair n i))
          (some EF.streamInitial) =
        some ((0, none), ([], (strategyOfTokens n (unRpn ts)).trades)) := by
    rw [show ((List.range (lenT n)).map fun i => tokP (Nat.pair n i)) =
      unRpn ts from hvL]
    exact hreadyPriced
  have hcountTok : frameTradeCount tokP lenT n = L.length := by
    calc
      frameTradeCount tokP lenT n =
          (strategyOfTokens n (unRpn ts)).trades.length :=
        frameTradeCount_eq_length_of_read tokP lenT n
          ((0, none), ([], (strategyOfTokens n (unRpn ts)).trades)) hreadyTokens
      _ = L.length := by rw [hprice, List.length_map]
  have hnotUnread : ¬ Unreadable (unRpn ts) := by
    intro hU
    rw [hU.deserializeTrades_eq_none] at hdecodePriced
    simp at hdecodePriced
  have hcountSym : rpnTradeCountAt tfP n (lenP n) = frameTradeCount tokP lenT n := by
    rcases rpnTradeCountAt_eq_frameTradeCount tfP tokP lenT n ts
      (by rw [hlen]; exact hvts) hvL with h | hU
    · rw [← h, hlen]
    · exact absurd hU hnotUnread
  have hpos : 0 < L.length := List.length_pos_iff.mpr hL
  rw [hprice, hcountSym, hcountTok, frameBudget_eq n L.length hpos]
  simp only [List.map_map]
  rfl

/-- **The conditioning transduction is correct on any stream**: whenever a day-`n`
source token stream decodes to the trader's day-`n` strategy, the transduced stream
decodes to the conditioned trader's day-`n` strategy.  No efficiency class appears, so
this is the shared core of every class-preservation endpoint for `thm:scon`.
Paper node: `thm:scon` -/
lemma strategyOfTokens_rpnConditionOutput
    (blocks : ℕ → List ℕ) (ψ : ℕ → Sentence)
    (hblocks : ∀ d, parseRpn (blocks d).length (blocks d) = some (ψ d, []))
    (ε : ℚ) (T : Trader) (n : ℕ) (src : List ℕ)
    (hsrc : strategyOfTokens n (unRpn src) = T.strat n) :
    strategyOfTokens n (unRpn (rpnConditionOutput blocks ε n src)) =
      (T.conditionedTranslation ψ ε).strat n := by
  set ts : List ℕ := rpnGuardedConditionTokens (rpnPriceEmit blocks ε) n src with hts
  set tfP : ℕ → ℕ := fun w => ts.getD w.unpair.2 0 with htfP
  set lenP : ℕ → ℕ := fun _ => ts.length with hlenP
  set tokP : ℕ → ℕ := fun w => (unRpn ts).getD w.unpair.2 0 with htokP
  set lenT : ℕ → ℕ := fun _ => (unRpn ts).length with hlenT
  have hvts : vpre tfP n (lenP n) = ts := by
    rw [vpre, htfP, hlenP]
    simp only [Nat.unpair_pair]
    exact (list_eq_rangeMap_getD _).symm
  have hvL : vpre tokP n (lenT n) = unRpn ts := by
    rw [vpre, htokP, hlenT]
    simp only [Nat.unpair_pair]
    exact (list_eq_rangeMap_getD _).symm
  set q : ℚ := frameBudget n (rpnTradeCountAt tfP n (lenP n)) with hq
  have hout : rpnConditionOutput blocks ε n src =
      rpnSafeSeparatedFrameOutput tfP lenP (blocks n) ε n
        (Encodable.encode q) (Encodable.encode q⁻¹) ts := by
    rw [rpnSafeSeparatedFrameOutput_eq_runs tfP lenP (blocks n) ε n _ _ ts hvts,
      rpnConditionOutput, ← hts, hq, ← frameBudgetCode_exact,
      ← frameInverseBudgetCode_exact, rpnTradeCountAt_eq_runs, hvts]
  rw [hout]
  have hjoin := strategyOfTokens_unRpn_rpnSafeSeparatedFrameOutput_trades
    tfP tokP lenP lenT (blocks n) (hblocks n) ε q n ts hvts hvL
  refine Strategy.ext ?_
  rw [hjoin]
  have hprice : (strategyOfTokens n (unRpn ts)).trades =
      (T.strat n).trades.map fun trade =>
        (trade.1.retainedConditionPrices ψ ε, trade.2) := by
    rw [hts, strategyOfTokens_rpnGuardedConditionTokens_trades blocks ψ
      hblocks ε n src, hsrc]
  have hframes := strategyOfTokens_safeSeparatedFrameTokenOutput_trades
    tokP lenT (ψ n) ε q n (unRpn ts) hvL.symm
  rw [hframes]
  by_cases hempty : (T.strat n).trades = []
  · rw [hprice, hempty]
    simp [Trader.conditionedTranslation,
      Strategy.separatedLocallyGatedConditionalContract]
    exact hempty
  · rw [hq, frameLegs_of_priced_trades tfP tokP lenP lenT n ts hvts hvL rfl (ψ n) ε
      (fun e : EF => e.retainedConditionPrices ψ ε) (T.strat n).trades hempty hprice]
    simp only [frameLeg_retained_eq_locallyGatedFirstLeg,
      frameLeg_retained_eq_locallyGatedSecondLeg]
    rfl

/-- **The finite-zero conditioning transduction**: the guarded zero-aware price pass
followed by the gated two-leg frame pass, whose budget is set by the priced stream's own
trade-run count. -/
def rpnZeroAwareOutput (zeroDays : Finset ℕ) (blocks : ℕ → List ℕ) (ε : ℚ) (n : ℕ)
    (ts : List ℕ) : List ℕ :=
  rpnSafeSeparatedFrameRuns (blocks n) ε n
    (frameBudgetCode n (rpnTradeRuns (rcPack 0 0 0)
      (rpnGuardedConditionTokens (rpnZeroAwareEmit zeroDays blocks ε) n ts)))
    (frameInverseBudgetCode n (rpnTradeRuns (rcPack 0 0 0)
      (rpnGuardedConditionTokens (rpnZeroAwareEmit zeroDays blocks ε) n ts)))
    (rpnGuardedConditionTokens (rpnZeroAwareEmit zeroDays blocks ε) n ts)

/-- **The zero-aware conditioning transduction is correct on any stream.**  The same
statement as `strategyOfTokens_rpnConditionOutput` for the finite-zero price rewrite: the
transduced stream decodes to the except-zero gated contract over the trader's day-`n`
strategy.  No efficiency class appears, so this is the shared core of every
class-preservation endpoint for the eventual form of `thm:scon`.
Paper node: `thm:scon` -/
lemma strategyOfTokens_rpnZeroAwareOutput
    (zeroDays : Finset ℕ) (blocks : ℕ → List ℕ) (ψ : ℕ → Sentence)
    (hblocks : ∀ d, parseRpn (blocks d).length (blocks d) = some (ψ d, []))
    (ε : ℚ) (T : Trader) (n : ℕ) (src : List ℕ)
    (hsrc : strategyOfTokens n (unRpn src) = T.strat n) :
    strategyOfTokens n (unRpn (rpnZeroAwareOutput zeroDays blocks ε n src)) =
      (T.strat n).separatedExceptZeroConditionalContract zeroDays ψ ε
        (conditioningBudget n) := by
  set ts : List ℕ := rpnGuardedConditionTokens (rpnZeroAwareEmit zeroDays blocks ε) n src with hts
  set tfP : ℕ → ℕ := fun w => ts.getD w.unpair.2 0 with htfP
  set lenP : ℕ → ℕ := fun _ => ts.length with hlenP
  set tokP : ℕ → ℕ := fun w => (unRpn ts).getD w.unpair.2 0 with htokP
  set lenT : ℕ → ℕ := fun _ => (unRpn ts).length with hlenT
  have hvts : vpre tfP n (lenP n) = ts := by
    rw [vpre, htfP, hlenP]
    simp only [Nat.unpair_pair]
    exact (list_eq_rangeMap_getD _).symm
  have hvL : vpre tokP n (lenT n) = unRpn ts := by
    rw [vpre, htokP, hlenT]
    simp only [Nat.unpair_pair]
    exact (list_eq_rangeMap_getD _).symm
  set q : ℚ := frameBudget n (rpnTradeCountAt tfP n (lenP n)) with hq
  have hout : rpnZeroAwareOutput zeroDays blocks ε n src =
      rpnSafeSeparatedFrameOutput tfP lenP (blocks n) ε n
        (Encodable.encode q) (Encodable.encode q⁻¹) ts := by
    rw [rpnSafeSeparatedFrameOutput_eq_runs tfP lenP (blocks n) ε n _ _ ts hvts,
      rpnZeroAwareOutput, ← hts, hq, ← frameBudgetCode_exact,
      ← frameInverseBudgetCode_exact, rpnTradeCountAt_eq_runs, hvts]
  rw [hout]
  have hjoin := strategyOfTokens_unRpn_rpnSafeSeparatedFrameOutput_trades
    tfP tokP lenP lenT (blocks n) (hblocks n) ε q n ts hvts hvL
  refine Strategy.ext ?_
  rw [hjoin]
  have hprice : (strategyOfTokens n (unRpn ts)).trades =
      (T.strat n).trades.map fun trade =>
        (trade.1.retainedConditionPricesExceptZero zeroDays ψ ε, trade.2) := by
    rw [hts, strategyOfTokens_rpnGuardedZeroAwareConditionTokens_trades zeroDays blocks ψ
      hblocks ε n src, hsrc]
  have hframes := strategyOfTokens_safeSeparatedFrameTokenOutput_trades
    tokP lenT (ψ n) ε q n (unRpn ts) hvL.symm
  rw [hframes]
  by_cases hempty : (T.strat n).trades = []
  · rw [hprice, hempty]
    simp [Strategy.separatedExceptZeroConditionalContract]
    exact hempty
  · rw [hq, frameLegs_of_priced_trades tfP tokP lenP lenT n ts hvts hvL rfl (ψ n) ε
      (fun e : EF => e.retainedConditionPricesExceptZero zeroDays ψ ε)
      (T.strat n).trades hempty hprice]
    simp only [frameLeg_exceptZero_eq_locallyGatedFirstLeg,
      frameLeg_exceptZero_eq_locallyGatedSecondLeg]
    rfl

/-! ## The class-preservation endpoints

The assembly: the source certificate gives the clocked digit stream of the RPN-expanded
strategy serialization; the guarded price pass rewrites its price days
(`rpnGuardedConditionRun_polySegStream` for emission,
`strategyOfTokens_rpnGuardedConditionTokens_trades` for agreement); the gated frame
join splices the two conditional legs (`rpnSafeSeparatedFrameOutput_polySegStream`,
`strategyOfTokens_unRpn_rpnSafeSeparatedFrameOutput_trades`); the budget codes are set
by the symbol-level trade-run count, exact against the token model
(`rpnTradeCountAt_eq_frameTradeCount`); and `ec_of_rawSegStream` digitizes back into an
`EfficientlyComputable` certificate. -/

/-- **The gated conditioning translation preserves the `dd:fuel` certificate**:
`EfficientlyComputable` → `EfficientlyComputable`, over any `𝓔𝓒` sentence sequence in
the write-out class `BigSentenceCodes`, in which a condition's Gödel code may be
exponential in the day.  The paper's own class `def:ec` is transported by
`CondStep.conditionedTranslation_preserves_machine`.
Paper node: `thm:scon` -/
lemma conditionedTranslation_preserves_ecRpn
    (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ) (ε : ℚ)
    (T : Trader) (hT : EfficientlyComputable T) :
    EfficientlyComputable (T.conditionedTranslation ψ ε) := by
  obtain ⟨lengthCode, tokenCode, a, k, hcert⟩ := hT
  obtain ⟨blocks, hblocksPoly, hblocksParse⟩ := hψ
  let source : ℕ → List ℕ := fun n =>
    clockedTokens lengthCode tokenCode (PrefixPatchCompile.ecClock a k n) n
  have hsource : PolySegStream source :=
    PrefixPatchCompile.clockedTokens_polySegStream lengthCode tokenCode a k
  let priced : ℕ → List ℕ := fun n =>
    digitize (rpnGuardedConditionTokens (rpnPriceEmit blocks ε) n
      (undigitize (source n)))
  have hpriced : PolySegStream priced :=
    rpnGuardedConditionRun_polySegStream hsource hblocksPoly ε
  set tfP : ℕ → ℕ := fun w => (undigitize (priced w.unpair.1)).getD w.unpair.2 0
    with htfP
  set lenP : ℕ → ℕ := fun m => (undigitize (priced m)).length with hlenP
  obtain ⟨ctc, htc⟩ := rpnTradeCountScan hpriced
  obtain ⟨⟨ccnt, hcnt⟩, -⟩ := hpriced.undigitizeTokens
  have hcountF : PolyFueled _ (fun n => rpnTradeCountAt tfP n (lenP n)) :=
    (htc.comp (PolyFueled.id.pair hcnt)).of_eq fun n => by
      simp only [Nat.unpair_pair]
      rfl
  obtain ⟨⟨cb, hbF⟩, ⟨ci, hiF⟩⟩ := frameBudgetCodes_polyFueled PolyFueled.id hcountF
  let framed : ℕ → List ℕ := fun n =>
    digitize (rpnSafeSeparatedFrameOutput tfP lenP (blocks n) ε n
      (frameBudgetCode n (rpnTradeCountAt tfP n (lenP n)))
      (frameInverseBudgetCode n (rpnTradeCountAt tfP n (lenP n)))
      (undigitize (priced n)))
  have hframed : PolySegStream framed :=
    rpnSafeSeparatedFrameOutput_polySegStream hpriced hblocksPoly hbF hiF ε
  apply ec_of_rawSegStream (T.conditionedTranslation ψ ε) hframed
  intro n
  have hraw : undigitize (priced n) =
      rpnGuardedConditionTokens (rpnPriceEmit blocks ε) n (undigitize (source n)) :=
    undigitize_digitize _
  have hvts : vpre tfP n (lenP n) = undigitize (priced n) := by
    rw [vpre, htfP, hlenP]
    simp only [Nat.unpair_pair]
    exact (list_eq_rangeMap_getD _).symm
  have hundig : undigitize (framed n) =
      rpnConditionOutput blocks ε n (undigitize (source n)) := by
    show undigitize (digitize _) = _
    rw [undigitize_digitize,
      rpnSafeSeparatedFrameOutput_eq_runs tfP lenP (blocks n) ε n _ _
        (undigitize (priced n)) hvts,
      rpnConditionOutput, ← hraw, rpnTradeCountAt_eq_runs, hvts]
  rw [hundig]
  exact strategyOfTokens_rpnConditionOutput blocks ψ hblocksParse ε T n
    (undigitize (source n)) (congrFun (congrArg Trader.strat hcert) n)

/-- **The eventual (finite-zero, launch-gated) conditioning translation preserves the
`dd:fuel` certificate**: `EfficientlyComputable` → `EfficientlyComputable`.  The paper's
own class `def:ec` is transported by
`CondStep.eventualConditionedTranslation_preserves_machine`.
Paper node: `thm:scon` -/
lemma eventualConditionedTranslation_preserves_ecRpn
    {P : History} {ψ : ℕ → Sentence}
    (F : EventualConditioningFloor P ψ) (hψ : BigSentenceCodes ψ)
    (T : Trader) (hT : EfficientlyComputable T) :
    EfficientlyComputable (T.eventualConditionedTranslation F) := by
  obtain ⟨lengthCode, tokenCode, a, k, hcert⟩ := hT
  obtain ⟨blocks, hblocksPoly, hblocksParse⟩ := hψ
  let source : ℕ → List ℕ := fun n =>
    clockedTokens lengthCode tokenCode (PrefixPatchCompile.ecClock a k n) n
  have hsource : PolySegStream source :=
    PrefixPatchCompile.clockedTokens_polySegStream lengthCode tokenCode a k
  let priced : ℕ → List ℕ := fun n =>
    digitize (rpnGuardedConditionTokens
      (rpnZeroAwareEmit F.zeroDays blocks F.epsilon) n (undigitize (source n)))
  have hpriced : PolySegStream priced :=
    rpnGuardedZeroAwareConditionRun_polySegStream F.zeroDays hsource hblocksPoly
      F.epsilon
  set tfP : ℕ → ℕ := fun w => (undigitize (priced w.unpair.1)).getD w.unpair.2 0
    with htfP
  set lenP : ℕ → ℕ := fun m => (undigitize (priced m)).length with hlenP
  obtain ⟨ctc, htc⟩ := rpnTradeCountScan hpriced
  obtain ⟨⟨ccnt, hcnt⟩, -⟩ := hpriced.undigitizeTokens
  have hcountF : PolyFueled _ (fun n => rpnTradeCountAt tfP n (lenP n)) :=
    (htc.comp (PolyFueled.id.pair hcnt)).of_eq fun n => by
      simp only [Nat.unpair_pair]
      rfl
  obtain ⟨⟨cb, hbF⟩, ⟨ci, hiF⟩⟩ := frameBudgetCodes_polyFueled PolyFueled.id hcountF
  let framed : ℕ → List ℕ := fun n =>
    digitize (rpnSafeSeparatedFrameOutput tfP lenP (blocks n) F.epsilon n
      (frameBudgetCode n (rpnTradeCountAt tfP n (lenP n)))
      (frameInverseBudgetCode n (rpnTradeCountAt tfP n (lenP n)))
      (undigitize (priced n)))
  have hframed : PolySegStream framed :=
    rpnSafeSeparatedFrameOutput_polySegStream hpriced hblocksPoly hbF hiF F.epsilon
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
  apply ec_of_rawSegStream (T.eventualConditionedTranslation F) houtput
  intro n
  by_cases hn : n < F.cutoff
  · have hout : output n = [] := by
      show (if F.cutoff ≤ n then framed n else []) = []
      rw [if_neg (by omega)]
    rw [hout, T.eventualConditionedTranslation_strat_of_lt F hn]
    simp [strategyOfTokens, deserializeTrades, unRpn, unRpnTokens,
      EF.streamReadFrom, EF.streamInitial, Trader.zero, undigitize]
    rfl
  · have hcn : F.cutoff ≤ n := Nat.le_of_not_gt hn
    have hout : output n = framed n := by
      show (if F.cutoff ≤ n then framed n else []) = framed n
      rw [if_pos hcn]
    rw [hout]
    set ts : List ℕ := undigitize (priced n) with hts
    set tokP : ℕ → ℕ := fun w => (unRpn (undigitize (priced w.unpair.1))).getD
      w.unpair.2 0 with htokP
    set lenT : ℕ → ℕ := fun m => (unRpn (undigitize (priced m))).length with hlenT
    have hvts : vpre tfP n (lenP n) = ts := by
      rw [vpre, hts, htfP, hlenP]
      simp only [Nat.unpair_pair]
      exact (list_eq_rangeMap_getD _).symm
    have hvL : vpre tokP n (lenT n) = unRpn ts := by
      rw [vpre, hts, htokP, hlenT]
      simp only [Nat.unpair_pair]
      exact (list_eq_rangeMap_getD _).symm
    set q : ℚ := frameBudget n (rpnTradeCountAt tfP n (lenP n)) with hq
    have hundig : undigitize (framed n) =
        rpnSafeSeparatedFrameOutput tfP lenP (blocks n) F.epsilon n
          (Encodable.encode q) (Encodable.encode q⁻¹) ts := by
      show undigitize (digitize _) = _
      rw [undigitize_digitize, frameBudgetCode_exact, frameInverseBudgetCode_exact]
    rw [hundig]
    have hjoin := strategyOfTokens_unRpn_rpnSafeSeparatedFrameOutput_trades
      tfP tokP lenP lenT (blocks n) (hblocksParse n) F.epsilon q n ts hvts hvL
    refine Strategy.ext ?_
    rw [hjoin]
    have horig : strategyOfTokens n (unRpn (undigitize (source n))) = T.strat n :=
      congrFun (congrArg Trader.strat hcert) n
    have hprice : (strategyOfTokens n (unRpn ts)).trades =
        (T.strat n).trades.map fun trade =>
          (trade.1.retainedConditionPricesExceptZero F.zeroDays ψ F.epsilon,
            trade.2) := by
      have hraw : ts = rpnGuardedConditionTokens
          (rpnZeroAwareEmit F.zeroDays blocks F.epsilon) n
          (undigitize (source n)) := by
        rw [hts]
        exact undigitize_digitize _
      rw [hraw, strategyOfTokens_rpnGuardedZeroAwareConditionTokens_trades
        F.zeroDays blocks ψ hblocksParse F.epsilon n (undigitize (source n)), horig]
    have hframes := strategyOfTokens_safeSeparatedFrameTokenOutput_trades
      tokP lenT (ψ n) F.epsilon q n (unRpn ts) hvL.symm
    have htarget := T.eventualConditionedTranslation_strat_of_le F hcn
    rw [hframes, htarget]
    by_cases hempty : (T.strat n).trades = []
    · rw [hprice, hempty]
      simp [Strategy.separatedExceptZeroConditionalContract]
      exact hempty
    · rw [hq, frameLegs_of_priced_trades tfP tokP lenP lenT n ts hvts hvL rfl (ψ n)
        F.epsilon
        (fun e : EF => e.retainedConditionPricesExceptZero F.zeroDays ψ F.epsilon)
        (T.strat n).trades hempty hprice]
      simp only [frameLeg_exceptZero_eq_locallyGatedFirstLeg,
        frameLeg_exceptZero_eq_locallyGatedSecondLeg]
      rfl

end RpnConditioning
end LogicalInduction
