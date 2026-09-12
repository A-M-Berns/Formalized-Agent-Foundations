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

The frame pass has none of its own.  Its emission obligations are discharged on the machine
side, through the class-agnostic transduction in `Transduction.lean`; the shared automaton
and its scalars are what this file supplies.

## Endpoints and consumers

This module publishes no class-preservation capstone.  `def:ec` is read on ordinary
machines, so `thm:scon`'s transports are the machine ones in
`Construction/Conditioning/TransductionFrame.lean`, and closure of the fuel calculus under
the conditioning translation would be a fact about the certification engine rather than a
paper claim.  What this module supplies is the shared machinery — the automaton, the
scalars, the frame legs and the transports over them — which
`Construction/Conditioning/Transduction.lean` imports and reuses in the machine rendering
that *is* paper-facing.  The fifteen `thm:scon`-annotated lemmas below are infrastructure
of that rendering, inventoried in `AxiomAudit.lean` as such rather than as endpoints;
`LogicalInduction/API.lean` lists this compiler as implementation, not interface.

This module renders the conditioning transducer in the RPN symbol model; the provenance
lines sit on the declarations below, not on this header.
-/

namespace LogicalInduction

namespace RpnConditioning

open ConditioningCompile

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
          -- Chunk: a price tag `0` with its sentence block and day token.
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
          · -- Chunk: a trade tag `6` with its sentence block.
            by_cases ht6 : t = 6
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
              · push Not at ht1
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
          -- Chunk: a price tag `0` with its sentence block and day token.
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
          · -- Chunk: a trade tag `6` with its sentence block.
            by_cases ht6 : t = 6
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
              · push Not at ht1
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
          -- Chunk: a price tag `0` with its sentence block and day token.
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
                  push Not at hex
                  have hmods : ∀ i, i ≤ rest.length →
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                        (rest.take i)) ≠ 2 := fun i hi => hex i hi
                  have hend := priceWalk_inside rest rest.length le_rfl hmods
                  rw [List.take_length] at hend
                  rw [List.foldl_cons, rpnCondStep_base_price] at hbase
                  rw [hbase, rcMode_pack] at hend
                  omega
          · -- Chunk: a trade tag `6` with its sentence block.
            by_cases ht6 : t = 6
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
                    push Not at hex
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
              · push Not at ht1
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

/-! ### The frame-pass master commutation

The commutation is proved by one induction that peels a *chunk* — a price tag with its
sentence block and day, a trade tag with its block, a payload tag with its code, or a lone
copied token — off the source and appeals to the induction hypothesis on the remainder
through `UnRpnContractsTo.frameAgree_chunk` and `FrameContract.cons_chunk`.  The cases that
do *not* reach the induction hypothesis are the leaves below: the empty stream, a price
block that runs out before its day, and an unparsable price or trade run, where both sides
poison.  They are stated separately so the induction itself reads as the chunk peeling it
is. -/

/-- The joint claim the frame-pass chunk induction carries on each stream: unconditional
agreement with the token model, and — under the base-mode invariant the acceptance gate
tests — the stronger prefix form. -/
private abbrev FrameJoint (second : Bool) (blkψ : List ℕ) (ψn : Sentence) (ε : ℚ)
    (day bc ibc : ℕ) (ts : List ℕ) : Prop :=
  FrameAgree (unRpn (rpnFrameOutput second blkψ ε day bc ibc ts))
      (conditioningFrameTokenOutput second (Encodable.encode ψn) day ε bc ibc
        (unRpn ts)) ∧
    (List.foldl rpnCondStep (rcPack 0 0 0) ts = rcPack 0 0 0 →
      FrameContract (rpnFrameOutput second blkψ ε day bc ibc ts)
        (conditioningFrameTokenOutput second (Encodable.encode ψn) day ε bc ibc
          (unRpn ts)))

/-- Leaf: the empty stream.  Both sides emit nothing. -/
private lemma frameJoint_nil (second : Bool) (blkψ : List ℕ) (ψn : Sentence) (ε : ℚ)
    (day bc ibc : ℕ) : FrameJoint second blkψ ψn ε day bc ibc [] := by
  have hA : rpnFrameOutput second blkψ ε day bc ibc [] = [] := by
    simp [rpnFrameOutput, rpnFrameRun]
  have hB : conditioningFrameTokenOutput second (Encodable.encode ψn) day ε bc
      ibc (unRpn []) = [] := by
    simp [conditioningFrameTokenOutput, conditioningFrameTokenRun, unRpn_nil]
  exact ⟨Or.inl (by rw [hA, hB, unRpn_nil]),
    fun _ => Or.inl (by rw [hA, hB]; exact UnRpnContractsTo.nil)⟩

/-- Leaf: a price tag and a complete sentence block, with no day token after it.  The
rewrite copies the stream, and the base-mode hypothesis is unsatisfiable because the run
stops in the price-day slot. -/
private lemma frameJoint_price_complete (second : Bool) (blkψ : List ℕ) (ψn : Sentence)
    (ε : ℚ) (day bc ibc : ℕ) {rest : List ℕ} {φ : Sentence}
    (hblk : parseRpn rest.length rest = some (φ, [])) :
    FrameJoint second blkψ ψn ε day bc ibc (0 :: rest) := by
  obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_price_block hblk
  have hcopyBlk := rpnFrameRun_copy_of_modes second blkψ ε day bc ibc
    (rcPack 1 1 0) [] rest (fun k hk => by
      have := hinv k hk; omega)
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

/-- Leaf: a price tag whose run never parses.  Either the run reaches the price-day slot,
in which case it poisons every extension, or it never leaves the run, in which case the
rewrite copies the stream; both sides are unreadable either way. -/
private lemma frameJoint_price_unparsable (second : Bool) (blkψ : List ℕ) (ψn : Sentence)
    (ε : ℚ) (day bc ibc : ℕ) {rest : List ℕ}
    (hp : parseRpn rest.length rest = none) :
    FrameJoint second blkψ ψn ε day bc ibc (0 :: rest) := by
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

/-- Leaf: a trade tag whose run never parses.  The same two shapes as the price leaf, with
the trade run's own exit condition. -/
private lemma frameJoint_trade_unparsable (second : Bool) (blkψ : List ℕ) (ψn : Sentence)
    (ε : ℚ) (day bc ibc : ℕ) {rest : List ℕ}
    (hp : parseRpn rest.length rest = none) :
    FrameJoint second blkψ ψn ε day bc ibc (6 :: rest) := by
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
  · push Not at hex
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

/-- Leaf: a bare escape tag with no payload after it. -/
private lemma frameJoint_escape_bare (second : Bool) (blkψ : List ℕ) (ψn : Sentence)
    (ε : ℚ) (day bc ibc : ℕ) :
    FrameJoint second blkψ ψn ε day bc ibc [1] := by
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

/-- Leaf: a bare structured-payload tag with no payload after it. -/
private lemma frameJoint_structured_bare (second : Bool) (blkψ : List ℕ) (ψn : Sentence)
    (ε : ℚ) (day bc ibc : ℕ) :
    FrameJoint second blkψ ψn ε day bc ibc [7] := by
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
      exact frameJoint_nil second blkψ ψn ε day bc ibc
  | succ N ih =>
      intro ts hts
      match ts with
      | [] => exact frameJoint_nil second blkψ ψn ε day bc ibc
      | t :: rest =>
          simp only [List.length_cons] at hts
          -- Chunk: a price tag `0` with its sentence block and day token.
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
                    exact frameJoint_price_complete second blkψ ψn ε day bc ibc hblk
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
                exact frameJoint_price_unparsable second blkψ ψn ε day bc ibc hp
          · -- Chunk: a trade tag `6` with its sentence block.
            by_cases ht6 : t = 6
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
                  exact frameJoint_trade_unparsable second blkψ ψn ε day bc ibc hp
            · -- Chunk: an escape tag `1` with its opaque payload code.
              by_cases ht1 : t = 1
              · subst ht1
                match rest with
                | [] => exact frameJoint_escape_bare second blkψ ψn ε day bc ibc
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
              · -- Chunk: a structured-payload tag `7` with its code.
                by_cases ht7 : t = 7
                · subst ht7
                  match rest with
                  | [] => exact frameJoint_structured_bare second blkψ ψn ε day bc ibc
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

/-! ### The gated two-leg join

`safeSeparatedFrameTokenOutput` emits the first frame leg alone unless the source is
structurally accepting, in which case it emits both.  The symbol side mirrors that shape
off `rpnStructurallyAccepts`.  Because the join appends two frame outputs, its agreement
with the token model runs through the prefix form `FrameContract` of the frame agreement
rather than `FrameAgree`, which does not survive an append. -/

/-- **The gated two-leg join at symbol level** (mirror of
`safeSeparatedFrameTokenOutput`): both frame legs are emitted only at a structurally
accepting source boundary. -/
def rpnSafeSeparatedFrameOutput (tf lenF : ℕ → ℕ) (blkψ : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (ts : List ℕ) : List ℕ :=
  let first := rpnFrameOutput false blkψ ε day bc ibc ts
  let second := rpnFrameOutput true blkψ ε day bc ibc ts
  if rpnStructurallyAccepts tf lenF day = 0 then first else first ++ second

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
  · push Not at hguard
    obtain ⟨j, hj, hm, hday⟩ := hguard
    rw [unRpn_nil, strategyOfTokens_nil_trades,
      strategyOfTokens_unRpn_trades_eq_nil_of_rpnBigDay n ts j hj hm hday]
    rfl

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

/-- The assembly shared by both conditioning transductions: over any price emitter whose
guarded pass rewrites the source trades by a coefficient map `g`, the gated two-leg join
decodes to the two `frameLeg` maps of those trades, at the budget the trade count sets.
The two capstones below differ only in `g` and in the contract they then recognize. -/
private lemma strategyOfTokens_gatedFrameOutput_trades
    (emit : List ℕ → ℕ → List ℕ) (g : EF → EF) (blkψ : List ℕ) {ψn : Sentence}
    (hblkψ : parseRpn blkψ.length blkψ = some (ψn, []))
    (ε : ℚ) (L : List (EF × Sentence)) (n : ℕ) (src : List ℕ)
    (hprice : (strategyOfTokens n
        (unRpn (rpnGuardedConditionTokens emit n src))).trades =
      L.map fun trade => (g trade.1, trade.2)) :
    (strategyOfTokens n (unRpn (rpnSafeSeparatedFrameRuns blkψ ε n
        (frameBudgetCode n (rpnTradeRuns (rcPack 0 0 0)
          (rpnGuardedConditionTokens emit n src)))
        (frameInverseBudgetCode n (rpnTradeRuns (rcPack 0 0 0)
          (rpnGuardedConditionTokens emit n src)))
        (rpnGuardedConditionTokens emit n src)))).trades =
      L.map (fun p => frameLeg false ψn ε
          (Strategy.localConditioningBudget (conditioningBudget n) L.length) n
          (g p.1, p.2)) ++
        L.map (fun p => frameLeg true ψn ε
          (Strategy.localConditioningBudget (conditioningBudget n) L.length) n
          (g p.1, p.2)) := by
  set ts : List ℕ := rpnGuardedConditionTokens emit n src with hts
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
  have hout : rpnSafeSeparatedFrameRuns blkψ ε n
        (frameBudgetCode n (rpnTradeRuns (rcPack 0 0 0) ts))
        (frameInverseBudgetCode n (rpnTradeRuns (rcPack 0 0 0) ts)) ts =
      rpnSafeSeparatedFrameOutput tfP lenP blkψ ε n
        (Encodable.encode q) (Encodable.encode q⁻¹) ts := by
    rw [rpnSafeSeparatedFrameOutput_eq_runs tfP lenP blkψ ε n _ _ ts hvts, hq,
      ← frameBudgetCode_exact, ← frameInverseBudgetCode_exact,
      rpnTradeCountAt_eq_runs, hvts]
  rw [hout]
  have hjoin := strategyOfTokens_unRpn_rpnSafeSeparatedFrameOutput_trades
    tfP tokP lenP lenT blkψ hblkψ ε q n ts hvts hvL
  rw [hjoin]
  have hframes := strategyOfTokens_safeSeparatedFrameTokenOutput_trades
    tokP lenT ψn ε q n (unRpn ts) hvL.symm
  rw [hframes]
  by_cases hempty : L = []
  · rw [hprice, hempty]
    simp
  · rw [hq, frameLegs_of_priced_trades tfP tokP lenP lenT n ts hvts hvL rfl ψn ε
      g L hempty hprice]

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
  refine Strategy.ext ?_
  rw [rpnConditionOutput,
    strategyOfTokens_gatedFrameOutput_trades (rpnPriceEmit blocks ε)
      (fun e : EF => e.retainedConditionPrices ψ ε) (blocks n) (hblocks n) ε
      (T.strat n).trades n src
      (by rw [strategyOfTokens_rpnGuardedConditionTokens_trades blocks ψ hblocks ε n src,
        hsrc])]
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
  refine Strategy.ext ?_
  rw [rpnZeroAwareOutput,
    strategyOfTokens_gatedFrameOutput_trades (rpnZeroAwareEmit zeroDays blocks ε)
      (fun e : EF => e.retainedConditionPricesExceptZero zeroDays ψ ε)
      (blocks n) (hblocks n) ε (T.strat n).trades n src
      (by rw [strategyOfTokens_rpnGuardedZeroAwareConditionTokens_trades zeroDays blocks ψ
        hblocks ε n src, hsrc])]
  simp only [frameLeg_exceptZero_eq_locallyGatedFirstLeg,
    frameLeg_exceptZero_eq_locallyGatedSecondLeg]
  rfl

end RpnConditioning
end LogicalInduction
