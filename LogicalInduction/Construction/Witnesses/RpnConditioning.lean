/-
# Symbol-level conditioning translation compiler

Closure under conditioning asks that conditioning an efficiently computable trader on a
computable sentence sequence again yield an efficiently computable trader.  Efficiency
(`EfficientlyComputable`) is metered on the RPN-expanded strategy stream, in which a
sentence slot is a whole symbol **run** rather than a single code.  The rewrite must
therefore walk the flat grammar with a run-aware automaton (a pending-subtree counter)
and splice the condition sentence as a *block*, using the fact that conjunction is
concatenation under the `3` shell: `rpn (φ ⋏ ψ) = 3 :: rpn φ ++ rpn ψ`.  The companion
compiler in `DigitConditioning.lean` rewrites the *contracted* stream instead, where a
sentence slot is one token.

Contents:

* the run-aware mode automaton `rpnCondStep` (packed state `⟨mode, counter, runLen⟩`)
  and the **run–parse correspondence**: over any block `parseRpn` consumes completely,
  the automaton walks the run and exits exactly at the block boundary;
* the **price pass** `rpnConditionRun`: a streaming transducer copying every input
  token and, at each price-day position, appending the RPN expansion of the conditional
  price expression — the buffered sentence run re-spliced into the conjunction shell,
  the condition block drawn from an `RpnSentenceCodes` stream — so that contracting the
  output reproduces the token-model rewrite `conditionPriceTokenRun` of the contracted
  input (`unRpn_rpnConditionRun`, anchored per chunk by `unRpn_price_rewrite_chunk`);
* the **frame pass** `rpnFrameRun` / `rpnFrameOutput`, replacing each trade run by the
  locally gated leg body, with its agreement `frameAgree_unRpn_rpnFrameOutput`, budget
  exactness `rpnTradeCountAt_eq_frameTradeCount`, and the gated two-leg join
  `rpnSafeSeparatedFrameOutput`;
* the emission certificates `rpnGuardedConditionRun_polySegStream` and
  `rpnFrameOutput_polySegStream`: each pass carries a digit `PolySegStream` to a digit
  `PolySegStream`;
* the class-preservation endpoints `conditionedTranslation_preserves_ecRpn` (gated) and
  `eventualConditionedTranslation_preserves_ecRpn` (finite-zero, launch-gated), and the
  paper-facing conditioning theorems assembled from them.

Paper node: `thm:scon` (symbol-metered conditioning translation).
-/
import LogicalInduction.Construction.Witnesses.DigitConditioning
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.Compactness

namespace LogicalInduction

namespace RpnConditioning

open Nat.Partrec (Code)
open Nat.Partrec.Code
open ConditioningCompile

-- `Primrec`/`PolyFueled` elaboration over deep product types unfolds `Nat.sqrt`'s
-- well-founded definition during `whnf` (through `Nat.pair`/`unpair`) and loops; making
-- it locally irreducible stops that.
attribute [local irreducible] Nat.sqrt

/-! ## The run-aware automaton state

Packed as `Nat.pair mode (Nat.pair counter runLen)`.  Modes:

* `0` — base (strategy grammar);
* `1` — inside a price sentence run (counter = open subtrees);
* `6` — escape payload inside a price run;
* `2` — price-day slot (the run just completed; the current token is the day);
* `4` — inside a trade sentence run; `7` — escape payload inside a trade run;
* `3` / `5` — opaque payload after a base-level `1` / `7` tag.

`runLen` counts the tokens of the current sentence run (price *and* trade runs track
it uniformly; only price runs consume it). -/

def rcPack (m c r : ℕ) : ℕ := Nat.pair m (Nat.pair c r)

def rcMode (st : ℕ) : ℕ := st.unpair.1
def rcCnt (st : ℕ) : ℕ := st.unpair.2.unpair.1
def rcLen (st : ℕ) : ℕ := st.unpair.2.unpair.2

@[simp] lemma rcMode_pack (m c r : ℕ) : rcMode (rcPack m c r) = m := by
  simp [rcMode, rcPack]

@[simp] lemma rcCnt_pack (m c r : ℕ) : rcCnt (rcPack m c r) = c := by
  simp [rcCnt, rcPack]

@[simp] lemma rcLen_pack (m c r : ℕ) : rcLen (rcPack m c r) = r := by
  simp [rcLen, rcPack]

lemma rcPack_surjective (st : ℕ) : st = rcPack (rcMode st) (rcCnt st) (rcLen st) := by
  simp [rcPack, rcMode, rcCnt, rcLen]

/-- One step of the run-aware conditioning automaton. -/
def rpnCondStep (st t : ℕ) : ℕ :=
  let m := rcMode st
  let c := rcCnt st
  let r := rcLen st
  if m = 0 then
    if t = 0 then rcPack 1 1 0
    else if t = 1 then rcPack 3 0 0
    else if t = 6 then rcPack 4 1 0
    else if t = 7 then rcPack 5 0 0
    else rcPack 0 0 0
  else if m = 1 then
    if t = 1 then rcPack 6 c (r + 1)
    else if t = 2 ∨ t = 3 ∨ t = 4 then rcPack 1 (c + 1) (r + 1)
    else if c ≤ 1 then rcPack 2 0 (r + 1) else rcPack 1 (c - 1) (r + 1)
  else if m = 6 then
    if c ≤ 1 then rcPack 2 0 (r + 1) else rcPack 1 (c - 1) (r + 1)
  else if m = 4 then
    if t = 1 then rcPack 7 c (r + 1)
    else if t = 2 ∨ t = 3 ∨ t = 4 then rcPack 4 (c + 1) (r + 1)
    else if c ≤ 1 then rcPack 0 0 0 else rcPack 4 (c - 1) (r + 1)
  else if m = 7 then
    if c ≤ 1 then rcPack 0 0 0 else rcPack 4 (c - 1) (r + 1)
  else rcPack 0 0 0

/-- The automaton only tests the small grammar tags, so it factors through the clamp. -/
lemma rpnCondStep_clamp (st t : ℕ) :
    rpnCondStep st (min t 9) = rpnCondStep st t := by
  by_cases h : t ≤ 9
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega : 9 ≤ t)]
    rw [rpnCondStep, rpnCondStep]
    have e0 : ¬ t = 0 := by omega
    have e1 : ¬ t = 1 := by omega
    have e234 : ¬ (t = 2 ∨ t = 3 ∨ t = 4) := by omega
    have e6 : ¬ t = 6 := by omega
    have e7 : ¬ t = 7 := by omega
    simp only [e0, e1, e234, e6, e7, if_false,
      show ((9 : ℕ) = 0) = False by simp, show ((9 : ℕ) = 1) = False by simp,
      show ((9 : ℕ) = 2 ∨ (9 : ℕ) = 3 ∨ (9 : ℕ) = 4) = False by simp,
      show ((9 : ℕ) = 6) = False by simp, show ((9 : ℕ) = 7) = False by simp]

lemma rcMode_step_le (st t : ℕ) : rcMode (rpnCondStep st t) ≤ 7 := by
  rw [rpnCondStep]
  split_ifs <;> simp

lemma rcCnt_step_le (st t : ℕ) : rcCnt (rpnCondStep st t) ≤ rcCnt st + 1 := by
  rw [rpnCondStep]
  split_ifs <;> simp <;> omega

/-- The run length either resets or grows by one. -/
lemma rcLen_step (st t : ℕ) :
    rcLen (rpnCondStep st t) = 0 ∨
      rcLen (rpnCondStep st t) = rcLen st + 1 := by
  rw [rpnCondStep]
  split_ifs <;> simp

lemma rcLen_step_le (st t : ℕ) : rcLen (rpnCondStep st t) ≤ rcLen st + 1 := by
  rcases rcLen_step st t with h | h <;> omega

/-! ## The run–parse correspondence

Whenever `parseRpn` consumes a block, the automaton started inside a run walks exactly
that block: the counter drops by one net, hits its minimum only at the block boundary,
and the run length grows by the block length.  Price runs (`1`/`6`) and trade runs
(`4`/`7`) share the walk shape, so one generic lemma serves both. -/

/-- Generic run walk: a sentence-run mode pair `(a, b)` with an arbitrary exit. -/
lemma foldl_rpnCondStep_run {a b : ℕ} {exit : ℕ → ℕ}
    (hrun : ∀ c r t, rpnCondStep (rcPack a (c + 1) r) t =
      if t = 1 then rcPack b (c + 1) (r + 1)
      else if t = 2 ∨ t = 3 ∨ t = 4 then rcPack a (c + 2) (r + 1)
      else if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (hesc : ∀ c r t, rpnCondStep (rcPack b (c + 1) r) t =
      if c = 0 then exit (r + 1) else rcPack a c (r + 1)) :
    ∀ (fuel : ℕ) (ts : List ℕ) {φ : Sentence} {rest : List ℕ},
      parseRpn fuel ts = some (φ, rest) →
      ∃ blk, ts = blk ++ rest ∧
        (∀ c r, List.foldl rpnCondStep (rcPack a (c + 1) r) blk =
          if c = 0 then exit (r + blk.length) else rcPack a c (r + blk.length)) ∧
        (∀ c r k, k < blk.length →
          rcMode (List.foldl rpnCondStep (rcPack a (c + 1) r) (blk.take k)) = a ∨
          rcMode (List.foldl rpnCondStep (rcPack a (c + 1) r) (blk.take k)) = b) := by
  intro fuel
  induction fuel with
  | zero => intro ts φ rest h; simp [parseRpn] at h
  | succ fuel ih =>
      intro ts φ rest h
      match ts with
      | [] => simp at h
      | t :: ts' =>
          rw [parseRpn_cons] at h
          by_cases h0 : t = 0
          · rw [if_pos h0] at h
            obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
            subst h0
            refine ⟨[0], rfl, fun c r => ?_, fun c r k hk => ?_⟩
            · rw [List.foldl_cons, List.foldl_nil, hrun]
              by_cases hc : c = 0 <;> simp [hc]
            · simp only [List.length_cons, List.length_nil] at hk
              have hk0 : k = 0 := by omega
              subst hk0
              simp only [List.take_zero, List.foldl_nil, rcMode_pack]
              exact Or.inl trivial
          · rw [if_neg h0] at h
            by_cases h1 : t = 1
            · rw [if_pos h1] at h
              match ts' with
              | [] => simp at h
              | c₀ :: ts'' =>
                  rw [List.head?_cons] at h
                  simp only [Option.bind_some] at h
                  cases hdec : Encodable.decode (α := Sentence) c₀ with
                  | none => rw [hdec] at h; simp at h
                  | some ψ =>
                      rw [hdec] at h
                      simp only [Option.map_some,
                        List.tail_cons] at h
                      obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
                      subst h1
                      refine ⟨[1, c₀], rfl, fun c r => ?_, fun c r k hk => ?_⟩
                      · rw [List.foldl_cons, List.foldl_cons, List.foldl_nil,
                          hrun, if_pos rfl, hesc]
                        by_cases hc : c = 0 <;> simp [hc]
                      · simp only [List.length_cons, List.length_nil] at hk
                        match k, hk with
                        | 0, _ =>
                            simp only [List.take_zero, List.foldl_nil,
                              rcMode_pack]
                            exact Or.inl trivial
                        | 1, _ =>
                            refine Or.inr ?_
                            show rcMode (List.foldl rpnCondStep
                              (rcPack a (c + 1) r) [1]) = b
                            rw [List.foldl_cons, List.foldl_nil, hrun,
                              if_pos rfl, rcMode_pack]
            · rw [if_neg h1] at h
              have hbin : ∀ (mk : Sentence → Sentence → Sentence),
                  ((parseRpn fuel ts').bind fun p =>
                    (parseRpn fuel p.2).bind fun q =>
                      some (mk p.1 q.1, q.2)) = some (φ, rest) →
                  (t = 2 ∨ t = 3 ∨ t = 4) →
                  ∃ blk, t :: ts' = blk ++ rest ∧
                    (∀ c r, List.foldl rpnCondStep (rcPack a (c + 1) r) blk =
                      if c = 0 then exit (r + blk.length)
                      else rcPack a c (r + blk.length)) ∧
                    (∀ c r k, k < blk.length →
                      rcMode (List.foldl rpnCondStep (rcPack a (c + 1) r)
                        (blk.take k)) = a ∨
                      rcMode (List.foldl rpnCondStep (rcPack a (c + 1) r)
                        (blk.take k)) = b) := by
                intro mk hh ht
                cases hp : parseRpn fuel ts' with
                | none => rw [hp] at hh; simp at hh
                | some p =>
                    rw [hp] at hh
                    simp only [Option.bind_some] at hh
                    cases hq : parseRpn fuel p.2 with
                    | none => rw [hq] at hh; simp at hh
                    | some q =>
                        rw [hq] at hh
                        simp only [Option.bind_some] at hh
                        obtain ⟨-, hrest⟩ :=
                          Prod.mk.injEq .. ▸ Option.some.inj hh
                        obtain ⟨blk₁, hts', hblk₁, hinv₁⟩ := ih ts' hp
                        obtain ⟨blk₂, hp2, hblk₂, hinv₂⟩ := ih p.2 hq
                        refine ⟨t :: blk₁ ++ blk₂, by
                          rw [hts', hp2, hrest]; simp, fun c r => ?_,
                          fun c r k hk => ?_⟩
                        · rw [List.cons_append, List.foldl_cons, hrun,
                            if_neg h1, if_pos ht, List.foldl_append]
                          have hb1 := hblk₁ (c + 1) (r + 1)
                          rw [if_neg (by omega)] at hb1
                          rw [show rcPack a (c + 1 + 1) (r + 1) =
                            rcPack a ((c + 1) + 1) (r + 1) from rfl, hb1]
                          rw [hblk₂ c (r + 1 + blk₁.length)]
                          simp only [List.length_append, List.length_cons]
                          by_cases hc : c = 0
                          · rw [if_pos hc, if_pos hc]
                            congr 1
                            omega
                          · rw [if_neg hc, if_neg hc]
                            congr 1
                            omega
                        · simp only [List.length_append, List.length_cons] at hk
                          rcases Nat.eq_zero_or_pos k with rfl | hkpos
                          · simp only [List.take_zero, List.foldl_nil,
                              rcMode_pack]
                            exact Or.inl trivial
                          · rw [List.cons_append,
                              show k = (k - 1) + 1 by omega, List.take_succ_cons,
                              List.foldl_cons, hrun, if_neg h1, if_pos ht,
                              List.take_append, List.foldl_append]
                            by_cases hj : k - 1 < blk₁.length
                            · rw [Nat.sub_eq_zero_of_le (le_of_lt hj),
                                List.take_zero, List.foldl_nil]
                              exact hinv₁ (c + 1) (r + 1) (k - 1) hj
                            · have hb1 := hblk₁ (c + 1) (r + 1)
                              rw [if_neg (by omega)] at hb1
                              rw [List.take_of_length_le (by omega),
                                show rcPack a (c + 1 + 1) (r + 1) =
                                  rcPack a ((c + 1) + 1) (r + 1) from rfl, hb1]
                              by_cases hj2 : k - 1 = blk₁.length
                              · rw [hj2, Nat.sub_self, List.take_zero,
                                  List.foldl_nil, rcMode_pack]
                                exact Or.inl rfl
                              · exact hinv₂ c (r + 1 + blk₁.length)
                                  (k - 1 - blk₁.length) (by omega)
              by_cases h2 : t = 2
              · rw [if_pos h2] at h
                exact hbin _ h (Or.inl h2)
              · rw [if_neg h2] at h
                by_cases h3 : t = 3
                · rw [if_pos h3] at h
                  exact hbin _ h (Or.inr (Or.inl h3))
                · rw [if_neg h3] at h
                  by_cases h4 : t = 4
                  · rw [if_pos h4] at h
                    exact hbin _ h (Or.inr (Or.inr h4))
                  · rw [if_neg h4] at h
                    obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
                    refine ⟨[t], rfl, fun c r => ?_, fun c r k hk => ?_⟩
                    · rw [List.foldl_cons, List.foldl_nil, hrun, if_neg h1,
                        if_neg (by omega)]
                      by_cases hc : c = 0 <;> simp [hc]
                    · simp only [List.length_cons, List.length_nil] at hk
                      have hk0 : k = 0 := by omega
                      subst hk0
                      simp only [List.take_zero, List.foldl_nil, rcMode_pack]
                      exact Or.inl trivial

/-- Price-run instance: the walk exits into the day-expect mode `2`. -/
lemma foldl_rpnCondStep_price_run (fuel : ℕ) (ts : List ℕ) {φ : Sentence}
    {rest : List ℕ} (h : parseRpn fuel ts = some (φ, rest)) :
    ∃ blk, ts = blk ++ rest ∧
      (∀ c r, List.foldl rpnCondStep (rcPack 1 (c + 1) r) blk =
        if c = 0 then rcPack 2 0 (r + blk.length)
        else rcPack 1 c (r + blk.length)) ∧
      (∀ c r k, k < blk.length →
        rcMode (List.foldl rpnCondStep (rcPack 1 (c + 1) r) (blk.take k)) = 1 ∨
        rcMode (List.foldl rpnCondStep (rcPack 1 (c + 1) r) (blk.take k)) = 6) := by
  refine foldl_rpnCondStep_run (b := 6) (exit := fun r' => rcPack 2 0 r')
    (fun c r t => ?_) (fun c r t => ?_) fuel ts h
  · rw [rpnCondStep]
    simp only [rcMode_pack, rcCnt_pack, rcLen_pack]
    split_ifs <;> simp only [rcPack, Nat.pair_eq_pair, true_and, and_true] <;> first | omega | (exfalso; assumption)
  · rw [rpnCondStep]
    simp only [rcMode_pack, rcCnt_pack, rcLen_pack]
    split_ifs <;> simp only [rcPack, Nat.pair_eq_pair, true_and, and_true] <;> first | omega | (exfalso; assumption)

/-- Trade-run instance: the walk exits back to base. -/
lemma foldl_rpnCondStep_trade_run (fuel : ℕ) (ts : List ℕ) {φ : Sentence}
    {rest : List ℕ} (h : parseRpn fuel ts = some (φ, rest)) :
    ∃ blk, ts = blk ++ rest ∧
      (∀ c r, List.foldl rpnCondStep (rcPack 4 (c + 1) r) blk =
        if c = 0 then rcPack 0 0 0 else rcPack 4 c (r + blk.length)) ∧
      (∀ c r k, k < blk.length →
        rcMode (List.foldl rpnCondStep (rcPack 4 (c + 1) r) (blk.take k)) = 4 ∨
        rcMode (List.foldl rpnCondStep (rcPack 4 (c + 1) r) (blk.take k)) = 7) := by
  refine foldl_rpnCondStep_run (b := 7) (exit := fun _ => rcPack 0 0 0)
    (fun c r t => ?_) (fun c r t => ?_) fuel ts h
  · rw [rpnCondStep]
    simp only [rcMode_pack, rcCnt_pack, rcLen_pack]
    split_ifs <;> simp only [rcPack, Nat.pair_eq_pair, true_and, and_true] <;> first | omega | (exfalso; assumption)
  · rw [rpnCondStep]
    simp only [rcMode_pack, rcCnt_pack, rcLen_pack]
    split_ifs <;> simp only [rcPack, Nat.pair_eq_pair, true_and, and_true] <;> first | omega | (exfalso; assumption)

/-- A complete price sentence block walks from the run entry to the day slot, with the
run length recording exactly the block length. -/
lemma foldl_rpnCondStep_price_block {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) :
    List.foldl rpnCondStep (rcPack 1 1 0) b = rcPack 2 0 b.length ∧
    ∀ k < b.length,
      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (b.take k)) = 1 ∨
      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (b.take k)) = 6 := by
  obtain ⟨blk, hts, hblk, hinv⟩ := foldl_rpnCondStep_price_run b.length b hb
  rw [List.append_nil] at hts
  subst hts
  exact ⟨by simpa using hblk 0 0, fun k hk => hinv 0 0 k hk⟩

/-- A complete trade sentence block walks from the run entry back to base. -/
lemma foldl_rpnCondStep_trade_block {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) :
    List.foldl rpnCondStep (rcPack 4 1 0) b = rcPack 0 0 0 ∧
    ∀ k < b.length,
      rcMode (List.foldl rpnCondStep (rcPack 4 1 0) (b.take k)) = 4 ∨
      rcMode (List.foldl rpnCondStep (rcPack 4 1 0) (b.take k)) = 7 := by
  obtain ⟨blk, hts, hblk, hinv⟩ := foldl_rpnCondStep_trade_run b.length b hb
  rw [List.append_nil] at hts
  subst hts
  exact ⟨by simpa using hblk 0 0, fun k hk => hinv 0 0 k hk⟩

/-! ## The price rewrite

The transducer copies every token; at a price-day position (mode `2`, token `D`) it
emits the copied day, the RPN expansion of the conditional price expression — with the
buffered sentence run re-spliced into the conjunction shell and the condition block
`blk` (a self-delimiting block parsing to `ψ D`) spliced twice — and the letE close
`8`, so the contraction replays `conditionPriceTokenRun`'s output exactly. -/

/-- The emitted rewrite at a price-day position. -/
def rpnConditionEmit (blk : List ℕ) (ε : ℚ) (buf : List ℕ) (D : ℕ) : List ℕ :=
  D ::
    1 :: Encodable.encode (-1 : ℚ) ::
    1 :: Encodable.encode (-1 : ℚ) ::
    1 :: Encodable.encode (1 : ℚ) :: 3 ::
    1 :: Encodable.encode (-1 : ℚ) ::
    0 :: 3 :: (buf ++ blk ++
      D :: 1 :: Encodable.encode (1 / ε : ℚ) ::
        1 :: Encodable.encode (1 / ε : ℚ) :: 0 :: (blk ++
          [D, 3, 5, 3, 3, 3, 4, 3, 8]))

/-- The price emitter of the conditioning compiler: at a price day `D`, splice the
condition block `blocks D` into the buffered run's conjunction shell. -/
def rpnPriceEmit (blocks : ℕ → List ℕ) (ε : ℚ) : List ℕ → ℕ → List ℕ :=
  fun buf D => rpnConditionEmit (blocks D) ε buf D

/-- Streaming buffer update: reset whenever the automaton leaves (or is outside) a
sentence run, extend inside one — the buffer is exactly the current run. -/
def rpnCondBuf (st : ℕ) (buf : List ℕ) (t : ℕ) : List ℕ :=
  if rcLen (rpnCondStep st t) = 0 then [] else buf ++ [t]

/-- The streaming price rewrite: state, run buffer, and emitted output. -/
def rpnConditionRun (emit : List ℕ → ℕ → List ℕ) :
    ℕ × List ℕ → List ℕ → (ℕ × List ℕ) × List ℕ
  | s, [] => (s, [])
  | (st, buf), t :: ts =>
      let rest := rpnConditionRun emit
        (rpnCondStep st t, rpnCondBuf st buf t) ts
      (rest.1,
        (if rcMode st = 2 then emit buf t else [t])
          ++ rest.2)

@[simp] lemma rpnConditionRun_nil (emit : List ℕ → ℕ → List ℕ) (s : ℕ × List ℕ) :
    rpnConditionRun emit s [] = (s, []) := rfl

lemma rpnConditionRun_append (emit : List ℕ → ℕ → List ℕ)
    (s : ℕ × List ℕ) (xs ys : List ℕ) :
    rpnConditionRun emit s (xs ++ ys) =
      let first := rpnConditionRun emit s xs
      let second := rpnConditionRun emit first.1 ys
      (second.1, first.2 ++ second.2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨st, buf⟩ := s
      simp only [List.cons_append, rpnConditionRun]
      rw [ih]
      simp [List.append_assoc]

/-- At a non-emitting position (control mode ≠ `2`) the transducer copies the token
through and leaves the buffer to the streaming update. -/
lemma rpnConditionRun_copy (emit : List ℕ → ℕ → List ℕ)
    (st : ℕ) (buf : List ℕ) (t : ℕ) (hm : rcMode st ≠ 2) (ts : List ℕ) :
    rpnConditionRun emit (st, buf) (t :: ts) =
      let rest := rpnConditionRun emit
        (rpnCondStep st t, rpnCondBuf st buf t) ts
      (rest.1, t :: rest.2) := by
  simp [rpnConditionRun, hm]

/-! ## Per-chunk contraction (the correctness anchor)

The contraction of the rewritten price chunk is the token-model rewrite of the
contracted chunk: `[0, ⌜φ⌝, D]` followed by `rawConditionalPriceTokens` and the letE
close.  This is the identity that lets the token-model correctness lemmas
(`strategyOfTokens_conditionPriceTokenRun_trades`) carry the symbol-level compiler. -/

/-- Conjunction of self-delimiting blocks is concatenation under the `3` shell. -/
lemma parseRpn_and_block {b₁ b₂ : List ℕ} {φ ψ : Sentence}
    (h₁ : parseRpn b₁.length b₁ = some (φ, []))
    (h₂ : parseRpn b₂.length b₂ = some (ψ, [])) :
    parseRpn (3 :: b₁ ++ b₂).length (3 :: b₁ ++ b₂) = some (φ ⋏ ψ, []) := by
  rw [List.cons_append, List.length_cons, parseRpn_cons,
    if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  rw [parseRpn_block_head h₁ b₂ (by simp)]
  simp only [Option.bind_some]
  rw [parseRpn_mono b₂ (by simp) h₂]
  rfl

/-- **The rewritten price chunk contracts to the token-model rewrite.** -/
lemma unRpn_price_rewrite_chunk {b blk : List ℕ} {φ ψn : Sentence}
    (hb : parseRpn b.length b = some (φ, []))
    (hblk : parseRpn blk.length blk = some (ψn, []))
    (D : ℕ) (ε : ℚ) (rest : List ℕ) :
    unRpn (0 :: b ++ rpnConditionEmit blk ε b D ++ rest) =
      0 :: Encodable.encode φ :: D ::
        (rawConditionalPriceTokens (Encodable.encode φ) (Encodable.encode ψn) D ε ++
          8 :: unRpn rest) := by
  have hand : parseRpn (3 :: b ++ blk).length (3 :: b ++ blk) =
      some (φ ⋏ ψn, []) := parseRpn_and_block hb hblk
  -- Reassociate to expose the leading original price chunk.
  have hshape : 0 :: b ++ rpnConditionEmit blk ε b D ++ rest =
      0 :: (b ++ D ::
        (1 :: Encodable.encode (-1 : ℚ) ::
         1 :: Encodable.encode (-1 : ℚ) ::
         1 :: Encodable.encode (1 : ℚ) :: 3 ::
         1 :: Encodable.encode (-1 : ℚ) ::
         (0 :: ((3 :: b ++ blk) ++ D ::
           (1 :: Encodable.encode (1 / ε : ℚ) ::
            1 :: Encodable.encode (1 / ε : ℚ) ::
            (0 :: (blk ++ D ::
              (3 :: 5 :: 3 :: 3 :: 3 :: 4 :: 3 :: 8 :: rest)))))))) := by
    simp [rpnConditionEmit]
  rw [hshape, unRpn_price_chunk_block hb]
  rw [unRpn_payload_chunk 1 _ (Or.inl rfl), unRpn_payload_chunk 1 _ (Or.inl rfl),
    unRpn_payload_chunk 1 _ (Or.inl rfl),
    unRpn_single_chunk 3 (by norm_num),
    unRpn_payload_chunk 1 _ (Or.inl rfl),
    unRpn_price_chunk_block hand,
    unRpn_payload_chunk 1 _ (Or.inl rfl), unRpn_payload_chunk 1 _ (Or.inl rfl),
    unRpn_price_chunk_block hblk,
    unRpn_single_chunk 3 (by norm_num), unRpn_single_chunk 5 (by norm_num),
    unRpn_single_chunk 3 (by norm_num), unRpn_single_chunk 3 (by norm_num),
    unRpn_single_chunk 3 (by norm_num), unRpn_single_chunk 4 (by norm_num),
    unRpn_single_chunk 3 (by norm_num), unRpn_single_chunk 8 (by norm_num)]
  rw [← conjunctionCode_exact]
  simp [rawConditionalPriceTokens, rawMinTokens, rawMulTokens, rawMaxTokens,
    rawSafeRecipTokens, rawPriceTokens, rawConstTokens, rawLowerSafeRecipTokens]

/-! ## Per-position views

The emission certificate reads the transducer per position: control state before
index `j`, the buffered run recovered *by position* (the last `rcLen` tokens), and the
per-position segment whose concatenation is the transducer output. -/

/-- Control state before source-token index `j` (mirror of
`EF.freezeTokenControlAt`). -/
def rpnCondControlAt (tf : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => rcPack 0 0 0
  | j + 1 => rpnCondStep (rpnCondControlAt tf n j) (tf (Nat.pair n j))

lemma rpnCondControlAt_eq_foldl (tf : ℕ → ℕ) (n : ℕ) : ∀ j,
    rpnCondControlAt tf n j = (vpre tf n j).foldl rpnCondStep (rcPack 0 0 0)
  | 0 => by simp [rpnCondControlAt, vpre]
  | j + 1 => by
      rw [rpnCondControlAt, rpnCondControlAt_eq_foldl tf n j, vpre_succ,
        List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma rcLen_controlAt_le (tf : ℕ → ℕ) (n : ℕ) : ∀ j,
    rcLen (rpnCondControlAt tf n j) ≤ j
  | 0 => by simp [rpnCondControlAt]
  | j + 1 => by
      rcases rcLen_step (rpnCondControlAt tf n j) (tf (Nat.pair n j)) with h | h <;>
        rw [rpnCondControlAt, h] <;>
        [omega; exact Nat.succ_le_succ (rcLen_controlAt_le tf n j)]

/-- The buffered run before index `j`, recovered by position: the `rcLen` tokens
immediately preceding `j`. -/
def rpnCondWindow (tf : ℕ → ℕ) (n j : ℕ) : List ℕ :=
  (List.range (rcLen (rpnCondControlAt tf n j))).map fun i =>
    tf (Nat.pair n (j - rcLen (rpnCondControlAt tf n j) + i))

@[simp] lemma rpnCondWindow_zero (tf : ℕ → ℕ) (n : ℕ) :
    rpnCondWindow tf n 0 = [] := by
  simp [rpnCondWindow, rpnCondControlAt]

/-- One source-token segment of the price rewrite. -/
def rpnConditionSegment (tf : ℕ → ℕ) (emit : List ℕ → ℕ → List ℕ) (z : ℕ) :
    List ℕ :=
  if rcMode (rpnCondControlAt tf z.unpair.1 z.unpair.2) = 2 then
    emit (rpnCondWindow tf z.unpair.1 z.unpair.2) (tf z)
  else [tf z]

/-- The streaming buffer tracks the position window. -/
lemma rpnCondBuf_window (tf : ℕ → ℕ) (n j : ℕ) :
    rpnCondBuf (rpnCondControlAt tf n j) (rpnCondWindow tf n j)
        (tf (Nat.pair n j)) = rpnCondWindow tf n (j + 1) := by
  have hstep : rpnCondStep (rpnCondControlAt tf n j) (tf (Nat.pair n j)) =
      rpnCondControlAt tf n (j + 1) := rfl
  rw [rpnCondBuf, hstep]
  rcases rcLen_step (rpnCondControlAt tf n j) (tf (Nat.pair n j)) with h | h <;>
    rw [hstep] at h
  · rw [if_pos h, rpnCondWindow, h]
    simp
  · rw [if_neg (by omega)]
    have hle := rcLen_controlAt_le tf n j
    rw [rpnCondWindow, rpnCondWindow, h, List.range_succ, List.map_append]
    congr 1
    · refine List.map_congr_left fun i _ => ?_
      congr 2
      omega
    · simp only [List.map_cons, List.map_nil]
      have harg : j + 1 - (rcLen (rpnCondControlAt tf n j) + 1) +
          rcLen (rpnCondControlAt tf n j) = j := by omega
      rw [harg]

/-- **Range form of the price rewrite**: over the per-position view of any stream, the
transducer's final state is the position control, its buffer the position window, and
its output the concatenation of the per-position segments. -/
lemma rpnConditionRun_range (tf : ℕ → ℕ) (emit : List ℕ → ℕ → List ℕ)
    (n count : ℕ) :
    rpnConditionRun emit (rcPack 0 0 0, [])
        ((List.range count).map fun j => tf (Nat.pair n j)) =
      ((rpnCondControlAt tf n count, rpnCondWindow tf n count),
        (List.range count).flatMap fun j =>
          rpnConditionSegment tf emit (Nat.pair n j)) := by
  induction count with
  | zero => simp [rpnCondControlAt]
  | succ count ih =>
      rw [List.range_succ, List.map_append, rpnConditionRun_append, ih]
      simp only [List.map_cons, List.map_nil,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rw [show rpnConditionRun emit
          (rpnCondControlAt tf n count, rpnCondWindow tf n count)
          [tf (Nat.pair n count)] =
        ((rpnCondStep (rpnCondControlAt tf n count) (tf (Nat.pair n count)),
          rpnCondBuf (rpnCondControlAt tf n count) (rpnCondWindow tf n count)
            (tf (Nat.pair n count))),
          (if rcMode (rpnCondControlAt tf n count) = 2 then
            emit (rpnCondWindow tf n count) (tf (Nat.pair n count))
          else [tf (Nat.pair n count)]) ++ []) from rfl]
      rw [rpnCondBuf_window,
        show rpnCondStep (rpnCondControlAt tf n count) (tf (Nat.pair n count)) =
          rpnCondControlAt tf n (count + 1) from rfl]
      simp only [List.append_nil]
      refine congrArg₂ Prod.mk rfl (congrArg₂ (· ++ ·) rfl ?_)
      rw [rpnConditionSegment]
      simp only [Nat.unpair_pair]

/-! ## The guarded rewrite (specification)

As in the digit model, price-day tokens are compared against the trading day: the
emitted condition blocks are drawn at the day index, so an oversized day would demand
a block the clock cannot afford.  The guarded rewrite emits the ordinary output when
every price-day token is within the trading day and the empty stream otherwise (an
oversized day forces the empty validated strategy on both sides). -/

/-- The guarded symbol-level price rewrite. -/
def rpnGuardedConditionTokens (emit : List ℕ → ℕ → List ℕ) (n : ℕ)
    (ts : List ℕ) : List ℕ :=
  if ∀ j < ts.length,
      rcMode ((ts.take j).foldl rpnCondStep (rcPack 0 0 0)) = 2 →
        ts.getD j 0 ≤ n
  then (rpnConditionRun emit (rcPack 0 0 0, []) ts).2
  else []

#print axioms foldl_rpnCondStep_price_block
#print axioms foldl_rpnCondStep_trade_block
#print axioms rpnConditionRun_range
#print axioms unRpn_price_rewrite_chunk

/-! ## Scalar components of the step (the fueled decomposition)

The packed step splits into three scalar functions of `(mode, counter, runLen, token)`
whose branch tests are single equalities/inequalities — the shape the `ifzSel`
cascades arithmetize.  All token tests factor through the clamp `min t 8`. -/

def rcModeF (m c t : ℕ) : ℕ :=
  if m = 0 then
    if t = 0 then 1 else if t = 1 then 3 else if t = 6 then 4
    else if t = 7 then 5 else 0
  else if m = 1 then
    if t = 1 then 6
    else if t = 2 then 1 else if t = 3 then 1 else if t = 4 then 1
    else if c ≤ 1 then 2 else 1
  else if m = 6 then if c ≤ 1 then 2 else 1
  else if m = 4 then
    if t = 1 then 7
    else if t = 2 then 4 else if t = 3 then 4 else if t = 4 then 4
    else if c ≤ 1 then 0 else 4
  else if m = 7 then if c ≤ 1 then 0 else 4
  else 0

def rcCntF (m c t : ℕ) : ℕ :=
  if m = 0 then (if t = 0 then 1 else if t = 6 then 1 else 0)
  else if m = 1 then
    if t = 1 then c
    else if t = 2 then c + 1 else if t = 3 then c + 1 else if t = 4 then c + 1
    else if c ≤ 1 then 0 else c - 1
  else if m = 6 then if c ≤ 1 then 0 else c - 1
  else if m = 4 then
    if t = 1 then c
    else if t = 2 then c + 1 else if t = 3 then c + 1 else if t = 4 then c + 1
    else if c ≤ 1 then 0 else c - 1
  else if m = 7 then if c ≤ 1 then 0 else c - 1
  else 0

def rcLenF (m c r t : ℕ) : ℕ :=
  if m = 0 then 0
  else if m = 1 then r + 1
  else if m = 6 then r + 1
  else if m = 4 then
    if t = 1 then r + 1
    else if t = 2 then r + 1 else if t = 3 then r + 1 else if t = 4 then r + 1
    else if c ≤ 1 then 0 else r + 1
  else if m = 7 then if c ≤ 1 then 0 else r + 1
  else 0

lemma rcMode_step_eq (st t : ℕ) :
    rcMode (rpnCondStep st t) = rcModeF (rcMode st) (rcCnt st) t := by
  rw [rpnCondStep, rcModeF]
  split_ifs <;> simp only [rcMode_pack] <;> omega

lemma rcCnt_step_eq (st t : ℕ) :
    rcCnt (rpnCondStep st t) = rcCntF (rcMode st) (rcCnt st) t := by
  rw [rpnCondStep, rcCntF]
  split_ifs <;> simp only [rcCnt_pack] <;> omega

lemma rcLen_step_eq (st t : ℕ) :
    rcLen (rpnCondStep st t) = rcLenF (rcMode st) (rcCnt st) (rcLen st) t := by
  rw [rpnCondStep, rcLenF]
  split_ifs <;> simp only [rcLen_pack] <;> omega

/-- The packed step through its scalar components. -/
lemma rpnCondStep_components (st t : ℕ) :
    rpnCondStep st t = rcPack (rcModeF (rcMode st) (rcCnt st) t)
      (rcCntF (rcMode st) (rcCnt st) t)
      (rcLenF (rcMode st) (rcCnt st) (rcLen st) t) := by
  conv_lhs => rw [rcPack_surjective (rpnCondStep st t)]
  rw [rcMode_step_eq, rcCnt_step_eq, rcLen_step_eq]

/-! ## Control bounds (for the polynomially bounded scan state) -/

lemma rcMode_controlAt_le (tf : ℕ → ℕ) (n : ℕ) : ∀ j,
    rcMode (rpnCondControlAt tf n j) ≤ 7
  | 0 => by simp [rpnCondControlAt]
  | j + 1 => by
      rw [rpnCondControlAt]
      exact rcMode_step_le _ _

lemma rcCnt_controlAt_le (tf : ℕ → ℕ) (n : ℕ) : ∀ j,
    rcCnt (rpnCondControlAt tf n j) ≤ j + 1
  | 0 => by simp [rpnCondControlAt]
  | j + 1 => by
      rw [rpnCondControlAt]
      exact le_trans (rcCnt_step_le _ _)
        (Nat.succ_le_succ (rcCnt_controlAt_le tf n j))

lemma rpnCondControlAt_le (tf : ℕ → ℕ) (n j : ℕ) :
    rpnCondControlAt tf n j ≤ Nat.pair 7 (Nat.pair (j + 1) j) := by
  conv_lhs => rw [rcPack_surjective (rpnCondControlAt tf n j)]
  rw [rcPack]
  calc Nat.pair (rcMode (rpnCondControlAt tf n j))
        (Nat.pair (rcCnt (rpnCondControlAt tf n j))
          (rcLen (rpnCondControlAt tf n j))) ≤
      Nat.pair 7 (Nat.pair (rcCnt (rpnCondControlAt tf n j))
        (rcLen (rpnCondControlAt tf n j))) :=
        pair_le_pair_left' _ (rcMode_controlAt_le tf n j)
    _ ≤ Nat.pair 7 (Nat.pair (j + 1) j) :=
        pair_le_pair_right' _
          (le_trans (pair_le_pair_left' _ (rcCnt_controlAt_le tf n j))
            (pair_le_pair_right' _ (rcLen_controlAt_le tf n j)))

/-! ## Fueled `if` combinators -/

private lemma polyFueled_ifz {c₁ c₂ c₃ : Code} {A B T : ℕ → ℕ}
    (hA : PolyFueled c₁ A) (hB : PolyFueled c₂ B) (hT : PolyFueled c₃ T) :
    ∃ c, PolyFueled c (fun z => if T z = 0 then A z else B z) :=
  ⟨_, (ifzSel_polyFueled.comp ((hA.pair hB).pair hT)).of_eq fun z => by
    simp only [Nat.unpair_pair, ifzSelFn]⟩

/-- Dispatch on an equality test `X z = k`. -/
private lemma polyFueled_ifEq {cx c₁ c₂ : Code} {X A B : ℕ → ℕ}
    (hX : PolyFueled cx X) (k : ℕ)
    (hA : PolyFueled c₁ A) (hB : PolyFueled c₂ B) :
    ∃ c, PolyFueled c (fun z => if X z = k then A z else B z) := by
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hT : PolyFueled _ (fun z => (X z - k) + (k - X z)) :=
    (had.comp ((subc_polyFueled.comp (hX.pair (PolyFueled.const k))).pair
      (subc_polyFueled.comp ((PolyFueled.const k).pair hX)))).of_eq fun z => by
        simp only [Nat.unpair_pair]
  obtain ⟨c, hc⟩ := polyFueled_ifz hA hB hT
  exact ⟨c, hc.of_eq fun z => by
    by_cases hk : X z = k
    · rw [if_pos (by omega), if_pos hk]
    · rw [if_neg (by omega), if_neg hk]⟩

/-- Dispatch on the counter test `X z ≤ 1`. -/
private lemma polyFueled_ifLeOne {cx c₁ c₂ : Code} {X A B : ℕ → ℕ}
    (hX : PolyFueled cx X) (hA : PolyFueled c₁ A) (hB : PolyFueled c₂ B) :
    ∃ c, PolyFueled c (fun z => if X z ≤ 1 then A z else B z) := by
  have hT : PolyFueled _ (fun z => X z - 1) :=
    (subc_polyFueled.comp (hX.pair (PolyFueled.const 1))).of_eq fun z => by
      simp only [Nat.unpair_pair]
  obtain ⟨c, hc⟩ := polyFueled_ifz hA hB hT
  exact ⟨c, hc.of_eq fun z => by
    by_cases hk : X z ≤ 1
    · rw [if_pos (by omega), if_pos hk]
    · rw [if_neg (by omega), if_neg hk]⟩

/-! ## Fueled component trees -/

lemma rcModeF_polyFueled {cm cc ct : Code} {m c t : ℕ → ℕ}
    (hm : PolyFueled cm m) (hc : PolyFueled cc c) (ht : PolyFueled ct t) :
    ∃ code, PolyFueled code (fun z => rcModeF (m z) (c z) (t z)) := by
  obtain ⟨_, hm0i⟩ := polyFueled_ifEq ht 7 (PolyFueled.const 5) (PolyFueled.const 0)
  obtain ⟨_, hm0h⟩ := polyFueled_ifEq ht 6 (PolyFueled.const 4) hm0i
  obtain ⟨_, hm0g⟩ := polyFueled_ifEq ht 1 (PolyFueled.const 3) hm0h
  obtain ⟨_, hm0⟩ := polyFueled_ifEq ht 0 (PolyFueled.const 1) hm0g
  obtain ⟨_, hle12⟩ := polyFueled_ifLeOne hc (PolyFueled.const 2) (PolyFueled.const 1)
  obtain ⟨_, hm1d⟩ := polyFueled_ifEq ht 4 (PolyFueled.const 1) hle12
  obtain ⟨_, hm1c⟩ := polyFueled_ifEq ht 3 (PolyFueled.const 1) hm1d
  obtain ⟨_, hm1b⟩ := polyFueled_ifEq ht 2 (PolyFueled.const 1) hm1c
  obtain ⟨_, hm1⟩ := polyFueled_ifEq ht 1 (PolyFueled.const 6) hm1b
  obtain ⟨_, hle04⟩ := polyFueled_ifLeOne hc (PolyFueled.const 0) (PolyFueled.const 4)
  obtain ⟨_, hm4d⟩ := polyFueled_ifEq ht 4 (PolyFueled.const 4) hle04
  obtain ⟨_, hm4c⟩ := polyFueled_ifEq ht 3 (PolyFueled.const 4) hm4d
  obtain ⟨_, hm4b⟩ := polyFueled_ifEq ht 2 (PolyFueled.const 4) hm4c
  obtain ⟨_, hm4⟩ := polyFueled_ifEq ht 1 (PolyFueled.const 7) hm4b
  obtain ⟨_, hT7⟩ := polyFueled_ifEq hm 7 hle04 (PolyFueled.const 0)
  obtain ⟨_, hT4⟩ := polyFueled_ifEq hm 4 hm4 hT7
  obtain ⟨_, hT6⟩ := polyFueled_ifEq hm 6 hle12 hT4
  obtain ⟨_, hT1⟩ := polyFueled_ifEq hm 1 hm1 hT6
  obtain ⟨code, hT0⟩ := polyFueled_ifEq hm 0 hm0 hT1
  exact ⟨code, hT0.of_eq fun z => by rw [rcModeF]⟩

lemma rcCntF_polyFueled {cm cc ct : Code} {m c t : ℕ → ℕ}
    (hm : PolyFueled cm m) (hc : PolyFueled cc c) (ht : PolyFueled ct t) :
    ∃ code, PolyFueled code (fun z => rcCntF (m z) (c z) (t z)) := by
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hsucc : PolyFueled _ (fun z => c z + 1) :=
    (had.comp (hc.pair (PolyFueled.const 1))).of_eq fun z => by
      simp only [Nat.unpair_pair]
  have hpred : PolyFueled _ (fun z => c z - 1) :=
    (subc_polyFueled.comp (hc.pair (PolyFueled.const 1))).of_eq fun z => by
      simp only [Nat.unpair_pair]
  obtain ⟨_, hm0i⟩ := polyFueled_ifEq ht 6 (PolyFueled.const 1) (PolyFueled.const 0)
  obtain ⟨_, hm0⟩ := polyFueled_ifEq ht 0 (PolyFueled.const 1) hm0i
  obtain ⟨_, hleC⟩ := polyFueled_ifLeOne hc (PolyFueled.const 0) hpred
  obtain ⟨_, hm1d⟩ := polyFueled_ifEq ht 4 hsucc hleC
  obtain ⟨_, hm1c⟩ := polyFueled_ifEq ht 3 hsucc hm1d
  obtain ⟨_, hm1b⟩ := polyFueled_ifEq ht 2 hsucc hm1c
  obtain ⟨_, hm1⟩ := polyFueled_ifEq ht 1 hc hm1b
  obtain ⟨_, hT7⟩ := polyFueled_ifEq hm 7 hleC (PolyFueled.const 0)
  obtain ⟨_, hT4⟩ := polyFueled_ifEq hm 4 hm1 hT7
  obtain ⟨_, hT6⟩ := polyFueled_ifEq hm 6 hleC hT4
  obtain ⟨_, hT1⟩ := polyFueled_ifEq hm 1 hm1 hT6
  obtain ⟨code, hT0⟩ := polyFueled_ifEq hm 0 hm0 hT1
  exact ⟨code, hT0.of_eq fun z => by rw [rcCntF]⟩

lemma rcLenF_polyFueled {cm cc cr ct : Code} {m c r t : ℕ → ℕ}
    (hm : PolyFueled cm m) (hc : PolyFueled cc c) (hr : PolyFueled cr r)
    (ht : PolyFueled ct t) :
    ∃ code, PolyFueled code (fun z => rcLenF (m z) (c z) (r z) (t z)) := by
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hsucc : PolyFueled _ (fun z => r z + 1) :=
    (had.comp (hr.pair (PolyFueled.const 1))).of_eq fun z => by
      simp only [Nat.unpair_pair]
  obtain ⟨_, hleR⟩ := polyFueled_ifLeOne hc (PolyFueled.const 0) hsucc
  obtain ⟨_, hm4d⟩ := polyFueled_ifEq ht 4 hsucc hleR
  obtain ⟨_, hm4c⟩ := polyFueled_ifEq ht 3 hsucc hm4d
  obtain ⟨_, hm4b⟩ := polyFueled_ifEq ht 2 hsucc hm4c
  obtain ⟨_, hm4⟩ := polyFueled_ifEq ht 1 hsucc hm4b
  obtain ⟨_, hT7⟩ := polyFueled_ifEq hm 7 hleR (PolyFueled.const 0)
  obtain ⟨_, hT4⟩ := polyFueled_ifEq hm 4 hm4 hT7
  obtain ⟨_, hT6⟩ := polyFueled_ifEq hm 6 hsucc hT4
  obtain ⟨_, hT1⟩ := polyFueled_ifEq hm 1 hsucc hT6
  obtain ⟨code, hT0⟩ := polyFueled_ifEq hm 0 (PolyFueled.const 0) hT1
  exact ⟨code, hT0.of_eq fun z => by rw [rcLenF]⟩

/-! ## The control scan

Over any digit `PolySegStream`, the packed control state at each token position of
the undigitized stream is poly-fueled (input `⟨n, j⟩`): the state is polynomially
bounded (counter and run length are at most the position), and every branch test of
the step factors through the token clamp. -/

lemma rpnCondScan {s : ℕ → List ℕ} (h : PolySegStream s) :
    ∃ c, PolyFueled c (fun z =>
      rpnCondControlAt (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0)
        z.unpair.1 z.unpair.2) := by
  obtain ⟨-, hbig⟩ := h.undigitizeTokens
  obtain ⟨ctc, htc⟩ := hbig.clampVal (PolyFueled.const 8)
  -- Step input `⟨n, ⟨j, prev⟩⟩`.
  have hn := PolyFueled.left
  have hj := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have htok := htc.comp (hn.pair hj)
  have hmode : PolyFueled _ (fun z : ℕ => rcMode (z.unpair.2.unpair.2)) :=
    PolyFueled.left.comp hprev
  have hcnt : PolyFueled _ (fun z : ℕ => rcCnt (z.unpair.2.unpair.2)) :=
    PolyFueled.left.comp (PolyFueled.right.comp hprev)
  have hlen : PolyFueled _ (fun z : ℕ => rcLen (z.unpair.2.unpair.2)) :=
    PolyFueled.right.comp (PolyFueled.right.comp hprev)
  obtain ⟨cM, hMF⟩ := rcModeF_polyFueled hmode hcnt htok
  obtain ⟨cC, hCF⟩ := rcCntF_polyFueled hmode hcnt htok
  obtain ⟨cL, hLF⟩ := rcLenF_polyFueled hmode hcnt hlen htok
  have hstep := hMF.pair (hCF.pair hLF)
  set tf : ℕ → ℕ := fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0 with htf
  have hbound : IsPolyBounded (fun w : ℕ =>
      rpnCondControlAt tf w.unpair.1 w.unpair.2) := by
    have hmaj : IsPolyBounded (fun w : ℕ =>
        Nat.pair 7 (Nat.pair (w.unpair.2 + 1) w.unpair.2)) :=
      ((IsPolyBounded.linear 7).of_le fun _ => by omega).pair
        (isPolyBounded_snd.add_one.pair isPolyBounded_snd)
    exact hmaj.of_le fun w => rpnCondControlAt_le tf w.unpair.1 w.unpair.2
  refine ⟨_, PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun n j => rpnCondControlAt tf n j)
    (fun n => rfl)
    (fun n j => ?_) hbound⟩
  show rpnCondControlAt tf n (j + 1) = _
  rw [show rpnCondControlAt tf n (j + 1) =
    rpnCondStep (rpnCondControlAt tf n j) (tf (Nat.pair n j)) from rfl,
    ← rpnCondStep_clamp, rpnCondStep_components]
  simp only [htf, Nat.unpair_pair, rcPack, Nat.reduceAdd]

/-! ## The day-guard flag -/

/-- `1` iff some price-day position below the cursor carries a day token exceeding
`n` (mirror of `ConditioningCompile.bigDayFlagAt` over the run-aware automaton). -/
def rpnBigDayFlagAt (tf : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      if rcMode (rpnCondControlAt tf n j) = 2 ∧ n < tf (Nat.pair n j) then 1
      else rpnBigDayFlagAt tf n j

lemma rpnBigDayFlagAt_le_one (tf : ℕ → ℕ) (n : ℕ) : ∀ j,
    rpnBigDayFlagAt tf n j ≤ 1
  | 0 => by simp [rpnBigDayFlagAt]
  | j + 1 => by
      rw [rpnBigDayFlagAt]
      split
      · exact le_refl 1
      · exact rpnBigDayFlagAt_le_one tf n j

lemma rpnBigDayFlagAt_eq_zero_iff (tf : ℕ → ℕ) (n J : ℕ) :
    rpnBigDayFlagAt tf n J = 0 ↔
      ∀ j < J, rcMode (rpnCondControlAt tf n j) = 2 → tf (Nat.pair n j) ≤ n := by
  induction J with
  | zero => simp [rpnBigDayFlagAt]
  | succ J ih =>
      rw [rpnBigDayFlagAt]
      by_cases hc : rcMode (rpnCondControlAt tf n J) = 2 ∧ n < tf (Nat.pair n J)
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

/-- The guard flag is poly-fueled over any digit `PolySegStream` (input `⟨n, j⟩`). -/
lemma rpnBigDayFlagScan {s : ℕ → List ℕ} (h : PolySegStream s) :
    ∃ c, PolyFueled c (fun z =>
      rpnBigDayFlagAt (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0)
        z.unpair.1 z.unpair.2) := by
  obtain ⟨cs, hscan⟩ := rpnCondScan h
  obtain ⟨cd, hclamp⟩ := h.dayClampTokens
  obtain ⟨cad, had⟩ := addc_polyFueled
  -- Step input `⟨n, ⟨j, prev⟩⟩`.
  have hn := PolyFueled.left
  have hj := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have hmz := PolyFueled.left.comp (hscan.comp (hn.pair hj))
  have hdz := hclamp.comp (hn.pair hj)
  have heq2 := had.comp ((subc_polyFueled.comp (hmz.pair (PolyFueled.const 2))).pair
    (subc_polyFueled.comp ((PolyFueled.const 2).pair hmz)))
  have hexcess := subc_polyFueled.comp (hdz.pair hn)
  have hinner := ifzSel_polyFueled.comp ((hexcess.pair (PolyFueled.const 0)).pair heq2)
  have hstep := ifzSel_polyFueled.comp ((hprev.pair (PolyFueled.const 1)).pair hinner)
  set tf : ℕ → ℕ := fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0 with htf
  refine ⟨_, PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun n j => rpnBigDayFlagAt tf n j)
    (fun n => rfl)
    (fun n j => ?_)
    ((IsPolyBounded.linear 1).of_le fun z =>
      le_trans (rpnBigDayFlagAt_le_one _ _ _) (by omega))⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  rw [rpnBigDayFlagAt]
  have htfj : tf (Nat.pair n j) = (undigitize (s n)).getD j 0 := by
    rw [htf]
    simp only [Nat.unpair_pair]
  rw [← htfj]
  rw [show (Nat.unpair (rpnCondControlAt tf n j)).1 =
    rcMode (rpnCondControlAt tf n j) from rfl]
  by_cases hm : rcMode (rpnCondControlAt tf n j) = 2
  · have heq2z : rcMode (rpnCondControlAt tf n j) - 2 +
        (2 - rcMode (rpnCondControlAt tf n j)) = 0 := by omega
    rw [if_pos heq2z]
    by_cases hd : n < tf (Nat.pair n j)
    · rw [if_pos ⟨hm, hd⟩, Nat.min_eq_right (by omega : n + 1 ≤ tf (Nat.pair n j)),
        if_neg (by omega : ¬ n + 1 - n = 0)]
    · rw [if_neg (by tauto :
          ¬ (rcMode (rpnCondControlAt tf n j) = 2 ∧ n < tf (Nat.pair n j))),
        Nat.min_eq_left (by omega : tf (Nat.pair n j) ≤ n + 1),
        if_pos (by omega : tf (Nat.pair n j) - n = 0)]
  · rw [if_neg (by tauto :
        ¬ (rcMode (rpnCondControlAt tf n j) = 2 ∧ n < tf (Nat.pair n j))),
      if_neg (by omega : ¬ rcMode (rpnCondControlAt tf n j) - 2 +
        (2 - rcMode (rpnCondControlAt tf n j)) = 0),
      if_pos rfl]

#print axioms rpnCondScan
#print axioms rpnBigDayFlagScan

/-! ## The trade-run exit count

The frame pass's budget codes are set by the number of completed trades; at symbol
level a trade is a *run*, so the count scans the control mode stream for run exits
(mode `4`/`7` with successor mode `0`). -/

/-- Number of completed trade runs strictly before source position `j`: a trade run
exits at the position whose control mode is `4`/`7` and whose successor mode is `0`. -/
def rpnTradeCountAt (tf : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      if (rcMode (rpnCondControlAt tf n j) = 4 ∨
            rcMode (rpnCondControlAt tf n j) = 7) ∧
          rcMode (rpnCondControlAt tf n (j + 1)) = 0 then
        rpnTradeCountAt tf n j + 1
      else rpnTradeCountAt tf n j

lemma rpnTradeCountAt_le (tf : ℕ → ℕ) (n : ℕ) : ∀ j, rpnTradeCountAt tf n j ≤ j
  | 0 => by simp [rpnTradeCountAt]
  | j + 1 => by
      rw [rpnTradeCountAt]
      have := rpnTradeCountAt_le tf n j
      split <;> omega

/-- The trade-run exit count is poly-fueled over any digit `PolySegStream`. -/
lemma rpnTradeCountScan {s : ℕ → List ℕ} (h : PolySegStream s) :
    ∃ c, PolyFueled c (fun z =>
      rpnTradeCountAt (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0)
        z.unpair.1 z.unpair.2) := by
  obtain ⟨cs, hscan⟩ := rpnCondScan h
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
  have hsucc : PolyFueled _ (fun z : ℕ => z.unpair.2.unpair.2 + 1) :=
    (had.comp (hprev.pair (PolyFueled.const 1))).of_eq fun z => by
      simp only [Nat.unpair_pair]
  obtain ⟨_, hA⟩ := polyFueled_ifEq hmz 7 hsucc hprev
  obtain ⟨_, hB⟩ := polyFueled_ifEq hmz 4 hsucc hA
  obtain ⟨_, hstep⟩ := polyFueled_ifEq hmz1 0 hB hprev
  set tf : ℕ → ℕ := fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0 with htf
  refine ⟨_, PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun n j => rpnTradeCountAt tf n j)
    (fun n => rfl)
    (fun n j => ?_)
    ((IsPolyBounded.linear 0).of_le fun z =>
      le_trans (rpnTradeCountAt_le _ _ _) (Nat.unpair_right_le z))⟩
  simp only [Nat.unpair_pair]
  rw [rpnTradeCountAt]
  rw [show (Nat.unpair (rpnCondControlAt tf n j)).1 =
      rcMode (rpnCondControlAt tf n j) from rfl,
    show (Nat.unpair (rpnCondControlAt tf n (j + 1))).1 =
      rcMode (rpnCondControlAt tf n (j + 1)) from rfl]
  by_cases hm1 : rcMode (rpnCondControlAt tf n (j + 1)) = 0
  · rw [if_pos hm1]
    by_cases hm4 : rcMode (rpnCondControlAt tf n j) = 4
    · rw [if_pos hm4, if_pos ⟨Or.inl hm4, hm1⟩]
    · rw [if_neg hm4]
      by_cases hm7 : rcMode (rpnCondControlAt tf n j) = 7
      · rw [if_pos hm7, if_pos ⟨Or.inr hm7, hm1⟩]
      · rw [if_neg hm7, if_neg (by tauto)]
  · rw [if_neg hm1, if_neg (by tauto)]

#print axioms rpnTradeCountScan

/-! ## The emission certificate

The digit stream of the guarded symbol-level price rewrite of any digit
`PolySegStream` is itself a `PolySegStream`, given a polynomially emittable condition
block stream: copied tokens are re-rendered digit blocks, the buffered run is copied
by position (`concatVar` over the recorded run length), the condition blocks are drawn
at the clamped day, and flagged days emit nothing. -/

/-- The digitized rewrite segment splits around its copies and splices. -/
lemma digitize_rpnConditionEmit (blk : List ℕ) (ε : ℚ) (buf : List ℕ) (D : ℕ) :
    digitize (rpnConditionEmit blk ε buf D) =
      tokenBlock D ++
      digitize [1, Encodable.encode (-1 : ℚ), 1, Encodable.encode (-1 : ℚ),
        1, Encodable.encode (1 : ℚ), 3, 1, Encodable.encode (-1 : ℚ), 0, 3] ++
      digitize buf ++ digitize blk ++
      tokenBlock D ++
      digitize [1, Encodable.encode (1 / ε : ℚ), 1, Encodable.encode (1 / ε : ℚ), 0] ++
      digitize blk ++
      tokenBlock D ++
      digitize [3, 5, 3, 3, 3, 4, 3, 8] := by
  simp [rpnConditionEmit, digitize]

/-- The digitized position window is a run of copied digit blocks. -/
lemma digitize_rpnCondWindow (tf : ℕ → ℕ) (n j : ℕ) :
    digitize (rpnCondWindow tf n j) =
      (List.range (rcLen (rpnCondControlAt tf n j))).flatMap fun i =>
        tokenBlock (tf (Nat.pair n
          (j - rcLen (rpnCondControlAt tf n j) + i))) := by
  rw [rpnCondWindow, digitize, List.flatMap_map]

/-- **The certificate, for an arbitrary emitter**: the digitized guarded symbol-level
rewrite of any digit `PolySegStream` is a `PolySegStream`, given that the emitted
segment — read at the *clamped* day, which is exact wherever the guard passes — is
itself polynomially emittable.
Paper node: `thm:scon` -/
lemma rpnGuardedConditionRun_polySegStream_of {s : ℕ → List ℕ} (h : PolySegStream s)
    (emit : List ℕ → ℕ → List ℕ)
    (hEmit : PolySegStream (fun z => digitize
      (emit (rpnCondWindow (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0)
          z.unpair.1 z.unpair.2)
        (min ((undigitize (s z.unpair.1)).getD z.unpair.2 0) (z.unpair.1 + 1))))) :
    PolySegStream (fun n => digitize (rpnGuardedConditionTokens emit n
      (undigitize (s n)))) := by
  obtain ⟨⟨cc, hcnt⟩, hbig⟩ := h.undigitizeTokens
  obtain ⟨cs, hscan⟩ := rpnCondScan h
  obtain ⟨cf, hflag⟩ := rpnBigDayFlagScan h
  obtain ⟨cad, had⟩ := addc_polyFueled
  set tf : ℕ → ℕ := fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0 with htf
  have hmodeZ := PolyFueled.left.comp hscan
  have hcopy := hbig.blockSeg
  have heq2 := had.comp ((subc_polyFueled.comp (hmodeZ.pair (PolyFueled.const 2))).pair
    (subc_polyFueled.comp ((PolyFueled.const 2).pair hmodeZ)))
  have hseg := hEmit.ifZero hcopy heq2
  have hassembled := hseg.concatVar hcnt
  have hflagEnd := hflag.comp (PolyFueled.id.pair hcnt)
  have hempty : PolySegStream (fun _ : ℕ => ([] : List ℕ)) :=
    PolySegStream.ofTokenStream PolyTokenStream.nil
  refine (hassembled.ifZero hempty hflagEnd).of_eq fun n => ?_
  simp only [Nat.unpair_pair]
  have hget : ∀ i, i < (undigitize (s n)).length →
      tf (Nat.pair n i) = (undigitize (s n)).getD i 0 := fun i _ => by
    rw [htf]
    simp only [Nat.unpair_pair]
  -- Guard equivalence between the flag and the list-level predicate.
  have hguardIff : rpnBigDayFlagAt tf n (undigitize (s n)).length = 0 ↔
      ∀ j < (undigitize (s n)).length,
        rcMode (((undigitize (s n)).take j).foldl rpnCondStep (rcPack 0 0 0)) = 2 →
          (undigitize (s n)).getD j 0 ≤ n := by
    rw [rpnBigDayFlagAt_eq_zero_iff]
    constructor
    · intro hall j hj hm
      rw [← hget j hj]
      refine hall j hj ?_
      rw [rpnCondControlAt_eq_foldl, vpre_eq_take hget (le_of_lt hj)]
      exact hm
    · intro hall j hj hm
      rw [hget j hj]
      refine hall j hj ?_
      rw [rpnCondControlAt_eq_foldl, vpre_eq_take hget (le_of_lt hj)] at hm
      exact hm
  by_cases hflagn : rpnBigDayFlagAt tf n (undigitize (s n)).length = 0
  · rw [if_pos hflagn, rpnGuardedConditionTokens, if_pos (hguardIff.mp hflagn)]
    have hts : undigitize (s n) =
        (List.range (undigitize (s n)).length).map fun j => tf (Nat.pair n j) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        rw [hget i (by simpa using h2)]
        exact (List.getD_eq_getElem (undigitize (s n)) 0 (by simpa using h2)).symm
    have hrun : (rpnConditionRun emit (rcPack 0 0 0, []) (undigitize (s n))).2 =
        (List.range (undigitize (s n)).length).flatMap fun j =>
          rpnConditionSegment tf emit (Nat.pair n j) := by
      conv_lhs => rw [hts]
      exact congrArg Prod.snd (rpnConditionRun_range tf emit n
        (undigitize (s n)).length)
    rw [hrun, digitize_flatMap]
    refine List.flatMap_congr fun j hj => ?_
    rw [List.mem_range] at hj
    rw [rpnConditionSegment]
    simp only [Nat.unpair_pair]
    rw [show (Nat.unpair (rpnCondControlAt tf n j)).1 =
      rcMode (rpnCondControlAt tf n j) from rfl]
    by_cases hm : rcMode (rpnCondControlAt tf n j) = 2
    · rw [if_pos (by omega : rcMode (rpnCondControlAt tf n j) - 2 +
        (2 - rcMode (rpnCondControlAt tf n j)) = 0), if_pos hm]
      have hdle : tf (Nat.pair n j) ≤ n :=
        (rpnBigDayFlagAt_eq_zero_iff tf n _).mp hflagn j hj hm
      have htfj : tf (Nat.pair n j) = (undigitize (s n)).getD j 0 := by
        rw [htf]
        simp only [Nat.unpair_pair]
      rw [htfj] at hdle
      have hclampEq : min ((undigitize (s n)).getD j 0) (n + 1) =
          (undigitize (s n)).getD j 0 := Nat.min_eq_left (by omega)
      simp only [Nat.unpair_pair, htf, hclampEq]
    · rw [if_neg (by omega : ¬ rcMode (rpnCondControlAt tf n j) - 2 +
        (2 - rcMode (rpnCondControlAt tf n j)) = 0), if_neg hm]
      rw [htf]
      simp only [Nat.unpair_pair]
      simp [digitize]
  · rw [if_neg hflagn, rpnGuardedConditionTokens,
      if_neg (fun hguard => hflagn (hguardIff.mpr hguard))]
    simp [digitize]

/-- **The price-pass certificate**: the digitized guarded symbol-level price rewrite of
any digit `PolySegStream` is a `PolySegStream`, over any polynomially emittable
condition block stream — copied tokens are re-rendered digit blocks, the buffered run
is copied by position (`concatVar` over the recorded run length), and the condition
blocks are drawn at the clamped day.
Paper node: `thm:scon` -/
lemma rpnGuardedConditionRun_polySegStream {s blocks : ℕ → List ℕ}
    (h : PolySegStream s) (hb : PolySegStream blocks) (ε : ℚ) :
    PolySegStream (fun n => digitize
      (rpnGuardedConditionTokens (rpnPriceEmit blocks ε) n (undigitize (s n)))) := by
  obtain ⟨⟨cc, hcnt⟩, hbig⟩ := h.undigitizeTokens
  obtain ⟨cs, hscan⟩ := rpnCondScan h
  obtain ⟨cd, hclamp⟩ := h.dayClampTokens
  obtain ⟨cad, had⟩ := addc_polyFueled
  set tf : ℕ → ℕ := fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0 with htf
  have hlenZ := PolyFueled.right.comp (PolyFueled.right.comp hscan)
  refine rpnGuardedConditionRun_polySegStream_of h _ ?_
  -- Day copies (clamped; exact under the guard).
  have hD := PolySegStream.block hclamp
  -- Constant frames.
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
  -- The window copy: `concatVar` over the recorded run length.
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
  -- Condition blocks at the clamped day.
  have hblkD := (hb.comp hclamp).digitizeStream
  refine (((((((((hD.append hA).append hwin).append hblkD).append
    hD).append hB).append hblkD).append hD).append hC)).of_eq fun z => ?_
  rw [rpnPriceEmit, digitize_rpnConditionEmit, digitize_rpnCondWindow]
  simp only [Nat.unpair_pair, htf, rcLen, List.append_assoc]

#print axioms rpnGuardedConditionRun_polySegStream

/-! ## The append wrinkle

`unRpn` does **not** distribute over an append: if `A` carries a poisoned chunk the
contraction stops inside `A` and never reads `B`, so in general
`unRpn (A ++ B) ≠ unRpn A ++ unRpn B`.  The two-leg join concatenates two frame outputs
and therefore cannot consume the plain agreement `FrameAgree`; it consumes the prefix
form `FrameContract` instead, which is available exactly when the source returns the run
automaton to base mode — the condition the structural-acceptance gate tests — together
with the observation that a *readable* source excludes both legs' poison branches, since
a poisoned leg's token image fails to deserialize. -/

/-! ## Parse localization

The whole-stream exactness argument needs to evaluate `unRpn` on transducer outputs
whose price chunks wrap *arbitrary* (possibly malformed) runs.  Two facts localize the
parse: a successful parse factors through a complete block (`parseRpn_strip`), and a
run the automaton walks to completion either parses completely or poisons **every**
extension (`parse_of_priceRunWalk`) — the two cases behind copied-chunk transparency
on garbage. -/

/-- Consumed-prefix completeness: a successful parse factors as a complete block
followed by the remainder. -/
lemma parseRpn_strip : ∀ (fuel : ℕ) (ts : List ℕ) {φ : Sentence} {rest : List ℕ},
    parseRpn fuel ts = some (φ, rest) →
    ∃ blk, ts = blk ++ rest ∧ parseRpn blk.length blk = some (φ, []) := by
  intro fuel
  induction fuel with
  | zero => intro ts φ rest h; simp [parseRpn] at h
  | succ fuel ih =>
      intro ts φ rest h
      match ts with
      | [] => simp at h
      | t :: ts' =>
          rw [parseRpn_cons] at h
          by_cases h0 : t = 0
          · rw [if_pos h0] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
            subst h0
            exact ⟨[0], rfl, rfl⟩
          · rw [if_neg h0] at h
            by_cases h1 : t = 1
            · rw [if_pos h1] at h
              match ts' with
              | [] => simp at h
              | c₀ :: ts'' =>
                  rw [List.head?_cons] at h
                  simp only [Option.bind_some] at h
                  cases hdec : Encodable.decode (α := Sentence) c₀ with
                  | none => rw [hdec] at h; simp at h
                  | some ψ =>
                      rw [hdec] at h
                      simp only [Option.map_some, List.tail_cons] at h
                      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
                      subst h1
                      refine ⟨[1, c₀], rfl, ?_⟩
                      rw [show ([1, c₀] : List ℕ).length = 1 + 1 from rfl,
                        parseRpn_cons]
                      simp [hdec]
            · rw [if_neg h1] at h
              have hbin : ∀ (mk : Sentence → Sentence → Sentence),
                  ((parseRpn fuel ts').bind fun p =>
                    (parseRpn fuel p.2).bind fun q =>
                      some (mk p.1 q.1, q.2)) = some (φ, rest) →
                  ((t = 2 ∧ mk = LO.Propositional.Formula.imp) ∨ (t = 3 ∧ mk = LO.Propositional.Formula.and) ∨
                    (t = 4 ∧ mk = LO.Propositional.Formula.or)) →
                  ∃ blk, t :: ts' = blk ++ rest ∧
                    parseRpn blk.length blk = some (φ, []) := by
                intro mk hh ht
                cases hp : parseRpn fuel ts' with
                | none => rw [hp] at hh; simp at hh
                | some p =>
                    rw [hp] at hh
                    simp only [Option.bind_some] at hh
                    cases hq : parseRpn fuel p.2 with
                    | none => rw [hq] at hh; simp at hh
                    | some q =>
                        rw [hq] at hh
                        simp only [Option.bind_some] at hh
                        obtain ⟨hφ, hrest⟩ :=
                          Prod.mk.injEq .. ▸ Option.some.inj hh
                        obtain ⟨blk₁, hts', hblk₁⟩ := ih ts' hp
                        obtain ⟨blk₂, hp2, hblk₂⟩ := ih p.2 hq
                        refine ⟨t :: blk₁ ++ blk₂, by
                          rw [hts', hp2, hrest]; simp, ?_⟩
                        have hb1 : parseRpn (blk₁.length + blk₂.length)
                            (blk₁ ++ blk₂) = some (p.1, blk₂) :=
                          parseRpn_block_head hblk₁ blk₂ (by omega)
                        have hb2 : parseRpn (blk₁.length + blk₂.length) blk₂ =
                            some (q.1, []) :=
                          parseRpn_mono blk₂ (by omega) hblk₂
                        rw [List.cons_append,
                          show (t :: (blk₁ ++ blk₂)).length =
                            (blk₁.length + blk₂.length) + 1 by simp,
                          parseRpn_cons, if_neg h0, if_neg h1]
                        rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · rw [if_pos rfl, hb1]
                          simp only [Option.bind_some]
                          rw [hb2]
                          simp only [Option.bind_some, ← hφ]
                        · rw [if_neg (by omega), if_pos rfl, hb1]
                          simp only [Option.bind_some]
                          rw [hb2]
                          simp only [Option.bind_some, ← hφ]
                        · rw [if_neg (by omega), if_neg (by omega), if_pos rfl,
                            hb1]
                          simp only [Option.bind_some]
                          rw [hb2]
                          simp only [Option.bind_some, ← hφ]
              by_cases h2 : t = 2
              · rw [if_pos h2] at h
                exact hbin _ h (Or.inl ⟨h2, rfl⟩)
              · rw [if_neg h2] at h
                by_cases h3 : t = 3
                · rw [if_pos h3] at h
                  exact hbin _ h (Or.inr (Or.inl ⟨h3, rfl⟩))
                · rw [if_neg h3] at h
                  by_cases h4 : t = 4
                  · rw [if_pos h4] at h
                    exact hbin _ h (Or.inr (Or.inr ⟨h4, rfl⟩))
                  · rw [if_neg h4] at h
                    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
                    refine ⟨[t], rfl, ?_⟩
                    rw [show ([t] : List ℕ).length = 0 + 1 from rfl,
                      parseRpn_cons, if_neg h0, if_neg h1, if_neg h2, if_neg h3,
                      if_neg h4]

/-! ### Run-step normal forms (for the converse walk argument) -/

/-- The step inside a price run, in offset-counter form. -/
lemma rpnCondStep_price (c r t : ℕ) :
    rpnCondStep (rcPack 1 (c + 1) r) t =
      if t = 1 then rcPack 6 (c + 1) (r + 1)
      else if t = 2 ∨ t = 3 ∨ t = 4 then rcPack 1 (c + 2) (r + 1)
      else if c = 0 then rcPack 2 0 (r + 1) else rcPack 1 c (r + 1) := by
  rw [rpnCondStep]
  simp only [rcMode_pack, rcCnt_pack, rcLen_pack]
  split_ifs <;> simp only [rcPack, Nat.pair_eq_pair, true_and, and_true] <;>
    first | omega | (exfalso; assumption)

/-- The step on an escape payload inside a price run. -/
lemma rpnCondStep_priceEsc (c r t : ℕ) :
    rpnCondStep (rcPack 6 (c + 1) r) t =
      if c = 0 then rcPack 2 0 (r + 1) else rcPack 1 c (r + 1) := by
  rw [rpnCondStep]
  simp only [rcMode_pack, rcCnt_pack, rcLen_pack]
  split_ifs <;> simp only [rcPack, Nat.pair_eq_pair, true_and, and_true] <;>
    first | omega | (exfalso; assumption)

/-- The step inside a trade run, in offset-counter form. -/
lemma rpnCondStep_trade (c r t : ℕ) :
    rpnCondStep (rcPack 4 (c + 1) r) t =
      if t = 1 then rcPack 7 (c + 1) (r + 1)
      else if t = 2 ∨ t = 3 ∨ t = 4 then rcPack 4 (c + 2) (r + 1)
      else if c = 0 then rcPack 0 0 0 else rcPack 4 c (r + 1) := by
  rw [rpnCondStep]
  simp only [rcMode_pack, rcCnt_pack, rcLen_pack]
  split_ifs <;> simp only [rcPack, Nat.pair_eq_pair, true_and, and_true] <;>
    first | omega | (exfalso; assumption)

/-- The step on an escape payload inside a trade run. -/
lemma rpnCondStep_tradeEsc (c r t : ℕ) :
    rpnCondStep (rcPack 7 (c + 1) r) t =
      if c = 0 then rcPack 0 0 0 else rcPack 4 c (r + 1) := by
  rw [rpnCondStep]
  simp only [rcMode_pack, rcCnt_pack, rcLen_pack]
  split_ifs <;> simp only [rcPack, Nat.pair_eq_pair, true_and, and_true] <;>
    first | omega | (exfalso; assumption)

/-- Inside a run the recorded run length grows by exactly one per token. -/
lemma rcLen_run_step (st t : ℕ)
    (hm : rcMode st = 1 ∨ rcMode st = 6) :
    rcLen (rpnCondStep st t) = rcLen st + 1 := by
  rw [rpnCondStep]
  split_ifs <;> simp only [rcLen_pack] <;> omega

/-! ### Generic run-walk step facts

The price (`1`/`6`, exit to the day slot) and trade (`4`/`7`, exit to base) runs share
the walk shape; every fact below is generic over the mode pair `(a, b)` and the exit,
constrained only by the two step-shape hypotheses (mirroring
`foldl_rpnCondStep_run`'s parametrization) and the exit's counter/mode
disambiguators. -/

/-- One step from a live run state: stay in the run (counter positive, run length
incremented) or take the exit. -/
lemma runWalk_step_cases {a b : ℕ} {exit : ℕ → ℕ}
    (hrun : ∀ c r t, rpnCondStep (rcPack a (c + 1) r) t =
      if t = 1 then rcPack b (c + 1) (r + 1)
      else if t = 2 ∨ t = 3 ∨ t = 4 then rcPack a (c + 2) (r + 1)
      else if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (hesc : ∀ c r t, rpnCondStep (rcPack b (c + 1) r) t =
      if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (st t : ℕ) (hm : rcMode st = a ∨ rcMode st = b) (hc : 1 ≤ rcCnt st) :
    ((rcMode (rpnCondStep st t) = a ∨ rcMode (rpnCondStep st t) = b) ∧
      1 ≤ rcCnt (rpnCondStep st t) ∧
      rcLen (rpnCondStep st t) = rcLen st + 1) ∨
    rpnCondStep st t = exit (rcLen st + 1) := by
  obtain ⟨m, c0, r0, rfl⟩ : ∃ m c0 r0, st = rcPack m c0 r0 :=
    ⟨rcMode st, rcCnt st, rcLen st, rcPack_surjective st⟩
  simp only [rcMode_pack, rcCnt_pack, rcLen_pack] at hm hc ⊢
  obtain ⟨c, rfl⟩ : ∃ c, c0 = c + 1 := ⟨c0 - 1, by omega⟩
  rcases hm with rfl | rfl
  · rw [hrun]
    split_ifs with h1 h2 h3
    · exact Or.inl ⟨Or.inr (by simp), by simp only [rcCnt_pack]; omega,
        by simp only [rcLen_pack]⟩
    · exact Or.inl ⟨Or.inl (by simp), by simp only [rcCnt_pack]; omega,
        by simp only [rcLen_pack]⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨Or.inl (by simp), by simp only [rcCnt_pack]; omega,
        by simp only [rcLen_pack]⟩
  · rw [hesc]
    split_ifs with h1
    · exact Or.inr rfl
    · exact Or.inl ⟨Or.inl (by simp), by simp only [rcCnt_pack]; omega,
        by simp only [rcLen_pack]⟩

/-- Inside a run the counter drops by at most one per token. -/
lemma rcCnt_runWalk_step_ge {a b : ℕ} {exit : ℕ → ℕ}
    (hrun : ∀ c r t, rpnCondStep (rcPack a (c + 1) r) t =
      if t = 1 then rcPack b (c + 1) (r + 1)
      else if t = 2 ∨ t = 3 ∨ t = 4 then rcPack a (c + 2) (r + 1)
      else if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (hesc : ∀ c r t, rpnCondStep (rcPack b (c + 1) r) t =
      if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (hexitCnt : ∀ r', rcCnt (exit r') = 0)
    (st t : ℕ) (hm : rcMode st = a ∨ rcMode st = b) (hc : 1 ≤ rcCnt st) :
    rcCnt st ≤ rcCnt (rpnCondStep st t) + 1 := by
  obtain ⟨m, c0, r0, rfl⟩ : ∃ m c0 r0, st = rcPack m c0 r0 :=
    ⟨rcMode st, rcCnt st, rcLen st, rcPack_surjective st⟩
  simp only [rcMode_pack, rcCnt_pack] at hm hc ⊢
  obtain ⟨c, rfl⟩ : ∃ c, c0 = c + 1 := ⟨c0 - 1, by omega⟩
  rcases hm with rfl | rfl
  · rw [hrun]
    split_ifs with h1 h2 h3 <;>
      first
        | (simp only [rcCnt_pack]; omega)
        | (rw [hexitCnt]; omega)
  · rw [hesc]
    split_ifs with h1 <;>
      first
        | (simp only [rcCnt_pack]; omega)
        | (rw [hexitCnt]; omega)

/-- A strict counter decrement from a run state with counter `≥ 2` lands back in
run mode `a` (never the exit): the closing token of a proper subtree. -/
lemma runWalk_step_decrement {a b : ℕ} {exit : ℕ → ℕ}
    (hrun : ∀ c r t, rpnCondStep (rcPack a (c + 1) r) t =
      if t = 1 then rcPack b (c + 1) (r + 1)
      else if t = 2 ∨ t = 3 ∨ t = 4 then rcPack a (c + 2) (r + 1)
      else if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (hesc : ∀ c r t, rpnCondStep (rcPack b (c + 1) r) t =
      if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (st t : ℕ) (hm : rcMode st = a ∨ rcMode st = b) (h2 : 2 ≤ rcCnt st)
    (hdec : rcCnt (rpnCondStep st t) < rcCnt st) :
    rpnCondStep st t = rcPack a (rcCnt st - 1) (rcLen st + 1) := by
  obtain ⟨m, c0, r0, rfl⟩ : ∃ m c0 r0, st = rcPack m c0 r0 :=
    ⟨rcMode st, rcCnt st, rcLen st, rcPack_surjective st⟩
  simp only [rcMode_pack, rcCnt_pack, rcLen_pack] at hm h2 hdec ⊢
  obtain ⟨c, rfl⟩ : ∃ c, c0 = c + 1 := ⟨c0 - 1, by omega⟩
  rcases hm with rfl | rfl
  · rw [hrun] at hdec ⊢
    split_ifs at hdec ⊢ with h1 hop hc0
    · simp only [rcCnt_pack] at hdec
      omega
    · simp only [rcCnt_pack] at hdec
      omega
    · omega
    · simp only [Nat.add_sub_cancel]
  · rw [hesc] at hdec ⊢
    split_ifs at hdec ⊢ with hc0
    · omega
    · simp only [Nat.add_sub_cancel]

/-- **The generic converse walk lemma**: a token run the automaton walks from counter
`c + 1` to its first return at counter `c` — staying strictly inside the run on every
proper prefix — either parses completely as one sentence block, or poisons every
extension (`parseRpn` fails on `u ++ tail` for every fuel and tail).  The only failure
mode of an arity-complete run is an undecodable escape payload, which every extension
reproduces.  Generic over the run-mode pair `(a, b)` and the exit, mirroring
`foldl_rpnCondStep_run`. -/
lemma parse_of_runWalk {a b : ℕ} {exit : ℕ → ℕ}
    (hrun : ∀ c r t, rpnCondStep (rcPack a (c + 1) r) t =
      if t = 1 then rcPack b (c + 1) (r + 1)
      else if t = 2 ∨ t = 3 ∨ t = 4 then rcPack a (c + 2) (r + 1)
      else if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (hesc : ∀ c r t, rpnCondStep (rcPack b (c + 1) r) t =
      if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (hexitCnt : ∀ r', rcCnt (exit r') = 0)
    (hexitMode : ∀ r', rcMode (exit r') ≠ a ∧ rcMode (exit r') ≠ b) :
    ∀ (N : ℕ) (u : List ℕ), u.length ≤ N → ∀ (c r : ℕ),
    List.foldl rpnCondStep (rcPack a (c + 1) r) u =
      (if c = 0 then exit (r + u.length) else rcPack a c (r + u.length)) →
    (∀ k < u.length,
      (rcMode (List.foldl rpnCondStep (rcPack a (c + 1) r) (u.take k)) = a ∨
        rcMode (List.foldl rpnCondStep (rcPack a (c + 1) r) (u.take k)) = b) ∧
      c + 1 ≤ rcCnt (List.foldl rpnCondStep (rcPack a (c + 1) r) (u.take k))) →
    (∃ φ, parseRpn u.length u = some (φ, [])) ∨
    (∀ fuel tail, parseRpn fuel (u ++ tail) = none) := by
  intro N
  induction N with
  | zero =>
      intro u hu c r h1 _
      match u with
      | [] =>
          rw [List.foldl_nil] at h1
          by_cases hc : c = 0
          · rw [if_pos hc] at h1
            have hcnt := congrArg rcCnt h1
            rw [rcCnt_pack, hexitCnt] at hcnt
            omega
          · rw [if_neg hc] at h1
            simp only [rcPack, Nat.pair_eq_pair] at h1
            omega
      | t :: u' => exact absurd hu (by simp)
  | succ N ih =>
      intro u hu c r h1 h2
      match u with
      | [] =>
          rw [List.foldl_nil] at h1
          by_cases hc : c = 0
          · rw [if_pos hc] at h1
            have hcnt := congrArg rcCnt h1
            rw [rcCnt_pack, hexitCnt] at hcnt
            omega
          · rw [if_neg hc] at h1
            simp only [rcPack, Nat.pair_eq_pair] at h1
            omega
      | t :: u' =>
          simp only [List.length_cons] at hu
          have hW1 : List.foldl rpnCondStep (rcPack a (c + 1) r) [t] =
              rpnCondStep (rcPack a (c + 1) r) t := rfl
          by_cases ht1 : t = 1
          · -- Escape: the run is exactly `[1, payload]`.
            subst ht1
            match u' with
            | [] =>
                rw [List.foldl_cons, List.foldl_nil, hrun,
                  if_pos rfl] at h1
                by_cases hc : c = 0
                · rw [if_pos hc] at h1
                  have hcnt := congrArg rcCnt h1
                  rw [rcCnt_pack, hexitCnt] at hcnt
                  omega
                · rw [if_neg hc] at h1
                  simp only [rcPack, Nat.pair_eq_pair] at h1
                  omega
            | p :: u'' =>
                have hW2 : List.foldl rpnCondStep (rcPack a (c + 1) r) [1, p] =
                    (if c = 0 then exit (r + 2) else rcPack a c (r + 2)) := by
                  rw [List.foldl_cons, List.foldl_cons, List.foldl_nil,
                    hrun, if_pos rfl, hesc]
                have hu'' : u'' = [] := by
                  by_contra hne
                  have h2len : 2 < (1 :: p :: u'').length := by
                    simp only [List.length_cons]
                    have := List.length_pos_iff.mpr hne
                    omega
                  have := h2 2 h2len
                  rw [show ((1 : ℕ) :: p :: u'').take 2 = [1, p] from rfl, hW2] at this
                  by_cases hc : c = 0
                  · rw [if_pos hc] at this
                    have hcnt := this.2
                    rw [hexitCnt] at hcnt
                    omega
                  · rw [if_neg hc] at this
                    simp only [rcMode_pack, rcCnt_pack] at this
                    omega
                subst hu''
                cases hdec : Encodable.decode (α := Sentence) p with
                | some ψ =>
                    exact Or.inl ⟨ψ, by
                      rw [show ([1, p] : List ℕ).length = 1 + 1 from rfl,
                        parseRpn_cons]
                      simp [hdec]⟩
                | none =>
                    refine Or.inr fun fuel tail => ?_
                    match fuel with
                    | 0 => rfl
                    | fuel + 1 =>
                        rw [List.cons_append, List.cons_append, parseRpn_cons,
                          if_neg (by norm_num), if_pos rfl]
                        simp [hdec]
          · by_cases htop : t = 2 ∨ t = 3 ∨ t = 4
            · -- Operator: split the tail at the first counter return.
              have hstep1 : rpnCondStep (rcPack a (c + 1) r) t =
                  rcPack a (c + 1 + 1) (r + 1) := by
                rw [hrun, if_neg ht1, if_pos htop]
              -- The tail walk.
              set W' : ℕ → ℕ := fun k =>
                List.foldl rpnCondStep (rcPack a (c + 1 + 1) (r + 1)) (u'.take k)
                with hW'
              have hWW' : ∀ k, List.foldl rpnCondStep (rcPack a (c + 1) r)
                  ((t :: u').take (k + 1)) = W' k := fun k => by
                rw [List.take_succ_cons, List.foldl_cons, hstep1]
              have htake : ∀ (l : List ℕ) (k : ℕ) (hk : k < l.length),
                  l.take (k + 1) = l.take k ++ [l[k]] := fun l k hk => by
                rw [List.take_add_one, List.getElem?_eq_getElem hk]
                rfl
              have hW'succ : ∀ k (hk : k < u'.length),
                  W' (k + 1) = rpnCondStep (W' k) (u'[k]'hk) := fun k hk => by
                rw [hW']
                try simp only []
                rw [htake u' k hk, List.foldl_append, List.foldl_cons,
                  List.foldl_nil]
              have hW'0 : W' 0 = rcPack a (c + 2) (r + 1) := rfl
              have hW'len : W' u'.length =
                  (if c = 0 then exit (r + (t :: u').length)
                    else rcPack a c (r + (t :: u').length)) := by
                rw [← h1, ← hWW' u'.length]
                congr 1
                rw [List.take_succ_cons, List.take_of_length_le le_rfl]
              -- Modes and counters strictly inside.
              have hmid : ∀ k < u'.length,
                  (rcMode (W' k) = a ∨ rcMode (W' k) = b) ∧
                    c + 1 ≤ rcCnt (W' k) := fun k hk => by
                have := h2 (k + 1) (by simp only [List.length_cons]; omega)
                rwa [hWW' k] at this
              -- First return of the counter to `c + 1`.
              have hPex : ∃ k, k ≤ u'.length ∧ rcCnt (W' k) ≤ c + 1 :=
                ⟨u'.length, le_rfl, by
                  rw [hW'len]
                  by_cases hc : c = 0
                  · rw [if_pos hc, hexitCnt]
                    omega
                  · rw [if_neg hc, rcCnt_pack]
                    omega⟩
              classical
              obtain ⟨k1, hk1le, hk1cnt, hmin⟩ :
                  ∃ k1, k1 ≤ u'.length ∧ rcCnt (W' k1) ≤ c + 1 ∧
                    ∀ k < k1, ¬ (k ≤ u'.length ∧ rcCnt (W' k) ≤ c + 1) :=
                ⟨Nat.find hPex, (Nat.find_spec hPex).1, (Nat.find_spec hPex).2,
                  fun k hk => Nat.find_min hPex hk⟩
              have hk1pos : 0 < k1 := by
                rcases Nat.eq_zero_or_pos k1 with h | h
                · exfalso
                  rw [h] at hk1cnt
                  rw [hW'0, rcCnt_pack] at hk1cnt
                  omega
                · exact h
              have hprevcnt : c + 2 ≤ rcCnt (W' (k1 - 1)) := by
                have := hmin (k1 - 1) (by omega)
                have hle : k1 - 1 ≤ u'.length := by omega
                omega
              have hk1m1lt : k1 - 1 < u'.length := by omega
              have hprevmode := (hmid (k1 - 1) hk1m1lt).1
              -- The run length along the walk (strictly inside only: the exit may
              -- reset it).
              have hlenW : ∀ k, k < u'.length → rcLen (W' k) = r + 1 + k := by
                intro k
                induction k with
                | zero => intro _; rw [hW'0, rcLen_pack]
                | succ k ihk =>
                    intro hk
                    have hk' : k < u'.length := by omega
                    have hcases := runWalk_step_cases hrun hesc (W' k)
                      (u'[k]'hk') (hmid k hk').1
                      (by have := (hmid k hk').2; omega)
                    rw [← hW'succ k hk'] at hcases
                    rcases hcases with ⟨-, -, hlen⟩ | hexitEq
                    · rw [hlen, ihk hk']
                      omega
                    · exfalso
                      have hmode := (hmid (k + 1) hk).1
                      rw [hexitEq] at hmode
                      rcases hmode with h | h
                      · exact (hexitMode _).1 h
                      · exact (hexitMode _).2 h
              -- The state at the first return.
              have hstepk1 : W' k1 =
                  rpnCondStep (W' (k1 - 1)) (u'[k1 - 1]'hk1m1lt) := by
                have := hW'succ (k1 - 1) hk1m1lt
                rwa [Nat.sub_add_cancel hk1pos] at this
              have hdecstep : rcCnt (rpnCondStep (W' (k1 - 1))
                  (u'[k1 - 1]'hk1m1lt)) < rcCnt (W' (k1 - 1)) := by
                rw [← hstepk1]
                omega
              have hk1state : W' k1 = rcPack a (c + 1) (r + 1 + k1) := by
                rw [hstepk1, runWalk_step_decrement hrun hesc _ _ hprevmode
                  (by omega) hdecstep]
                have hcnteq : rcCnt (W' (k1 - 1)) - 1 = c + 1 := by
                  have hback := rcCnt_runWalk_step_ge hrun hesc hexitCnt
                    (W' (k1 - 1)) (u'[k1 - 1]'hk1m1lt) hprevmode (by omega)
                  rw [← hstepk1] at hback
                  omega
                rw [hcnteq, hlenW (k1 - 1) hk1m1lt]
                congr 1
                omega
              -- The two children.
              set u1 := u'.take k1 with hu1
              set u2 := u'.drop k1 with hu2
              have hu1len : u1.length = k1 := by
                rw [hu1, List.length_take]
                omega
              have hu2len : u2.length = u'.length - k1 := by
                rw [hu2, List.length_drop]
              have hW2eq : ∀ k, List.foldl rpnCondStep
                  (rcPack a (c + 1) (r + 1 + k1)) (u2.take k) = W' (k1 + k) := by
                intro k
                rw [hW']
                try simp only []
                rw [List.take_add, List.foldl_append, ← hu2]
                congr 1
                exact hk1state.symm
              -- Child 1 hypotheses.
              have hchild1 := ih u1 (by rw [hu1len]; omega) (c + 1) (r + 1)
                (by
                  rw [if_neg (Nat.succ_ne_zero c), hu1len, hu1]
                  exact hk1state)
                (by
                  intro k hk
                  rw [hu1len] at hk
                  have htt : u1.take k = u'.take k := by
                    rw [hu1, List.take_take, min_eq_left (by omega)]
                  rw [htt]
                  refine ⟨(hmid k (by omega)).1, ?_⟩
                  show c + 1 + 1 ≤ rcCnt (W' k)
                  have := hmin k hk
                  have hle : k ≤ u'.length := by omega
                  omega)
              -- Child 2 hypotheses.
              have hchild2 := ih u2 (by rw [hu2len]; omega) c (r + 1 + k1)
                (by
                  conv_lhs => rw [show u2 = u2.take u2.length from
                    (List.take_length).symm]
                  rw [hW2eq u2.length, hu2len,
                    show k1 + (u'.length - k1) = u'.length by omega, hW'len]
                  have harg : r + 1 + k1 + (u'.length - k1) =
                      r + (t :: u').length := by
                    simp only [List.length_cons]
                    omega
                  by_cases hc : c = 0
                  · rw [if_pos hc, if_pos hc, harg]
                  · rw [if_neg hc, if_neg hc, harg])
                (by
                  intro k hk
                  rw [hW2eq k]
                  have hklt : k1 + k < u'.length := by
                    rw [hu2len] at hk
                    omega
                  exact ⟨(hmid (k1 + k) hklt).1, (hmid (k1 + k) hklt).2⟩)
              -- Combine.
              have hsplit : u' = u1 ++ u2 := (List.take_append_drop k1 u').symm
              rcases hchild1 with ⟨φ1, hφ1⟩ | hpoison1
              · rcases hchild2 with ⟨φ2, hφ2⟩ | hpoison2
                · -- Both children parse: the whole run parses.
                  refine Or.inl ?_
                  have hb1 : parseRpn (u1.length + u2.length) (u1 ++ u2) =
                      some (φ1, u2) :=
                    parseRpn_block_head hφ1 u2 (by omega)
                  have hb2 : parseRpn (u1.length + u2.length) u2 =
                      some (φ2, []) := parseRpn_mono u2 (by omega) hφ2
                  have hlen' : (t :: u').length = (u1.length + u2.length) + 1 := by
                    rw [hsplit]
                    simp
                  rw [hlen', hsplit]
                  rw [parseRpn_cons, if_neg (by omega), if_neg ht1]
                  rcases htop with rfl | rfl | rfl
                  · exact ⟨LO.Propositional.Formula.imp φ1 φ2, by
                      rw [if_pos rfl, hb1]
                      simp only [Option.bind_some]
                      rw [hb2]
                      simp only [Option.bind_some]⟩
                  · exact ⟨LO.Propositional.Formula.and φ1 φ2, by
                      rw [if_neg (by omega), if_pos rfl, hb1]
                      simp only [Option.bind_some]
                      rw [hb2]
                      simp only [Option.bind_some]⟩
                  · exact ⟨LO.Propositional.Formula.or φ1 φ2, by
                      rw [if_neg (by omega), if_neg (by omega), if_pos rfl, hb1]
                      simp only [Option.bind_some]
                      rw [hb2]
                      simp only [Option.bind_some]⟩
                · -- Second child poisons.
                  refine Or.inr fun fuel tail => ?_
                  match fuel with
                  | 0 => rfl
                  | fuel + 1 =>
                      rw [List.cons_append, parseRpn_cons, if_neg (by omega),
                        if_neg ht1]
                      have hrest : u' ++ tail = u1 ++ (u2 ++ tail) := by
                        rw [hsplit, List.append_assoc]
                      have hnone : ∀ (mk : Sentence → Sentence → Sentence),
                          ((parseRpn fuel (u' ++ tail)).bind fun p =>
                            (parseRpn fuel p.2).bind fun q =>
                              some (mk p.1 q.1, q.2)) = none := by
                        intro mk
                        cases hp : parseRpn fuel (u' ++ tail) with
                        | none => rfl
                        | some pr =>
                            have hbig : parseRpn (fuel + u1.length)
                                (u' ++ tail) = some pr :=
                              parseRpn_mono _ (by omega) hp
                            have hblk : parseRpn (fuel + u1.length)
                                (u' ++ tail) = some (φ1, u2 ++ tail) := by
                              rw [hrest]
                              exact parseRpn_block_head hφ1 (u2 ++ tail)
                                (by omega)
                            rw [hblk] at hbig
                            obtain rfl := Option.some.inj hbig
                            simp only [Option.bind_some]
                            rw [hpoison2 fuel tail]
                            rfl
                      rcases htop with rfl | rfl | rfl
                      · rw [if_pos rfl]
                        exact hnone _
                      · rw [if_neg (by omega), if_pos rfl]
                        exact hnone _
                      · rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
                        exact hnone _
              · -- First child poisons.
                refine Or.inr fun fuel tail => ?_
                match fuel with
                | 0 => rfl
                | fuel + 1 =>
                    rw [List.cons_append, parseRpn_cons, if_neg (by omega),
                      if_neg ht1]
                    have hrest : u' ++ tail = u1 ++ (u2 ++ tail) := by
                      rw [hsplit, List.append_assoc]
                    have hnone : ∀ (mk : Sentence → Sentence → Sentence),
                        ((parseRpn fuel (u' ++ tail)).bind fun p =>
                          (parseRpn fuel p.2).bind fun q =>
                            some (mk p.1 q.1, q.2)) = none := by
                      intro mk
                      rw [hrest, hpoison1 fuel (u2 ++ tail)]
                      rfl
                    rcases htop with rfl | rfl | rfl
                    · rw [if_pos rfl]
                      exact hnone _
                    · rw [if_neg (by omega), if_pos rfl]
                      exact hnone _
                    · rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
                      exact hnone _
            · -- Leaf (`0` or an atom): the run is exactly `[t]`.
              have hstep1 : rpnCondStep (rcPack a (c + 1) r) t =
                  (if c = 0 then exit (r + 1) else rcPack a c (r + 1)) := by
                rw [hrun, if_neg ht1, if_neg htop]
              have hu' : u' = [] := by
                by_contra hne
                have h1len : 1 < (t :: u').length := by
                  simp only [List.length_cons]
                  have := List.length_pos_iff.mpr hne
                  omega
                have := h2 1 h1len
                rw [show (t :: u').take 1 = [t] from rfl, hW1, hstep1] at this
                by_cases hc : c = 0
                · rw [if_pos hc] at this
                  have hcnt := this.2
                  rw [hexitCnt] at hcnt
                  omega
                · rw [if_neg hc] at this
                  simp only [rcMode_pack, rcCnt_pack] at this
                  omega
              subst hu'
              by_cases ht0 : t = 0
              · exact Or.inl ⟨LO.Propositional.Formula.falsum, by
                  subst ht0
                  rfl⟩
              · exact Or.inl ⟨LO.Propositional.Formula.atom (t - 5), by
                  rw [show ([t] : List ℕ).length = 0 + 1 from rfl, parseRpn_cons,
                    if_neg ht0, if_neg ht1, if_neg (by omega), if_neg (by omega),
                    if_neg (by omega)]⟩

/-- Price-run instance of the converse walk lemma: exit into the day-expect mode. -/
lemma parse_of_priceRunWalk : ∀ (N : ℕ) (u : List ℕ), u.length ≤ N → ∀ (c r : ℕ),
    List.foldl rpnCondStep (rcPack 1 (c + 1) r) u =
      (if c = 0 then rcPack 2 0 (r + u.length) else rcPack 1 c (r + u.length)) →
    (∀ k < u.length,
      (rcMode (List.foldl rpnCondStep (rcPack 1 (c + 1) r) (u.take k)) = 1 ∨
        rcMode (List.foldl rpnCondStep (rcPack 1 (c + 1) r) (u.take k)) = 6) ∧
      c + 1 ≤ rcCnt (List.foldl rpnCondStep (rcPack 1 (c + 1) r) (u.take k))) →
    (∃ φ, parseRpn u.length u = some (φ, [])) ∨
    (∀ fuel tail, parseRpn fuel (u ++ tail) = none) :=
  parse_of_runWalk (b := 6) (exit := fun r' => rcPack 2 0 r')
    (fun c r t => rpnCondStep_price c r t)
    (fun c r t => rpnCondStep_priceEsc c r t)
    (fun r' => rcCnt_pack 2 0 r')
    (fun r' => ⟨by simp, by simp⟩)

/-- Trade-run instance of the converse walk lemma: exit back to base. -/
lemma parse_of_tradeRunWalk : ∀ (N : ℕ) (u : List ℕ), u.length ≤ N → ∀ (c r : ℕ),
    List.foldl rpnCondStep (rcPack 4 (c + 1) r) u =
      (if c = 0 then rcPack 0 0 0 else rcPack 4 c (r + u.length)) →
    (∀ k < u.length,
      (rcMode (List.foldl rpnCondStep (rcPack 4 (c + 1) r) (u.take k)) = 4 ∨
        rcMode (List.foldl rpnCondStep (rcPack 4 (c + 1) r) (u.take k)) = 7) ∧
      c + 1 ≤ rcCnt (List.foldl rpnCondStep (rcPack 4 (c + 1) r) (u.take k))) →
    (∃ φ, parseRpn u.length u = some (φ, [])) ∨
    (∀ fuel tail, parseRpn fuel (u ++ tail) = none) :=
  parse_of_runWalk (b := 7) (exit := fun _ => rcPack 0 0 0)
    (fun c r t => rpnCondStep_trade c r t)
    (fun c r t => rpnCondStep_tradeEsc c r t)
    (fun r' => rcCnt_pack 0 0 0)
    (fun r' => ⟨by simp, by simp⟩)

#print axioms parseRpn_strip
#print axioms parse_of_runWalk
#print axioms parse_of_priceRunWalk
#print axioms parse_of_tradeRunWalk

/-! ## Whole-stream contraction exactness (the master commutation)

`unRpn` of the transducer output on an **arbitrary** stream — garbage included — is
the token-model price rewrite (`conditionPriceTokenRun`) of the contraction.  The
proof is a chunk induction: well-formed chunks contract by
`unRpn_price_rewrite_chunk` / `unRpn_trade_chunk_block`; a malformed chunk poisons
both sides at the same chunk (the transducer's insertion sits beyond the poisoned
run, so the `∀`-tail poison of `parse_of_runWalk` kills the rewritten stream too). -/

/-- The cons unfolding of the streaming rewrite. -/
lemma rpnConditionRun_cons (emit : List ℕ → ℕ → List ℕ) (st : ℕ) (buf : List ℕ)
    (t : ℕ) (ts : List ℕ) :
    rpnConditionRun emit (st, buf) (t :: ts) =
      ((rpnConditionRun emit (rpnCondStep st t, rpnCondBuf st buf t) ts).1,
        (if rcMode st = 2 then emit buf t else [t]) ++
          (rpnConditionRun emit (rpnCondStep st t, rpnCondBuf st buf t) ts).2) :=
  rfl

/-! ### Base-state and reset step equations -/

/-- The step from the base control state. -/
lemma rpnCondStep_base (t : ℕ) :
    rpnCondStep (rcPack 0 0 0) t =
      if t = 0 then rcPack 1 1 0
      else if t = 1 then rcPack 3 0 0
      else if t = 6 then rcPack 4 1 0
      else if t = 7 then rcPack 5 0 0
      else rcPack 0 0 0 := by
  rw [rpnCondStep]
  simp only [rcMode_pack, rcCnt_pack, rcLen_pack]
  simp

lemma rpnCondStep_base_price : rpnCondStep (rcPack 0 0 0) 0 = rcPack 1 1 0 := by
  rw [rpnCondStep_base]
  norm_num

lemma rpnCondStep_base_one : rpnCondStep (rcPack 0 0 0) 1 = rcPack 3 0 0 := by
  rw [rpnCondStep_base]
  norm_num

lemma rpnCondStep_base_trade : rpnCondStep (rcPack 0 0 0) 6 = rcPack 4 1 0 := by
  rw [rpnCondStep_base]
  norm_num

lemma rpnCondStep_base_seven : rpnCondStep (rcPack 0 0 0) 7 = rcPack 5 0 0 := by
  rw [rpnCondStep_base]
  norm_num

lemma rpnCondStep_base_other (t : ℕ)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (h6 : t ≠ 6) (h7 : t ≠ 7) :
    rpnCondStep (rcPack 0 0 0) t = rcPack 0 0 0 := by
  rw [rpnCondStep_base, if_neg h0, if_neg h1, if_neg h6, if_neg h7]

/-- Any mode outside the walking set falls back to base. -/
lemma rpnCondStep_fallback (st t : ℕ)
    (h0 : rcMode st ≠ 0) (h1 : rcMode st ≠ 1) (h6 : rcMode st ≠ 6)
    (h4 : rcMode st ≠ 4) (h7 : rcMode st ≠ 7) :
    rpnCondStep st t = rcPack 0 0 0 := by
  rw [rpnCondStep, if_neg h0, if_neg h1, if_neg h6, if_neg h4, if_neg h7]

lemma rcLen_step_base (t : ℕ) : rcLen (rpnCondStep (rcPack 0 0 0) t) = 0 := by
  rw [rpnCondStep_base]
  split_ifs <;> simp

lemma rpnCondBuf_of_len_zero (st : ℕ) (buf : List ℕ) (t : ℕ)
    (h : rcLen (rpnCondStep st t) = 0) : rpnCondBuf st buf t = [] := by
  rw [rpnCondBuf, if_pos h]

lemma rpnCondBuf_base (buf : List ℕ) (t : ℕ) :
    rpnCondBuf (rcPack 0 0 0) buf t = [] :=
  rpnCondBuf_of_len_zero _ _ _ (rcLen_step_base t)

/-- The cons unfolding from an opaque-payload mode (`3` / `5`): copy and fall back. -/
lemma rpnConditionRun_from_payload (emit : List ℕ → ℕ → List ℕ)
    (m c' r' : ℕ) (hm : m = 3 ∨ m = 5) (buf : List ℕ) (t : ℕ) (L : List ℕ) :
    rpnConditionRun emit (rcPack m c' r', buf) (t :: L) =
      ((rpnConditionRun emit (rcPack 0 0 0, []) L).1,
        t :: (rpnConditionRun emit (rcPack 0 0 0, []) L).2) := by
  have hstep : rpnCondStep (rcPack m c' r') t = rcPack 0 0 0 :=
    rpnCondStep_fallback _ _
      (by rcases hm with rfl | rfl <;> simp)
      (by rcases hm with rfl | rfl <;> simp)
      (by rcases hm with rfl | rfl <;> simp)
      (by rcases hm with rfl | rfl <;> simp)
      (by rcases hm with rfl | rfl <;> simp)
  have hbuf : rpnCondBuf (rcPack m c' r') buf t = [] :=
    rpnCondBuf_of_len_zero _ _ _ (by rw [hstep]; simp)
  rw [rpnConditionRun_cons, hstep, hbuf,
    if_neg (by rcases hm with rfl | rfl <;> simp)]
  simp

/-- The cons unfolding at a price-day slot: emit the conditional-price expansion and
fall back to base. -/
lemma rpnConditionRun_from_day (emit : List ℕ → ℕ → List ℕ)
    (r' : ℕ) (buf : List ℕ) (d : ℕ) (L : List ℕ) :
    rpnConditionRun emit (rcPack 2 0 r', buf) (d :: L) =
      ((rpnConditionRun emit (rcPack 0 0 0, []) L).1,
        emit buf d ++
          (rpnConditionRun emit (rcPack 0 0 0, []) L).2) := by
  have hstep : rpnCondStep (rcPack 2 0 r') d = rcPack 0 0 0 :=
    rpnCondStep_fallback _ _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have hbuf : rpnCondBuf (rcPack 2 0 r') buf d = [] :=
    rpnCondBuf_of_len_zero _ _ _ (by rw [hstep]; simp)
  rw [rpnConditionRun_cons, hstep, hbuf, if_pos (by simp)]

/-! ### Copy behavior and the buffer fold -/

/-- The buffer after a copied stretch (fold of `rpnCondBuf` along the walk). -/
def rpnCondBufFold (st : ℕ) (buf : List ℕ) : List ℕ → List ℕ
  | [] => buf
  | t :: ts => rpnCondBufFold (rpnCondStep st t) (rpnCondBuf st buf t) ts

lemma rpnCondBufFold_append (st : ℕ) (buf : List ℕ) (xs ys : List ℕ) :
    rpnCondBufFold st buf (xs ++ ys) =
      rpnCondBufFold (List.foldl rpnCondStep st xs)
        (rpnCondBufFold st buf xs) ys := by
  induction xs generalizing st buf with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.cons_append, rpnCondBufFold, List.foldl_cons]
      rw [ih]

/-- Copy behavior: while no consumed position is in the emission mode `2`, the
transducer copies its input verbatim. -/
lemma rpnConditionRun_copy_of_ne_two (emit : List ℕ → ℕ → List ℕ)
    (st : ℕ) (buf : List ℕ) (ts : List ℕ)
    (h : ∀ k < ts.length, rcMode (List.foldl rpnCondStep st (ts.take k)) ≠ 2) :
    rpnConditionRun emit (st, buf) ts =
      ((List.foldl rpnCondStep st ts, rpnCondBufFold st buf ts), ts) := by
  induction ts generalizing st buf with
  | nil => rfl
  | cons t ts ih =>
      have h0 : rcMode st ≠ 2 := by
        have := h 0 (by simp)
        simpa using this
      rw [rpnConditionRun_cons, if_neg h0,
        ih (rpnCondStep st t) (rpnCondBuf st buf t) (fun k hk => by
          have := h (k + 1) (by simp only [List.length_cons]; omega)
          rwa [List.take_succ_cons, List.foldl_cons] at this)]
      simp [rpnCondBufFold]

/-- Along a price run the buffer accumulates the walked tokens. -/
lemma rpnCondBufFold_run (st : ℕ) (buf : List ℕ) (ts : List ℕ)
    (h : ∀ k < ts.length,
      rcMode (List.foldl rpnCondStep st (ts.take k)) = 1 ∨
      rcMode (List.foldl rpnCondStep st (ts.take k)) = 6) :
    rpnCondBufFold st buf ts = buf ++ ts := by
  induction ts generalizing st buf with
  | nil => simp [rpnCondBufFold]
  | cons t ts ih =>
      have h0 : rcMode st = 1 ∨ rcMode st = 6 := by
        have := h 0 (by simp)
        simpa using this
      have hbuf : rpnCondBuf st buf t = buf ++ [t] := by
        rw [rpnCondBuf, rcLen_run_step st t h0, if_neg (by omega)]
      rw [show rpnCondBufFold st buf (t :: ts) =
          rpnCondBufFold (rpnCondStep st t) (rpnCondBuf st buf t) ts from rfl,
        hbuf, ih (rpnCondStep st t) (buf ++ [t]) (fun k hk => by
          have := h (k + 1) (by simp only [List.length_cons]; omega)
          rwa [List.take_succ_cons, List.foldl_cons] at this)]
      simp

/-- The buffer is empty after any nonempty stretch whose final control has run
length `0`. -/
lemma rpnCondBufFold_reset (st : ℕ) (buf : List ℕ) (ts : List ℕ) (hne : ts ≠ [])
    (h : rcLen (List.foldl rpnCondStep st ts) = 0) :
    rpnCondBufFold st buf ts = [] := by
  rcases List.eq_nil_or_concat' ts with rfl | ⟨ts', t, rfl⟩
  · exact absurd rfl hne
  · rw [rpnCondBufFold_append]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    rw [show rpnCondBufFold (List.foldl rpnCondStep st ts')
        (rpnCondBufFold st buf ts') [t] =
      rpnCondBuf (List.foldl rpnCondStep st ts')
        (rpnCondBufFold st buf ts') t from rfl]
    exact rpnCondBuf_of_len_zero _ _ _ h

/-! ### Run-walk trajectory invariants (first-exit localization) -/

/-- While no prefix has exited, the walk from a fresh run entry stays in the run
modes with positive counter and run length equal to the position. -/
lemma runWalk_inside {a b : ℕ} {exit : ℕ → ℕ}
    (hrun : ∀ c r t, rpnCondStep (rcPack a (c + 1) r) t =
      if t = 1 then rcPack b (c + 1) (r + 1)
      else if t = 2 ∨ t = 3 ∨ t = 4 then rcPack a (c + 2) (r + 1)
      else if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (hesc : ∀ c r t, rpnCondStep (rcPack b (c + 1) r) t =
      if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (e : ℕ) (hexitModeEq : ∀ r', rcMode (exit r') = e)
    (v : List ℕ) : ∀ j, j ≤ v.length →
    (∀ i, i ≤ j → rcMode (List.foldl rpnCondStep (rcPack a 1 0) (v.take i)) ≠ e) →
    (rcMode (List.foldl rpnCondStep (rcPack a 1 0) (v.take j)) = a ∨
      rcMode (List.foldl rpnCondStep (rcPack a 1 0) (v.take j)) = b) ∧
    1 ≤ rcCnt (List.foldl rpnCondStep (rcPack a 1 0) (v.take j)) ∧
    rcLen (List.foldl rpnCondStep (rcPack a 1 0) (v.take j)) = j := by
  intro j
  induction j with
  | zero => intro _ _; simp
  | succ j ih =>
      intro hj hmods
      have hjlt : j < v.length := by omega
      obtain ⟨hm, hc, hl⟩ := ih (by omega) (fun i hi => hmods i (by omega))
      have htake : v.take (j + 1) = v.take j ++ [v[j]'hjlt] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hjlt]
        rfl
      have hstep : List.foldl rpnCondStep (rcPack a 1 0) (v.take (j + 1)) =
          rpnCondStep (List.foldl rpnCondStep (rcPack a 1 0) (v.take j))
            (v[j]'hjlt) := by
        rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hstep]
      rcases runWalk_step_cases hrun hesc _ (v[j]'hjlt) hm hc with
        ⟨hm', hc', hl'⟩ | hexitEq
      · exact ⟨hm', hc', by rw [hl', hl]⟩
      · exfalso
        refine hmods (j + 1) le_rfl ?_
        rw [hstep, hexitEq, hexitModeEq]

/-- At the first exit position the walk state is exactly the exit, and every earlier
position is strictly inside. -/
lemma runWalk_first_exit {a b : ℕ} {exit : ℕ → ℕ}
    (hrun : ∀ c r t, rpnCondStep (rcPack a (c + 1) r) t =
      if t = 1 then rcPack b (c + 1) (r + 1)
      else if t = 2 ∨ t = 3 ∨ t = 4 then rcPack a (c + 2) (r + 1)
      else if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (hesc : ∀ c r t, rpnCondStep (rcPack b (c + 1) r) t =
      if c = 0 then exit (r + 1) else rcPack a c (r + 1))
    (e : ℕ) (hexitModeEq : ∀ r', rcMode (exit r') = e)
    (hea : e ≠ a) (heb : e ≠ b)
    (v : List ℕ) (k₀ : ℕ) (hk₀ : k₀ ≤ v.length)
    (hfirst : ∀ i < k₀,
      rcMode (List.foldl rpnCondStep (rcPack a 1 0) (v.take i)) ≠ e)
    (hexitAt : rcMode (List.foldl rpnCondStep (rcPack a 1 0) (v.take k₀)) = e) :
    1 ≤ k₀ ∧
    List.foldl rpnCondStep (rcPack a 1 0) (v.take k₀) = exit k₀ ∧
    ∀ i < k₀,
      ((rcMode (List.foldl rpnCondStep (rcPack a 1 0) (v.take i)) = a ∨
        rcMode (List.foldl rpnCondStep (rcPack a 1 0) (v.take i)) = b) ∧
      1 ≤ rcCnt (List.foldl rpnCondStep (rcPack a 1 0) (v.take i)) ∧
      rcLen (List.foldl rpnCondStep (rcPack a 1 0) (v.take i)) = i) := by
  have hpos : 1 ≤ k₀ := by
    by_contra h
    have hk0 : k₀ = 0 := by omega
    subst hk0
    rw [List.take_zero, List.foldl_nil, rcMode_pack] at hexitAt
    exact hea hexitAt.symm
  have hinside : ∀ i < k₀,
      ((rcMode (List.foldl rpnCondStep (rcPack a 1 0) (v.take i)) = a ∨
        rcMode (List.foldl rpnCondStep (rcPack a 1 0) (v.take i)) = b) ∧
      1 ≤ rcCnt (List.foldl rpnCondStep (rcPack a 1 0) (v.take i)) ∧
      rcLen (List.foldl rpnCondStep (rcPack a 1 0) (v.take i)) = i) := fun i hi =>
    runWalk_inside hrun hesc e hexitModeEq v i (by omega)
      (fun i' hi' => hfirst i' (by omega))
  refine ⟨hpos, ?_, hinside⟩
  have hklt : k₀ - 1 < v.length := by omega
  have htake : v.take k₀ = v.take (k₀ - 1) ++ [v[k₀ - 1]'hklt] := by
    conv_lhs => rw [show k₀ = (k₀ - 1) + 1 by omega]
    rw [List.take_add_one, List.getElem?_eq_getElem hklt]
    rfl
  obtain ⟨hm, hc, hl⟩ := hinside (k₀ - 1) (by omega)
  rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil] at hexitAt ⊢
  rcases runWalk_step_cases hrun hesc _ (v[k₀ - 1]'hklt) hm hc with
    ⟨hm', -, -⟩ | hexitEq
  · exfalso
    rcases hm' with h | h
    · rw [h] at hexitAt
      exact hea hexitAt.symm
    · rw [h] at hexitAt
      exact heb hexitAt.symm
  · rw [hexitEq, hl]
    congr 1
    omega

/-- Price-run instance of the first-exit localization. -/
lemma priceWalk_first_exit (v : List ℕ) (k₀ : ℕ) (hk₀ : k₀ ≤ v.length)
    (hfirst : ∀ i < k₀,
      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (v.take i)) ≠ 2)
    (hexitAt : rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (v.take k₀)) = 2) :
    1 ≤ k₀ ∧
    List.foldl rpnCondStep (rcPack 1 1 0) (v.take k₀) = rcPack 2 0 k₀ ∧
    ∀ i < k₀,
      ((rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (v.take i)) = 1 ∨
        rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (v.take i)) = 6) ∧
      1 ≤ rcCnt (List.foldl rpnCondStep (rcPack 1 1 0) (v.take i)) ∧
      rcLen (List.foldl rpnCondStep (rcPack 1 1 0) (v.take i)) = i) :=
  runWalk_first_exit (b := 6) (exit := fun r' => rcPack 2 0 r')
    (fun c r t => rpnCondStep_price c r t)
    (fun c r t => rpnCondStep_priceEsc c r t)
    2 (fun r' => rcMode_pack 2 0 r') (by norm_num) (by norm_num)
    v k₀ hk₀ hfirst hexitAt

/-- Trade-run instance of the first-exit localization. -/
lemma tradeWalk_first_exit (v : List ℕ) (k₀ : ℕ) (hk₀ : k₀ ≤ v.length)
    (hfirst : ∀ i < k₀,
      rcMode (List.foldl rpnCondStep (rcPack 4 1 0) (v.take i)) ≠ 0)
    (hexitAt : rcMode (List.foldl rpnCondStep (rcPack 4 1 0) (v.take k₀)) = 0) :
    1 ≤ k₀ ∧
    List.foldl rpnCondStep (rcPack 4 1 0) (v.take k₀) = rcPack 0 0 0 ∧
    ∀ i < k₀,
      ((rcMode (List.foldl rpnCondStep (rcPack 4 1 0) (v.take i)) = 4 ∨
        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) (v.take i)) = 7) ∧
      1 ≤ rcCnt (List.foldl rpnCondStep (rcPack 4 1 0) (v.take i)) ∧
      rcLen (List.foldl rpnCondStep (rcPack 4 1 0) (v.take i)) = i) :=
  runWalk_first_exit (b := 7) (exit := fun _ => rcPack 0 0 0)
    (fun c r t => rpnCondStep_trade c r t)
    (fun c r t => rpnCondStep_tradeEsc c r t)
    0 (fun _ => rcMode_pack 0 0 0) (by norm_num) (by norm_num)
    v k₀ hk₀ hfirst hexitAt

/-- Trade-run instance of the inside invariant (for streams that never exit). -/
lemma tradeWalk_inside (v : List ℕ) (j : ℕ) (hj : j ≤ v.length)
    (hmods : ∀ i, i ≤ j →
      rcMode (List.foldl rpnCondStep (rcPack 4 1 0) (v.take i)) ≠ 0) :
    (rcMode (List.foldl rpnCondStep (rcPack 4 1 0) (v.take j)) = 4 ∨
      rcMode (List.foldl rpnCondStep (rcPack 4 1 0) (v.take j)) = 7) ∧
    1 ≤ rcCnt (List.foldl rpnCondStep (rcPack 4 1 0) (v.take j)) ∧
    rcLen (List.foldl rpnCondStep (rcPack 4 1 0) (v.take j)) = j :=
  runWalk_inside (b := 7) (exit := fun _ => rcPack 0 0 0)
    (fun c r t => rpnCondStep_trade c r t)
    (fun c r t => rpnCondStep_tradeEsc c r t)
    0 (fun _ => rcMode_pack 0 0 0) v j hj hmods

/-! ### Token-model run equations (per contracted chunk) -/

section TokenRunEq

variable (ψc : ℕ → ℕ) (ε : ℚ)

lemma conditionPriceTokenRun_single (t : ℕ)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (h6 : t ≠ 6) (h7 : t ≠ 7) (L : List ℕ) :
    (conditionPriceTokenRun ψc ε (0, 0) (t :: L)).2 =
      t :: (conditionPriceTokenRun ψc ε (0, 0) L).2 := by
  simp [conditionPriceTokenRun, conditionPriceTokenEmit, EF.freezeTokenNext,
    h0, h1, h6, h7]

lemma conditionPriceTokenRun_one (t : ℕ) :
    (conditionPriceTokenRun ψc ε (0, 0) [t]).2 = [t] := by
  simp [conditionPriceTokenRun, conditionPriceTokenEmit]

lemma conditionPriceTokenRun_payload (t c : ℕ) (ht : t = 1 ∨ t = 7) (L : List ℕ) :
    (conditionPriceTokenRun ψc ε (0, 0) (t :: c :: L)).2 =
      t :: c :: (conditionPriceTokenRun ψc ε (0, 0) L).2 := by
  rcases ht with rfl | rfl <;>
    simp [conditionPriceTokenRun, conditionPriceTokenEmit, EF.freezeTokenNext]

lemma conditionPriceTokenRun_price (fc d : ℕ) (L : List ℕ) :
    (conditionPriceTokenRun ψc ε (0, 0) (0 :: fc :: d :: L)).2 =
      0 :: fc :: d :: (rawConditionalPriceTokens fc (ψc d) d ε ++
        8 :: (conditionPriceTokenRun ψc ε (0, 0) L).2) := by
  simp [conditionPriceTokenRun, conditionPriceTokenEmit, EF.freezeTokenNext]

lemma conditionPriceTokenRun_price_pair (fc : ℕ) :
    (conditionPriceTokenRun ψc ε (0, 0) [0, fc]).2 = [0, fc] := by
  simp [conditionPriceTokenRun, conditionPriceTokenEmit, EF.freezeTokenNext]

lemma conditionPriceTokenRun_trade (fc : ℕ) (L : List ℕ) :
    (conditionPriceTokenRun ψc ε (0, 0) (6 :: fc :: L)).2 =
      6 :: fc :: (conditionPriceTokenRun ψc ε (0, 0) L).2 := by
  simp [conditionPriceTokenRun, conditionPriceTokenEmit, EF.freezeTokenNext]

end TokenRunEq

/-! ### The master commutation -/

/-- **Whole-stream contraction exactness, for an arbitrary emitter**: on every input
stream — well-formed or garbage — the contraction of the transducer output is the
token-model rewrite `R` of the contraction, provided `R` copies every non-price chunk,
splices the shared price body `Z` at a completed price leaf, and the symbol emitter
contracts to that same body (`hemit`).
Paper node: `thm:scon` -/
theorem unRpn_rpnConditionRun_of (emit : List ℕ → ℕ → List ℕ) (R : List ℕ → List ℕ)
    (Z : ℕ → ℕ → List ℕ)
    (hRnil : R [] = [])
    (hRsingle : ∀ t L, t ≠ 0 → t ≠ 1 → t ≠ 6 → t ≠ 7 → R (t :: L) = t :: R L)
    (hRone : ∀ t, R [t] = [t])
    (hRpayload : ∀ t c L, (t = 1 ∨ t = 7) → R (t :: c :: L) = t :: c :: R L)
    (hRprice : ∀ fc d L, R (0 :: fc :: d :: L) = 0 :: fc :: d :: (Z fc d ++ R L))
    (hRpricePair : ∀ fc, R [0, fc] = [0, fc])
    (hRtrade : ∀ fc L, R (6 :: fc :: L) = 6 :: fc :: R L)
    (hemit : ∀ (b : List ℕ) (φ : Sentence),
      parseRpn b.length b = some (φ, []) → ∀ (D : ℕ) (rest : List ℕ),
        unRpn (0 :: b ++ emit b D ++ rest) =
          0 :: Encodable.encode φ :: D ::
            (Z (Encodable.encode φ) D ++ unRpn rest)) :
    ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    unRpn ((rpnConditionRun emit (rcPack 0 0 0, []) ts).2) = R (unRpn ts) := by
  intro N
  induction N with
  | zero =>
      intro ts hts
      obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact hRnil.symm
  | succ N ih =>
      intro ts hts
      match ts with
      | [] => exact hRnil.symm
      | t :: rest =>
          simp only [List.length_cons] at hts
          by_cases ht0 : t = 0
          · -- Price chunk.
            subst ht0
            cases hp : parseRpn rest.length rest with
            | some pr =>
                obtain ⟨φ, r1⟩ := pr
                obtain ⟨blk, heq, hblk⟩ := parseRpn_strip rest.length rest hp
                obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_price_block hblk
                match r1 with
                | [] =>
                    rw [List.append_nil] at heq
                    subst heq
                    -- Transducer output: pure copy (the walk exits only at the
                    -- final state, which is never consumed).
                    have hout : (rpnConditionRun emit (rcPack 0 0 0, [])
                        (0 :: rest)).2 = 0 :: rest :=
                      congrArg Prod.snd (rpnConditionRun_copy_of_ne_two emit
                        (rcPack 0 0 0) [] (0 :: rest) (by
                          intro k hk
                          match k with
                          | 0 => simp
                          | j + 1 =>
                              simp only [List.length_cons] at hk
                              rw [List.take_succ_cons, List.foldl_cons,
                                rpnCondStep_base_price]
                              have := hinv j (by omega)
                              omega))
                    have hun : unRpn (0 :: rest) = [0, Encodable.encode φ] := by
                      rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
                        hblk]
                    rw [hout, hun, hRpricePair]
                | d :: r2 =>
                    subst heq
                    -- Transducer output: copy the block, splice at the day.
                    have hblkcopy : rpnConditionRun emit (rcPack 1 1 0, [])
                        blk = ((rcPack 2 0 blk.length, blk), blk) := by
                      rw [rpnConditionRun_copy_of_ne_two emit _ _ _
                        (fun k hk => by have := hinv k hk; omega)]
                      rw [hwalk, rpnCondBufFold_run _ _ _ (fun k hk => hinv k hk)]
                      simp
                    have hout : (rpnConditionRun emit (rcPack 0 0 0, [])
                        (0 :: (blk ++ d :: r2))).2 =
                      0 :: blk ++ emit blk d ++
                        (rpnConditionRun emit (rcPack 0 0 0, []) r2).2 := by
                      rw [rpnConditionRun_cons, if_neg (by simp),
                        rpnCondStep_base_price, rpnCondBuf_base,
                        rpnConditionRun_append]
                      simp [hblkcopy, rpnConditionRun_from_day,
                        List.append_assoc]
                    have hr2 : r2.length ≤ N := by
                      have hlt := parseRpn_length_lt _ _ _ _ hp
                      simp only [List.length_cons] at hlt
                      omega
                    rw [hout,
                      hemit blk _ hblk d _,
                      ih r2 hr2,
                      unRpn_price_chunk_block hblk d r2,
                      hRprice]
            | none =>
                have hun0 : unRpn (0 :: rest) = [0, 0] := by
                  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl, hp]
                by_cases hex : ∃ k, k < rest.length ∧
                    rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                      (rest.take k)) = 2
                · -- First completion: the walked prefix poisons every extension.
                  classical
                  obtain ⟨hk₀lt, hk₀mode⟩ := Nat.find_spec hex
                  set k₀ := Nat.find hex with hk₀def
                  have hfirst : ∀ i < k₀,
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0)
                        (rest.take i)) ≠ 2 := fun i hi hmode =>
                    Nat.find_min hex hi ⟨by omega, hmode⟩
                  obtain ⟨hk₀pos, hW, hinside⟩ := priceWalk_first_exit rest k₀
                    (le_of_lt hk₀lt) hfirst hk₀mode
                  have htakelen : (rest.take k₀).length = k₀ := by
                    rw [List.length_take]
                    omega
                  have hconv := parse_of_priceRunWalk k₀ (rest.take k₀)
                    (le_of_eq htakelen) 0 0
                    (by
                      rw [if_pos rfl, htakelen]
                      simpa using hW)
                    (by
                      intro k hk
                      rw [htakelen] at hk
                      rw [List.take_take, min_eq_left (le_of_lt hk)]
                      exact ⟨(hinside k hk).1, (hinside k hk).2.1⟩)
                  rcases hconv with ⟨φu, hφu⟩ | hpoison
                  · exfalso
                    rw [← List.take_append_drop k₀ rest] at hp
                    rw [parseRpn_block_head hφu (rest.drop k₀) (by
                      simp only [List.length_append]
                      omega)] at hp
                    simp at hp
                  · -- Both contractions stop with `[0, 0]` at this chunk.
                    have hucopy := rpnConditionRun_copy_of_ne_two emit
                      (rcPack 1 1 0) [] (rest.take k₀) (by
                        intro k hk
                        rw [htakelen] at hk
                        rw [List.take_take, min_eq_left (le_of_lt hk)]
                        have := (hinside k hk).1
                        omega)
                    have hout : (rpnConditionRun emit (rcPack 0 0 0, [])
                        (0 :: rest)).2 = 0 :: (rest.take k₀ ++
                          (rpnConditionRun emit
                            (List.foldl rpnCondStep (rcPack 1 1 0)
                              (rest.take k₀),
                             rpnCondBufFold (rcPack 1 1 0) [] (rest.take k₀))
                            (rest.drop k₀)).2) := by
                      conv_lhs =>
                        rw [show rest = rest.take k₀ ++ rest.drop k₀ from
                          (List.take_append_drop k₀ rest).symm]
                      rw [rpnConditionRun_cons, if_neg (by simp),
                        rpnCondStep_base_price, rpnCondBuf_base,
                        rpnConditionRun_append]
                      simp [hucopy]
                    have hunL : ∀ Y, unRpn (0 :: (rest.take k₀ ++ Y)) =
                        [0, 0] := fun Y => by
                      rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
                        hpoison _ _]
                    rw [hout, hunL, hun0, hRpricePair]
                · -- No completion: pure copy, both contractions stop.
                  have hout : (rpnConditionRun emit (rcPack 0 0 0, [])
                      (0 :: rest)).2 = 0 :: rest :=
                    congrArg Prod.snd (rpnConditionRun_copy_of_ne_two emit
                      (rcPack 0 0 0) [] (0 :: rest) (by
                        intro k hk
                        match k with
                        | 0 => simp
                        | j + 1 =>
                            simp only [List.length_cons] at hk
                            rw [List.take_succ_cons, List.foldl_cons,
                              rpnCondStep_base_price]
                            exact fun hmode => hex ⟨j, by omega, hmode⟩))
                  rw [hout, hun0, hRpricePair]
          · by_cases ht6 : t = 6
            · -- Trade chunk.
              subst ht6
              cases hp : parseRpn rest.length rest with
              | some pr =>
                  obtain ⟨φ, r1⟩ := pr
                  obtain ⟨blk, heq, hblk⟩ := parseRpn_strip rest.length rest hp
                  subst heq
                  obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_trade_block hblk
                  have hblkne : blk ≠ [] := by
                    have := parseRpn_length_lt blk.length blk φ [] hblk
                    intro hnil
                    rw [hnil] at this
                    simp at this
                  have hblkcopy : rpnConditionRun emit (rcPack 4 1 0, [])
                      blk = ((rcPack 0 0 0, []), blk) := by
                    rw [rpnConditionRun_copy_of_ne_two emit _ _ _
                      (fun k hk => by have := hinv k hk; omega)]
                    rw [hwalk, rpnCondBufFold_reset _ _ _ hblkne (by
                      rw [hwalk]; simp)]
                  have hout : (rpnConditionRun emit (rcPack 0 0 0, [])
                      (6 :: (blk ++ r1))).2 =
                    6 :: (blk ++
                      (rpnConditionRun emit (rcPack 0 0 0, []) r1).2) := by
                    rw [rpnConditionRun_cons, if_neg (by simp),
                      rpnCondStep_base_trade, rpnCondBuf_base,
                      rpnConditionRun_append]
                    simp [hblkcopy]
                  have hr1 : r1.length ≤ N := by
                    have hlt := parseRpn_length_lt _ _ _ _ hp
                    omega
                  rw [hout, unRpn_trade_chunk_block hblk _,
                    ih r1 hr1,
                    unRpn_trade_chunk_block hblk r1,
                    hRtrade]
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
                      rw [List.length_take]
                      omega
                    have hconv := parse_of_tradeRunWalk k₀ (rest.take k₀)
                      (le_of_eq htakelen) 0 0
                      (by
                        rw [if_pos rfl]
                        exact hW)
                      (by
                        intro k hk
                        rw [htakelen] at hk
                        rw [List.take_take, min_eq_left (le_of_lt hk)]
                        exact ⟨(hinside k hk).1, (hinside k hk).2.1⟩)
                    rcases hconv with ⟨φu, hφu⟩ | hpoison
                    · exfalso
                      rw [← List.take_append_drop k₀ rest] at hp
                      rw [parseRpn_block_head hφu (rest.drop k₀) (by
                        simp only [List.length_append]
                        omega)] at hp
                      simp at hp
                    · have hucopy := rpnConditionRun_copy_of_ne_two emit
                        (rcPack 4 1 0) [] (rest.take k₀) (by
                          intro k hk
                          rw [htakelen] at hk
                          rw [List.take_take, min_eq_left (le_of_lt hk)]
                          have := (hinside k hk).1
                          omega)
                      have hout : (rpnConditionRun emit (rcPack 0 0 0, [])
                          (6 :: rest)).2 = 6 :: (rest.take k₀ ++
                            (rpnConditionRun emit
                              (List.foldl rpnCondStep (rcPack 4 1 0)
                                (rest.take k₀),
                               rpnCondBufFold (rcPack 4 1 0) []
                                 (rest.take k₀))
                              (rest.drop k₀)).2) := by
                        conv_lhs =>
                          rw [show rest = rest.take k₀ ++ rest.drop k₀ from
                            (List.take_append_drop k₀ rest).symm]
                        rw [rpnConditionRun_cons, if_neg (by simp),
                          rpnCondStep_base_trade, rpnCondBuf_base,
                          rpnConditionRun_append]
                        simp [hucopy]
                      have hunL : ∀ Y, unRpn (6 :: (rest.take k₀ ++ Y)) =
                          [6, 0] := fun Y => by
                        rw [unRpn, List.length_cons, unRpnTokens_cons,
                          if_neg (by norm_num), if_pos rfl, hpoison _ _]
                      rw [hout, hunL, hun0]
                      rw [hRtrade, hRnil]
                  · -- Never exits: pure copy of an unfinished trade run.
                    have hout : (rpnConditionRun emit (rcPack 0 0 0, [])
                        (6 :: rest)).2 = 6 :: rest :=
                      congrArg Prod.snd (rpnConditionRun_copy_of_ne_two emit
                        (rcPack 0 0 0) [] (6 :: rest) (by
                          intro k hk
                          match k with
                          | 0 => simp
                          | j + 1 =>
                              simp only [List.length_cons] at hk
                              rw [List.take_succ_cons, List.foldl_cons,
                                rpnCondStep_base_trade]
                              have hmods : ∀ i, i ≤ j →
                                  rcMode (List.foldl rpnCondStep (rcPack 4 1 0)
                                    (rest.take i)) ≠ 0 := fun i hi hmode =>
                                hex ⟨i, by omega, hmode⟩
                              have := (tradeWalk_inside rest j (by omega)
                                hmods).1
                              omega))
                    rw [hout, hun0]
                    rw [hRtrade, hRnil]
            · by_cases ht1 : t = 1
              · -- Constant payload chunk.
                subst ht1
                match rest with
                | [] =>
                    have hout : (rpnConditionRun emit (rcPack 0 0 0, [])
                        [1]).2 = [1] := by
                      rw [rpnConditionRun_cons, if_neg (by simp)]
                      rfl
                    rw [hout, show unRpn [1] = [1] from rfl,
                      hRone]
                | c :: rest' =>
                    have hout : (rpnConditionRun emit (rcPack 0 0 0, [])
                        (1 :: c :: rest')).2 =
                      1 :: c :: (rpnConditionRun emit (rcPack 0 0 0, [])
                        rest').2 := by
                      rw [rpnConditionRun_cons, if_neg (by simp),
                        rpnCondStep_base_one, rpnCondBuf_base,
                        rpnConditionRun_from_payload emit 3 0 0
                          (Or.inl rfl) [] c rest']
                      rfl
                    have hr : rest'.length ≤ N := by
                      simp only [List.length_cons] at hts
                      omega
                    rw [hout, unRpn_payload_chunk 1 c (Or.inl rfl) _,
                      ih rest' hr,
                      unRpn_payload_chunk 1 c (Or.inl rfl) rest',
                      hRpayload 1 c _ (Or.inl rfl)]
              · by_cases ht7 : t = 7
                · -- Variable payload chunk.
                  subst ht7
                  match rest with
                  | [] =>
                      have hout : (rpnConditionRun emit (rcPack 0 0 0, [])
                          [7]).2 = [7] := by
                        rw [rpnConditionRun_cons, if_neg (by simp)]
                        rfl
                      rw [hout, show unRpn [7] = [7] from rfl,
                        hRone]
                  | c :: rest' =>
                      have hout : (rpnConditionRun emit (rcPack 0 0 0, [])
                          (7 :: c :: rest')).2 =
                        7 :: c :: (rpnConditionRun emit (rcPack 0 0 0, [])
                          rest').2 := by
                        rw [rpnConditionRun_cons, if_neg (by simp),
                          rpnCondStep_base_seven, rpnCondBuf_base,
                          rpnConditionRun_from_payload emit 5 0 0
                            (Or.inr rfl) [] c rest']
                        rfl
                      have hr : rest'.length ≤ N := by
                        simp only [List.length_cons] at hts
                        omega
                      rw [hout, unRpn_payload_chunk 7 c (Or.inr rfl) _,
                        ih rest' hr,
                        unRpn_payload_chunk 7 c (Or.inr rfl) rest',
                        hRpayload 7 c _ (Or.inr rfl)]
                · -- Bare operator/close token: transparent.
                  have hout : (rpnConditionRun emit (rcPack 0 0 0, [])
                      (t :: rest)).2 =
                    t :: (rpnConditionRun emit (rcPack 0 0 0, []) rest).2 := by
                    rw [rpnConditionRun_cons, if_neg (by simp),
                      rpnCondStep_base_other t ht0 ht1 ht6 ht7, rpnCondBuf_base]
                    rfl
                  rw [hout, unRpn_single_chunk t ⟨ht0, ht1, ht6, ht7⟩ _,
                    ih rest (by omega),
                    unRpn_single_chunk t ⟨ht0, ht1, ht6, ht7⟩ rest,
                    hRsingle t _ ht0 ht1 ht6 ht7]

/-- **Whole-stream contraction exactness for the price pass**: on every input stream
— well-formed or garbage — the contraction of the transducer output is the token-model
price rewrite (`conditionPriceTokenRun`) of the contraction.
Paper node: `thm:scon` -/
theorem unRpn_rpnConditionRun (blocks : ℕ → List ℕ) (ψ : ℕ → Sentence)
    (hblocks : ∀ D, parseRpn (blocks D).length (blocks D) = some (ψ D, []))
    (ε : ℚ) : ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    unRpn ((rpnConditionRun (rpnPriceEmit blocks ε) (rcPack 0 0 0, []) ts).2) =
      (conditionPriceTokenRun (fun D => Encodable.encode (ψ D)) ε (0, 0)
        (unRpn ts)).2 :=
  unRpn_rpnConditionRun_of (rpnPriceEmit blocks ε)
    (fun L => (conditionPriceTokenRun (fun D => Encodable.encode (ψ D)) ε (0, 0) L).2)
    (fun fc d => rawConditionalPriceTokens fc (Encodable.encode (ψ d)) d ε ++ [8])
    rfl
    (fun t L h0 h1 h6 h7 => conditionPriceTokenRun_single _ ε t h0 h1 h6 h7 L)
    (fun t => conditionPriceTokenRun_one _ ε t)
    (fun t c L ht => conditionPriceTokenRun_payload _ ε t c ht L)
    (fun fc d L => by
      try simp only []
      rw [conditionPriceTokenRun_price]
      simp [List.append_assoc])
    (fun fc => conditionPriceTokenRun_price_pair _ ε fc)
    (fun fc L => conditionPriceTokenRun_trade _ ε fc L)
    (fun b φ hb D rest => by
      rw [rpnPriceEmit, unRpn_price_rewrite_chunk hb (hblocks D) D ε rest]
      simp [List.append_assoc])

#print axioms unRpn_rpnConditionRun_of
#print axioms unRpn_rpnConditionRun

/-! ## Guard-honesty transfer

An oversized price-day at a run-aware mode-2 position of the **symbol** stream forces
the empty validated strategy on the contraction: either the day survives contraction
at a token-model mode-2 position of `unRpn ts` carrying the same day token — then
`strategyOfTokens_trades_eq_nil_of_bigDay` applies — or an earlier chunk poisoned the
contraction and the decoder rejects from every base-mode state. -/

/-- The contraction rejects from every base-mode parser state (the poison tails
`[0, 0]` / `[6, 0]` are undecodable regardless of the surrounding parse). -/
def Unreadable (out : List ℕ) : Prop :=
  ∀ (mp : ℕ × Option Sentence) (stack : List EF) (trades : List (EF × Sentence)),
    mp.1 = 0 → EF.streamReadFrom out (some (mp, (stack, trades))) = none

lemma Unreadable.deserializeTrades_eq_none {out : List ℕ} (h : Unreadable out) :
    deserializeTrades out = none := by
  unfold deserializeTrades
  rw [show EF.streamReadFrom out (some EF.streamInitial) = none from
    h (0, none) [] [] rfl]

lemma unreadable_price_poison : Unreadable [0, 0] := by
  intro mp stack trades hmp
  obtain ⟨m, pend⟩ := mp
  simp only at hmp
  subst hmp
  simp [EF.streamReadFrom, EF.streamStep, decode_zero_sentence]

lemma unreadable_trade_poison : Unreadable [6, 0] := by
  intro mp stack trades hmp
  obtain ⟨m, pend⟩ := mp
  simp only at hmp
  subst hmp
  rcases stack with _ | ⟨e, st'⟩ <;>
    simp [EF.streamReadFrom, EF.streamStep, decode_zero_sentence]

/-- Prepending a complete contracted chunk (mode automaton returns to base)
preserves unreadability. -/
lemma Unreadable.cons_chunk {C R : List ℕ}
    (hC : List.foldl freezeMode4Step 0 C = 0)
    (h : Unreadable R) : Unreadable (C ++ R) := by
  intro mp stack trades hmp
  rw [EF.streamReadFrom_append]
  cases hmid : EF.streamReadFrom C (some (mp, (stack, trades))) with
  | none => rw [EF.streamReadFrom_none]
  | some st₁ =>
      have hmatch := matches_streamReadFrom C (0, 0) (mp, (stack, trades)) st₁
        ⟨hmp.symm, fun h2 => absurd (hmp.symm.trans h2) (by norm_num)⟩ hmid
      rcases st₁ with ⟨mp₁, stack₁, trades₁⟩
      have hmode1 : mp₁.1 = 0 := by
        have h1 := hmatch.1
        rw [← freezeMode4_eq_foldl] at h1
        rw [show freezeMode4 C = 0 from hC] at h1
        exact h1.symm
      exact h mp₁ stack₁ trades₁ hmode1

/-- Shift a token-model mode-2 witness across a complete contracted chunk. -/
lemma mode2_witness_shift (C R : List ℕ)
    (hC : List.foldl freezeMode4Step 0 C = 0)
    (j'' : ℕ) (hj'' : j'' < R.length) (hm : freezeMode4 (R.take j'') = 2)
    (d : ℕ) (hd : R.getD j'' 0 = d) :
    ∃ j' < (C ++ R).length, freezeMode4 ((C ++ R).take j') = 2 ∧
      (C ++ R).getD j' 0 = d := by
  refine ⟨C.length + j'', by simp only [List.length_append]; omega, ?_, ?_⟩
  · rw [List.take_add, List.take_left, List.drop_left]
    rw [freezeMode4, List.foldl_append, hC]
    exact hm
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    simpa using hd

/-- **Localization of a symbol-level mode-2 position**: it either survives
contraction as a token-model mode-2 position carrying the same day token, or the
contraction is unreadable. -/
lemma rpn_mode2_localize : ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    ∀ j, j < ts.length →
    rcMode (List.foldl rpnCondStep (rcPack 0 0 0) (ts.take j)) = 2 →
    (∃ j' < (unRpn ts).length,
      freezeMode4 ((unRpn ts).take j') = 2 ∧
      (unRpn ts).getD j' 0 = ts.getD j 0) ∨
    Unreadable (unRpn ts) := by
  intro N
  induction N with
  | zero =>
      intro ts hts j hj _
      obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp at hj
  | succ N ih =>
      intro ts hts j hj hmode
      match ts with
      | [] => simp at hj
      | t :: rest =>
          simp only [List.length_cons] at hts hj
          match j with
          | 0 =>
              rw [List.take_zero, List.foldl_nil, rcMode_pack] at hmode
              omega
          | j + 1 =>
              rw [List.take_succ_cons, List.foldl_cons] at hmode
              by_cases ht0 : t = 0
              · -- Price chunk.
                subst ht0
                rw [rpnCondStep_base_price] at hmode
                cases hp : parseRpn rest.length rest with
                | some pr =>
                    obtain ⟨φ, r1⟩ := pr
                    obtain ⟨blk, heq, hblk⟩ := parseRpn_strip rest.length rest hp
                    obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_price_block hblk
                    match r1 with
                    | [] =>
                        rw [List.append_nil] at heq
                        subst heq
                        exfalso
                        have := hinv j (by omega)
                        omega
                    | d :: r2 =>
                        subst heq
                        rcases Nat.lt_trichotomy j blk.length with hjb | hjb | hjb
                        · exfalso
                          rw [List.take_append_of_le_length (le_of_lt hjb)]
                            at hmode
                          have := hinv j hjb
                          omega
                        · -- The day position: direct witness at token index 2.
                          subst hjb
                          refine Or.inl ?_
                          rw [unRpn_price_chunk_block hblk d r2]
                          refine ⟨2, by simp only [List.length_cons]; omega,
                            rfl, ?_⟩
                          simp only [List.getD_cons_succ, List.getD_cons_zero]
                          rw [List.getD_append_right _ _ _ _ le_rfl,
                            Nat.sub_self, List.getD_cons_zero]
                        · -- Beyond the chunk: recurse past the day emission.
                          have hjsplit : j = blk.length + (j - blk.length) := by
                            omega
                          rw [hjsplit, List.take_add, List.take_left,
                            List.drop_left, List.foldl_append, hwalk,
                            show j - blk.length = (j - blk.length - 1) + 1 by
                              omega,
                            List.take_succ_cons, List.foldl_cons,
                            rpnCondStep_fallback _ _ (by simp) (by simp)
                              (by simp) (by simp) (by simp)] at hmode
                          have hjr2 : j - blk.length - 1 < r2.length := by
                            simp only [List.length_append, List.length_cons]
                              at hj
                            omega
                          have hr2N : r2.length ≤ N := by
                            simp only [List.length_append, List.length_cons]
                              at hts
                            omega
                          rcases ih r2 hr2N (j - blk.length - 1) hjr2 hmode with
                            ⟨j'', hj'', hm'', hd''⟩ | hun
                          · refine Or.inl ?_
                            rw [unRpn_price_chunk_block hblk d r2]
                            have := mode2_witness_shift
                              [0, Encodable.encode φ, d] (unRpn r2) rfl
                              j'' hj'' hm'' _ hd''
                            simp only [List.cons_append, List.nil_append]
                              at this
                            refine this.imp fun j' hj' => ?_
                            refine ⟨hj'.1, hj'.2.1, ?_⟩
                            rw [hj'.2.2, List.getD_cons_succ,
                              List.getD_append_right _ _ _ _ (by omega)]
                            conv_rhs => rw [show j - blk.length =
                                (j - blk.length - 1) + 1 from by omega,
                              List.getD_cons_succ]
                          · refine Or.inr ?_
                            rw [unRpn_price_chunk_block hblk d r2]
                            exact Unreadable.cons_chunk
                              (C := [0, Encodable.encode φ, d]) rfl hun
                | none =>
                    refine Or.inr ?_
                    rw [show unRpn (0 :: rest) = [0, 0] from by
                      rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
                        hp]]
                    exact unreadable_price_poison
              · by_cases ht6 : t = 6
                · -- Trade chunk.
                  subst ht6
                  rw [rpnCondStep_base_trade] at hmode
                  cases hp : parseRpn rest.length rest with
                  | some pr =>
                      obtain ⟨φ, r1⟩ := pr
                      obtain ⟨blk, heq, hblk⟩ :=
                        parseRpn_strip rest.length rest hp
                      subst heq
                      obtain ⟨hwalk, hinv⟩ := foldl_rpnCondStep_trade_block hblk
                      rcases Nat.lt_trichotomy j blk.length with hjb | hjb | hjb
                      · exfalso
                        rw [List.take_append_of_le_length (le_of_lt hjb)]
                          at hmode
                        have := hinv j hjb
                        omega
                      · exfalso
                        subst hjb
                        rw [List.take_left, hwalk] at hmode
                        simp at hmode
                      · have hjsplit : j = blk.length + (j - blk.length) := by
                          omega
                        rw [hjsplit, List.take_add, List.take_left,
                          List.drop_left, List.foldl_append, hwalk] at hmode
                        have hjr1 : j - blk.length < r1.length := by
                          simp only [List.length_append] at hj
                          omega
                        have hr1N : r1.length ≤ N := by
                          simp only [List.length_append] at hts
                          have := parseRpn_length_lt blk.length blk φ [] hblk
                          omega
                        rcases ih r1 hr1N (j - blk.length) hjr1 hmode with
                          ⟨j'', hj'', hm'', hd''⟩ | hun
                        · refine Or.inl ?_
                          rw [unRpn_trade_chunk_block hblk r1]
                          have := mode2_witness_shift
                            [6, Encodable.encode φ] (unRpn r1) rfl
                            j'' hj'' hm'' _ hd''
                          simp only [List.cons_append, List.nil_append] at this
                          refine this.imp fun j' hj' => ?_
                          refine ⟨hj'.1, hj'.2.1, ?_⟩
                          rw [hj'.2.2, List.getD_cons_succ,
                            List.getD_append_right _ _ _ _ (by omega)]
                        · refine Or.inr ?_
                          rw [unRpn_trade_chunk_block hblk r1]
                          exact Unreadable.cons_chunk
                            (C := [6, Encodable.encode φ]) rfl hun
                  | none =>
                      refine Or.inr ?_
                      rw [show unRpn (6 :: rest) = [6, 0] from by
                        rw [unRpn, List.length_cons, unRpnTokens_cons,
                          if_neg (by norm_num), if_pos rfl, hp]]
                      exact unreadable_trade_poison
                · by_cases ht1 : t = 1
                  · -- Constant payload chunk.
                    subst ht1
                    rw [rpnCondStep_base_one] at hmode
                    match rest with
                    | [] => exact absurd hj (by simp)
                    | c :: rest' =>
                        match j with
                        | 0 =>
                            rw [List.take_zero, List.foldl_nil, rcMode_pack]
                              at hmode
                            omega
                        | j + 1 =>
                            rw [List.take_succ_cons, List.foldl_cons,
                              rpnCondStep_fallback _ _ (by simp) (by simp)
                                (by simp) (by simp) (by simp)] at hmode
                            simp only [List.length_cons] at hj hts
                            rcases ih rest' (by omega) j (by omega) hmode with
                              ⟨j'', hj'', hm'', hd''⟩ | hun
                            · refine Or.inl ?_
                              rw [unRpn_payload_chunk 1 c (Or.inl rfl) rest']
                              have := mode2_witness_shift [1, c] (unRpn rest')
                                rfl j'' hj'' hm'' _ hd''
                              simp only [List.cons_append, List.nil_append]
                                at this
                              refine this.imp fun j' hj' => ?_
                              exact ⟨hj'.1, hj'.2.1, by
                                rw [hj'.2.2, List.getD_cons_succ,
                                  List.getD_cons_succ]⟩
                            · refine Or.inr ?_
                              rw [unRpn_payload_chunk 1 c (Or.inl rfl) rest']
                              exact Unreadable.cons_chunk (C := [1, c]) rfl hun
                  · by_cases ht7 : t = 7
                    · -- Variable payload chunk.
                      subst ht7
                      rw [rpnCondStep_base_seven] at hmode
                      match rest with
                      | [] => exact absurd hj (by simp)
                      | c :: rest' =>
                          match j with
                          | 0 =>
                              rw [List.take_zero, List.foldl_nil, rcMode_pack]
                                at hmode
                              omega
                          | j + 1 =>
                              rw [List.take_succ_cons, List.foldl_cons,
                                rpnCondStep_fallback _ _ (by simp) (by simp)
                                  (by simp) (by simp) (by simp)] at hmode
                              simp only [List.length_cons] at hj hts
                              rcases ih rest' (by omega) j (by omega) hmode with
                                ⟨j'', hj'', hm'', hd''⟩ | hun
                              · refine Or.inl ?_
                                rw [unRpn_payload_chunk 7 c (Or.inr rfl) rest']
                                have := mode2_witness_shift [7, c] (unRpn rest')
                                  rfl j'' hj'' hm'' _ hd''
                                simp only [List.cons_append, List.nil_append]
                                  at this
                                refine this.imp fun j' hj' => ?_
                                exact ⟨hj'.1, hj'.2.1, by
                                  rw [hj'.2.2, List.getD_cons_succ,
                                    List.getD_cons_succ]⟩
                              · refine Or.inr ?_
                                rw [unRpn_payload_chunk 7 c (Or.inr rfl) rest']
                                exact Unreadable.cons_chunk (C := [7, c]) rfl
                                  hun
                    · -- Bare operator/close token.
                      rw [rpnCondStep_base_other t ht0 ht1 ht6 ht7] at hmode
                      rcases ih rest (by omega) j (by omega) hmode with
                        ⟨j'', hj'', hm'', hd''⟩ | hun
                      · refine Or.inl ?_
                        rw [unRpn_single_chunk t ⟨ht0, ht1, ht6, ht7⟩ rest]
                        have := mode2_witness_shift [t] (unRpn rest)
                          (by simp [freezeMode4Step, ht0, ht1, ht6, ht7])
                          j'' hj'' hm'' _ hd''
                        simp only [List.cons_append, List.nil_append] at this
                        refine this.imp fun j' hj' => ?_
                        exact ⟨hj'.1, hj'.2.1, by
                          rw [hj'.2.2, List.getD_cons_succ]⟩
                      · refine Or.inr ?_
                        rw [unRpn_single_chunk t ⟨ht0, ht1, ht6, ht7⟩ rest]
                        exact Unreadable.cons_chunk (C := [t])
                          (by simp [freezeMode4Step, ht0, ht1, ht6, ht7]) hun

/-- **Symbol-level guard honesty**: an oversized price-day at a run-aware mode-2
position of the symbol stream forces the empty validated strategy on the
contraction.
Paper node: `thm:scon` -/
theorem strategyOfTokens_unRpn_trades_eq_nil_of_rpnBigDay (n : ℕ) (ts : List ℕ)
    (j : ℕ) (hj : j < ts.length)
    (hmode : rcMode (List.foldl rpnCondStep (rcPack 0 0 0) (ts.take j)) = 2)
    (hday : n < ts.getD j 0) :
    (strategyOfTokens n (unRpn ts)).trades = [] := by
  rcases rpn_mode2_localize ts.length ts le_rfl j hj hmode with
    ⟨j', hj', hm', hd'⟩ | hun
  · refine strategyOfTokens_trades_eq_nil_of_bigDay n (unRpn ts) j' hj' hm' ?_
    rw [hd']
    exact hday
  · have hdec := hun.deserializeTrades_eq_none
    unfold strategyOfTokens
    split
    · rfl
    · next trades hdecode =>
        rw [hdec] at hdecode
        exact absurd hdecode (by simp)

/-- The empty stream decodes to the empty validated strategy. -/
lemma strategyOfTokens_nil_trades (n : ℕ) :
    (strategyOfTokens n ([] : List ℕ)).trades = [] := by
  have hdec : deserializeTrades ([] : List ℕ) = some [] := rfl
  unfold strategyOfTokens
  split
  · rfl
  · next trades hdecode =>
      rw [hdec] at hdecode
      obtain rfl := Option.some.inj hdecode
      simp

/-- **The guarded price-pass strategy-level equality**: the contraction of the
guarded symbol-level price rewrite decodes to the retained-condition-price
translation of the contraction's strategy — on every stream, including under a
failed guard (both sides are then empty by guard honesty).
Paper node: `thm:scon` -/
theorem strategyOfTokens_rpnGuardedConditionTokens_trades
    (blocks : ℕ → List ℕ) (ψ : ℕ → Sentence)
    (hblocks : ∀ D, parseRpn (blocks D).length (blocks D) = some (ψ D, []))
    (ε : ℚ) (n : ℕ) (ts : List ℕ) :
    (strategyOfTokens n
        (unRpn (rpnGuardedConditionTokens (rpnPriceEmit blocks ε) n ts))).trades =
      (strategyOfTokens n (unRpn ts)).trades.map fun trade =>
        (trade.1.retainedConditionPrices ψ ε, trade.2) := by
  rw [rpnGuardedConditionTokens]
  split_ifs with hguard
  · rw [unRpn_rpnConditionRun blocks ψ hblocks ε ts.length ts le_rfl]
    exact strategyOfTokens_conditionPriceTokenRun_trades ψ ε n (unRpn ts)
  · push_neg at hguard
    obtain ⟨j, hj, hm, hday⟩ := hguard
    rw [unRpn_nil, strategyOfTokens_nil_trades,
      strategyOfTokens_unRpn_trades_eq_nil_of_rpnBigDay n ts j hj hm hday]
    rfl

#print axioms rpn_mode2_localize
#print axioms strategyOfTokens_unRpn_trades_eq_nil_of_rpnBigDay
#print axioms strategyOfTokens_rpnGuardedConditionTokens_trades

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
      (if (rcMode st = 4 ∨ rcMode st = 7) ∧ rcMode (rpnCondStep st t) = 0
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
          rcMode (List.foldl rpnCondStep st (ts.take k)) = 7) ∧
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
        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) init) = 7 := by
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
theorem tradeRuns_unRpn_agree : ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
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
                        show rpnCondStep (rcPack 2 0 blk.length) d = rcPack 0 0 0 from
                          rpnCondStep_fallback _ _ (by simp [rcMode, rcPack])
                            (by simp [rcMode, rcPack]) (by simp [rcMode, rcPack])
                            (by simp [rcMode, rcPack]) (by simp [rcMode, rcPack]),
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
                        show rpnCondStep (rcPack (if t = 1 then 3 else 5) 0 0) c =
                            rcPack 0 0 0 from
                          rpnCondStep_fallback _ _
                            (by split <;> simp [rcMode, rcPack])
                            (by split <;> simp [rcMode, rcPack])
                            (by split <;> simp [rcMode, rcPack])
                            (by split <;> simp [rcMode, rcPack])
                            (by split <;> simp [rcMode, rcPack]),
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
theorem rpnTradeCountAt_eq_frameTradeCount (tf tokenFn lenFn : ℕ → ℕ) (n : ℕ)
    (ts : List ℕ) (hts : vpre tf n ts.length = ts)
    (hL : vpre tokenFn n (lenFn n) = unRpn ts) :
    rpnTradeCountAt tf n ts.length = frameTradeCount tokenFn lenFn n ∨
      Unreadable (unRpn ts) := by
  rw [rpnTradeCountAt_eq_runs, hts, frameTradeCount, tradeScanNat]
  simp only [Nat.unpair_pair]
  rw [tradeScanAt_eq_runs, hL]
  exact tradeRuns_unRpn_agree ts.length ts le_rfl

#print axioms tradeRuns_unRpn_agree
#print axioms rpnTradeCountAt_eq_frameTradeCount

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
  else if (rcMode st = 4 ∨ rcMode st = 7) ∧ rcMode st' = 0 then d.pred
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
        rcMode (List.foldl rpnCondStep st (ts.take k)) = 4 ∨
        rcMode (List.foldl rpnCondStep st (ts.take k)) = 7) ∧
      ¬((rcMode (List.foldl rpnCondStep st (ts.take k)) = 4 ∨
          rcMode (List.foldl rpnCondStep st (ts.take k)) = 7) ∧
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
          rcases hm with hm | hm | hm | hm <;>
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
        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) init) = 7 := by
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
theorem depthMode_unRpn_agree : ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
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
                        rcPack 0 0 0 :=
                      rpnCondStep_fallback _ _ (by simp [rcMode, rcPack])
                        (by simp [rcMode, rcPack]) (by simp [rcMode, rcPack])
                        (by simp [rcMode, rcPack]) (by simp [rcMode, rcPack])
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
                      rpnCondStep_fallback _ _
                        (by split <;> simp [rcMode, rcPack])
                        (by split <;> simp [rcMode, rcPack])
                        (by split <;> simp [rcMode, rcPack])
                        (by split <;> simp [rcMode, rcPack])
                        (by split <;> simp [rcMode, rcPack])
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

#print axioms depthMode_unRpn_agree

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
theorem rpnStructurallyAccepts_agree (tf tokenFn lenF lenFn : ℕ → ℕ) (n : ℕ)
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
  obtain ⟨_, hA7⟩ := polyFueled_ifEq hmz 7 hexit hprev
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
              · rw [if_pos hnext, if_pos ⟨Or.inr hm7, hnext⟩]
              · rw [if_neg hnext, if_neg (by tauto)]
            · rw [if_neg hm7, if_neg (by tauto)]

#print axioms rpnStructurallyAccepts_agree
#print axioms rpnDepthScan


/-! ## The frame pass (symbol level) — emission and contraction anchor

The token-model frame transducer (`conditioningFrameTokenRun`) replaces each trade
chunk `[6, φc]` of the priced stream by a locally gated leg body
(`rawLocallyGated{Beta,Second}BodyTokens`) closing with a re-emitted trade.  At the
symbol level the trade sentence is a run; the mirror emission splices the buffered
run into the two sentence slots of the body — the conjunction block
`3 :: run ++ blockψ` at the ratio's numerator and re-emitted trade, and `blockψ` at
the denominator — leaving the gate arithmetic (constants, `letE` variables,
operators) verbatim.  The contraction anchor below is compositional, through the
prefix-contraction algebra `UnRpnContractsTo`. -/

lemma _root_.LogicalInduction.UnRpnContractsTo.of_eq {xs ys xs' ys' : List ℕ} (h : UnRpnContractsTo xs ys)
    (hx : xs = xs') (hy : ys = ys') : UnRpnContractsTo xs' ys' := hx ▸ hy ▸ h

lemma _root_.LogicalInduction.UnRpnContractsTo.single (t : ℕ) (ht : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 6 ∧ t ≠ 7) :
    UnRpnContractsTo [t] [t] :=
  (UnRpnTransparent.single t ht).contractsTo

lemma _root_.LogicalInduction.UnRpnContractsTo.payload (t c : ℕ) (ht : t = 1 ∨ t = 7) :
    UnRpnContractsTo [t, c] [t, c] :=
  (UnRpnTransparent.payload t c ht).contractsTo

/-- A price chunk with an expanded sentence block contracts to the token-model
price leaf. -/
lemma _root_.LogicalInduction.UnRpnContractsTo.priceSym {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) (day : ℕ) :
    UnRpnContractsTo (0 :: b ++ [day]) (rawPriceTokens (Encodable.encode φ) day) :=
  fun rest => by
    rw [show (0 :: b ++ [day]) ++ rest = 0 :: (b ++ day :: rest) by simp,
      unRpn_price_chunk_block hb day rest]
    rfl

/-- A trade chunk with an expanded sentence block contracts to the token-model
trade pair. -/
lemma _root_.LogicalInduction.UnRpnContractsTo.tradeSym {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) :
    UnRpnContractsTo (6 :: b) [6, Encodable.encode φ] := fun rest => by
  rw [show (6 :: b) ++ rest = 6 :: (b ++ rest) by simp,
    unRpn_trade_chunk_block hb rest]
  rfl

/-! ### The raw-combinator algebra -/

lemma _root_.LogicalInduction.UnRpnContractsTo.constTok (c : ℕ) :
    UnRpnContractsTo (rawConstTokens c) (rawConstTokens c) :=
  UnRpnContractsTo.payload 1 c (Or.inl rfl)

lemma _root_.LogicalInduction.UnRpnContractsTo.varTok (i : ℕ) : UnRpnContractsTo [7, i] [7, i] :=
  UnRpnContractsTo.payload 7 i (Or.inr rfl)

lemma _root_.LogicalInduction.UnRpnContractsTo.mulTok {a a' b b' : List ℕ}
    (ha : UnRpnContractsTo a a') (hb : UnRpnContractsTo b b') :
    UnRpnContractsTo (rawMulTokens a b) (rawMulTokens a' b') :=
  (ha.append hb).append (UnRpnContractsTo.single 3 (by norm_num))

lemma _root_.LogicalInduction.UnRpnContractsTo.addTok {a a' b b' : List ℕ}
    (ha : UnRpnContractsTo a a') (hb : UnRpnContractsTo b b') :
    UnRpnContractsTo (rawAddTokens a b) (rawAddTokens a' b') :=
  (ha.append hb).append (UnRpnContractsTo.single 2 (by norm_num))

lemma _root_.LogicalInduction.UnRpnContractsTo.maxTok {a a' b b' : List ℕ}
    (ha : UnRpnContractsTo a a') (hb : UnRpnContractsTo b b') :
    UnRpnContractsTo (rawMaxTokens a b) (rawMaxTokens a' b') :=
  (ha.append hb).append (UnRpnContractsTo.single 4 (by norm_num))

lemma _root_.LogicalInduction.UnRpnContractsTo.safeRecipTok {a a' : List ℕ} (ha : UnRpnContractsTo a a') :
    UnRpnContractsTo (rawSafeRecipTokens a) (rawSafeRecipTokens a') :=
  ha.append (UnRpnContractsTo.single 5 (by norm_num))

lemma _root_.LogicalInduction.UnRpnContractsTo.minTok {a a' b b' : List ℕ}
    (ha : UnRpnContractsTo a a') (hb : UnRpnContractsTo b b') :
    UnRpnContractsTo (rawMinTokens a b) (rawMinTokens a' b') :=
  (UnRpnContractsTo.constTok _).mulTok
    (((UnRpnContractsTo.constTok _).mulTok ha).maxTok
      ((UnRpnContractsTo.constTok _).mulTok hb))

lemma _root_.LogicalInduction.UnRpnContractsTo.absTok {a a' : List ℕ} (ha : UnRpnContractsTo a a') :
    UnRpnContractsTo (rawAbsTokens a) (rawAbsTokens a') :=
  ha.maxTok ((UnRpnContractsTo.constTok _).mulTok ha)

lemma _root_.LogicalInduction.UnRpnContractsTo.clip01Tok {a a' : List ℕ} (ha : UnRpnContractsTo a a') :
    UnRpnContractsTo (rawClip01Tokens a) (rawClip01Tokens a') :=
  (UnRpnContractsTo.constTok _).maxTok ((UnRpnContractsTo.constTok _).minTok ha)

lemma _root_.LogicalInduction.UnRpnContractsTo.gateTok {r r' m m' : List ℕ}
    (hr : UnRpnContractsTo r r') (hm : UnRpnContractsTo m m')
    (bc ibc : ℕ) :
    UnRpnContractsTo (rawConditioningGateTokens r m bc ibc)
      (rawConditioningGateTokens r' m' bc ibc) :=
  UnRpnContractsTo.clip01Tok
    ((((UnRpnContractsTo.constTok _).addTok
        ((UnRpnContractsTo.constTok bc).mulTok hm.safeRecipTok)).addTok
      ((UnRpnContractsTo.constTok _).mulTok hr)).mulTok
    ((UnRpnContractsTo.constTok ibc).mulTok ((UnRpnContractsTo.constTok _).maxTok hm)))

lemma _root_.LogicalInduction.UnRpnContractsTo.lowerSafeRecipTok {a a' : List ℕ} (ha : UnRpnContractsTo a a')
    (ε : ℚ) :
    UnRpnContractsTo (rawLowerSafeRecipTokens a ε) (rawLowerSafeRecipTokens a' ε) :=
  (UnRpnContractsTo.constTok _).mulTok
    (((UnRpnContractsTo.constTok _).mulTok ha).safeRecipTok)

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
    (UnRpnContractsTo.priceSym hconj day).mulTok
      (UnRpnContractsTo.lowerSafeRecipTok (UnRpnContractsTo.priceSym hblk day) ε)
  have hmin : UnRpnContractsTo
      (rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate bc ibc)))
      (rawMinTokens [7, 1] (rawMulTokens [7, 1] (rpnFrameGate bc ibc))) :=
    (UnRpnContractsTo.varTok 1).minTok ((UnRpnContractsTo.varTok 1).mulTok hgate)
  have hclose : UnRpnContractsTo [(8 : ℕ)] [8] :=
    UnRpnContractsTo.single 8 (by norm_num)
  cases second with
  | false =>
      have htail : UnRpnContractsTo (6 :: (3 :: buf ++ blk))
          [6, Encodable.encode (φ ⋏ ψn)] := UnRpnContractsTo.tradeSym hconj
      have hcomp := (((hratio.append hmin).append hclose).append
        (hclose.append htail))
      refine hcomp.of_eq ?_ ?_
      · simp [rpnFrameEmit]
      · simp [rawLocallyGatedBetaBodyTokens, rawConditioningRatioTokens,
          rpnFrameGate, conjunctionCode_exact]
  | true =>
      have htail : UnRpnContractsTo (6 :: blk) [6, Encodable.encode ψn] :=
        UnRpnContractsTo.tradeSym hblk
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

#print axioms rpnFrameEmit_contractsTo

/-! ### The frame run (streaming, exit-triggered) -/

/-- Tokens emitted at one source position of the frame pass. -/
def rpnFrameEmitAt (second : Bool) (blk : List ℕ) (ε : ℚ) (day bc ibc : ℕ)
    (st : ℕ) (buf : List ℕ) (t : ℕ) : List ℕ :=
  if rcMode st = 0 ∧ t = 6 then []
  else if rcMode st = 4 ∨ rcMode st = 7 then
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

lemma rpnFrameEmitAt_base_other (second : Bool) (blk : List ℕ) (ε : ℚ)
    (day bc ibc : ℕ) (buf : List ℕ) (t : ℕ) (ht : t ≠ 6) :
    rpnFrameEmitAt second blk ε day bc ibc (rcPack 0 0 0) buf t = [t] := by
  simp [rpnFrameEmitAt, ht]

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
      rcMode (List.foldl rpnCondStep st (ts.take k)) ≠ 7) :
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
lemma rcLen_trade_run_step (st t : ℕ) (hm : rcMode st = 4 ∨ rcMode st = 7)
    (hne : rcMode (rpnCondStep st t) ≠ 0) :
    rcLen (rpnCondStep st t) = rcLen st + 1 := by
  rw [rcMode_step_eq] at hne
  rw [rcLen_step_eq]
  rcases hm with hm | hm <;>
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
        rcMode (List.foldl rpnCondStep st (ts.take k)) = 7) ∧
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
        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) init) = 7 := by
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
      rw [rpnFrameEmitAt, if_neg (by rcases hmodeInit with h | h <;> simp [h]),
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
        rcMode (rpnFrameRun second blk ε day bc ibc (rcPack 0 0 0, []) ts).1.1 = 7
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

/-! ### Token-model frame run equations (per contracted chunk) -/

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

lemma conditioningFrameTokenOutput_nil :
    conditioningFrameTokenOutput second ψCode day ε bc ibc [] = [] := by
  simp [conditioningFrameTokenOutput, conditioningFrameTokenRun]

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

lemma conditioningFrameTokenOutput_trade_flush :
    conditioningFrameTokenOutput second ψCode day ε bc ibc [6] = [6] := by
  simp [conditioningFrameTokenOutput, conditioningFrameTokenRun,
    conditioningFrameTokenEmit, EF.freezeTokenNext]

end FrameTokenRunEq

/-- Price-run instance of the inside invariant (for streams that never exit). -/
lemma priceWalk_inside (v : List ℕ) (j : ℕ) (hj : j ≤ v.length)
    (hmods : ∀ i, i ≤ j →
      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (v.take i)) ≠ 2) :
    (rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (v.take j)) = 1 ∨
      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) (v.take j)) = 6) ∧
    1 ≤ rcCnt (List.foldl rpnCondStep (rcPack 1 1 0) (v.take j)) ∧
    rcLen (List.foldl rpnCondStep (rcPack 1 1 0) (v.take j)) = j :=
  runWalk_inside (b := 6) (exit := fun r' => rcPack 2 0 r')
    (fun c r t => rpnCondStep_price c r t)
    (fun c r t => rpnCondStep_priceEsc c r t)
    2 (fun r' => rcMode_pack 2 0 r') v j hj hmods

/-! ### Splitting the contraction at a chunk boundary

The two-leg join concatenates two symbol-level frame outputs, and `unRpn` does **not**
distribute over an append when the left factor carries a poisoned chunk.  It does
split, though, on any stream the run automaton walks back to base mode: either the
stream is `UnRpnContractsTo`-transparent ahead of every continuation, or its first poisoned
chunk stops the contraction outright.  Same chunk induction as
`tradeRuns_unRpn_agree`, with the first-exit localization supplying the
poisons-every-extension branch. -/

/-- A stream that contracts to *something* ahead of any continuation contracts to its
own contraction. -/
lemma _root_.LogicalInduction.UnRpnContractsTo.self {A X : List ℕ} (h : UnRpnContractsTo A X) :
    UnRpnContractsTo A (unRpn A) := by
  have hX : unRpn A = X := by
    have h0 := h []
    rwa [List.append_nil, unRpn_nil, List.append_nil] at h0
  rw [hX]; exact h

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
theorem unRpn_split : ∀ (N : ℕ) (A : List ℕ), A.length ≤ N →
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
                        rcPack 0 0 0 :=
                      rpnCondStep_fallback _ _ (by simp [rcMode, rcPack])
                        (by simp [rcMode, rcPack]) (by simp [rcMode, rcPack])
                        (by simp [rcMode, rcPack]) (by simp [rcMode, rcPack])
                    have hbase2 : List.foldl rpnCondStep (rcPack 0 0 0) r2 =
                        rcPack 0 0 0 := by
                      rw [List.foldl_cons, rpnCondStep_base_price,
                        List.foldl_append, hwalk, List.foldl_cons, hstD] at hbase
                      exact hbase
                    have hA2 : (0 : ℕ) :: (blk ++ d0 :: r2) =
                        (0 :: blk ++ [d0]) ++ r2 := by simp
                    have hC := UnRpnContractsTo.priceSym hblk d0
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
                  have hC := UnRpnContractsTo.tradeSym hblk
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
                      rpnCondStep_fallback _ _
                        (by split <;> simp [rcMode, rcPack])
                        (by split <;> simp [rcMode, rcPack])
                        (by split <;> simp [rcMode, rcPack])
                        (by split <;> simp [rcMode, rcPack])
                        (by split <;> simp [rcMode, rcPack])
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

#print axioms unRpn_split

/-! ### Both-poison agreement -/

/-- Outputs agree up to a common unreadable failure. -/
def FrameAgree (a b : List ℕ) : Prop :=
  a = b ∨ (Unreadable a ∧ Unreadable b)

lemma FrameAgree.of_eq {a b : List ℕ} (h : a = b) : FrameAgree a b := Or.inl h

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

lemma FrameAgree.of_eq_append {C a b x y : List ℕ}
    (hC : List.foldl freezeMode4Step 0 C = 0) (h : FrameAgree a b)
    (hx : x = C ++ a) (hy : y = C ++ b) : FrameAgree x y := by
  rw [hx, hy]; exact h.cons_chunk hC

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
needs — `FrameAgree` alone does not survive an append. -/
def FrameContract (A B : List ℕ) : Prop :=
  UnRpnContractsTo A B ∨ (UnRpnStops A ∧ Unreadable (unRpn A) ∧ Unreadable B)

lemma _root_.LogicalInduction.UnRpnContractsTo.nil : UnRpnContractsTo [] [] := fun rest => by simp

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

lemma _root_.LogicalInduction.UnRpnContractsTo.frameAgree_chunk {C P A B : List ℕ} (hC : UnRpnContractsTo C P)
    (hF : List.foldl freezeMode4Step 0 P = 0) (h : FrameAgree (unRpn A) B) :
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
set_option maxHeartbeats 1000000 in
/-- A price-run mode step never returns to base and never enters a trade run. -/
lemma rcModeF_price_ne {m c t : ℕ} (h : m = 1 ∨ m = 6) :
    rcModeF m c t ≠ 0 ∧ rcModeF m c t ≠ 4 ∧ rcModeF m c t ≠ 7 := by
  rcases h with rfl | rfl <;> rw [rcModeF] <;> split_ifs <;>
    first
      | exact absurd ‹False› not_false
      | refine ⟨by omega, by omega, by omega⟩

/-- Inside a price run the automaton stays in the run or reaches the day slot; it never
returns to base and never enters a trade run. -/
lemma rcMode_step_of_price_run {st t : ℕ} (h : rcMode st = 1 ∨ rcMode st = 6) :
    rcMode (rpnCondStep st t) ≠ 0 ∧ rcMode (rpnCondStep st t) ≠ 4 ∧
      rcMode (rpnCondStep st t) ≠ 7 := by
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
theorem frameJoint_unRpn_rpnFrameOutput (second : Bool) (blkψ : List ℕ)
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
                        rcPack 0 0 0 :=
                      rpnCondStep_fallback _ _ (by simp) (by simp) (by simp)
                        (by simp) (by simp)
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
                      (UnRpnContractsTo.priceSym hblk d).of_eq (by simp)
                        (by simp [rawPriceTokens])
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
                        (rest.take k)) ≠ 7 := by
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
                      rcMode (List.foldl rpnCondStep (rcPack 1 1 0) rest) ≠ 7 := by
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
                    simp [rpnFrameEmitAt, hmodeEnd.2.1, hmodeEnd.2.2]
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
                          rcMode (List.foldl rpnCondStep (rcPack 4 1 0) u') = 7 := by
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
                          if_neg (by rcases hmodeU' with h | h <;> simp [h]),
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
                        simp only [rpnFrameRun_nil, List.nil_append, List.append_assoc, hstepLast, hcat]
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
                          (rest.take k)) = 7) ∧
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
                        rcMode (List.foldl rpnCondStep (rcPack 4 1 0) rest) = 7 := by
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
                      rpnCondStep_fallback _ _ (by simp) (by simp) (by simp)
                        (by simp) (by simp)
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
                        rpnCondStep_fallback _ _ (by simp) (by simp) (by simp)
                          (by simp) (by simp)
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
theorem frameAgree_unRpn_rpnFrameOutput (second : Bool) (blkψ : List ℕ)
    {ψn : Sentence} (hblkψ : parseRpn blkψ.length blkψ = some (ψn, []))
    (ε : ℚ) (day bc ibc : ℕ) (ts : List ℕ) :
    FrameAgree (unRpn (rpnFrameOutput second blkψ ε day bc ibc ts))
      (conditioningFrameTokenOutput second (Encodable.encode ψn) day ε bc ibc
        (unRpn ts)) :=
  (frameJoint_unRpn_rpnFrameOutput second blkψ hblkψ ε day bc ibc ts.length ts
    le_rfl).1

/-- **The frame pass contracts as a prefix** whenever the source stream returns the run
automaton to base mode — the condition the acceptance gate tests.  This is the
primitive the two-leg join consumes: `FrameAgree` alone does not survive an append.
Paper node: `thm:scon` -/
theorem frameContract_rpnFrameOutput (second : Bool) (blkψ : List ℕ)
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
theorem strategyOfTokens_unRpn_rpnFrameOutput_trades (second : Bool) (blkψ : List ℕ)
    {ψn : Sentence} (hblkψ : parseRpn blkψ.length blkψ = some (ψn, []))
    (ε : ℚ) (day bc ibc : ℕ) (n : ℕ) (ts : List ℕ) :
    (strategyOfTokens n
        (unRpn (rpnFrameOutput second blkψ ε day bc ibc ts))).trades =
      (strategyOfTokens n (conditioningFrameTokenOutput second
        (Encodable.encode ψn) day ε bc ibc (unRpn ts))).trades :=
  (frameAgree_unRpn_rpnFrameOutput second blkψ hblkψ ε day bc ibc
    ts).strategyOfTokens_trades_eq n

#print axioms frameJoint_unRpn_rpnFrameOutput
#print axioms frameAgree_unRpn_rpnFrameOutput
#print axioms frameContract_rpnFrameOutput
#print axioms strategyOfTokens_unRpn_rpnFrameOutput_trades

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
          rcMode (rpnCondControlAt tf n j) = 7 then
        (if rcMode (rpnCondControlAt tf n (j + 1)) = 0 then
          rpnFrameEmit second blkψ ε day bc ibc
            (rpnCondWindow tf n j ++ [tf (Nat.pair n j)])
        else [])
      else [tf (Nat.pair n j)] := by
  rw [rpnFrameSegment]
  simp only [Nat.unpair_pair, rpnFrameEmitAt]
  rfl

#print axioms rpnFrameRun_range
#print axioms rpnFrameSegment_eq

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
`PolySegStream` is a `PolySegStream`, over any polynomially emittable condition block
stream and poly-fueled day/budget codes.
Paper node: `thm:scon` -/
lemma rpnFrameOutput_polySegStream (second : Bool) {src blocks : ℕ → List ℕ}
    (hsrc : PolySegStream src) (hblocks : PolySegStream blocks)
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
        (ibcF z.unpair.1) (rpnCondWindow tf z.unpair.1 z.unpair.2 ++ [tf (Nat.pair z.unpair.1 z.unpair.2)]))) := by
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
  have hseg7 := hExit.ifZero hcopy heq7
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
  have hblock6 : PolySegStream (fun _ : ℕ => tokenBlock 6) :=
    PolySegStream.block (PolyFueled.const 6)
  have hflush := hblock6.ifZero (hblock6.ifZero hempty heq7End) heq4End
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
        · rw [if_pos (by omega), if_pos (Or.inr hm7)]
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
      · rw [if_pos (by omega), if_pos (Or.inr hm7)]
        simp [digitize]
      · rw [if_neg (by omega), if_neg (by tauto)]
        simp [digitize]

#print axioms rpnFrameOutput_polySegStream


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
    (hsrc : PolySegStream src) (hblocks : PolySegStream blocks)
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

#print axioms rpnAcceptScan
#print axioms rpnSafeSeparatedFrameOutput_polySegStream

/-- **The gated two-leg join agrees with the token model**: the contraction of the
symbol-level gated join decodes to the same validated strategy as the token-model
gated join of the contraction.
Paper node: `thm:scon` -/
theorem strategyOfTokens_unRpn_rpnSafeSeparatedFrameOutput_trades
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

#print axioms strategyOfTokens_unRpn_rpnSafeSeparatedFrameOutput_trades

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
theorem unRpn_rpnZeroAwareConditionRun (zeroDays : Finset ℕ) (blocks : ℕ → List ℕ)
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
      try simp only []
      rw [zeroAwareConditionPriceTokenRun_price])
    (fun fc => zeroAwareConditionPriceTokenRun_price_pair zeroDays _ ε fc)
    (fun fc L => zeroAwareConditionPriceTokenRun_trade zeroDays _ ε fc L)
    (fun b φ hb D rest => by
      try simp only []
      rw [rpnZeroAwareEmit]
      by_cases hD : D ∈ zeroDays
      · rw [if_pos hD, unRpn_zero_rewrite_chunk hb D rest, if_pos hD]
        simp
      · rw [if_neg hD, unRpn_price_rewrite_chunk hb (hblocks D) D ε rest, if_neg hD]
        simp [List.append_assoc])

/-- **The zero-aware guarded price-pass strategy-level equality.**
Paper node: `thm:scon` -/
theorem strategyOfTokens_rpnGuardedZeroAwareConditionTokens_trades
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
    {s blocks : ℕ → List ℕ} (h : PolySegStream s) (hb : PolySegStream blocks)
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


#print axioms unRpn_rpnZeroAwareConditionRun
#print axioms rpnGuardedZeroAwareConditionRun_polySegStream

/-! ### The class-preservation endpoints

The assembly: the source certificate gives the clocked digit stream of the RPN-expanded
strategy serialization; the guarded price pass rewrites its price days
(`rpnGuardedConditionRun_polySegStream` for emission,
`strategyOfTokens_rpnGuardedConditionTokens_trades` for agreement); the gated frame
join splices the two conditional legs (`rpnSafeSeparatedFrameOutput_polySegStream`,
`strategyOfTokens_unRpn_rpnSafeSeparatedFrameOutput_trades`); the budget codes are set
by the symbol-level trade-run count, exact against the token model
(`rpnTradeCountAt_eq_frameTradeCount`); and `ec_of_rawSegStream` digitizes back into a
`def:ec` certificate. -/

/-- **The gated conditioning translation preserves symbol-metered efficient
computability** (`def:ec` → `def:ec`), over any `𝓔𝓒` sentence sequence.
Paper node: `thm:scon` -/
theorem conditionedTranslation_preserves_ecRpn
    (ψ : ℕ → Sentence) (hψ : RpnSentenceCodes ψ) (ε : ℚ)
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
  -- Abbreviations for the contracted priced stream.
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
      rpnSafeSeparatedFrameOutput tfP lenP (blocks n) ε n
        (Encodable.encode q) (Encodable.encode q⁻¹) ts := by
    show undigitize (digitize _) = _
    rw [undigitize_digitize, frameBudgetCode_exact, frameInverseBudgetCode_exact]
  rw [hundig]
  have hjoin := strategyOfTokens_unRpn_rpnSafeSeparatedFrameOutput_trades
    tfP tokP lenP lenT (blocks n) (hblocksParse n) ε q n ts hvts hvL
  refine strategy_ext_trades ?_
  rw [hjoin]
  -- The price pass: the contraction of the priced stream is the token-model rewrite.
  have horig : strategyOfTokens n (unRpn (undigitize (source n))) = T.strat n :=
    congrFun (congrArg Trader.strat hcert) n
  have hprice : (strategyOfTokens n (unRpn ts)).trades =
      (T.strat n).trades.map fun trade =>
        (trade.1.retainedConditionPrices ψ ε, trade.2) := by
    have hraw : ts =
        rpnGuardedConditionTokens (rpnPriceEmit blocks ε) n (undigitize (source n)) := by
      rw [hts]
      exact undigitize_digitize _
    rw [hraw, strategyOfTokens_rpnGuardedConditionTokens_trades blocks ψ
      hblocksParse ε n (undigitize (source n)), horig]
  have hframes := strategyOfTokens_safeSeparatedFrameTokenOutput_trades
    tokP lenT (ψ n) ε q n (unRpn ts) hvL.symm
  rw [hframes]
  by_cases hempty : (T.strat n).trades = []
  · rw [hprice, hempty]
    simp [Trader.conditionedTranslation,
      Strategy.separatedLocallyGatedConditionalContract]
    exact hempty
  · have hpricedNe : (strategyOfTokens n (unRpn ts)).trades ≠ [] := by
      rw [hprice]
      simpa using hempty
    have hdecodePriced :=
      deserializeTrades_eq_some_of_strategyOfTokens_trades_ne_nil
        n (unRpn ts) hpricedNe
    have hreadyPriced := streamReadFrom_eq_ready_of_deserializeTrades_eq_some
      (unRpn ts) (strategyOfTokens n (unRpn ts)).trades hdecodePriced
    have hreadyTokens :
        EF.streamReadFrom ((List.range (lenT n)).map fun i => tokP (Nat.pair n i))
            (some EF.streamInitial) =
          some ((0, none), ([], (strategyOfTokens n (unRpn ts)).trades)) := by
      rw [show ((List.range (lenT n)).map fun i => tokP (Nat.pair n i)) =
        unRpn ts from hvL]
      exact hreadyPriced
    have hcountTok : frameTradeCount tokP lenT n = (T.strat n).trades.length := by
      calc
        frameTradeCount tokP lenT n =
            (strategyOfTokens n (unRpn ts)).trades.length :=
          frameTradeCount_eq_length_of_read tokP lenT n
            ((0, none), ([], (strategyOfTokens n (unRpn ts)).trades)) hreadyTokens
        _ = (T.strat n).trades.length := by rw [hprice, List.length_map]
    -- the symbol-side trade-run count is exact against the token-side count
    have hnotUnread : ¬ Unreadable (unRpn ts) := by
      intro hU
      rw [hU.deserializeTrades_eq_none] at hdecodePriced
      simp at hdecodePriced
    have hcountSym : rpnTradeCountAt tfP n (lenP n) = frameTradeCount tokP lenT n := by
      have hlenEq : ts.length = lenP n := rfl
      have := rpnTradeCountAt_eq_frameTradeCount tfP tokP lenT n ts
        (by rw [hlenEq]; exact hvts) hvL
      rcases this with h | hU
      · rw [← h, hlenEq]
      · exact absurd hU hnotUnread
    have hpos : 0 < (T.strat n).trades.length := List.length_pos_iff.mpr hempty
    rw [hprice, hq, hcountSym, hcountTok,
      frameBudget_eq n (T.strat n).trades.length hpos]
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

#print axioms conditionedTranslation_preserves_ecRpn

/-- **The eventual (finite-zero, launch-gated) conditioning translation preserves
symbol-metered efficient computability** (`def:ec` → `def:ec`).
Paper node: `thm:scon` -/
theorem eventualConditionedTranslation_preserves_ecRpn
    {P : History} {ψ : ℕ → Sentence}
    (F : EventualConditioningFloor P ψ) (hψ : RpnSentenceCodes ψ)
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
    refine strategy_ext_trades ?_
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
    · have hpricedNe : (strategyOfTokens n (unRpn ts)).trades ≠ [] := by
        rw [hprice]
        simpa using hempty
      have hdecodePriced :=
        deserializeTrades_eq_some_of_strategyOfTokens_trades_ne_nil
          n (unRpn ts) hpricedNe
      have hreadyPriced := streamReadFrom_eq_ready_of_deserializeTrades_eq_some
        (unRpn ts) (strategyOfTokens n (unRpn ts)).trades hdecodePriced
      have hreadyTokens :
          EF.streamReadFrom ((List.range (lenT n)).map fun i => tokP (Nat.pair n i))
              (some EF.streamInitial) =
            some ((0, none), ([], (strategyOfTokens n (unRpn ts)).trades)) := by
        rw [show ((List.range (lenT n)).map fun i => tokP (Nat.pair n i)) =
          unRpn ts from hvL]
        exact hreadyPriced
      have hcountTok : frameTradeCount tokP lenT n = (T.strat n).trades.length := by
        calc
          frameTradeCount tokP lenT n =
              (strategyOfTokens n (unRpn ts)).trades.length :=
            frameTradeCount_eq_length_of_read tokP lenT n
              ((0, none), ([], (strategyOfTokens n (unRpn ts)).trades)) hreadyTokens
          _ = (T.strat n).trades.length := by rw [hprice, List.length_map]
      have hnotUnread : ¬ Unreadable (unRpn ts) := by
        intro hU
        rw [hU.deserializeTrades_eq_none] at hdecodePriced
        simp at hdecodePriced
      have hcountSym :
          rpnTradeCountAt tfP n (lenP n) = frameTradeCount tokP lenT n := by
        have hlenEq : ts.length = lenP n := rfl
        have := rpnTradeCountAt_eq_frameTradeCount tfP tokP lenT n ts
          (by rw [hlenEq]; exact hvts) hvL
        rcases this with h | hU
        · rw [← h, hlenEq]
        · exact absurd hU hnotUnread
      have hpos : 0 < (T.strat n).trades.length := List.length_pos_iff.mpr hempty
      rw [hprice, hq, hcountSym, hcountTok,
        frameBudget_eq n (T.strat n).trades.length hpos]
      simp only [List.map_map]
      change
        ((T.strat n).trades.map fun p =>
          frameLeg false (ψ n) F.epsilon
            (Strategy.localConditioningBudget (conditioningBudget n)
              (T.strat n).trades.length) n
            (p.1.retainedConditionPricesExceptZero F.zeroDays ψ F.epsilon, p.2)) ++
          ((T.strat n).trades.map fun p =>
            frameLeg true (ψ n) F.epsilon
              (Strategy.localConditioningBudget (conditioningBudget n)
                (T.strat n).trades.length) n
              (p.1.retainedConditionPricesExceptZero F.zeroDays ψ F.epsilon, p.2)) =
          ((T.strat n).separatedExceptZeroConditionalContract
            F.zeroDays ψ F.epsilon (conditioningBudget n)).trades
      simp only [frameLeg_exceptZero_eq_locallyGatedFirstLeg,
        frameLeg_exceptZero_eq_locallyGatedSecondLeg]
      rfl

#print axioms eventualConditionedTranslation_preserves_ecRpn

end RpnConditioning

namespace ConditioningCompile

open RpnConditioning

/-! ## `thm:scon` packaging: operational witnesses and the paper-facing endpoints

The two symbol-metered translation certificates discharge the operational witness
structures of `Properties/Conditioning.lean`, closing the criterion level: conditioning a
logical inductor on a computable presentation yields a logical inductor of the
conditioned market. -/

/-! ### Public operational witness constructors -/

/-- Construct the complete prefix-safe operational witness from an exact rational market
and a finite-zero floor certificate.
Paper node: `thm:scon` -/
noncomputable def eventualConditioningOperationalWitness
    {P : History} {DP extra : DeductiveProcess}
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (floor : EventualConditioningFloor P C.condition) :
    EventualConditioningOperationalWitness P DP extra C where
  floor := floor
  conditioned_computable :=
    (conditionedMarketComputation market C.condition C.condition_codes).toComputable
  translation_ec := fun T hT =>
    eventualConditionedTranslation_preserves_ecRpn floor
      C.condition_codes T hT

/-- Construct the complete gated-conditioning operational witness from a named rational
base-market computation and an actual positive denominator floor.
Paper node: `thm:scon` -/
noncomputable def gatedConditioningOperationalWitness
    {P : History} {DP extra : DeductiveProcess}
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (ε : ℚ) (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d, (ε : ℝ) ≤ P d (C.condition d)) :
    GatedConditioningOperationalWitness P DP extra C ε where
  epsilon_pos := hε
  denominator_floor := hfloor
  conditioned_computable :=
    (conditionedMarketComputation market C.condition C.condition_codes).toComputable
  translation_ec := fun T hT =>
    conditionedTranslation_preserves_ecRpn C.condition
      C.condition_codes ε T hT

/-- The paper's finite-prefix denominator repair supplies the floor and the exact rational
market computation required by the operational witness.  Transporting logical induction
from `P` to the patched history is a separate step, behind the qualified
finite-perturbation theorem and its two `EfficientPrefixPatch` certificates.
Paper node: `thm:scon` -/
noncomputable def denominatorPatchedGatedConditioningOperationalWitness
    {P : History} {DP extra : DeductiveProcess}
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (cutoff : ℕ) (ε : ℚ) (hε : 0 < (ε : ℝ)) (hεone : (ε : ℝ) ≤ 1)
    (htail : ∀ day, cutoff ≤ day → (ε : ℝ) ≤ P day (C.condition day)) :
    GatedConditioningOperationalWitness
      (denominatorPatchedHistory P C.condition cutoff) DP extra C ε :=
  gatedConditioningOperationalWitness C
    (denominatorPatchedMarketComputation market C.condition C.condition_codes cutoff)
    ε hε (denominatorPatchedHistory_floor P C.condition cutoff hεone htail)

/-! ### The paper-facing `thm:scon` endpoints -/

/-- Closure under conditioning through the concrete gated translator.
Paper node: `thm:scon` -/
theorem lic_conditioned_gated_ofMarketComputation
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (ε : ℚ) (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d, (ε : ℝ) ≤ P d (C.condition d)) :
    IsLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  LogicalInduction.lic_conditioned_gated P DP extra C
    (gatedConditioningOperationalWitness C market ε hε hfloor)

/-- Closure under conditioning through the prefix-safe finite-zero compiler.  This does
not modify the base history and therefore does not depend on unrestricted
finite-perturbation closure.
Paper node: `thm:scon` -/
theorem lic_conditioned_eventualOfFloor
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (floor : EventualConditioningFloor P C.condition) :
    IsLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  LogicalInduction.lic_conditioned_eventual P DP extra C
    (eventualConditioningOperationalWitness C market floor)

/-- Closure under conditioning from joint consistency of the base stages with the whole
condition sequence, plus concrete computability data.  The proof stays on the original
market: the finite exceptional prefix is handled by the zero-aware compiler.

`hjoint` is **repo-side**, not a premise of the paper's `thm:scon`; it is what the analytic
price-floor argument consumes, and it confines this constructor to the
consistent-conditioning case.  The degenerate case (some stage of the union process has no
propositionally consistent world) is handled separately by
`isLogicalInductor_of_stage_unsatisfiable`.
Paper node: `thm:scon` -/
theorem lic_conditioned_eventual_ofMarketComputation
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (C.condition i)) :
    IsLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  lic_conditioned_eventualOfFloor P DP extra C market
    (eventualConditioningFloorOfJointConsistency
      P DP market C.condition C.condition_codes hjoint)

/-- Fixed-sentence form of Closure Under Conditioning, with **no** consistency hypothesis —
the paper's `thm:scon` statement exactly.  The two branches are the paper's two cases: where
`Θ ∪ {ψ}` stays satisfiable at every stage the analytic price-floor argument runs, and where
some stage of `Θ ∪ {ψ}` is already unsatisfiable the criterion holds vacuously (no plausible
world remains to assess a trader's net worth, so nothing exploits — the paper's remark that
conditional prices go to `1` where the denominator vanishes).
Kind `C` (composition of the two branches); hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_fixed_ofComputationAndMarket
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (base : DeductiveProcessComputation DP) (market : MarketComputation P)
    (ψ : Sentence) :
    IsLogicalInductor
      (conditionedHistory P (fun _ => ψ)) (DP.adjoinSentence ψ) := by
  let C := fixedConditioningPresentation base ψ
  by_cases hjoint : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds ψ
  · have hjointC : ∀ n, ∃ v : PCWorld,
        v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (C.condition i) := by
      intro n
      obtain ⟨v, hv, hψ⟩ := hjoint n
      exact ⟨v, hv, fun _ => hψ⟩
    have hresult :=
      lic_conditioned_eventual_ofMarketComputation
        P DP (fixedConditionProcess ψ) C market hjointC
    simpa [C, fixedConditioningPresentation,
      DeductiveProcess.adjoinSentence] using hresult
  · push_neg at hjoint
    obtain ⟨N, hN⟩ := hjoint
    refine isLogicalInductor_of_stage_unsatisfiable _ _
      ((conditionedMarketComputation market (fun _ => ψ)
        (C.condition_codes)).toComputable)
      C.combined_computable (N := N) ?_
    intro v hv
    rw [DeductiveProcess.adjoinSentence,
      PCWorld.consistentWith_union_iff] at hv
    exact hN v hv.1 (hv.2 ψ (by simp [fixedConditionProcess]))

/-- Growing finite-prefix form of Closure Under Conditioning, with **no** consistency
hypothesis — the paper's `thm:scon` statement exactly.  As in the fixed-sentence form, the
two branches are the paper's two cases.  Where every finite stage of `Θ ∪ {ψ₁…ψₙ}` is
satisfiable, propositional compactness (`DeductiveProcess.exists_consistentWithTheory`)
produces a *single* world consistent with the whole growing theory, which is exactly what
the analytic price-floor argument consumes.  Where some stage is already unsatisfiable the
criterion holds vacuously.
Kind `C` (composition of the two branches); hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_growing_ofComputationsAndMarket
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (base : DeductiveProcessComputation DP)
    (more : CompactConditioningProcessComputation extra)
    (market : MarketComputation P) :
    IsLogicalInductor
      (conditionedHistory P
        (fun n => deductiveStageCondition (extra.D n)))
      (DP.union extra) := by
  let C := conditioningPresentationOfComputations base more
  by_cases hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union extra).D n)
  · obtain ⟨w, hw⟩ := (DP.union extra).exists_consistentWithTheory hsat
    have hjointC : ∀ n, ∃ v : PCWorld,
        v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (C.condition i) := by
      intro n
      refine ⟨w, ((PCWorld.consistentWith_union_iff w DP extra n).mp (hw n)).1, fun i => ?_⟩
      exact (C.holds_condition i w).2
        ((PCWorld.consistentWith_union_iff w DP extra i).mp (hw i)).2
    exact lic_conditioned_eventual_ofMarketComputation
      P DP extra C market hjointC
  · push_neg at hsat
    obtain ⟨N, hN⟩ := hsat
    exact isLogicalInductor_of_stage_unsatisfiable _ _
      ((conditionedMarketComputation market C.condition
        C.condition_codes).toComputable)
      C.combined_computable (N := N) hN

/-- Paper-facing SCON constructor: the canonical finite-stage presentation and the complete
market/trader compiler are both assembled from their named computations.
Paper node: `thm:scon` -/
theorem lic_conditioned_gated_ofComputationsAndMarket
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (base : DeductiveProcessComputation DP)
    (more : CompactConditioningProcessComputation extra)
    (market : MarketComputation P) (ε : ℚ) (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d, (ε : ℝ) ≤
      P d (deductiveStageCondition (extra.D d))) :
    IsLogicalInductor
      (conditionedHistory P (fun n => deductiveStageCondition (extra.D n)))
      (DP.union extra) :=
  lic_conditioned_gated_ofMarketComputation P DP extra
    (conditioningPresentationOfComputations base more) market ε hε hfloor

#print axioms eventualConditioningOperationalWitness
#print axioms gatedConditioningOperationalWitness
#print axioms denominatorPatchedGatedConditioningOperationalWitness
#print axioms lic_conditioned_gated_ofMarketComputation
#print axioms lic_conditioned_eventualOfFloor
#print axioms lic_conditioned_eventual_ofMarketComputation
#print axioms lic_conditioned_fixed_ofComputationAndMarket
#print axioms lic_conditioned_growing_ofComputationsAndMarket
#print axioms lic_conditioned_gated_ofComputationsAndMarket

end ConditioningCompile


end LogicalInduction
