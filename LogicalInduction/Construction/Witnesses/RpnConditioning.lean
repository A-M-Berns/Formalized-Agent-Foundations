/-
# Symbol-level conditioning translation compiler (RPN-5, part 1)

The digit-model conditioning compiler (`DigitConditioning.lean`) rewrites price chunks
of the *contracted* strategy stream, so its source certificates are digit-metered
(`EfficientlyComputableTok₂`).  The collapsed class `EfficientlyComputable` meters the
RPN-expanded stream, where sentence slots are symbol **runs**; the price rewrite must
walk the flat grammar with a run-aware automaton (pending-counter scan) and splice the
condition sentence as a *block* (conjunction = concatenation:
`rpn (φ ⋏ ψ) = 3 :: rpn φ ++ rpn ψ`).

This file provides the spec layer of that compiler:

* the run-aware mode automaton `rpnCondStep` (packed state `⟨mode, counter, runLen⟩`),
  its clamp/bounds lemmas, and the **run–parse correspondence**: over any block that
  `parseRpn` consumes completely, the automaton walks the run and exits exactly at the
  block boundary;
* the price rewrite `rpnConditionRun` — a streaming transducer that copies every input
  token and, at each price-day position, appends the RPN expansion of the conditional
  price expression (the buffered sentence run re-spliced into the conjunction shell,
  the condition block drawn from an `RpnSentenceCodes` stream) plus the letE close, so
  the contraction of the output is exactly the token-model rewrite
  (`conditionPriceTokenRun`) of the contraction of the input;
* the per-chunk contraction identity `unRpn_price_rewrite_chunk` anchoring that claim;
* the poly-fueled side: the packed control scan (`rpnCondScan`), the day-guard flag
  scan, and the emission certificate `rpnGuardedConditionRun_polySegStream` — the
  digitized guarded rewrite of any digit `PolySegStream` is a `PolySegStream`.

The class-preservation endpoints are stated at the end and remain open
(`TODO(blueprint:thm:scon)`): whole-stream contraction exactness, guard-honesty
transfer, and the frame-pass mirror.

Paper node: `thm:scon` (symbol-metered conditioning translation).
-/
import LogicalInduction.Construction.Witnesses.DigitConditioning
import LogicalInduction.Framework.RpnEmission

namespace LogicalInduction

namespace RpnConditioning

open Nat.Partrec (Code)
open Nat.Partrec.Code
open ConditioningCompile

-- Deep `Primrec`/`PolyFueled` compositions over paired inputs loop `whnf` on `Nat.sqrt`
-- (pair/unpair unfolding); keep it opaque throughout (the standard `dd:fuel` safeguard).
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
    simp only [e0, e1, e234, e6, e7, if_false, ite_false,
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
                      simp only [Option.bind_some, Option.map_some,
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

/-- Streaming buffer update: reset whenever the automaton leaves (or is outside) a
sentence run, extend inside one — the buffer is exactly the current run. -/
def rpnCondBuf (st : ℕ) (buf : List ℕ) (t : ℕ) : List ℕ :=
  if rcLen (rpnCondStep st t) = 0 then [] else buf ++ [t]

/-- The streaming price rewrite: state, run buffer, and emitted output. -/
def rpnConditionRun (blocks : ℕ → List ℕ) (ε : ℚ) :
    ℕ × List ℕ → List ℕ → (ℕ × List ℕ) × List ℕ
  | s, [] => (s, [])
  | (st, buf), t :: ts =>
      let rest := rpnConditionRun blocks ε
        (rpnCondStep st t, rpnCondBuf st buf t) ts
      (rest.1,
        (if rcMode st = 2 then rpnConditionEmit (blocks t) ε buf t else [t])
          ++ rest.2)

@[simp] lemma rpnConditionRun_nil (blocks : ℕ → List ℕ) (ε : ℚ) (s : ℕ × List ℕ) :
    rpnConditionRun blocks ε s [] = (s, []) := rfl

lemma rpnConditionRun_append (blocks : ℕ → List ℕ) (ε : ℚ)
    (s : ℕ × List ℕ) (xs ys : List ℕ) :
    rpnConditionRun blocks ε s (xs ++ ys) =
      let first := rpnConditionRun blocks ε s xs
      let second := rpnConditionRun blocks ε first.1 ys
      (second.1, first.2 ++ second.2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨st, buf⟩ := s
      simp only [List.cons_append, rpnConditionRun]
      rw [ih]
      simp [List.append_assoc]

/-- Inside a run (and at nowhere else relevant to emission) the buffer is untouched by
the rewrite; a copied token emits itself. -/
lemma rpnConditionRun_copy (blocks : ℕ → List ℕ) (ε : ℚ)
    (st : ℕ) (buf : List ℕ) (t : ℕ) (hm : rcMode st ≠ 2) (ts : List ℕ) :
    rpnConditionRun blocks ε (st, buf) (t :: ts) =
      let rest := rpnConditionRun blocks ε
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
def rpnConditionSegment (tf : ℕ → ℕ) (blocks : ℕ → List ℕ) (ε : ℚ) (z : ℕ) :
    List ℕ :=
  if rcMode (rpnCondControlAt tf z.unpair.1 z.unpair.2) = 2 then
    rpnConditionEmit (blocks (tf z)) ε (rpnCondWindow tf z.unpair.1 z.unpair.2)
      (tf z)
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
lemma rpnConditionRun_range (tf : ℕ → ℕ) (blocks : ℕ → List ℕ) (ε : ℚ)
    (n count : ℕ) :
    rpnConditionRun blocks ε (rcPack 0 0 0, [])
        ((List.range count).map fun j => tf (Nat.pair n j)) =
      ((rpnCondControlAt tf n count, rpnCondWindow tf n count),
        (List.range count).flatMap fun j =>
          rpnConditionSegment tf blocks ε (Nat.pair n j)) := by
  induction count with
  | zero => simp [rpnConditionRun, rpnCondControlAt]
  | succ count ih =>
      rw [List.range_succ, List.map_append, rpnConditionRun_append, ih]
      simp only [List.map_cons, List.map_nil, List.range_succ,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rw [show rpnConditionRun blocks ε
          (rpnCondControlAt tf n count, rpnCondWindow tf n count)
          [tf (Nat.pair n count)] =
        ((rpnCondStep (rpnCondControlAt tf n count) (tf (Nat.pair n count)),
          rpnCondBuf (rpnCondControlAt tf n count) (rpnCondWindow tf n count)
            (tf (Nat.pair n count))),
          (if rcMode (rpnCondControlAt tf n count) = 2 then
            rpnConditionEmit (blocks (tf (Nat.pair n count))) ε
              (rpnCondWindow tf n count) (tf (Nat.pair n count))
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
def rpnGuardedConditionTokens (blocks : ℕ → List ℕ) (ε : ℚ) (n : ℕ)
    (ts : List ℕ) : List ℕ :=
  if ∀ j < ts.length,
      rcMode ((ts.take j).foldl rpnCondStep (rcPack 0 0 0)) = 2 →
        ts.getD j 0 ≤ n
  then (rpnConditionRun blocks ε (rcPack 0 0 0, []) ts).2
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

/-- **The certificate**: the digitized guarded symbol-level price rewrite of any digit
`PolySegStream` is a `PolySegStream`, over any polynomially emittable condition block
stream.
Paper node: `thm:scon` -/
lemma rpnGuardedConditionRun_polySegStream {s blocks : ℕ → List ℕ}
    (h : PolySegStream s) (hb : PolySegStream blocks) (ε : ℚ) :
    PolySegStream (fun n => digitize (rpnGuardedConditionTokens blocks ε n
      (undigitize (s n)))) := by
  obtain ⟨⟨cc, hcnt⟩, hbig⟩ := h.undigitizeTokens
  obtain ⟨cs, hscan⟩ := rpnCondScan h
  obtain ⟨cd, hclamp⟩ := h.dayClampTokens
  obtain ⟨cf, hflag⟩ := rpnBigDayFlagScan h
  obtain ⟨cad, had⟩ := addc_polyFueled
  set tf : ℕ → ℕ := fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0 with htf
  -- Per-position views (input `z = ⟨n, j⟩`).
  have hmodeZ := PolyFueled.left.comp hscan
  have hlenZ := PolyFueled.right.comp (PolyFueled.right.comp hscan)
  -- Copy branch: one digit block per source token.
  have hcopy := hbig.blockSeg
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
    have hz : PolyFueled Code.left (fun m : ℕ => m.unpair.1) := PolyFueled.left
    have hn2 := PolyFueled.left.comp hz
    have hj2 := PolyFueled.right.comp hz
    have hlenW := hlenZ.comp hz
    have hsub := subc_polyFueled.comp (hj2.pair hlenW)
    have hoff := had.comp (hsub.pair PolyFueled.right)
    exact ⟨_, (hn2.pair hoff).of_eq fun w => by
      simp only [Nat.unpair_pair, rcLen]⟩
  obtain ⟨cidx, hidx⟩ := hidxE
  have hwin := (hbig.comp hidx).blockSeg.concatVar hlenZ
  -- Condition blocks at the clamped day.
  have hblkD := (hb.comp hclamp).digitizeStream
  -- The emit branch and the mode dispatch.
  have hEmit := ((((((((hD.append hA).append hwin).append hblkD).append
    hD).append hB).append hblkD).append hD).append hC)
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
    have hrun : (rpnConditionRun blocks ε (rcPack 0 0 0, []) (undigitize (s n))).2 =
        (List.range (undigitize (s n)).length).flatMap fun j =>
          rpnConditionSegment tf blocks ε (Nat.pair n j) := by
      conv_lhs => rw [hts]
      exact congrArg Prod.snd (rpnConditionRun_range tf blocks ε n
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
      rw [digitize_rpnConditionEmit, digitize_rpnCondWindow]
      simp only [Nat.unpair_pair, htf, rcLen, hclampEq, List.append_assoc]
    · rw [if_neg (by omega : ¬ rcMode (rpnCondControlAt tf n j) - 2 +
        (2 - rcMode (rpnCondControlAt tf n j)) = 0), if_neg hm]
      rw [htf]
      simp only [Nat.unpair_pair]
      simp [digitize]
  · rw [if_neg hflagn, rpnGuardedConditionTokens,
      if_neg (fun hguard => hflagn (hguardIff.mpr hguard))]
    simp [digitize]

#print axioms rpnGuardedConditionRun_polySegStream

/-! ## Endpoints (open)

The remaining distance to the class-preservation endpoints, with the pieces above in
hand:

1. **Whole-stream contraction exactness** for the price pass: on every input stream,
   `unRpn (rpnGuardedConditionTokens …)` decodes to the same strategy as
   `guardedConditionTokens … (unRpn ts)` — well-formed chunks by
   `unRpn_price_rewrite_chunk` + the run–parse correspondence; malformed streams by
   rejection preservation (the rewrite copies the poisoning chunk verbatim).
2. **Guard honesty transfer**: an oversized price-day at a run-aware mode-2 position
   maps to a mode-2 position of the contracted stream
   (`strategyOfTokens_trades_eq_nil_of_bigDay` then applies verbatim).
3. **The frame pass mirror** (`conditioningFrameTokenRun` at the symbol level): the
   same automaton + splice toolkit, with the trade sentence wrapped as
   `3 :: run ++ block` and the two legs assembled by position (`concatVar`); its
   PolySegStream certificate is the same assembly shape as
   `rpnGuardedConditionRun_polySegStream`.
4. The zero-aware variants for the eventual translation (mirror of
   `guardedZeroAwareConditionTokens`). -/

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
  simp only [rcMode_pack, rcCnt_pack, rcLen_pack] at hm hc ⊢
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
    · simp only [rcCnt_pack, Nat.add_sub_cancel]
  · rw [hesc] at hdec ⊢
    split_ifs at hdec ⊢ with hc0
    · omega
    · simp only [rcCnt_pack, Nat.add_sub_cancel]

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
                rw [List.take_succ, List.getElem?_eq_getElem hk]
                rfl
              have hW'succ : ∀ k (hk : k < u'.length),
                  W' (k + 1) = rpnCondStep (W' k) (u'[k]'hk) := fun k hk => by
                rw [hW']
                simp only []
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
                simp only []
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
lemma rpnConditionRun_cons (blocks : ℕ → List ℕ) (ε : ℚ) (st : ℕ) (buf : List ℕ)
    (t : ℕ) (ts : List ℕ) :
    rpnConditionRun blocks ε (st, buf) (t :: ts) =
      ((rpnConditionRun blocks ε (rpnCondStep st t, rpnCondBuf st buf t) ts).1,
        (if rcMode st = 2 then rpnConditionEmit (blocks t) ε buf t else [t]) ++
          (rpnConditionRun blocks ε (rpnCondStep st t, rpnCondBuf st buf t) ts).2) :=
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
lemma rpnConditionRun_from_payload (blocks : ℕ → List ℕ) (ε : ℚ)
    (m c' r' : ℕ) (hm : m = 3 ∨ m = 5) (buf : List ℕ) (t : ℕ) (L : List ℕ) :
    rpnConditionRun blocks ε (rcPack m c' r', buf) (t :: L) =
      ((rpnConditionRun blocks ε (rcPack 0 0 0, []) L).1,
        t :: (rpnConditionRun blocks ε (rcPack 0 0 0, []) L).2) := by
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
lemma rpnConditionRun_from_day (blocks : ℕ → List ℕ) (ε : ℚ)
    (r' : ℕ) (buf : List ℕ) (d : ℕ) (L : List ℕ) :
    rpnConditionRun blocks ε (rcPack 2 0 r', buf) (d :: L) =
      ((rpnConditionRun blocks ε (rcPack 0 0 0, []) L).1,
        rpnConditionEmit (blocks d) ε buf d ++
          (rpnConditionRun blocks ε (rcPack 0 0 0, []) L).2) := by
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
lemma rpnConditionRun_copy_of_ne_two (blocks : ℕ → List ℕ) (ε : ℚ)
    (st : ℕ) (buf : List ℕ) (ts : List ℕ)
    (h : ∀ k < ts.length, rcMode (List.foldl rpnCondStep st (ts.take k)) ≠ 2) :
    rpnConditionRun blocks ε (st, buf) ts =
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
        rw [List.take_succ, List.getElem?_eq_getElem hjlt]
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
    rw [List.take_succ, List.getElem?_eq_getElem hklt]
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

/-- **Whole-stream contraction exactness for the price pass**: on every input stream
— well-formed or garbage — the contraction of the transducer output is the
token-model price rewrite (`conditionPriceTokenRun`) of the contraction.
Paper node: `thm:scon` -/
theorem unRpn_rpnConditionRun (blocks : ℕ → List ℕ) (ψ : ℕ → Sentence)
    (hblocks : ∀ D, parseRpn (blocks D).length (blocks D) = some (ψ D, []))
    (ε : ℚ) : ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    unRpn ((rpnConditionRun blocks ε (rcPack 0 0 0, []) ts).2) =
      (conditionPriceTokenRun (fun D => Encodable.encode (ψ D)) ε (0, 0)
        (unRpn ts)).2 := by
  intro N
  induction N with
  | zero =>
      intro ts hts
      obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero (by omega)
      rfl
  | succ N ih =>
      intro ts hts
      match ts with
      | [] => rfl
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
                    have hout : (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                        (0 :: rest)).2 = 0 :: rest :=
                      congrArg Prod.snd (rpnConditionRun_copy_of_ne_two blocks ε
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
                    rw [hout, hun, conditionPriceTokenRun_price_pair]
                | d :: r2 =>
                    subst heq
                    -- Transducer output: copy the block, splice at the day.
                    have hblkcopy : rpnConditionRun blocks ε (rcPack 1 1 0, [])
                        blk = ((rcPack 2 0 blk.length, blk), blk) := by
                      rw [rpnConditionRun_copy_of_ne_two blocks ε _ _ _
                        (fun k hk => by have := hinv k hk; omega)]
                      rw [hwalk, rpnCondBufFold_run _ _ _ (fun k hk => hinv k hk)]
                      simp
                    have hout : (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                        (0 :: (blk ++ d :: r2))).2 =
                      0 :: blk ++ rpnConditionEmit (blocks d) ε blk d ++
                        (rpnConditionRun blocks ε (rcPack 0 0 0, []) r2).2 := by
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
                      unRpn_price_rewrite_chunk hblk (hblocks d) d ε _,
                      ih r2 hr2,
                      unRpn_price_chunk_block hblk d r2,
                      conditionPriceTokenRun_price]
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
                    have hucopy := rpnConditionRun_copy_of_ne_two blocks ε
                      (rcPack 1 1 0) [] (rest.take k₀) (by
                        intro k hk
                        rw [htakelen] at hk
                        rw [List.take_take, min_eq_left (le_of_lt hk)]
                        have := (hinside k hk).1
                        omega)
                    have hout : (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                        (0 :: rest)).2 = 0 :: (rest.take k₀ ++
                          (rpnConditionRun blocks ε
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
                      simp [hucopy, List.append_assoc]
                    have hunL : ∀ Y, unRpn (0 :: (rest.take k₀ ++ Y)) =
                        [0, 0] := fun Y => by
                      rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
                        hpoison _ _]
                    rw [hout, hunL, hun0, conditionPriceTokenRun_price_pair]
                · -- No completion: pure copy, both contractions stop.
                  have hout : (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                      (0 :: rest)).2 = 0 :: rest :=
                    congrArg Prod.snd (rpnConditionRun_copy_of_ne_two blocks ε
                      (rcPack 0 0 0) [] (0 :: rest) (by
                        intro k hk
                        match k with
                        | 0 => simp
                        | j + 1 =>
                            simp only [List.length_cons] at hk
                            rw [List.take_succ_cons, List.foldl_cons,
                              rpnCondStep_base_price]
                            exact fun hmode => hex ⟨j, by omega, hmode⟩))
                  rw [hout, hun0, conditionPriceTokenRun_price_pair]
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
                  have hblkcopy : rpnConditionRun blocks ε (rcPack 4 1 0, [])
                      blk = ((rcPack 0 0 0, []), blk) := by
                    rw [rpnConditionRun_copy_of_ne_two blocks ε _ _ _
                      (fun k hk => by have := hinv k hk; omega)]
                    rw [hwalk, rpnCondBufFold_reset _ _ _ hblkne (by
                      rw [hwalk]; simp)]
                  have hout : (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                      (6 :: (blk ++ r1))).2 =
                    6 :: (blk ++
                      (rpnConditionRun blocks ε (rcPack 0 0 0, []) r1).2) := by
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
                    conditionPriceTokenRun_trade]
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
                    · have hucopy := rpnConditionRun_copy_of_ne_two blocks ε
                        (rcPack 4 1 0) [] (rest.take k₀) (by
                          intro k hk
                          rw [htakelen] at hk
                          rw [List.take_take, min_eq_left (le_of_lt hk)]
                          have := (hinside k hk).1
                          omega)
                      have hout : (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                          (6 :: rest)).2 = 6 :: (rest.take k₀ ++
                            (rpnConditionRun blocks ε
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
                        simp [hucopy, List.append_assoc]
                      have hunL : ∀ Y, unRpn (6 :: (rest.take k₀ ++ Y)) =
                          [6, 0] := fun Y => by
                        rw [unRpn, List.length_cons, unRpnTokens_cons,
                          if_neg (by norm_num), if_pos rfl, hpoison _ _]
                      rw [hout, hunL, hun0]
                      rw [conditionPriceTokenRun_trade]
                      rfl
                  · -- Never exits: pure copy of an unfinished trade run.
                    have hout : (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                        (6 :: rest)).2 = 6 :: rest :=
                      congrArg Prod.snd (rpnConditionRun_copy_of_ne_two blocks ε
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
                    rw [conditionPriceTokenRun_trade]
                    rfl
            · by_cases ht1 : t = 1
              · -- Constant payload chunk.
                subst ht1
                match rest with
                | [] =>
                    have hout : (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                        [1]).2 = [1] := by
                      rw [rpnConditionRun_cons, if_neg (by simp)]
                      rfl
                    rw [hout, show unRpn [1] = [1] from rfl,
                      conditionPriceTokenRun_one]
                | c :: rest' =>
                    have hout : (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                        (1 :: c :: rest')).2 =
                      1 :: c :: (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                        rest').2 := by
                      rw [rpnConditionRun_cons, if_neg (by simp),
                        rpnCondStep_base_one, rpnCondBuf_base,
                        rpnConditionRun_from_payload blocks ε 3 0 0
                          (Or.inl rfl) [] c rest']
                      rfl
                    have hr : rest'.length ≤ N := by
                      simp only [List.length_cons] at hts
                      omega
                    rw [hout, unRpn_payload_chunk 1 c (Or.inl rfl) _,
                      ih rest' hr,
                      unRpn_payload_chunk 1 c (Or.inl rfl) rest',
                      conditionPriceTokenRun_payload _ _ 1 c (Or.inl rfl)]
              · by_cases ht7 : t = 7
                · -- Variable payload chunk.
                  subst ht7
                  match rest with
                  | [] =>
                      have hout : (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                          [7]).2 = [7] := by
                        rw [rpnConditionRun_cons, if_neg (by simp)]
                        rfl
                      rw [hout, show unRpn [7] = [7] from rfl,
                        conditionPriceTokenRun_one]
                  | c :: rest' =>
                      have hout : (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                          (7 :: c :: rest')).2 =
                        7 :: c :: (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                          rest').2 := by
                        rw [rpnConditionRun_cons, if_neg (by simp),
                          rpnCondStep_base_seven, rpnCondBuf_base,
                          rpnConditionRun_from_payload blocks ε 5 0 0
                            (Or.inr rfl) [] c rest']
                        rfl
                      have hr : rest'.length ≤ N := by
                        simp only [List.length_cons] at hts
                        omega
                      rw [hout, unRpn_payload_chunk 7 c (Or.inr rfl) _,
                        ih rest' hr,
                        unRpn_payload_chunk 7 c (Or.inr rfl) rest',
                        conditionPriceTokenRun_payload _ _ 7 c (Or.inr rfl)]
                · -- Bare operator/close token: transparent.
                  have hout : (rpnConditionRun blocks ε (rcPack 0 0 0, [])
                      (t :: rest)).2 =
                    t :: (rpnConditionRun blocks ε (rcPack 0 0 0, []) rest).2 := by
                    rw [rpnConditionRun_cons, if_neg (by simp),
                      rpnCondStep_base_other t ht0 ht1 ht6 ht7, rpnCondBuf_base]
                    rfl
                  rw [hout, unRpn_single_chunk t ⟨ht0, ht1, ht6, ht7⟩ _,
                    ih rest (by omega),
                    unRpn_single_chunk t ⟨ht0, ht1, ht6, ht7⟩ rest,
                    conditionPriceTokenRun_single _ _ t ht0 ht1 ht6 ht7]

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
    (strategyOfTokens n (unRpn (rpnGuardedConditionTokens blocks ε n ts))).trades =
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

/-! ### Endpoint statements (open, recorded — not sorried)

The two target endpoints are stated here as comments rather than sorried theorems so
the mainline keeps its strict no-`sorryAx` guarantee for public statements.  The
remaining distance is itemized above ("Endpoints (open)"); every construction
ingredient below them is proved.

```
theorem conditionedTranslation_preserves_ecRpn
    (ψ : ℕ → Sentence) (hψ : RpnSentenceCodes ψ) (ε : ℚ)
    (T : Trader) (hT : EfficientlyComputable T) :
    EfficientlyComputable (T.conditionedTranslation ψ ε)
-- TODO(blueprint:thm:scon): compose `rpnGuardedConditionRun_polySegStream` with the
-- symbol-level frame pass and discharge contraction exactness.

theorem eventualConditionedTranslation_preserves_ecRpn
    {P : History} {ψ : ℕ → Sentence}
    (F : EventualConditioningFloor P ψ) (hψ : RpnSentenceCodes ψ)
    (T : Trader) (hT : EfficientlyComputable T) :
    EfficientlyComputable (T.eventualConditionedTranslation F)
-- TODO(blueprint:thm:scon): zero-aware mirror of the guarded rewrite + frame pass +
-- launch gate, as in `eventualConditionedTranslation_preserves_ec₂`.
```
-/

end RpnConditioning

end LogicalInduction
