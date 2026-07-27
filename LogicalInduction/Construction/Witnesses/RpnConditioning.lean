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
* the per-chunk contraction identity `unRpn_price_rewrite_chunk` anchoring that claim.

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
      ∃ blk, ts = blk ++ rest ∧ ∀ c r,
        List.foldl rpnCondStep (rcPack a (c + 1) r) blk =
          if c = 0 then exit (r + blk.length) else rcPack a c (r + blk.length) := by
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
            refine ⟨[0], rfl, fun c r => ?_⟩
            rw [List.foldl_cons, List.foldl_nil, hrun]
            by_cases hc : c = 0 <;> simp [hc]
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
                      refine ⟨[1, c₀], rfl, fun c r => ?_⟩
                      rw [List.foldl_cons, List.foldl_cons, List.foldl_nil,
                        hrun, if_pos rfl, hesc]
                      by_cases hc : c = 0 <;> simp [hc]
            · rw [if_neg h1] at h
              have hbin : ∀ (mk : Sentence → Sentence → Sentence),
                  ((parseRpn fuel ts').bind fun p =>
                    (parseRpn fuel p.2).bind fun q =>
                      some (mk p.1 q.1, q.2)) = some (φ, rest) →
                  (t = 2 ∨ t = 3 ∨ t = 4) →
                  ∃ blk, t :: ts' = blk ++ rest ∧ ∀ c r,
                    List.foldl rpnCondStep (rcPack a (c + 1) r) blk =
                      if c = 0 then exit (r + blk.length)
                      else rcPack a c (r + blk.length) := by
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
                        obtain ⟨blk₁, hts', hblk₁⟩ := ih ts' hp
                        obtain ⟨blk₂, hp2, hblk₂⟩ := ih p.2 hq
                        refine ⟨t :: blk₁ ++ blk₂, by
                          rw [hts', hp2, hrest]; simp, fun c r => ?_⟩
                        rw [List.cons_append, List.foldl_cons, hrun,
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
                    refine ⟨[t], rfl, fun c r => ?_⟩
                    rw [List.foldl_cons, List.foldl_nil, hrun, if_neg h1,
                      if_neg (by omega)]
                    by_cases hc : c = 0 <;> simp [hc]

/-- Price-run instance: the walk exits into the day-expect mode `2`. -/
lemma foldl_rpnCondStep_price_run (fuel : ℕ) (ts : List ℕ) {φ : Sentence}
    {rest : List ℕ} (h : parseRpn fuel ts = some (φ, rest)) :
    ∃ blk, ts = blk ++ rest ∧ ∀ c r,
      List.foldl rpnCondStep (rcPack 1 (c + 1) r) blk =
        if c = 0 then rcPack 2 0 (r + blk.length)
        else rcPack 1 c (r + blk.length) := by
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
    ∃ blk, ts = blk ++ rest ∧ ∀ c r,
      List.foldl rpnCondStep (rcPack 4 (c + 1) r) blk =
        if c = 0 then rcPack 0 0 0 else rcPack 4 c (r + blk.length) := by
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
    List.foldl rpnCondStep (rcPack 1 1 0) b = rcPack 2 0 b.length := by
  obtain ⟨blk, hts, hblk⟩ := foldl_rpnCondStep_price_run b.length b hb
  rw [List.append_nil] at hts
  subst hts
  simpa using hblk 0 0

/-- A complete trade sentence block walks from the run entry back to base. -/
lemma foldl_rpnCondStep_trade_block {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) :
    List.foldl rpnCondStep (rcPack 4 1 0) b = rcPack 0 0 0 := by
  obtain ⟨blk, hts, hblk⟩ := foldl_rpnCondStep_trade_run b.length b hb
  rw [List.append_nil] at hts
  subst hts
  simpa using hblk 0 0

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

end RpnConditioning

end LogicalInduction
