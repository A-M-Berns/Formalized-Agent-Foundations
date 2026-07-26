/-
# Polish-notation sentence blocks (the `Tok₃` layer, part 1: the pure coding)

The digit-metered emission model (`EfficientlyComputableTok₂`) meters token *bit*
size, but sentences still travel as single `Encodable` pair-code tokens, whose bit
size is the formula's symbol count only up to balance: skewed formulas inflate
exponentially.  The `Tok₃` layer removes that residual by letting sentence slots of
the flat strategy stream carry **Polish-notation symbol runs** instead: one token per
formula symbol, so poly digit-stream length = poly symbol count — the paper's `𝓔𝓒`
metering on the nose.

Symbol alphabet of a sentence block:

* `0` — `⊥`;
* `1` — **escape**: the next token is a literal pair code for the whole subformula
  (decoded by `Encodable.decode`; this makes the inclusions from the token and digit
  models verbatim splices);
* `2` / `3` / `4` — `➝` / `⋏` / `⋎`, each followed by its two operands;
* `t + 5` — atom `t`.

Prefix order is forward self-delimiting: a pending-formula counter starts at `1`,
leaves decrement it, binary tags increment it, and the block ends exactly when it
reaches `0` — every proper prefix keeps it positive.

This file is the pure layer: the coding, the fuelled block parser, round trips, and
injectivity.  The stream transducer and its computability live in part 2.

Paper node: `def:ec` (symbol-metered sentence slots).
-/
import LogicalInduction.Framework.Criterion

namespace LogicalInduction

open LO.Propositional

/-! ## The coding -/

/-- Polish-notation symbol run of a sentence (no escapes: the canonical form). -/
def rpn : Sentence → List ℕ
  | Formula.atom a => [a + 5]
  | Formula.falsum => [0]
  | Formula.and φ ψ => 3 :: (rpn φ ++ rpn ψ)
  | Formula.or φ ψ => 4 :: (rpn φ ++ rpn ψ)
  | Formula.imp φ ψ => 2 :: (rpn φ ++ rpn ψ)

lemma rpn_ne_nil (φ : Sentence) : rpn φ ≠ [] := by
  cases φ <;> simp [rpn]

lemma rpn_length_pos (φ : Sentence) : 0 < (rpn φ).length := by
  cases φ <;> simp [rpn]

/-! ## The block parser

`parseRpn fuel ts` reads one sentence block from the front of `ts` and returns the
parsed sentence together with the unread suffix.  Fuel bounds the recursion; any
`fuel ≥ ts.length` is enough (each call consumes at least one token). -/

def parseRpn : ℕ → List ℕ → Option (Sentence × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 0 then some (Formula.falsum, rest)
      else if t = 1 then
        rest.head?.bind fun c =>
          (Encodable.decode (α := Sentence) c).map fun φ => (φ, rest.tail)
      else if t = 2 then
        (parseRpn fuel rest).bind fun p =>
          (parseRpn fuel p.2).bind fun q => some (Formula.imp p.1 q.1, q.2)
      else if t = 3 then
        (parseRpn fuel rest).bind fun p =>
          (parseRpn fuel p.2).bind fun q => some (Formula.and p.1 q.1, q.2)
      else if t = 4 then
        (parseRpn fuel rest).bind fun p =>
          (parseRpn fuel p.2).bind fun q => some (Formula.or p.1 q.1, q.2)
      else some (Formula.atom (t - 5), rest)

@[simp] lemma parseRpn_zero (ts : List ℕ) : parseRpn 0 ts = none := rfl

@[simp] lemma parseRpn_nil (fuel : ℕ) : parseRpn (fuel + 1) [] = none := rfl

lemma parseRpn_cons (fuel t : ℕ) (rest : List ℕ) :
    parseRpn (fuel + 1) (t :: rest) =
      if t = 0 then some (Formula.falsum, rest)
      else if t = 1 then
        rest.head?.bind fun c =>
          (Encodable.decode (α := Sentence) c).map fun φ => (φ, rest.tail)
      else if t = 2 then
        (parseRpn fuel rest).bind fun p =>
          (parseRpn fuel p.2).bind fun q => some (Formula.imp p.1 q.1, q.2)
      else if t = 3 then
        (parseRpn fuel rest).bind fun p =>
          (parseRpn fuel p.2).bind fun q => some (Formula.and p.1 q.1, q.2)
      else if t = 4 then
        (parseRpn fuel rest).bind fun p =>
          (parseRpn fuel p.2).bind fun q => some (Formula.or p.1 q.1, q.2)
      else some (Formula.atom (t - 5), rest) := rfl

/-- A successful parse consumes at least one token and returns a strict suffix. -/
lemma parseRpn_length_lt : ∀ (fuel : ℕ) (ts : List ℕ) (φ : Sentence) (rest : List ℕ),
    parseRpn fuel ts = some (φ, rest) → rest.length < ts.length
  | 0, ts, φ, rest => by simp
  | fuel + 1, [], φ, rest => by simp
  | fuel + 1, t :: ts, φ, rest => by
      intro h
      rw [parseRpn_cons] at h
      by_cases h0 : t = 0
      · rw [if_pos h0] at h
        obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        simp
      rw [if_neg h0] at h
      by_cases h1 : t = 1
      · rw [if_pos h1] at h
        rcases ts with _ | ⟨c, ts'⟩
        · simp at h
        rw [List.head?_cons] at h
        rcases hdec : Encodable.decode (α := Sentence) c with _ | ψ
        · simp [hdec] at h
        · simp only [Option.bind_some, hdec, Option.map_some, List.tail_cons] at h
          obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
          simp
      rw [if_neg h1] at h
      have hbin : ∀ (hb : (parseRpn fuel ts).bind
            (fun p => (parseRpn fuel p.2).bind fun q =>
              some (Formula.imp p.1 q.1, q.2)) = some (φ, rest) ∨
          (parseRpn fuel ts).bind
            (fun p => (parseRpn fuel p.2).bind fun q =>
              some (Formula.and p.1 q.1, q.2)) = some (φ, rest) ∨
          (parseRpn fuel ts).bind
            (fun p => (parseRpn fuel p.2).bind fun q =>
              some (Formula.or p.1 q.1, q.2)) = some (φ, rest)),
          rest.length < (t :: ts).length := by
        intro hb
        have key : ∃ φ1 r1 φ2, parseRpn fuel ts = some (φ1, r1) ∧
            parseRpn fuel r1 = some (φ2, rest) := by
          rcases hp1 : parseRpn fuel ts with _ | ⟨φ1, r1⟩
          · exfalso
            rcases hb with hb | hb | hb <;> rw [hp1] at hb <;> simp at hb
          rcases hp2 : parseRpn fuel r1 with _ | ⟨φ2, r2⟩
          · exfalso
            rcases hb with hb | hb | hb <;> rw [hp1] at hb <;>
              simp only [Option.bind_some] at hb <;> rw [hp2] at hb <;> simp at hb
          rcases hb with hb | hb | hb <;> rw [hp1] at hb
          all_goals
            simp only [Option.bind_some] at hb
            rw [hp2] at hb
            simp only [Option.bind_some] at hb
            obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hb
            exact ⟨φ1, r1, φ2, rfl, hp2⟩
        obtain ⟨φ1, r1, φ2, hp1, hp2⟩ := key
        have l1 := parseRpn_length_lt fuel ts φ1 r1 hp1
        have l2 := parseRpn_length_lt fuel r1 φ2 rest hp2
        simp only [List.length_cons]
        omega
      by_cases h2 : t = 2
      · rw [if_pos h2] at h
        exact hbin (Or.inl h)
      rw [if_neg h2] at h
      by_cases h3 : t = 3
      · rw [if_pos h3] at h
        exact hbin (Or.inr (Or.inl h))
      rw [if_neg h3] at h
      by_cases h4 : t = 4
      · rw [if_pos h4] at h
        exact hbin (Or.inr (Or.inr h))
      rw [if_neg h4] at h
      obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      simp

/-- Fuel monotonicity: a successful parse survives any larger fuel. -/
lemma parseRpn_mono : ∀ {fuel fuel' : ℕ} (ts : List ℕ) {out : Sentence × List ℕ},
    fuel ≤ fuel' → parseRpn fuel ts = some out → parseRpn fuel' ts = some out := by
  intro fuel
  induction fuel with
  | zero => intro fuel' ts out _ h; simp at h
  | succ fuel ih =>
      intro fuel' ts out hle h
      match fuel', hle with
      | fuel' + 1, hle =>
          have hle' : fuel ≤ fuel' := by omega
          match ts with
          | [] => simp at h
          | t :: rest =>
              rw [parseRpn_cons] at h ⊢
              by_cases h0 : t = 0
              · rwa [if_pos h0] at h ⊢
              rw [if_neg h0] at h ⊢
              by_cases h1 : t = 1
              · rwa [if_pos h1] at h ⊢
              rw [if_neg h1] at h ⊢
              have hbin : ∀ (mk : Sentence → Sentence → Sentence),
                  (parseRpn fuel rest).bind
                    (fun p => (parseRpn fuel p.2).bind fun q =>
                      some (mk p.1 q.1, q.2)) = some out →
                  (parseRpn fuel' rest).bind
                    (fun p => (parseRpn fuel' p.2).bind fun q =>
                      some (mk p.1 q.1, q.2)) = some out := by
                intro mk hb
                rcases hp1 : parseRpn fuel rest with _ | ⟨φ1, r1⟩
                · rw [hp1] at hb
                  simp at hb
                rw [hp1] at hb
                simp only [Option.bind_some] at hb
                rcases hp2 : parseRpn fuel r1 with _ | ⟨φ2, r2⟩
                · rw [hp2] at hb
                  simp at hb
                rw [hp2] at hb
                rw [ih rest hle' hp1]
                simp only [Option.bind_some]
                rw [ih r1 hle' hp2]
                exact hb
              by_cases h2 : t = 2
              · rw [if_pos h2] at h ⊢
                exact hbin Formula.imp h
              rw [if_neg h2] at h ⊢
              by_cases h3 : t = 3
              · rw [if_pos h3] at h ⊢
                exact hbin Formula.and h
              rw [if_neg h3] at h ⊢
              by_cases h4 : t = 4
              · rw [if_pos h4] at h ⊢
                exact hbin Formula.or h
              rw [if_neg h4] at h ⊢
              exact h

/-! ## Round trips -/

/-- **Canonical round trip**: parsing a Polish run recovers the sentence and leaves
the suffix untouched, under any sufficient fuel. -/
lemma parseRpn_rpn : ∀ (φ : Sentence) (rest : List ℕ) {fuel : ℕ},
    (rpn φ).length ≤ fuel →
    parseRpn fuel (rpn φ ++ rest) = some (φ, rest) := by
  intro φ
  induction φ with
  | atom a =>
      intro rest fuel hfuel
      match fuel, hfuel with
      | fuel + 1, _ =>
          rw [rpn, List.cons_append, List.nil_append, parseRpn_cons,
            if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_neg (by omega)]
          norm_num
  | falsum =>
      intro rest fuel hfuel
      match fuel, hfuel with
      | fuel + 1, _ =>
          rw [rpn, List.cons_append, List.nil_append, parseRpn_cons, if_pos rfl]
  | and φ ψ ihφ ihψ =>
      intro rest fuel hfuel
      rw [rpn] at hfuel
      match fuel, hfuel with
      | fuel + 1, hfuel =>
          rw [rpn, List.cons_append, parseRpn_cons,
            if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl,
            List.append_assoc,
            ihφ (rpn ψ ++ rest) (fuel := fuel) (by
              simp only [List.length_cons, List.length_append] at hfuel ⊢
              omega)]
          simp only [Option.bind_some]
          rw [ihψ rest (fuel := fuel) (by
              simp only [List.length_cons, List.length_append] at hfuel ⊢
              omega)]
          rfl
  | or φ ψ ihφ ihψ =>
      intro rest fuel hfuel
      rw [rpn] at hfuel
      match fuel, hfuel with
      | fuel + 1, hfuel =>
          rw [rpn, List.cons_append, parseRpn_cons,
            if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_pos rfl,
            List.append_assoc,
            ihφ (rpn ψ ++ rest) (fuel := fuel) (by
              simp only [List.length_cons, List.length_append] at hfuel ⊢
              omega)]
          simp only [Option.bind_some]
          rw [ihψ rest (fuel := fuel) (by
              simp only [List.length_cons, List.length_append] at hfuel ⊢
              omega)]
          rfl
  | imp φ ψ ihφ ihψ =>
      intro rest fuel hfuel
      rw [rpn] at hfuel
      match fuel, hfuel with
      | fuel + 1, hfuel =>
          rw [rpn, List.cons_append, parseRpn_cons,
            if_neg (by omega), if_neg (by omega), if_pos rfl,
            List.append_assoc,
            ihφ (rpn ψ ++ rest) (fuel := fuel) (by
              simp only [List.length_cons, List.length_append] at hfuel ⊢
              omega)]
          simp only [Option.bind_some]
          rw [ihψ rest (fuel := fuel) (by
              simp only [List.length_cons, List.length_append] at hfuel ⊢
              omega)]
          rfl

/-- **Escape round trip**: a two-token escape block parses to its decoded sentence. -/
lemma parseRpn_escape (φ : Sentence) (rest : List ℕ) {fuel : ℕ} (hfuel : 1 ≤ fuel) :
    parseRpn fuel (1 :: Encodable.encode φ :: rest) = some (φ, rest) := by
  match fuel, hfuel with
  | fuel + 1, _ =>
      rw [parseRpn_cons, if_neg (by omega), if_pos rfl]
      simp [Encodable.encodek]

/-- Injectivity of the canonical coding. -/
lemma rpn_injective : Function.Injective rpn := by
  intro φ ψ h
  have hφ := parseRpn_rpn φ [] (fuel := (rpn φ).length) le_rfl
  have hψ := parseRpn_rpn ψ [] (fuel := (rpn φ).length) (le_of_eq (by rw [h]))
  rw [List.append_nil] at hφ hψ
  rw [h] at hφ hψ
  obtain ⟨h1, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj (hφ.symm.trans hψ)
  exact h1

/-! ## The stream transducer

`unRpn` walks the flat strategy grammar and contracts each sentence block back to a
single pair-code token: sentence slots follow tags `0` (price — one day token after)
and `6` (trade); tags `1` and `7` carry one opaque payload token; everything else is
copied.  A failed block parse emits the undecodable code `0` and stops, preserving
rejection.  Fuel decreases once per grammar chunk; `ts.length` always suffices. -/

def unRpnTokens : ℕ → List ℕ → List ℕ
  | _, [] => []
  | 0, _ => []
  | fuel + 1, t :: rest =>
      if t = 0 then
        match parseRpn rest.length rest with
        | none => [0, 0]
        | some (φ, r1) =>
            match r1 with
            | [] => [0, Encodable.encode φ]
            | d :: r2 => 0 :: Encodable.encode φ :: d :: unRpnTokens fuel r2
      else if t = 6 then
        match parseRpn rest.length rest with
        | none => [6, 0]
        | some (φ, r1) => 6 :: Encodable.encode φ :: unRpnTokens fuel r1
      else if t = 1 then
        match rest with
        | [] => [1]
        | c :: r => 1 :: c :: unRpnTokens fuel r
      else if t = 7 then
        match rest with
        | [] => [7]
        | c :: r => 7 :: c :: unRpnTokens fuel r
      else t :: unRpnTokens fuel rest

/-- Contract every sentence block of a flat strategy stream to its pair code. -/
def unRpn (ts : List ℕ) : List ℕ := unRpnTokens ts.length ts

lemma unRpnTokens_cons (fuel t : ℕ) (rest : List ℕ) :
    unRpnTokens (fuel + 1) (t :: rest) =
      if t = 0 then
        match parseRpn rest.length rest with
        | none => [0, 0]
        | some (φ, r1) =>
            match r1 with
            | [] => [0, Encodable.encode φ]
            | d :: r2 => 0 :: Encodable.encode φ :: d :: unRpnTokens fuel r2
      else if t = 6 then
        match parseRpn rest.length rest with
        | none => [6, 0]
        | some (φ, r1) => 6 :: Encodable.encode φ :: unRpnTokens fuel r1
      else if t = 1 then
        match rest with
        | [] => [1]
        | c :: r => 1 :: c :: unRpnTokens fuel r
      else if t = 7 then
        match rest with
        | [] => [7]
        | c :: r => 7 :: c :: unRpnTokens fuel r
      else t :: unRpnTokens fuel rest := rfl

/-- Fuel invariance above the list length. -/
lemma unRpnTokens_congr_aux : ∀ (n : ℕ) (ts : List ℕ), ts.length ≤ n →
    ∀ (fuel fuel' : ℕ), ts.length ≤ fuel → ts.length ≤ fuel' →
    unRpnTokens fuel ts = unRpnTokens fuel' ts
  | _, [], _, fuel, fuel', _, _ => by cases fuel <;> cases fuel' <;> rfl
  | 0, t :: rest, hn, fuel, fuel', hf, hf' => by simp at hn
  | n + 1, t :: rest, hn, fuel, fuel', hf, hf' => by
      match fuel, fuel', hf, hf' with
      | fuel + 1, fuel' + 1, hf, hf' =>
          simp only [List.length_cons] at hn hf hf'
          rw [unRpnTokens_cons, unRpnTokens_cons]
          by_cases h0 : t = 0
          · rw [if_pos h0, if_pos h0]
            rcases hp : parseRpn rest.length rest with _ | ⟨φ, r1⟩
            · rfl
            rcases r1 with _ | ⟨d, r2⟩
            · rfl
            simp only []
            have hlen := parseRpn_length_lt _ _ _ _ hp
            simp only [List.length_cons] at hlen
            rw [unRpnTokens_congr_aux n r2 (by omega) fuel fuel' (by omega)
              (by omega)]
          rw [if_neg h0, if_neg h0]
          by_cases h6 : t = 6
          · rw [if_pos h6, if_pos h6]
            rcases hp : parseRpn rest.length rest with _ | ⟨φ, r1⟩
            · rfl
            simp only []
            have hlen := parseRpn_length_lt _ _ _ _ hp
            rw [unRpnTokens_congr_aux n r1 (by omega) fuel fuel' (by omega)
              (by omega)]
          rw [if_neg h6, if_neg h6]
          by_cases h1 : t = 1
          · rw [if_pos h1, if_pos h1]
            rcases rest with _ | ⟨c, r⟩
            · rfl
            simp only []
            simp only [List.length_cons] at hn hf hf'
            rw [unRpnTokens_congr_aux n r (by omega) fuel fuel' (by omega)
              (by omega)]
          rw [if_neg h1, if_neg h1]
          by_cases h7 : t = 7
          · rw [if_pos h7, if_pos h7]
            rcases rest with _ | ⟨c, r⟩
            · rfl
            simp only []
            simp only [List.length_cons] at hn hf hf'
            rw [unRpnTokens_congr_aux n r (by omega) fuel fuel' (by omega)
              (by omega)]
          rw [if_neg h7, if_neg h7]
          rw [unRpnTokens_congr_aux n rest (by omega) fuel fuel' (by omega)
            (by omega)]

lemma unRpnTokens_congr (ts : List ℕ) {fuel fuel' : ℕ}
    (hf : ts.length ≤ fuel) (hf' : ts.length ≤ fuel') :
    unRpnTokens fuel ts = unRpnTokens fuel' ts :=
  unRpnTokens_congr_aux ts.length ts le_rfl fuel fuel' hf hf'

/-! ### Chunk equations for `unRpn` (canonical blocks) -/

lemma unRpn_nil : unRpn [] = [] := rfl

/-- A complete price chunk with a canonical Polish block contracts exactly. -/
lemma unRpn_price_chunk (φ : Sentence) (d : ℕ) (rest : List ℕ) :
    unRpn (0 :: (rpn φ ++ d :: rest)) =
      0 :: Encodable.encode φ :: d :: unRpn rest := by
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
    parseRpn_rpn φ (d :: rest) (by simp)]
  simp only []
  rw [unRpnTokens_congr rest (by simp only [List.length_cons, List.length_append]; omega) le_rfl]
  rfl

/-- A complete trade chunk with a canonical Polish block contracts exactly. -/
lemma unRpn_trade_chunk (φ : Sentence) (rest : List ℕ) :
    unRpn (6 :: (rpn φ ++ rest)) =
      6 :: Encodable.encode φ :: unRpn rest := by
  rw [unRpn, List.length_cons, unRpnTokens_cons,
    if_neg (by norm_num), if_pos rfl,
    parseRpn_rpn φ rest (by simp)]
  simp only []
  rw [unRpnTokens_congr rest (by simp only [List.length_cons, List.length_append]; omega) le_rfl]
  rfl

/-- A complete price chunk with an escaped canonical code contracts exactly. -/
lemma unRpn_price_escape_chunk (φ : Sentence) (d : ℕ) (rest : List ℕ) :
    unRpn (0 :: 1 :: Encodable.encode φ :: d :: rest) =
      0 :: Encodable.encode φ :: d :: unRpn rest := by
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
    parseRpn_escape φ (d :: rest) (by simp)]
  simp only []
  rw [unRpnTokens_congr rest (by simp only [List.length_cons, List.length_append]; omega) le_rfl]
  rfl

/-- A complete trade chunk with an escaped canonical code contracts exactly. -/
lemma unRpn_trade_escape_chunk (φ : Sentence) (rest : List ℕ) :
    unRpn (6 :: 1 :: Encodable.encode φ :: rest) =
      6 :: Encodable.encode φ :: unRpn rest := by
  rw [unRpn, List.length_cons, unRpnTokens_cons,
    if_neg (by norm_num), if_pos rfl,
    parseRpn_escape φ rest (by simp)]
  simp only []
  rw [unRpnTokens_congr rest (by simp only [List.length_cons, List.length_append]; omega) le_rfl]
  rfl

/-- Opaque payload chunks (rational constants, variable indices) copy verbatim. -/
lemma unRpn_payload_chunk (t c : ℕ) (ht : t = 1 ∨ t = 7) (rest : List ℕ) :
    unRpn (t :: c :: rest) = t :: c :: unRpn rest := by
  rcases ht with rfl | rfl
  · rw [unRpn, List.length_cons, unRpnTokens_cons,
      if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    simp only []
    rw [unRpnTokens_congr rest (by simp only [List.length_cons, List.length_append]; omega) le_rfl]
    rfl
  · rw [unRpn, List.length_cons, unRpnTokens_cons,
      if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
      if_pos rfl]
    simp only []
    rw [unRpnTokens_congr rest (by simp only [List.length_cons, List.length_append]; omega) le_rfl]
    rfl

/-- Bare operator/close tokens copy verbatim. -/
lemma unRpn_single_chunk (t : ℕ) (ht : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 6 ∧ t ≠ 7)
    (rest : List ℕ) :
    unRpn (t :: rest) = t :: unRpn rest := by
  obtain ⟨h0, h1, h6, h7⟩ := ht
  rw [unRpn, List.length_cons, unRpnTokens_cons,
    if_neg h0, if_neg h6, if_neg h1, if_neg h7]
  rw [unRpnTokens_congr rest (by omega) le_rfl]
  rfl

/-- Escape parse with an arbitrary decodable payload. -/
lemma parseRpn_escape' {c : ℕ} {φ : Sentence}
    (hdec : Encodable.decode (α := Sentence) c = some φ)
    (rest : List ℕ) {fuel : ℕ} (hfuel : 1 ≤ fuel) :
    parseRpn fuel (1 :: c :: rest) = some (φ, rest) := by
  match fuel, hfuel with
  | fuel + 1, _ =>
      rw [parseRpn_cons, if_neg (by omega), if_pos rfl]
      simp [hdec]

/-- Escape parse failure on an undecodable payload. -/
lemma parseRpn_escape_none {c : ℕ}
    (hdec : Encodable.decode (α := Sentence) c = none)
    (rest : List ℕ) (fuel : ℕ) :
    parseRpn fuel (1 :: c :: rest) = none := by
  match fuel with
  | 0 => rfl
  | fuel + 1 =>
      rw [parseRpn_cons, if_neg (by omega), if_pos rfl]
      simp [hdec]

/-! ## The escape expansion

`escExpand` is the forward splice for the model inclusions: each sentence-slot token
`c` becomes the two-token escape block `[1, c]`, everything else is copied.  Composed
with `unRpn` it re-emits the *canonical* code of the decoded sentence, so the streams
need not agree token-for-token on non-canonical codes — but they parse identically,
which is the simulation theorem below. -/

def escExpandTokens : ℕ → List ℕ → List ℕ
  | _, [] => []
  | 0, _ => []
  | fuel + 1, t :: rest =>
      if t = 0 then
        match rest with
        | [] => [0]
        | c :: r1 =>
            match r1 with
            | [] => [0, 1, c]
            | d :: r2 => 0 :: 1 :: c :: d :: escExpandTokens fuel r2
      else if t = 6 then
        match rest with
        | [] => [6]
        | c :: r => 6 :: 1 :: c :: escExpandTokens fuel r
      else if t = 1 then
        match rest with
        | [] => [1]
        | c :: r => 1 :: c :: escExpandTokens fuel r
      else if t = 7 then
        match rest with
        | [] => [7]
        | c :: r => 7 :: c :: escExpandTokens fuel r
      else t :: escExpandTokens fuel rest

/-- Escape-expand every sentence slot of a flat strategy stream. -/
def escExpand (ts : List ℕ) : List ℕ := escExpandTokens ts.length ts

lemma escExpandTokens_cons (fuel t : ℕ) (rest : List ℕ) :
    escExpandTokens (fuel + 1) (t :: rest) =
      if t = 0 then
        match rest with
        | [] => [0]
        | c :: r1 =>
            match r1 with
            | [] => [0, 1, c]
            | d :: r2 => 0 :: 1 :: c :: d :: escExpandTokens fuel r2
      else if t = 6 then
        match rest with
        | [] => [6]
        | c :: r => 6 :: 1 :: c :: escExpandTokens fuel r
      else if t = 1 then
        match rest with
        | [] => [1]
        | c :: r => 1 :: c :: escExpandTokens fuel r
      else if t = 7 then
        match rest with
        | [] => [7]
        | c :: r => 7 :: c :: escExpandTokens fuel r
      else t :: escExpandTokens fuel rest := rfl

lemma escExpandTokens_congr_aux : ∀ (n : ℕ) (ts : List ℕ), ts.length ≤ n →
    ∀ (fuel fuel' : ℕ), ts.length ≤ fuel → ts.length ≤ fuel' →
    escExpandTokens fuel ts = escExpandTokens fuel' ts
  | _, [], _, fuel, fuel', _, _ => by cases fuel <;> cases fuel' <;> rfl
  | 0, t :: rest, hn, fuel, fuel', hf, hf' => by simp at hn
  | n + 1, t :: rest, hn, fuel, fuel', hf, hf' => by
      match fuel, fuel', hf, hf' with
      | fuel + 1, fuel' + 1, hf, hf' =>
          simp only [List.length_cons] at hn hf hf'
          rw [escExpandTokens_cons, escExpandTokens_cons]
          by_cases h0 : t = 0
          · rw [if_pos h0, if_pos h0]
            rcases rest with _ | ⟨c, r1⟩
            · rfl
            rcases r1 with _ | ⟨d, r2⟩
            · rfl
            simp only []
            simp only [List.length_cons] at hn hf hf'
            rw [escExpandTokens_congr_aux n r2 (by omega) fuel fuel' (by omega)
              (by omega)]
          rw [if_neg h0, if_neg h0]
          by_cases h6 : t = 6
          · rw [if_pos h6, if_pos h6]
            rcases rest with _ | ⟨c, r⟩
            · rfl
            simp only []
            simp only [List.length_cons] at hn hf hf'
            rw [escExpandTokens_congr_aux n r (by omega) fuel fuel' (by omega)
              (by omega)]
          rw [if_neg h6, if_neg h6]
          by_cases h1 : t = 1
          · rw [if_pos h1, if_pos h1]
            rcases rest with _ | ⟨c, r⟩
            · rfl
            simp only []
            simp only [List.length_cons] at hn hf hf'
            rw [escExpandTokens_congr_aux n r (by omega) fuel fuel' (by omega)
              (by omega)]
          rw [if_neg h1, if_neg h1]
          by_cases h7 : t = 7
          · rw [if_pos h7, if_pos h7]
            rcases rest with _ | ⟨c, r⟩
            · rfl
            simp only []
            simp only [List.length_cons] at hn hf hf'
            rw [escExpandTokens_congr_aux n r (by omega) fuel fuel' (by omega)
              (by omega)]
          rw [if_neg h7, if_neg h7]
          rw [escExpandTokens_congr_aux n rest (by omega) fuel fuel' (by omega)
            (by omega)]

lemma escExpandTokens_congr (ts : List ℕ) {fuel fuel' : ℕ}
    (hf : ts.length ≤ fuel) (hf' : ts.length ≤ fuel') :
    escExpandTokens fuel ts = escExpandTokens fuel' ts :=
  escExpandTokens_congr_aux ts.length ts le_rfl fuel fuel' hf hf'

/-- The escape splice at most doubles the stream. -/
lemma escExpand_length_le : ∀ (n : ℕ) (ts : List ℕ), ts.length ≤ n →
    ∀ (fuel : ℕ), ts.length ≤ fuel →
    (escExpandTokens fuel ts).length ≤ 2 * ts.length
  | _, [], _, fuel, _ => by
      have h : escExpandTokens fuel [] = [] := by cases fuel <;> rfl
      simp [h]
  | 0, t :: rest, hn, fuel, hf => by simp at hn
  | n + 1, t :: rest, hn, fuel, hf => by
      match fuel, hf with
      | fuel + 1, hf =>
          simp only [List.length_cons] at hn hf
          rw [escExpandTokens_cons]
          by_cases h0 : t = 0
          · rw [if_pos h0]
            rcases rest with _ | ⟨c, r1⟩
            · simp only []
              simp
            rcases r1 with _ | ⟨d, r2⟩
            · simp only []
              simp
            simp only [List.length_cons] at hn hf ⊢
            have := escExpand_length_le n r2 (by omega) fuel (by omega)
            omega
          rw [if_neg h0]
          by_cases h6 : t = 6
          · rw [if_pos h6]
            rcases rest with _ | ⟨c, r⟩
            · simp only []
              simp
            simp only [List.length_cons] at hn hf ⊢
            have := escExpand_length_le n r (by omega) fuel (by omega)
            omega
          rw [if_neg h6]
          by_cases h1 : t = 1
          · rw [if_pos h1]
            rcases rest with _ | ⟨c, r⟩
            · simp only []
              simp
            simp only [List.length_cons] at hn hf ⊢
            have := escExpand_length_le n r (by omega) fuel (by omega)
            omega
          rw [if_neg h1]
          by_cases h7 : t = 7
          · rw [if_pos h7]
            rcases rest with _ | ⟨c, r⟩
            · simp only []
              simp
            simp only [List.length_cons] at hn hf ⊢
            have := escExpand_length_le n r (by omega) fuel (by omega)
            omega
          rw [if_neg h7]
          have := escExpand_length_le n rest (by omega) fuel (by omega)
          simp only [List.length_cons]
          omega

/-! ### Chunk equations for `escExpand` -/

lemma escExpand_price_chunk (c d : ℕ) (r2 : List ℕ) :
    escExpand (0 :: c :: d :: r2) = 0 :: 1 :: c :: d :: escExpand r2 := by
  rw [escExpand, List.length_cons, escExpandTokens_cons, if_pos rfl]
  simp only []
  rw [escExpandTokens_congr r2 (by simp only [List.length_cons]; omega) le_rfl]
  rfl

lemma escExpand_trade_chunk (c : ℕ) (r : List ℕ) :
    escExpand (6 :: c :: r) = 6 :: 1 :: c :: escExpand r := by
  rw [escExpand, List.length_cons, escExpandTokens_cons,
    if_neg (by norm_num), if_pos rfl]
  simp only []
  rw [escExpandTokens_congr r (by simp only [List.length_cons]; omega) le_rfl]
  rfl

lemma escExpand_payload_chunk (t c : ℕ) (ht : t = 1 ∨ t = 7) (r : List ℕ) :
    escExpand (t :: c :: r) = t :: c :: escExpand r := by
  rcases ht with rfl | rfl
  · rw [escExpand, List.length_cons, escExpandTokens_cons,
      if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    simp only []
    rw [escExpandTokens_congr r (by simp only [List.length_cons]; omega) le_rfl]
    rfl
  · rw [escExpand, List.length_cons, escExpandTokens_cons,
      if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    simp only []
    rw [escExpandTokens_congr r (by simp only [List.length_cons]; omega) le_rfl]
    rfl

lemma escExpand_single_chunk (t : ℕ) (ht : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 6 ∧ t ≠ 7)
    (r : List ℕ) :
    escExpand (t :: r) = t :: escExpand r := by
  obtain ⟨h0, h1, h6, h7⟩ := ht
  rw [escExpand, List.length_cons, escExpandTokens_cons,
    if_neg h0, if_neg h6, if_neg h1, if_neg h7]
  rw [escExpandTokens_congr r (by omega) le_rfl]
  rfl

/-! ### Escape contractions with arbitrary payloads -/

lemma unRpn_price_escape' {c : ℕ} {φ : Sentence}
    (hdec : Encodable.decode (α := Sentence) c = some φ) (d : ℕ)
    (rest : List ℕ) :
    unRpn (0 :: 1 :: c :: d :: rest) = 0 :: Encodable.encode φ :: d :: unRpn rest := by
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
    parseRpn_escape' hdec (d :: rest) (by simp)]
  simp only []
  rw [unRpnTokens_congr rest (by simp only [List.length_cons]; omega) le_rfl]
  rfl

lemma unRpn_price_escape_none {c : ℕ}
    (hdec : Encodable.decode (α := Sentence) c = none) (d : ℕ) (rest : List ℕ) :
    unRpn (0 :: 1 :: c :: d :: rest) = [0, 0] := by
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
    parseRpn_escape_none hdec (d :: rest) _]

lemma unRpn_trade_escape' {c : ℕ} {φ : Sentence}
    (hdec : Encodable.decode (α := Sentence) c = some φ) (rest : List ℕ) :
    unRpn (6 :: 1 :: c :: rest) = 6 :: Encodable.encode φ :: unRpn rest := by
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_neg (by norm_num), if_pos rfl,
    parseRpn_escape' hdec rest (by simp)]
  simp only []
  rw [unRpnTokens_congr rest (by simp only [List.length_cons]; omega) le_rfl]
  rfl

lemma unRpn_trade_escape_none {c : ℕ}
    (hdec : Encodable.decode (α := Sentence) c = none) (rest : List ℕ) :
    unRpn (6 :: 1 :: c :: rest) = [6, 0] := by
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_neg (by norm_num), if_pos rfl,
    parseRpn_escape_none hdec rest _]

/-! ## The escape simulation

The contraction of an escape-expanded stream parses exactly like the original stream —
the emitted canonical codes decode to the same sentences — except that a stream
stranded mid-chunk (truncated) leaves the original at a non-ready parser state where
the contraction has already failed.  Either way the deserialized trades agree. -/

/-- Simulation outcome: identical parser results, or the contraction failed while the
original is stranded at a non-ready state. -/
def SimOut (a b : Option EF.StreamState) : Prop :=
  a = b ∨ (a = none ∧ ∃ st, b = some st ∧ st.1.1 ≠ 0)

lemma decode_zero_sentence : Encodable.decode (α := Sentence) 0 = none := by
  show Formula.ofNat 0 = none
  simp [Formula.ofNat]

lemma foldl_streamStep_none (ts : List ℕ) :
    List.foldl EF.streamStep none ts = none := by
  induction ts with
  | nil => rfl
  | cons t rest ih => simpa [EF.streamStep] using ih

lemma streamReadFrom_unRpn_escExpand : ∀ (n : ℕ) (ts : List ℕ), ts.length ≤ n →
    ∀ (mp : ℕ × Option Sentence) (stack : List EF)
      (trades : List (EF × Sentence)), mp.1 = 0 →
    SimOut
      (EF.streamReadFrom (unRpn (escExpand ts)) (some (mp, (stack, trades))))
      (EF.streamReadFrom ts (some (mp, (stack, trades))))
  | n, [], _, mp, stack, trades, hm => by
      rw [show escExpand [] = [] from rfl, show unRpn [] = [] from rfl]
      exact Or.inl rfl
  | 0, t :: rest, hn, mp, stack, trades, hm => by simp at hn
  | n + 1, t :: rest, hn, mp, stack, trades, hm => by
      obtain ⟨m, pend⟩ := mp
      simp only at hm
      subst hm
      simp only [List.length_cons] at hn
      by_cases h0 : t = 0
      · subst h0
        match rest with
        | [] =>
            rw [show escExpand [0] = [0] from rfl, show unRpn [0] = [0, 0] from rfl]
            refine Or.inr ⟨?_, ((1, none), (stack, trades)), ?_, by norm_num⟩
            · simp [EF.streamReadFrom, EF.streamStep, decode_zero_sentence]
            · simp [EF.streamReadFrom, EF.streamStep]
        | [c] =>
            rw [show escExpand [0, c] = [0, 1, c] from rfl]
            rcases hdec : Encodable.decode (α := Sentence) c with _ | φ
            · rw [show unRpn [0, 1, c] = [0, 0] from by
                rw [unRpn, show ([0, 1, c] : List ℕ).length = 3 from rfl,
                  unRpnTokens_cons, if_pos rfl, parseRpn_escape_none hdec [] _]]
              refine Or.inl ?_
              simp [EF.streamReadFrom, EF.streamStep, decode_zero_sentence, hdec]
            · rw [show unRpn [0, 1, c] = [0, Encodable.encode φ] from by
                rw [unRpn, show ([0, 1, c] : List ℕ).length = 3 from rfl,
                  unRpnTokens_cons, if_pos rfl, parseRpn_escape' hdec [] (by simp)]]
              refine Or.inl ?_
              simp [EF.streamReadFrom, EF.streamStep, hdec, Encodable.encodek]
        | c :: d :: r2 =>
            rw [escExpand_price_chunk]
            rcases hdec : Encodable.decode (α := Sentence) c with _ | φ
            · rw [unRpn_price_escape_none hdec]
              refine Or.inl ?_
              simp [EF.streamReadFrom, EF.streamStep, decode_zero_sentence, hdec,
                foldl_streamStep_none]
            · rw [unRpn_price_escape' hdec]
              have hstep : ∀ ts' : List ℕ, ∀ ctok,
                  Encodable.decode (α := Sentence) ctok = some φ →
                  EF.streamReadFrom (0 :: ctok :: d :: ts')
                      (some ((0, pend), (stack, trades))) =
                    EF.streamReadFrom ts'
                      (some ((0, none), (EF.price φ d :: stack, trades))) := by
                intro ts' ctok hdec'
                simp [EF.streamReadFrom, EF.streamStep, hdec']
              rw [hstep _ c hdec, hstep _ (Encodable.encode φ) (Encodable.encodek φ)]
              simp only [List.length_cons] at hn
              exact streamReadFrom_unRpn_escExpand n r2 (by omega) (0, none)
                (EF.price φ d :: stack) trades rfl
      by_cases h6 : t = 6
      · subst h6
        match rest with
        | [] =>
            rw [show escExpand [6] = [6] from rfl, show unRpn [6] = [6, 0] from rfl]
            refine Or.inr ⟨?_, ((4, none), (stack, trades)), ?_, by norm_num⟩
            · rcases stack with _ | ⟨e, st'⟩ <;>
                simp [EF.streamReadFrom, EF.streamStep, decode_zero_sentence]
            · simp [EF.streamReadFrom, EF.streamStep]
        | c :: r =>
            rw [escExpand_trade_chunk]
            rcases hdec : Encodable.decode (α := Sentence) c with _ | φ
            · rw [unRpn_trade_escape_none hdec]
              refine Or.inl ?_
              rcases stack with _ | ⟨e, st'⟩ <;>
                simp [EF.streamReadFrom, EF.streamStep, decode_zero_sentence, hdec,
                  foldl_streamStep_none]
            · rw [unRpn_trade_escape' hdec]
              rcases stack with _ | ⟨e, st'⟩
              · refine Or.inl ?_
                simp [EF.streamReadFrom, EF.streamStep, hdec, Encodable.encodek,
                  foldl_streamStep_none]
              · have hstep : ∀ ts' : List ℕ, ∀ ctok,
                    Encodable.decode (α := Sentence) ctok = some φ →
                    EF.streamReadFrom (6 :: ctok :: ts')
                        (some ((0, pend), (e :: st', trades))) =
                      EF.streamReadFrom ts'
                        (some ((0, none), (st', trades ++ [(e, φ)]))) := by
                  intro ts' ctok hdec'
                  simp [EF.streamReadFrom, EF.streamStep, hdec']
                rw [hstep _ c hdec, hstep _ (Encodable.encode φ) (Encodable.encodek φ)]
                simp only [List.length_cons] at hn
                exact streamReadFrom_unRpn_escExpand n r (by omega) (0, none)
                  st' (trades ++ [(e, φ)]) rfl
      by_cases h1 : t = 1
      · subst h1
        match rest with
        | [] =>
            rw [show escExpand [1] = [1] from rfl, show unRpn [1] = [1] from rfl]
            exact Or.inl rfl
        | c :: r =>
            rw [escExpand_payload_chunk 1 c (Or.inl rfl),
              unRpn_payload_chunk 1 c (Or.inl rfl)]
            rcases hdec : Encodable.decode (α := ℚ) c with _ | q
            · refine Or.inl ?_
              simp [EF.streamReadFrom, EF.streamStep, hdec, foldl_streamStep_none]
            · have hstep : ∀ ts' : List ℕ,
                  EF.streamReadFrom (1 :: c :: ts')
                      (some ((0, pend), (stack, trades))) =
                    EF.streamReadFrom ts'
                      (some ((0, none), (EF.const q :: stack, trades))) := by
                intro ts'
                simp [EF.streamReadFrom, EF.streamStep, hdec]
              rw [hstep, hstep]
              simp only [List.length_cons] at hn
              exact streamReadFrom_unRpn_escExpand n r (by omega) (0, none)
                (EF.const q :: stack) trades rfl
      by_cases h7 : t = 7
      · subst h7
        match rest with
        | [] =>
            rw [show escExpand [7] = [7] from rfl, show unRpn [7] = [7] from rfl]
            exact Or.inl rfl
        | c :: r =>
            rw [escExpand_payload_chunk 7 c (Or.inr rfl),
              unRpn_payload_chunk 7 c (Or.inr rfl)]
            have hstep : ∀ ts' : List ℕ,
                EF.streamReadFrom (7 :: c :: ts')
                    (some ((0, pend), (stack, trades))) =
                  EF.streamReadFrom ts'
                    (some ((0, none), (EF.var c :: stack, trades))) := by
              intro ts'
              simp [EF.streamReadFrom, EF.streamStep]
            rw [hstep, hstep]
            simp only [List.length_cons] at hn
            exact streamReadFrom_unRpn_escExpand n r (by omega) (0, none)
              (EF.var c :: stack) trades rfl
      · rw [escExpand_single_chunk t ⟨h0, h1, h6, h7⟩,
          unRpn_single_chunk t ⟨h0, h1, h6, h7⟩]
        have hread : ∀ ts' : List ℕ,
            EF.streamReadFrom (t :: ts') (some ((0, pend), (stack, trades))) =
              EF.streamReadFrom ts'
                (EF.streamStep (some ((0, pend), (stack, trades))) t) :=
          fun _ => rfl
        rw [hread, hread]
        rcases hstep : EF.streamStep (some ((0, pend), (stack, trades))) t
          with _ | st'
        · rw [show ∀ ts' : List ℕ, EF.streamReadFrom ts' none = none from
            foldl_streamStep_none,
            show ∀ ts' : List ℕ, EF.streamReadFrom ts' none = none from
            foldl_streamStep_none]
          exact Or.inl rfl
        · have hmode : st'.1.1 = 0 := by
            simp only [EF.streamStep, if_pos rfl] at hstep
            rw [if_neg h0] at hstep
            rw [if_neg h1] at hstep
            by_cases ht2 : t = 2
            · rw [if_pos ht2] at hstep
              match stack, hstep with
              | b :: a :: rest', hstep =>
                  obtain rfl := Option.some.inj hstep
                  rfl
            rw [if_neg ht2] at hstep
            by_cases ht3 : t = 3
            · rw [if_pos ht3] at hstep
              match stack, hstep with
              | b :: a :: rest', hstep =>
                  obtain rfl := Option.some.inj hstep
                  rfl
            rw [if_neg ht3] at hstep
            by_cases ht4 : t = 4
            · rw [if_pos ht4] at hstep
              match stack, hstep with
              | b :: a :: rest', hstep =>
                  obtain rfl := Option.some.inj hstep
                  rfl
            rw [if_neg ht4] at hstep
            by_cases ht5 : t = 5
            · rw [if_pos ht5] at hstep
              match stack, hstep with
              | a :: rest', hstep =>
                  obtain rfl := Option.some.inj hstep
                  rfl
            rw [if_neg ht5] at hstep
            rw [if_neg h6] at hstep
            rw [if_neg h7] at hstep
            by_cases ht8 : t = 8
            · rw [if_pos ht8] at hstep
              match stack, hstep with
              | body :: x :: rest', hstep =>
                  obtain rfl := Option.some.inj hstep
                  rfl
            rw [if_neg ht8] at hstep
            exact absurd hstep (by simp)
          obtain ⟨⟨m', pend'⟩, ⟨stack', trades'⟩⟩ := st'
          simp only at hmode
          exact streamReadFrom_unRpn_escExpand n rest (by omega) (m', pend')
            stack' trades' hmode


/-- **Escape-splice correctness**: the contracted escape expansion deserializes to the
same trades as the original stream. -/
lemma deserializeTrades_unRpn_escExpand (ts : List ℕ) :
    deserializeTrades (unRpn (escExpand ts)) = deserializeTrades ts := by
  have h := streamReadFrom_unRpn_escExpand ts.length ts le_rfl (0, none) [] [] rfl
  unfold deserializeTrades
  rcases h with h | ⟨hnone, st, hsome, hmode⟩
  · rw [show EF.streamInitial = ((0, none), ([], [])) from rfl, h]
  · rw [show EF.streamInitial = ((0, none), ([], [])) from rfl, hnone, hsome]
    rcases st with ⟨⟨m, pend⟩, ⟨stack, trades⟩⟩
    simp only at hmode
    match m, hmode with
    | m + 1, _ => cases pend <;> cases stack <;> rfl

/-- **Escape-splice strategy correctness**: the contracted escape expansion validates
to the same day-`n` strategy. -/
lemma strategyOfTokens_unRpn_escExpand (n : ℕ) (ts : List ℕ) :
    strategyOfTokens n (unRpn (escExpand ts)) = strategyOfTokens n ts := by
  unfold strategyOfTokens
  rw [deserializeTrades_unRpn_escExpand]

/-! ## The symbol-metered emission model (`Tok₃`)

A `Tok₃` trader emits a digit stream whose undigitized tokens form an RPN-expanded
strategy stream; the decode contracts sentence blocks (`unRpn`) before validation.
Poly digit length now meters formula *symbols*: sentences may be arbitrarily deep and
skewed.  The escape tag keeps both earlier models included by verbatim splice. -/

/-- The total trader denoted by two digit-emission programs under a day clock, with
Polish sentence blocks contracted before validation.
Paper node: `def:trader`, `def:ec` -/
def clockedTrader₃ (lengthCode tokenCode : Nat.Partrec.Code) (clock : ℕ → ℕ) :
    Trader where
  strat n := strategyOfTokens n (unRpn (undigitize
    (clockedTokens lengthCode tokenCode (clock n) n)))

/-- **The symbol-metered efficient-computability class** (`def:ec`, `Tok₃`): two
programs under one polynomial clock emit the digit stream of an RPN-expanded strategy
serialization.
Paper node: `def:ec` -/
def EfficientlyComputableTok₃ (Tr : Trader) : Prop :=
  ∃ (lengthCode tokenCode : Nat.Partrec.Code) (a k : ℕ),
    clockedTrader₃ lengthCode tokenCode (fun n => a * (n + 1) ^ k + a) = Tr

/-! ### The escape-slot automaton

Sentence-slot positions of a flat strategy stream, as a small forward automaton:
mode `0` = base (tags `0`/`6` open sentence slots, `1`/`7` opaque payloads), mode `1`
= price sentence slot (day follows), mode `2` = price day, mode `3` = trade sentence
slot, mode `4` = opaque payload.  Slots are modes `1` and `3`.  Base transitions test
only tags `≤ 7`, so the automaton factors through the digit clamp. -/

def escModeStep (m t : ℕ) : ℕ :=
  if m = 0 then
    if t = 0 then 1
    else if t = 6 then 3
    else if t = 1 then 4
    else if t = 7 then 4
    else 0
  else if m = 1 then 2
  else 0

def escModeList (ts : List ℕ) : ℕ := ts.foldl escModeStep 0

lemma escModeStep_le (m t : ℕ) : escModeStep m t ≤ 4 := by
  rw [escModeStep]
  split_ifs <;> omega

lemma escModeList_le (ts : List ℕ) : escModeList ts ≤ 4 := by
  rw [escModeList]
  rcases ts.eq_nil_or_concat with rfl | ⟨l, t, rfl⟩
  · simp
  · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact escModeStep_le _ _

lemma escModeList_snoc (ts : List ℕ) (t : ℕ) :
    escModeList (ts ++ [t]) = escModeStep (escModeList ts) t := by
  rw [escModeList, List.foldl_append, List.foldl_cons, List.foldl_nil, escModeList]

lemma escModeStep_clamp (m t : ℕ) :
    escModeStep m (min t 9) = escModeStep m t := by
  by_cases h : t ≤ 9
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega : 9 ≤ t)]
    rw [escModeStep, escModeStep]
    split_ifs <;> omega

/-! ### The per-token fold form of the escape splice -/

/-- `escExpand` as a per-token fold over the slot automaton. -/
def escExpandFold : ℕ → List ℕ → List ℕ
  | _, [] => []
  | m, t :: rest =>
      (if m = 1 ∨ m = 3 then [1, t] else [t]) ++ escExpandFold (escModeStep m t) rest

lemma escExpandFold_eq_escExpand : ∀ (n : ℕ) (ts : List ℕ), ts.length ≤ n →
    escExpandFold 0 ts = escExpand ts
  | _, [], _ => rfl
  | 0, t :: rest, hn => by simp at hn
  | n + 1, t :: rest, hn => by
      simp only [List.length_cons] at hn
      by_cases h0 : t = 0
      · subst h0
        match rest with
        | [] => rfl
        | [c] =>
            show escExpandFold 0 [0, c] = escExpand [0, c]
            rw [show escExpand [0, c] = [0, 1, c] from rfl]
            rfl
        | c :: d :: r2 =>
            rw [escExpand_price_chunk]
            show ([0] ++ escExpandFold 1 (c :: d :: r2)) = _
            rw [show escExpandFold 1 (c :: d :: r2) =
              [1, c] ++ escExpandFold 2 (d :: r2) from rfl]
            rw [show escExpandFold 2 (d :: r2) = [d] ++ escExpandFold 0 r2 from rfl]
            simp only [List.length_cons] at hn
            rw [escExpandFold_eq_escExpand n r2 (by omega)]
            rfl
      by_cases h6 : t = 6
      · subst h6
        match rest with
        | [] => rfl
        | c :: r =>
            rw [escExpand_trade_chunk]
            show ([6] ++ escExpandFold 3 (c :: r)) = _
            rw [show escExpandFold 3 (c :: r) = [1, c] ++ escExpandFold 0 r from rfl]
            simp only [List.length_cons] at hn
            rw [escExpandFold_eq_escExpand n r (by omega)]
            rfl
      by_cases h1 : t = 1
      · subst h1
        match rest with
        | [] => rfl
        | c :: r =>
            rw [escExpand_payload_chunk 1 c (Or.inl rfl)]
            show ([1] ++ escExpandFold 4 (c :: r)) = _
            rw [show escExpandFold 4 (c :: r) = [c] ++ escExpandFold 0 r from rfl]
            simp only [List.length_cons] at hn
            rw [escExpandFold_eq_escExpand n r (by omega)]
            rfl
      by_cases h7 : t = 7
      · subst h7
        match rest with
        | [] => rfl
        | c :: r =>
            rw [escExpand_payload_chunk 7 c (Or.inr rfl)]
            show ([7] ++ escExpandFold 4 (c :: r)) = _
            rw [show escExpandFold 4 (c :: r) = [c] ++ escExpandFold 0 r from rfl]
            simp only [List.length_cons] at hn
            rw [escExpandFold_eq_escExpand n r (by omega)]
            rfl
      · rw [escExpand_single_chunk t ⟨h0, h1, h6, h7⟩]
        show ((if (0 : ℕ) = 1 ∨ (0 : ℕ) = 3 then [1, t] else [t]) ++
          escExpandFold (escModeStep 0 t) rest) = _
        rw [if_neg (by norm_num),
          show escModeStep 0 t = 0 by
            rw [escModeStep, if_pos rfl, if_neg h0, if_neg h6, if_neg h1, if_neg h7]]
        rw [escExpandFold_eq_escExpand n rest (by omega)]
        rfl

lemma escExpandFold_append (m : ℕ) (xs ys : List ℕ) :
    escExpandFold m (xs ++ ys) =
      escExpandFold m xs ++ escExpandFold (xs.foldl escModeStep m) ys := by
  induction xs generalizing m with
  | nil => rfl
  | cons t rest ih =>
      simp only [List.cons_append, escExpandFold, List.foldl_cons]
      rw [ih]
      simp [List.append_assoc]

#print axioms parseRpn_rpn
#print axioms parseRpn_escape
#print axioms rpn_injective
#print axioms unRpn_price_chunk
#print axioms unRpn_trade_chunk
#print axioms strategyOfTokens_unRpn_escExpand
#print axioms escExpandFold_eq_escExpand

end LogicalInduction
