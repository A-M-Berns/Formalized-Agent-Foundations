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

#print axioms parseRpn_rpn
#print axioms parseRpn_escape
#print axioms rpn_injective
#print axioms unRpn_price_chunk
#print axioms unRpn_trade_chunk

end LogicalInduction
