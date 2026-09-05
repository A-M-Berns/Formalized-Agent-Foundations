import LogicalInduction.Framework.Criterion

/-!
# Polish-notation sentence blocks: the pure coding

Renders `def:ec`'s write-out metering on sentence slots.  Where a sentence travels as a
single `Encodable` pair-code token its bit size tracks the formula's symbol count only up
to balance — skewed formulas inflate exponentially — so a sentence block is instead a
Polish-notation symbol run, one token per formula symbol, and a polynomial token count
meters formula *symbols* rather than the magnitude of a single pair code.  This is a cost
measure on the emission surface; the relation of the certificate class to the paper's
runtime class is `EfficientlyComputable.toMachine` (`dd:fuel`).

Symbol alphabet of a sentence block:

* `0` — `⊥`;
* `1` — **escape**: the next token is a literal `Encodable` pair code for the whole
  subformula, or, as `[1, 0, …]`, opens a structured paper-prime block;
* `2` / `3` / `4` — `➝` / `⋏` / `⋎`, each followed by its two operands;
* `t + 5` — atom `t`.

Prefix order is forward self-delimiting: a pending-formula counter starts at `1`, leaves
decrement it, binary tags increment it, and the block ends exactly when it reaches `0` —
every proper prefix keeps it positive.

The grammar objects themselves — `rpn`, `parseRpn`, `parseRpnLegacy`, `unRpn`,
`unRpnTokens` and `parseStructuredPaperPrime(C)` — are defined in
`Framework/Criterion.lean`, beside the serializers they meter; this module is their lemma
corpus.  What it defines of its own is the vocabulary built on top: `UnRpnTransparent` and
`UnRpnContractsTo` (the splice relations), `EF.priceFree`, the escape splice
(`escExpandTokens`, `escExpand`, `escExpandFold`), the slot automaton (`escModeStep`,
`escModeList`), `SimOut`, and the code-level mirrors `parseRpnC` / `unRpnTokensC`.

Main results and where they are consumed: the block algebra `parseRpn_rpn`,
`parseRpn_escape`, `parseRpn_append`, `parseRpn_mono` and `parseRpn_block_head` feeds the
`RpnSentenceCodes` combinators of `Framework/RpnSplice.lean`; `rpn_injective` is the
round-trip; `unRpn_price_chunk_block` / `unRpn_trade_chunk_block` and the
`UnRpnContractsTo.*` laws feed `Framework/RpnSplice.lean` and `Framework/RpnEmission.lean`;
`strategyOfTokens_unRpn_escExpand` is the escape simulation theorem; and
`escExpandFold_eq_escExpand`, `escExpandFold_append` and the `escModeList_*` facts are what
`Framework/RpnEmission.lean` folds over.  `parseRpnC_eq` / `unRpnTokensC_eq` tie the
code-level mirrors to the originals, and their primitive recursiveness is packaged in
`Framework/RpnComputation.lean`.

An efficiently computable trader emits a digit stream whose undigitized tokens form an
RPN-expanded strategy stream, and the decode contracts sentence blocks (`unRpn`) before
validation, so poly digit length meters formula *symbols* and sentences may be arbitrarily
deep and skewed.  The escape tag `1` is what makes the token- and digit-metered models
(`EfficientlyComputableTok`, `EfficientlyComputableDigit`) verbatim splices into this one.

Paper node: `def:ec` (token-metered sentence slots — a subclass rendering, not the node's
own class).
-/

namespace LogicalInduction

open LO.Propositional

/-! ## The block parser

`parseRpn fuel ts` reads one sentence block from the front of `ts` and returns the
parsed sentence together with the unread suffix.  Fuel bounds the recursion; any
`fuel ≥ ts.length` is enough (each call consumes at least one token). -/

@[simp] lemma parseRpn_zero (ts : List ℕ) : parseRpn 0 ts = none := rfl

@[simp] lemma parseRpn_nil (fuel : ℕ) : parseRpn (fuel + 1) [] = none := rfl

lemma parseRpn_cons (fuel t : ℕ) (rest : List ℕ) :
    parseRpn (fuel + 1) (t :: rest) =
      if t = 0 then some (Formula.falsum, rest)
      else if t = 1 then
        match rest with
        | 0 :: payload => parseStructuredPaperPrime payload
        | c :: tail => (Encodable.decode (α := Sentence) c).map fun φ => (φ, tail)
        | [] => none
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

/-- Every stream accepted by the unstructured fragment has exactly the same parse under
the full grammar: the only new dispatch prefix is `[1, 0]`, and sentence code `0` decodes
to nothing in the fragment. -/
lemma parseRpn_of_legacy : ∀ {fuel : ℕ} {ts : List ℕ} {out},
    parseRpnLegacy fuel ts = some out → parseRpn fuel ts = some out := by
  intro fuel
  induction fuel with
  | zero => intro ts out h; simp [parseRpnLegacy] at h
  | succ fuel ih =>
      intro ts out h
      rcases ts with _ | ⟨t, rest⟩
      · simp [parseRpnLegacy] at h
      simp only [parseRpnLegacy] at h
      rw [parseRpn_cons]
      by_cases h0 : t = 0
      · simpa [h0] using h
      rw [if_neg h0] at h ⊢
      by_cases h1 : t = 1
      · rw [if_pos h1] at h ⊢
        rcases rest with _ | ⟨c, tail⟩
        · simp at h
        cases c with
        | zero =>
            have hz : Encodable.decode (α := Sentence) 0 = none := by
              show Formula.ofNat 0 = none
              simp [Formula.ofNat]
            simp [hz] at h
        | succ c => simpa using h
      rw [if_neg h1] at h ⊢
      have hbin : ∀ (mk : Sentence → Sentence → Sentence),
          ((parseRpnLegacy fuel rest).bind fun p =>
            (parseRpnLegacy fuel p.2).bind fun q => some (mk p.1 q.1, q.2)) = some out →
          ((parseRpn fuel rest).bind fun p =>
            (parseRpn fuel p.2).bind fun q => some (mk p.1 q.1, q.2)) = some out := by
        intro mk hb
        rcases hp : parseRpnLegacy fuel rest with _ | p
        · simp [hp] at hb
        rw [hp] at hb
        simp only [Option.bind_some] at hb
        rw [ih hp]
        simp only [Option.bind_some]
        rcases hq : parseRpnLegacy fuel p.2 with _ | q
        · simp [hq] at hb
        rw [hq] at hb
        simp only [Option.bind_some] at hb
        rw [ih hq]
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
      simpa [h4] using h

/-! ### Fragment-grammar parser facts

The unstructured fragment — tags `0`-`4` and the two-token escape — is the sub-grammar the
freeze compiler's positional matcher is scoped to, because a structured paper-prime leaf
has no constant-depth positional pattern (`Construction/Witnesses/RpnFreeze.lean`).  Its
characterization therefore needs the fragment analogues of the parse lemmas, and
`parseRpn_of_legacy` carries every fragment parse into the full grammar unchanged. -/

lemma parseRpnLegacy_cons (fuel t : ℕ) (rest : List ℕ) :
    parseRpnLegacy (fuel + 1) (t :: rest) =
      if t = 0 then some (Formula.falsum, rest)
      else if t = 1 then
        rest.head?.bind fun c =>
          (Encodable.decode (α := Sentence) c).map fun φ => (φ, rest.tail)
      else if t = 2 then
        (parseRpnLegacy fuel rest).bind fun p =>
          (parseRpnLegacy fuel p.2).bind fun q => some (Formula.imp p.1 q.1, q.2)
      else if t = 3 then
        (parseRpnLegacy fuel rest).bind fun p =>
          (parseRpnLegacy fuel p.2).bind fun q => some (Formula.and p.1 q.1, q.2)
      else if t = 4 then
        (parseRpnLegacy fuel rest).bind fun p =>
          (parseRpnLegacy fuel p.2).bind fun q => some (Formula.or p.1 q.1, q.2)
      else some (Formula.atom (t - 5), rest) := rfl

lemma parseRpnLegacy_mono : ∀ {fuel fuel' : ℕ} (ts : List ℕ) {out : Sentence × List ℕ},
    fuel ≤ fuel' → parseRpnLegacy fuel ts = some out → parseRpnLegacy fuel' ts = some out := by
  intro fuel
  induction fuel with
  | zero => intro fuel' ts out _ h; simp [parseRpnLegacy] at h
  | succ fuel ih =>
      intro fuel' ts out hle h
      match fuel', hle with
      | fuel' + 1, hle =>
          have hle' : fuel ≤ fuel' := by omega
          match ts with
          | [] => simp [parseRpnLegacy] at h
          | t :: rest =>
              rw [parseRpnLegacy_cons] at h ⊢
              by_cases h0 : t = 0
              · rwa [if_pos h0] at h ⊢
              rw [if_neg h0] at h ⊢
              by_cases h1 : t = 1
              · rwa [if_pos h1] at h ⊢
              rw [if_neg h1] at h ⊢
              have hbin : ∀ (mk : Sentence → Sentence → Sentence),
                  (parseRpnLegacy fuel rest).bind
                    (fun p => (parseRpnLegacy fuel p.2).bind fun q =>
                      some (mk p.1 q.1, q.2)) = some out →
                  (parseRpnLegacy fuel' rest).bind
                    (fun p => (parseRpnLegacy fuel' p.2).bind fun q =>
                      some (mk p.1 q.1, q.2)) = some out := by
                intro mk hb
                rcases hp1 : parseRpnLegacy fuel rest with _ | ⟨φ1, r1⟩
                · rw [hp1] at hb
                  simp at hb
                rw [hp1] at hb
                simp only [Option.bind_some] at hb
                rcases hp2 : parseRpnLegacy fuel r1 with _ | ⟨φ2, r2⟩
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

/-- **Parse extension** (self-delimitation): a successful parse is unchanged by
appending a suffix to the input — the consumed block determines the result. -/
lemma parseRpnLegacy_append : ∀ (fuel : ℕ) (ts : List ℕ) {φ : Sentence} {r : List ℕ}
    (tail : List ℕ), parseRpnLegacy fuel ts = some (φ, r) →
    parseRpnLegacy fuel (ts ++ tail) = some (φ, r ++ tail) := by
  intro fuel
  induction fuel with
  | zero => intro ts φ r tail h; simp [parseRpnLegacy] at h
  | succ fuel ih =>
      intro ts φ r tail h
      match ts with
      | [] => simp [parseRpnLegacy] at h
      | t :: rest =>
          rw [parseRpnLegacy_cons] at h
          rw [List.cons_append, parseRpnLegacy_cons]
          by_cases h0 : t = 0
          · rw [if_pos h0] at h ⊢
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
            rfl
          · rw [if_neg h0] at h ⊢
            by_cases h1 : t = 1
            · rw [if_pos h1] at h ⊢
              match rest with
              | [] => simp at h
              | c :: rest' =>
                  simp only [List.cons_append, List.head?_cons, Option.bind_some] at h ⊢
                  cases hdec : Encodable.decode (α := Sentence) c with
                  | none => rw [hdec] at h; simp at h
                  | some ψ =>
                      rw [hdec] at h
                      simp only [Option.map_some, List.tail_cons] at h ⊢
                      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
                      rfl
            · rw [if_neg h1] at h ⊢
              have hbin : ∀ (mk : Sentence → Sentence → Sentence),
                  ((parseRpnLegacy fuel rest).bind fun p =>
                    (parseRpnLegacy fuel p.2).bind fun q =>
                      some (mk p.1 q.1, q.2)) = some (φ, r) →
                  ((parseRpnLegacy fuel (rest ++ tail)).bind fun p =>
                    (parseRpnLegacy fuel p.2).bind fun q =>
                      some (mk p.1 q.1, q.2)) = some (φ, r ++ tail) := by
                intro mk hh
                cases hp : parseRpnLegacy fuel rest with
                | none => rw [hp] at hh; simp at hh
                | some p =>
                    rw [hp] at hh
                    simp only [Option.bind_some] at hh
                    cases hq : parseRpnLegacy fuel p.2 with
                    | none => rw [hq] at hh; simp at hh
                    | some q =>
                        rw [hq] at hh
                        simp only [Option.bind_some] at hh
                        obtain ⟨h1', h2'⟩ := Prod.mk.injEq .. ▸ Option.some.inj hh
                        rw [ih rest tail hp]
                        simp only [Option.bind_some]
                        rw [ih p.2 tail hq]
                        simp only [Option.bind_some]
                        rw [h1', h2']
              by_cases h2 : t = 2
              · rw [if_pos h2] at h ⊢; exact hbin _ h
              · rw [if_neg h2] at h ⊢
                by_cases h3 : t = 3
                · rw [if_pos h3] at h ⊢; exact hbin _ h
                · rw [if_neg h3] at h ⊢
                  by_cases h4 : t = 4
                  · rw [if_pos h4] at h ⊢; exact hbin _ h
                  · rw [if_neg h4] at h ⊢
                    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
                    rfl

/-- A complete self-delimiting block placed at the head of a longer stream parses to
its sentence with exactly the appended tail as remainder, at any fuel covering the
stream. -/
lemma parseRpnLegacy_block_head {b : List ℕ} {φ : Sentence}
    (hb : parseRpnLegacy b.length b = some (φ, [])) (tail : List ℕ) {fuel : ℕ}
    (hfuel : b.length ≤ fuel) :
    parseRpnLegacy fuel (b ++ tail) = some (φ, tail) := by
  have := parseRpnLegacy_append b.length b tail hb
  simpa using parseRpnLegacy_mono (b ++ tail) hfuel this
/-- Escape parse with an arbitrary decodable payload. -/
lemma parseRpnLegacy_escape' {c : ℕ} {φ : Sentence}
    (hdec : Encodable.decode (α := Sentence) c = some φ)
    (rest : List ℕ) {fuel : ℕ} (hfuel : 1 ≤ fuel) :
    parseRpnLegacy fuel (1 :: c :: rest) = some (φ, rest) := by
  match fuel, hfuel with
  | fuel + 1, _ =>
      rw [parseRpnLegacy_cons, if_neg (by omega), if_pos rfl]
      simp [hdec]

lemma parseRpnLegacy_strip : ∀ (fuel : ℕ) (ts : List ℕ) {φ : Sentence} {rest : List ℕ},
    parseRpnLegacy fuel ts = some (φ, rest) →
    ∃ blk, ts = blk ++ rest ∧ parseRpnLegacy blk.length blk = some (φ, []) := by
  intro fuel
  induction fuel with
  | zero => intro ts φ rest h; simp [parseRpnLegacy] at h
  | succ fuel ih =>
      intro ts φ rest h
      match ts with
      | [] => simp [parseRpnLegacy] at h
      | t :: ts' =>
          rw [parseRpnLegacy_cons] at h
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
                        parseRpnLegacy_cons]
                      simp [hdec]
            · rw [if_neg h1] at h
              have hbin : ∀ (mk : Sentence → Sentence → Sentence),
                  ((parseRpnLegacy fuel ts').bind fun p =>
                    (parseRpnLegacy fuel p.2).bind fun q =>
                      some (mk p.1 q.1, q.2)) = some (φ, rest) →
                  ((t = 2 ∧ mk = LO.Propositional.Formula.imp) ∨
                    (t = 3 ∧ mk = LO.Propositional.Formula.and) ∨
                    (t = 4 ∧ mk = LO.Propositional.Formula.or)) →
                  ∃ blk, t :: ts' = blk ++ rest ∧
                    parseRpnLegacy blk.length blk = some (φ, []) := by
                intro mk hh ht
                cases hp : parseRpnLegacy fuel ts' with
                | none => rw [hp] at hh; simp at hh
                | some p =>
                    rw [hp] at hh
                    simp only [Option.bind_some] at hh
                    cases hq : parseRpnLegacy fuel p.2 with
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
                        have hb1 : parseRpnLegacy (blk₁.length + blk₂.length)
                            (blk₁ ++ blk₂) = some (p.1, blk₂) :=
                          parseRpnLegacy_block_head hblk₁ blk₂ (by omega)
                        have hb2 : parseRpnLegacy (blk₁.length + blk₂.length) blk₂ =
                            some (q.1, []) :=
                          parseRpnLegacy_mono blk₂ (by omega) hblk₂
                        rw [List.cons_append,
                          show (t :: (blk₁ ++ blk₂)).length =
                            (blk₁.length + blk₂.length) + 1 by simp,
                          parseRpnLegacy_cons, if_neg h0, if_neg h1]
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
                      parseRpnLegacy_cons, if_neg h0, if_neg h1, if_neg h2, if_neg h3,
                      if_neg h4]

lemma readStructuredLength_suffix {ts : List ℕ} {n : ℕ} {rest : List ℕ}
    (h : readStructuredLength ts = some (n, rest)) : rest <:+ ts := by
  induction ts generalizing n rest with
  | nil => simp [readStructuredLength] at h
  | cons t ts ih =>
      by_cases h0 : t = 0
      · subst t
        simp only [readStructuredLength, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact List.suffix_cons 0 ts
      by_cases h1 : t = 1
      · subst t
        simp only [readStructuredLength] at h
        rcases hr : readStructuredLength ts with _ | ⟨m, r⟩
        · simp [hr] at h
        · simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact (ih hr).trans (List.suffix_cons 1 ts)
      · simp [readStructuredLength, h0, h1] at h

lemma readStructuredLength_append {ts : List ℕ} {n : ℕ} {rest : List ℕ}
    (h : readStructuredLength ts = some (n, rest)) (tail : List ℕ) :
    readStructuredLength (ts ++ tail) = some (n, rest ++ tail) := by
  induction ts generalizing n rest with
  | nil => simp [readStructuredLength] at h
  | cons t ts ih =>
      by_cases h0 : t = 0
      · subst t
        simp only [readStructuredLength, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      by_cases h1 : t = 1
      · subst t
        simp only [readStructuredLength] at h ⊢
        rcases hr : readStructuredLength ts with _ | ⟨m, r⟩
        · simp [hr] at h
        · simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          change (readStructuredLength (ts ++ tail)).map (fun p => (p.1 + 1, p.2)) = _
          rw [ih hr]
          rfl
      · simp [readStructuredLength, h0, h1] at h

public lemma parseStructuredNat_suffix : ∀ {fuel : ℕ} {ts : List ℕ} {n : ℕ}
    {rest : List ℕ}, parseStructuredNat fuel ts = some (n, rest) → rest <:+ ts := by
  intro fuel
  induction fuel with
  | zero => intro ts n rest h; simp [parseStructuredNat] at h
  | succ fuel ih =>
      intro ts n rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [parseStructuredNat] at h
      rw [parseStructuredNat] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact List.suffix_cons t ts
      all_goals
        rcases hp : parseStructuredNat fuel ts with _ | p <;> simp [hp] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        exact (ih hp).trans (List.suffix_cons t ts)

public lemma parseStructuredArithmeticTerm_suffix : ∀ {fuel depth : ℕ} {ts : List ℕ}
    {code : ℕ} {rest : List ℕ},
      parseStructuredArithmeticTerm fuel depth ts = some (code, rest) → rest <:+ ts := by
  intro fuel
  induction fuel with
  | zero => intro depth ts code rest h; simp [parseStructuredArithmeticTerm] at h
  | succ fuel ih =>
      intro depth ts code rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [parseStructuredArithmeticTerm] at h
      rw [parseStructuredArithmeticTerm] at h
      split_ifs at h
      · rcases hp : parseStructuredNat fuel ts with _ | p <;> simp [hp] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        exact (parseStructuredNat_suffix hp).trans (List.suffix_cons t ts)
      · rcases hp : parseStructuredNat fuel ts with _ | p <;> simp [hp] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        exact (parseStructuredNat_suffix hp).trans (List.suffix_cons t ts)
      · obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact List.suffix_cons t ts
      · obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact List.suffix_cons t ts
      all_goals
        rcases hp : parseStructuredArithmeticTerm fuel 0 ts with _ | p <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticTerm fuel 0 p.2 with _ | q <;> simp [hq] at h
        rcases h with ⟨a, hqrest, -⟩
        have hrest : q.2 = rest := by
          rw [hqrest]
        subst rest
        exact ((ih hq).trans (ih hp)).trans (List.suffix_cons t ts)

public lemma parseStructuredArithmeticFormula_suffix :
    ∀ {fuel depth : ℕ} {ts : List ℕ} {code : ℕ} {rest : List ℕ},
      parseStructuredArithmeticFormula fuel depth ts = some (code, rest) → rest <:+ ts := by
  intro fuel
  induction fuel with
  | zero =>
      intro depth ts code rest h
      simp [parseStructuredArithmeticFormula] at h
  | succ fuel ih =>
      intro depth ts code rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [parseStructuredArithmeticFormula] at h
      rw [parseStructuredArithmeticFormula] at h
      by_cases h9 : t = 9
      · rw [if_pos h9] at h
        obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact List.suffix_cons t ts
      rw [if_neg h9] at h
      by_cases h10 : t = 10
      · rw [if_pos h10] at h
        obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact List.suffix_cons t ts
      rw [if_neg h10] at h
      by_cases hrel : t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14
      · rw [if_pos hrel] at h
        rcases hp : parseStructuredArithmeticTerm fuel 0 ts with _ | p
        · simp [hp] at h
        simp only [hp, Option.bind_some] at h
        rcases hq : parseStructuredArithmeticTerm fuel 0 p.2 with _ | q
        · simp [hq] at h
        simp only [hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        exact ((parseStructuredArithmeticTerm_suffix hq).trans
          (parseStructuredArithmeticTerm_suffix hp)).trans (List.suffix_cons t ts)
      rw [if_neg hrel] at h
      by_cases hbin : t = 15 ∨ t = 16
      · rw [if_pos hbin] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p
        · simp [hp] at h
        simp only [hp, Option.bind_some] at h
        rcases hq : parseStructuredArithmeticFormula fuel 0 p.2 with _ | q
        · simp [hq] at h
        simp only [hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        exact ((ih hq).trans (ih hp)).trans (List.suffix_cons t ts)
      rw [if_neg hbin] at h
      by_cases hquant : t = 17 ∨ t = 18
      · rw [if_pos hquant] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p
        · simp [hp] at h
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        exact (ih hp).trans (List.suffix_cons t ts)
      rw [if_neg hquant] at h
      by_cases h20 : t = 20
      · rw [if_pos h20] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p
        · simp [hp] at h
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        exact (ih hp).trans (List.suffix_cons t ts)
      rw [if_neg h20] at h
      by_cases h21 : t = 21
      · rw [if_pos h21] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p
        · simp [hp] at h
        simp only [hp, Option.bind_some] at h
        rcases hq : parseStructuredArithmeticFormula fuel 0 p.2 with _ | q
        · simp [hq] at h
        simp only [hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        exact ((ih hq).trans (ih hp)).trans (List.suffix_cons t ts)
      rw [if_neg h21] at h
      by_cases h22 : t = 22
      · rw [if_pos h22] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p
        · simp [hp] at h
        simp only [hp, Option.bind_some] at h
        rcases hq : parseStructuredArithmeticFormula fuel 0 p.2 with _ | q
        · simp [hq] at h
        simp only [hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        exact ((ih hq).trans (ih hp)).trans (List.suffix_cons t ts)
      rw [if_neg h22] at h
      simp at h

lemma parseStructuredPaperPrime_tail_suffix {polarity : ℕ} {framed : List ℕ}
    {φ : Sentence} {rest : List ℕ}
    (h : parseStructuredPaperPrime (polarity :: framed) = some (φ, rest)) :
    rest <:+ framed := by
  rw [parseStructuredPaperPrime] at h
  split at h <;> try contradiction
  rcases hr : readStructuredLength framed with _ | ⟨n, payload⟩
  · simp [hr] at h
  rw [hr] at h
  simp only [Option.bind_some] at h
  split at h <;> try contradiction
  rcases hp : parseStructuredArithmeticFormula n 0 (payload.take n) with _ | ⟨code, r⟩
  · simp [hp] at h
  rw [hp] at h
  rcases r with _ | ⟨x, xs⟩
  · change (if List.getD payload n 0 = 19 then
        some (Formula.atom (Nat.pair 5 (Nat.pair polarity code)), payload.drop (n + 1))
      else none) = some (φ, rest) at h
    by_cases hterm : payload.getD n 0 = 19
    · rw [if_pos hterm] at h
      obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      exact (List.drop_suffix (n + 1) payload).trans (readStructuredLength_suffix hr)
    · rw [if_neg hterm] at h
      contradiction
  · simp at h

lemma parseStructuredPaperPrime_suffix {ts : List ℕ} {φ : Sentence} {rest : List ℕ}
    (h : parseStructuredPaperPrime ts = some (φ, rest)) : rest <:+ ts := by
  rcases ts with _ | ⟨polarity, framed⟩
  · simp [parseStructuredPaperPrime] at h
  exact (parseStructuredPaperPrime_tail_suffix h).trans
    (List.suffix_cons polarity framed)

lemma parseStructuredPaperPrime_length_lt {ts : List ℕ} {φ : Sentence} {rest : List ℕ}
    (h : parseStructuredPaperPrime ts = some (φ, rest)) : rest.length < ts.length := by
  rcases ts with _ | ⟨t, ts⟩
  · simp [parseStructuredPaperPrime] at h
  have hle := (parseStructuredPaperPrime_tail_suffix h).length_le
  simp only [List.length_cons]
  omega

lemma parseStructuredPaperPrime_append {ts : List ℕ} {φ : Sentence} {rest : List ℕ}
    (tail : List ℕ) (h : parseStructuredPaperPrime ts = some (φ, rest)) :
    parseStructuredPaperPrime (ts ++ tail) = some (φ, rest ++ tail) := by
  rcases ts with _ | ⟨polarity, framed⟩
  · simp [parseStructuredPaperPrime] at h
  rw [parseStructuredPaperPrime] at h
  split at h <;> try contradiction
  rename_i hpol
  rcases hr : readStructuredLength framed with _ | ⟨n, payload⟩
  · simp [hr] at h
  rw [hr] at h
  simp only [Option.bind_some] at h
  split at h <;> try contradiction
  rename_i hlen
  rcases hp : parseStructuredArithmeticFormula n 0 (payload.take n) with _ | ⟨code, r⟩
  · simp [hp] at h
  rw [hp] at h
  rcases r with _ | ⟨x, xs⟩
  · change (if List.getD payload n 0 = 19 then
        some (Formula.atom (Nat.pair 5 (Nat.pair polarity code)), payload.drop (n + 1))
      else none) = some (φ, rest) at h
    by_cases hterm : payload.getD n 0 = 19
    · rw [if_pos hterm] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      have hnlt : n < payload.length := by
        have hne : n ≠ payload.length := by
          intro heq
          subst n
          simpa [List.getD] using hterm
        omega
      simp only [List.cons_append, parseStructuredPaperPrime, hpol, ↓reduceIte]
      rw [readStructuredLength_append hr tail]
      simp only [Option.bind_some]
      have hlen' : n ≤ payload.length + tail.length := by omega
      rw [if_pos (by simpa using hlen')]
      rw [List.take_append_of_le_length hlen, hp]
      simp only
      rw [List.getD_append _ _ _ _ hnlt, hterm, if_pos rfl,
        List.drop_append_of_le_length (by omega : n + 1 ≤ payload.length)]
    · rw [if_neg hterm] at h
      contradiction
  · simp at h

/-! ### Structured-block span facts

A successfully parsed structured paper-prime block is delimited by the reserved
terminator `19`: every consumed token before the terminator differs from `19`, and the parse
consumes through exactly one final `19`.  These facts let streaming scanners recognize
the block boundary from the terminator alone, without replaying the Foundation
decoder. -/

lemma readStructuredLength_shape {ts : List ℕ} {n : ℕ} {rest : List ℕ}
    (h : readStructuredLength ts = some (n, rest)) :
    ts = List.replicate n 1 ++ 0 :: rest := by
  induction ts generalizing n rest with
  | nil => simp [readStructuredLength] at h
  | cons t ts ih =>
      by_cases h0 : t = 0
      · subst t
        simp only [readStructuredLength, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      by_cases h1 : t = 1
      · subst t
        simp only [readStructuredLength] at h
        rcases hr : readStructuredLength ts with _ | ⟨m, r⟩
        · simp [hr] at h
        · simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ih hr]
          simp [List.replicate_succ]
      · simp [readStructuredLength, h0, h1] at h

lemma parseStructuredNat_consumed_lt : ∀ {fuel : ℕ} {ts : List ℕ} {n : ℕ}
    {rest : List ℕ}, parseStructuredNat fuel ts = some (n, rest) →
      ∃ w, ts = w ++ rest ∧ ∀ x ∈ w, x < 19 := by
  intro fuel
  induction fuel with
  | zero => intro ts n rest h; simp [parseStructuredNat] at h
  | succ fuel ih =>
      intro ts n rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [parseStructuredNat] at h
      rw [parseStructuredNat] at h
      split_ifs at h with h0 h1 h2
      · obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact ⟨[t], rfl, by simp [h0]⟩
      all_goals
        rcases hp : parseStructuredNat fuel ts with _ | p <;> simp [hp] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        obtain ⟨w, rfl, hw⟩ := ih hp
        refine ⟨t :: w, rfl, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · exact hw x hx'

lemma parseStructuredArithmeticTerm_consumed_lt : ∀ {fuel depth : ℕ} {ts : List ℕ}
    {code : ℕ} {rest : List ℕ},
      parseStructuredArithmeticTerm fuel depth ts = some (code, rest) →
      ∃ w, ts = w ++ rest ∧ ∀ x ∈ w, x < 19 := by
  intro fuel
  induction fuel with
  | zero => intro depth ts code rest h; simp [parseStructuredArithmeticTerm] at h
  | succ fuel ih =>
      intro depth ts code rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [parseStructuredArithmeticTerm] at h
      rw [parseStructuredArithmeticTerm] at h
      split_ifs at h with h3 h4 h5 h6 hb
      · rcases hp : parseStructuredNat fuel ts with _ | p <;> simp [hp] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        obtain ⟨w, rfl, hw⟩ := parseStructuredNat_consumed_lt hp
        refine ⟨t :: w, rfl, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · exact hw x hx'
      · rcases hp : parseStructuredNat fuel ts with _ | p <;> simp [hp] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        obtain ⟨w, rfl, hw⟩ := parseStructuredNat_consumed_lt hp
        refine ⟨t :: w, rfl, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · exact hw x hx'
      · obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact ⟨[t], rfl, by simp [h5]⟩
      · obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact ⟨[t], rfl, by simp [h6]⟩
      all_goals
        rcases hp : parseStructuredArithmeticTerm fuel 0 ts with _ | p <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticTerm fuel 0 p.2 with _ | q <;> simp [hq] at h
        obtain ⟨a, rfl, -⟩ := h
        obtain ⟨w₁, hts, hw₁⟩ := ih hp
        obtain ⟨w₂, hp2, hw₂⟩ := ih hq
        refine ⟨t :: w₁ ++ w₂, by rw [hts, hp2]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · rcases List.mem_append.mp hx' with hx₁ | hx₂
          · exact hw₁ x hx₁
          · exact hw₂ x hx₂

/-- A successful structured formula parse consumes a span containing no reserved
terminator `19`.  The bound is `≠ 19` rather than `< 19` because the formula grammar uses
tags `20`/`21`/`22` for the paper's primitive `¬`/`⟹`/`⟺` (`dd:nnf`); the term and numeral
sub-grammars stay under `19` (`parseStructuredArithmeticTerm_consumed_lt`).  `≠ 19` is
exactly what the three consumers use — ruling the terminator out of a consumed span.

*Proof kind:* `P` proved. -/
lemma parseStructuredArithmeticFormula_consumed_lt :
    ∀ {fuel depth : ℕ} {ts : List ℕ} {code : ℕ} {rest : List ℕ},
      parseStructuredArithmeticFormula fuel depth ts = some (code, rest) →
      ∃ w, ts = w ++ rest ∧ ∀ x ∈ w, x ≠ 19 := by
  intro fuel
  induction fuel with
  | zero =>
      intro depth ts code rest h
      simp [parseStructuredArithmeticFormula] at h
  | succ fuel ih =>
      intro depth ts code rest h
      rcases ts with _ | ⟨t, ts⟩
      · simp [parseStructuredArithmeticFormula] at h
      rw [parseStructuredArithmeticFormula] at h
      by_cases h9 : t = 9
      · rw [if_pos h9] at h
        obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact ⟨[t], rfl, by simp [h9]⟩
      rw [if_neg h9] at h
      by_cases h10 : t = 10
      · rw [if_pos h10] at h
        obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact ⟨[t], rfl, by simp [h10]⟩
      rw [if_neg h10] at h
      by_cases hrel : t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14
      · rw [if_pos hrel] at h
        rcases hp : parseStructuredArithmeticTerm fuel 0 ts with _ | p <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticTerm fuel 0 p.2 with _ | q <;> simp [hq] at h
        obtain ⟨a, rfl, -⟩ := h
        obtain ⟨w₁, hts, hw₁⟩ := parseStructuredArithmeticTerm_consumed_lt hp
        obtain ⟨w₂, hp2, hw₂⟩ := parseStructuredArithmeticTerm_consumed_lt hq
        refine ⟨t :: w₁ ++ w₂, by rw [hts, hp2]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · rcases List.mem_append.mp hx' with hx₁ | hx₂
          · have := hw₁ x hx₁; omega
          · have := hw₂ x hx₂; omega
      rw [if_neg hrel] at h
      by_cases hbin : t = 15 ∨ t = 16
      · rw [if_pos hbin] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticFormula fuel 0 p.2 with _ | q <;> simp [hq] at h
        obtain ⟨a, rfl, -⟩ := h
        obtain ⟨w₁, hts, hw₁⟩ := ih hp
        obtain ⟨w₂, hp2, hw₂⟩ := ih hq
        refine ⟨t :: w₁ ++ w₂, by rw [hts, hp2]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · rcases List.mem_append.mp hx' with hx₁ | hx₂
          · exact hw₁ x hx₁
          · exact hw₂ x hx₂
      rw [if_neg hbin] at h
      by_cases hquant : t = 17 ∨ t = 18
      · rw [if_pos hquant] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p <;> simp [hp] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        obtain ⟨w₁, hts, hw₁⟩ := ih hp
        refine ⟨t :: w₁, by rw [hts]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · exact hw₁ x hx'
      rw [if_neg hquant] at h
      by_cases h20 : t = 20
      · rw [if_pos h20] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p <;> simp [hp] at h
        rcases h with ⟨-, hrest⟩
        subst rest
        obtain ⟨w₁, hts, hw₁⟩ := ih hp
        refine ⟨t :: w₁, by rw [hts]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · exact hw₁ x hx'
      rw [if_neg h20] at h
      by_cases h21 : t = 21
      · rw [if_pos h21] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticFormula fuel 0 p.2 with _ | q <;> simp [hq] at h
        obtain ⟨a, rfl, -⟩ := h
        obtain ⟨w₁, hts, hw₁⟩ := ih hp
        obtain ⟨w₂, hp2, hw₂⟩ := ih hq
        refine ⟨t :: w₁ ++ w₂, by rw [hts, hp2]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · rcases List.mem_append.mp hx' with hx₁ | hx₂
          · exact hw₁ x hx₁
          · exact hw₂ x hx₂
      rw [if_neg h21] at h
      by_cases h22 : t = 22
      · rw [if_pos h22] at h
        rcases hp : parseStructuredArithmeticFormula fuel 0 ts with _ | p <;> simp [hp] at h
        rcases hq : parseStructuredArithmeticFormula fuel 0 p.2 with _ | q <;> simp [hq] at h
        obtain ⟨a, rfl, -⟩ := h
        obtain ⟨w₁, hts, hw₁⟩ := ih hp
        obtain ⟨w₂, hp2, hw₂⟩ := ih hq
        refine ⟨t :: w₁ ++ w₂, by rw [hts, hp2]; simp, ?_⟩
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · rcases List.mem_append.mp hx' with hx₁ | hx₂
          · exact hw₁ x hx₁
          · exact hw₂ x hx₂
      rw [if_neg h22] at h
      simp at h

/-- **Structured span**: a successful structured paper-prime parse consumes a
`19`-free span followed by exactly one terminator `19`. -/
lemma parseStructuredPaperPrime_span {ts : List ℕ} {φ : Sentence} {rest : List ℕ}
    (h : parseStructuredPaperPrime ts = some (φ, rest)) :
    ∃ w, ts = w ++ 19 :: rest ∧ ∀ x ∈ w, x ≠ 19 := by
  rcases ts with _ | ⟨polarity, framed⟩
  · simp [parseStructuredPaperPrime] at h
  rw [parseStructuredPaperPrime] at h
  split at h <;> try contradiction
  rename_i hpol
  rcases hr : readStructuredLength framed with _ | ⟨n, payload⟩
  · simp [hr] at h
  rw [hr] at h
  simp only [Option.bind_some] at h
  split at h <;> try contradiction
  rename_i hlen
  rcases hp : parseStructuredArithmeticFormula n 0 (payload.take n) with _ | ⟨code, r⟩
  · simp [hp] at h
  rw [hp] at h
  rcases r with _ | ⟨x, xs⟩
  · change (if List.getD payload n 0 = 19 then
        some (Formula.atom (Nat.pair 5 (Nat.pair polarity code)), payload.drop (n + 1))
      else none) = some (φ, rest) at h
    by_cases hterm : payload.getD n 0 = 19
    · rw [if_pos hterm] at h
      obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      have hnlt : n < payload.length := by
        have hne : n ≠ payload.length := by
          intro heq
          subst n
          simpa [List.getD] using hterm
        omega
      obtain ⟨w, hw, hwlt⟩ := parseStructuredArithmeticFormula_consumed_lt hp
      rw [List.append_nil] at hw
      have hpay : payload = payload.take n ++ 19 :: payload.drop (n + 1) := by
        conv_lhs => rw [← List.take_append_drop n payload]
        congr 1
        rw [List.drop_eq_getElem_cons hnlt]
        congr 1
        rw [List.getD_eq_getElem _ _ hnlt] at hterm
        exact hterm
      refine ⟨polarity :: List.replicate n 1 ++ 0 :: payload.take n, ?_, ?_⟩
      · rw [readStructuredLength_shape hr]
        conv_lhs => rw [hpay]
        simp
      · intro x hx
        rcases List.mem_cons.mp (by
            simpa using hx : x ∈ polarity ::
              (List.replicate n 1 ++ 0 :: payload.take n)) with rfl | hx'
        · omega
        · rcases List.mem_append.mp hx' with hx₁ | hx₂
          · have := List.eq_of_mem_replicate hx₁
            omega
          · rcases List.mem_cons.mp hx₂ with rfl | hx₃
            · omega
            · rw [hw] at hx₃
              exact hwlt x hx₃
    · rw [if_neg hterm] at h
      contradiction
  · simp at h

/-- The unary length reader is blind to everything past the first token outside
`{0, 1}`; in particular a leading `19` fails it for every continuation. -/
lemma readStructuredLength_cases (fr : List ℕ) :
    (∃ k, fr = List.replicate k 1) ∨
    (∀ y, readStructuredLength (fr ++ y) = none) ∨
    (∃ n fr', fr = List.replicate n 1 ++ 0 :: fr' ∧
      ∀ y, readStructuredLength (fr ++ y) = some (n, fr' ++ y)) := by
  induction fr with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons t fr ih =>
      by_cases h0 : t = 0
      · subst t
        exact Or.inr (Or.inr ⟨0, fr, rfl, fun y => rfl⟩)
      by_cases h1 : t = 1
      · subst t
        rcases ih with ⟨k, rfl⟩ | hnone | ⟨n, fr', rfl, hsome⟩
        · exact Or.inl ⟨k + 1, by simp [List.replicate_succ]⟩
        · refine Or.inr (Or.inl fun y => ?_)
          simp only [List.cons_append, readStructuredLength, hnone y, Option.map_none]
        · refine Or.inr (Or.inr ⟨n + 1, fr', by simp [List.replicate_succ], fun y => ?_⟩)
          simp only [List.cons_append, readStructuredLength, hsome y, Option.map_some]
      · refine Or.inr (Or.inl fun y => ?_)
        simp [readStructuredLength, h0, h1]

lemma readStructuredLength_replicate_19 (k : ℕ) (z : List ℕ) :
    readStructuredLength (List.replicate k 1 ++ 19 :: z) = none := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append,
      readStructuredLength, ih, Option.map_none]

/-- **Tail invariance at the first terminator**: on any stream whose structured
segment ends at its first `19`, the parse outcome — success with the corresponding
suffix, or failure — is independent of what follows that terminator. -/
lemma parseStructuredPaperPrime_first19 (w : List ℕ) (hw : ∀ x ∈ w, x ≠ 19)
    (tail : List ℕ) :
    parseStructuredPaperPrime (w ++ 19 :: tail) =
      (parseStructuredPaperPrime (w ++ [19])).map fun p => (p.1, tail) := by
  rcases w with _ | ⟨polarity, fr⟩
  · simp only [List.nil_append]
    rw [parseStructuredPaperPrime, parseStructuredPaperPrime]
    rw [if_neg (by omega), if_neg (by omega)]
    rfl
  have hfr19 : ∀ x ∈ fr, x ≠ 19 := fun x hx => hw x (List.mem_cons_of_mem _ hx)
  simp only [List.cons_append]
  rw [parseStructuredPaperPrime, parseStructuredPaperPrime]
  by_cases hpol : polarity ≤ 1
  · rw [if_pos hpol, if_pos hpol]
    rcases readStructuredLength_cases fr with ⟨k, rfl⟩ | hnone | ⟨n, fr', rfl, hsome⟩
    · rw [readStructuredLength_replicate_19 k tail,
        readStructuredLength_replicate_19 k []]
      rfl
    · rw [hnone (19 :: tail), hnone [19]]
      rfl
    · have hfr' : ∀ x ∈ fr', x ≠ 19 := fun x hx =>
        hfr19 x (by simp [hx])
      rw [hsome (19 :: tail), hsome [19]]
      simp only [Option.bind_some]
      by_cases hn : n ≤ fr'.length + 1
      · rw [if_pos (by simp; omega), if_pos (by simp; omega)]
        have hwin : (fr' ++ 19 :: tail).take n = (fr' ++ [19]).take n := by
          rw [List.take_append, List.take_append]
          rcases Nat.lt_or_ge n (fr'.length + 1) with hlt | hge
          · rw [Nat.sub_eq_zero_of_le (by omega), List.take_zero, List.take_zero]
          · have hn1 : n = fr'.length + 1 := by omega
            subst hn1
            simp
        rw [hwin]
        rcases hp : parseStructuredArithmeticFormula n 0 ((fr' ++ [19]).take n)
          with _ | ⟨code, r⟩
        · rw [hp]
          rfl
        rcases r with _ | ⟨x, xs⟩
        swap
        · rw [hp]
          rfl
        rw [hp]
        by_cases hnL : n < fr'.length
        · have hgd : ∀ z : List ℕ, List.getD (fr' ++ z) n 0 = fr'[n]'hnL := by
            intro z
            rw [List.getD_append _ _ _ _ hnL]
            simp [List.getD, List.getElem?_eq_getElem hnL]
          have hne19 : fr'[n]'hnL ≠ 19 := hfr' _ (List.getElem_mem hnL)
          change (if List.getD (fr' ++ 19 :: tail) n 0 = 19 then _ else none) =
            Option.map _ (if List.getD (fr' ++ [19]) n 0 = 19 then _ else none)
          rw [hgd (19 :: tail), hgd [19], if_neg hne19, if_neg hne19]
          rfl
        · by_cases hnL1 : n = fr'.length
          · change (if List.getD (fr' ++ 19 :: tail) n 0 = 19 then
                some (_, (fr' ++ 19 :: tail).drop (n + 1)) else none) =
              Option.map _ (if List.getD (fr' ++ [19]) n 0 = 19 then
                some (_, (fr' ++ [19]).drop (n + 1)) else none)
            subst hnL1
            rw [List.getD_append_right _ _ _ _ le_rfl,
              List.getD_append_right _ _ _ _ le_rfl]
            simp only [Nat.sub_self, List.getD_cons_zero, if_pos rfl]
            have hd1 : (fr' ++ 19 :: tail).drop (fr'.length + 1) = tail := by
              rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]
              simp
            have hd2 : (fr' ++ [19]).drop (fr'.length + 1) = [] := by
              rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]
              simp
            rw [hd1, hd2]
            rfl
          · exfalso
            have hn1 : n = fr'.length + 1 := by omega
            obtain ⟨v, hv, hvlt⟩ := parseStructuredArithmeticFormula_consumed_lt hp
            rw [List.append_nil] at hv
            have h19 : (19 : ℕ) ∈ (fr' ++ [19]).take n := by
              rw [List.take_of_length_le (by simp [hn1])]
              simp
            rw [hv] at h19
            exact hvlt 19 h19 rfl
      · have hR : ¬ n ≤ (fr' ++ [19]).length := by simp; omega
        conv_rhs => rw [if_neg hR]
        by_cases hn2 : n ≤ (fr' ++ 19 :: tail).length
        · rw [if_pos hn2]
          rcases hp : parseStructuredArithmeticFormula n 0
              ((fr' ++ 19 :: tail).take n) with _ | ⟨code, r⟩
          · rfl
          rcases r with _ | ⟨x, xs⟩
          swap
          · rfl
          exfalso
          obtain ⟨v, hv, hvlt⟩ := parseStructuredArithmeticFormula_consumed_lt hp
          rw [List.append_nil] at hv
          have h19 : (19 : ℕ) ∈ ((fr' ++ 19 :: tail).take n) := by
            rw [List.take_append]
            refine List.mem_append.mpr (Or.inr ?_)
            rw [show n - fr'.length = (n - fr'.length - 1) + 1 by omega,
              List.take_succ_cons]
            exact List.mem_cons_self ..
          rw [hv] at h19
          exact hvlt 19 h19 rfl
        · rw [if_neg hn2]
          rfl
  · rw [if_neg hpol, if_neg hpol]
    rfl

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
        cases c with
        | zero =>
            have hlt := parseStructuredPaperPrime_length_lt h
            simp only [List.length_cons]
            omega
        | succ c =>
            rcases hdec : Encodable.decode (α := Sentence) (c + 1) with _ | ψ
            · simp [hdec] at h
            · simp only [hdec, Option.map_some] at h
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
      have hc : Encodable.encode φ ≠ 0 := by
        change LO.Propositional.Formula.toNat φ ≠ 0
        cases φ <;> simp [LO.Propositional.Formula.toNat]
      rcases he : Encodable.encode φ with _ | c
      · exact absurd he hc
      · have henc := Encodable.encodek φ
        rw [he] at henc
        simpa [henc]

/-- **Parse extension** (self-delimitation): a successful parse is unchanged by
appending a suffix to the input — the consumed block determines the result. -/
lemma parseRpn_append : ∀ (fuel : ℕ) (ts : List ℕ) {φ : Sentence} {r : List ℕ}
    (tail : List ℕ), parseRpn fuel ts = some (φ, r) →
    parseRpn fuel (ts ++ tail) = some (φ, r ++ tail) := by
  intro fuel
  induction fuel with
  | zero => intro ts φ r tail h; simp [parseRpn] at h
  | succ fuel ih =>
      intro ts φ r tail h
      match ts with
      | [] => simp at h
      | t :: rest =>
          rw [parseRpn_cons] at h
          rw [List.cons_append, parseRpn_cons]
          by_cases h0 : t = 0
          · rw [if_pos h0] at h ⊢
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
            rfl
          · rw [if_neg h0] at h ⊢
            by_cases h1 : t = 1
            · rw [if_pos h1] at h ⊢
              match rest with
              | [] => simp at h
              | c :: rest' =>
                  cases c with
                  | zero =>
                      exact parseStructuredPaperPrime_append tail h
                  | succ c =>
                      cases hdec : Encodable.decode (α := Sentence) (c + 1) with
                      | none => simp [hdec] at h
                      | some ψ =>
                          simp [hdec] at h ⊢
                          obtain ⟨rfl, rfl⟩ := h
                          exact ⟨rfl, rfl⟩
            · rw [if_neg h1] at h ⊢
              have hbin : ∀ (mk : Sentence → Sentence → Sentence),
                  ((parseRpn fuel rest).bind fun p =>
                    (parseRpn fuel p.2).bind fun q =>
                      some (mk p.1 q.1, q.2)) = some (φ, r) →
                  ((parseRpn fuel (rest ++ tail)).bind fun p =>
                    (parseRpn fuel p.2).bind fun q =>
                      some (mk p.1 q.1, q.2)) = some (φ, r ++ tail) := by
                intro mk hh
                cases hp : parseRpn fuel rest with
                | none => rw [hp] at hh; simp at hh
                | some p =>
                    rw [hp] at hh
                    simp only [Option.bind_some] at hh
                    cases hq : parseRpn fuel p.2 with
                    | none => rw [hq] at hh; simp at hh
                    | some q =>
                        rw [hq] at hh
                        simp only [Option.bind_some] at hh
                        obtain ⟨h1', h2'⟩ := Prod.mk.injEq .. ▸ Option.some.inj hh
                        rw [ih rest tail hp]
                        simp only [Option.bind_some]
                        rw [ih p.2 tail hq]
                        simp only [Option.bind_some]
                        rw [h1', h2']
              by_cases h2 : t = 2
              · rw [if_pos h2] at h ⊢; exact hbin _ h
              · rw [if_neg h2] at h ⊢
                by_cases h3 : t = 3
                · rw [if_pos h3] at h ⊢; exact hbin _ h
                · rw [if_neg h3] at h ⊢
                  by_cases h4 : t = 4
                  · rw [if_pos h4] at h ⊢; exact hbin _ h
                  · rw [if_neg h4] at h ⊢
                    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
                    rfl

/-- A complete self-delimiting block placed at the head of a longer stream parses to
its sentence with exactly the appended tail as remainder, at any fuel covering the
stream. -/
lemma parseRpn_block_head {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) (tail : List ℕ) {fuel : ℕ}
    (hfuel : b.length ≤ fuel) :
    parseRpn fuel (b ++ tail) = some (φ, tail) := by
  have := parseRpn_append b.length b tail hb
  simpa using parseRpn_mono (b ++ tail) hfuel this

/-- Injectivity of the canonical coding. -/
lemma rpn_injective : Function.Injective rpn := by
  intro φ ψ h
  have hφ := parseRpn_rpn φ [] (fuel := (rpn φ).length) le_rfl
  have hψ := parseRpn_rpn ψ [] (fuel := (rpn φ).length) (le_of_eq (by rw [h]))
  rw [List.append_nil] at hφ hψ
  rw [h] at hφ hψ
  obtain ⟨h1, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj (hφ.symm.trans hψ)
  exact h1

/-! ### Contraction transparency

A token run is *transparent* when the stream contraction copies it verbatim and
continues: the shape of every strategy-stream fragment that opens no sentence slot.
Payload chunks, bare operator tokens, and their concatenations are transparent, and a
transparent prefix commutes with `unRpn`. -/

/-- `unRpn` copies `ts` verbatim ahead of any continuation. -/
def UnRpnTransparent (ts : List ℕ) : Prop :=
  ∀ rest, unRpn (ts ++ rest) = ts ++ unRpn rest

lemma UnRpnTransparent.nil : UnRpnTransparent [] := fun _ => rfl

lemma UnRpnTransparent.append {xs ys : List ℕ}
    (hx : UnRpnTransparent xs) (hy : UnRpnTransparent ys) :
    UnRpnTransparent (xs ++ ys) := fun rest => by
  rw [List.append_assoc, hx (ys ++ rest), hy rest, List.append_assoc]

/-! ## The stream transducer

`unRpn` walks the flat strategy grammar and contracts each sentence block back to a
single pair-code token: sentence slots follow tags `0` (price — one day token after)
and `6` (trade); tags `1` and `7` carry one opaque payload token; everything else is
copied.  A failed block parse emits the undecodable code `0` and stops, preserving
rejection.  Fuel decreases once per grammar chunk; `ts.length` always suffices. -/

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
  rw [unRpnTokens_congr rest (by simp only [List.length_append]; omega) le_rfl]
  rfl

/-- The contraction never lengthens a stream by more than the one trailing
failure marker: the economic length bounds of a spliced emission transfer to its
token-level serialization. -/
lemma unRpnTokens_length_le : ∀ (fuel : ℕ) (ts : List ℕ),
    (unRpnTokens fuel ts).length ≤ ts.length + 1 := by
  intro fuel
  induction fuel with
  | zero => intro ts; cases ts <;> simp [unRpnTokens]
  | succ fuel ih =>
      intro ts
      match ts with
      | [] => simp [unRpnTokens]
      | t :: rest =>
          rw [unRpnTokens_cons]
          by_cases h0 : t = 0
          · rw [if_pos h0]
            cases hp : parseRpn rest.length rest with
            | none => simp
            | some pr =>
                obtain ⟨φ, r1⟩ := pr
                cases r1 with
                | nil => simp
                | cons d r2 =>
                    have hlt := parseRpn_length_lt rest.length rest φ (d :: r2) hp
                    have := ih r2
                    simp only [List.length_cons] at hlt ⊢
                    omega
          · rw [if_neg h0]
            by_cases h6 : t = 6
            · rw [if_pos h6]
              cases hp : parseRpn rest.length rest with
              | none => simp
              | some pr =>
                  obtain ⟨φ, r1⟩ := pr
                  have hlt := parseRpn_length_lt rest.length rest φ r1 hp
                  have := ih r1
                  simp only [List.length_cons] at ⊢
                  omega
            · rw [if_neg h6]
              by_cases h1 : t = 1
              · rw [if_pos h1]
                cases rest with
                | nil => simp
                | cons c r =>
                    have := ih r
                    simp only [List.length_cons] at ⊢
                    omega
              · rw [if_neg h1]
                by_cases h7 : t = 7
                · rw [if_pos h7]
                  cases rest with
                  | nil => simp
                  | cons c r =>
                      have := ih r
                      simp only [List.length_cons] at ⊢
                      omega
                · rw [if_neg h7]
                  have := ih rest
                  simp only [List.length_cons] at ⊢
                  omega

/-- The whole-stream form of `unRpnTokens_length_le`: contraction adds at most the one
trailing failure marker. -/
lemma unRpn_length_le (ts : List ℕ) : (unRpn ts).length ≤ ts.length + 1 :=
  unRpnTokens_length_le ts.length ts

/-- A complete price chunk with **any** self-delimiting block parsing to `φ`
contracts exactly (canonical runs and escapes are the two special cases). -/
lemma unRpn_price_chunk_block {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) (d : ℕ) (rest : List ℕ) :
    unRpn (0 :: (b ++ d :: rest)) =
      0 :: Encodable.encode φ :: d :: unRpn rest := by
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
    parseRpn_block_head hb (d :: rest) (by simp)]
  simp only []
  rw [unRpnTokens_congr rest
    (by simp only [List.length_cons, List.length_append]; omega) le_rfl]
  rfl

/-- A complete trade chunk with **any** self-delimiting block parsing to `φ`
contracts exactly. -/
lemma unRpn_trade_chunk_block {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) (rest : List ℕ) :
    unRpn (6 :: (b ++ rest)) =
      6 :: Encodable.encode φ :: unRpn rest := by
  rw [unRpn, List.length_cons, unRpnTokens_cons,
    if_neg (by norm_num), if_pos rfl,
    parseRpn_block_head hb rest (by simp)]
  simp only []
  rw [unRpnTokens_congr rest
    (by simp only [List.length_append]; omega) le_rfl]
  rfl

/-- Opaque payload chunks (rational constants, variable indices) copy verbatim. -/
lemma unRpn_payload_chunk (t c : ℕ) (ht : t = 1 ∨ t = 7) (rest : List ℕ) :
    unRpn (t :: c :: rest) = t :: c :: unRpn rest := by
  rcases ht with rfl | rfl
  · rw [unRpn, List.length_cons, unRpnTokens_cons,
      if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    simp only []
    rw [unRpnTokens_congr rest (by simp only [List.length_cons]; omega) le_rfl]
    rfl
  · rw [unRpn, List.length_cons, unRpnTokens_cons,
      if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
      if_pos rfl]
    simp only []
    rw [unRpnTokens_congr rest (by simp only [List.length_cons]; omega) le_rfl]
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

/-- Payload chunks are transparent. -/
lemma UnRpnTransparent.payload (t c : ℕ) (ht : t = 1 ∨ t = 7) :
    UnRpnTransparent [t, c] := fun rest => by
  simpa using unRpn_payload_chunk t c ht rest

/-- Bare operator/close tokens are transparent. -/
lemma UnRpnTransparent.single (t : ℕ) (ht : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 6 ∧ t ≠ 7) :
    UnRpnTransparent [t] := fun rest => by
  simpa using unRpn_single_chunk t ht rest

/-- No `price` leaves: the feature's serialization opens no sentence slot. -/
def EF.priceFree : EF → Prop
  | .price _ _ => False
  | .const _ => True
  | .add a b => a.priceFree ∧ b.priceFree
  | .mul a b => a.priceFree ∧ b.priceFree
  | .max a b => a.priceFree ∧ b.priceFree
  | .safeRecip a => a.priceFree
  | .var _ => True
  | .letE x body => x.priceFree ∧ body.priceFree

/-- The serialization of a price-leaf-free feature is transparent: its tokens are
payload pairs (`1`/`7` tags) and bare operator tokens (`2`–`5`, `8`). -/
lemma EF.serialize_unRpnTransparent : ∀ e : EF, EF.priceFree e →
    UnRpnTransparent e.serialize := by
  intro e
  induction e with
  | price φ n => intro h; exact absurd h not_false
  | const q => intro _; exact UnRpnTransparent.payload 1 _ (Or.inl rfl)
  | add a b iha ihb =>
      intro h
      obtain ⟨ha, hb⟩ := h
      exact ((iha ha).append (ihb hb)).append
        (UnRpnTransparent.single 2 (by norm_num))
  | mul a b iha ihb =>
      intro h
      obtain ⟨ha, hb⟩ := h
      exact ((iha ha).append (ihb hb)).append
        (UnRpnTransparent.single 3 (by norm_num))
  | max a b iha ihb =>
      intro h
      obtain ⟨ha, hb⟩ := h
      exact ((iha ha).append (ihb hb)).append
        (UnRpnTransparent.single 4 (by norm_num))
  | safeRecip a iha =>
      intro h
      exact (iha h).append
        (UnRpnTransparent.single 5 (by norm_num))
  | var i => intro _; exact UnRpnTransparent.payload 7 _ (Or.inr rfl)
  | letE x body ihx ihbody =>
      intro h
      obtain ⟨hx, hbody⟩ := h
      exact ((ihx hx).append (ihbody hbody)).append
        (UnRpnTransparent.single 8 (by norm_num))

/-- Escape parse with an arbitrary decodable payload. -/
lemma parseRpn_escape' {c : ℕ} {φ : Sentence}
    (hdec : Encodable.decode (α := Sentence) c = some φ)
    (rest : List ℕ) {fuel : ℕ} (hfuel : 1 ≤ fuel) :
    parseRpn fuel (1 :: c :: rest) = some (φ, rest) := by
  match fuel, hfuel with
  | fuel + 1, _ =>
      rw [parseRpn_cons, if_neg (by omega), if_pos rfl]
      have hc : c ≠ 0 := by
        intro hc
        subst c
        change LO.Propositional.Formula.ofNat 0 = some φ at hdec
        simp [LO.Propositional.Formula.ofNat] at hdec
      rcases c with _ | c
      · contradiction
      · simp [hdec]

/-- Escape parse failure on an undecodable payload. -/
lemma parseRpn_escape_none {c : ℕ}
    (hc : c ≠ 0) (hdec : Encodable.decode (α := Sentence) c = none)
    (rest : List ℕ) (fuel : ℕ) :
    parseRpn fuel (1 :: c :: rest) = none := by
  match fuel with
  | 0 => rfl
  | fuel + 1 =>
      rw [parseRpn_cons, if_neg (by omega), if_pos rfl]
      rcases c with _ | c
      · contradiction
      · simp [hdec]

lemma parseRpn_structured_poison (rest : List ℕ) (fuel : ℕ) :
    parseRpn fuel (1 :: 0 :: 2 :: rest) = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [parseRpn_cons, if_neg (by norm_num), if_pos rfl]
      simp [parseStructuredPaperPrime]

/-! ## The escape expansion

`escExpand` is the forward splice for the model inclusions: each sentence-slot token
`c` becomes the two-token escape block `[1, c]`, everything else is copied.  Composed
with `unRpn` it re-emits the *canonical* code of the decoded sentence, so the streams
need not agree token-for-token on non-canonical codes — but they parse identically,
which is the simulation theorem below. -/

/-- Fuel-clocked escape splice: each sentence-slot token becomes `[1, c]` (or `[1, 0, 2]`,
a deliberately unparseable block, when `c = 0`), everything else copies; `ts.length` fuel
always suffices (`escExpandTokens_congr`). -/
def escExpandTokens : ℕ → List ℕ → List ℕ
  | _, [] => []
  | 0, _ => []
  | fuel + 1, t :: rest =>
      if t = 0 then
        match rest with
        | [] => [0]
        | c :: r1 =>
            match r1 with
            | [] => if c = 0 then [0, 1, 0, 2] else [0, 1, c]
            | d :: r2 =>
                if c = 0 then 0 :: 1 :: 0 :: 2 :: d :: escExpandTokens fuel r2
                else 0 :: 1 :: c :: d :: escExpandTokens fuel r2
      else if t = 6 then
        match rest with
        | [] => [6]
        | c :: r =>
            if c = 0 then 6 :: 1 :: 0 :: 2 :: escExpandTokens fuel r
            else 6 :: 1 :: c :: escExpandTokens fuel r
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
            | [] => if c = 0 then [0, 1, 0, 2] else [0, 1, c]
            | d :: r2 =>
                if c = 0 then 0 :: 1 :: 0 :: 2 :: d :: escExpandTokens fuel r2
                else 0 :: 1 :: c :: d :: escExpandTokens fuel r2
      else if t = 6 then
        match rest with
        | [] => [6]
        | c :: r =>
            if c = 0 then 6 :: 1 :: 0 :: 2 :: escExpandTokens fuel r
            else 6 :: 1 :: c :: escExpandTokens fuel r
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
              split <;> simp
            simp only [List.length_cons] at hn hf ⊢
            have := escExpand_length_le n r2 (by omega) fuel (by omega)
            split <;> simp only [List.length_cons] <;> omega
          rw [if_neg h0]
          by_cases h6 : t = 6
          · rw [if_pos h6]
            rcases rest with _ | ⟨c, r⟩
            · simp only []
              simp
            simp only [List.length_cons] at hn hf ⊢
            have := escExpand_length_le n r (by omega) fuel (by omega)
            split <;> simp only [List.length_cons] <;> omega
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

/-- The escape splice preserves polynomial emission length: it at most doubles the
stream.  This is the `escExpand` form of `escExpand_length_le`, the one a client meters
with. -/
lemma escExpand_length_le' (ts : List ℕ) : (escExpand ts).length ≤ 2 * ts.length :=
  escExpand_length_le ts.length ts le_rfl ts.length le_rfl

/-! ### Chunk equations for `escExpand` -/

lemma escExpand_price_chunk (c d : ℕ) (hc : c ≠ 0) (r2 : List ℕ) :
    escExpand (0 :: c :: d :: r2) = 0 :: 1 :: c :: d :: escExpand r2 := by
  rw [escExpand, List.length_cons, escExpandTokens_cons, if_pos rfl]
  simp only []
  rw [if_neg hc]
  rw [escExpandTokens_congr r2 (by simp only [List.length_cons]; omega) le_rfl]
  rfl

lemma escExpand_trade_chunk (c : ℕ) (hc : c ≠ 0) (r : List ℕ) :
    escExpand (6 :: c :: r) = 6 :: 1 :: c :: escExpand r := by
  rw [escExpand, List.length_cons, escExpandTokens_cons,
    if_neg (by norm_num), if_pos rfl]
  simp only []
  rw [if_neg hc]
  rw [escExpandTokens_congr r (by simp only [List.length_cons]; omega) le_rfl]
  rfl

lemma escExpand_price_zero_chunk (d : ℕ) (r : List ℕ) :
    escExpand (0 :: 0 :: d :: r) = 0 :: 1 :: 0 :: 2 :: d :: escExpand r := by
  rw [escExpand, List.length_cons, escExpandTokens_cons, if_pos rfl]
  simp only [↓reduceIte]
  rw [escExpandTokens_congr r (by simp only [List.length_cons]; omega) le_rfl]
  rfl

lemma escExpand_price_truncated (c : ℕ) (hc : c ≠ 0) :
    escExpand [0, c] = [0, 1, c] := by
  rw [escExpand, show ([0, c] : List ℕ).length = 2 from rfl,
    escExpandTokens_cons, if_pos rfl]
  simp [hc]

lemma escExpand_price_zero_truncated : escExpand [0, 0] = [0, 1, 0, 2] := rfl

lemma escExpand_trade_zero_chunk (r : List ℕ) :
    escExpand (6 :: 0 :: r) = 6 :: 1 :: 0 :: 2 :: escExpand r := by
  rw [escExpand, List.length_cons, escExpandTokens_cons,
    if_neg (by norm_num), if_pos rfl]
  simp only [↓reduceIte]
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
    (hc : c ≠ 0) (hdec : Encodable.decode (α := Sentence) c = none)
    (d : ℕ) (rest : List ℕ) :
    unRpn (0 :: 1 :: c :: d :: rest) = [0, 0] := by
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
    parseRpn_escape_none hc hdec (d :: rest) _]

lemma unRpn_trade_escape' {c : ℕ} {φ : Sentence}
    (hdec : Encodable.decode (α := Sentence) c = some φ) (rest : List ℕ) :
    unRpn (6 :: 1 :: c :: rest) = 6 :: Encodable.encode φ :: unRpn rest := by
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_neg (by norm_num), if_pos rfl,
    parseRpn_escape' hdec rest (by simp)]
  simp only []
  rw [unRpnTokens_congr rest (by simp only [List.length_cons]; omega) le_rfl]
  rfl

lemma unRpn_trade_escape_none {c : ℕ}
    (hc : c ≠ 0) (hdec : Encodable.decode (α := Sentence) c = none)
    (rest : List ℕ) :
    unRpn (6 :: 1 :: c :: rest) = [6, 0] := by
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_neg (by norm_num), if_pos rfl,
    parseRpn_escape_none hc hdec rest _]

lemma unRpn_price_structured_poison (d : ℕ) (rest : List ℕ) :
    unRpn (0 :: 1 :: 0 :: 2 :: d :: rest) = [0, 0] := by
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl,
    parseRpn_structured_poison (d :: rest)]

lemma unRpn_price_structured_poison_truncated :
    unRpn [0, 1, 0, 2] = [0, 0] := by
  norm_num [unRpn, unRpnTokens, parseRpn_structured_poison]

lemma unRpn_price_escape_none_truncated {c : ℕ} (hc : c ≠ 0)
    (hdec : Encodable.decode (α := Sentence) c = none) :
    unRpn [0, 1, c] = [0, 0] := by
  rw [unRpn, show ([0, 1, c] : List ℕ).length = 3 from rfl,
    unRpnTokens_cons, if_pos rfl, parseRpn_escape_none hc hdec []]

lemma unRpn_price_escape_truncated {c : ℕ} {φ : Sentence}
    (hdec : Encodable.decode (α := Sentence) c = some φ) :
    unRpn [0, 1, c] = [0, Encodable.encode φ] := by
  rw [unRpn, show ([0, 1, c] : List ℕ).length = 3 from rfl,
    unRpnTokens_cons, if_pos rfl, parseRpn_escape' hdec [] (by simp)]

lemma unRpn_trade_structured_poison (rest : List ℕ) :
    unRpn (6 :: 1 :: 0 :: 2 :: rest) = [6, 0] := by
  rw [unRpn, List.length_cons, unRpnTokens_cons,
    if_neg (by norm_num), if_pos rfl, parseRpn_structured_poison rest]

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
            cases c with
            | zero =>
                rw [escExpand_price_zero_truncated,
                  unRpn_price_structured_poison_truncated]
                refine Or.inl ?_
                simp [EF.streamReadFrom, EF.streamStep, decode_zero_sentence]
            | succ c =>
                rw [escExpand_price_truncated (c + 1) (by omega)]
                rcases hdec : Encodable.decode (α := Sentence) (c + 1) with _ | φ
                · rw [unRpn_price_escape_none_truncated (by omega) hdec]
                  refine Or.inl ?_
                  simp [EF.streamReadFrom, EF.streamStep, decode_zero_sentence, hdec]
                · rw [unRpn_price_escape_truncated hdec]
                  refine Or.inl ?_
                  simp [EF.streamReadFrom, EF.streamStep, hdec, Encodable.encodek]
        | c :: d :: r2 =>
            cases c with
            | zero =>
                rw [escExpand_price_zero_chunk, unRpn_price_structured_poison]
                refine Or.inl ?_
                simp [EF.streamReadFrom, EF.streamStep, decode_zero_sentence,
                  foldl_streamStep_none]
            | succ c =>
                rw [escExpand_price_chunk (c + 1) d (by omega)]
                rcases hdec : Encodable.decode (α := Sentence) (c + 1) with _ | φ
                · rw [unRpn_price_escape_none (by omega) hdec]
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
                  rw [hstep _ (c + 1) hdec,
                    hstep _ (Encodable.encode φ) (Encodable.encodek φ)]
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
            cases c with
            | zero =>
              rw [escExpand_trade_zero_chunk, unRpn_trade_structured_poison]
              refine Or.inl ?_
              rcases stack with _ | ⟨e, st'⟩ <;>
                simp [EF.streamReadFrom, EF.streamStep, decode_zero_sentence,
                  foldl_streamStep_none]
            | succ c =>
              rw [escExpand_trade_chunk (c + 1) (by omega)]
              rcases hdec : Encodable.decode (α := Sentence) (c + 1) with _ | φ
              · rw [unRpn_trade_escape_none (by omega) hdec]
                refine Or.inl ?_
                rcases stack with _ | ⟨e, st'⟩ <;>
                  simp [EF.streamReadFrom, EF.streamStep, decode_zero_sentence, hdec,
                    foldl_streamStep_none]
              · rw [unRpn_trade_escape' hdec]
                rcases stack with _ | ⟨e, st'⟩
                · refine Or.inl ?_
                  simp [EF.streamReadFrom, EF.streamStep,
                    foldl_streamStep_none]
                · have hstep : ∀ ts' : List ℕ, ∀ ctok,
                      Encodable.decode (α := Sentence) ctok = some φ →
                      EF.streamReadFrom (6 :: ctok :: ts')
                          (some ((0, pend), (e :: st', trades))) =
                        EF.streamReadFrom ts'
                          (some ((0, none), (st', trades ++ [(e, φ)]))) := by
                    intro ts' ctok hdec'
                    simp [EF.streamReadFrom, EF.streamStep, hdec']
                  rw [hstep _ (c + 1) hdec,
                    hstep _ (Encodable.encode φ) (Encodable.encodek φ)]
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
            simp only [EF.streamStep] at hstep
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

/-! ## Compositional splice contraction (`UnRpnContractsTo`)

`UnRpnContractsTo ts out`: ahead of any continuation, the contraction rewrites the
run `ts` to `out` and proceeds.  Transparent runs contract to themselves; price and
trade chunks with self-delimiting blocks contract to their token-level chunks; and
the relation composes under append — so a spliced serialization contracts to its
token-level serialization by mirroring the concrete concatenation shape. -/

/-- `unRpn` rewrites `ts` to `out` ahead of any continuation. -/
def UnRpnContractsTo (ts out : List ℕ) : Prop :=
  ∀ rest, unRpn (ts ++ rest) = out ++ unRpn rest

lemma UnRpnTransparent.contractsTo {ts : List ℕ} (h : UnRpnTransparent ts) :
    UnRpnContractsTo ts ts := h

lemma UnRpnContractsTo.append {xs ox ys oy : List ℕ}
    (hx : UnRpnContractsTo xs ox) (hy : UnRpnContractsTo ys oy) :
    UnRpnContractsTo (xs ++ ys) (ox ++ oy) := fun rest => by
  rw [List.append_assoc, hx (ys ++ rest), hy rest, List.append_assoc]

/-- A price chunk with a self-delimiting block contracts to the token-level chunk. -/
lemma UnRpnContractsTo.priceChunk {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) (d : ℕ) :
    UnRpnContractsTo (0 :: b ++ [d]) [0, Encodable.encode φ, d] := fun rest => by
  have := unRpn_price_chunk_block hb d rest
  simpa [List.append_assoc] using this

/-- A trade chunk with a self-delimiting block contracts to the token-level chunk. -/
lemma UnRpnContractsTo.tradeChunk {b : List ℕ} {φ : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) :
    UnRpnContractsTo (6 :: b) [6, Encodable.encode φ] := fun rest => by
  simpa using unRpn_trade_chunk_block hb rest

/-- Whole-stream form: a contracting run is its own contraction (empty tail). -/
lemma UnRpnContractsTo.unRpn_eq {ts out : List ℕ} (h : UnRpnContractsTo ts out) :
    unRpn ts = out ++ unRpn [] := by
  simpa using h []

/-- **Trade-splice contraction**: a trade list rendered with transparent coefficient
runs and arbitrary self-delimiting sentence blocks contracts to its token-level
serialization. -/
lemma unRpn_tradeBlocks : ∀ (L : List ((EF × Sentence) × List ℕ)),
    (∀ p ∈ L, UnRpnTransparent (EF.serialize p.1.1)) →
    (∀ p ∈ L, parseRpn p.2.length p.2 = some (p.1.2, [])) →
    unRpn (L.flatMap fun p => EF.serialize p.1.1 ++ 6 :: p.2) =
      serializeTrades (L.map Prod.fst) := by
  intro L
  induction L with
  | nil => intro _ _; rfl
  | cons p L ih =>
      intro htr hblk
      simp only [List.flatMap_cons, List.map_cons]
      rw [List.append_assoc,
        htr p (List.mem_cons_self ..) ((6 :: p.2) ++ (L.flatMap fun q =>
          EF.serialize q.1.1 ++ 6 :: q.2)),
        show (6 :: p.2) ++ (L.flatMap fun q => EF.serialize q.1.1 ++ 6 :: q.2) =
          6 :: (p.2 ++ L.flatMap fun q => EF.serialize q.1.1 ++ 6 :: q.2) from rfl,
        unRpn_trade_chunk_block (hblk p (List.mem_cons_self ..)),
        ih (fun q hq => htr q (List.mem_cons_of_mem _ hq))
          (fun q hq => hblk q (List.mem_cons_of_mem _ hq))]
      rfl

/-! ### The escape-slot automaton

Sentence-slot positions of a flat strategy stream, as a small forward automaton:
mode `0` = base (tags `0`/`6` open sentence slots, `1`/`7` opaque payloads), mode `1`
= price sentence slot (day follows), mode `2` = price day, mode `3` = trade sentence
slot, mode `4` = opaque payload.  Slots are modes `1` and `3`.  Base transitions test
only tags `≤ 7`, so the automaton factors through the digit clamp. -/

/-- One transition of the slot automaton: mode `0` base, `1` price sentence slot, `2`
price day, `3` trade sentence slot, `4` opaque payload.  Base transitions test only tags
`≤ 7`, so the automaton factors through the digit clamp (`escModeStep_clamp`). -/
def escModeStep (m t : ℕ) : ℕ :=
  if m = 0 then
    if t = 0 then 1
    else if t = 6 then 3
    else if t = 1 then 4
    else if t = 7 then 4
    else 0
  else if m = 1 then 2
  else 0

/-- The automaton's mode after reading a prefix; slots are the positions at mode `1` or
`3`. -/
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
      (if m = 1 ∨ m = 3 then (if t = 0 then [1, 0, 2] else [1, t]) else [t]) ++
        escExpandFold (escModeStep m t) rest

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
            cases c <;> rfl
        | c :: d :: r2 =>
            cases c with
            | zero =>
                rw [escExpand_price_zero_chunk]
                change 0 :: 1 :: 0 :: 2 :: d :: escExpandFold 0 r2 = _
                simp only [List.length_cons] at hn
                rw [escExpandFold_eq_escExpand n r2 (by omega)]
            | succ c =>
                rw [escExpand_price_chunk (c + 1) d (by omega)]
                change 0 :: 1 :: (c + 1) :: d :: escExpandFold 0 r2 = _
                simp only [List.length_cons] at hn
                rw [escExpandFold_eq_escExpand n r2 (by omega)]
      by_cases h6 : t = 6
      · subst h6
        match rest with
        | [] => rfl
        | c :: r =>
            cases c with
            | zero =>
                rw [escExpand_trade_zero_chunk]
                change 6 :: 1 :: 0 :: 2 :: escExpandFold 0 r = _
                simp only [List.length_cons] at hn
                rw [escExpandFold_eq_escExpand n r (by omega)]
            | succ c =>
                rw [escExpand_trade_chunk (c + 1) (by omega)]
                change 6 :: 1 :: (c + 1) :: escExpandFold 0 r = _
                simp only [List.length_cons] at hn
                rw [escExpandFold_eq_escExpand n r (by omega)]
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

/-! ## Code-level parsing (for the compiler)

The trading firm's compiler needs the decode primitive recursive.  Building
`Primrec` for `Formula` constructors is unnecessary: parse straight to the *pair
code* — `⊥ ↦ pair 0 0 + 1`, `atom t ↦ pair 1 t + 1`, binops `pair tag (pair c₁ c₂)
+ 1` — and use the `Primcodable` round trip (`encode ∘ decode`) as the escape
validity test.  These mirror `parseRpn`/`unRpnTokens` exactly. -/

/-- Code-level mirror of `parseRpn`: parses straight to the `Primcodable` pair code, using
`encode ∘ decode` as the escape-validity test, so the trading firm's compiler can certify
the decode without `Primrec` instances for `Formula`'s constructors (`parseRpnC_eq`). -/
def parseRpnC : ℕ → List ℕ → Option (ℕ × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
      if t = 0 then some (Nat.pair 0 0 + 1, rest)
      else if t = 1 then
        match rest with
        | 0 :: payload => parseStructuredPaperPrimeC payload
        | c :: tail =>
            if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then none
            else some (Encodable.encode (Encodable.decode (α := Sentence) c) - 1, tail)
        | [] => none
      else if t = 2 then
        (parseRpnC fuel rest).bind fun p =>
          (parseRpnC fuel p.2).bind fun q =>
            some (Nat.pair 2 (Nat.pair p.1 q.1) + 1, q.2)
      else if t = 3 then
        (parseRpnC fuel rest).bind fun p =>
          (parseRpnC fuel p.2).bind fun q =>
            some (Nat.pair 3 (Nat.pair p.1 q.1) + 1, q.2)
      else if t = 4 then
        (parseRpnC fuel rest).bind fun p =>
          (parseRpnC fuel p.2).bind fun q =>
            some (Nat.pair 4 (Nat.pair p.1 q.1) + 1, q.2)
      else some (Nat.pair 1 (t - 5) + 1, rest)

lemma parseRpnC_cons (fuel t : ℕ) (rest : List ℕ) :
    parseRpnC (fuel + 1) (t :: rest) =
      if t = 0 then some (Nat.pair 0 0 + 1, rest)
      else if t = 1 then
        match rest with
        | 0 :: payload => parseStructuredPaperPrimeC payload
        | c :: tail =>
            if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then none
            else some (Encodable.encode (Encodable.decode (α := Sentence) c) - 1, tail)
        | [] => none
      else if t = 2 then
        (parseRpnC fuel rest).bind fun p =>
          (parseRpnC fuel p.2).bind fun q =>
            some (Nat.pair 2 (Nat.pair p.1 q.1) + 1, q.2)
      else if t = 3 then
        (parseRpnC fuel rest).bind fun p =>
          (parseRpnC fuel p.2).bind fun q =>
            some (Nat.pair 3 (Nat.pair p.1 q.1) + 1, q.2)
      else if t = 4 then
        (parseRpnC fuel rest).bind fun p =>
          (parseRpnC fuel p.2).bind fun q =>
            some (Nat.pair 4 (Nat.pair p.1 q.1) + 1, q.2)
      else some (Nat.pair 1 (t - 5) + 1, rest) := rfl

lemma parseStructuredPaperPrimeC_eq (ts : List ℕ) :
    parseStructuredPaperPrimeC ts =
      (parseStructuredPaperPrime ts).map fun pr => (Encodable.encode pr.1, pr.2) := by
  rcases ts with _ | ⟨polarity, framed⟩
  · rfl
  rw [parseStructuredPaperPrimeC, parseStructuredPaperPrime]
  split <;> try rfl
  rcases readStructuredLength framed with _ | ⟨n, payload⟩
  · rfl
  simp only [Option.bind_some]
  split <;> try rfl
  rcases parseStructuredArithmeticFormula n 0 (payload.take n) with _ | ⟨code, rest⟩
  · rfl
  rcases rest with _ | ⟨x, xs⟩
  · by_cases hterm : payload.getD n 0 = 19
    · simp only [hterm, if_true, Option.map_some, Option.some.injEq, Prod.mk.injEq,
        and_true]
      change Nat.pair 1 (Nat.pair 5 (Nat.pair polarity code)) + 1 =
        (Formula.atom (Nat.pair 5 (Nat.pair polarity code)) : Sentence).toNat
      rfl
    · simp only [hterm, if_false, Option.map_none]
  · rfl

/-- Code-level parsing computes exactly the encoded sentence-level parse. -/
lemma parseRpnC_eq : ∀ (fuel : ℕ) (ts : List ℕ),
    parseRpnC fuel ts =
      (parseRpn fuel ts).map fun pr => (Encodable.encode pr.1, pr.2)
  | 0, ts => rfl
  | fuel + 1, [] => rfl
  | fuel + 1, t :: rest => by
      rw [parseRpnC_cons, parseRpn_cons]
      by_cases h0 : t = 0
      · rw [if_pos h0, if_pos h0]
        rfl
      rw [if_neg h0, if_neg h0]
      by_cases h1 : t = 1
      · rw [if_pos h1, if_pos h1]
        rcases rest with _ | ⟨c, r⟩
        · rfl
        cases c with
        | zero => exact parseStructuredPaperPrimeC_eq r
        | succ c =>
            rcases hdec : Encodable.decode (α := Sentence) (c + 1) with _ | φ
            · simp [hdec, Encodable.encode_none]
            · simp [hdec, Encodable.encode_some]
      rw [if_neg h1, if_neg h1]
      have hbin : ∀ (tag : ℕ) (mk : Sentence → Sentence → Sentence),
          (∀ φ ψ, Encodable.encode (mk φ ψ) =
            Nat.pair tag (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) →
          ((parseRpnC fuel rest).bind fun p =>
            (parseRpnC fuel p.2).bind fun q =>
              some (Nat.pair tag (Nat.pair p.1 q.1) + 1, q.2)) =
          ((parseRpn fuel rest).bind fun p =>
            (parseRpn fuel p.2).bind fun q =>
              some (mk p.1 q.1, q.2)).map fun pr => (Encodable.encode pr.1, pr.2) := by
        intro tag mk hmk
        rw [parseRpnC_eq fuel rest]
        rcases parseRpn fuel rest with _ | ⟨φ1, r1⟩
        · rfl
        simp only [Option.map_some, Option.bind_some]
        rw [parseRpnC_eq fuel r1]
        rcases parseRpn fuel r1 with _ | ⟨φ2, r2⟩
        · rfl
        simp only [Option.map_some, Option.bind_some, hmk]
      by_cases h2 : t = 2
      · rw [if_pos h2, if_pos h2]
        exact hbin 2 Formula.imp (fun φ ψ => rfl)
      rw [if_neg h2, if_neg h2]
      by_cases h3 : t = 3
      · rw [if_pos h3, if_pos h3]
        exact hbin 3 Formula.and (fun φ ψ => rfl)
      rw [if_neg h3, if_neg h3]
      by_cases h4 : t = 4
      · rw [if_pos h4, if_pos h4]
        exact hbin 4 Formula.or (fun φ ψ => rfl)
      rw [if_neg h4, if_neg h4]
      rfl

/-! ### The code-level stream contraction -/

/-- Code-level mirror of `unRpnTokens` (`unRpnTokensC_eq`), the form
`Framework/RpnComputation.lean` packages for `Primrec.nat_strong_rec`. -/
def unRpnTokensC : ℕ → List ℕ → List ℕ
  | _, [] => []
  | 0, _ => []
  | fuel + 1, t :: rest =>
      if t = 0 then
        match parseRpnC rest.length rest with
        | none => [0, 0]
        | some (e, r1) =>
            match r1 with
            | [] => [0, e]
            | d :: r2 => 0 :: e :: d :: unRpnTokensC fuel r2
      else if t = 6 then
        match parseRpnC rest.length rest with
        | none => [6, 0]
        | some (e, r1) => 6 :: e :: unRpnTokensC fuel r1
      else if t = 1 then
        match rest with
        | [] => [1]
        | c :: r => 1 :: c :: unRpnTokensC fuel r
      else if t = 7 then
        match rest with
        | [] => [7]
        | c :: r => 7 :: c :: unRpnTokensC fuel r
      else t :: unRpnTokensC fuel rest

lemma unRpnTokensC_cons (fuel t : ℕ) (rest : List ℕ) :
    unRpnTokensC (fuel + 1) (t :: rest) =
      if t = 0 then
        match parseRpnC rest.length rest with
        | none => [0, 0]
        | some (e, r1) =>
            match r1 with
            | [] => [0, e]
            | d :: r2 => 0 :: e :: d :: unRpnTokensC fuel r2
      else if t = 6 then
        match parseRpnC rest.length rest with
        | none => [6, 0]
        | some (e, r1) => 6 :: e :: unRpnTokensC fuel r1
      else if t = 1 then
        match rest with
        | [] => [1]
        | c :: r => 1 :: c :: unRpnTokensC fuel r
      else if t = 7 then
        match rest with
        | [] => [7]
        | c :: r => 7 :: c :: unRpnTokensC fuel r
      else t :: unRpnTokensC fuel rest := rfl

/-- The code-level contraction computes the sentence-level one. -/
lemma unRpnTokensC_eq : ∀ (fuel : ℕ) (ts : List ℕ),
    unRpnTokensC fuel ts = unRpnTokens fuel ts
  | fuel, [] => by cases fuel <;> rfl
  | 0, t :: rest => rfl
  | fuel + 1, t :: rest => by
      rw [unRpnTokensC_cons, unRpnTokens_cons]
      by_cases h0 : t = 0
      · rw [if_pos h0, if_pos h0, parseRpnC_eq]
        rcases parseRpn rest.length rest with _ | ⟨φ, r1⟩
        · rfl
        simp only [Option.map_some]
        rcases r1 with _ | ⟨d, r2⟩
        · rfl
        simp only []
        rw [unRpnTokensC_eq fuel r2]
      rw [if_neg h0, if_neg h0]
      by_cases h6 : t = 6
      · rw [if_pos h6, if_pos h6, parseRpnC_eq]
        rcases parseRpn rest.length rest with _ | ⟨φ, r1⟩
        · rfl
        simp only [Option.map_some]
        rw [unRpnTokensC_eq fuel r1]
      rw [if_neg h6, if_neg h6]
      by_cases h1 : t = 1
      · rw [if_pos h1, if_pos h1]
        rcases rest with _ | ⟨c, r⟩
        · rfl
        simp only []
        rw [unRpnTokensC_eq fuel r]
      rw [if_neg h1, if_neg h1]
      by_cases h7 : t = 7
      · rw [if_pos h7, if_pos h7]
        rcases rest with _ | ⟨c, r⟩
        · rfl
        simp only []
        rw [unRpnTokensC_eq fuel r]
      rw [if_neg h7, if_neg h7]
      rw [unRpnTokensC_eq fuel rest]

/-- `unRpn` through the code-level contraction. -/
lemma unRpn_eq_unRpnTokensC (ts : List ℕ) : unRpn ts = unRpnTokensC ts.length ts :=
  (unRpnTokensC_eq ts.length ts).symm

end LogicalInduction
