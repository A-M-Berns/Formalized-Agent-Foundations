import LogicalInduction.Construction.Witnesses.RpnFreeze

/-!
# Structured spelling patterns: the pattern characterization with no side condition

Renders `app:ifp` (tex:6018): the unconditional spelling characterization the corrected
finite-perturbation freeze recognizer rests on.  `RpnFreeze` handles the legacy grammar, and
the full grammar `parseRpn` under `NoReserved`; this module removes that condition by
listing the structured alternatives.

The residual hypothesis there is exactly the structured paper-prime leaf: at a reserved atom
`atom (Nat.pair 5 _)` the full grammar admits a whole extra family of spellings — the
`[1, 0, …]` blocks — and `RpnFreeze.patterns`, whose alternatives are *single tokens*, cannot
name them, because a structured block's unary length field makes it a variable-width segment.

* `StructBlock pol fc` is the token language of one structured paper-prime block,

      [1, 0, pol] ++ 1^|p| ++ 0 :: p ++ [19]    with  pol ≤ 1  and  p a complete payload.

* `PatSeg` is the segment alphabet — a literal token, an escape payload hole, or a whole
  structured block — with `PatSeg.MatchesSeg` and `SegMatch`.  A run matches a segment
  pattern when it splits, in order, into segment matches.  The split is forced by the *run*
  rather than by the pattern's length, since a structured block is variable-width and
  self-delimiting; that is why `SegMatch` is an existential over decompositions rather than
  a positional `List.Forall₂`.
* `StructBlockRelaxed` / `PatSeg.MatchesRelaxed` / `SegMatchRelaxed` is the relaxed language:
  everything a pattern demands except the length identification, which is the half a
  finite-state device decides.  Its `pol ≤ 1` and `19 ∉ p` conjuncts are load-bearing.
* `structAlts` and `segPatterns` are the complete finite spelling list of a target under the
  full grammar.
* Main results: `parseRpn_block_inv` (seven-way head inversion, the structured block being
  the seventh alternative), `segPatterns_sound`, `segPatterns_complete`, and
  `parseRpn_iff_segMatch` — the characterization with no `BotFree` (the escape's infinite
  decode fibre lives inside a hole) and no `NoReserved` condition on the target.

Consumed by `SegmentAutomaton.lean` and `SegmentCounter.lean`, which split `SegMatch` into
the relaxed and counter halves, and through them by `SegRec.ifParseFull_mem_FP`.
`parseRpn_iff_segMatch`, `segPatterns_sound` and `segPatterns_complete` are in
`AxiomAudit.lean`.
-/

namespace LogicalInduction

open LO.Propositional

namespace StructPat

/-! ## The structured block as a token language -/

/-- The token language of one structured paper-prime block denoting
`atom (Nat.pair 5 (Nat.pair pol fc))`.

This is a transcription of `parseStructuredPaperPrime`'s successful shape: the two-token
dispatch prefix `[1, 0]`, the polarity, the unary length field `1^|p|` closed by `0`, the
payload `p` itself, and the reserved terminator `19`. -/
def StructBlock (pol fc : ℕ) (b : List ℕ) : Prop :=
  ∃ p : List ℕ, b = [1, 0, pol] ++ List.replicate p.length 1 ++ 0 :: p ++ [19] ∧
    pol ≤ 1 ∧ parseStructuredArithmeticFormula p.length 0 p = some (fc, [])

/-- The unary length field reads back exactly what it spells.

Proof kind: `P` proved.  Provenance: (a) induction on the field width. -/
lemma readStructuredLength_replicate (n : ℕ) (r : List ℕ) :
    readStructuredLength (List.replicate n 1 ++ 0 :: r) = some (n, r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, readStructuredLength, ih,
        Option.map_some]

/-- **Every structured block parses**, to the reserved atom it spells.

Proof kind: `P` proved.  Provenance: (a) `readStructuredLength_replicate`;
(b) `parseRpn_cons`, `parseStructuredPaperPrime`. -/
lemma structBlock_parse {pol fc : ℕ} {b : List ℕ} (h : StructBlock pol fc b) :
    parseRpn b.length b = some (Formula.atom (Nat.pair 5 (Nat.pair pol fc)), []) := by
  obtain ⟨p, rfl, hpol, hform⟩ := h
  have hb : ([1, 0, pol] ++ List.replicate p.length 1 ++ 0 :: p ++ [19] : List ℕ) =
      1 :: 0 :: pol :: (List.replicate p.length 1 ++ 0 :: (p ++ [19])) := by
    simp
  rw [hb]
  rw [show (1 :: 0 :: pol :: (List.replicate p.length 1 ++ 0 :: (p ++ [19]))).length =
      (0 :: pol :: (List.replicate p.length 1 ++ 0 :: (p ++ [19]))).length + 1 from rfl,
    parseRpn_cons, if_neg (by omega), if_pos rfl]
  show parseStructuredPaperPrime (pol :: (List.replicate p.length 1 ++ 0 :: (p ++ [19])))
      = _
  rw [parseStructuredPaperPrime, if_pos hpol, readStructuredLength_replicate]
  simp only [Option.bind_some]
  rw [if_pos (by simp)]
  have htake : (p ++ [19]).take p.length = p := List.take_left ..
  rw [htake, hform]
  simp

/-- **Inversion of a structured leaf parse.**  A successful `parseStructuredPaperPrime`
consumes exactly one structured block and denotes exactly the reserved atom that block
spells.

Proof kind: `P` proved.  Provenance: (a) `readStructuredLength_shape`;
(b) `parseStructuredPaperPrime`. -/
lemma parseStructuredPaperPrime_inv {payload : List ℕ} {φ : Sentence} {rest : List ℕ}
    (h : parseStructuredPaperPrime payload = some (φ, rest)) :
    ∃ pol fc b, StructBlock pol fc b ∧
      φ = Formula.atom (Nat.pair 5 (Nat.pair pol fc)) ∧ 1 :: 0 :: payload = b ++ rest := by
  rcases payload with _ | ⟨polarity, framed⟩
  · simp [parseStructuredPaperPrime] at h
  rw [parseStructuredPaperPrime] at h
  split at h <;> try contradiction
  rename_i hpol
  rcases hr : readStructuredLength framed with _ | ⟨n, payload2⟩
  · simp [hr] at h
  rw [hr] at h
  simp only [Option.bind_some] at h
  split at h <;> try contradiction
  rename_i hlen
  rcases hp : parseStructuredArithmeticFormula n 0 (payload2.take n) with _ | ⟨code, r⟩
  · simp [hp] at h
  rw [hp] at h
  rcases r with _ | ⟨x, xs⟩
  · change (if List.getD payload2 n 0 = 19 then
        some (Formula.atom (Nat.pair 5 (Nat.pair polarity code)), payload2.drop (n + 1))
      else none) = some (φ, rest) at h
    by_cases hterm : payload2.getD n 0 = 19
    · rw [if_pos hterm] at h
      obtain ⟨hφ, hrest⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      have hnlt : n < payload2.length := by
        have hne : n ≠ payload2.length := by
          intro heq
          subst n
          simp [List.getD] at hterm
        omega
      have hplen : (payload2.take n).length = n := by
        simp [List.length_take]; omega
      have hpay : payload2 = payload2.take n ++ 19 :: payload2.drop (n + 1) := by
        conv_lhs => rw [← List.take_append_drop n payload2]
        congr 1
        rw [List.drop_eq_getElem_cons hnlt]
        congr 1
        rw [List.getD_eq_getElem _ _ hnlt] at hterm
        exact hterm
      refine ⟨polarity, code, [1, 0, polarity] ++
        List.replicate (payload2.take n).length 1 ++ 0 :: payload2.take n ++ [19],
        ⟨payload2.take n, rfl, hpol, ?_⟩, hφ.symm, ?_⟩
      · rw [hplen]; exact hp
      · rw [readStructuredLength_shape hr, ← hrest, hplen]
        conv_lhs => rw [hpay]
        simp
    · rw [if_neg hterm] at h
      contradiction
  · simp at h

/-! ## Block-level inversion for the full grammar -/

/-- Stripping a complete block off the front of a successful full-grammar parse.

Proof kind: `P` proved.  Provenance: (a) `parseStructuredPaperPrime_inv`,
`structBlock_parse`; (b) `parseRpn_cons`, `parseRpn_block_head`, `parseRpn_mono`. -/
lemma parseRpn_strip : ∀ (fuel : ℕ) (ts : List ℕ) {φ : Sentence} {rest : List ℕ},
    parseRpn fuel ts = some (φ, rest) →
    ∃ blk, ts = blk ++ rest ∧ parseRpn blk.length blk = some (φ, []) := by
  intro fuel
  induction fuel with
  | zero => intro ts φ rest h; simp at h
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
          rw [if_neg h0] at h
          by_cases h1 : t = 1
          · rw [if_pos h1] at h
            subst h1
            rcases ts' with _ | ⟨c₀, ts''⟩
            · simp at h
            cases c₀ with
            | zero =>
                have h' : parseStructuredPaperPrime ts'' = some (φ, rest) := h
                obtain ⟨pol, fc, blk, hsb, hφ, heq⟩ := parseStructuredPaperPrime_inv h'
                exact ⟨blk, heq, by rw [hφ]; exact structBlock_parse hsb⟩
            | succ c =>
                have h' : ((Encodable.decode (α := Sentence) (c + 1)).map
                    fun ψ => (ψ, ts'')) = some (φ, rest) := h
                rcases hdec : (Encodable.decode (α := Sentence) (c + 1)) with _ | ψ
                · rw [hdec] at h'; simp at h'
                rw [hdec] at h'
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
                obtain ⟨rfl, rfl⟩ := h'
                exact ⟨[1, c + 1], rfl, parseRpn_escape' hdec [] (by simp)⟩
          rw [if_neg h1] at h
          have hbin : ∀ (mk : Sentence → Sentence → Sentence),
              ((parseRpn fuel ts').bind fun p =>
                (parseRpn fuel p.2).bind fun q => some (mk p.1 q.1, q.2)) = some (φ, rest) →
              ((t = 2 ∧ mk = Formula.imp) ∨ (t = 3 ∧ mk = Formula.and) ∨
                (t = 4 ∧ mk = Formula.or)) →
              ∃ blk, t :: ts' = blk ++ rest ∧ parseRpn blk.length blk = some (φ, []) := by
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
                    obtain ⟨hφ, hrest⟩ := Prod.mk.injEq .. ▸ Option.some.inj hh
                    obtain ⟨blk₁, hts', hblk₁⟩ := ih ts' hp
                    obtain ⟨blk₂, hp2, hblk₂⟩ := ih p.2 hq
                    refine ⟨t :: blk₁ ++ blk₂, by rw [hts', hp2, hrest]; simp, ?_⟩
                    have hb1 : parseRpn (blk₁.length + blk₂.length) (blk₁ ++ blk₂) =
                        some (p.1, blk₂) := parseRpn_block_head hblk₁ blk₂ (by omega)
                    have hb2 : parseRpn (blk₁.length + blk₂.length) blk₂ = some (q.1, []) :=
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
                    · rw [if_neg (by omega), if_neg (by omega), if_pos rfl, hb1]
                      simp only [Option.bind_some]
                      rw [hb2]
                      simp only [Option.bind_some, ← hφ]
          by_cases h2 : t = 2
          · rw [if_pos h2] at h
            exact hbin _ h (Or.inl ⟨h2, rfl⟩)
          rw [if_neg h2] at h
          by_cases h3 : t = 3
          · rw [if_pos h3] at h
            exact hbin _ h (Or.inr (Or.inl ⟨h3, rfl⟩))
          rw [if_neg h3] at h
          by_cases h4 : t = 4
          · rw [if_pos h4] at h
            exact hbin _ h (Or.inr (Or.inr ⟨h4, rfl⟩))
          rw [if_neg h4] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
          refine ⟨[t], rfl, ?_⟩
          rw [show ([t] : List ℕ).length = 0 + 1 from rfl,
            parseRpn_cons, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4]

/-- Two complete self-delimiting blocks parse in sequence under any binary shell.

Proof kind: `C` composition.  Provenance: (b) `parseRpn_block_head`, `parseRpn_mono`. -/
lemma parseRpn_bin_body {b₁ b₂ : List ℕ} {φ ψ : Sentence}
    (mk : Sentence → Sentence → Sentence) {fuel : ℕ}
    (h₁ : parseRpn b₁.length b₁ = some (φ, []))
    (h₂ : parseRpn b₂.length b₂ = some (ψ, []))
    (hfuel : (b₁ ++ b₂).length ≤ fuel) :
    ((parseRpn fuel (b₁ ++ b₂)).bind fun p =>
        (parseRpn fuel p.2).bind fun q => some (mk p.1 q.1, q.2)) = some (mk φ ψ, []) := by
  simp only [List.length_append] at hfuel
  rw [parseRpn_block_head h₁ b₂ (by omega)]
  simp only [Option.bind_some]
  rw [parseRpn_mono b₂ (by omega) h₂]
  rfl

/-- Inversion of a complete binary-shell parse into its two complete sub-blocks.

Proof kind: `P` proved.  Provenance: (a) `parseRpn_strip`. -/
lemma parseRpn_bin_inv {rest : List ℕ} {fuel : ℕ}
    {mk : Sentence → Sentence → Sentence} {φ : Sentence}
    (h : ((parseRpn fuel rest).bind fun p =>
      (parseRpn fuel p.2).bind fun q => some (mk p.1 q.1, q.2)) = some (φ, [])) :
    ∃ b₁ b₂ φ₁ φ₂, rest = b₁ ++ b₂ ∧ φ = mk φ₁ φ₂ ∧
      parseRpn b₁.length b₁ = some (φ₁, []) ∧
      parseRpn b₂.length b₂ = some (φ₂, []) := by
  rcases hp : parseRpn fuel rest with _ | ⟨φ₁, r₁⟩
  · rw [hp] at h; simp at h
  rw [hp] at h
  simp only [Option.bind_some] at h
  rcases hq : parseRpn fuel r₁ with _ | ⟨φ₂, r₂⟩
  · rw [hq] at h; simp at h
  rw [hq] at h
  simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hmk, rfl⟩ := h
  obtain ⟨b₁, hb₁, hpb₁⟩ := parseRpn_strip fuel rest hp
  obtain ⟨b₂, hb₂, hpb₂⟩ := parseRpn_strip fuel r₁ hq
  rw [List.append_nil] at hb₂
  subst hb₂
  exact ⟨b₁, r₁, φ₁, φ₂, hb₁, hmk.symm, hpb₁, hpb₂⟩

/-- **Inversion of a complete full-grammar block parse at its head token.**

Seven-way inversion; the structured paper-prime block is the seventh alternative.

Proof kind: `P` proved.  Provenance: (a) `parseStructuredPaperPrime_inv`,
`parseRpn_bin_inv`; (b) `parseRpn_cons`. -/
lemma parseRpn_block_inv {b : List ℕ} {ψ : Sentence}
    (h : parseRpn b.length b = some (ψ, [])) :
    (b = [0] ∧ ψ = ⊥) ∨
    (∃ c, b = [1, c] ∧ (Encodable.decode c : Option Sentence) = some ψ) ∨
    (∃ pol fc, StructBlock pol fc b ∧
      ψ = Formula.atom (Nat.pair 5 (Nat.pair pol fc))) ∨
    (∃ b₁ b₂ φ₁ φ₂, b = 2 :: (b₁ ++ b₂) ∧ ψ = φ₁ 🡒 φ₂ ∧
      parseRpn b₁.length b₁ = some (φ₁, []) ∧
      parseRpn b₂.length b₂ = some (φ₂, [])) ∨
    (∃ b₁ b₂ φ₁ φ₂, b = 3 :: (b₁ ++ b₂) ∧ ψ = φ₁ ⋏ φ₂ ∧
      parseRpn b₁.length b₁ = some (φ₁, []) ∧
      parseRpn b₂.length b₂ = some (φ₂, [])) ∨
    (∃ b₁ b₂ φ₁ φ₂, b = 4 :: (b₁ ++ b₂) ∧ ψ = φ₁ ⋎ φ₂ ∧
      parseRpn b₁.length b₁ = some (φ₁, []) ∧
      parseRpn b₂.length b₂ = some (φ₂, [])) ∨
    (∃ a, b = [a + 5] ∧ ψ = Formula.atom a) := by
  cases b with
  | nil => simp at h
  | cons t rest =>
      rw [List.length_cons, parseRpn_cons] at h
      by_cases h0 : t = 0
      · subst h0
        rw [if_pos rfl] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
        subst h2
        exact Or.inl ⟨rfl, h1.symm⟩
      rw [if_neg h0] at h
      by_cases h1 : t = 1
      · subst h1
        rw [if_pos rfl] at h
        rcases rest with _ | ⟨c₀, tail⟩
        · simp at h
        cases c₀ with
        | zero =>
            have h' : parseStructuredPaperPrime tail = some (ψ, []) := h
            obtain ⟨pol, fc, blk, hsb, hψ, heq⟩ := parseStructuredPaperPrime_inv h'
            rw [List.append_nil] at heq
            exact Or.inr (Or.inr (Or.inl ⟨pol, fc, heq ▸ hsb, hψ⟩))
        | succ c =>
            have h' : ((Encodable.decode (α := Sentence) (c + 1)).map
                fun φ => (φ, tail)) = some (ψ, []) := h
            rcases hdec : (Encodable.decode (α := Sentence) (c + 1)) with _ | φ
            · rw [hdec] at h'; simp at h'
            rw [hdec] at h'
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
            obtain ⟨rfl, rfl⟩ := h'
            exact Or.inr (Or.inl ⟨c + 1, rfl, hdec⟩)
      rw [if_neg h1] at h
      by_cases h2 : t = 2
      · subst h2
        rw [if_pos rfl] at h
        obtain ⟨b₁, b₂, φ₁, φ₂, hsplit, hmk, hp₁, hp₂⟩ := parseRpn_bin_inv h
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨b₁, b₂, φ₁, φ₂, by rw [hsplit], hmk, hp₁, hp₂⟩)))
      rw [if_neg h2] at h
      by_cases h3 : t = 3
      · subst h3
        rw [if_pos rfl] at h
        obtain ⟨b₁, b₂, φ₁, φ₂, hsplit, hmk, hp₁, hp₂⟩ := parseRpn_bin_inv h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨b₁, b₂, φ₁, φ₂, by rw [hsplit], hmk, hp₁, hp₂⟩))))
      rw [if_neg h3] at h
      by_cases h4 : t = 4
      · subst h4
        rw [if_pos rfl] at h
        obtain ⟨b₁, b₂, φ₁, φ₂, hsplit, hmk, hp₁, hp₂⟩ := parseRpn_bin_inv h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨b₁, b₂, φ₁, φ₂, by rw [hsplit], hmk, hp₁, hp₂⟩)))))
      rw [if_neg h4] at h
      obtain ⟨hφ, ht⟩ := Prod.mk.inj (Option.some.inj h)
      subst ht
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t - 5, ?_, hφ.symm⟩)))))
      congr 1
      omega

/-! ## Segment patterns -/

/-- One segment of a spelling pattern: a fixed token, an escape payload slot, or a whole
structured paper-prime block. -/
inductive PatSeg
  | /-- A fixed grammar token. -/ lit (t : ℕ)
  | /-- An escape payload slot for the subformula `χ`. -/ hole (χ : Sentence)
  | /-- A structured paper-prime block denoting `atom (Nat.pair 5 (Nat.pair pol fc))`. -/
    struct (pol fc : ℕ)

/-- What a single pattern segment demands of the run fragment in its position. -/
def PatSeg.MatchesSeg : PatSeg → List ℕ → Prop
  | .lit t, b => b = [t]
  | .hole χ, b => ∃ c, b = [c] ∧ (Encodable.decode c : Option Sentence) = some χ
  | .struct pol fc, b => StructBlock pol fc b

@[simp] lemma PatSeg.matchesSeg_lit (t : ℕ) (b : List ℕ) :
    (PatSeg.lit t).MatchesSeg b ↔ b = [t] := Iff.rfl

@[simp] lemma PatSeg.matchesSeg_hole (χ : Sentence) (b : List ℕ) :
    (PatSeg.hole χ).MatchesSeg b ↔
      ∃ c, b = [c] ∧ (Encodable.decode c : Option Sentence) = some χ := Iff.rfl

@[simp] lemma PatSeg.matchesSeg_struct (pol fc : ℕ) (b : List ℕ) :
    (PatSeg.struct pol fc).MatchesSeg b ↔ StructBlock pol fc b := Iff.rfl

/-- A run matches a pattern when it splits into segment matches, in order. -/
def SegMatch (p : List PatSeg) (b : List ℕ) : Prop :=
  ∃ bs : List (List ℕ), List.Forall₂ PatSeg.MatchesSeg p bs ∧ b = bs.flatten

lemma segMatch_nil (b : List ℕ) : SegMatch [] b ↔ b = [] := by
  constructor
  · rintro ⟨bs, hf, rfl⟩
    rw [List.forall₂_nil_left_iff.mp hf]
    rfl
  · rintro rfl
    exact ⟨[], List.Forall₂.nil, rfl⟩

lemma segMatch_cons_left_iff {σ : PatSeg} {p : List PatSeg} {b : List ℕ} :
    SegMatch (σ :: p) b ↔ ∃ b₁ b₂, σ.MatchesSeg b₁ ∧ SegMatch p b₂ ∧ b = b₁ ++ b₂ := by
  constructor
  · rintro ⟨bs, hf, rfl⟩
    obtain ⟨b₁, bs', h₁, hrest, rfl⟩ := List.forall₂_cons_left_iff.mp hf
    exact ⟨b₁, bs'.flatten, h₁, ⟨bs', hrest, rfl⟩, by simp⟩
  · rintro ⟨b₁, b₂, h₁, ⟨bs, hf, rfl⟩, rfl⟩
    exact ⟨b₁ :: bs, List.Forall₂.cons h₁ hf, by simp⟩

lemma segMatch_cons {σ : PatSeg} {p : List PatSeg} {b₁ b₂ : List ℕ}
    (h₁ : σ.MatchesSeg b₁) (h₂ : SegMatch p b₂) : SegMatch (σ :: p) (b₁ ++ b₂) :=
  segMatch_cons_left_iff.mpr ⟨b₁, b₂, h₁, h₂, rfl⟩

lemma segMatch_single {σ : PatSeg} {b : List ℕ} (h : σ.MatchesSeg b) : SegMatch [σ] b :=
  ⟨[b], List.Forall₂.cons h List.Forall₂.nil, by simp⟩

lemma segMatch_append {p₁ p₂ : List PatSeg} {b₁ b₂ : List ℕ}
    (h₁ : SegMatch p₁ b₁) (h₂ : SegMatch p₂ b₂) : SegMatch (p₁ ++ p₂) (b₁ ++ b₂) := by
  obtain ⟨bs₁, hf₁, rfl⟩ := h₁
  obtain ⟨bs₂, hf₂, rfl⟩ := h₂
  exact ⟨bs₁ ++ bs₂, List.rel_append hf₁ hf₂, by simp⟩

/-- Splitting a match along a concatenation of patterns. -/
lemma segMatch_append_inv : ∀ (p₁ p₂ : List PatSeg) (b : List ℕ),
    SegMatch (p₁ ++ p₂) b → ∃ b₁ b₂, b = b₁ ++ b₂ ∧ SegMatch p₁ b₁ ∧ SegMatch p₂ b₂ := by
  intro p₁
  induction p₁ with
  | nil => intro p₂ b h; exact ⟨[], b, rfl, (segMatch_nil []).mpr rfl, h⟩
  | cons σ p ih =>
      intro p₂ b h
      rw [List.cons_append, segMatch_cons_left_iff] at h
      obtain ⟨b₀, b', hσ, hrest, rfl⟩ := h
      obtain ⟨b₁, b₂, rfl, h₁, h₂⟩ := ih p₂ b' hrest
      exact ⟨b₀ ++ b₁, b₂, by simp, segMatch_cons hσ h₁, h₂⟩

/-! ### The relaxed language: the half a finite-state device can decide

A structured block's unary length field must equal its payload's own token count, and that
is an `aⁿbⁿ` constraint no bounded-state device decides.  The recognizer therefore splits
the match in two, and this is the half that survives the split: everything a pattern demands
*except* the length identification.  The other half is a one-counter machine
(`SegCtr.segCtr`), and `SegCtr.segMatch_iff_relaxed_and_ctr` shows the split is exact.

Two conjuncts here are load-bearing rather than decorative.  `pol ≤ 1` is what
`parseStructuredPaperPrime` demands of the polarity slot, so a pattern naming an
out-of-range polarity has *empty* relaxed language and the automaton's polarity row has to
enforce it.  `19 ∉ p` is what makes the block self-delimiting: the terminator is the first
`19`, and a complete payload parse never contains one
(`PayAuto.nineteen_not_mem_of_parse`). -/

/-- A structured block with the length field NOT checked against the payload length. -/
def StructBlockRelaxed (pol fc : ℕ) (b : List ℕ) : Prop :=
  ∃ (L : ℕ) (p : List ℕ),
    b = [1, 0, pol] ++ List.replicate L 1 ++ 0 :: p ++ [19] ∧ pol ≤ 1 ∧
      parseStructuredArithmeticFormula p.length 0 p = some (fc, []) ∧ 19 ∉ p

/-- What a single pattern segment demands once the length identification is dropped. -/
def PatSeg.MatchesRelaxed : PatSeg → List ℕ → Prop
  | .lit t, b => b = [t]
  | .hole χ, b => ∃ c, b = [c] ∧ (Encodable.decode c : Option Sentence) = some χ
  | .struct pol fc, b => StructBlockRelaxed pol fc b

/-- A run matches a pattern relaxedly when it splits, in order, into relaxed segment
matches. -/
def SegMatchRelaxed (p : List PatSeg) (b : List ℕ) : Prop :=
  ∃ bs : List (List ℕ), List.Forall₂ PatSeg.MatchesRelaxed p bs ∧ b = bs.flatten

/-- The structured alternatives available at an atom.  They exist exactly at the reserved
shape `atom (Nat.pair 5 (Nat.pair pol fc))` with `pol ≤ 1`, which is the only sentence a
structured block can denote (`parseStructuredPaperPrime_inv`). -/
def structAlts (a : ℕ) : List (List PatSeg) :=
  if a.unpair.1 = 5 ∧ a.unpair.2.unpair.1 ≤ 1 then
    [[PatSeg.struct a.unpair.2.unpair.1 a.unpair.2.unpair.2]] else []

/-- The complete spelling patterns of a target under the **full** grammar `parseRpn`.

This mirrors `RpnFreeze.patterns` and adds, at each atom, the structured alternatives. -/
def segPatterns : Sentence → List (List PatSeg)
  | ⊥ => [[.lit 0], [.lit 1, .hole ⊥]]
  | .atom a =>
      [[.lit (a + 5)], [.lit 1, .hole (Formula.atom a : Sentence)]] ++ structAlts a
  | φ 🡒 χ =>
      [.lit 1, .hole (φ 🡒 χ)] ::
        (segPatterns φ).flatMap fun p₁ =>
          (segPatterns χ).map fun p₂ => PatSeg.lit 2 :: (p₁ ++ p₂)
  | φ ⋏ χ =>
      [.lit 1, .hole (φ ⋏ χ)] ::
        (segPatterns φ).flatMap fun p₁ =>
          (segPatterns χ).map fun p₂ => PatSeg.lit 3 :: (p₁ ++ p₂)
  | φ ⋎ χ =>
      [.lit 1, .hole (φ ⋎ χ)] ::
        (segPatterns φ).flatMap fun p₁ =>
          (segPatterns χ).map fun p₂ => PatSeg.lit 4 :: (p₁ ++ p₂)

/-- The escape pattern is listed for **every** target. -/
lemma escape_mem_segPatterns (ψ : Sentence) :
    [PatSeg.lit 1, PatSeg.hole ψ] ∈ segPatterns ψ := by
  -- `simp` leaves the residual `Formula.falsum = ⊥` / `a.and b = a ⋏ b` goals: the
  -- `segPatterns` equations are stated in the `LogicalConnective` notation, which is only
  -- *defeq* to the raw constructor `cases` produces.
  cases ψ <;> simp [segPatterns] <;> rfl

private lemma segMatch_escape_parse {ψ : Sentence} {b : List ℕ}
    (h : SegMatch [PatSeg.lit 1, PatSeg.hole ψ] b) :
    parseRpn b.length b = some (ψ, []) := by
  obtain ⟨b₀, b', hb₀, h', rfl⟩ := segMatch_cons_left_iff.mp h
  obtain ⟨b₁, b₂, hb₁, h₂, rfl⟩ := segMatch_cons_left_iff.mp h'
  have hb₂ : b₂ = [] := (segMatch_nil b₂).mp h₂
  subst hb₂
  have hb₀' : b₀ = [1] := hb₀
  subst hb₀'
  obtain ⟨c, rfl, hdec⟩ := hb₁
  simpa using parseRpn_escape' (fuel := 2) hdec [] (by norm_num)

/-- The reserved atom carried by a structured alternative is the atom itself. -/
private lemma reserved_pair_eq {a : ℕ} (h5 : a.unpair.1 = 5) :
    Nat.pair 5 (Nat.pair a.unpair.2.unpair.1 a.unpair.2.unpair.2) = a := by
  rw [Nat.pair_unpair, ← h5, Nat.pair_unpair]

/-! ## Soundness, completeness, and the characterization -/

/-- **Every listed segment pattern really parses**, for every target — no side condition.

Proof kind: `P` proved.  Provenance: (a) `structBlock_parse`, `parseRpn_bin_body`,
`segMatch_escape_parse`.
Paper node: `app:ifp` -/
lemma segPatterns_sound : ∀ (ψ : Sentence), ∀ p ∈ segPatterns ψ, ∀ b : List ℕ,
    SegMatch p b → parseRpn b.length b = some (ψ, []) := by
  have hbin : ∀ (t : ℕ) (p₁ p₂ : List PatSeg) (φ χ : Sentence) (b : List ℕ),
      SegMatch (PatSeg.lit t :: (p₁ ++ p₂)) b →
      (∀ b₁, SegMatch p₁ b₁ → parseRpn b₁.length b₁ = some (φ, [])) →
      (∀ b₂, SegMatch p₂ b₂ → parseRpn b₂.length b₂ = some (χ, [])) →
      ∃ b₁ b₂, b = t :: (b₁ ++ b₂) ∧
        parseRpn b₁.length b₁ = some (φ, []) ∧
        parseRpn b₂.length b₂ = some (χ, []) := by
    intro t p₁ p₂ φ χ b hb h₁ h₂
    obtain ⟨b₀, b', hb₀, hrest, rfl⟩ := segMatch_cons_left_iff.mp hb
    have hb₀' : b₀ = [t] := hb₀
    subst hb₀'
    obtain ⟨c₁, c₂, rfl, hm₁, hm₂⟩ := segMatch_append_inv p₁ p₂ b' hrest
    exact ⟨c₁, c₂, by simp, h₁ c₁ hm₁, h₂ c₂ hm₂⟩
  intro ψ
  induction ψ using LO.Propositional.Formula.rec' with
  | hfalsum =>
      intro p hp b hb
      simp only [segPatterns, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · obtain ⟨b₀, b', hb₀, h', rfl⟩ := segMatch_cons_left_iff.mp hb
        have hb' : b' = [] := (segMatch_nil b').mp h'
        subst hb'
        have hb₀' : b₀ = [0] := hb₀
        subst hb₀'
        rfl
      · exact segMatch_escape_parse hb
  | hatom a =>
      intro p hp b hb
      rcases List.mem_append.mp hp with hp' | hp'
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl
        · obtain ⟨b₀, b', hb₀, h', rfl⟩ := segMatch_cons_left_iff.mp hb
          have hb' : b' = [] := (segMatch_nil b').mp h'
          subst hb'
          have hb₀' : b₀ = [a + 5] := hb₀
          subst hb₀'
          rw [show ([a + 5] ++ ([] : List ℕ)) = [a + 5] from rfl,
            show ([a + 5] : List ℕ).length = 0 + 1 from rfl, parseRpn_cons,
            if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega)]
          simp
        · exact segMatch_escape_parse hb
      · unfold structAlts at hp'
        split at hp'
        · rename_i hcond
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          subst hp'
          obtain ⟨b₀, b', hb₀, h', rfl⟩ := segMatch_cons_left_iff.mp hb
          have hb' : b' = [] := (segMatch_nil b').mp h'
          subst hb'
          rw [List.append_nil]
          have := structBlock_parse (b := b₀) hb₀
          rw [reserved_pair_eq hcond.1] at this
          exact this
        · simp at hp'
  | himp φ χ ihφ ihχ =>
      intro p hp b hb
      simp only [segPatterns, List.mem_cons, List.mem_flatMap, List.mem_map] at hp
      rcases hp with rfl | ⟨p₁, hp₁, p₂, hp₂, rfl⟩
      · exact segMatch_escape_parse hb
      · obtain ⟨b₁, b₂, rfl, h₁, h₂⟩ :=
          hbin 2 p₁ p₂ φ χ b hb (fun b₁ h => ihφ p₁ hp₁ b₁ h) (fun b₂ h => ihχ p₂ hp₂ b₂ h)
        rw [show ((2 : ℕ) :: (b₁ ++ b₂)).length = (b₁ ++ b₂).length + 1 by simp,
          parseRpn_cons, if_neg (by omega), if_neg (by omega), if_pos rfl]
        exact parseRpn_bin_body Formula.imp h₁ h₂ le_rfl
  | hand φ χ ihφ ihχ =>
      intro p hp b hb
      simp only [segPatterns, List.mem_cons, List.mem_flatMap, List.mem_map] at hp
      rcases hp with rfl | ⟨p₁, hp₁, p₂, hp₂, rfl⟩
      · exact segMatch_escape_parse hb
      · obtain ⟨b₁, b₂, rfl, h₁, h₂⟩ :=
          hbin 3 p₁ p₂ φ χ b hb (fun b₁ h => ihφ p₁ hp₁ b₁ h) (fun b₂ h => ihχ p₂ hp₂ b₂ h)
        rw [show ((3 : ℕ) :: (b₁ ++ b₂)).length = (b₁ ++ b₂).length + 1 by simp,
          parseRpn_cons, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos rfl]
        exact parseRpn_bin_body Formula.and h₁ h₂ le_rfl
  | hor φ χ ihφ ihχ =>
      intro p hp b hb
      simp only [segPatterns, List.mem_cons, List.mem_flatMap, List.mem_map] at hp
      rcases hp with rfl | ⟨p₁, hp₁, p₂, hp₂, rfl⟩
      · exact segMatch_escape_parse hb
      · obtain ⟨b₁, b₂, rfl, h₁, h₂⟩ :=
          hbin 4 p₁ p₂ φ χ b hb (fun b₁ h => ihφ p₁ hp₁ b₁ h) (fun b₂ h => ihχ p₂ hp₂ b₂ h)
        rw [show ((4 : ℕ) :: (b₁ ++ b₂)).length = (b₁ ++ b₂).length + 1 by simp,
          parseRpn_cons, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_pos rfl]
        exact parseRpn_bin_body Formula.or h₁ h₂ le_rfl

/-- **The segment pattern list is exhaustive — unconditionally.**

Every complete *full-grammar* parse of *any* target matches one of the finitely many listed
segment patterns: the structured alternative is listed at the one node shape that can carry
it, and the inversion's seventh branch lands on it.

Proof kind: `P` proved.  Provenance: (a) `parseRpn_block_inv`, `escape_mem_segPatterns`,
`segMatch_append`.
Paper node: `app:ifp` -/
lemma segPatterns_complete : ∀ (ψ : Sentence), ∀ b : List ℕ,
    parseRpn b.length b = some (ψ, []) → ∃ p ∈ segPatterns ψ, SegMatch p b := by
  have hesc : ∀ (ψ : Sentence) (c : ℕ),
      (Encodable.decode c : Option Sentence) = some ψ →
      ∃ p ∈ segPatterns ψ, SegMatch p [1, c] := by
    intro ψ c hd
    refine ⟨_, escape_mem_segPatterns ψ, ?_⟩
    exact segMatch_cons (b₁ := [1]) rfl (segMatch_single ⟨c, rfl, hd⟩)
  intro ψ
  induction ψ using LO.Propositional.Formula.rec' with
  | hfalsum =>
      intro b hb
      rcases parseRpn_block_inv hb with
        ⟨rfl, _⟩ | ⟨c, rfl, hd⟩ | ⟨_, _, _, hψ⟩ | ⟨_, _, _, _, rfl, hψ, _, _⟩ |
        ⟨_, _, _, _, rfl, hψ, _, _⟩ | ⟨_, _, _, _, rfl, hψ, _, _⟩ | ⟨a', rfl, hψ⟩
      · exact ⟨[PatSeg.lit 0], by simp [segPatterns], segMatch_single rfl⟩
      · exact hesc _ c hd
      · exact absurd hψ (by simp)
      · exact absurd hψ (by simp)
      · exact absurd hψ (by simp)
      · exact absurd hψ (by simp)
      · exact absurd hψ (by simp)
  | hatom a =>
      intro b hb
      rcases parseRpn_block_inv hb with
        ⟨rfl, hψ⟩ | ⟨c, rfl, hd⟩ | ⟨pol, fc, hsb, hψ⟩ | ⟨_, _, _, _, rfl, hψ, _, _⟩ |
        ⟨_, _, _, _, rfl, hψ, _, _⟩ | ⟨_, _, _, _, rfl, hψ, _, _⟩ | ⟨a', rfl, hψ⟩
      · exact absurd hψ (by simp)
      · exact hesc _ c hd
      · obtain rfl := (Formula.atom.inj hψ).symm
        obtain ⟨_, _, hpol, _⟩ := id hsb
        have h5 : (Nat.pair 5 (Nat.pair pol fc)).unpair.1 = 5 := by
          simp [Nat.unpair_pair]
        have h2 : (Nat.pair 5 (Nat.pair pol fc)).unpair.2 = Nat.pair pol fc := by
          simp [Nat.unpair_pair]
        refine ⟨[PatSeg.struct pol fc], ?_, segMatch_single hsb⟩
        refine List.mem_append.mpr (Or.inr ?_)
        unfold structAlts
        rw [if_pos ⟨h5, by rw [h2]; simpa using hpol⟩]
        rw [h2]
        simp
      · exact absurd hψ (by simp)
      · exact absurd hψ (by simp)
      · exact absurd hψ (by simp)
      · obtain rfl := Formula.atom.inj hψ
        exact ⟨[PatSeg.lit (a + 5)], by simp [segPatterns], segMatch_single rfl⟩
  | himp φ χ ihφ ihχ =>
      intro b hb
      rcases parseRpn_block_inv hb with
        ⟨rfl, hψ⟩ | ⟨c, rfl, hd⟩ | ⟨_, _, _, hψ⟩ |
        ⟨b₁, b₂, φ₁, φ₂, rfl, hψ, hp₁, hp₂⟩ | ⟨_, _, _, _, rfl, hψ, _, _⟩ |
        ⟨_, _, _, _, rfl, hψ, _, _⟩ | ⟨a', rfl, hψ⟩
      · exact absurd hψ (by simp)
      · exact hesc _ c hd
      · exact absurd hψ (by simp)
      · obtain ⟨rfl, rfl⟩ := Formula.imp.inj hψ
        obtain ⟨p₁, hm₁, hb₁⟩ := ihφ b₁ hp₁
        obtain ⟨p₂, hm₂, hb₂⟩ := ihχ b₂ hp₂
        refine ⟨PatSeg.lit 2 :: (p₁ ++ p₂), ?_,
          segMatch_cons (b₁ := [2]) rfl (segMatch_append hb₁ hb₂)⟩
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
          ⟨p₁, hm₁, List.mem_map.mpr ⟨p₂, hm₂, rfl⟩⟩)
      · exact absurd hψ (by simp)
      · exact absurd hψ (by simp)
      · exact absurd hψ (by simp)
  | hand φ χ ihφ ihχ =>
      intro b hb
      rcases parseRpn_block_inv hb with
        ⟨rfl, hψ⟩ | ⟨c, rfl, hd⟩ | ⟨_, _, _, hψ⟩ | ⟨_, _, _, _, rfl, hψ, _, _⟩ |
        ⟨b₁, b₂, φ₁, φ₂, rfl, hψ, hp₁, hp₂⟩ | ⟨_, _, _, _, rfl, hψ, _, _⟩ | ⟨a', rfl, hψ⟩
      · exact absurd hψ (by simp)
      · exact hesc _ c hd
      · exact absurd hψ (by simp)
      · exact absurd hψ (by simp)
      · obtain ⟨rfl, rfl⟩ := Formula.and.inj hψ
        obtain ⟨p₁, hm₁, hb₁⟩ := ihφ b₁ hp₁
        obtain ⟨p₂, hm₂, hb₂⟩ := ihχ b₂ hp₂
        refine ⟨PatSeg.lit 3 :: (p₁ ++ p₂), ?_,
          segMatch_cons (b₁ := [3]) rfl (segMatch_append hb₁ hb₂)⟩
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
          ⟨p₁, hm₁, List.mem_map.mpr ⟨p₂, hm₂, rfl⟩⟩)
      · exact absurd hψ (by simp)
      · exact absurd hψ (by simp)
  | hor φ χ ihφ ihχ =>
      intro b hb
      rcases parseRpn_block_inv hb with
        ⟨rfl, hψ⟩ | ⟨c, rfl, hd⟩ | ⟨_, _, _, hψ⟩ | ⟨_, _, _, _, rfl, hψ, _, _⟩ |
        ⟨_, _, _, _, rfl, hψ, _, _⟩ | ⟨b₁, b₂, φ₁, φ₂, rfl, hψ, hp₁, hp₂⟩ | ⟨a', rfl, hψ⟩
      · exact absurd hψ (by simp)
      · exact hesc _ c hd
      · exact absurd hψ (by simp)
      · exact absurd hψ (by simp)
      · exact absurd hψ (by simp)
      · obtain ⟨rfl, rfl⟩ := Formula.or.inj hψ
        obtain ⟨p₁, hm₁, hb₁⟩ := ihφ b₁ hp₁
        obtain ⟨p₂, hm₂, hb₂⟩ := ihχ b₂ hp₂
        refine ⟨PatSeg.lit 4 :: (p₁ ++ p₂), ?_,
          segMatch_cons (b₁ := [4]) rfl (segMatch_append hb₁ hb₂)⟩
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
          ⟨p₁, hm₁, List.mem_map.mpr ⟨p₂, hm₂, rfl⟩⟩)
      · exact absurd hψ (by simp)

/-- **The characterization, with every side condition gone.**

A run denotes `ψ` under the full grammar `parseRpn` exactly when it matches one of `ψ`'s
finitely many segment patterns — for *every* `ψ`: `⊥` subformulas and reserved atoms
included.  `RpnFreeze.parseRpn_iff_patMatch` is the `NoReserved` form.

Proof kind: `C` composition.  Provenance: (a) `segPatterns_sound`,
`segPatterns_complete`.
Paper node: `app:ifp` -/
lemma parseRpn_iff_segMatch (ψ : Sentence) (b : List ℕ) :
    parseRpn b.length b = some (ψ, []) ↔ ∃ p ∈ segPatterns ψ, SegMatch p b :=
  ⟨segPatterns_complete ψ b, fun ⟨_, hp, hm⟩ => segPatterns_sound ψ _ hp b hm⟩

end StructPat

end LogicalInduction
