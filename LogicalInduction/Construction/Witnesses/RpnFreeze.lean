/-
# Symbol-level finite-prefix freeze compiler

`Properties/FinitePerturbations.lean` compiles the administrative prefix freeze
`EF.freezeBefore` into a flat streaming transducer over the *contracted* strategy stream
(`EF.freezeTokenRun`): after a price frame `[0, ⌜φ⌝, day]` with `day < cutoff` it appends
the constant-quote suffix `[1, quote, 8]`.  The collapsed efficiency class
`EfficientlyComputable` meters the RPN-expanded stream, where the sentence slot is a
symbol **run** rather than a single pair code, so the freeze must walk the flat grammar
and — at a price-day position — look the quote up *from the run*.

The lookup is the whole content of this file.  The LIA's prefix quote table is a finite
list of `(sentence, rational)` entries (`PrefixPatchCompile.liaPrefixQuote`), so for each
table sentence we must decide whether the buffered run denotes it.  The list-level
decision `runMatches` runs the full block parser, so it covers every block of the
extended grammar — structured paper-prime leaves included — and transfers the
token-model table verbatim (`runQuoteFromEntries_exact`,
`runPrefixQuoteFromStates_exact`).

The *positional* matcher is scoped to the legacy fragment.  A legacy run for a fixed
target is a fixed *constant-depth* pattern — the target's Polish traversal, with any
subterm optionally replaced by the two-token escape `[1, code]` — so the decision is a
bounded composition of token comparisons, not a scan: `matchRun` recurses on the target
sentence and returns the position just past the matched run.  Its characterization
`matchRun_iff` (soundness `matchRun_sound` + completeness `matchRun_complete`) stops
exactly at the block's end iff the block parses **in the legacy grammar**
(`parseRpnLegacy`).  A structured paper-prime leaf has no constant-depth positional
decision: its payload admits non-canonical spellings, so the positional test would have
to replay the structured parser, whose contracted state is a whole Foundation code —
the same side of the `dd:fuel` boundary as the escape decode below.  The positional
chain (`runMatchesLegacy`, `runQuoteFromEntriesAt`, `runPrefixQuoteFromStatesAt`)
therefore certifies the legacy fragment only.

The transducer itself is an instance of the emitter-generic run rewriter in
`RpnConditioning.lean`: `freezeEmit` plugs into `rpnConditionRun`, so the commutation
`unRpn_rpnConditionRun_of` and the emission certificate
`rpnGuardedConditionRun_polySegStream_of` are reused rather than reproved.

## Disclosed residual: the emission certificate

This residual predates the structured first-order leaf and is independent of it: the
obstruction is `decode` on an exponentially large escape payload, which the structured
codec neither introduces nor worsens.  A structured leaf simply lands on the same side of
the boundary, for the reason given above.

Everything below is unconditional and axiom-clean, but it does **not** yield
`liaEfficientPrefixPatch`.  The missing step is the fuel certificate for the emitted
segment: `matchRun_polyFueled` asks for a `PolyFueled` (poly-*bounded*) token function,
whereas a digit stream supplies only `BigDigits`.  The one test that does not factor
through a small clamp is the escape leaf, which must decide `Encodable.decode c = some ψ`
for an exponentially large `c`; since Foundation's `Formula.ofNat` ignores the payload at
tag `0`, `decode` is not injective, so the test reduces to `Nat.unpair` / integer square
root, which `BigDigits` does not close over.

**Narrowed (`matchRun_eq_matchRunCanon`, below).**  That decode ambiguity is caused
*entirely* by `⊥`: `CanonicalCodes.lean` proves Foundation's decoder injective on every
sentence with no `⊥` subformula, and exhibits the two codes that break it at `⊥`.  So on
a `⊥`-free target the escape test is a comparison against a fixed numeral, `matchRun`
agrees with the constant-comparison matcher `matchRunCanon`, and **no square root is
needed at all**.  The disclosure below therefore binds exactly when the frozen quote table
contains a sentence with a `⊥` subformula.

That gap is a limitation of the fuel model (`dd:fuel`), not of the mathematics: in the
intended complexity model the claim holds, since `unpair` on poly-bit inputs is
poly-time.  Closing it inside the fuel calculus — a `BigDigits.sqrt` — is blocked
structurally rather than by effort.  `BigDigits` is closed under an operation exactly
when that operation's base-4 digit recurrence has a poly-bounded carry (`addCarry4 ≤ 1`,
`mulCarry4 x y p ≤ 3(p+1)`, `ltFlag4 ≤ 1`, …), because the iterated state of
`PolyFueled.prec` must be `IsPolyBounded`; and, more fundamentally, `evaln`'s guard
bounds every sub-code's input by its fuel, so the fuel calculus admits no large
intermediates anywhere.  Square root's carry is the partial remainder, which has `Θ(len)`
digits and cannot be compressed to `O(log)` bits.  So the toolkit is closed under the
forward big-value operations (`add`, `mul`, `natPair`, `ltNat`, `clampVal`) and open
under their *inverses* (`sqrt`, `unpair`, division by a large divisor).

Paper node: `app:ifp` / `thm:ifp` (the finite-prefix efficiency closure), `def:lia`.
-/
import LogicalInduction.Construction.Witnesses.CanonicalCodes
import LogicalInduction.Construction.Witnesses.RpnConditioning

namespace LogicalInduction

namespace RpnFreeze

open PrefixPatchCompile RpnConditioning
open Nat.Partrec (Code)

-- `PolyFueled` elaboration over paired inputs unfolds `Nat.sqrt`'s well-founded definition
-- during `whnf` (reached via `Nat.pair`/`unpair`) and loops; local opacity stops that.
attribute [local irreducible] Nat.sqrt

/-- Tokens read from a stream between two positions. -/
def segOf (get : ℕ → ℕ) (p q : ℕ) : List ℕ :=
  (List.range (q - p)).map fun i => get (p + i)

@[simp] lemma segOf_length (get : ℕ → ℕ) (p q : ℕ) :
    (segOf get p q).length = q - p := by simp [segOf]

@[simp] lemma segOf_self (get : ℕ → ℕ) (p : ℕ) : segOf get p p = [] := by
  simp [segOf]

lemma segOf_getD (get : ℕ → ℕ) {p q i : ℕ} (h : i < q - p) :
    (segOf get p q).getD i 0 = get (p + i) := by
  rw [segOf, List.getD_eq_getElem _ _ (by simpa using h)]
  simp

lemma segOf_cons (get : ℕ → ℕ) {p q : ℕ} (h : p < q) :
    segOf get p q = get p :: segOf get (p + 1) q := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [segOf, List.getElem_map, List.getElem_range]
    match i with
    | 0 => simp
    | i + 1 =>
        simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range]
        congr 1
        omega

lemma segOf_split (get : ℕ → ℕ) {p r q : ℕ} (h₁ : p ≤ r) (h₂ : r ≤ q) :
    segOf get p q = segOf get p r ++ segOf get r q := by
  have hsplit : q - p = (r - p) + (q - r) := by omega
  rw [segOf, hsplit, List.range_add, List.map_append]
  congr 1
  simp only [List.map_map, segOf, Function.comp_def]
  refine List.map_congr_left fun i _ => ?_
  congr 1
  omega

/-! ### The structured paper-prime leaf denotes only reserved atoms

The second ambiguity source, independent of the `⊥` fiber that `CanonicalCodes.lean`
settles: a structured leaf `[1, 0, …]` admits non-canonical payload spellings, so a run
matcher cannot recognize it by comparing against a fixed word.  It does not have to.  The
structured parser returns *only* atoms of the reserved shape `atom (Nat.pair 7 _)`, so a
target outside that shape is never denoted by a structured block and the matcher may reject
the block on its two-token tag alone — no replay of the structured parser, and no decode.

This is what makes "a table avoiding the reserved atom shape needs no structured
recognition" a proved side condition rather than a plausible one. -/

/-- **Every structured paper-prime leaf denotes a reserved atom.**

Proof kind: `P` proved.  Provenance: (b) `parseStructuredPaperPrime`.
Paper node: `app:ifp` -/
lemma parseStructuredPaperPrime_shape : ∀ {payload : List ℕ} {φ : Sentence} {r : List ℕ},
    parseStructuredPaperPrime payload = some (φ, r) →
      ∃ pol fc : ℕ, φ = LO.Propositional.Formula.atom (Nat.pair 7 (Nat.pair pol fc)) := by
  intro payload φ r h
  cases payload with
  | nil => exfalso; revert h; simp [parseStructuredPaperPrime]
  | cons pol framed =>
      simp only [parseStructuredPaperPrime] at h
      split_ifs at h with hp
      cases hb : readStructuredLength framed with
      | none => rw [hb] at h; exfalso; revert h; simp
      | some p =>
          rw [hb] at h
          simp only [Option.bind_some] at h
          rcases hpa : parseStructuredArithmeticFormula p.1 0 (p.2.take p.1) with
            _ | ⟨formulaCode, tail⟩
          · rw [hpa] at h; exfalso; revert h; simp
          · rw [hpa] at h
            cases tail with
            | nil =>
                split_ifs at h with hle h19
                exact ⟨pol, formulaCode, (congrArg Prod.fst (Option.some.inj h)).symm⟩
            | cons a b => exfalso; revert h; simp

/-- **A target outside the reserved atom shape is never denoted by a structured leaf.** -/
lemma parseStructuredPaperPrime_ne_of_not_reserved {payload : List ℕ} {ψ : Sentence}
    {r : List ℕ}
    (hψ : ∀ pol fc : ℕ,
      ψ ≠ LO.Propositional.Formula.atom (Nat.pair 7 (Nat.pair pol fc))) :
    parseStructuredPaperPrime payload ≠ some (ψ, r) := by
  intro h
  obtain ⟨pol, fc, hshape⟩ := parseStructuredPaperPrime_shape h
  exact hψ pol fc hshape

/-- The constant-depth positional run matcher. -/
def matchRun (get : ℕ → ℕ) : Sentence → ℕ → ℕ
  | ⊥, p =>
      if get p = 1 then (if sentenceMatches ⊥ (get (p + 1)) = 1 then p + 3 else 0)
      else if get p = 0 then p + 2 else 0
  | .atom a, p =>
      if get p = 1 then
        (if sentenceMatches (.atom a) (get (p + 1)) = 1 then p + 3 else 0)
      else if get p = a + 5 then p + 2 else 0
  | φ 🡒 ψ, p =>
      if get p = 1 then
        (if sentenceMatches (φ 🡒 ψ) (get (p + 1)) = 1 then p + 3 else 0)
      else if get p = 2 then
        (if matchRun get φ (p + 1) = 0 then 0
          else matchRun get ψ (matchRun get φ (p + 1) - 1))
      else 0
  | φ ⋏ ψ, p =>
      if get p = 1 then
        (if sentenceMatches (φ ⋏ ψ) (get (p + 1)) = 1 then p + 3 else 0)
      else if get p = 3 then
        (if matchRun get φ (p + 1) = 0 then 0
          else matchRun get ψ (matchRun get φ (p + 1) - 1))
      else 0
  | φ ⋎ ψ, p =>
      if get p = 1 then
        (if sentenceMatches (φ ⋎ ψ) (get (p + 1)) = 1 then p + 3 else 0)
      else if get p = 4 then
        (if matchRun get φ (p + 1) = 0 then 0
          else matchRun get ψ (matchRun get φ (p + 1) - 1))
      else 0

/-- Escape form of the matcher, uniform in the target. -/
lemma matchRun_escape (get : ℕ → ℕ) (φ : Sentence) (p : ℕ) (h : get p = 1) :
    matchRun get φ p =
      if sentenceMatches φ (get (p + 1)) = 1 then p + 3 else 0 := by
  cases φ <;> simp only [matchRun, h] <;> rfl

/-! ### The canonical-code matcher

`matchRun`'s escape test `sentenceMatches ψ c` is the decoder-faithful one, and it reads
`Nat.unpair` at every node — the recorded obstruction to certifying the matcher at the
symbol-metered emission site.  `CanonicalCodes.lean` shows that this is caused *entirely*
by `⊥`: off the `⊥` fiber Foundation's decoder is injective.  So on a `⊥`-free target the
matcher below — whose only tests are comparisons of a stream token against a **fixed
numeral** — is the same function.  `matchRunCanon` is not an alternative semantics; it is
`matchRun` with the square root removed, and `matchRun_eq_matchRunCanon` says so. -/

/-- `matchRun` with every escape test replaced by a comparison against the target's
canonical code.  Every test is a comparison against a constant. -/
def matchRunCanon (get : ℕ → ℕ) : Sentence → ℕ → ℕ
  | ⊥, p =>
      if get p = 1 then
        (if get (p + 1) = Encodable.encode (⊥ : Sentence) then p + 3 else 0)
      else if get p = 0 then p + 2 else 0
  | .atom a, p =>
      if get p = 1 then
        (if get (p + 1) = Encodable.encode (LO.Propositional.Formula.atom a : Sentence) then p + 3 else 0)
      else if get p = a + 5 then p + 2 else 0
  | φ 🡒 ψ, p =>
      if get p = 1 then
        (if get (p + 1) = Encodable.encode (φ 🡒 ψ) then p + 3 else 0)
      else if get p = 2 then
        (if matchRunCanon get φ (p + 1) = 0 then 0
          else matchRunCanon get ψ (matchRunCanon get φ (p + 1) - 1))
      else 0
  | φ ⋏ ψ, p =>
      if get p = 1 then
        (if get (p + 1) = Encodable.encode (φ ⋏ ψ) then p + 3 else 0)
      else if get p = 3 then
        (if matchRunCanon get φ (p + 1) = 0 then 0
          else matchRunCanon get ψ (matchRunCanon get φ (p + 1) - 1))
      else 0
  | φ ⋎ ψ, p =>
      if get p = 1 then
        (if get (p + 1) = Encodable.encode (φ ⋎ ψ) then p + 3 else 0)
      else if get p = 4 then
        (if matchRunCanon get φ (p + 1) = 0 then 0
          else matchRunCanon get ψ (matchRunCanon get φ (p + 1) - 1))
      else 0

/-- Escape form of the canonical matcher, uniform in the target. -/
lemma matchRunCanon_escape (get : ℕ → ℕ) (φ : Sentence) (p : ℕ) (h : get p = 1) :
    matchRunCanon get φ p =
      if get (p + 1) = Encodable.encode φ then p + 3 else 0 := by
  cases φ <;> simp only [matchRunCanon, h] <;> rfl

/-- **The square root is not needed on a `⊥`-free target.**  The decoder-faithful
positional matcher and the constant-comparison matcher are the same function whenever the
target sentence has no `⊥` subformula — and every recursive call is on a subformula, hence
also `⊥`-free.

This narrows the disclosure in this file's header and in `matchRun_polyFueled`'s scope
warning: `Nat.unpair` is forced **iff** the frozen table contains a sentence with a `⊥`
subformula (`decode_and_noncanonical` is the converse witness).

Proof kind: `P` proved.  Provenance: (a) `sentenceMatches_of_botFree`,
`matchRun_escape`, `matchRunCanon_escape`.
Paper node: `app:ifp` -/
lemma matchRun_eq_matchRunCanon (get : ℕ → ℕ) :
    ∀ (φ : Sentence), BotFree φ → ∀ p : ℕ,
      matchRun get φ p = matchRunCanon get φ p := by
  intro φ
  induction φ using LO.Propositional.Formula.rec' with
  | hfalsum => exact fun h => absurd h id
  | hatom a =>
      intro _ p
      by_cases hp : get p = 1
      · rw [matchRun_escape get _ p hp, matchRunCanon_escape get _ p hp,
          sentenceMatches_of_botFree _ (by simp)]
        by_cases hc : get (p + 1) = Encodable.encode (LO.Propositional.Formula.atom a : Sentence) <;>
          simp [hc]
      · simp only [matchRun, matchRunCanon, if_neg hp]
  | himp φ ψ ihφ ihψ =>
      rintro ⟨hbφ, hbψ⟩ p
      by_cases hp : get p = 1
      · rw [matchRun_escape get _ p hp, matchRunCanon_escape get _ p hp,
          sentenceMatches_of_botFree _ ((botFree_imp φ ψ).mpr ⟨hbφ, hbψ⟩)]
        by_cases hc : get (p + 1) = Encodable.encode (φ 🡒 ψ) <;> simp [hc]
      · simp only [matchRun, matchRunCanon, if_neg hp, ihφ hbφ, ihψ hbψ]
  | hand φ ψ ihφ ihψ =>
      rintro ⟨hbφ, hbψ⟩ p
      by_cases hp : get p = 1
      · rw [matchRun_escape get _ p hp, matchRunCanon_escape get _ p hp,
          sentenceMatches_of_botFree _ ((botFree_and φ ψ).mpr ⟨hbφ, hbψ⟩)]
        by_cases hc : get (p + 1) = Encodable.encode (φ ⋏ ψ) <;> simp [hc]
      · simp only [matchRun, matchRunCanon, if_neg hp, ihφ hbφ, ihψ hbψ]
  | hor φ ψ ihφ ihψ =>
      rintro ⟨hbφ, hbψ⟩ p
      by_cases hp : get p = 1
      · rw [matchRun_escape get _ p hp, matchRunCanon_escape get _ p hp,
          sentenceMatches_of_botFree _ ((botFree_or φ ψ).mpr ⟨hbφ, hbψ⟩)]
        by_cases hc : get (p + 1) = Encodable.encode (φ ⋎ ψ) <;> simp [hc]
      · simp only [matchRun, matchRunCanon, if_neg hp, ihφ hbφ, ihψ hbψ]

/-- Two complete self-delimiting blocks parse in sequence under any binary shell. -/
lemma parseRpn_bin_body {b₁ b₂ : List ℕ} {φ ψ : Sentence}
    (mk : Sentence → Sentence → Sentence) {fuel : ℕ}
    (h₁ : parseRpnLegacy b₁.length b₁ = some (φ, []))
    (h₂ : parseRpnLegacy b₂.length b₂ = some (ψ, []))
    (hfuel : (b₁ ++ b₂).length ≤ fuel) :
    ((parseRpnLegacy fuel (b₁ ++ b₂)).bind fun p =>
        (parseRpnLegacy fuel p.2).bind fun q => some (mk p.1 q.1, q.2)) =
      some (mk φ ψ, []) := by
  simp only [List.length_append] at hfuel
  rw [parseRpnLegacy_block_head h₁ b₂ (by omega)]
  simp only [Option.bind_some]
  rw [parseRpnLegacy_mono b₂ (by omega) h₂]
  rfl


/-- Inversion of a complete binary-shell parse into its two complete sub-blocks. -/
lemma parseRpn_bin_inv {rest : List ℕ} {fuel : ℕ}
    {mk : Sentence → Sentence → Sentence} {φ : Sentence}
    (h : ((parseRpnLegacy fuel rest).bind fun p =>
      (parseRpnLegacy fuel p.2).bind fun q => some (mk p.1 q.1, q.2)) = some (φ, [])) :
    ∃ b₁ b₂ φ₁ φ₂, rest = b₁ ++ b₂ ∧ φ = mk φ₁ φ₂ ∧
      parseRpnLegacy b₁.length b₁ = some (φ₁, []) ∧
      parseRpnLegacy b₂.length b₂ = some (φ₂, []) := by
  rcases hp : parseRpnLegacy fuel rest with _ | ⟨φ₁, r₁⟩
  · rw [hp] at h; simp at h
  rw [hp] at h
  simp only [Option.bind_some] at h
  rcases hq : parseRpnLegacy fuel r₁ with _ | ⟨φ₂, r₂⟩
  · rw [hq] at h; simp at h
  rw [hq] at h
  simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hmk, rfl⟩ := h
  obtain ⟨b₁, hb₁, hpb₁⟩ := parseRpnLegacy_strip fuel rest hp
  obtain ⟨b₂, hb₂, hpb₂⟩ := parseRpnLegacy_strip fuel r₁ hq
  rw [List.append_nil] at hb₂
  subst hb₂
  exact ⟨b₁, r₁, φ₁, φ₂, hb₁, hmk.symm, hpb₁, hpb₂⟩

/-- **Matcher soundness**: a successful positional match certifies that the tokens it
consumed form a complete self-delimiting block parsing to the target. -/
lemma matchRun_sound : ∀ (φ : Sentence) (get : ℕ → ℕ) (p q : ℕ),
    matchRun get φ p = q + 1 →
    p ≤ q ∧ parseRpnLegacy (segOf get p q).length (segOf get p q) = some (φ, []) := by
  have hesc : ∀ (φ : Sentence) (get : ℕ → ℕ) (p q : ℕ), get p = 1 →
      matchRun get φ p = q + 1 →
      p ≤ q ∧ parseRpnLegacy (segOf get p q).length (segOf get p q) = some (φ, []) := by
    intro φ get p q he h
    rw [matchRun_escape get φ p he] at h
    by_cases hm : sentenceMatches φ (get (p + 1)) = 1
    · rw [if_pos hm] at h
      have hq : q = p + 2 := by omega
      subst hq
      refine ⟨by omega, ?_⟩
      have hseg : segOf get p (p + 2) = get p :: get (p + 1) :: [] := by
        rw [segOf_cons get (by omega), segOf_cons get (by omega)]
        simp
      rw [hseg, he]
      exact parseRpnLegacy_escape' ((sentenceMatches_eq_one_iff φ (get (p + 1))).mp hm)
        [] (by simp)
    · rw [if_neg hm] at h
      omega
  intro φ
  induction φ with
  | falsum =>
      intro get p q h
      by_cases he : get p = 1
      · exact hesc _ get p q he h
      · rw [matchRun, if_neg he] at h
        by_cases h0 : get p = 0
        · rw [if_pos h0] at h
          have hq : q = p + 1 := by omega
          subst hq
          refine ⟨by omega, ?_⟩
          have hseg : segOf get p (p + 1) = get p :: [] := by
            rw [segOf_cons get (by omega)]
            simp
          rw [hseg, h0]
          rfl
        · rw [if_neg h0] at h
          omega
  | atom a =>
      intro get p q h
      by_cases he : get p = 1
      · exact hesc _ get p q he h
      · rw [matchRun, if_neg he] at h
        by_cases h0 : get p = a + 5
        · rw [if_pos h0] at h
          have hq : q = p + 1 := by omega
          subst hq
          refine ⟨by omega, ?_⟩
          have hseg : segOf get p (p + 1) = get p :: [] := by
            rw [segOf_cons get (by omega)]
            simp
          rw [hseg, h0, List.length_cons, List.length_nil, parseRpnLegacy_cons,
            if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_neg (by omega)]
          simp
        · rw [if_neg h0] at h
          omega
  | imp φ ψ ihφ ihψ =>
      intro get p q h
      by_cases he : get p = 1
      · exact hesc _ get p q he h
      · rw [matchRun, if_neg he] at h
        by_cases h0 : get p = 2
        · rw [if_pos h0] at h
          by_cases hr : matchRun get φ (p + 1) = 0
          · rw [if_pos hr] at h; omega
          · rw [if_neg hr] at h
            obtain ⟨r, hrr⟩ : ∃ r, matchRun get φ (p + 1) = r + 1 :=
              ⟨matchRun get φ (p + 1) - 1, by omega⟩
            rw [hrr] at h
            simp only [Nat.add_sub_cancel] at h
            obtain ⟨h1le, h1parse⟩ := ihφ get (p + 1) r hrr
            obtain ⟨h2le, h2parse⟩ := ihψ get r q h
            refine ⟨by omega, ?_⟩
            rw [segOf_cons get (by omega), segOf_split get h1le h2le, h0,
              List.length_cons, parseRpnLegacy_cons, if_neg (by omega),
              if_neg (by omega), if_pos rfl]
            exact parseRpn_bin_body LO.Propositional.Formula.imp h1parse h2parse
              le_rfl
        · rw [if_neg h0] at h; omega
  | and φ ψ ihφ ihψ =>
      intro get p q h
      by_cases he : get p = 1
      · exact hesc _ get p q he h
      · rw [matchRun, if_neg he] at h
        by_cases h0 : get p = 3
        · rw [if_pos h0] at h
          by_cases hr : matchRun get φ (p + 1) = 0
          · rw [if_pos hr] at h; omega
          · rw [if_neg hr] at h
            obtain ⟨r, hrr⟩ : ∃ r, matchRun get φ (p + 1) = r + 1 :=
              ⟨matchRun get φ (p + 1) - 1, by omega⟩
            rw [hrr] at h
            simp only [Nat.add_sub_cancel] at h
            obtain ⟨h1le, h1parse⟩ := ihφ get (p + 1) r hrr
            obtain ⟨h2le, h2parse⟩ := ihψ get r q h
            refine ⟨by omega, ?_⟩
            rw [segOf_cons get (by omega), segOf_split get h1le h2le, h0,
              List.length_cons, parseRpnLegacy_cons, if_neg (by omega),
              if_neg (by omega), if_neg (by omega), if_pos rfl]
            exact parseRpn_bin_body LO.Propositional.Formula.and h1parse h2parse
              le_rfl
        · rw [if_neg h0] at h; omega
  | or φ ψ ihφ ihψ =>
      intro get p q h
      by_cases he : get p = 1
      · exact hesc _ get p q he h
      · rw [matchRun, if_neg he] at h
        by_cases h0 : get p = 4
        · rw [if_pos h0] at h
          by_cases hr : matchRun get φ (p + 1) = 0
          · rw [if_pos hr] at h; omega
          · rw [if_neg hr] at h
            obtain ⟨r, hrr⟩ : ∃ r, matchRun get φ (p + 1) = r + 1 :=
              ⟨matchRun get φ (p + 1) - 1, by omega⟩
            rw [hrr] at h
            simp only [Nat.add_sub_cancel] at h
            obtain ⟨h1le, h1parse⟩ := ihφ get (p + 1) r hrr
            obtain ⟨h2le, h2parse⟩ := ihψ get r q h
            refine ⟨by omega, ?_⟩
            rw [segOf_cons get (by omega), segOf_split get h1le h2le, h0,
              List.length_cons, parseRpnLegacy_cons, if_neg (by omega),
              if_neg (by omega), if_neg (by omega), if_neg (by omega),
              if_pos rfl]
            exact parseRpn_bin_body LO.Propositional.Formula.or h1parse h2parse
              le_rfl
        · rw [if_neg h0] at h; omega

/-- **Matcher completeness**: on a stream carrying a complete self-delimiting block for
the target at position `p`, the positional matcher succeeds exactly at the block's end. -/
lemma matchRun_complete : ∀ (N : ℕ) (b : List ℕ), b.length ≤ N →
    ∀ (φ : Sentence) (get : ℕ → ℕ) (p : ℕ),
    parseRpnLegacy b.length b = some (φ, []) →
    (∀ i, i < b.length → get (p + i) = b.getD i 0) →
    matchRun get φ p = p + b.length + 1 := by
  intro N
  induction N with
  | zero =>
      intro b hb φ get p h _
      obtain rfl : b = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [parseRpnLegacy] at h
  | succ N ih =>
      intro b hb φ get p h hget
      match b with
      | [] => simp [parseRpnLegacy] at h
      | t :: rest =>
          have hp0 : get p = t := by simpa using hget 0 (by simp)
          simp only [List.length_cons] at hb h
          rw [parseRpnLegacy_cons] at h
          by_cases h0 : t = 0
          · subst h0
            rw [if_pos rfl, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [matchRun, if_neg (by omega), if_pos (by omega)]
            simp
          rw [if_neg h0] at h
          by_cases h1 : t = 1
          · subst h1
            rw [if_pos rfl] at h
            match rest with
            | [] => simp at h
            | c :: r =>
                simp only [List.head?_cons, Option.bind_some, List.tail_cons] at h
                rcases hdec : Encodable.decode (α := Sentence) c with _ | φ'
                · rw [hdec] at h; simp at h
                · rw [hdec] at h
                  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hpc : get (p + 1) = c := by simpa using hget 1 (by simp)
                  rw [matchRun_escape get _ p (by omega), hpc,
                    if_pos ((sentenceMatches_eq_one_iff _ c).mpr hdec)]
                  simp
          rw [if_neg h1] at h
          -- The three binary shells share the sub-block decomposition.
          have hbin : ∀ (mk : Sentence → Sentence → Sentence),
              ((parseRpnLegacy rest.length rest).bind fun x =>
                (parseRpnLegacy rest.length x.2).bind fun y =>
                  some (mk x.1 y.1, y.2)) = some (φ, []) →
              ∃ b₁ b₂ φ₁ φ₂, rest = b₁ ++ b₂ ∧ φ = mk φ₁ φ₂ ∧
                matchRun get φ₁ (p + 1) = p + 1 + b₁.length + 1 ∧
                matchRun get φ₂ (p + 1 + b₁.length) =
                  p + 1 + b₁.length + b₂.length + 1 ∧
                (t :: rest).length = b₁.length + b₂.length + 1 := by
            intro mk hmk
            obtain ⟨b₁, b₂, φ₁, φ₂, rfl, rfl, hb₁, hb₂⟩ := parseRpn_bin_inv hmk
            simp only [List.length_append] at hb
            have hg1 : ∀ i, i < b₁.length → get (p + 1 + i) = b₁.getD i 0 := by
              intro i hi
              have hlt : i + 1 < (t :: (b₁ ++ b₂)).length := by
                simp only [List.length_cons, List.length_append]
                omega
              have := hget (i + 1) hlt
              rw [show p + (i + 1) = p + 1 + i by omega] at this
              rw [this, List.getD_cons_succ,
                List.getD_append _ _ _ _ (by omega)]
            have hg2 : ∀ i, i < b₂.length →
                get (p + 1 + b₁.length + i) = b₂.getD i 0 := by
              intro i hi
              have hlt : (b₁.length + i) + 1 < (t :: (b₁ ++ b₂)).length := by
                simp only [List.length_cons, List.length_append]
                omega
              have := hget ((b₁.length + i) + 1) hlt
              rw [show p + ((b₁.length + i) + 1) = p + 1 + b₁.length + i by
                omega] at this
              rw [this, List.getD_cons_succ,
                List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
            exact ⟨b₁, b₂, φ₁, φ₂, rfl, rfl,
              ih b₁ (by omega) φ₁ get (p + 1) hb₁ hg1,
              ih b₂ (by omega) φ₂ get (p + 1 + b₁.length) hb₂ hg2,
              by simp only [List.length_cons, List.length_append]⟩
          by_cases h2 : t = 2
          · subst h2
            rw [if_pos rfl] at h
            obtain ⟨b₁, b₂, φ₁, φ₂, rfl, rfl, hm1, hm2, hlen⟩ :=
              hbin LO.Propositional.Formula.imp h
            rw [matchRun, if_neg (by omega), if_pos (by omega), hm1,
              if_neg (by omega), Nat.add_sub_cancel, hm2, hlen]
            omega
          rw [if_neg h2] at h
          by_cases h3 : t = 3
          · subst h3
            rw [if_pos rfl] at h
            obtain ⟨b₁, b₂, φ₁, φ₂, rfl, rfl, hm1, hm2, hlen⟩ :=
              hbin LO.Propositional.Formula.and h
            rw [matchRun, if_neg (by omega), if_pos (by omega), hm1,
              if_neg (by omega), Nat.add_sub_cancel, hm2, hlen]
            omega
          rw [if_neg h3] at h
          by_cases h4 : t = 4
          · subst h4
            rw [if_pos rfl] at h
            obtain ⟨b₁, b₂, φ₁, φ₂, rfl, rfl, hm1, hm2, hlen⟩ :=
              hbin LO.Propositional.Formula.or h
            rw [matchRun, if_neg (by omega), if_pos (by omega), hm1,
              if_neg (by omega), Nat.add_sub_cancel, hm2, hlen]
            omega
          rw [if_neg h4, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [matchRun, if_neg (by omega), if_pos (by omega)]
          simp

/-- **The matcher characterization**: on a stream carrying the block `b` at position `p`,
the matcher stops exactly at the block's end iff the block parses to the target.
Paper node: `app:ifp` -/
lemma matchRun_iff {b : List ℕ} {φ : Sentence} {get : ℕ → ℕ} {p : ℕ}
    (hget : ∀ i, i < b.length → get (p + i) = b.getD i 0) :
    matchRun get φ p = p + b.length + 1 ↔ parseRpnLegacy b.length b = some (φ, []) := by
  constructor
  · intro h
    obtain ⟨hle, hparse⟩ := matchRun_sound φ get p (p + b.length) h
    have hseg : segOf get p (p + b.length) = b := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [segOf, List.getElem_map, List.getElem_range]
        rw [hget i h2, List.getD_eq_getElem b 0 h2]
    rwa [hseg] at hparse
  · intro h
    exact matchRun_complete b.length b le_rfl φ get p h hget

/-- Whether a token run denotes the target: the list-level decision runs the full
block parser, so structured paper-prime leaves are matched exactly like every legacy
block.  (The *positional* matcher `matchRun` above is scoped to the legacy fragment;
see the module docstring.) -/
def runMatches (target : Sentence) (b : List ℕ) : ℕ :=
  if parseRpn b.length b = some (target, []) then 1 else 0

lemma runMatches_eq_one_iff (target : Sentence) (b : List ℕ) :
    runMatches target b = 1 ↔ parseRpn b.length b = some (target, []) := by
  by_cases h : parseRpn b.length b = some (target, [])
  · simp [runMatches, h]
  · simp [runMatches, h]

/-- On a run the target test agrees with the token-model decoder test at the run's
contracted code. -/
lemma runMatches_of_parse {b : List ℕ} {φ target : Sentence}
    (hb : parseRpn b.length b = some (φ, [])) :
    runMatches target b = sentenceMatches target (Encodable.encode φ) := by
  by_cases hteq : target = φ
  · subst hteq
    rw [(runMatches_eq_one_iff target b).mpr hb,
      (sentenceMatches_eq_one_iff target (Encodable.encode target)).mpr
        (Encodable.encodek target)]
  · have hzero : runMatches target b = 0 := by
      rw [runMatches, if_neg fun hp => hteq (by
        rw [hb] at hp
        exact (congrArg Prod.fst (Option.some.inj hp)).symm)]
    rw [hzero]
    refine ((sentenceMatches_eq_zero_iff target (Encodable.encode φ)).mpr ?_).symm
    rw [Encodable.encodek]
    simpa using fun h => hteq h.symm

/-- Run-level form of `PrefixPatchCompile.encodedQuoteFromEntries`. -/
def runQuoteFromEntries : List (Sentence × ℚ) → List ℕ → ℕ
  | [], _ => Encodable.encode (0 : ℚ)
  | (target, q) :: entries, b =>
      if runMatches target b = 0 then runQuoteFromEntries entries b
      else Encodable.encode q

lemma runQuoteFromEntries_exact (entries : List (Sentence × ℚ))
    {b : List ℕ} {φ : Sentence} (hb : parseRpn b.length b = some (φ, [])) :
    runQuoteFromEntries entries b =
      encodedQuoteFromEntries entries (Encodable.encode φ) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨target, q⟩
      rw [runQuoteFromEntries, encodedQuoteFromEntries, runMatches_of_parse hb]
      split
      · exact ih
      · rfl

/-- Run-level form of `PrefixPatchCompile.encodedPrefixQuoteFromStates`. -/
def runPrefixQuoteFromStates : List RationalBeliefState → ℕ → List ℕ → ℕ
  | [], _, _ => Encodable.encode (0 : ℚ)
  | state :: _, 0, b => runQuoteFromEntries state.entries b
  | _ :: states, day + 1, b => runPrefixQuoteFromStates states day b

/-- The run-level prefix quote table agrees with the token-model one at the run's
contracted code.
Paper node: `def:lia` -/
lemma runPrefixQuoteFromStates_exact (states : List RationalBeliefState) (day : ℕ)
    {b : List ℕ} {φ : Sentence} (hb : parseRpn b.length b = some (φ, [])) :
    runPrefixQuoteFromStates states day b =
      encodedPrefixQuoteFromStates states day (Encodable.encode φ) := by
  induction states generalizing day with
  | nil => rfl
  | cons state states ih =>
      cases day with
      | zero =>
          exact runQuoteFromEntries_exact state.entries hb
      | succ day => exact ih day

/-! ### The symbol-level freeze transducer

The transducer is selector-indexed, matching `EF.freezeTokenRunOn`.  At the flat grammar
the selector and the quote table are read **from the buffered sentence run** — `selRun`,
`quoteRun` — because the run is what the transducer has; `hsel`/`hq` bridge them to the
code-level pair the token model uses, exactly as `runQuoteFromEntries_exact` supplies.
The day-cutoff forms at the end are instances. -/

/-- The token-model freeze, as a whole-stream rewrite. -/
def freezeTokensOn (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (L : List ℕ) :
    List ℕ :=
  (EF.freezeTokenRunOn selCode quoteCode (0, 0) L).2

/-- The body the token-model freeze splices at a completed price leaf. -/
def freezeBodyOn (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (fc d : ℕ) : List ℕ :=
  if selCode d fc then [1, quoteCode d fc, 8] else []

lemma freezeTokensOn_nil (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) :
    freezeTokensOn selCode quoteCode [] = [] := rfl

lemma freezeTokensOn_single (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (t : ℕ)
    (L : List ℕ) (h0 : t ≠ 0) (h1 : t ≠ 1) (h6 : t ≠ 6) (h7 : t ≠ 7) :
    freezeTokensOn selCode quoteCode (t :: L)
      = t :: freezeTokensOn selCode quoteCode L := by
  simp [freezeTokensOn, EF.freezeTokenRunOn, EF.freezeTokenEmitOn, EF.freezeTokenNext,
    h0, h1, h6, h7]

lemma freezeTokensOn_one (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (t : ℕ) :
    freezeTokensOn selCode quoteCode [t] = [t] := by
  simp [freezeTokensOn, EF.freezeTokenRunOn, EF.freezeTokenEmitOn]

lemma freezeTokensOn_payload (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (t c : ℕ)
    (ht : t = 1 ∨ t = 7) (L : List ℕ) :
    freezeTokensOn selCode quoteCode (t :: c :: L)
      = t :: c :: freezeTokensOn selCode quoteCode L := by
  rcases ht with rfl | rfl <;>
    simp [freezeTokensOn, EF.freezeTokenRunOn, EF.freezeTokenEmitOn, EF.freezeTokenNext]

lemma freezeTokensOn_price (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (fc d : ℕ)
    (L : List ℕ) :
    freezeTokensOn selCode quoteCode (0 :: fc :: d :: L) =
      0 :: fc :: d :: (freezeBodyOn selCode quoteCode fc d ++
        freezeTokensOn selCode quoteCode L) := by
  simp only [freezeTokensOn, EF.freezeTokenRunOn, EF.freezeTokenEmitOn,
    EF.freezeTokenNext, freezeBodyOn]
  by_cases hd : selCode d fc = true <;> simp [hd]

lemma freezeTokensOn_pricePair (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (fc : ℕ) : freezeTokensOn selCode quoteCode [0, fc] = [0, fc] := by
  simp [freezeTokensOn, EF.freezeTokenRunOn, EF.freezeTokenEmitOn, EF.freezeTokenNext]

lemma freezeTokensOn_trade (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) (fc : ℕ)
    (L : List ℕ) :
    freezeTokensOn selCode quoteCode (6 :: fc :: L)
      = 6 :: fc :: freezeTokensOn selCode quoteCode L := by
  simp [freezeTokensOn, EF.freezeTokenRunOn, EF.freezeTokenEmitOn, EF.freezeTokenNext]

/-- **The symbol-level freeze emitter**: at a selected price-day slot, retain the day and
splice the constant quote of the buffered sentence run under the administrative binding. -/
def freezeEmitOn (selRun : List ℕ → ℕ → Bool) (quoteRun : List ℕ → ℕ → ℕ) :
    List ℕ → ℕ → List ℕ :=
  fun buf D => if selRun buf D then [D, 1, quoteRun buf D, 8] else [D]

/-- **The rewritten price chunk contracts to the token-model freeze.** -/
lemma unRpn_freezeOn_rewrite_chunk (selRun : List ℕ → ℕ → Bool)
    (quoteRun : List ℕ → ℕ → ℕ) (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, selRun b D = selCode D (Encodable.encode φ))
    (hq : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, quoteRun b D = quoteCode D (Encodable.encode φ))
    {b : List ℕ} {φ : Sentence} (hb : parseRpn b.length b = some (φ, []))
    (D : ℕ) (rest : List ℕ) :
    unRpn (0 :: b ++ freezeEmitOn selRun quoteRun b D ++ rest) =
      0 :: Encodable.encode φ :: D ::
        (freezeBodyOn selCode quoteCode (Encodable.encode φ) D ++ unRpn rest) := by
  rw [freezeEmitOn, freezeBodyOn, hsel b φ hb D]
  by_cases hd : selCode D (Encodable.encode φ) = true
  · rw [if_pos hd, if_pos hd]
    have hshape : 0 :: b ++ [D, 1, quoteRun b D, 8] ++ rest =
        0 :: (b ++ D :: 1 :: quoteRun b D :: 8 :: rest) := by simp
    rw [hshape, unRpn_price_chunk_block hb,
      unRpn_payload_chunk 1 _ (Or.inl rfl), unRpn_single_chunk 8 (by norm_num),
      hq b φ hb D]
    simp
  · rw [if_neg hd, if_neg hd]
    have hshape : 0 :: b ++ [D] ++ rest = 0 :: (b ++ D :: rest) := by simp
    rw [hshape, unRpn_price_chunk_block hb]
    simp

/-- **Whole-stream contraction exactness for the selector-indexed freeze pass**: on every
input stream — well-formed or garbage — the contraction of the symbol-level freeze
transducer's output is the token-model freeze of the contraction.

This is the bridge the machine-class certificate needs: the transducer runs on the *flat*
stream a machine actually holds, while `EF.freezeTokenRunOn` — and hence
`FreezeStreamRewriter` — is stated on the contracted one.
Paper node: `app:ifp` -/
theorem unRpn_rpnFreezeRunOn (selRun : List ℕ → ℕ → Bool) (quoteRun : List ℕ → ℕ → ℕ)
    (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, selRun b D = selCode D (Encodable.encode φ))
    (hq : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, quoteRun b D = quoteCode D (Encodable.encode φ)) :
    ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    unRpn ((rpnConditionRun (freezeEmitOn selRun quoteRun) (rcPack 0 0 0, []) ts).2) =
      freezeTokensOn selCode quoteCode (unRpn ts) :=
  unRpn_rpnConditionRun_of (freezeEmitOn selRun quoteRun)
    (freezeTokensOn selCode quoteCode) (freezeBodyOn selCode quoteCode)
    (freezeTokensOn_nil selCode quoteCode)
    (fun t L h0 h1 h6 h7 => freezeTokensOn_single selCode quoteCode t L h0 h1 h6 h7)
    (freezeTokensOn_one selCode quoteCode)
    (fun t c L ht => freezeTokensOn_payload selCode quoteCode t c ht L)
    (freezeTokensOn_price selCode quoteCode)
    (freezeTokensOn_pricePair selCode quoteCode)
    (freezeTokensOn_trade selCode quoteCode)
    (fun _ _ hb D rest => unRpn_freezeOn_rewrite_chunk selRun quoteRun selCode quoteCode
      hsel hq hb D rest)

/-! ### The day-cutoff instances -/

/-- The token-model prefix freeze, as a whole-stream rewrite. -/
def freezeTokens (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) (L : List ℕ) : List ℕ :=
  freezeTokensOn (fun d _ => decide (d < cutoff)) quoteCode L

/-- The body the token-model freeze splices at a completed price leaf. -/
def freezeBody (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) (fc d : ℕ) : List ℕ :=
  if d < cutoff then [1, quoteCode d fc, 8] else []

lemma freezeBody_eq (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) (fc d : ℕ) :
    freezeBody quoteCode cutoff fc d
      = freezeBodyOn (fun d _ => decide (d < cutoff)) quoteCode fc d := by
  simp only [freezeBody, freezeBodyOn, decide_eq_true_eq]

lemma freezeTokens_nil (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) :
    freezeTokens quoteCode cutoff [] = [] := rfl

lemma freezeTokens_single (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) (t : ℕ)
    (L : List ℕ) (h0 : t ≠ 0) (h1 : t ≠ 1) (h6 : t ≠ 6) (h7 : t ≠ 7) :
    freezeTokens quoteCode cutoff (t :: L) = t :: freezeTokens quoteCode cutoff L :=
  freezeTokensOn_single _ quoteCode t L h0 h1 h6 h7

lemma freezeTokens_one (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) (t : ℕ) :
    freezeTokens quoteCode cutoff [t] = [t] :=
  freezeTokensOn_one _ quoteCode t

lemma freezeTokens_payload (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) (t c : ℕ)
    (ht : t = 1 ∨ t = 7) (L : List ℕ) :
    freezeTokens quoteCode cutoff (t :: c :: L) =
      t :: c :: freezeTokens quoteCode cutoff L :=
  freezeTokensOn_payload _ quoteCode t c ht L

lemma freezeTokens_price (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) (fc d : ℕ)
    (L : List ℕ) :
    freezeTokens quoteCode cutoff (0 :: fc :: d :: L) =
      0 :: fc :: d :: (freezeBody quoteCode cutoff fc d ++
        freezeTokens quoteCode cutoff L) := by
  rw [freezeBody_eq]
  exact freezeTokensOn_price _ quoteCode fc d L

lemma freezeTokens_pricePair (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) (fc : ℕ) :
    freezeTokens quoteCode cutoff [0, fc] = [0, fc] :=
  freezeTokensOn_pricePair _ quoteCode fc

lemma freezeTokens_trade (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ) (fc : ℕ)
    (L : List ℕ) :
    freezeTokens quoteCode cutoff (6 :: fc :: L) =
      6 :: fc :: freezeTokens quoteCode cutoff L :=
  freezeTokensOn_trade _ quoteCode fc L

/-- **The symbol-level freeze emitter**: at a price-day slot before the cutoff, retain
the day and splice the constant quote of the buffered sentence run under the
administrative binding. -/
def freezeEmit (quoteRun : List ℕ → ℕ → ℕ) (cutoff : ℕ) : List ℕ → ℕ → List ℕ :=
  freezeEmitOn (fun _ D => decide (D < cutoff)) quoteRun

/-- **The rewritten price chunk contracts to the token-model freeze.** -/
lemma unRpn_freeze_rewrite_chunk (quoteRun : List ℕ → ℕ → ℕ)
    (quoteCode : ℕ → ℕ → ℕ) (cutoff : ℕ)
    (hq : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, quoteRun b D = quoteCode D (Encodable.encode φ))
    {b : List ℕ} {φ : Sentence} (hb : parseRpn b.length b = some (φ, []))
    (D : ℕ) (rest : List ℕ) :
    unRpn (0 :: b ++ freezeEmit quoteRun cutoff b D ++ rest) =
      0 :: Encodable.encode φ :: D ::
        (freezeBody quoteCode cutoff (Encodable.encode φ) D ++ unRpn rest) := by
  rw [freezeBody_eq, freezeEmit]
  exact unRpn_freezeOn_rewrite_chunk _ quoteRun _ quoteCode (fun _ _ _ _ => rfl) hq hb
    D rest

/-- **Whole-stream contraction exactness for the freeze pass**: on every input stream —
well-formed or garbage — the contraction of the symbol-level freeze transducer's output
is the token-model prefix freeze of the contraction.
Paper node: `app:ifp` -/
theorem unRpn_rpnFreezeRun (quoteRun : List ℕ → ℕ → ℕ) (quoteCode : ℕ → ℕ → ℕ)
    (cutoff : ℕ)
    (hq : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, quoteRun b D = quoteCode D (Encodable.encode φ)) :
    ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    unRpn ((rpnConditionRun (freezeEmit quoteRun cutoff) (rcPack 0 0 0, []) ts).2) =
      freezeTokens quoteCode cutoff (unRpn ts) :=
  unRpn_rpnFreezeRunOn _ quoteRun _ quoteCode (fun _ _ _ _ => rfl) hq

/-! ### The machine-class obligation, moved to the flat stream

`FreezeStreamRewriter` (`Properties/FinitePerturbations.lean`) is stated on the
*contracted* stream, because that is what `strategyOfTokens` parses.  A machine never holds
the contracted stream — computing `unRpn` would mean re-encoding each parsed sentence — so
the pass it can actually run is the flat-grammar one, and `unRpn_rpnFreezeRunOn` is what
carries it across.  The lemma below is that carry, once. -/

/-- **`FreezeStreamRewriter` reduces to a flat-stream pass.**  A polynomial-time rewrite of
the machine's own output word that computes the *symbol-level* freeze transducer discharges
the contracted-stream obligation, because contraction commutes with the pass.

What remains after this is a single `Complexity.FP` statement about
`rpnConditionRun (freezeEmitOn selRun quoteRun)` — the flat automaton with a freeze
emitter — and its emitter is the run-level table lookup.

Kind `C`; hypotheses `(a)` except `hflat`, which is the residual obligation.
Paper node: `app:ifp` -/
lemma freezeStreamRewriter_of_flatPass (selRun : List ℕ → ℕ → Bool)
    (quoteRun : List ℕ → ℕ → ℕ) (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, selRun b D = selCode D (Encodable.encode φ))
    (hq : ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
      ∀ D, quoteRun b D = quoteCode D (Encodable.encode φ))
    (hflat : ∀ F : List Bool → List Bool, F ∈ Complexity.FP →
      ∃ G : List Bool → List Bool, G ∈ Complexity.FP ∧ ∀ x : List Bool,
        undigitize (bitsToDigits (G x))
          = (rpnConditionRun (freezeEmitOn selRun quoteRun) (rcPack 0 0 0, [])
              (undigitize (bitsToDigits (F x)))).2) :
    FreezeStreamRewriter selCode quoteCode := by
  intro F hF
  obtain ⟨G, hG, hGspec⟩ := hflat F hF
  refine ⟨G, hG, fun x => ?_⟩
  rw [hGspec x]
  exact unRpn_rpnFreezeRunOn selRun quoteRun selCode quoteCode hsel hq _ _ le_rfl

/-! ### The poly-fueled side

The matcher is a *constant-depth* composition, so its fuel certificate is a plain
induction over the target sentence — no scan and no automaton state. -/

private lemma polyFueled_addConst {cf : Code} {f : ℕ → ℕ} (hf : PolyFueled cf f)
    (K : ℕ) : ∃ c, PolyFueled c (fun z => f z + K) := by
  obtain ⟨cad, had⟩ := addc_polyFueled
  exact ⟨_, (had.comp (hf.pair (PolyFueled.const K))).of_eq
    (fun z => by simp only [Nat.unpair_pair])⟩

private lemma polyFueled_subConst {cf : Code} {f : ℕ → ℕ} (hf : PolyFueled cf f)
    (K : ℕ) : ∃ c, PolyFueled c (fun z => f z - K) :=
  ⟨_, (subc_polyFueled.comp (hf.pair (PolyFueled.const K))).of_eq
    (fun z => by simp only [Nat.unpair_pair])⟩

private lemma polyFueled_ifEqConst {cf ca cb : Code} {f A B : ℕ → ℕ}
    (hf : PolyFueled cf f) (K : ℕ) (hA : PolyFueled ca A) (hB : PolyFueled cb B) :
    ∃ c, PolyFueled c (fun z => if f z = K then A z else B z) := by
  obtain ⟨ceq, heq⟩ := polyFueled_eqConst hf K
  obtain ⟨c, hc⟩ := polyFueled_ifZero heq hB hA
  exact ⟨c, hc.of_eq fun z => by by_cases h : f z = K <;> simp [h]⟩

private lemma polyFueled_ifEqFn {cf cg ca cb : Code} {f g A B : ℕ → ℕ}
    (hf : PolyFueled cf f) (hg : PolyFueled cg g)
    (hA : PolyFueled ca A) (hB : PolyFueled cb B) :
    ∃ c, PolyFueled c (fun z => if f z = g z then A z else B z) := by
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hs1 : PolyFueled _ (fun z => f z - g z) :=
    (subc_polyFueled.comp (hf.pair hg)).of_eq (fun z => by simp only [Nat.unpair_pair])
  have hs2 : PolyFueled _ (fun z => g z - f z) :=
    (subc_polyFueled.comp (hg.pair hf)).of_eq (fun z => by simp only [Nat.unpair_pair])
  have htest : PolyFueled _ (fun z => (f z - g z) + (g z - f z)) :=
    (had.comp (hs1.pair hs2)).of_eq (fun z => by simp only [Nat.unpair_pair])
  obtain ⟨c, hc⟩ := polyFueled_ifZero htest hA hB
  exact ⟨c, hc.of_eq fun z => by
    by_cases h : f z = g z
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]⟩

/-- The positional run matcher against a fixed target is polynomially fueled over any
poly-fueled token function, stream index and start position.

**Scope warning — this is the token-metered hypothesis, and it is *not* available at the
symbol-metered emission site.**  A digit stream supplies only `BigDigits` access to its
tokens (values may be exponential), never `PolyFueled`.  Every test inside `matchRun`
factors through a small clamp — grammar tags `0/1/2/3/4`, atom tokens `a + 5` — except the
escape leaf, which must decide `Encodable.decode c = some ψ` for an exponentially large
`c`; Foundation's `ofNat` ignores the payload at tag `0`, so `decode` is not injective and
that decision reduces to `Nat.unpair` (integer square root).  The `BigDigits` API does not
provide it, and cannot without either a new axiom or `TC⁰` division machinery: closure
requires a poly-bounded digit carry, and square root's carry is the partial remainder,
which is `Θ(len)` digits wide — the digit model is closed under the forward big-value
operations and open under their inverses.  This is therefore a disclosed
boundary: `EfficientPrefixPatch.preserves_ec` has no LIA inhabitant at the collapsed
class, and this lemma is the token-model half of the certificate only.

**Scope of the boundary.**  `matchRun_eq_matchRunCanon` above shows the escape decision
needs `unpair` only when the *target* has a `⊥` subformula; on a `⊥`-free target every
test in the matcher is a comparison against a fixed numeral. -/
lemma matchRun_polyFueled {ct cn : Code} {tf N : ℕ → ℕ}
    (htf : PolyFueled ct tf) (hN : PolyFueled cn N) (target : Sentence) :
    ∀ {cp : Code} {P : ℕ → ℕ}, PolyFueled cp P →
      ∃ c, PolyFueled c
        (fun z => matchRun (fun i => tf (Nat.pair (N z) i)) target (P z)) := by
  induction target with
  | falsum =>
      intro cp P hP
      have hg0 := htf.comp (hN.pair hP)
      have hg1 := htf.comp (hN.pair hP.succ_comp)
      obtain ⟨cm, hm⟩ := sentenceMatches_polyFueled (⊥ : Sentence)
      obtain ⟨c3, h3⟩ := polyFueled_addConst hP 3
      obtain ⟨c2, h2⟩ := polyFueled_addConst hP 2
      obtain ⟨ca, ha⟩ :=
        polyFueled_ifEqConst (hm.comp hg1) 1 h3 (PolyFueled.const 0)
      obtain ⟨cb, hb⟩ := polyFueled_ifEqConst hg0 0 h2 (PolyFueled.const 0)
      obtain ⟨c, hc⟩ := polyFueled_ifEqConst hg0 1 ha hb
      exact ⟨c, hc.of_eq fun z => by rw [matchRun]⟩
  | atom a =>
      intro cp P hP
      have hg0 := htf.comp (hN.pair hP)
      have hg1 := htf.comp (hN.pair hP.succ_comp)
      obtain ⟨cm, hm⟩ := sentenceMatches_polyFueled ((.atom a : Sentence))
      obtain ⟨c3, h3⟩ := polyFueled_addConst hP 3
      obtain ⟨c2, h2⟩ := polyFueled_addConst hP 2
      obtain ⟨ca, ha⟩ :=
        polyFueled_ifEqConst (hm.comp hg1) 1 h3 (PolyFueled.const 0)
      obtain ⟨cb, hb⟩ := polyFueled_ifEqConst hg0 (a + 5) h2 (PolyFueled.const 0)
      obtain ⟨c, hc⟩ := polyFueled_ifEqConst hg0 1 ha hb
      exact ⟨c, hc.of_eq fun z => by rw [matchRun]⟩
  | imp φ ψ ihφ ihψ =>
      intro cp P hP
      have hg0 := htf.comp (hN.pair hP)
      have hg1 := htf.comp (hN.pair hP.succ_comp)
      obtain ⟨cm, hm⟩ := sentenceMatches_polyFueled ((φ 🡒 ψ : Sentence))
      obtain ⟨c3, h3⟩ := polyFueled_addConst hP 3
      obtain ⟨ca, ha⟩ :=
        polyFueled_ifEqConst (hm.comp hg1) 1 h3 (PolyFueled.const 0)
      obtain ⟨cφ, hφ⟩ := ihφ hP.succ_comp
      obtain ⟨cd, hd⟩ := polyFueled_subConst hφ 1
      obtain ⟨cψ, hψ⟩ := ihψ hd
      obtain ⟨cbody, hbody⟩ :=
        polyFueled_ifEqConst hφ 0 (PolyFueled.const 0) hψ
      obtain ⟨cb, hb⟩ := polyFueled_ifEqConst hg0 2 hbody (PolyFueled.const 0)
      obtain ⟨c, hc⟩ := polyFueled_ifEqConst hg0 1 ha hb
      exact ⟨c, hc.of_eq fun z => by rw [matchRun]⟩
  | and φ ψ ihφ ihψ =>
      intro cp P hP
      have hg0 := htf.comp (hN.pair hP)
      have hg1 := htf.comp (hN.pair hP.succ_comp)
      obtain ⟨cm, hm⟩ := sentenceMatches_polyFueled ((φ ⋏ ψ : Sentence))
      obtain ⟨c3, h3⟩ := polyFueled_addConst hP 3
      obtain ⟨ca, ha⟩ :=
        polyFueled_ifEqConst (hm.comp hg1) 1 h3 (PolyFueled.const 0)
      obtain ⟨cφ, hφ⟩ := ihφ hP.succ_comp
      obtain ⟨cd, hd⟩ := polyFueled_subConst hφ 1
      obtain ⟨cψ, hψ⟩ := ihψ hd
      obtain ⟨cbody, hbody⟩ :=
        polyFueled_ifEqConst hφ 0 (PolyFueled.const 0) hψ
      obtain ⟨cb, hb⟩ := polyFueled_ifEqConst hg0 3 hbody (PolyFueled.const 0)
      obtain ⟨c, hc⟩ := polyFueled_ifEqConst hg0 1 ha hb
      exact ⟨c, hc.of_eq fun z => by rw [matchRun]⟩
  | or φ ψ ihφ ihψ =>
      intro cp P hP
      have hg0 := htf.comp (hN.pair hP)
      have hg1 := htf.comp (hN.pair hP.succ_comp)
      obtain ⟨cm, hm⟩ := sentenceMatches_polyFueled ((φ ⋎ ψ : Sentence))
      obtain ⟨c3, h3⟩ := polyFueled_addConst hP 3
      obtain ⟨ca, ha⟩ :=
        polyFueled_ifEqConst (hm.comp hg1) 1 h3 (PolyFueled.const 0)
      obtain ⟨cφ, hφ⟩ := ihφ hP.succ_comp
      obtain ⟨cd, hd⟩ := polyFueled_subConst hφ 1
      obtain ⟨cψ, hψ⟩ := ihψ hd
      obtain ⟨cbody, hbody⟩ :=
        polyFueled_ifEqConst hφ 0 (PolyFueled.const 0) hψ
      obtain ⟨cb, hb⟩ := polyFueled_ifEqConst hg0 4 hbody (PolyFueled.const 0)
      obtain ⟨c, hc⟩ := polyFueled_ifEqConst hg0 1 ha hb
      exact ⟨c, hc.of_eq fun z => by rw [matchRun]⟩

/-! ### Positional form of the run-level tables -/

lemma runMatches_cases (target : Sentence) (b : List ℕ) :
    runMatches target b = 0 ∨ runMatches target b = 1 := by
  rw [runMatches]; split <;> simp

/-- Legacy-fragment list-level match: the list form of the positional matcher.  The
poly-fueled positional chain below certifies this fragment only — a structured
paper-prime leaf joins the escape decode on the far side of the `dd:fuel` boundary
(see the module docstring), so the full-grammar `runMatches` above has no positional
fuel certificate. -/
def runMatchesLegacy (target : Sentence) (b : List ℕ) : ℕ :=
  if matchRun (fun i => b.getD i 0) target 0 = b.length + 1 then 1 else 0

lemma runMatchesLegacy_eq_one_iff (target : Sentence) (b : List ℕ) :
    runMatchesLegacy target b = 1 ↔ parseRpnLegacy b.length b = some (target, []) := by
  have hget : ∀ i, i < b.length → (fun i => b.getD i 0) (0 + i) = b.getD i 0 :=
    fun i _ => by simp
  have hiff := matchRun_iff (b := b) (φ := target)
    (get := fun i => b.getD i 0) (p := 0) hget
  rw [Nat.zero_add] at hiff
  rw [runMatchesLegacy]
  split
  · next h => simp [hiff.mp h]
  · next h =>
      simp only [Nat.zero_ne_one, false_iff]
      exact fun hparse => h (hiff.mpr hparse)

lemma runMatchesLegacy_cases (target : Sentence) (b : List ℕ) :
    runMatchesLegacy target b = 0 ∨ runMatchesLegacy target b = 1 := by
  rw [runMatchesLegacy]; split <;> simp

lemma runMatchesLegacy_segOf (get : ℕ → ℕ) {p q : ℕ} (h : p ≤ q) (target : Sentence) :
    runMatchesLegacy target (segOf get p q) =
      if matchRun get target p = q + 1 then 1 else 0 := by
  have hget : ∀ i, i < (segOf get p q).length →
      get (p + i) = (segOf get p q).getD i 0 := by
    intro i hi
    rw [segOf_getD get (by simpa using hi)]
  have hiff := matchRun_iff (b := segOf get p q) (φ := target) (get := get) (p := p)
    hget
  rw [show p + (segOf get p q).length + 1 = q + 1 by
    simp only [segOf_length]; omega] at hiff
  by_cases hm : matchRun get target p = q + 1
  · rw [if_pos hm, (runMatchesLegacy_eq_one_iff target _).mpr (hiff.mp hm)]
  · rw [if_neg hm]
    rcases runMatchesLegacy_cases target (segOf get p q) with hz | ho
    · exact hz
    · exact absurd (hiff.mpr ((runMatchesLegacy_eq_one_iff target _).mp ho)) hm

/-- Legacy-fragment list-level quote lookup (the list form of the positional table). -/
def runQuoteFromEntriesLegacy : List (Sentence × ℚ) → List ℕ → ℕ
  | [], _ => Encodable.encode (0 : ℚ)
  | (target, q) :: entries, b =>
      if runMatchesLegacy target b = 0 then runQuoteFromEntriesLegacy entries b
      else Encodable.encode q

/-- Positional form of `runQuoteFromEntriesLegacy`. -/
def runQuoteFromEntriesAt : List (Sentence × ℚ) → (ℕ → ℕ) → ℕ → ℕ → ℕ
  | [], _, _, _ => Encodable.encode (0 : ℚ)
  | (target, q) :: entries, get, p, e =>
      if matchRun get target p = e + 1 then Encodable.encode q
      else runQuoteFromEntriesAt entries get p e

lemma runQuoteFromEntriesLegacy_segOf (entries : List (Sentence × ℚ)) (get : ℕ → ℕ)
    {p q : ℕ} (h : p ≤ q) :
    runQuoteFromEntriesLegacy entries (segOf get p q) =
      runQuoteFromEntriesAt entries get p q := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨target, r⟩
      rw [runQuoteFromEntriesLegacy, runQuoteFromEntriesAt,
        runMatchesLegacy_segOf get h target]
      by_cases hm : matchRun get target p = q + 1
      · simp [hm]
      · simp [hm, ih]

/-- Legacy-fragment list-level prefix quote table. -/
def runPrefixQuoteFromStatesLegacy : List RationalBeliefState → ℕ → List ℕ → ℕ
  | [], _, _ => Encodable.encode (0 : ℚ)
  | state :: _, 0, b => runQuoteFromEntriesLegacy state.entries b
  | _ :: states, day + 1, b => runPrefixQuoteFromStatesLegacy states day b

/-- Positional form of `runPrefixQuoteFromStatesLegacy`. -/
def runPrefixQuoteFromStatesAt :
    List RationalBeliefState → ℕ → (ℕ → ℕ) → ℕ → ℕ → ℕ
  | [], _, _, _, _ => Encodable.encode (0 : ℚ)
  | state :: _, 0, get, p, e => runQuoteFromEntriesAt state.entries get p e
  | _ :: states, day + 1, get, p, e => runPrefixQuoteFromStatesAt states day get p e

lemma runPrefixQuoteFromStatesLegacy_segOf (states : List RationalBeliefState)
    (day : ℕ) (get : ℕ → ℕ) {p q : ℕ} (h : p ≤ q) :
    runPrefixQuoteFromStatesLegacy states day (segOf get p q) =
      runPrefixQuoteFromStatesAt states day get p q := by
  induction states generalizing day with
  | nil => rfl
  | cons state states ih =>
      cases day with
      | zero => exact runQuoteFromEntriesLegacy_segOf state.entries get h
      | succ day => exact ih day

lemma runQuoteFromEntriesAt_polyFueled (entries : List (Sentence × ℚ))
    {ct cn cp ce : Code} {tf N P E : ℕ → ℕ}
    (htf : PolyFueled ct tf) (hN : PolyFueled cn N) (hP : PolyFueled cp P)
    (hE : PolyFueled ce E) :
    ∃ c, PolyFueled c (fun z =>
      runQuoteFromEntriesAt entries (fun i => tf (Nat.pair (N z) i)) (P z) (E z)) := by
  induction entries with
  | nil => exact ⟨_, PolyFueled.const (Encodable.encode (0 : ℚ))⟩
  | cons entry entries ih =>
      rcases entry with ⟨target, r⟩
      obtain ⟨cm, hm⟩ := matchRun_polyFueled htf hN target hP
      obtain ⟨crest, hrest⟩ := ih
      obtain ⟨c, hc⟩ := polyFueled_ifEqFn hm hE.succ_comp
        (PolyFueled.const (Encodable.encode r)) hrest
      exact ⟨c, hc.of_eq fun z => by rw [runQuoteFromEntriesAt]⟩

lemma runPrefixQuoteFromStatesAt_polyFueled (states : List RationalBeliefState)
    {ct cn cp ce cd : Code} {tf N P E D : ℕ → ℕ}
    (htf : PolyFueled ct tf) (hN : PolyFueled cn N) (hP : PolyFueled cp P)
    (hE : PolyFueled ce E) (hD : PolyFueled cd D) :
    ∃ c, PolyFueled c (fun z =>
      runPrefixQuoteFromStatesAt states (D z) (fun i => tf (Nat.pair (N z) i))
        (P z) (E z)) := by
  induction states generalizing cd D with
  | nil => exact ⟨_, PolyFueled.const (Encodable.encode (0 : ℚ))⟩
  | cons state states ih =>
      obtain ⟨centry, hentry⟩ :=
        runQuoteFromEntriesAt_polyFueled state.entries htf hN hP hE
      obtain ⟨cpred, hpred⟩ := polyFueled_subConst hD 1
      obtain ⟨crest, hrest⟩ := ih hpred
      obtain ⟨c, hc⟩ := polyFueled_ifZero hD hentry hrest
      refine ⟨c, hc.of_eq fun z => ?_⟩
      cases hd : D z with
      | zero => simp only [if_pos, runPrefixQuoteFromStatesAt]
      | succ day =>
          simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel,
            runPrefixQuoteFromStatesAt]

end RpnFreeze
end LogicalInduction
