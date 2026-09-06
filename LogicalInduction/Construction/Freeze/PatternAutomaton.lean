import LogicalInduction.Construction.Freeze.RunAutomaton
import LogicalInduction.Construction.Freeze.Compiler

/-!
# Recognizing a target's spellings with an automaton

`app:ifp` — `RpnFreeze.parseRpnLegacy_iff_patMatch`'s characterization turned into a
`Complexity.FP` decision.  That lemma says a run denotes a target exactly when it matches one
of finitely many **patterns**: literal grammar tokens, with a `hole χ` wherever an escape leaf
may stand, the hole's obligation being `decode c = some χ`.  It carries no `BotFree`, because
`⊥`'s infinite decode fibre lives inside the hole predicate rather than in the pattern list.

The shape of the turning is the point.  A pattern is a literal list, so matching it is a
prefix walk with a counter bounded by the pattern's own length — a `RunAuto.BlockAutomaton`
whose guards are `RunAuto.litGuard`s at literal positions and, at a hole, one guard per
subformula.  The whole of what is *not* available unconditionally is collected in a single
interface, `HoleGuards`: a polynomial-time test of "does this code decode to `χ`".

That isolation is the deliverable.  Everything else here — the automaton, the fold, the
disjunction over the pattern list, and the `FP` membership of all of it — is unconditional
and axiom-clean.

## Objects

`HoleGuards`, `tokGuard`, `patRows`, `patAuto`, `patNest`.

`HoleGuards` is inhabited: `FiberTest.holeGuards` (`FiberTest.lean`, on the axiom-clean
`fiberW_mem_FP`) is the instance, and it is on the freeze recognizer's critical path.  What it
costs is `Nat.unpair` on a token's digit word, hence integer square root in `FP`
(`DigitFP.sqrtRemW_mem_FP`, `DigitFP.unpairW_spec`); on a `⊥`-free `χ` the test degenerates to
a fixed-numeral comparison, because Foundation's decoder is injective off the `⊥` fibre
(`decode_eq_some_iff_of_botFree`).

## Main results

The automaton's correctness chain runs `patAuto_step_of_lt` / `_of_ge` and
`foldl_patAuto_fail` (the failure state absorbs) to `foldl_patAuto` (the fold reaches the end
state exactly on a match, from any reachable position) and `patAuto_accepts`.  The disjunction
`patNest` takes branch `X` as soon as one pattern matches (`patNest_pos`, `patNest_neg`,
`patNest_mem_FP`).

The two consumer-facing decisions are `ifParseLegacy_mem_FP` — branching on "this word's run
denotes `ψ` in the legacy grammar" is polynomial time with *no* syntactic condition on `ψ` —
and `ifParse_mem_FP` at the grammar the freeze parses with, where `NoReserved` is the only
survivor, because the structured paper-prime branch denotes reserved atoms and nothing else
(`parseStructuredPaperPrime_shape`).

`NoReserved` cannot be dropped the way `BotFree` was: the structured payload's unary length
field is an `aⁿbⁿ` constraint, which `RunAuto.BlockAutomaton` cannot express — covering
reserved targets would need `RunAuto.BlockMachine`.

Everything here is construction infrastructure rather than a paper statement, so the
declarations are `lemma`s and `def`s.  The two consumer-facing decisions carry `app:ifp`,
because they are what the freeze's recognizer is; the rest do not.
-/

namespace LogicalInduction.PatAuto

open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold
open LogicalInduction.RunAuto LogicalInduction.RpnFreeze

-- The `Nat.pair`/`unpair` reachable from the sentence codec unfolds `Nat.sqrt`'s
-- well-founded definition during `whnf` and loops; local opacity stops that.
-- See `notes/lean-gotchas.md`.
attribute [local irreducible] Nat.sqrt

/-! ## The escape-leaf test -/

/-- **The escape-leaf test, as an interface.**

For each subformula `χ` a polynomial-time decision of "this token's code decodes to `χ`".
On a `⊥`-free `χ` the test degenerates to a comparison against the fixed numeral `⌜χ⌝`
(`decode_eq_some_iff_of_botFree`) and `RunAuto.litGuard` supplies it; in general it does not,
because Foundation's decoder discards the payload at tag `0` and `⊥`'s fibre is infinite
(`decode_falsum_noncanonical`).

Building an instance requires deciding `decode c = some ⊥` in `Complexity.FP` — that is
"`c - 1` is a perfect square", with the connective cases propagating it through `Nat.unpair`,
i.e. a polynomial-time integer square root.  `⊥`'s infinite fibre is the only obstruction to
inhabiting the interface everywhere.  `FiberTest.holeGuards` (`FiberTest.lean`, built on the
axiom-clean `fiberW_mem_FP`) is the instance, and it is on the freeze recognizer's critical
path. -/
structure HoleGuards where
  /-- The guard for each subformula. -/
  guard : Sentence → TokGuard
  /-- It decides the escape-leaf obligation. -/
  guard_spec : ∀ (χ : Sentence) (c : ℕ),
    (guard χ).P c = true ↔ (Encodable.decode c : Option Sentence) = some χ

/-- The guard a pattern token asks for: a fixed numeral at a literal, the hole test at a
hole. -/
def tokGuard (H : HoleGuards) : PatTok → TokGuard
  | .lit t => litGuard t
  | .hole χ => H.guard χ

/-- The guard a pattern token demands is exactly the token's own obligation. -/
lemma tokGuard_spec (H : HoleGuards) (τ : PatTok) (c : ℕ) :
    (tokGuard H τ).P c = true ↔ τ.Matches c := by
  cases τ with
  | lit t => simp [tokGuard, litGuard]
  | hole χ => rw [tokGuard]; exact H.guard_spec χ c

/-! ## The automaton for one pattern -/

/-- The dispatch table: at position `i` demand the pattern's `i`-th token and advance;
anywhere else, fail.  `p.length + 1` is the absorbing failure state. -/
def patRows (H : HoleGuards) (p : List PatTok) (i : ℕ) : GuardRow :=
  match p[i]? with
  | some τ => ⟨[(tokGuard H τ, i + 1)], p.length + 1⟩
  | none => ⟨[], p.length + 1⟩

/-- **The prefix matcher for one pattern.** -/
def patAuto (H : HoleGuards) (p : List PatTok) : BlockAutomaton :=
  guardedAutomaton (p.length + 1) (patRows H p) (fun i => decide (i = p.length))

/-- Inside the pattern, the step advances on a satisfied guard and falls to the absorbing
state otherwise. -/
lemma patAuto_step_of_lt (H : HoleGuards) (p : List PatTok) {i : ℕ} (hi : i < p.length)
    (t : ℕ) :
    (patAuto H p).step i t
      = if (tokGuard H p[i]).P t = true then i + 1 else p.length + 1 := by
  have hrow : patRows H p i = ⟨[(tokGuard H p[i], i + 1)], p.length + 1⟩ := by
    unfold patRows
    rw [List.getElem?_eq_getElem hi]
  rw [patAuto, guardedAutomaton_step]
  simp only [hrow, rowStep]
  split_ifs <;> omega

/-- Past the pattern's end, every step falls to the absorbing state. -/
lemma patAuto_step_of_ge (H : HoleGuards) (p : List PatTok) {i : ℕ} (hi : p.length ≤ i)
    (t : ℕ) :
    (patAuto H p).step i t = p.length + 1 := by
  have hrow : patRows H p i = ⟨[], p.length + 1⟩ := by
    unfold patRows
    rw [List.getElem?_eq_none hi]
  rw [patAuto, guardedAutomaton_step]
  simp only [hrow, rowStep]
  omega

/-- The failure state absorbs. -/
lemma foldl_patAuto_fail (H : HoleGuards) (p : List PatTok) :
    ∀ b : List ℕ, List.foldl (patAuto H p).step (p.length + 1) b = p.length + 1
  | [] => rfl
  | t :: b => by
      rw [List.foldl_cons, patAuto_step_of_ge H p (by omega) t]
      exact foldl_patAuto_fail H p b

/-- **The fold reaches the end state exactly on a match**, from any reachable position.

Proof kind: `P` proved.  Provenance: (a) `patAuto_step_of_lt`, `foldl_patAuto_fail`,
`tokGuard_spec`; (b) `List.drop_eq_getElem_cons`. -/
lemma foldl_patAuto (H : HoleGuards) (p : List PatTok) : ∀ (b : List ℕ) (i : ℕ), i ≤ p.length →
    (List.foldl (patAuto H p).step i b = p.length ↔ PatMatch (p.drop i) b)
  | [], i, hi => by
      rw [List.foldl_nil, patMatch_nil_right]
      constructor
      · intro h; subst h; simp
      · intro h
        have hle : p.length ≤ i := List.drop_eq_nil_iff.mp h
        omega
  | (t :: b), i, hi => by
      rw [List.foldl_cons]
      by_cases hlt : i < p.length
      · rw [patAuto_step_of_lt H p hlt t, List.drop_eq_getElem_cons hlt,
          patMatch_cons_left_iff]
        by_cases hg : (tokGuard H p[i]).P t = true
        · rw [if_pos hg, foldl_patAuto H p b (i + 1) (by omega)]
          constructor
          · intro h
            exact ⟨t, b, (tokGuard_spec H _ t).mp hg, h, rfl⟩
          · rintro ⟨c, b', _, hrest, hcb⟩
            obtain ⟨rfl, rfl⟩ := List.cons.inj hcb
            exact hrest
        · rw [if_neg hg, foldl_patAuto_fail H p b]
          constructor
          · intro h; omega
          · rintro ⟨c, b', hc, _, hcb⟩
            obtain ⟨rfl, -⟩ := List.cons.inj hcb
            exact absurd ((tokGuard_spec H _ t).mpr hc) hg
      · have hge : p.length ≤ i := by omega
        have hdrop : p.drop i = [] := List.drop_eq_nil_of_le hge
        rw [patAuto_step_of_ge H p hge t, foldl_patAuto_fail H p b, hdrop]
        constructor
        · intro h; omega
        · intro h; exact absurd h (by simp)

/-- **The automaton decides the pattern.** -/
lemma patAuto_accepts (H : HoleGuards) (p : List PatTok) (b : List ℕ) :
    (patAuto H p).Accepts b = true ↔ PatMatch p b := by
  rw [BlockAutomaton.Accepts, patAuto, guardedAutomaton_accept, decide_eq_true_eq]
  have h := foldl_patAuto H p b 0 (Nat.zero_le _)
  rw [List.drop_zero] at h
  rw [BlockAutomaton.run]
  exact h

/-! ## The disjunction over a target's patterns -/

/-- A nest over the pattern list: take `X` as soon as one pattern matches. -/
def patNest (H : HoleGuards) (S X Y : List Bool → List Bool) :
    List (List PatTok) → List Bool → List Bool
  | [], z => Y z
  | p :: ps, z =>
      if (patAuto H p).Accepts (decodeBits (S z)) = true then X z
      else patNest H S X Y ps z

/-- If some pattern in the list matches, the nest takes the `X` branch. -/
lemma patNest_pos (H : HoleGuards) (S X Y : List Bool → List Bool) :
    ∀ (l : List (List PatTok)) (z : List Bool),
      (∃ p ∈ l, PatMatch p (decodeBits (S z))) → patNest H S X Y l z = X z
  | [], z, hm => by obtain ⟨p, hp, -⟩ := hm; exact absurd hp (by simp)
  | (p :: l), z, hm => by
      rw [patNest]
      by_cases h : PatMatch p (decodeBits (S z))
      · rw [if_pos ((patAuto_accepts H p _).mpr h)]
      · rw [if_neg (fun hc => h ((patAuto_accepts H p _).mp hc))]
        refine patNest_pos H S X Y l z ?_
        obtain ⟨q, hq, hqm⟩ := hm
        rcases List.mem_cons.mp hq with hc | hc
        · exact absurd (hc ▸ hqm) h
        · exact ⟨q, hc, hqm⟩

/-- If none matches, it takes the `Y` branch. -/
lemma patNest_neg (H : HoleGuards) (S X Y : List Bool → List Bool) :
    ∀ (l : List (List PatTok)) (z : List Bool),
      (¬ ∃ p ∈ l, PatMatch p (decodeBits (S z))) → patNest H S X Y l z = Y z
  | [], z, _ => by rw [patNest]
  | (p :: l), z, hm => by
      rw [patNest, if_neg (fun hc =>
        hm ⟨p, List.mem_cons_self .., (patAuto_accepts H p _).mp hc⟩)]
      exact patNest_neg H S X Y l z
        (fun hc => hm (by obtain ⟨q, hq, hqm⟩ := hc; exact ⟨q, List.mem_cons_of_mem _ hq, hqm⟩))

/-- The nest is polynomial time when its three components are. -/
lemma patNest_mem_FP (H : HoleGuards) {S X Y : List Bool → List Bool} (hS : S ∈ FP)
    (hX : X ∈ FP) (hY : Y ∈ FP) :
    ∀ l : List (List PatTok), (fun z => patNest H S X Y l z) ∈ FP
  | [] => by
      have heq : (fun z => patNest H S X Y [] z) = Y := by funext z; rw [patNest]
      rwa [heq]
  | (p :: l) => by
      have hrec := patNest_mem_FP H hS hX hY l
      have h := (patAuto H p).ifAuto_mem_FP hS hX hrec
      have heq : (fun z => if (patAuto H p).Accepts (decodeBits (S z)) = true then X z
            else patNest H S X Y l z) = fun z => patNest H S X Y (p :: l) z := by
        funext z; rw [patNest]
      rwa [heq] at h

/-! ## The decisions the freeze asks for -/

/-- **Branching on "this word's run denotes `ψ` in the legacy grammar" is polynomial
time** — with no syntactic condition on `ψ` at all, given the hole guards.

Proof kind: `C` composition.  Provenance: (a) `patNest_pos`, `patNest_neg`,
`patNest_mem_FP`; (b) `RpnFreeze.parseRpnLegacy_iff_patMatch`.
Paper node: `app:ifp` -/
lemma ifParseLegacy_mem_FP (H : HoleGuards) (ψ : Sentence)
    {S X Y : List Bool → List Bool} (hS : S ∈ FP) (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if parseRpnLegacy (decodeBits (S z)).length (decodeBits (S z))
          = some (ψ, []) then X z else Y z) ∈ FP := by
  have h := patNest_mem_FP H hS hX hY (patterns ψ)
  have heq : (fun z => patNest H S X Y (patterns ψ) z)
      = fun z => if parseRpnLegacy (decodeBits (S z)).length (decodeBits (S z))
          = some (ψ, []) then X z else Y z := by
    funext z
    by_cases hp : parseRpnLegacy (decodeBits (S z)).length (decodeBits (S z))
        = some (ψ, [])
    · rw [patNest_pos H S X Y _ z
        ((parseRpnLegacy_iff_patMatch ψ (decodeBits (S z))).mp hp), if_pos hp]
    · rw [patNest_neg H S X Y _ z
        (fun hc => hp ((parseRpnLegacy_iff_patMatch ψ (decodeBits (S z))).mpr hc)),
        if_neg hp]
  rwa [heq] at h

/-- **The same at the grammar the freeze parses with.**

`NoReserved` survives here, and it is the *only* survivor: the structured paper-prime branch
of `parseRpn` denotes reserved atoms and nothing else
(`parseStructuredPaperPrime_shape`), so a target with no reserved-atom subformula never
reaches it.  Covering reserved targets needs a different device — the structured payload's
unary length field is an `aⁿbⁿ` constraint, so `RunAuto.BlockAutomaton` cannot express it
and `RunAuto.BlockMachine` is what would have to be used.

Proof kind: `C` composition.  Provenance: (a) `ifParseLegacy_mem_FP`;
(b) `RpnFreeze.parseRpn_iff_patMatch`.
Paper node: `app:ifp` -/
lemma ifParse_mem_FP (H : HoleGuards) {ψ : Sentence} (hnr : NoReserved ψ)
    {S X Y : List Bool → List Bool} (hS : S ∈ FP) (hX : X ∈ FP) (hY : Y ∈ FP) :
    (fun z => if parseRpn (decodeBits (S z)).length (decodeBits (S z))
          = some (ψ, []) then X z else Y z) ∈ FP := by
  have h := patNest_mem_FP H hS hX hY (patterns ψ)
  have heq : (fun z => patNest H S X Y (patterns ψ) z)
      = fun z => if parseRpn (decodeBits (S z)).length (decodeBits (S z))
          = some (ψ, []) then X z else Y z := by
    funext z
    by_cases hp : parseRpn (decodeBits (S z)).length (decodeBits (S z)) = some (ψ, [])
    · rw [patNest_pos H S X Y _ z
        ((parseRpn_iff_patMatch hnr (decodeBits (S z))).mp hp), if_pos hp]
    · rw [patNest_neg H S X Y _ z
        (fun hc => hp ((parseRpn_iff_patMatch hnr (decodeBits (S z))).mpr hc)),
        if_neg hp]
  rwa [heq] at h

end LogicalInduction.PatAuto
