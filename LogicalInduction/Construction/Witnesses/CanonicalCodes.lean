/-
# Canonical Gödel codes: where the escape leaf really needs `unpair`

The finite-perturbation freeze must decide, at a price leaf, whether the buffered
sentence run denotes a *table* sentence.  In the flat RPN grammar one spelling of a
sentence is the two-token escape `[1, c]`, whose meaning is `Encodable.decode c`
(`parseRpn`, `Framework/Criterion.lean`), so the decision is
`Encodable.decode c = some ψ` for a target `ψ` fixed by the table.

The recorded obstruction (`RpnFreeze.lean`'s header, `matchRun_polyFueled`'s scope
warning) is that this test cannot be the canonical-code comparison `c = ⌜ψ⌝`, because
Foundation's `Formula.ofNat` **ignores the payload at tag `0`**: every `e` with
`e.unpair.1 = 0` decodes to `⊥`.  `decode` is therefore not injective, and the honest
test `sentenceMatches` (`BoundedEvaluation.lean`) reads `Nat.unpair`, i.e. integer square
root — the one primitive the `dd:fuel` digit calculus is not closed under.

**This file draws the line exactly.**  The non-injectivity is *entirely* caused by `⊥`:

* `decode_eq_some_iff_of_botFree` — if the target sentence contains **no `⊥`
  subformula**, then `decode c = some ψ ↔ c = ⌜ψ⌝`.  The escape test collapses to a
  comparison against a fixed numeral, which is a forward digit operation and needs no
  square root at all.
* `sentenceMatches_of_botFree` — the operational form: the decoder-faithful matcher
  *is* the canonical comparison on `⊥`-free targets.
* `decode_falsum_noncanonical`, `ofNat_and_pair`, `decode_and_noncanonical` — the
  converse side.  `⊥` genuinely has two codes, and the ambiguity propagates through
  every connective, so the restriction is not an artifact of how the proof is arranged:
  for a target with a `⊥` subformula the canonical test is *unsound* (it rejects codes
  the parser accepts), and the freeze would leave such a leaf unfrozen, breaking
  `EF.freezeOn_denoteWith`'s exactness.

So the standing disclosure is narrower than recorded: `unpair` is unavoidable **iff**
the frozen table contains a sentence with a `⊥` subformula.  For a `⊥`-free table every
test in the freeze matcher is a comparison against a constant.

Supporting infrastructure for the freeze certificate rather than a paper claim; the
declarations are `lemma`s.
Paper node: `app:ifp` (the finite-perturbation efficiency closure).
-/
import LogicalInduction.Construction.Witnesses.BoundedEvaluation

namespace LogicalInduction

open LO.Propositional PrefixPatchCompile

private lemma decode_sentence_eq_ofNat (n : ℕ) :
    (Encodable.decode n : Option Sentence) = Formula.ofNat n := rfl

private lemma encode_sentence_eq_toNat (φ : Sentence) :
    Encodable.encode φ = Formula.toNat φ := rfl

/-! ## `⊥`-freeness -/

/-- A sentence with no `⊥` subformula.  This is exactly the class on which Foundation's
`Formula.ofNat` is injective. -/
def BotFree : Sentence → Prop
  | ⊥ => False
  | .atom _ => True
  | φ 🡒 ψ => BotFree φ ∧ BotFree ψ
  | φ ⋏ ψ => BotFree φ ∧ BotFree ψ
  | φ ⋎ ψ => BotFree φ ∧ BotFree ψ

@[simp] lemma botFree_falsum : ¬ BotFree (⊥ : Sentence) := id
@[simp] lemma botFree_atom (a : ℕ) : BotFree (Formula.atom a) := trivial
@[simp] lemma botFree_imp (φ ψ : Sentence) :
    BotFree (φ 🡒 ψ) ↔ BotFree φ ∧ BotFree ψ := Iff.rfl
@[simp] lemma botFree_and (φ ψ : Sentence) :
    BotFree (φ ⋏ ψ) ↔ BotFree φ ∧ BotFree ψ := Iff.rfl
@[simp] lemma botFree_or (φ ψ : Sentence) :
    BotFree (φ ⋎ ψ) ↔ BotFree φ ∧ BotFree ψ := Iff.rfl

/-! ## The reserved atom shape -/

/-- A sentence no subformula of which is a **reserved atom** `atom (Nat.pair 7 _)`.

Tag `7` is the atom payload the structured paper-prime leaf builds
(`parseStructuredPaperPrime`), and it is the *only* sentence shape that leaf can denote
(`RpnFreeze.parseStructuredPaperPrime_shape`).  So a target satisfying this is never denoted
by a structured block, and a run matcher may reject one on its two-token tag alone. -/
def NoReserved : Sentence → Prop
  | ⊥ => True
  | .atom a => ∀ pol fc : ℕ, a ≠ Nat.pair 7 (Nat.pair pol fc)
  | φ 🡒 ψ => NoReserved φ ∧ NoReserved ψ
  | φ ⋏ ψ => NoReserved φ ∧ NoReserved ψ
  | φ ⋎ ψ => NoReserved φ ∧ NoReserved ψ

@[simp] lemma noReserved_falsum : NoReserved (⊥ : Sentence) := trivial
@[simp] lemma noReserved_atom (a : ℕ) :
    NoReserved (Formula.atom a) ↔ ∀ pol fc : ℕ, a ≠ Nat.pair 7 (Nat.pair pol fc) := Iff.rfl
@[simp] lemma noReserved_imp (φ ψ : Sentence) :
    NoReserved (φ 🡒 ψ) ↔ NoReserved φ ∧ NoReserved ψ := Iff.rfl
@[simp] lemma noReserved_and (φ ψ : Sentence) :
    NoReserved (φ ⋏ ψ) ↔ NoReserved φ ∧ NoReserved ψ := Iff.rfl
@[simp] lemma noReserved_or (φ ψ : Sentence) :
    NoReserved (φ ⋎ ψ) ↔ NoReserved φ ∧ NoReserved ψ := Iff.rfl

/-! ## The recognition side conditions, in one place

The freeze's run-level lookup carries side conditions rather than machinery, and they are
easier to audit collected than scattered.  There are **three**, in two families:

*On each sentence of the frozen quote table* — bundled as `Recognizable` below:

1. `BotFree ψ` — no `⊥` subformula.  Without it the escape leaf admits infinitely many
   codes (`decode_falsum_noncanonical`), so no finite spelling list is exhaustive and the
   decision reduces to `Nat.unpair` / integer square root.
2. `NoReserved ψ` — no reserved-atom subformula.  Without it a structured block may denote
   the target, and the structured payload admits non-canonical spellings that no fixed word
   comparison catches.

*On the table as a whole*:

3. The constant output bound `FreezeStep.RunOracle.R_length_le` — the emitted quote block
   fits in a fixed budget.  This is the paper's own finiteness (`app:ifp`) reappearing as
   the condition that makes `TokenFold.runFold_mem_FP`'s emission budget close.

Conditions 1 and 2 are what make a target's complete spellings a *finite explicit list*
(`RpnFreeze.spellings`); condition 3 is what makes emitting the answer polynomial.  None of
them is a restriction on the freeze, the trader, or the market — all three are properties of
the table being frozen. -/

/-- The per-sentence recognition conditions on a frozen table entry. -/
structure Recognizable (ψ : Sentence) : Prop where
  /-- No `⊥` subformula: the escape leaf has a unique code. -/
  botFree : BotFree ψ
  /-- No reserved-atom subformula: the structured leaf cannot denote it. -/
  noReserved : NoReserved ψ

/-! ## Injectivity of the decoder on `⊥`-free targets -/

/-- **The ruling.**  Off the `⊥` fiber the Foundation decoder is injective: a code
denoting a `⊥`-free sentence *is* that sentence's canonical code.

This is what turns the escape-leaf decision `decode c = some ψ` — recorded as reducing
to `Nat.unpair` / integer square root — into the comparison `c = ⌜ψ⌝` against a fixed
numeral, whenever the target is `⊥`-free.

Proof kind: `P` proved.  Provenance: (b) Foundation `Formula.ofNat`, `Encodable.encodek`,
`Nat.pair_unpair`.
Paper node: `app:ifp` -/
lemma decode_eq_some_iff_of_botFree :
    ∀ (φ : Sentence), BotFree φ → ∀ c : ℕ,
      (Encodable.decode c : Option Sentence) = some φ ↔ c = Encodable.encode φ := by
  intro φ hφ c
  refine ⟨?_, fun h => by subst h; exact Encodable.encodek φ⟩
  revert c
  induction φ using LO.Propositional.Formula.rec' with
  | hfalsum => exact absurd hφ id
  | hatom a =>
      intro c hc
      rw [decode_sentence_eq_ofNat] at hc
      cases c with
      | zero => simp [Formula.ofNat] at hc
      | succ e =>
          rcases htag : e.unpair.1 with _ | _ | tag
          · simp [Formula.ofNat, htag] at hc
          · simp only [Formula.ofNat, htag] at hc
            have hd : (Encodable.decode e.unpair.2 : Option ℕ) = some e.unpair.2 := rfl
            rw [hd] at hc
            simp only [Option.map_some] at hc
            have hpay : e.unpair.2 = a := by
              have := Option.some.inj hc
              exact Formula.atom.inj this
            have hpair : Nat.pair e.unpair.1 e.unpair.2 = e := Nat.pair_unpair e
            rw [htag, hpay] at hpair
            rw [encode_sentence_eq_toNat, Formula.toNat]
            have hea : (Encodable.encode a : ℕ) = a := rfl
            rw [hea, hpair]
          · rcases tag with _ | _ | _ | tag <;>
              simp [Formula.ofNat, htag, Option.bind_eq_some_iff] at hc
  | himp φ ψ ihφ ihψ =>
      obtain ⟨hbφ, hbψ⟩ := hφ
      intro c hc
      rw [decode_sentence_eq_ofNat] at hc
      cases c with
      | zero => simp [Formula.ofNat] at hc
      | succ e =>
          rcases htag : e.unpair.1 with _ | _ | _ | tag
          · simp [Formula.ofNat, htag] at hc
          · simp [Formula.ofNat, htag] at hc
          · simp only [Formula.ofNat, htag] at hc
            rcases hα : (Formula.ofNat e.unpair.2.unpair.1 : Option Sentence) with _ | α
            · rw [hα] at hc; simp at hc
            · rcases hβ : (Formula.ofNat e.unpair.2.unpair.2 : Option Sentence) with _ | β
              · rw [hα, hβ] at hc; simp at hc
              · rw [hα, hβ] at hc
                have hc' : (some (α 🡒 β) : Option Sentence) = some (φ 🡒 ψ) := hc
                obtain ⟨hab1, hab2⟩ := Formula.imp.inj (Option.some.inj hc')
                have h1 := ihφ hbφ _ (by rw [decode_sentence_eq_ofNat, hα, hab1])
                have h2 := ihψ hbψ _ (by rw [decode_sentence_eq_ofNat, hβ, hab2])
                rw [encode_sentence_eq_toNat] at h1 h2
                have hp2 : Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2
                    = e.unpair.2 := Nat.pair_unpair _
                have hp1 : Nat.pair e.unpair.1 e.unpair.2 = e := Nat.pair_unpair e
                have htagN : e.unpair.1 = 2 := by omega
                rw [encode_sentence_eq_toNat,
                  show Formula.toNat (φ 🡒 ψ)
                      = Nat.pair 2 (Nat.pair φ.toNat ψ.toNat) + 1 from rfl,
                  ← h1, ← h2, hp2, ← htagN, hp1]
          · rcases tag with _ | _ | tag <;>
              simp [Formula.ofNat, htag, Option.bind_eq_some_iff] at hc
  | hand φ ψ ihφ ihψ =>
      obtain ⟨hbφ, hbψ⟩ := hφ
      intro c hc
      rw [decode_sentence_eq_ofNat] at hc
      cases c with
      | zero => simp [Formula.ofNat] at hc
      | succ e =>
          rcases htag : e.unpair.1 with _ | _ | _ | _ | tag
          · simp [Formula.ofNat, htag] at hc
          · simp [Formula.ofNat, htag] at hc
          · simp [Formula.ofNat, htag, Option.bind_eq_some_iff] at hc
          · simp only [Formula.ofNat, htag] at hc
            rcases hα : (Formula.ofNat e.unpair.2.unpair.1 : Option Sentence) with _ | α
            · rw [hα] at hc; simp at hc
            · rcases hβ : (Formula.ofNat e.unpair.2.unpair.2 : Option Sentence) with _ | β
              · rw [hα, hβ] at hc; simp at hc
              · rw [hα, hβ] at hc
                have hc' : (some (α ⋏ β) : Option Sentence) = some (φ ⋏ ψ) := hc
                obtain ⟨hab1, hab2⟩ := Formula.and.inj (Option.some.inj hc')
                have h1 := ihφ hbφ _ (by rw [decode_sentence_eq_ofNat, hα, hab1])
                have h2 := ihψ hbψ _ (by rw [decode_sentence_eq_ofNat, hβ, hab2])
                rw [encode_sentence_eq_toNat] at h1 h2
                have hp2 : Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2
                    = e.unpair.2 := Nat.pair_unpair _
                have hp1 : Nat.pair e.unpair.1 e.unpair.2 = e := Nat.pair_unpair e
                have htagN : e.unpair.1 = 3 := by omega
                rw [encode_sentence_eq_toNat,
                  show Formula.toNat (φ ⋏ ψ)
                      = Nat.pair 3 (Nat.pair φ.toNat ψ.toNat) + 1 from rfl,
                  ← h1, ← h2, hp2, ← htagN, hp1]
          · rcases tag with _ | tag <;>
              simp [Formula.ofNat, htag, Option.bind_eq_some_iff] at hc
  | hor φ ψ ihφ ihψ =>
      obtain ⟨hbφ, hbψ⟩ := hφ
      intro c hc
      rw [decode_sentence_eq_ofNat] at hc
      cases c with
      | zero => simp [Formula.ofNat] at hc
      | succ e =>
          rcases htag : e.unpair.1 with _ | _ | _ | _ | _ | tag
          · simp [Formula.ofNat, htag] at hc
          · simp [Formula.ofNat, htag] at hc
          · simp [Formula.ofNat, htag, Option.bind_eq_some_iff] at hc
          · simp [Formula.ofNat, htag, Option.bind_eq_some_iff] at hc
          · simp only [Formula.ofNat, htag] at hc
            rcases hα : (Formula.ofNat e.unpair.2.unpair.1 : Option Sentence) with _ | α
            · rw [hα] at hc; simp at hc
            · rcases hβ : (Formula.ofNat e.unpair.2.unpair.2 : Option Sentence) with _ | β
              · rw [hα, hβ] at hc; simp at hc
              · rw [hα, hβ] at hc
                have hc' : (some (α ⋎ β) : Option Sentence) = some (φ ⋎ ψ) := hc
                obtain ⟨hab1, hab2⟩ := Formula.or.inj (Option.some.inj hc')
                have h1 := ihφ hbφ _ (by rw [decode_sentence_eq_ofNat, hα, hab1])
                have h2 := ihψ hbψ _ (by rw [decode_sentence_eq_ofNat, hβ, hab2])
                rw [encode_sentence_eq_toNat] at h1 h2
                have hp2 : Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2
                    = e.unpair.2 := Nat.pair_unpair _
                have hp1 : Nat.pair e.unpair.1 e.unpair.2 = e := Nat.pair_unpair e
                have htagN : e.unpair.1 = 4 := by omega
                rw [encode_sentence_eq_toNat,
                  show Formula.toNat (φ ⋎ ψ)
                      = Nat.pair 4 (Nat.pair φ.toNat ψ.toNat) + 1 from rfl,
                  ← h1, ← h2, hp2, ← htagN, hp1]
          · simp [Formula.ofNat, htag] at hc

/-- **The operational form of the ruling.**  On a `⊥`-free target the decoder-faithful
matcher `sentenceMatches` — whose definition reads `Nat.unpair` at every node — is
extensionally the canonical-code comparison.

Proof kind: `C` composition.  Provenance: (a) `decode_eq_some_iff_of_botFree`,
(b) `sentenceMatches_eq_one_iff`, `sentenceMatches_eq_zero_iff`.
Paper node: `app:ifp` -/
lemma sentenceMatches_of_botFree (φ : Sentence) (hφ : BotFree φ) (c : ℕ) :
    sentenceMatches φ c = if c = Encodable.encode φ then 1 else 0 := by
  by_cases h : c = Encodable.encode φ
  · rw [if_pos h]
    exact (sentenceMatches_eq_one_iff φ c).mpr
      ((decode_eq_some_iff_of_botFree φ hφ c).mpr h)
  · rw [if_neg h]
    exact (sentenceMatches_eq_zero_iff φ c).mpr
      (fun hdec => h ((decode_eq_some_iff_of_botFree φ hφ c).mp hdec))

/-! ## The converse side: `⊥` really is ambiguous, and the ambiguity propagates -/

/-- `2` is a non-canonical code for `⊥`: `⌜⊥⌝ = 1`.  This is the whole source of the
decoder's non-injectivity — `Formula.ofNat` discards the payload at tag `0`.

Proof kind: `N-` non-vacuity witness (the negative side).  Provenance: (b) Foundation
`Formula.ofNat`.
Paper node: `app:ifp` -/
lemma decode_falsum_noncanonical :
    (Encodable.decode 2 : Option Sentence) = some ⊥ ∧
      (2 : ℕ) ≠ Encodable.encode (⊥ : Sentence) := by
  constructor
  · rw [decode_sentence_eq_ofNat]
    have h : (1 : ℕ).unpair.1 = 0 := by decide
    simp [Formula.ofNat, h]
  · rw [show Encodable.encode (⊥ : Sentence) = 1 from by decide]
    omega

/-- The conjunction node of `Formula.ofNat`, read forwards: any pair of codes for `φ`
and `ψ` gives a code for `φ ⋏ ψ`. -/
lemma ofNat_and_pair {φ ψ : Sentence} {c d : ℕ}
    (hc : (Encodable.decode c : Option Sentence) = some φ)
    (hd : (Encodable.decode d : Option Sentence) = some ψ) :
    (Encodable.decode (Nat.pair 3 (Nat.pair c d) + 1) : Option Sentence)
      = some (φ ⋏ ψ) := by
  rw [decode_sentence_eq_ofNat] at hc hd ⊢
  simp [Formula.ofNat, hc, hd]

/-- **The restriction is necessary, not an artifact.**  `⊥`'s two codes propagate
through every connective, so a target with a `⊥` subformula has at least two codes and
the canonical comparison `c = ⌜ψ⌝` *rejects codes the parser accepts*.  A freeze using
that test would leave such a price leaf unfrozen, which is exactly the hypothesis
`EF.freezeOn_denoteWith` needs (`hin` must hold at *every* selected leaf).

Proof kind: `N-` non-vacuity witness (the negative side).  Provenance:
(a) `decode_falsum_noncanonical`, `ofNat_and_pair`.
Paper node: `app:ifp` -/
lemma decode_and_noncanonical (φ : Sentence) :
    (Encodable.decode (Nat.pair 3 (Nat.pair (Encodable.encode φ) 2) + 1) :
        Option Sentence) = some (φ ⋏ ⊥) ∧
      Nat.pair 3 (Nat.pair (Encodable.encode φ) 2) + 1
        ≠ Encodable.encode (φ ⋏ (⊥ : Sentence)) := by
  refine ⟨ofNat_and_pair (Encodable.encodek φ) decode_falsum_noncanonical.1, ?_⟩
  have he : Encodable.encode (φ ⋏ (⊥ : Sentence))
      = Nat.pair 3 (Nat.pair (Encodable.encode φ) 1) + 1 := by
    rw [encode_sentence_eq_toNat, encode_sentence_eq_toNat]
    rw [show Formula.toNat (φ ⋏ (⊥ : Sentence))
        = Nat.pair 3 (Nat.pair φ.toNat (⊥ : Sentence).toNat) + 1 from rfl]
    rw [show ((⊥ : Sentence)).toNat = 1 from by decide]
  rw [he]
  intro h
  have h1 : Nat.pair 3 (Nat.pair (Encodable.encode φ) 2)
      = Nat.pair 3 (Nat.pair (Encodable.encode φ) 1) := by omega
  exact absurd (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h1).2).2 (by omega)

#print axioms LogicalInduction.decode_eq_some_iff_of_botFree
#print axioms LogicalInduction.sentenceMatches_of_botFree
#print axioms LogicalInduction.decode_falsum_noncanonical
#print axioms LogicalInduction.decode_and_noncanonical

end LogicalInduction
