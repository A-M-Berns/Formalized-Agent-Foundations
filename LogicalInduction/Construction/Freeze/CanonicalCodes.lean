import LogicalInduction.Construction.Freeze.Prefix

/-!
# Canonical Gödel codes: where the escape leaf needs `unpair`

The finite-perturbation freeze decides, at a price leaf, whether the buffered sentence run
denotes a *table* sentence.  In the flat RPN grammar one spelling of a sentence is the
two-token escape `[1, c]`, whose meaning is `Encodable.decode c` (`parseRpn`,
`Framework/Criterion.lean`), so the decision is `Encodable.decode c = some ψ` for a target
`ψ` fixed by the table.

That test is not the canonical-code comparison `c = ⌜ψ⌝` in general, because Foundation's
`Formula.ofNat` **ignores the payload at tag `0`**: every `e` with `e.unpair.1 = 0` decodes
to `⊥`.  So `decode` is not injective, and the decoder-faithful matcher `sentenceMatches`
(`Prefix.lean`) reads `Nat.unpair`, i.e. integer square root — the one primitive
the `dd:fuel` digit calculus is not closed under.

This file draws the line exactly: the non-injectivity is caused *entirely* by `⊥`.

* `decode_eq_some_iff_of_botFree` — on a target with no `⊥` subformula,
  `decode c = some ψ ↔ c = ⌜ψ⌝`, so the escape test is a comparison against a fixed
  numeral, a forward digit operation needing no square root.
* `sentenceMatches_of_botFree` — its operational form: on a `⊥`-free target the
  decoder-faithful matcher *is* the canonical comparison.  It is consumed in
  `Compiler.lean` (the spelling-list lane); the injectivity lemma itself is consumed there
  and in `PatternAutomaton.lean`.
* `decode_falsum_noncanonical`, `ofNat_and_pair`, `decode_and_noncanonical` — the converse.
  `⊥` has two codes and the ambiguity propagates through every connective, so on a target
  with a `⊥` subformula the canonical test rejects codes the parser accepts, leaving the
  price leaf unfrozen and defeating `EF.freezeOn_denoteWith`'s exactness.

So `unpair` is unavoidable exactly when the frozen table contains a sentence with a `⊥`
subformula; for a `⊥`-free table every test in the freeze matcher is a comparison against a
constant.

The file also defines the two per-sentence recognition conditions `BotFree` and
`NoReserved` and bundles them as `Recognizable`; where each stands in the current freeze is
recorded at `## The recognition conditions and where the freeze stands`.

Supporting infrastructure for the freeze certificate rather than a statement of a paper
claim, so the declarations are `lemma`s, each carrying its own provenance line for `app:ifp`,
the finite-perturbation efficiency closure.  The module header itself is prose and anchors no
annotation.
-/

namespace LogicalInduction

open LO.Propositional PrefixPatchCompile

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

/-- A sentence no subformula of which is a **reserved atom** `atom (Nat.pair 5 _)`.

Tag `5` is the atom payload the structured paper-prime leaf builds
(`parseStructuredPaperPrime`), and it is the *only* sentence shape that leaf can denote
(`RpnFreeze.parseStructuredPaperPrime_shape`).  So a target satisfying this is never denoted
by a structured block, and a run matcher may reject one on its two-token tag alone. -/
def NoReserved : Sentence → Prop
  | ⊥ => True
  | .atom a => ∀ pol fc : ℕ, a ≠ Nat.pair 5 (Nat.pair pol fc)
  | φ 🡒 ψ => NoReserved φ ∧ NoReserved ψ
  | φ ⋏ ψ => NoReserved φ ∧ NoReserved ψ
  | φ ⋎ ψ => NoReserved φ ∧ NoReserved ψ

@[simp] lemma noReserved_falsum : NoReserved (⊥ : Sentence) := trivial
@[simp] lemma noReserved_atom (a : ℕ) :
    NoReserved (Formula.atom a) ↔ ∀ pol fc : ℕ, a ≠ Nat.pair 5 (Nat.pair pol fc) := Iff.rfl
@[simp] lemma noReserved_imp (φ ψ : Sentence) :
    NoReserved (φ 🡒 ψ) ↔ NoReserved φ ∧ NoReserved ψ := Iff.rfl
@[simp] lemma noReserved_and (φ ψ : Sentence) :
    NoReserved (φ ⋏ ψ) ↔ NoReserved φ ∧ NoReserved ψ := Iff.rfl
@[simp] lemma noReserved_or (φ ψ : Sentence) :
    NoReserved (φ ⋎ ψ) ↔ NoReserved φ ∧ NoReserved ψ := Iff.rfl

/-! ## The recognition conditions and where the freeze stands

The freeze's run-level lookup carries three side conditions.  Two are per-sentence
conditions on the frozen quote table, bundled below as `Recognizable`; the third is a
condition on the table as a whole.  Neither per-sentence condition is a hypothesis of the
freeze endpoint `FreezeOracle.machine_lic_iff_of_finiteSupport`; both are recorded here
because they are exactly what the `⊥`-fibre lemmas above are about, and because
`Recognizable` is the compatibility hypothesis of the endpoint's restricted form.

1. `BotFree ψ` — no `⊥` subformula.  It is what a *spelling-list* recognizer needs: without
   it the escape leaf admits infinitely many codes (`decode_falsum_noncanonical`), so no
   finite spelling list is exhaustive and the decision reduces to `Nat.unpair` / integer
   square root.  The freeze makes that decision instead of avoiding it:
   `DigitFP.sqrtRemW_mem_FP` and `DigitFP.unpairW_spec` put base-4 integer square root and
   `Nat.unpair` inside `Complexity.FP`, `FiberTest.fiberW_mem_FP` is the escape-leaf test
   built on them, and `RpnFreeze.patterns` replaces the spelling list by a list of patterns
   with holes, so the infinite fibre lives inside a hole predicate rather than defeating
   exhaustiveness.
2. `NoReserved ψ` — no reserved-atom subformula.  It is what the *structured* branch needs:
   without it a structured block may denote the target, which takes two devices.  The
   structured payload's unary length field must be matched against the payload's own token
   count — an `aⁿbⁿ` constraint, since `parseStructuredNat`'s self-loop at the numeral `0`
   makes that length unbounded even for a fixed target — and the payload language of a fixed
   formula code must be recognized exactly.  `CtrAuto.ctrMachine` is the first
   (`RunAuto.BlockMachine` instantiated as a finite control with one unary counter) and
   `PayAuto` the second.  The recognizer the freeze runs,
   `RpnFreeze.parseRpn_iff_patMatch`, needs only this condition.
3. The constant output bound `FreezeStep.RunOracle.R_length_le` — the emitted quote block
   fits in a fixed budget.  This is the paper's own finiteness (`app:ifp`) reappearing as
   the condition that makes `TokenFold.runFold_mem_FP`'s emission budget close, and it is
   what makes emitting the answer polynomial.

None of the three restricts the freeze, the trader or the market: all three are properties
of the table being frozen. -/

/-- The per-sentence recognition conditions on a frozen table entry, bundled.

The freeze endpoint does not take this bundle; its strongest consumer is the restricted
form `FreezeOracle.machine_lic_iff_of_recognizableSupport`, reached through
`FreezeOracle.RecognizableSupportPerturbation`, which `LogicalInduction.API` exports. -/
structure Recognizable (ψ : Sentence) : Prop where
  /-- No `⊥` subformula: the escape leaf has a unique code. -/
  botFree : BotFree ψ
  /-- No reserved-atom subformula: the structured leaf cannot denote it. -/
  noReserved : NoReserved ψ

/-! ## Injectivity of the decoder on `⊥`-free targets -/

/-- **The ruling.**  Off the `⊥` fiber the Foundation decoder is injective: a code
denoting a `⊥`-free sentence *is* that sentence's canonical code.

On a `⊥`-free target this turns the escape-leaf decision `decode c = some ψ`, which in
general reduces to `Nat.unpair` / integer square root, into the comparison `c = ⌜ψ⌝`
against a fixed numeral.

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
      rw [decode_sentence_eq_ofNat'] at hc
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
            rw [encode_sentence_eq_toNat', Formula.toNat]
            have hea : (Encodable.encode a : ℕ) = a := rfl
            rw [hea, hpair]
          · rcases tag with _ | _ | _ | tag <;>
              simp [Formula.ofNat, htag, Option.bind_eq_some_iff] at hc
  | himp φ ψ ihφ ihψ =>
      obtain ⟨hbφ, hbψ⟩ := hφ
      intro c hc
      rw [decode_sentence_eq_ofNat'] at hc
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
                have h1 := ihφ hbφ _ (by rw [decode_sentence_eq_ofNat', hα, hab1])
                have h2 := ihψ hbψ _ (by rw [decode_sentence_eq_ofNat', hβ, hab2])
                rw [encode_sentence_eq_toNat'] at h1 h2
                have hp2 : Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2
                    = e.unpair.2 := Nat.pair_unpair _
                have hp1 : Nat.pair e.unpair.1 e.unpair.2 = e := Nat.pair_unpair e
                have htagN : e.unpair.1 = 2 := by omega
                rw [encode_sentence_eq_toNat',
                  show Formula.toNat (φ 🡒 ψ)
                      = Nat.pair 2 (Nat.pair φ.toNat ψ.toNat) + 1 from rfl,
                  ← h1, ← h2, hp2, ← htagN, hp1]
          · rcases tag with _ | _ | tag <;>
              simp [Formula.ofNat, htag, Option.bind_eq_some_iff] at hc
  | hand φ ψ ihφ ihψ =>
      obtain ⟨hbφ, hbψ⟩ := hφ
      intro c hc
      rw [decode_sentence_eq_ofNat'] at hc
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
                have h1 := ihφ hbφ _ (by rw [decode_sentence_eq_ofNat', hα, hab1])
                have h2 := ihψ hbψ _ (by rw [decode_sentence_eq_ofNat', hβ, hab2])
                rw [encode_sentence_eq_toNat'] at h1 h2
                have hp2 : Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2
                    = e.unpair.2 := Nat.pair_unpair _
                have hp1 : Nat.pair e.unpair.1 e.unpair.2 = e := Nat.pair_unpair e
                have htagN : e.unpair.1 = 3 := by omega
                rw [encode_sentence_eq_toNat',
                  show Formula.toNat (φ ⋏ ψ)
                      = Nat.pair 3 (Nat.pair φ.toNat ψ.toNat) + 1 from rfl,
                  ← h1, ← h2, hp2, ← htagN, hp1]
          · rcases tag with _ | tag <;>
              simp [Formula.ofNat, htag, Option.bind_eq_some_iff] at hc
  | hor φ ψ ihφ ihψ =>
      obtain ⟨hbφ, hbψ⟩ := hφ
      intro c hc
      rw [decode_sentence_eq_ofNat'] at hc
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
                have h1 := ihφ hbφ _ (by rw [decode_sentence_eq_ofNat', hα, hab1])
                have h2 := ihψ hbψ _ (by rw [decode_sentence_eq_ofNat', hβ, hab2])
                rw [encode_sentence_eq_toNat'] at h1 h2
                have hp2 : Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2
                    = e.unpair.2 := Nat.pair_unpair _
                have hp1 : Nat.pair e.unpair.1 e.unpair.2 = e := Nat.pair_unpair e
                have htagN : e.unpair.1 = 4 := by omega
                rw [encode_sentence_eq_toNat',
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

/-! ## The converse: `⊥` is genuinely ambiguous, and the ambiguity propagates -/

/-- `2` is a non-canonical code for `⊥`: `⌜⊥⌝ = 1`.  This is the whole source of the
decoder's non-injectivity — `Formula.ofNat` discards the payload at tag `0`.

Proof kind: `N-` non-vacuity witness (the negative side).  Provenance: (b) Foundation
`Formula.ofNat`.
Paper node: `app:ifp` -/
lemma decode_falsum_noncanonical :
    (Encodable.decode 2 : Option Sentence) = some ⊥ ∧
      (2 : ℕ) ≠ Encodable.encode (⊥ : Sentence) := by
  constructor
  · rw [decode_sentence_eq_ofNat']
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
  rw [decode_sentence_eq_ofNat'] at hc hd ⊢
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
    rw [encode_sentence_eq_toNat', encode_sentence_eq_toNat']
    rw [show Formula.toNat (φ ⋏ (⊥ : Sentence))
        = Nat.pair 3 (Nat.pair φ.toNat (⊥ : Sentence).toNat) + 1 from rfl]
    rw [show ((⊥ : Sentence)).toNat = 1 from by decide]
  rw [he]
  intro h
  have h1 : Nat.pair 3 (Nat.pair (Encodable.encode φ) 2)
      = Nat.pair 3 (Nat.pair (Encodable.encode φ) 1) := by omega
  exact absurd (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h1).2).2 (by omega)

end LogicalInduction
