import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Foundation.Propositional.Logic.Basic

/-!
# Foundations — the object language and the pricing carrier

The §2 substrate the logical induction criterion is stated over: the propositional object
language, and the valuation and history types that carry prices.

* `Sentence` is `LO.Propositional.Formula ℕ`, a reducible `abbrev`, so Foundation's
  `DecidableEq` and `Encodable` instances transfer; `Encodable` — a computable `ℕ`-coding
  of sentences — is what `def:ec` needs to emit sentence codes at all. The paper fixes its
  language `ℒ` only up to "some language of propositional logic" with the usual
  connectives and modus ponens (tex:560); atoms over `ℕ` are a concrete countable choice.
* `Valuation` is `Sentence → ℝ`, the paper's `def:market` valuation with the codomain
  widened from `[0,1]` to `ℝ` so that valuation features denote as *total* real-valued
  functions. The `[0,1]` constraint is imposed by the consumers that need it
  (`ComputableMarket`, `PCWorld`).
* `History` is `ℕ → Valuation`, one valuation per day: the domain a `def:valfeature` /
  `def:tf` feature's denotation is a function of. As an iterated Pi type over `ℝ` it
  carries the product topology automatically, which is what `continuous_denote` and the
  Brouwer fixed-point step of the construction consume.

Days are indexed from `0` here and from `ℕ⁺` in the paper (tex:556), so day `n` here is
the paper's day `n+1`; ranks and price features follow the convention uniformly.

The two `example`s pin the substrate facts `def:ec` relies on, and
`decode_sentence_eq_ofNat` / `encode_sentence_eq_toNat` identify the `Encodable` coding, and
`encode_falsum` / `encode_atom` / `encode_imp` / `encode_and` / `encode_or` (with the derived
`encode_negAtom` / `encode_top`) give the constructor codes in closed pairing form
with Foundation's own `Formula.ofNat` / `Formula.toNat` definitionally, which is what lets a
code-level matcher be written in Foundation's terms and read back as a `Sentence` code
(`Construction/Freeze/Prefix.lean`, `Construction/Freeze/CanonicalCodes.lean`).

Worlds, deductive processes, features, traders, exploitation and both efficiency classes
are `Framework/Criterion.lean` and `Framework/Efficiency.lean`; this module is only
the language and the pricing carrier.
-/

namespace LogicalInduction

/-! ## The object language -/

/-- Sentences of the ambient propositional language, as a thin wrapper over Foundation's
`Formula ℕ`. Atoms over `ℕ` give a concrete countable language; the wrapper is a reducible
`abbrev` so Foundation's instances (`DecidableEq`, and — the fact that gates `def:ec` —
`Encodable`, a computable `ℕ`-coding of sentences) transfer for free. -/
abbrev Sentence : Type := LO.Propositional.Formula ℕ

-- The two substrate facts `def:ec` relies on, confirmed available on `Sentence`.
example : DecidableEq Sentence := inferInstance
example : Encodable Sentence := inferInstance

/-- The `Sentence` decoder is Foundation's `Formula.ofNat`, definitionally. -/
lemma decode_sentence_eq_ofNat (n : ℕ) :
    (Encodable.decode n : Option Sentence) =
      LO.Propositional.Formula.ofNat n := rfl

/-- The `Sentence` encoder is Foundation's `Formula.toNat`, definitionally. -/
lemma encode_sentence_eq_toNat (φ : Sentence) :
    Encodable.encode φ = LO.Propositional.Formula.toNat φ := rfl

/-! ### The constructor codes

The five `Formula` constructors' Gödel codes in closed pairing form, each `rfl` through
Foundation's `toNat`.  Every compiler that dispatches on a sentence's code — the prefix
machine's validity test, the deductive-process atom encoders, the emission lanes — reads
them off here rather than restating them. -/

/-- `⌜⊥⌝ = 1`. -/
lemma encode_falsum : Encodable.encode (LO.Propositional.Formula.falsum : Sentence) = 1 := rfl

/-- `⌜atom a⌝ = ⟪1, a⟫ + 1`. -/
lemma encode_atom (a : ℕ) :
    Encodable.encode (LO.Propositional.Formula.atom a : Sentence) = Nat.pair 1 a + 1 := rfl

/-- `⌜φ 🡒 ψ⌝ = ⟪2, ⟪⌜φ⌝, ⌜ψ⌝⟫⟫ + 1`. -/
lemma encode_imp (φ ψ : Sentence) :
    Encodable.encode (LO.Propositional.Formula.imp φ ψ) =
      Nat.pair 2 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1 := rfl

/-- `⌜φ ⋏ ψ⌝ = ⟪3, ⟪⌜φ⌝, ⌜ψ⌝⟫⟫ + 1`. -/
lemma encode_and (φ ψ : Sentence) :
    Encodable.encode (LO.Propositional.Formula.and φ ψ) =
      Nat.pair 3 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1 := rfl

/-- `⌜φ ⋎ ψ⌝ = ⟪4, ⟪⌜φ⌝, ⌜ψ⌝⟫⟫ + 1`. -/
lemma encode_or (φ ψ : Sentence) :
    Encodable.encode (LO.Propositional.Formula.or φ ψ) =
      Nat.pair 4 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1 := rfl

/-- `⌜∼atom m⌝`, the negated-atom code the deductive-process lanes publish. -/
lemma encode_negAtom (m : ℕ) :
    Encodable.encode (∼(LO.Propositional.Formula.atom m) : Sentence) =
      Nat.pair 2 (Nat.pair (Nat.pair 1 m + 1) (Nat.pair 0 0 + 1)) + 1 := rfl

/-- `⌜⊤⌝`, i.e. `⌜⊥ 🡒 ⊥⌝`. -/
lemma encode_top :
    Encodable.encode (⊤ : Sentence) =
      Nat.pair 2 (Nat.pair (Nat.pair 0 0 + 1) (Nat.pair 0 0 + 1)) + 1 := rfl

/-! ## Valuations and histories -/

/-- `def:market` (Valuation). A value assignment to sentences. The paper's valuations land
in `[0,1]`; the codomain here is `ℝ` so that valuation features denote as *total*
real-valued functions, the `[0,1]` constraint being imposed downstream where a consumer
needs it (markets and worlds). -/
abbrev Valuation : Type := Sentence → ℝ

/-- A **valuation history**: one valuation per day. This is the domain a valuation
feature's denotation is a (continuous) function of (`def:valfeature`, `def:tf`). Carries
the product topology automatically as an iterated Pi type over `ℝ`.

Indexing note (disclosed convention, not a modeling change): the paper indexes days from
`ℕ⁺` (tex:556) and this development indexes from `0`, so "day `n`" here is the paper's day
`n+1`. Ranks and price features follow this convention uniformly. -/
abbrev History : Type := ℕ → Valuation

end LogicalInduction
