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

The two `example`s pin the substrate facts `def:ec` relies on.

Worlds, deductive processes, features, traders, exploitation and both efficiency classes
are `Framework/Criterion.lean` and `Framework/MachineEfficiency.lean`; this module is only
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
