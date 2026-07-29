/-
# Part I — Foundations (`LogicalInduction.Foundations`)

Language and the probabilistic substrate the criterion is stated over
(arXiv:1609.03543 §2–§3).

Defined here:

* `def:lang`   → `Sentence` — thin wrapper over Foundation's `Formula ℕ` / `⊢` /
  `Consistent`. `Formula ℕ` carries `DecidableEq` and `Encodable` (→ computable
  sentence codes, which `def:ec` needs).
* `def:market` → `Valuation` (a value assignment to sentences) and `History` (one
  valuation per day). A `def:tf` feature's denotation is a function of a `History`.

Built on this substrate downstream, in `Computable.lean` / `Criterion.lean`:

* `def:market` → `ComputableMarket` — a `History` of `[0,1]`-pricings with a computable
  price sequence.
* `def:world` → `PCWorld` — a propositionally consistent `{0,1}` valuation.
* `def:worlds` → `DeductiveProcess` — `D n ⊆ D (n+1)`, each propositionally consistent,
  union = theorems.
* `def:ec`     → `EfficientlyComputable` — a fuel-clocked interpreter (`dd:fuel`),
  **not** a complexity class. This is a disclosed type-`(c)` modeling choice.
-/
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Foundation.Propositional.Logic.Basic

namespace LogicalInduction

/-- `def:lang`. Sentences of the ambient propositional language, as a thin wrapper over
Foundation's `Formula ℕ`. Atoms over `ℕ` give a concrete countable language; the wrapper
is a reducible `abbrev` so Foundation's instances (`DecidableEq`, and — the fact that
gates `def:ec` — `Encodable`, a computable `ℕ`-coding of sentences) transfer for free. -/
abbrev Sentence : Type := LO.Propositional.Formula ℕ

-- The two substrate facts `def:ec` will rely on, confirmed available on `Sentence`.
example : DecidableEq Sentence := inferInstance
example : Encodable Sentence := inferInstance

/-- `def:market` (Valuation). A value assignment to sentences. The paper's valuations
land in `[0,1]`; we keep the codomain `ℝ` so that valuation features denote as *total*
real-valued functions (the `[0,1]` constraint is imposed downstream where a consumer
needs it, e.g. on markets and worlds). -/
abbrev Valuation : Type := Sentence → ℝ

/-- A **valuation history**: one valuation per day. This is the domain a valuation
feature's denotation is a (continuous) function of (`def:valfeature`, `def:tf`). Carries
the product topology automatically as an iterated Pi type over `ℝ`.

Indexing note (disclosed convention, not a modeling change): the paper indexes days from
`ℕ⁺`; we index from `0`. So "day `n`" here is the paper's day `n+1`. Ranks and price
features follow this convention uniformly. -/
abbrev History : Type := ℕ → Valuation

end LogicalInduction
