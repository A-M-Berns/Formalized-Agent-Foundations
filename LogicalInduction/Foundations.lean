/-
# Part I — Foundations (`LogicalInduction.Foundations`)

Language and the probabilistic substrate the criterion is stated over. Nodes hosted here
(see roadmap §3, Part I):

* `def:lang`   → `Sentence` — thin wrapper over Foundation's `Formula ℕ` / `⊢` /
  `Consistent`. Inspect Foundation's *actual* API; do not assume it. `Formula ℕ` carries
  `DecidableEq` and `Encodable` (→ computable sentence codes, which `def:ec` needs).
* `def:market` / `def:world` → `Valuation`, `World` — a world is a propositionally
  consistent `{0,1}` valuation; a market is a computable sequence of `[0,1]`-pricings.
* `def:worlds` → `DeductiveProcess` — `D n ⊆ D (n+1)`, each propositionally consistent,
  union = theorems.
* `def:ec`     → `EfficientlyComputable` — a fuel-clocked interpreter (`dd:fuel`),
  **not** a complexity class. This is a disclosed type-`(c)` modeling choice.

When this Part grows past one file, promote it to the Mathlib idiom: a `Foundations/`
directory of content files plus this file as their roll-up.

TODO(blueprint:def:lang): wrap Foundation's propositional `Formula ℕ` interface.
-/

namespace LogicalInduction

end LogicalInduction
