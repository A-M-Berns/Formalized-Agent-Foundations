import LogicalInduction.Construction.Freeze.RunAutomaton

/-!
# The escape-leaf test, as an interface

`app:ifp` — the one thing a spelling recognizer cannot have unconditionally.  A run denotes a
target exactly when it matches one of finitely many spelling patterns: literal grammar
tokens, with a hole wherever an escape leaf may stand, the hole's obligation being
`decode c = some χ`.  Everything in that decision is a fixed-numeral comparison except the
hole, and `HoleGuards` is that hole, isolated: a polynomial-time test of "does this code
decode to `χ`", one per subformula.

Isolating it is the deliverable.  The automata that consume the interface —
`SegmentAutomaton`, `SegmentCounter`, `SegmentRecognizer` — are unconditional and
axiom-clean; the whole of what is not is here, in one structure with one field.

`HoleGuards` is inhabited: `FiberTest.holeGuards` (`FiberTest.lean`, on the axiom-clean
`fiberW_mem_FP`) is the instance, and it is on the freeze recognizer's critical path.  What
it costs is `Nat.unpair` on a token's digit word, hence integer square root in `FP`
(`DigitFP.sqrtRemW_mem_FP`, `DigitFP.unpairW_spec`); on a `⊥`-free `χ` the test degenerates
to a fixed-numeral comparison, because Foundation's decoder is injective off the `⊥` fibre
(`decode_eq_some_iff_of_botFree`).
-/

namespace LogicalInduction.PatAuto

open LogicalInduction.RunAuto

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

end LogicalInduction.PatAuto
