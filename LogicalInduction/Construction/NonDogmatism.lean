import LogicalInduction.Construction.NonDogmatism.RepeatedEnumeration
import LogicalInduction.Construction.NonDogmatism.Kraft
import LogicalInduction.Construction.NonDogmatism.PrefixMachine
import LogicalInduction.Construction.NonDogmatism.UniversalDovetailer
import LogicalInduction.Construction.NonDogmatism.UniversalPrefix
import LogicalInduction.Construction.NonDogmatism.BitPrefix
import LogicalInduction.Construction.NonDogmatism.StrictSeparators
import LogicalInduction.Construction.NonDogmatism.Endpoints

/-!
# Non-dogmatism and universal semimeasures (`LogicalInduction.Construction.NonDogmatism`)

The §4.6 lane: `thm:nd` (tex:1528), `thm:obu` (tex:1540), `thm:ob` (tex:1552), `thm:dus`
(tex:1561) and `thm:strict` (tex:1575).  It is not the whole of §4.6: `thm:ifp` (tex:1521)
sits in the same subsection and is discharged in `Construction/Freeze/`.

`Properties/NonDogmatism.lean`, `Properties/UniformNonDogmatism.lean`,
`Properties/OccamBounds.lean` and `Properties/UniversalSemimeasure.lean` state those nodes over
an arbitrary inductor.  Four of the five are stated behind an interface: an efficient repeated
enumeration of the source, a prefix machine supplying the complexity measure, a universal
continuous semimeasure, a bit-prefix sentence presentation, and separator data for the strict
form.  This directory constructs every one of them, so nothing in §4.6 is left as a caller
premise.  `thm:nd` is the exception and is listed here only to place the subsection: its
endpoints in `Properties/NonDogmatism.lean` take `[IsLogicalInductor P DP]` and a semantic
plausible-world hypothesis and no constructed interface at all, so no declaration in this
directory carries that node.

## The source premise

* `RepeatedEnumeration` — `triangularRepeat` and `EfficientRepeatedEnumeration.ofBig` for an
  already write-out-metered sentence stream, and `CEEnumeration` /
  `EfficientRepeatedEnumeration.ofCE` for an arbitrary computably enumerable one.  The latter
  carries out, under the interpreter clock, the padding-and-repeating step of `thm:obu`'s own
  proof (tex:5651-5656), padding with `source 0` rather than with the paper's `⊤`;
  `lic_uniform_nonDogmatism_ofCE` is `thm:obu` at the paper's own premise.

## Prefix complexity

* `Kraft` — Kraft's inequality for a finite prefix-free binary code, proved from Mathlib
  alone; it is the budget the Occam risk allocation of `thm:ob` spends.
* `PrefixMachine` — a concrete self-delimiting sentence code discharging **every** field of
  `PrefixMachinePresentation`, including both fuel-model emission programs and the additive
  negation overhead `κ(∼φ) ≤ κ(φ) + 2`.
* `UniversalPrefix` — the same boundary at the prefix complexity of a genuine self-delimiting
  *universal* machine, so `thm:ob` is not tied to one fixed code.

## Universal semimeasures

* `UniversalDovetailer` — an explicit dovetail over `Nat.Partrec.Code` with a stage clock,
  trimmed top-down into a monotone sequence of semimeasures, whose mixture `universalMass`
  dominates every lower-semicomputable continuous semimeasure.
* `BitPrefix` — the concrete `BitPrefixSentences` presentation `thm:dus` is stated over:
  literal finite conjunctions over an independent atom family, with the naming field
  discharged by an explicit write-out emitter (`def:ec`) rather than assumed.
* `StrictSeparators` — the `StrictSeparatorPresentation` for `thm:strict` over Kleene's
  recursively inseparable pair, including `no_ce_null_prefix_family`, which proves that the
  simpler nested-prefix interface is unsatisfiable rather than merely inconvenient.

## The endpoints

* `Endpoints` — `thm:dus` and `thm:strict` made unconditional over the constructed `LIA`.
  `thm:dus` runs in two lanes: over `emptyBitDeductiveProcess`, where atom independence is
  discharged vacuously, and over `paperDP T`, whose stages are non-empty and where
  `paperIndependentBitAtoms` discharges it substantively.  `thm:strict` has only the first
  lane: its single endpoint
  `lic_strict_domination_universalSemimeasure_unconditional` is stated over
  `liaHistory emptyBitDeductiveProcess`, and `LogicalInduction/README.md`'s non-vacuity
  caveat on the constantly-empty process applies to it in full.
-/
