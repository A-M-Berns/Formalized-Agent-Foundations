import LogicalInduction.Construction.Knowledge.Syntax
import LogicalInduction.Construction.Knowledge.SubstEmission
import LogicalInduction.Construction.Knowledge.DayMachine
import LogicalInduction.Construction.Knowledge.SourceNumbering
import LogicalInduction.Construction.Knowledge.SourceRecognizer
import LogicalInduction.Construction.Knowledge.SourceWindow
import LogicalInduction.Construction.Knowledge.Endpoints

/-!
# Computational knowledge (`LogicalInduction.Construction.Knowledge`)

The §4.9–4.10 lane: `thm:pac` (tex:1869), `thm:pazfc` (tex:1881), `thm:incons` (tex:1893),
`thm:halts` (tex:1923), `thm:loops` (tex:1935) and `thm:dontwait` (tex:1946), rendered over
the single paper-facing market `liaHistory (paperDP T)` at the paper's own §2
representability premise (tex:600-606).

`Properties/MetaLearning.lean` states five of them over an arbitrary inductor — `thm:pac`,
`thm:incons`, `thm:halts`, `thm:loops` and `thm:dontwait`.  `thm:pazfc` has no
arbitrary-inductor form: that module supplies only its representation interfaces, and the
node's one endpoint is `lic_belief_stronger_theory_consistency_unconditional` in
`Construction/Knowledge/Endpoints.lean`.  What this
directory adds is the construction that discharges their interfaces: a claim syntax whose
day-`n` sentence genuinely names the day-`n` machine and its input, the `def:ec` write-out
certificate for that syntax, and — for `thm:incons` — the decoder that reads a machine's
written axioms back as the theory it presents (`dd:machinetheory`).

## The claim syntax and its certificate

* `Syntax` — the bridge between the propositional public language and the first-order
  arithmetic the representation theorem is stated in.  It fixes the universal schemas
  (`universalHaltingSchema`, `universalBoundedHaltingSchema`), their compact Gödel names,
  the narrow background-theory translation premise `ComputationTheoryPresentation`, and the
  horizon interface `ComputableHorizon`, inhabited at every computable step budget by
  `ComputableHorizon.of`.
* `SubstEmission` — the `def:ec` (tex:753) certificate for those families: writing a closed
  term into a fixed arithmetic schema is token-metered emittable for an arbitrary and
  Lean-opaque schema (`polyArithmeticFormulaSeq_subst_arg`,
  `polyArithmeticFormulaSeq_schemaArgBody`, with the sentence-class corollaries the
  endpoints consume).  The obligation is discharged, not assumed.

## Reading a machine as a theory

The `thm:incons` lane needs a day's axioms *as written*, so that the claim is about the
theory the machine presents rather than about its emitted stream.

* `DayMachine` — machines carrying the day in their own source (`Nat.Partrec.Code.curry`),
  the reusable day-varying witness for `DigitMachineCodes`, with `dayMachine_sourceNat_ne`
  separating the days.
* `SourceNumbering` — the inverse of the naming map `ArithSource.sourceNat`, composed with
  the structured grammar of `Framework/Criterion.lean` to send a source's *name* to the
  Gödel code of the negation of the formula it compiles to.
* `SourceRecognizer` — the primitive-recursive gate `sourceRun`, sound and complete for the
  token runs that are genuinely written sources, which the permissive numeric parser is not.
* `SourceWindow` — the splice of a day's written axioms into one written conjunction, the
  per-entry admissibility gate that makes the splice a statement about the presented theory,
  and the code `negWindowCode` the represented predicate is instantiated at.

## The endpoints

* `Endpoints` — the six paper-facing theorems over `liaHistory (paperDP T)`:
  `lic_belief_finitistic_consistency_unconditional` (`thm:pac`),
  `lic_belief_stronger_theory_consistency_unconditional` (`thm:pazfc`),
  `lic_does_not_anticipate_halting_ofComputation` and its `_unconditional` form
  (`thm:dontwait`), `lia_learns_halting_patterns_unconditional` (`thm:halts`),
  `lic_learns_provable_nonhalting_patterns_unconditional` (`thm:loops`) and
  `lic_disbelief_inconsistent_theories_unconditional` (`thm:incons`), together with the
  applied witnesses that keep each lane non-vacuous.

The design shared by all of them — a *universal* represented object with the day's data in
the argument term rather than in the schema, so that two sequences with the same extension
but different programs give literally different sentences — is stated once in `Endpoints`
and cited, not restated, at each theorem.
-/
