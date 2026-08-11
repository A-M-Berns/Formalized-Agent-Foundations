/-
# Surface probe — developer tool for regenerating the `AxiomAudit.lean` Tier-2 block

Not a build target (absent from `lakefile.lean`); run manually with `lake env lean
SurfaceProbe.lean`. Two commands:

* `#surface_types <endpoints…>` — prints the structures reachable from the *types* of the
  given endpoints, transitively through structure fields. This is the Tier-2 boundary set:
  structures whose fields are hypotheses of a Tier-1 endpoint. Seed it with the full
  `#assert_axioms_clean` list from `AxiomAudit.lean`. Results are filtered to the
  formalization namespaces (`LogicalInduction`, `CartesianFrames`), so it serves both
  inventories in `AxiomAudit.lean`.
* `#dump_fields <structs…>` — prints each structure's field-name set, in the exact shape the
  `#assert_fields` assertions expect.

When the surface changes deliberately, rerun both and update `AxiomAudit.lean` and the
`Paper node:` annotations, then `scripts/check-paper-nodes.sh`.
-/
import Lean.Util.CollectAxioms
import LogicalInduction.Properties
import LogicalInduction.Construction
import CartesianFrames.Examples

open Lean Elab Command Meta in
/-- Structures appearing in the types of `ids`, closed transitively through the field
types of structures already found. -/
elab "#surface_types " ids:ident+ : command => do
  let env0 ← getEnv
  let mut hits : Std.HashSet Name := {}
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let info ← getConstInfo name
    for c in info.type.getUsedConstants do
      if Lean.isStructure env0 c then hits := hits.insert c
  let mut frontier := hits.toList
  while !frontier.isEmpty do
    let s := frontier.head!
    frontier := frontier.tail!
    for f in Lean.getStructureFields env0 s do
      if let some fi := Lean.getFieldInfo? env0 s f then
        let info ← getConstInfo fi.projFn
        for c in info.type.getUsedConstants do
          if Lean.isStructure env0 c && !hits.contains c then
            hits := hits.insert c; frontier := c :: frontier
  let libs : List Name := [`LogicalInduction, `CartesianFrames]
  let out := (hits.toList.filterMap fun h =>
    if libs.any (·.isPrefixOf h) then some h.toString else none).toArray.qsort (· < ·)
  logInfo m!"STRUCTS-IN-ENDPOINT-TYPES:\n{String.intercalate "\n" out.toList}"

open Lean Elab Command in
/-- Each structure's field-name set, one per line, as `Name :: f1 f2 …`. -/
elab "#dump_fields " ids:ident+ : command => do
  let env ← getEnv
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let fs := (Lean.getStructureFields env n).map Name.toString
    logInfo m!"{n} :: {String.intercalate " " fs.toList}"

namespace LogicalInduction
open ConditioningCompile FeedbackTruth FeedbackEmission PrefixPatchCompile

-- Seed lists intentionally omitted from version control noise; paste the current
-- `#assert_axioms_clean` names below when regenerating. Example:
--   #surface_types exists_logical_inductor lic_self_trust …
--   #dump_fields Trader IsLogicalInductor …

end LogicalInduction

namespace CartesianFrames

-- Same, seeded from the CF-INVENTORY block. Example:
--   #surface_types Frame.biextEquiv_iff_homotopyEquiv Frame.collapse …
--   #dump_fields Frame Frame.Hom Frame.Biextensional

end CartesianFrames
