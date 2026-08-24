# Stage-3 spike artifacts (not built)

Nothing in this directory is part of any Lake target. `lean_lib LogicalInduction` declares
no `globs`, so it builds `LogicalInduction.lean` and its import closure only; these files
are not in it. They cannot compile inside FAF today because they `import Complexitylib`,
and the compatibility fork is not yet wired in as a dependency (see
`../complexitylib-adoption.md` §5, §11).

They are recorded here because they *were* compiled — against a ported complexitylib at
Lean 4.31 / Mathlib v4.31.0 — and the adoption plan rests on what they establish.

| file | what it is | status |
| --- | --- | --- |
| `0001-utm-function-output.patch` | `Complexity.TM.UTMBody.utmTM_simulates_computer`, the function-output universal theorem, as a diff against upstream `UTM/Universal.lean` | compiles; belongs upstream / in the fork |
| `0002-lean431-port-fixes.patch` | the 4.30 → 4.31 compatibility fixes needed to build `UTM.Universal` and `Classes.P.Defs` — 36 changed lines across 6 files | compiles; belongs in the fork |
| `DescExec.lean` | FAF-owned executable coding of described machines, with the simulation and `Primrec` theorems | compiles; eventual home `LogicalInduction/Construction/Machine/DescExec.lean` |

## Reproducing

```sh
git clone --branch dev https://github.com/SamuelSchlesinger/complexitylib
cd complexitylib
git checkout b673821
echo 'leanprover/lean4:v4.31.0' > lean-toolchain
# repoint lakefile.toml's mathlib require at a local Mathlib v4.31.0 checkout —
# FAF's own .lake/packages/mathlib works and avoids a second 6 GB build
patch -p0 < 0002-lean431-port-fixes.patch
patch -p0 < 0001-utm-function-output.patch
lake build Complexitylib.Models.TuringMachine.UTM.Universal Complexitylib.Classes.P.Defs
cp DescExec.lean . && lake env lean DescExec.lean
```

## Axiom report

Every endpoint below was checked with `#print axioms`; all depend on exactly
`[propext, Classical.choice, Quot.sound]` — the same three as complexitylib's existing
decider endpoints. No `sorry`, no new axiom.

```
Complexity.TM.UTMBody.utmTM_simulates_computer
LogicalInduction.MachineExec.codedStep_eq
LogicalInduction.MachineExec.runCoded_eq
LogicalInduction.MachineExec.decode_initCoded
LogicalInduction.MachineExec.evalCoded_reachesIn
LogicalInduction.MachineExec.primrec_codedStep
LogicalInduction.MachineExec.primrec_runCoded
LogicalInduction.MachineExec.primrec_evalCoded
LogicalInduction.MachineExec.primrec_lookup
```
