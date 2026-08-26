# Fork provenance for the `complexitylib` dependency

The two patches here are the entire delta between upstream `complexitylib` and the pinned
compatibility fork FAF depends on. They are kept in the repository so the dependency can be
audited — and reconstructed — without cloning the fork.

| field | value |
| --- | --- |
| upstream base | `SamuelSchlesinger/complexitylib` @ `b673821` (branch `dev`) |
| fork | <https://github.com/A-M-Berns/complexitylib> |
| branch | `faf/v4.31` |
| pinned head | `a16b3f568dab7183b205368bb950856a44db583c` |
| licence | Apache-2.0, same as this repository |

| file | fork commit | what it is |
| --- | --- | --- |
| `0002-lean431-port-fixes.patch` | `badc970` | the mechanical Lean 4.31 / Mathlib v4.31.0 port — 36 changed lines across 6 files |
| `0001-utm-function-output.patch` | `a16b3f5` | `utmTM_simulates_computer`: universal simulation for arbitrary function output, 69 added lines in `UTM/Universal.lean` |

Neither patch alters a mathematical statement, definition or proof of upstream's; the first
is tactic repair against 4.31's elaborator and simp set, the second is purely additive. Both
are upstreamable, and the fork is meant to retire into a plain upstream `require` once
upstream reaches this toolchain.

**The executable bridge is no longer here.** It is production code at
`LogicalInduction/Construction/Machine/DescExec.lean`, compiled by the `MachineExec` default
target. This directory holds only third-party provenance.

## What FAF actually imports

`DescExec` imports `Complexitylib.Models.TuringMachine.UTM.Internal.Interp` and nothing else
from the fork. That closure is 5 files / ~2,160 lines:

```
906  Complexitylib.Models.TuringMachine
509  Complexitylib.Models.TuringMachine.UTM.Internal.Desc
264  Complexitylib.Models.TuringMachine.UTM.Encoding
264  Complexitylib.Models.TuringMachine.UTM.Internal.Interp
217  Complexitylib.Mathlib.NatBits
```

Only `NatBits` (2 lines) is touched by the port, so 34 of the 36 ported lines and all of
`utmTM_simulates_computer` sit *outside* FAF's trust path. `DescExec` is the only module in
this repository permitted to name a `Complexity.*` declaration — the same discipline
`PFR/` ↔ `ShannonInformation.API` follows.

## Reproducing the fork from upstream

```sh
git clone https://github.com/SamuelSchlesinger/complexitylib && cd complexitylib
git checkout -b faf/v4.31 b673821
echo 'leanprover/lean4:v4.31.0' > lean-toolchain
# lakefile.toml + lake-manifest.json: repoint mathlib to v4.31.0 (fabf563a)
patch -p1 < 0002-lean431-port-fixes.patch
patch -p1 < 0001-utm-function-output.patch
lake build Complexitylib.Models.TuringMachine.UTM.Universal Complexitylib.Classes.P.Defs
```

## Axiom report

`utmTM_simulates_computer` depends on exactly `[propext, Classical.choice, Quot.sound]` —
the same three as upstream's `utmTM_simulates_decider` and `utmTM_universal`. No `sorry`, no
new axiom. The FAF-side endpoints are checked in `DescExec.lean`'s own build.
