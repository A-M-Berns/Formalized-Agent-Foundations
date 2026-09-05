# Palomar registry entries

Scaffolding for submitting this repository's results to the
[Palomar registry](https://palomar-registry.org), a Lean FRO / ICARM registry of
Lean-verified results.

**Nothing here is written yet.** Every `Challenge.lean` and `Solution.lean` below is a
stub carrying a module docstring and no statement, and every `comparator.json` names a
placeholder in `theorem_names`. The one exception is `SmokeTest/`, which is a real,
working triple that exists only to validate the harness and must never be submitted.

## What a Palomar entry is

One registry entry is **one Comparator configuration**: a `Challenge.lean` /
`Solution.lean` / `comparator.json` triple. The challenge states the compared results
with `sorry`; the solution discharges them.

One repository at one commit can carry many entries, and this is explicitly how Palomar
expects it to work — CONTRIBUTING.md §2:

> One submission and one Palomar entry correspond to exactly one Comparator
> configuration. If a repository/commit contains twelve different configuration files,
> submit it twelve times with twelve different paths. Those become twelve entries
> sharing a repository and commit but retaining distinct path and declaration
> information.

So each entry below is submitted separately, naming its own `comparator.json` path. Per
§6.2 the metadata path is selected the same way — it "may point anywhere inside the
repository, but its basename must be exactly `formalization.yaml`" — which is why each
entry carries its own rather than the repository sharing one at the root.

The rule that shapes everything else: **a challenge's transitive import closure may
contain only Lean core, Mathlib, Tau Ceti and CSLib.** It may not reach a module of
this repository, nor `Foundation`, nor `Complexitylib`. A challenge must therefore
restate its subject matter over Mathlib alone — it cannot import `FiniteFactoredSets.API`
and quote a theorem from it. The solution has no such restriction and is where
`import FiniteFactoredSets.API` belongs.

Permitted axioms are exactly `propext`, `Quot.sound`, `Classical.choice` — which is the
same bar `AxiomAudit.lean` already holds the whole repository to.

## Layout and the module-name scheme

```
Palomar/<Entry>/
  Challenge.lean       module Palomar.<Entry>.Challenge
  Solution.lean        module Palomar.<Entry>.Solution
  comparator.json      the four required keys
  formalization.yaml   v0.4 metadata (absent for SmokeTest, which is never submitted)
```

Entry directories are `CamelCase` and are exactly the last-but-one component of the
Lean module name. Three constraints force this, and it is worth recording why, because
the obvious alternative — `palomar/finite-factored-sets/` — fails all three:

1. **Lean module components cannot contain hyphens.** They match
   `[A-Za-z_][A-Za-z0-9_']*`, so `finite-factored-sets` can never be a module name
   component, and Palomar requires `challenge_module` to be a dotted Lean name.
2. **Bare `Challenge` / `Solution` module names would collide.** With seven entries,
   seven files would all claim the module name `Challenge`. Palomar's own rule is that
   "Lake selects the first regular, non-symlink source file matching each module inside
   the project" — first-wins across the whole project. `import Challenge` inside one
   entry's solution could silently resolve to a *different* entry's challenge. The
   `Palomar.<Entry>.` prefix makes every module name unique.
3. **macOS filesystems are case-insensitive by default.** `palomar/` and `Palomar/`
   are the same directory, so a lowercase `palomar/` holding artifacts could not
   coexist with a `Palomar/` holding the Lean module tree. There is one tree.

The `Palomar` prefix is not decoration: without it the entry namespace would be
`FiniteFactoredSets.Challenge`, which puts a second source root under the existing
`FiniteFactoredSets.*` namespace and reintroduces exactly the first-wins hazard from
point 2.

Every `lean_lib` in `lakefile.lean` uses `srcDir := "."`, so the module name is just the
repository-relative path — `Palomar/FiniteFactoredSets/Challenge.lean` is
`Palomar.FiniteFactoredSets.Challenge`, with no mapping to remember.

## Building

The `Palomar` library is declared in `lakefile.lean` but is deliberately **not** a
`@[default_target]`. These are stubs; a stub that broke `lake build` would turn every
unrelated CI run red for no reason. Build them explicitly:

```sh
lake build Palomar                                    # every entry
lake build Palomar.SmokeTest.Challenge Palomar.SmokeTest.Solution   # one entry
```

Comparator reads `.olean` files, so the two modules of an entry must be built before it
is run.

## Entries

| Directory | Paper | Source | Library it draws on | State |
|---|---|---|---|---|
| `CartesianFrames/` | Cartesian Frames | arXiv:2109.10996 | `CartesianFrames` | **Written** — Theorem 24, passes Comparator |
| `FiniteFactoredSets/` | Temporal Inference with Finite Factored Sets | arXiv:2109.11513 | `FiniteFactoredSets` | stub |
| `FactoredSpaces/` | Factored Space Models | arXiv:2412.02579 | `FactoredSpaces` | stub |
| `Condensation/` | Condensation: A Theory of Concepts | OpenReview `HwKFJ3odui` | `Condensation` | stub |
| `ModalAgents/` | Robust Cooperation in the Prisoner's Dilemma | arXiv:1401.5577 | `ModalAgents` | stub |
| `LogicalInductionFuel/` | Logical Induction | arXiv:1609.03543 | `LogicalInduction` | stub |
| `LogicalInductionMachine/` | Logical Induction | arXiv:1609.03543 | `MachineExec` | placeholder, deferred |
| `SmokeTest/` | — harness check, never submitted — | — | Mathlib only | harness |

`LogicalInductionMachine/` is a **placeholder**: the entry is deferred, and its
scaffolding exists so the decision to defer is visible rather than implicit.

Entry ordering, which commit to register, the public abstracts, and the classification
codes are all open questions for Anson; the `formalization.yaml` files mark them
`TODO(Anson)` and `PROPOSED` rather than deciding them.

## The wiring gate

`scripts/check_palomar_wiring.py` validates every entry: the four files exist, the
`comparator.json` parses with exactly the allowed keys and the exact permitted-axiom
set, the module names match the files on disk, `Challenge.lean` is inside Palomar's
100 KiB / 1000-line hard cap (warning above 32 KiB / 300 lines), and — the check that
matters — the challenge's transitive import closure reaches nothing outside Lean core,
Mathlib, Tau Ceti and CSLib.

```sh
python3 scripts/check_palomar_wiring.py
```

Stubs pass. It is **not** yet wired into any CI gate; see the scaffolding report for
where it would slot in.

## Comparator smoke test

`SmokeTest/` states one small Mathlib-only lemma (Gauss's sum) as a `sorry` and proves
it. Running Comparator against it confirms the harness works, so that the first real
entry debugs mathematics rather than plumbing.

### Installing Comparator

Pinned to `v4.31.0`, matching this repository's `lean-toolchain` — `lean4export` must be
version-compatible with the Lean that produced the oleans, so the tags must agree.

```sh
git clone --depth 1 --branch v4.31.0 \
  https://github.com/leanprover/comparator.git ~/.local/share/palomar/comparator
cd ~/.local/share/palomar/comparator
lake build lean4export comparator
```

### Running it

Comparator sandboxes the kernel replay with [`landrun`](https://github.com/Zouuup/landrun),
which is Linux-only (it uses Landlock LSM, and the documented invocation wraps it in
`systemd-run`). **On macOS there is no landrun**, so use the `fake-landrun.sh` shim from
Comparator's own test suite — this is exactly what Comparator's `runtests.lean` does.
The sandbox is a containment measure for running untrusted submissions; skipping it
locally does not weaken the mathematical check, but a registry-side run does sandbox.

From the repository root:

```sh
lake build Palomar.SmokeTest.Challenge Palomar.SmokeTest.Solution

COMPARATOR=~/.local/share/palomar/comparator
COMPARATOR_LANDRUN=$COMPARATOR/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=$COMPARATOR/.lake/packages/lean4export/.lake/build/bin/lean4export \
  lake env $COMPARATOR/.lake/build/bin/comparator Palomar/SmokeTest/comparator.json
```

The same invocation runs a real entry — swap the config path.

What a pass establishes, in Comparator's own terms: every name in `theorem_names`
proves the same statement as the challenge, uses no axiom outside `permitted_axioms`,
and is accepted by the Lean kernel.

### `enable_nanoda`

Comparator v4.31.0 parses `enable_nanoda` as a **non-optional** `Bool` — omitting it
fails before any mathematics is checked, with
`uncaught exception: Comparator.Config.enable_nanoda: Bool expected`. Every config in
Comparator's own test suite sets it.

Palomar accepts the key but overrides it. CONTRIBUTING.md §2.3: it "is accepted for
Comparator compatibility but is intentionally non-authoritative. Its submitted value is
ignored, and the field may be absent. Palomar always writes a separate protected
configuration with NanoDa enabled." So setting it is safe and omitting it is safe — the
only thing that cares is a local Comparator run.

So any config meant to be *run* sets `"enable_nanoda": false` — `SmokeTest/` and
`CartesianFrames/` both do. The remaining stubs carry only the four required keys; add
the field when you write one, or a local run will fail before it type-checks anything.
`scripts/check_palomar_wiring.py` permits the key and does not require it.

### Verified transcript

Run on 2026-08-28 against Comparator `v4.31.0` (`fd2e25de`), Lean `v4.31.0`:

| Case | Result |
|---|---|
| Correct solution | `Lean default kernel accepts the solution` / `Your solution is okay!` — exit 0 |
| Solution proves a different statement | `uncaught exception: Challenge and solution theorem statement do not match: 'palomar_smoke_gauss'` — exit 1 |
| Solution left `sorry` | `uncaught exception: Illegal axiom detected: 'sorryAx'` — exit 1 |

Both failure modes are caught, so the harness is trustworthy for the first real entry.
