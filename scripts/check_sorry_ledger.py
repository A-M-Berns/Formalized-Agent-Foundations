#!/usr/bin/env python3
"""Check that every `sorryAx`-dependent Condensation declaration is on the ledger.

`AxiomAudit.lean`'s `CONDENSATION-INVENTORY` block is machine-checked by
`#assert_axioms_clean`: a listed endpoint that acquires a `sorry` fails the Lean build.
Its companion `CONDENSATION-PENDING` block is *pure Lean comment* — it compiles to
nothing and asserts nothing — and names the endpoints whose statements are final but
whose proofs are still `sorry`.  `scripts/check-condensation-nodes.py` fences that block
from the *annotation* side (no name in both blocks, no pending entry naming a
non-annotated declaration, no malformed line, empty once the paper is `completed`).

Nothing, until this script, fenced it from the *Lean* side.  A new `sorry` — in a fresh
lemma, in an un-annotated helper, or reintroduced into a proof that used to be finished —
was invisible to every gate in the repository, because the only mechanized `sorry` check
is `#assert_axioms_clean` and its reach is exactly the names someone remembered to type
into it.  This script closes that: it asks Lean itself which Condensation declarations
depend on `sorryAx`, and fails unless every one of them is named in the pending block.

What it does, once per run:

1. Writes a scratch Lean file (outside the repository — see `--scratch-dir`) that does
   `import Condensation` and, in a single `run_cmd`, walks `env.header.moduleData` for
   every imported module whose name has `Condensation` as its root component, takes that
   module's `constNames` and `extraConstNames`, and runs `Lean.collectAxioms` on each.
   It prints one `DECL` line per constant (module, raw name, de-mangled user name,
   private flag, `sorryAx` flag) and, redundantly but greppably, one `SORRY_DEP` line
   per constant that depends on `sorryAx`.
2. Runs that file with a **single** `lake env lean` invocation — one elaboration per gate
   run, not one per declaration.  Measured wall time on the reference machine: ~4.5s
   against warm `.lake/build` oleans.  (`lake build` is never invoked; this script only
   *reads* whatever oleans are already built, so a stale `.lake/build` yields a stale
   answer.  Run it after the build, in the same CI job.)
3. Filters Lean-internal and compiler-generated names (below).
4. Reads the ledger with `paper_nodes.read_pending`, using **both** its sections, and
   reports the two directions of drift.

## Which module counts as "the Condensation library"

The defining module, not the name.  A constant is in scope iff `env.getModuleIdxFor?`
puts it in a module whose *root component* is `Condensation` — i.e. `Condensation` itself
or `Condensation.*`, which is exactly `lakefile.lean`'s
`globs := #[.andSubmodules `Condensation]`.  Namespaces are deliberately not consulted:
a `Condensation.Quantitative` lemma stated in the root namespace is in scope, and a
`Condensation.*`-namespaced declaration contributed by some other library would not be.
The scan additionally sweeps `env.constants` the other way round, through
`getModuleIdxFor?`, and folds in (reporting as `XMISS`) anything the `moduleData` walk
missed, so the two enumerations cannot disagree silently.

## What is filtered, and why

Over-reporting is cheap here — a spurious name costs one line of ledger — and
under-reporting is the failure this gate exists to prevent, so the filter is deliberately
narrow and every drop is auditable with `--all`.

**Private declarations are de-mangled, never dropped.**  `private lemma foo` in module
`Condensation.Perfect` is the constant `_private.Condensation.Perfect.0.Condensation.foo`.
That is a real declaration with a real `sorry` in it, and dropping it would be exactly the
hole this gate closes.  The scan runs `Lean.privateToUserName?` and reports the
user-facing name (`Condensation.foo`), flagged `private` in `--all` output; the ledger
should name it in that user-facing spelling.  Because de-mangling happens first, no
`_private` component survives to meet the underscore rule below.

Dropped, matched against **whole name components** of the de-mangled name (so a
declaration called `Condensation.foo_eq_2` or `Condensation.entropy_ind_le` is *not*
touched — only a component that is exactly the generated form):

* equation and unfolding lemmas — `eq_<n>`, `eq_<n>_<m>`, `eq_def`, `_eq_<n>`,
  `_sunfold`, `_unfold`, `_definition`;
* elaborator/compiler auxiliaries — `_proof_<n>`, `proof_<n>`, `match_<n>`,
  `_match_<n>`, `_spec_<n>`, `_lambda_<n>`, `_closed_<n>`, `_example_<n>`,
  `_cstage1`, `_cstage2`, `_impl`, `_redArg`, `_unsafe_rec`, `_regBuiltin`;
* inductive/structure boilerplate — `rec`, `recOn`, `casesOn`, `brecOn`,
  `binductionOn`, `below`, `ibelow`, `ind`, `induct`, `noConfusion*`, `inj`, `injEq`,
  `sizeOf_spec`, `sizeOf_inst`, `_sizeOf_<n>`, `toCtorIdx`, `ofNat_toCtorIdx`,
  `fromCtorIdx`;
* and, as a catch-all, any remaining component beginning with `_`, which in Lean 4 is
  the convention for a name the user did not write.

A generated name never carries a `sorry` its parent does not carry — `Foo.eq_1` is
`sorry`-dependent exactly when `Foo` is — so dropping them removes noise, not signal.
This is checked, not assumed: a dropped name whose *longest kept ancestor* is itself
absent from the kept `sorryAx` set is reported as an ORPHAN violation rather than
silently discarded, so a filter that swallows a real declaration fails the gate.

## The two directions of drift, and why both are violations

*Unlisted*: a declaration depends on `sorryAx` and is named in neither ledger section.
That is the primary failure — an unrecorded `sorry`.

*Stale*: a name is on the ledger but no longer depends on `sorryAx`.  This is likewise a
**violation**, not a note.  A stale excuse is precisely the drift the ledger exists to
catch: the pending block is a declaration of intent whose whole value is that its length
is the honest count of unfinished proofs, and an entry that outlives its `sorry` inflates
that count and, worse, leaves an endpoint sitting outside `#assert_axioms_clean` where
nothing checks it.  "M2 proved this endpoint" means moving the name from the pending
block into the inventory block in the same commit as the proof; a failure here is what
makes the second half of that pair non-optional.

Two interactions worth knowing:

* `scripts/check-condensation-nodes.py` already fails on a pending name that is not an
  *annotated* declaration.  For a paper-facing endpoint that was just proved, both gates
  therefore fire, and both are cured by the same edit (move the name into the inventory
  block).  The messages differ usefully: that checker says the entry names no annotation,
  this one says the entry names nothing `sorry`-dependent.
* the pending block's *consumers* section holds un-annotated declarations, which that
  checker does not police at all; for those, this gate is the only one watching, in both
  directions.

A stale entry naming a constant that does not exist in the Condensation library at all
(renamed, retired) is reported separately from one naming a constant that exists and is
now clean, because the repairs differ.  Both are violations.

Exit status: 0 clean, 1 ledger violations, 2 infrastructure failure (Lean did not run,
produced no parseable report, or `AxiomAudit.lean` has no ledger block).

Run from the repository root.
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_nodes  # noqa: E402

AUDIT = Path("AxiomAudit.lean")
PENDING_BLOCK = "CONDENSATION-PENDING"
LIB_ROOT = "Condensation"

# --------------------------------------------------------------------------- the scan

# One `run_cmd`, one elaboration.  `{root}` is the library's root module component.
#
# `env.header.moduleData[i]` is the loaded olean data for the module at index `i` of
# `env.header.moduleNames`; `constNames` is every constant the module defines and
# `extraConstNames` the code-generator auxiliaries it also owns.  `Lean.collectAxioms`
# (`Lean/Util/CollectAxioms.lean`, `[Monad m] [MonadEnv m] : Name → m (Array Name)`)
# answers from the olean's pre-computed axiom extension for imported declarations, so
# this walk does not re-traverse any proof term.
LEAN_SCAN = r'''import {root}
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  IO.println "SORRY_GATE_BEGIN"
  IO.println s!"MODULE_COUNT\t{{mods.size}}\t{{data.size}}"
  let mut targets : Array (Name × Name) := #[]
  let mut seen : NameSet := {{}}
  for i in [0 : mods.size] do
    let m := mods[i]!
    if m.getRoot == `{root} then
      let d := data[i]!
      IO.println s!"MODULE\t{{m}}\t{{d.constNames.size}}\t{{d.extraConstNames.size}}"
      for c in d.constNames do
        unless seen.contains c do
          seen := seen.insert c
          targets := targets.push (c, m)
      for c in d.extraConstNames do
        unless seen.contains c do
          seen := seen.insert c
          targets := targets.push (c, m)
  -- Completeness cross-check, taken the other way round: anything the environment
  -- attributes to a `{root}` module but the `moduleData` walk missed is folded in and
  -- announced, so the two enumerations cannot disagree in silence.
  for (c, _) in env.constants.map₁ do
    match env.getModuleIdxFor? c with
    | some idx =>
      let m := mods[idx.toNat]!
      if m.getRoot == `{root} && !seen.contains c then
        seen := seen.insert c
        targets := targets.push (c, m)
        IO.println s!"XMISS\t{{m}}\t{{c}}"
    | none => pure ()
  IO.println s!"SCANNED\t{{targets.size}}"
  let mut count := 0
  for (c, m) in targets do
    let axs ← Lean.collectAxioms c
    let isSorry := axs.contains ``sorryAx
    let user? := Lean.privateToUserName? c
    let userStr := match user? with
      | some u => toString u
      | none => toString c
    let priv := if user?.isSome then "1" else "0"
    let flag := if isSorry then "1" else "0"
    IO.println s!"DECL\t{{m}}\t{{c}}\t{{userStr}}\t{{priv}}\t{{flag}}"
    if isSorry then
      count := count + 1
      IO.println s!"SORRY_DEP: {{userStr}}\t{{m}}\t{{c}}\t{{priv}}"
  IO.println s!"SORRY_COUNT\t{{count}}"
  IO.println "SORRY_GATE_END"
'''

# --------------------------------------------------------------------------- the filter

GENERATED_COMPONENTS = frozenset({
    "rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow",
    "ind", "induct", "inj", "injEq", "sizeOf_spec", "sizeOf_inst",
    "toCtorIdx", "ofNat_toCtorIdx", "fromCtorIdx",
    "eq_def", "_sunfold", "_unfold", "_definition",
    "_cstage1", "_cstage2", "_impl", "_redArg", "_unsafe_rec", "_regBuiltin",
})

GENERATED_PATTERNS = (
    ("noConfusion", re.compile(r"^noConfusion")),
    ("proof_<n>", re.compile(r"^_?proof_\d+$")),
    ("match_<n>", re.compile(r"^_?match_\d+$")),
    ("eq_<n>", re.compile(r"^_?eq_\d+(_\d+)*$")),
    ("spec_<n>", re.compile(r"^_?spec_\d+$")),
    ("lambda_<n>", re.compile(r"^_?lambda_\d+$")),
    ("closed_<n>", re.compile(r"^_?closed_\d+$")),
    ("example_<n>", re.compile(r"^_?example_\d+$")),
    ("sizeOf_<n>", re.compile(r"^_?sizeOf_\d+$")),
    ("elim_<n>", re.compile(r"^_?elim_\d+$")),
)


def filter_reason(user_name):
    """Why this de-mangled name is compiler-generated, or `None` to keep it.

    Matching is per whole name component: `Condensation.foo_eq_2` keeps (its last
    component is `foo_eq_2`, not `eq_2`), `Condensation.foo.eq_2` drops.
    """
    for component in user_name.split("."):
        if component in GENERATED_COMPONENTS:
            return f"generated component {component!r}"
        for label, pattern in GENERATED_PATTERNS:
            if pattern.match(component):
                return f"generated component {component!r} ({label})"
    for component in user_name.split("."):
        if component.startswith("_"):
            return f"underscore-prefixed component {component!r}"
    return None


def longest_kept_ancestor(user_name, kept):
    """The longest strict prefix of `user_name` that survived the filter, if any.

    Used by the orphan check: a generated name's `sorry` always comes from the
    declaration it was generated for, so a dropped `sorryAx`-dependent name must have a
    kept `sorryAx`-dependent ancestor.  One that does not is a filter bug, not noise.
    """
    parts = user_name.split(".")
    for cut in range(len(parts) - 1, 0, -1):
        candidate = ".".join(parts[:cut])
        if candidate in kept:
            return candidate
    return None


# --------------------------------------------------------------------------- running Lean


class ScanFailure(Exception):
    """The scan could not be run or produced no parseable report."""


class Decl:
    __slots__ = ("module", "raw", "user", "private_", "sorry_")

    def __init__(self, module, raw, user, private_, sorry_):
        self.module = module
        self.raw = raw
        self.user = user
        self.private_ = private_
        self.sorry_ = sorry_


def run_scan(scratch_dir, keep_scratch, lean_root):
    """Elaborate the scan once.  Returns `(decls, notes, seconds)`."""
    workdir = scratch_dir or tempfile.mkdtemp(prefix="sorry-ledger-")
    Path(workdir).mkdir(parents=True, exist_ok=True)
    scratch = Path(workdir) / "sorry_ledger_scan.lean"
    scratch.write_text(LEAN_SCAN.format(root=lean_root), encoding="utf-8")
    started = time.monotonic()
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(scratch)],
            capture_output=True, text=True, check=False,
        )
    except FileNotFoundError:
        raise ScanFailure("`lake` not found on PATH — run this from the repository root "
                          "in the project's toolchain environment")
    finally:
        elapsed = time.monotonic() - started
        if not keep_scratch and scratch_dir is None:
            shutil.rmtree(workdir, ignore_errors=True)

    if proc.returncode != 0 or "SORRY_GATE_END" not in proc.stdout:
        sys.stdout.write(proc.stdout)
        sys.stderr.write(proc.stderr)
        raise ScanFailure(
            f"the scan did not complete (lake env lean exit {proc.returncode}).  "
            f"This gate only *reads* the oleans in `.lake/build`; build the {lean_root} "
            "target first, in the same job, and note that a build running concurrently "
            "in the same checkout can make an olean momentarily absent."
        )

    decls, notes = [], []
    for line in proc.stdout.splitlines():
        if line.startswith("DECL\t"):
            _, module, raw, user, private_, sorry_ = line.split("\t")
            decls.append(Decl(module, raw, user, private_ == "1", sorry_ == "1"))
        elif line.startswith(("MODULE\t", "MODULE_COUNT\t", "SCANNED\t",
                              "SORRY_COUNT\t", "XMISS\t")):
            notes.append(line)
    return decls, notes, elapsed


# --------------------------------------------------------------------------- the gate


def main():
    parser = argparse.ArgumentParser(
        description="Fail unless every sorryAx-dependent Condensation declaration is "
                    "named in AxiomAudit.lean's CONDENSATION-PENDING ledger.")
    parser.add_argument("--all", "--verbose", dest="verbose", action="store_true",
                        help="print the unfiltered scan and every filter decision, so "
                             "the filter itself can be audited")
    parser.add_argument("--print-ledger", action="store_true",
                        help="print a ready-to-paste pending block covering every "
                             "surviving sorryAx-dependent declaration")
    parser.add_argument("--scratch-dir", default=None,
                        help="where to write the scratch Lean file (default: a fresh "
                             "temporary directory, removed afterwards).  It must not be "
                             "inside a `lean_lib` source directory.")
    parser.add_argument("--keep-scratch", action="store_true",
                        help="do not delete the scratch Lean file")
    parser.add_argument("--audit", default=str(AUDIT),
                        help=f"path to the audit file (default: {AUDIT})")
    args = parser.parse_args()

    audit = Path(args.audit)
    if not audit.is_file():
        print(f"FAIL: {audit}: not found — run this script from the repository root")
        return 2

    try:
        decls, notes, elapsed = run_scan(args.scratch_dir, args.keep_scratch, LIB_ROOT)
    except ScanFailure as failure:
        print(f"FAIL: {failure}")
        return 2
    if not decls:
        print("FAIL: the scan reported no declarations at all — is the "
              f"`{LIB_ROOT}` target built?")
        return 2

    kept, dropped = [], []
    for decl in decls:
        reason = filter_reason(decl.user)
        (dropped if reason else kept).append((decl, reason))

    kept_names = {decl.user for decl, _ in kept}
    kept_sorry = {decl.user for decl, _ in kept if decl.sorry_}
    kept_sorry_by_name = {decl.user: decl for decl, _ in kept if decl.sorry_}
    all_names = {decl.user for decl in decls}

    print(f"condensation sorry ledger: scanned {len(decls)} declarations in "
          f"{elapsed:.1f}s ({len(kept)} user-facing, {len(dropped)} generated)")
    for note in notes:
        if note.startswith("XMISS\t"):
            print("  note: " + note.replace("\t", " "))

    if args.verbose:
        print("\n--- scan notes")
        for note in notes:
            print("  " + note.replace("\t", "  "))
        print("\n--- unfiltered sorryAx-dependent constants "
              f"({sum(1 for d in decls if d.sorry_)})")
        for decl in sorted(decls, key=lambda d: (d.module, d.user)):
            if decl.sorry_:
                mark = " [private]" if decl.private_ else ""
                reason = filter_reason(decl.user)
                verdict = f"DROPPED: {reason}" if reason else "kept"
                print(f"  {decl.user}{mark}\n      module: {decl.module}\n"
                      f"      raw:    {decl.raw}\n      {verdict}")
        print("\n--- every filter drop (whether sorry-dependent or not)")
        for decl, reason in sorted(dropped, key=lambda p: (p[0].module, p[0].user)):
            print(f"  {decl.user}  --  {reason}"
                  f"{'  [SORRY]' if decl.sorry_ else ''}")

    failures = []

    # A dropped name that is sorry-dependent must trace back to a kept sorry-dependent
    # declaration; otherwise the filter has swallowed something real.
    for decl, reason in dropped:
        if not decl.sorry_:
            continue
        if longest_kept_ancestor(decl.user, kept_sorry) is None:
            failures.append(
                f"{audit}: ORPHANED GENERATED DECLARATION: {decl.user!r} "
                f"(module {decl.module}) depends on `sorryAx` and was filtered out as "
                f"{reason}, but no surviving declaration it belongs to is itself "
                "sorry-dependent.  Either the filter in scripts/check_sorry_ledger.py "
                "is swallowing a real declaration, or this is a genuinely orphaned "
                "`sorry`; both need a human.")

    pending = paper_nodes.read_pending(audit, PENDING_BLOCK)
    if pending is None:
        print(f"FAIL: {audit}: no `-- {PENDING_BLOCK}-BEGIN/END` block — this gate has "
              "no ledger to check against")
        for name in sorted(kept_sorry):
            print(f"  unrecorded `sorry`: {name}")
        return 2

    failures.extend(pending.problems)
    entries = dict(pending.entries)
    consumers = dict(getattr(pending, "consumers", {}) or {})
    listed = set(entries) | set(consumers)

    for name in sorted(kept_sorry - listed):
        decl = kept_sorry_by_name[name]
        kind = " (private)" if decl.private_ else ""
        failures.append(
            f"{audit}: UNRECORDED SORRY: {name!r}{kind} (module {decl.module}) depends "
            f"on `sorryAx` but is named in neither section of the {PENDING_BLOCK} "
            "block.  Add it with a reason, or finish the proof.")

    for name in sorted(listed - kept_sorry):
        where = "consumers section" if name in consumers else "main section"
        reason = consumers.get(name) or entries.get(name)
        if name in all_names or name in kept_names:
            cure = ("move it into the CONDENSATION-INVENTORY block's "
                    "`#assert_axioms_clean`" if name in entries else
                    "drop the entry, and axiom-check it in the Condensation "
                    "consumer-surface `#assert_axioms_clean` if it is advertised there")
            failures.append(
                f"{audit}: STALE LEDGER ENTRY: {name!r} is staged in the "
                f"{PENDING_BLOCK} block's {where} ({reason}) but no longer depends on "
                f"`sorryAx`.  Its proof is finished: {cure}, in the same commit; the "
                "pending block's length is only honest if entries leave it.")
        else:
            failures.append(
                f"{audit}: STALE LEDGER ENTRY: {name!r} is staged in the "
                f"{PENDING_BLOCK} block's {where} ({reason}) but names no declaration "
                f"in the {LIB_ROOT} library at all.  It was renamed or retired; update "
                "or remove the entry.")

    if args.print_ledger:
        print(f"\n--- ready-to-paste {PENDING_BLOCK} body "
              f"({len(kept_sorry)} declarations)")
        width = max((len(n) for n in kept_sorry), default=0)
        for decl in sorted((d for d, _ in kept if d.sorry_),
                           key=lambda d: (d.module, d.user)):
            reason = entries.get(decl.user) or consumers.get(decl.user) \
                or f"TODO: reason ({decl.module})"
            print(f"-- {decl.user.ljust(width)}  -- {reason}")

    if failures:
        print()
        for failure in failures:
            print("FAIL: " + failure)
        print(f"\ncondensation sorry ledger: {len(failures)} violation(s); "
              f"{len(kept_sorry)} sorry-dependent declarations, {len(listed)} ledgered "
              f"({len(entries)} main, {len(consumers)} consumers)")
        return 1

    print(f"condensation sorry ledger: OK — {len(kept_sorry)} sorry-dependent "
          f"declarations, all ledgered ({len(entries)} main, {len(consumers)} "
          f"consumers); {elapsed:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
