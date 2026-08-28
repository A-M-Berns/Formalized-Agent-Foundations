#!/usr/bin/env python3
"""Two second opinions on the compiled library: kernel replay, and a blanket axiom audit.

`AxiomAudit.lean` is an *enumerated inventory*. It says so itself: "It says nothing
about whether the list is complete." `#assert_axioms_clean` reaches exactly the
names someone typed into it, and `scripts/check_sorry_ledger.py` closes half the
remaining gap by enumerating every `sorryAx`-dependent Condensation declaration
from the compiled environment. Two holes are left, and neither is exotic.

**Nothing checks the declarations nobody listed, against axioms other than
`sorryAx`.** `native_decide` mints a fresh axiom during compilation that appears
in no source file, so no `grep` and no source-reading lint can see it; an axiom
can also reach in through an import. The blanket audit
(`leanprover-community/axiom-audit`) asks the compiled environment about *every*
declaration defined under each audited root, against `propext`,
`Classical.choice`, `Quot.sound` — the same three, unchanged.

**Nothing re-derives the environment the audit reads.** Both `#assert_axioms_clean`
and the sorry ledger read the environment `lake build` produced; a declaration that
entered it without the kernel checking it — `addDeclCore (doCheck := false)`, a
tactic reaching past the checked environment, a bug in Lean's import or
parallel-elaboration handling — is clean to both, because reading an environment is
not re-deriving it. `leanchecker` replays each compiled module through the kernel,
and catches exactly that.

The three are not redundant, and the round that added these two demonstrated it
rather than asserting it: a theorem of `False` added with `doCheck := false` builds
green, reports "does not depend on any axioms", passes the blanket audit, and is
caught only by replay; a `native_decide` proof in an unlisted declaration builds
green, passes replay and passes `#assert_axioms_clean`, and is caught only by the
blanket audit.

## Division of labour with the registered-snapshot checks

Palomar runs Comparator and NanoDa — an independent type checker — over
*registration commits*. That is the deep, slow verification of a frozen snapshot.
These two gates are the everyday coverage of `main` **between** those freezes: they
run on push to `main` and on a nightly schedule, not on every pull request, because
a pull request's protection is the build plus the enumerated inventory and replay's
wall time does not belong in that path. Neither layer replaces the other. Palomar
answers "is this snapshot sound, by an independent implementation"; this answers
"did anything land on main today that the kernel would not accept, or that carries
an axiom nobody declared".

## Scope

Every `lean_lib` in `lakefile.lean` is either audited or excluded *by name* below,
and a library that is neither fails this script rather than being silently skipped
— the same fail-closed discipline `scripts/check_paper_wiring.py` applies to the
paper registry.

## The pin

`leanchecker` ships inside the Lean toolchain from v4.28.0 onward — the standalone
`leanprover/lean4checker` is deprecated — so the checker is the one `lean-toolchain`
already names, and a skew between library and checker cannot come from a pin
drifting. `axiom-audit` is pinned to a tag *and* to the commit that tag resolved to,
verified after the clone, because a tag is mutable and a pin its publisher can move
is not a pin.
"""
from __future__ import annotations

import json
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
LAKEFILE = ROOT / "lakefile.lean"
TOOLCHAIN = ROOT / "lean-toolchain"

ALLOWED = ("propext", "Classical.choice", "Quot.sound")

REPO = "https://github.com/leanprover-community/axiom-audit.git"
PINNED_REF = "v0.1.2"
PINNED_SHA = "46024e005996495c65ef609368e11ab39c4222e3"

# Every library whose declarations are replayed and audited, and why it is in
# scope. Vendored dependency code is included deliberately: it is compiled into
# this repository's environment and the paper libraries' results rest on it, and
# auditing it costs one more prefix.
AUDITED = {
    "LogicalInduction": "paper library",
    "ModalAgents": "paper library",
    "CartesianFrames": "paper library",
    "FiniteFactoredSets": "paper library",
    "FactoredSpaces": "paper library",
    "Condensation": "paper library (in-progress; its `sorry` ledger is "
                    "scripts/check_sorry_ledger.py, and the pending block is empty)",
    "ShannonInformation": "shared paper-neutral infrastructure over the vendored PFR "
                          "entropy substrate",
    "PFR": "vendored subset of teorth/pfr — dependency code, audited anyway: it is "
           "compiled into this environment and the Shannon layer rests on it",
    "ProvabilityLogic": "vendored subset of FormalizedFormalLogic/ProvabilityLogic — "
                        "same reasoning; ModalAgents' GL fixed point rests on it. "
                        "Checked on its built closure; see PARTIAL below",
    "APITests": "the client-style smoke tests; they are declarations in this "
                "environment like any other",
    "AxiomAudit": "the inventory target itself",
}

# Audited libraries that are *not* `@[default_target]`s. `lake build` compiles only
# the modules an audited library imports from them, so the committed source tree
# overstates what exists: the coverage here is the built closure, and the gate
# asserts that it is non-empty rather than that it is complete. Stated rather than
# hidden, because "we replayed ProvabilityLogic" would otherwise read as a claim
# about all 34 of its modules when it is a claim about the ones ModalAgents needs.
#
# The audit still covers what matters even where replay does not reach: an axiom in
# an unbuilt vendored module cannot affect a result nobody imports, and one in a
# built module propagates into the importing library's audited declarations.
PARTIAL = {
    "ProvabilityLogic": "not a `@[default_target]`; only the modules ModalAgents "
                        "imports are compiled",
}

# Every library deliberately out of scope, and why. A library is excluded only
# when a reason survives being written down.
EXCLUDED = {
    "Scratchpad": "not a `@[default_target]`, so `lake build` never compiles it and "
                  "there are no oleans to check. Excluding it is a statement about "
                  "what was built, not a judgement about the code; `assert_scope` "
                  "below fails if it ever becomes a default target.",
    "MachineExec": "not a separate module tree: its `roots` is "
                   "`LogicalInduction.Construction.Machine`, so its modules carry the "
                   "`LogicalInduction` prefix and are already replayed and audited "
                   "under that root. A second root here would double the work and "
                   "audit nothing new.",
}

REPLAYING = re.compile(r"^replaying (\S+)$", re.M)
LEAN_LIB = re.compile(r"^lean_lib\s+(\w+)", re.M)
DEFAULT_TARGET = re.compile(r"@\[default_target\]\s*\nlean_lib\s+(\w+)", re.M)
MACHINE_EXEC_ROOTS = re.compile(r"lean_lib\s+MachineExec\b.*?roots\s*:=\s*#\[`([\w.]+)\]", re.S)


# --------------------------------------------------------------------------- scope

def declared_libraries(lakefile: str) -> set[str]:
    return set(LEAN_LIB.findall(lakefile))


def default_targets(lakefile: str) -> set[str]:
    return set(DEFAULT_TARGET.findall(lakefile))


def assert_scope(lakefile: str) -> list[str]:
    """Every declared library is classified, and each classification still holds."""
    problems: list[str] = []
    declared = declared_libraries(lakefile)
    if not declared:
        return ["no `lean_lib` found in lakefile.lean — that is a broken checkout, "
                "not a project with nothing to check"]
    classified = set(AUDITED) | set(EXCLUDED)
    for lib in sorted(declared - classified):
        problems.append(f"lean_lib {lib!r} is declared in lakefile.lean and is neither "
                        "audited nor excluded by name. Classify it in scripts/lean_gates.py; "
                        "a library nobody classified is a library nobody checked")
    for lib in sorted(classified - declared):
        problems.append(f"scripts/lean_gates.py classifies {lib!r} and no lean_lib "
                        "declares it — a stale entry reads as a reviewed decision")
    targets = default_targets(lakefile)
    for lib in sorted(set(AUDITED) & declared):
        if lib not in targets and lib not in PARTIAL:
            problems.append(f"{lib!r} is audited but is not a `@[default_target]`, so "
                            "`lake build` may not have compiled it. Either make it one, "
                            "or record it in PARTIAL with the reason its coverage is the "
                            "built closure rather than the source tree")
    for lib in sorted(PARTIAL):
        if lib not in AUDITED:
            problems.append(f"{lib!r} is recorded as partially covered and is not audited")
        elif lib in targets:
            problems.append(f"{lib!r} is a `@[default_target]` now, so its whole source "
                            "tree is built and it no longer belongs in PARTIAL")
    if "Scratchpad" in targets:
        problems.append("Scratchpad is now a `@[default_target]`, so it is built and the "
                        "reason it is excluded no longer holds")
    machine = MACHINE_EXEC_ROOTS.search(lakefile)
    if "MachineExec" in declared:
        if not machine:
            problems.append("MachineExec is excluded because its modules sit under an "
                            "audited root, and its `roots :=` could not be read to "
                            "confirm that")
        elif not any(machine.group(1).startswith(root + ".") or machine.group(1) == root
                     for root in AUDITED):
            problems.append(f"MachineExec's root {machine.group(1)!r} is under no audited "
                            "prefix, so excluding it leaves its modules unchecked")
    return problems


BUILD_LIB = ROOT / ".lake" / "build" / "lib" / "lean"


def built_modules(root: str) -> list[str]:
    """Every module of a library that `lake build` actually produced an olean for."""
    modules: list[str] = []
    if (BUILD_LIB / f"{root}.olean").is_file():
        modules.append(root)
    directory = BUILD_LIB / root
    if directory.is_dir():
        modules += [".".join(p.relative_to(BUILD_LIB).with_suffix("").parts)
                    for p in directory.rglob("*.olean")]
    return sorted(set(modules))


def modules_of(root: str) -> list[str]:
    """What this root is checked over: its sources, or its built closure if partial."""
    return built_modules(root) if root in PARTIAL else source_modules(root)


def source_modules(root: str) -> list[str]:
    """Every committed module of a library: `<Root>.lean` if present, plus `<Root>/**`."""
    modules: list[str] = []
    if (ROOT / f"{root}.lean").is_file():
        modules.append(root)
    directory = ROOT / root
    if directory.is_dir():
        modules += [".".join(p.relative_to(ROOT).with_suffix("").parts)
                    for p in directory.rglob("*.lean")]
    return sorted(set(modules))


def audited_roots() -> list[str]:
    return sorted(AUDITED)


# ------------------------------------------------------------------------- verdicts

def replay_verdict(returncode: int, output: str,
                   expected: dict[str, list[str]]) -> list[str]:
    """Fails closed: a non-zero exit, an empty enumeration, or a missing module."""
    problems: list[str] = []
    flat = sorted({m for ms in expected.values() for m in ms})
    if not flat:
        problems.append("the committed sources name no modules to replay; that is a "
                        "broken checkout, not a library with nothing to check")
    got = set(REPLAYING.findall(output))
    if returncode != 0:
        problems.append(f"leanchecker exited {returncode}")
    if not got:
        problems.append("leanchecker enumerated no modules — it replayed nothing, which "
                        "exits zero and looks exactly like a clean run")
    for root in sorted(expected):
        missing = [m for m in expected[root] if m not in got]
        if missing:
            problems.append(f"{root}: {len(missing)} committed module(s) not replayed: "
                            f"{missing[:10]}{' …' if len(missing) > 10 else ''}")
    return problems


def audit_verdict(root: str, returncode: int, stdout: str) -> tuple[list[str], dict]:
    """Fails closed: unparseable output, nothing audited, a widened allowlist, a violation."""
    problems: list[str] = []
    try:
        report = json.loads(stdout.strip().splitlines()[-1]) if stdout.strip() else {}
    except (json.JSONDecodeError, IndexError):
        return [f"{root}: the audit printed no parseable JSON report (exit {returncode})"], {}
    if not report:
        return [f"{root}: the audit printed no report (exit {returncode})"], {}
    if "error" in report:
        problems.append(f"{root}: the audit could not run: {report['error']}")
    audited = report.get("audited")
    if not isinstance(audited, int) or audited <= 0:
        problems.append(f"{root}: the audit reports {audited!r} declarations audited; an "
                        "audit that audited nothing passes by checking nothing")
    if report.get("root") != root:
        problems.append(f"{root}: the audit reports root {report.get('root')!r}")
    allowed = tuple(report.get("allowed") or ())
    if allowed != ALLOWED:
        problems.append(f"{root}: the audit ran with allowlist {list(allowed)}, "
                        f"not {list(ALLOWED)}")
    for violation in report.get("violations") or []:
        problems.append(f"{root}: {violation.get('decl')} depends on "
                        f"{violation.get('axioms')} outside {list(ALLOWED)}")
    if returncode != 0 and not problems:
        problems.append(f"{root}: the audit exited {returncode} while reporting no violation")
    return problems, report


# ---------------------------------------------------------------------------- tools

def assert_toolchain() -> list[str]:
    """The checker Lean hands us is the toolchain `lean-toolchain` names.

    Loud, not quiet: a checker from another toolchain does not check less, it
    crashes or refuses an incompatible olean header — and a crash with no output
    is the one shape that could be mistaken for a clean run, which is why the
    module count is asserted too."""
    if not TOOLCHAIN.is_file():
        return ["lean-toolchain is missing"]
    pinned = TOOLCHAIN.read_text().strip()
    version = pinned.rsplit(":", 1)[-1]
    which = subprocess.run(["elan", "which", "leanchecker"], cwd=ROOT,
                           capture_output=True, text=True)
    if which.returncode != 0:
        return [f"`elan which leanchecker` failed ({which.returncode}): "
                f"{which.stderr.strip()[:200]}. The toolchain pinned as {pinned!r} ships "
                "no `leanchecker`; it arrived in v4.28.0"]
    if version not in which.stdout.strip():
        return [f"`elan which leanchecker` resolved to {which.stdout.strip()!r}, which "
                f"does not name the pinned toolchain {pinned!r}"]
    return []


def fetch_tool(workdir: pathlib.Path) -> tuple[pathlib.Path | None, list[str]]:
    clone = workdir / "axiom-audit"
    got = subprocess.run(["git", "clone", "--depth", "1", "--branch", PINNED_REF,
                          REPO, str(clone)], capture_output=True, text=True)
    if got.returncode != 0:
        return None, [f"cloning {REPO} at {PINNED_REF} failed: {got.stderr.strip()[:300]}"]
    head = subprocess.run(["git", "-C", str(clone), "rev-parse", "HEAD"],
                          capture_output=True, text=True).stdout.strip()
    if head != PINNED_SHA:
        return None, [f"{PINNED_REF} resolved to {head!r}, not the pinned {PINNED_SHA!r}. "
                      "A tag is mutable; the commit is the pin"]
    shutil.copy(TOOLCHAIN, clone / "lean-toolchain")
    build = subprocess.run(["lake", "build"], cwd=clone, capture_output=True, text=True)
    if build.returncode != 0:
        return None, [f"building axiom-audit at {PINNED_SHA} under "
                      f"{TOOLCHAIN.read_text().strip()!r} failed:\n"
                      f"{(build.stdout + build.stderr)[-1500:]}"]
    binary = clone / ".lake" / "build" / "bin" / "axiom-audit"
    if not binary.is_file():
        return None, [f"axiom-audit built but produced no binary at {binary}"]
    return binary, []


# ------------------------------------------------------------------------- the modes

def run_replay() -> int:
    problems = assert_scope(LAKEFILE.read_text()) + assert_toolchain()
    if problems:
        report_failure("KERNEL REPLAY", problems)
        return 1
    expected = {root: modules_of(root) for root in audited_roots()}
    thin = [root for root in PARTIAL if not expected.get(root)]
    if thin:
        report_failure("KERNEL REPLAY",
                       [f"{root}: recorded as partially covered, and the build produced "
                        "no oleans for it at all — that is a broken build, not a library "
                        "with nothing to check" for root in thin])
        return 1
    started = time.monotonic()
    proc = subprocess.run(["lake", "env", "leanchecker", "-v", *audited_roots()],
                          cwd=ROOT, capture_output=True, text=True)
    elapsed = time.monotonic() - started
    output = proc.stdout + proc.stderr
    got = sorted(set(REPLAYING.findall(output)))

    print(f"KERNEL REPLAY: {len(got)} module(s) replayed through the kernel "
          f"in {elapsed:.0f}s, across {len(expected)} audited root(s):")
    for root in audited_roots():
        here = [m for m in got if m == root or m.startswith(root + ".")]
        note = f" [built closure only: {PARTIAL[root]}]" if root in PARTIAL else ""
        print(f"  {root}: {len(here)} module(s) — {AUDITED[root]}{note}")
        for module in here:
            print(f"    {module}")
    for lib, why in sorted(EXCLUDED.items()):
        print(f"  (not replayed) {lib}: {why.splitlines()[0]}")

    problems = replay_verdict(proc.returncode, output, expected)
    if problems:
        report_failure("KERNEL REPLAY", problems,
                       "leanchecker output", output.splitlines()[-40:])
        return 1
    print(f"KERNEL REPLAY: the kernel accepted every declaration in all {len(got)} "
          "replayed module(s).")
    return 0


def run_audit() -> int:
    problems = assert_scope(LAKEFILE.read_text())
    if problems:
        report_failure("BLANKET AXIOM AUDIT", problems)
        return 1
    findings: list[str] = []
    total = 0
    with tempfile.TemporaryDirectory() as tmp:
        binary, problems = fetch_tool(pathlib.Path(tmp))
        if problems:
            report_failure("BLANKET AXIOM AUDIT — the tool", problems)
            return 1
        print(f"BLANKET AXIOM AUDIT: axiom-audit {PINNED_REF} ({PINNED_SHA}), "
              f"allowlist {list(ALLOWED)}")
        for root in audited_roots():
            modules = modules_of(root)
            if not modules:
                findings.append(f"{root}: no committed modules found under this root")
                continue
            started = time.monotonic()
            proc = subprocess.run(
                ["lake", "env", str(binary), "--root", root,
                 "--modules", ",".join(modules), "--json"],
                cwd=ROOT, capture_output=True, text=True)
            elapsed = time.monotonic() - started
            here, report = audit_verdict(root, proc.returncode, proc.stdout)
            findings += here
            audited = report.get("audited") or 0
            total += audited
            print(f"  {root}: {audited} declaration(s) over {len(modules)} module(s) "
                  f"in {elapsed:.0f}s — axioms used: "
                  f"{report.get('axiomsUsed') or ['none']}")
            if proc.stderr.strip() and here:
                findings.append(f"{root}: stderr — {proc.stderr.strip()[-600:]}")
    for lib, why in sorted(EXCLUDED.items()):
        print(f"  (not audited) {lib}: {why.splitlines()[0]}")
    if findings:
        report_failure("BLANKET AXIOM AUDIT", findings)
        return 1
    print(f"BLANKET AXIOM AUDIT: {total} declaration(s) across "
          f"{len(audited_roots())} root(s), all within {list(ALLOWED)}.")
    return 0


def report_failure(label: str, problems: list[str],
                   extra_label: str = "", extra: list[str] | None = None) -> None:
    print(f"{label} FAILED:", file=sys.stderr)
    for problem in problems:
        print(f"  - {problem}", file=sys.stderr)
    if extra:
        print(f"\n  {extra_label}:", file=sys.stderr)
        for line in extra:
            print(f"    {line}", file=sys.stderr)


# ------------------------------------------------------------------------ self-test

def self_test() -> int:
    """Null inputs first: every way these gates can check nothing is a failure.

    The verdicts run on captured output rather than by invoking Lean, so this
    runs in a job with no toolchain and no network — which is the point, since it
    is what gates the run that does have both.
    """
    lakefile = LAKEFILE.read_text()
    good = "replaying CartesianFrames\nreplaying CartesianFrames.Basic\n"
    expected = {"CartesianFrames": ["CartesianFrames", "CartesianFrames.Basic"]}
    clean = json.dumps({"root": "PFR", "allowed": list(ALLOWED), "audited": 798,
                        "ok": True, "axiomsUsed": list(ALLOWED), "violations": []})
    dirty = json.dumps({"root": "PFR", "allowed": list(ALLOWED), "audited": 798,
                        "ok": False, "axiomsUsed": ["sorryAx"],
                        "violations": [{"decl": "PFR.x", "axioms": ["sorryAx"]}]})
    empty = json.dumps({"root": "PFR", "allowed": list(ALLOWED), "audited": 0,
                        "ok": False, "axiomsUsed": [], "violations": []})

    sys.path.insert(0, str(ROOT / "scripts"))
    import papers

    cases = [
        # Null inputs — replay.
        ("a silent replay is a failure", bool(replay_verdict(0, "", expected)), True),
        ("an empty expectation is a failure, not a skip",
         bool(replay_verdict(0, good, {})), True),
        ("a zero exit with a missing module is a failure",
         bool(replay_verdict(0, "replaying CartesianFrames\n", expected)), True),
        ("a full enumeration with exit zero passes",
         replay_verdict(0, good, expected), []),
        ("replaying more than the sources name is not a failure",
         replay_verdict(0, good + "replaying CartesianFrames.Gone\n", expected), []),
        ("a non-zero exit fails even with a full enumeration",
         bool(replay_verdict(1, good, expected)), True),
        ("a line that is not an enumeration line is not read as one",
         REPLAYING.findall("uncaught exception: replaying is hard\n"), []),
        # Null inputs — audit.
        ("no audit output is a failure", bool(audit_verdict("PFR", 0, "")[0]), True),
        ("unparseable audit output is a failure",
         bool(audit_verdict("PFR", 0, "not json")[0]), True),
        ("zero declarations audited is a failure",
         bool(audit_verdict("PFR", 0, empty)[0]), True),
        ("a clean audit passes", audit_verdict("PFR", 0, clean)[0], []),
        ("a violation is reported and names the declaration",
         "PFR.x" in audit_verdict("PFR", 1, dirty)[0][0], True),
        ("a non-zero exit with no violation is still a failure",
         bool(audit_verdict("PFR", 1, clean)[0]), True),
        ("an audit of a different root is a failure",
         bool(audit_verdict("PFR", 0, clean.replace('"PFR"', '"Other"'))[0]), True),
        ("a widened allowlist is a failure",
         bool(audit_verdict("PFR", 0, json.dumps(
             {"root": "PFR", "allowed": list(ALLOWED) + ["sorryAx"], "audited": 1,
              "ok": True, "axiomsUsed": [], "violations": []}))[0]), True),
        # Scope: the classification is complete and still true of the lakefile.
        ("the live lakefile's every library is classified", assert_scope(lakefile), []),
        ("a non-default-target audited library must be recorded as partial",
         bool(assert_scope(lakefile.replace(
             "@[default_target]\nlean_lib PFR where", "lean_lib PFR where"))), True),
        ("a partial entry for a default target is caught",
         bool(assert_scope(lakefile.replace(
             "lean_lib ProvabilityLogic where",
             "@[default_target]\nlean_lib ProvabilityLogic where"))), True),
        ("every partially covered library is audited",
         sorted(set(PARTIAL) - set(AUDITED)), []),
        ("an unclassified library is caught",
         bool(assert_scope(lakefile + "\nlean_lib Sneaky where\n  srcDir := \".\"\n")), True),
        ("a stale classification is caught",
         bool(assert_scope(lakefile.replace("lean_lib PFR where", "lean_lib PFRx where"))), True),
        ("no library is both audited and excluded",
         set(AUDITED) & set(EXCLUDED), set()),
        ("every excluded library carries a reason",
         all(why.strip() for why in EXCLUDED.values()), True),
        ("every audited library carries a reason",
         all(why.strip() for why in AUDITED.values()), True),
        ("every registered paper's library is audited",
         sorted({p["library"] for p in papers.PAPERS.values()} - set(AUDITED)), []),
        # The pin, and the allowance.
        ("the pinned commit is a full 40-character SHA", len(PINNED_SHA), 40),
        ("the pinned commit is hexadecimal",
         all(c in "0123456789abcdef" for c in PINNED_SHA), True),
        ("the allowance is exactly the standard three", len(ALLOWED), 3),
        ("the allowance is the one AxiomAudit.lean states",
         all(a in (ROOT / "AxiomAudit.lean").read_text() for a in ALLOWED), True),
        # The live tree, so the gates cannot pass by having stopped matching.
        ("every audited root has committed modules",
         [r for r in audited_roots() if not source_modules(r)], []),
        ("module names are derived from paths, not guessed",
         "CartesianFrames.Basic" in source_modules("CartesianFrames"), True),
        ("a library with a root module file includes it",
         "CartesianFrames" in source_modules("CartesianFrames"), True),
        ("a library with no root module file does not invent one",
         "PFR" in source_modules("PFR"), False),
    ]
    failures = 0
    print("LEAN GATES SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}"
              + ("" if got == want else f"\n      got {got!r}, want {want!r}"))
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    if "--replay" in argv:
        return run_replay()
    if "--audit" in argv:
        return run_audit()
    print(__doc__)
    print("usage: lean_gates.py (--self-test | --replay | --audit)", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
