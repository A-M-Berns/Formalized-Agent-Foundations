#!/usr/bin/env python3
"""Enforce that every Palomar registry entry in `Palomar/` is correctly wired.

A Palomar entry is one Comparator configuration: a `Challenge.lean` / `Solution.lean` /
`comparator.json` triple, plus the `formalization.yaml` that describes it.  One
repository and commit can carry many entries; this repository carries one per planned
submission, under `Palomar/<Entry>/`.

The registry's own verifier checks all of this on the submitted commit.  By then it is
too late to be cheap: a rejected submission costs a round trip, and the failure that
costs the most is the one this script exists for — an illegal *import* in a challenge
module.  Palomar requires that a challenge's transitive import closure contain **only**
Lean core, Mathlib (at a verified revision, with its pinned manifest closure), Tau Ceti,
and CSLib.  It may not contain a module of this repository, `Foundation`, or
`Complexitylib`.  That rule is easy to violate by accident and invisible locally: the
challenge compiles perfectly, because everything it imports is present.  So this script
resolves the closure statically and fails closed.

What it checks, per entry directory under `Palomar/`:

  1. all four files exist and are non-empty;
  2. `comparator.json` parses, is a single object, carries exactly the four required
     keys (plus the optional `definition_names`), and its `permitted_axioms` is exactly
     `{propext, Quot.sound, Classical.choice}`;
  3. `challenge_module` / `solution_module` name the entry's own two modules, and those
     dotted names resolve to the files on disk;
  4. `Challenge.lean` is inside Palomar's hard caps — 100 KiB and 1000 lines — and a
     warning is reported (not a failure) above the audit thresholds of 32 KiB / 300
     lines;
  5. the challenge's transitive import closure is confined to the permitted roots.

Stubs pass: a challenge module with a docstring and no imports has an empty closure, and
a placeholder `theorem_names` entry is still a nonempty list of strings.  Statement
content is deliberately not checked — that is a mathematical review, not a wiring gate.

`Palomar/SmokeTest/` is checked like any other entry (it is a real triple and must stay
valid) but is flagged in the output as never-to-be-submitted.

Run from the repository root.  Exits non-zero on any violation; warnings alone exit 0.
"""

import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PALOMAR = os.path.join(ROOT, "Palomar")

REQUIRED_KEYS = {"challenge_module", "solution_module", "theorem_names",
                 "permitted_axioms"}
# `definition_names` is Palomar's optional definition-hole list. `enable_nanoda` is
# accepted and ignored by the registry, but Comparator v4.31.0 parses it as a
# *non-optional* Bool — every config in Comparator's own test suite sets it — so a
# config that omits it cannot be run locally. Both are permitted, neither is required.
OPTIONAL_KEYS = {"definition_names", "enable_nanoda"}
PERMITTED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}

# The Comparator harness check. A real triple, checked like any other entry, but never
# submitted and so carrying no `formalization.yaml`.
SMOKE_TEST = "SmokeTest"

# Hard caps and audit-warning thresholds, from PalomarPolicy CONTRIBUTING.md §2.2.
HARD_BYTES, HARD_LINES = 100 * 1024, 1000
WARN_BYTES, WARN_LINES = 32 * 1024, 300

# Import roots a challenge module may reach.  `Init`/`Lean`/`Std`/`Lake` are Lean core.
# The rest is Mathlib together with its pinned manifest closure, which Palomar's
# `allowed-challenge-repositories.json` admits under the Mathlib root
# (`include_pinned_manifest_closure: true`), plus the two qualified roots.
CORE_ROOTS = {"Init", "Lean", "Std", "Lake"}
MATHLIB_CLOSURE_ROOTS = {
    "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible",
    "ImportGraph", "LeanSearchClient", "Cli",
}
QUALIFIED_ROOTS = {"TauCeti", "Cslib", "CSLib"}
ALLOWED_ROOTS = CORE_ROOTS | MATHLIB_CLOSURE_ROOTS | QUALIFIED_ROOTS

# Roots that are definitely not permitted, named so the message can say why rather than
# just "unknown".  Everything else unknown also fails, but less informatively.
KNOWN_FORBIDDEN = {
    "Foundation": "FormalizedFormalLogic/Foundation — a repository dependency, not an "
                  "allowed challenge root",
    "Complexitylib": "A-M-Berns/complexitylib fork — a repository dependency, not an "
                     "allowed challenge root",
}

violations = []
warnings = []

BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT = re.compile(r"^\s*--.*$", re.M)
IMPORT = re.compile(r"^import\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$",
                    re.M)


def rel(p):
    return os.path.relpath(p, ROOT)


def imports_of(path):
    """The modules a Lean file imports.

    Block and line comments are stripped first.  This repository's module docstrings
    contain prose beginning with the word `import`, which a naive line scan reads as an
    import of a module named `that`; stripping comments is what keeps the closure walk
    from chasing them.
    """
    text = open(path, encoding="utf-8").read()
    text = BLOCK_COMMENT.sub("", text)
    text = LINE_COMMENT.sub("", text)
    return IMPORT.findall(text)


def local_module_path(module):
    """Path for a module provided by this repository, or None.

    Every `lean_lib` in `lakefile.lean` uses `srcDir := "."`, so a dotted module name is
    just its repository-relative path.
    """
    candidate = os.path.join(ROOT, *module.split(".")) + ".lean"
    return candidate if os.path.isfile(candidate) else None


def check_closure(entry, challenge_path, challenge_module):
    """Walk the challenge's transitive import closure; report every illegal root.

    Resolution is deliberately asymmetric.  A module provided by *this repository* is
    resolved to its file and recursed into, because a local module can pull in more
    local modules and the whole chain is a violation worth naming.  A module under a
    permitted external root is accepted and **not** recursed into: Palomar admits
    Mathlib's pinned manifest closure wholesale, so following imports inside Mathlib
    would cost a great deal and could not change the verdict.
    """
    seen = {challenge_module}
    stack = [(challenge_module, challenge_path, [challenge_module])]
    reported = set()

    while stack:
        module, path, chain = stack.pop()
        for imp in imports_of(path):
            if imp in seen:
                continue
            seen.add(imp)
            root = imp.split(".")[0]
            trail = " -> ".join(chain + [imp])

            if root in ALLOWED_ROOTS:
                continue

            local = local_module_path(imp)
            if local is not None:
                if imp not in reported:
                    reported.add(imp)
                    violations.append(
                        "%s: challenge imports repository module `%s` — a challenge "
                        "closure may contain only Lean core, Mathlib, Tau Ceti and "
                        "CSLib.\n      via %s" % (entry, imp, trail))
                stack.append((imp, local, chain + [imp]))
                continue

            if imp not in reported:
                reported.add(imp)
                why = KNOWN_FORBIDDEN.get(root, "unknown provider; not a permitted "
                                                "challenge root")
                violations.append(
                    "%s: challenge imports `%s` (%s).\n      via %s"
                    % (entry, imp, why, trail))


def check_entry(entry):
    d = os.path.join(PALOMAR, entry)
    names = ["Challenge.lean", "Solution.lean", "comparator.json"]
    # `SmokeTest` is a harness check, not a submission: it validates the Comparator
    # invocation and is never registered, so it carries no `formalization.yaml`.
    # Everything else about it is checked exactly as a real entry.
    if entry != SMOKE_TEST:
        names.append("formalization.yaml")
    files = {name: os.path.join(d, name) for name in names}

    missing = [n for n, p in files.items() if not os.path.isfile(p)]
    if missing:
        violations.append("%s: missing %s" % (entry, ", ".join(sorted(missing))))
        return
    for name, p in files.items():
        if os.path.getsize(p) == 0:
            violations.append("%s: %s is empty" % (entry, name))

    # --- comparator.json -----------------------------------------------------
    try:
        with open(files["comparator.json"], encoding="utf-8") as fh:
            cfg = json.load(fh)
    except Exception as exc:  # noqa: BLE001 - report, never crash the gate
        violations.append("%s: comparator.json does not parse: %s" % (entry, exc))
        return

    if not isinstance(cfg, dict):
        violations.append("%s: comparator.json must be a single JSON object" % entry)
        return

    keys = set(cfg)
    if missing_keys := REQUIRED_KEYS - keys:
        violations.append("%s: comparator.json missing key(s): %s"
                          % (entry, ", ".join(sorted(missing_keys))))
    if extra := keys - REQUIRED_KEYS - OPTIONAL_KEYS:
        violations.append("%s: comparator.json has unexpected key(s): %s"
                          % (entry, ", ".join(sorted(extra))))

    axioms = cfg.get("permitted_axioms")
    if not isinstance(axioms, list) or set(axioms) != PERMITTED_AXIOMS:
        violations.append(
            "%s: permitted_axioms must be exactly %s, got %r"
            % (entry, sorted(PERMITTED_AXIOMS), axioms))

    names = cfg.get("theorem_names")
    if (not isinstance(names, list) or not names
            or not all(isinstance(n, str) and n for n in names)):
        violations.append("%s: theorem_names must be a nonempty list of strings, "
                          "got %r" % (entry, names))
    elif any(n.startswith("TODO") for n in names):
        warnings.append("%s: theorem_names is still a placeholder (%s)"
                        % (entry, ", ".join(n for n in names if n.startswith("TODO"))))

    # --- module names match the files on disk --------------------------------
    expected = {"challenge_module": "Palomar.%s.Challenge" % entry,
                "solution_module": "Palomar.%s.Solution" % entry}
    for key, want in expected.items():
        got = cfg.get(key)
        if got != want:
            violations.append("%s: %s is %r, expected %r (the module name must match "
                              "the file's path under Palomar/)" % (entry, key, got, want))
        elif local_module_path(want) is None:
            violations.append("%s: %s names `%s`, which does not resolve to a file"
                              % (entry, key, want))

    # --- challenge size caps --------------------------------------------------
    ch = files["Challenge.lean"]
    nbytes = os.path.getsize(ch)
    nlines = sum(1 for _ in open(ch, encoding="utf-8"))
    if nbytes > HARD_BYTES or nlines > HARD_LINES:
        violations.append("%s: Challenge.lean exceeds Palomar's hard cap "
                          "(%d bytes / %d lines; cap is %d / %d)"
                          % (entry, nbytes, nlines, HARD_BYTES, HARD_LINES))
    elif nbytes > WARN_BYTES or nlines > WARN_LINES:
        warnings.append("%s: Challenge.lean is over the audit-warning threshold "
                        "(%d bytes / %d lines; threshold is %d / %d) — the registry "
                        "will flag it for review"
                        % (entry, nbytes, nlines, WARN_BYTES, WARN_LINES))

    # --- the check that matters ----------------------------------------------
    check_closure(entry, ch, "Palomar.%s.Challenge" % entry)


def main():
    if not os.path.isdir(PALOMAR):
        print("FAIL: no Palomar/ directory at %s" % rel(PALOMAR))
        return 1

    entries = sorted(e for e in os.listdir(PALOMAR)
                     if os.path.isdir(os.path.join(PALOMAR, e)))
    if not entries:
        print("FAIL: Palomar/ contains no entry directories")
        return 1

    for entry in entries:
        check_entry(entry)

    for entry in entries:
        tag = "  (smoke test — never submit)" if entry == SMOKE_TEST else ""
        print("checked Palomar/%s%s" % (entry, tag))

    for w in warnings:
        print("WARN: %s" % w)

    if violations:
        print()
        for v in violations:
            print("FAIL: %s" % v)
        print("\n%d violation(s) across %d entries." % (len(violations), len(entries)))
        return 1

    print("\nOK: %d entries wired correctly (%d warning(s))."
          % (len(entries), len(warnings)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
