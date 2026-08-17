#!/usr/bin/env python3
"""Enforce that every formalized paper in this repository is fully wired up.

The individual gates each check one thing well — that cited nodes exist, that endpoints
are axiom-clean, that the trust-surface page is fresh.  None of them notices a paper
that was never connected to those gates in the first place, which is exactly how
`ModalAgents/` went for its whole life without a committed paper source or a single
provenance annotation while every check reported green.

This script closes that hole, and keeps it closed.  It reads `scripts/papers.py` and
verifies, for each registered paper, that:

  1. the paper's source and PDF are committed, and the source is non-empty;
  2. the library directory exists and contains Lean;
  3. `AxiomAudit.lean` imports the library, so its endpoints are inside the axiom gate;
  4. the library's node checker exists, is executable, and runs clean;
  5. that checker is a blocking step in CI;
  6. the library has a README;
  7. the trust-surface guide renders at least one node for the paper, per the coverage
     stamp `gen-trust-surface.py` writes into the page (see TRUST_SURFACE_ALL_PAPERS).
  8. every paper marked `completed` has a documented consumer API entrypoint and a
     client-style smoke test that imports only that API;
  9. those smoke tests are collected in the default-built `APITests` library.

and — the part that makes it hold in perpetuity — that **every `lean_lib` declared in
`lakefile.lean` is either a registered paper or an explicitly excused non-paper
library**.  A new formalization therefore cannot ship half-connected: adding the
library breaks this check until the paper is registered and wired, and removing a
paper's source or dropping its checker from CI breaks it too.

Run from the repository root.  Exits non-zero on any violation.
"""

import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_nodes  # noqa: E402
from papers import PAPERS, NON_PAPER_LIBRARIES  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CI = os.path.join(ROOT, ".github/workflows/ci.yml")
AUDIT = os.path.join(ROOT, "AxiomAudit.lean")
LAKEFILE = os.path.join(ROOT, "lakefile.lean")
TRUST_SURFACE = os.path.join(ROOT, "docs/trust-surface.html")
API_TEST_ROOT = os.path.join(ROOT, "APITests.lean")

# The trust-surface guide is paper-generic and covers every registered paper, so the
# requirement is blocking: a new paper must appear in the guide, not merely be registered.
TRUST_SURFACE_ALL_PAPERS = True

violations = []
notes = []


def path(rel):
    return os.path.join(ROOT, rel)


def declared_libraries():
    text = open(LAKEFILE).read()
    return set(re.findall(r"^lean_lib\s+(\w+)", text, re.M))


def run(cmd):
    """Run a checker; return (ok, first_meaningful_line)."""
    try:
        p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=600)
    except Exception as exc:  # noqa: BLE001 - report, never crash the gate
        return False, "could not run: %s" % exc
    out = (p.stdout + p.stderr).strip().splitlines()
    # Several checkers in this repo exit 0 while printing FAIL; trust the text too.
    printed_failure = any(
        re.search(r"\bFAIL\b|violation|Traceback", line) for line in out
    )
    ok = p.returncode == 0 and not printed_failure
    return ok, (out[-1] if out else "(no output)")


def lean_module(rel):
    """Translate a repository-relative Lean source path to its import name."""
    return rel.removesuffix(".lean").replace("/", ".")


def imports(rel):
    text = open(path(rel), encoding="utf-8").read()
    return re.findall(r"^import\s+([^\s]+)\s*$", text, re.M)


# ---------------------------------------------------------------- per-paper wiring
for key, paper in sorted(PAPERS.items()):
    lib = paper["library"]
    tag = "%s (%s)" % (key, lib)
    status = paper.get("status", "in-progress")

    if status not in {"in-progress", "completed"}:
        violations.append(
            "%s: status %r is invalid (expected 'in-progress' or 'completed')"
            % (tag, status))

    for field in ("source", "pdf", "readme"):
        rel = paper.get(field)
        if not rel:
            violations.append("%s: registry field %r is empty" % (tag, field))
            continue
        if not os.path.exists(path(rel)):
            violations.append("%s: %s missing at %s" % (tag, field, rel))
        elif field == "source" and os.path.getsize(path(rel)) == 0:
            violations.append("%s: paper source %s is empty" % (tag, rel))

    # A registry entry whose (scheme, source_format) pair has no parser is worse than a
    # missing one: nothing else notices, and the tooling that reads it just finds no
    # nodes — which reads as "this paper numbers nothing" rather than as an error.
    try:
        paper_nodes.scheme_of(paper)
    except KeyError as exc:
        violations.append("%s: node-citation scheme is unusable — %s" % (tag, exc.args[0]))

    for field in ("knowledge", "errata", "coverage_table"):
        rel = paper.get(field)
        if rel and not os.path.exists(path(rel)):
            violations.append("%s: registry names %s=%s but it does not exist"
                              % (tag, field, rel))

    libdir = path(lib)
    if not os.path.isdir(libdir):
        violations.append("%s: library directory %s/ does not exist" % (tag, lib))
    elif not any(f.endswith(".lean") for _, _, fs in os.walk(libdir) for f in fs):
        violations.append("%s: library directory %s/ contains no Lean source" % (tag, lib))

    audit = open(AUDIT).read()
    if not re.search(r"^import\s+%s\b" % re.escape(lib), audit, re.M):
        violations.append(
            "%s: AxiomAudit.lean does not import %s — its endpoints are outside the "
            "axiom gate" % (tag, lib))

    checker = paper.get("node_checker")
    if not checker:
        violations.append("%s: no node_checker registered" % tag)
    elif not os.path.exists(path(checker)):
        violations.append("%s: node checker %s does not exist" % (tag, checker))
    else:
        if checker.endswith(".sh") and not os.access(path(checker), os.X_OK):
            violations.append("%s: node checker %s is not executable" % (tag, checker))
        cmd = ([path(checker)] if checker.endswith(".sh")
               else ["python3", path(checker)])
        ok, last = run(cmd)
        if not ok:
            violations.append("%s: node checker failed — %s" % (tag, last))

        ci = open(CI).read() if os.path.exists(CI) else ""
        if os.path.basename(checker) not in ci:
            violations.append(
                "%s: node checker %s is not referenced in %s — provenance would be "
                "unchecked between harness runs"
                % (tag, checker, os.path.relpath(CI, ROOT)))

    # The guide stamps how many nodes it rendered for each registered paper, so this
    # tests what the page actually contains rather than whether a title string occurs
    # somewhere in it.
    if os.path.exists(TRUST_SURFACE):
        page = open(TRUST_SURFACE, encoding="utf-8", errors="replace").read()
        stamp = re.search(r"<!-- trust-surface-papers: ([^>]*) -->", page)
        rendered = dict(
            (part.split("=")[0], int(part.split("=")[1]))
            for part in (stamp.group(1).split() if stamp else []) if "=" in part)
        if rendered.get(key, 0) < 1:
            msg = ("%s: the trust-surface guide (%s) renders no node for this paper"
                   % (tag, os.path.relpath(TRUST_SURFACE, ROOT)))
            (violations if TRUST_SURFACE_ALL_PAPERS else notes).append(msg)

    # Consumer readiness is a completion gate, not an obstacle to incremental work.
    # A paper may be registered while in progress; changing its status to `completed`
    # opts it into the supported-API contract below.
    if status == "completed":
        api = paper.get("api")
        api_test = paper.get("api_test")
        if not api:
            violations.append("%s: completed paper has no api entrypoint" % tag)
        elif not os.path.exists(path(api)):
            violations.append("%s: API entrypoint missing at %s" % (tag, api))
        else:
            api_text = open(path(api), encoding="utf-8").read()
            if not api.startswith(lib + "/"):
                violations.append(
                    "%s: API entrypoint %s is not inside %s/" % (tag, api, lib))
            if "/-!" not in api_text:
                violations.append(
                    "%s: API entrypoint %s has no module documentation" % (tag, api))
            api_imports = imports(api)
            if not api_imports:
                violations.append("%s: API entrypoint %s exports no Lean modules"
                                  % (tag, api))
            if "AxiomAudit" in api_imports:
                violations.append("%s: API entrypoint %s imports AxiomAudit"
                                  % (tag, api))

        if not api_test:
            violations.append("%s: completed paper has no api_test" % tag)
        elif not os.path.exists(path(api_test)):
            violations.append("%s: API smoke test missing at %s" % (tag, api_test))
        elif api:
            if not api_test.startswith("APITests/"):
                violations.append(
                    "%s: API smoke test %s is not isolated under APITests/"
                    % (tag, api_test))
            expected = lean_module(api)
            actual = imports(api_test)
            if actual != [expected]:
                violations.append(
                    "%s: %s must import only %s (found %s)"
                    % (tag, api_test, expected, ", ".join(actual) or "no imports"))

            aggregate = (open(API_TEST_ROOT, encoding="utf-8").read()
                         if os.path.exists(API_TEST_ROOT) else "")
            test_module = lean_module(api_test)
            if not re.search(r"^import\s+%s\s*$" % re.escape(test_module),
                             aggregate, re.M):
                violations.append(
                    "%s: APITests.lean does not import %s" % (tag, test_module))

# ----------------------------------------------------- perpetuity: nothing unlisted
declared = declared_libraries()
registered = {p["library"] for p in PAPERS.values()}
excused = set(NON_PAPER_LIBRARIES)

if "APITests" not in declared:
    violations.append("lakefile.lean does not declare the APITests client library")
else:
    lakefile = open(LAKEFILE, encoding="utf-8").read()
    if not re.search(r"@\[default_target\]\s*\nlean_lib\s+APITests\b", lakefile):
        violations.append("lean_lib APITests is not a default target, so CI may skip it")

for lib in sorted(declared - registered - excused):
    violations.append(
        "lean_lib %s is declared in lakefile.lean but is neither a registered paper "
        "(scripts/papers.py PAPERS) nor an excused non-paper library "
        "(NON_PAPER_LIBRARIES). If it formalizes a paper, register it and wire it up; "
        "if not, excuse it there with a reason." % lib)

for lib in sorted(registered - declared):
    violations.append(
        "scripts/papers.py registers library %s but lakefile.lean declares no such "
        "lean_lib — the registry has gone stale." % lib)

for lib in sorted(excused - declared):
    notes.append("NON_PAPER_LIBRARIES excuses %s, which lakefile.lean no longer "
                 "declares; the entry can be dropped." % lib)

for lib, reason in sorted(NON_PAPER_LIBRARIES.items()):
    if not reason or not reason.strip():
        violations.append("NON_PAPER_LIBRARIES[%r] has no reason recorded" % lib)

# ------------------------------------------------------------------------- report
for note in notes:
    print("note: %s" % note)
for v in violations:
    print("VIOLATION: %s" % v)

if violations:
    print("\n%d violation(s)." % len(violations))
    sys.exit(1)

completed = sum(p.get("status", "in-progress") == "completed" for p in PAPERS.values())
print("paper-wiring check: OK (%d papers registered, %d completed APIs, "
      "%d non-paper libraries excused%s)"
      % (len(PAPERS), completed, len(NON_PAPER_LIBRARIES),
         "; %d note(s)" % len(notes) if notes else ""))
