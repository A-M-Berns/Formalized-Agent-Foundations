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
  7. the trust-surface guide covers the paper (see TRUST_SURFACE_ALL_PAPERS below).

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
from papers import PAPERS, NON_PAPER_LIBRARIES  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CI = os.path.join(ROOT, ".github/workflows/ci.yml")
AUDIT = os.path.join(ROOT, "AxiomAudit.lean")
LAKEFILE = os.path.join(ROOT, "lakefile.lean")
TRUST_SURFACE = os.path.join(ROOT, "docs/trust-surface.html")

# The trust-surface guide covers Logical Induction today; extending it to every paper
# is tracked work.  Flip this to True once the generator is paper-generic, and the
# check below becomes blocking for all papers instead of reporting a known gap.
TRUST_SURFACE_ALL_PAPERS = False

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


# ---------------------------------------------------------------- per-paper wiring
for key, paper in sorted(PAPERS.items()):
    lib = paper["library"]
    tag = "%s (%s)" % (key, lib)

    for field in ("source", "pdf", "readme"):
        rel = paper.get(field)
        if not rel:
            violations.append("%s: registry field %r is empty" % (tag, field))
            continue
        if not os.path.exists(path(rel)):
            violations.append("%s: %s missing at %s" % (tag, field, rel))
        elif field == "source" and os.path.getsize(path(rel)) == 0:
            violations.append("%s: paper source %s is empty" % (tag, rel))

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

    if os.path.exists(TRUST_SURFACE):
        page = open(TRUST_SURFACE, encoding="utf-8", errors="replace").read()
        covered = paper["title"].split(":")[0] in page or paper["arxiv"] in page
        if not covered:
            msg = ("%s: the trust-surface guide (%s) does not cover this paper"
                   % (tag, os.path.relpath(TRUST_SURFACE, ROOT)))
            (violations if TRUST_SURFACE_ALL_PAPERS else notes).append(msg)

# ----------------------------------------------------- perpetuity: nothing unlisted
declared = declared_libraries()
registered = {p["library"] for p in PAPERS.values()}
excused = set(NON_PAPER_LIBRARIES)

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

print("paper-wiring check: OK (%d papers registered, %d non-paper libraries excused%s)"
      % (len(PAPERS), len(NON_PAPER_LIBRARIES),
         "; %d note(s)" % len(notes) if notes else ""))
