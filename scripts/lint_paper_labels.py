#!/usr/bin/env python3
"""Enforce the repo-wide declaration-keyword rules (CLAUDE.md, "Working conventions";
originally set out in LogicalInduction/notes/consolidation.md rules 1-2):

* every `theorem` in a paper library carries a docstring naming its paper label;
* `private theorem` does not occur (private statements are not paper statements —
  use `private lemma`).  This ban is global.

The accepted label form is per library, because the two papers have different
provenance keys:

* `LogicalInduction/` — the paper labels its nodes, so a `thm:`/`lem:`/`cor:`/`def:`/
  `app:` label, an `App.` reference, or a `§` section reference is the key.
* `CartesianFrames/` — most nodes carry no LaTeX label, so the printed number is the
  key and nothing else will do: the docstring must carry a `Paper node:` line naming a
  numbered `Claim` or `Theorem`.  A bare `§` reference is *not* enough there; a
  `theorem` in that library is by convention a paper claim or theorem, and
  `scripts/check-cartesian-frames-nodes.py` inventories it by that annotation.
* `FactoredSpaces/` — section-scoped shared counter with lettered appendix sections
  (`Lemma A.1`, `Corollary C.14`); the annotation must name a result, not a definition.
* `ModalAgents/` — same situation: only 22 of that paper's nodes are labelled, so the
  printed number is again the key.  Its counter is section-scoped and shared across
  `theorem`/`lemma`/`proposition`/`corollary`/`condition`, so node numbers read
  `<section>.<n>` and a bare integer will not do.  Its `definition` environment is
  uncounted, so `Definition` is not an accepted kind here (citing one is caught, with
  a sharper message, by `scripts/check-modal-agents-nodes.py`).

This linter enforces only that a `theorem` *names* a node in its library's format;
that the node exists in the committed TeX, that the annotation is anchored to a named
declaration, and that the declaration is inventoried in `AxiomAudit.lean` are the
per-paper node checkers' job.

Exit status is the number of offending files capped at 1. Run from the repo root.
"""

import re
import sys
from pathlib import Path

LI_LABEL = re.compile(r"(thm|lem|cor|def|app):[a-zA-Z]+|App\.\s|§")
CF_LABEL = re.compile(r"Paper node:.*(Claim|Theorem)\s+[0-9]+")
# Finite Factored Sets numbers every environment on its own global counter, so a
# paper-facing `theorem` there cites `Theorem n`, `Proposition n`, `Lemma n` or
# `Corollary n` — never a `<section>.<n>` pair.
FFS_LABEL = re.compile(
    r"Paper node:.*(Theorem|Proposition|Lemma|Corollary)\s+[0-9]+")

MA_LABEL = re.compile(
    r"Paper node:.*(Theorem|Lemma|Proposition|Corollary|Condition)\s+[0-9]+\.[0-9]+"
)
# Factored Space Models shares one section-scoped counter across every environment and
# letters its appendix sections, so a paper-facing `theorem` cites `Lemma 4.7`,
# `Theorem 6.2`, `Corollary C.14`, … — a `<section>.<n>` pair with a numeric or lettered
# section.  A `theorem` renders a paper *result*, so `Definition` is not accepted here.
FSM_LABEL = re.compile(
    r"Paper node:.*(Theorem|Lemma|Proposition|Corollary)\s+(?:[0-9]+|[A-Z])\.[0-9]+"
)
DECL = re.compile(r"^\s*(?P<private>private\s+)?(?:protected\s+)?theorem\s+(?P<name>[\w.]+)")

def block_depth_after(line, depth):
    """Nestable-comment depth after scanning `line`, given `depth` at its start."""
    k = 0
    while k < len(line):
        if line[k:k + 2] == "/-":
            depth += 1
            k += 2
        elif line[k:k + 2] == "-/":
            depth = max(0, depth - 1)
            k += 2
        else:
            k += 1
    return depth

violations = []
libraries = {
    Path("LogicalInduction"): LI_LABEL,
    Path("CartesianFrames"): CF_LABEL,
    Path("ModalAgents"): MA_LABEL,
    Path("FiniteFactoredSets"): FFS_LABEL,
    Path("FactoredSpaces"): FSM_LABEL,
}
paths = [(path, label) for library, label in libraries.items()
         for path in library.rglob("*.lean")]
for path, label in sorted(paths, key=lambda entry: entry[0]):
    lines = path.read_text().splitlines()
    depth = 0
    for i, line in enumerate(lines):
        at_start = depth
        depth = block_depth_after(line, depth)
        if at_start > 0:  # line begins inside a block comment / docstring — prose, not a decl
            continue
        m = DECL.match(line)
        if not m:
            continue
        if m.group("private"):
            violations.append(f"{path}:{i + 1}: private theorem {m.group('name')} (use private lemma)")
            continue
        j = i - 1
        while j >= 0 and not lines[j].strip():
            j -= 1
        if j < 0 or not lines[j].rstrip().endswith("-/"):
            violations.append(f"{path}:{i + 1}: theorem {m.group('name')} has no docstring")
            continue
        doc = [lines[j]]
        while "/--" not in doc[0] and j > 0:
            j -= 1
            doc.insert(0, lines[j])
        if not label.search("\n".join(doc)):
            violations.append(f"{path}:{i + 1}: theorem {m.group('name')} docstring names no paper label")

for v in violations:
    print(v)
print(f"\n{len(violations)} violation(s)." if violations else "All theorems carry paper labels.")
sys.exit(1 if violations else 0)
