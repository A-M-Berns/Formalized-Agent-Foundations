#!/usr/bin/env python3
"""Enforce the declaration-keyword rules for the Critch PBL formalization
(adapted from the logical-induction branch's lint_paper_labels.py):

* every `theorem` in Critch/ carries a docstring citing its paper node (a §-citation;
  Critch 2019 is a PDF source with no `\\label`s, so §/Property/Theorem citations are
  the label convention — see AxiomAudit.lean's header);
* `private theorem` does not occur (private statements are not paper statements —
  use `private lemma`).

Exit status is the number of offending files capped at 1. Run from the repo root.
"""

import re
import sys
from pathlib import Path

LIB = Path("Critch")
LABEL = re.compile(r"§|Theorem\s+\d|Propert(y|ies)\s+\d|Proposition\s+\d|Definition\s+\d")
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
for path in sorted(LIB.rglob("*.lean")):
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
        if not LABEL.search("\n".join(doc)):
            violations.append(f"{path}:{i + 1}: theorem {m.group('name')} docstring names no paper node")

for v in violations:
    print(v)
print(f"\n{len(violations)} violation(s)." if violations else "All theorems carry paper nodes.")
sys.exit(1 if violations else 0)
