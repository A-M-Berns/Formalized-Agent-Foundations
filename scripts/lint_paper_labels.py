#!/usr/bin/env python3
"""Enforce notes/consolidation.md declaration-keyword rules 1-2:

* every `theorem` in a paper library carries a docstring naming its paper label
  (LI label/App./section, or a Cartesian Frames numbered Claim/Theorem);
* `private theorem` does not occur (private statements are not paper statements —
  use `private lemma`).

Exit status is the number of offending files capped at 1. Run from the repo root.
"""

import re
import sys
from pathlib import Path

LABEL = re.compile(
    r"(thm|lem|cor|def|app):[a-zA-Z]+|App\.\s|§|"
    r"Paper node:\s*(Claim|Theorem)\s+[0-9]+"
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
libraries = [Path("LogicalInduction"), Path("CartesianFrames")]
paths = [path for library in libraries for path in library.rglob("*.lean")]
for path in sorted(paths):
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
            violations.append(f"{path}:{i + 1}: theorem {m.group('name')} docstring names no paper label")

for v in violations:
    print(v)
print(f"\n{len(violations)} violation(s)." if violations else "All theorems carry paper labels.")
sys.exit(1 if violations else 0)
