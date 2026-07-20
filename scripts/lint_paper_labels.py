#!/usr/bin/env python3
"""Enforce notes/consolidation.md declaration-keyword rules 1-2:

* every `theorem` in LogicalInduction/ carries a docstring naming its paper label
  (thm:/lem:/cor:/def: node, an `App.` reference, or a § citation);
* `private theorem` does not occur (private statements are not paper statements —
  use `private lemma`).

Exit status is the number of offending files capped at 1. Run from the repo root.
"""

import re
import sys
from pathlib import Path

LABEL = re.compile(r"(thm|lem|cor|def|app):[a-zA-Z]+|App\.\s|§")
DECL = re.compile(r"^\s*(?P<private>private\s+)?(?:protected\s+)?theorem\s+(?P<name>[\w.]+)")

violations = []
for path in sorted(Path("LogicalInduction").rglob("*.lean")):
    lines = path.read_text().splitlines()
    for i, line in enumerate(lines):
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
