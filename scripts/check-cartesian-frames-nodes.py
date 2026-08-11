#!/usr/bin/env python3
"""Check Cartesian Frames `Paper node:` annotations against the arXiv source.

The paper numbers nodes in prose rather than assigning LaTeX labels to most of them.
This checker treats the printed `(Definition|Claim|Theorem) n` as the stable source ID.
"""

import re
import sys
from pathlib import Path

TEX = Path("notes/2109.10996v1-main.tex")
LIB = Path("CartesianFrames")
NODE = re.compile(r"\\textbf\{(Definition|Claim|Theorem)\s+([0-9]+)\}")
USED = re.compile(r"Paper node:\s*(Definition|Claim|Theorem)\s+([0-9]+)")

source = {f"{kind} {number}" for kind, number in NODE.findall(TEX.read_text())}
used: list[tuple[Path, int, str]] = []

for path in [Path("CartesianFrames.lean"), *sorted(LIB.rglob("*.lean"))]:
    for line_number, line in enumerate(path.read_text().splitlines(), start=1):
        for kind, number in USED.findall(line):
            used.append((path, line_number, f"{kind} {number}"))

violations = [
    f"{path}:{line}: INVALID NODE: {node!r} is not numbered in {TEX}"
    for path, line, node in used
    if node not in source
]

for violation in violations:
    print(violation)

if violations:
    print(f"\n{len(violations)} violation(s).")
    sys.exit(1)

print(
    "cartesian-frames node check: OK "
    f"({len(used)} annotations, {len(set(node for _, _, node in used))} numbered nodes used)"
)

