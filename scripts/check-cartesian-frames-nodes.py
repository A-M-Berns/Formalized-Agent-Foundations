#!/usr/bin/env python3
"""Check Cartesian Frames `Paper node:` annotations against the arXiv source.

The paper numbers nodes in prose rather than assigning LaTeX labels to most of them.
This checker treats the printed `(Definition|Claim|Theorem) n` as the stable source ID
and checks both directions:

* validity — every node cited in a `Paper node:` line is actually numbered in the
  committed TeX source (a `Paper node:` line may cite several nodes, comma-separated);
* coverage — every node annotated anywhere in the library is carried by at least one
  declaration listed in `AxiomAudit.lean`'s CF-INVENTORY block, so no paper node is
  claimed without a checked endpoint.
"""

import re
import sys
from pathlib import Path

TEX = Path("notes/2109.10996v1-main.tex")
LIB = Path("CartesianFrames")
AUDIT = Path("AxiomAudit.lean")
NODE = re.compile(r"\\textbf\{(Definition|Claim|Theorem)\s+([0-9]+)\}")
NODE_ID = re.compile(r"(Definition|Claim|Theorem)\s+([0-9]+)")
DOCSTRING_DECL = re.compile(
    r"/--(.*?)-/\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?"
    r"(?:private\s+)?(?:scoped\s+)?"
    r"(?:theorem|lemma|def|structure|abbrev|class|instance)\s+([\w.']+)",
    re.S,
)

source = {f"{kind} {number}" for kind, number in NODE.findall(TEX.read_text())}
violations: list[str] = []

# Direction 1: validity of every cited node, line by line.
used: list[tuple[Path, int, str]] = []
for path in [Path("CartesianFrames.lean"), *sorted(LIB.rglob("*.lean"))]:
    for line_number, line in enumerate(path.read_text().splitlines(), start=1):
        if "Paper node:" not in line:
            continue
        for kind, number in NODE_ID.findall(line):
            used.append((path, line_number, f"{kind} {number}"))

violations += [
    f"{path}:{line}: INVALID NODE: {node!r} is not numbered in {TEX}"
    for path, line, node in used
    if node not in source
]

# Direction 2: every annotated node has an inventoried endpoint carrying it.
audit_text = AUDIT.read_text()
inventory_match = re.search(
    r"-- CF-INVENTORY-BEGIN(.*?)-- CF-INVENTORY-END", audit_text, re.S
)
if inventory_match is None:
    violations.append(f"{AUDIT}: missing CF-INVENTORY-BEGIN/END markers")
    inventory: set[str] = set()
else:
    inventory = {
        token
        for token in inventory_match.group(1).split()
        if token not in {"#assert_axioms_clean"} and not token.startswith("--")
    }

def inventoried(name: str) -> bool:
    return any(
        name == inv or name.endswith("." + inv) or inv.endswith("." + name)
        for inv in inventory
    )

covered: set[str] = set()
declared: set[str] = set()
for path in sorted(LIB.rglob("*.lean")):
    for match in DOCSTRING_DECL.finditer(path.read_text()):
        doc, name = match.group(1), match.group(2)
        nodes = {
            f"{kind} {number}"
            for line in doc.splitlines()
            if "Paper node:" in line
            for kind, number in NODE_ID.findall(line)
        }
        declared |= nodes
        if inventoried(name):
            covered |= nodes

violations += [
    f"UNCOVERED NODE: {node!r} is annotated in {LIB}/ but no declaration carrying it "
    f"is listed in {AUDIT}'s CF-INVENTORY block"
    for node in sorted(declared - covered, key=lambda s: (s.split()[0], int(s.split()[1])))
]

for violation in violations:
    print(violation)

if violations:
    print(f"\n{len(violations)} violation(s).")
    sys.exit(1)

print(
    "cartesian-frames node check: OK "
    f"({len(used)} citations, {len(declared)} distinct nodes, "
    f"{len(inventory)} inventoried endpoints)"
)
