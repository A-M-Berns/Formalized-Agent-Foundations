#!/usr/bin/env python3
"""Endpoint-coverage check — the converse of `check-paper-nodes.sh`.

`check-paper-nodes.sh` verifies the *inventory → paper* direction: every declaration
listed in `AxiomAudit.lean` cites a real `\\label` and carries a `Paper node:` field.
It does **not** verify the *paper → inventory* direction, which is the F9 gap: that every
paper node we claim to formalize actually has a public endpoint in the audited inventory.

This script closes that direction. For every paper label cited in any `Paper node:`
annotation under `LogicalInduction/`, it checks that at least one declaration carrying that
label is a member of the `AxiomAudit.lean` inventory (a Tier-1 `#assert_axioms_clean`
endpoint or a Tier-2 `#assert_fields` structure). A label with no inventory endpoint is a
paper theorem we annotate but never expose on the trust surface — exactly the "paper-facing
declaration outside the audit" defect.

Coverage here is a *statement-surface* check and is deliberately orthogonal to axiom
cleanliness: `AxiomAudit.lean`'s build enforces cleanliness (no stray axioms / `sorryAx`);
this script enforces completeness of the enumerated surface. The two are reported
separately on purpose — a green build plus a green coverage run are two independent claims.

Run from the repo root. Exit status is nonzero on any uncovered, non-excluded label.
"""

import re
import sys
from pathlib import Path

LIB = Path("LogicalInduction")
AUDIT = Path("AxiomAudit.lean")
CLASSIFICATION = Path("scripts/coverage-classification.md")
TIERS = {"instantiated", "universal", "qualified", "interface"}

# Labels that legitimately have no standalone endpoint of their own:
#   app:*  — appendix *proof* references, always attached to a `thm:`/`lem:` whose own
#            label carries the endpoint; the appendix is never a separate statement.
# Add labels here only with a one-line justification; the default posture is "no exclusion".
EXCLUDE_PREFIXES = ("app:",)
EXCLUDE_LABELS: dict[str, str] = {
    # e.g. "def:foo": "realized only as a private helper, not a paper statement",
}

LABEL = re.compile(r"`([a-z]+:[a-zA-Z0-9_-]+)`")
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:structure|def|theorem|lemma|abbrev|class)\s+([A-Za-z_][A-Za-z0-9_.']*)"
)


def short(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def inventory_members() -> set[str]:
    """Short-names listed in AxiomAudit.lean, up to `end LogicalInduction`.

    Tier-1: every ident on an `#assert_axioms_clean` head/continuation line.
    Tier-2: the *first* ident of each `#assert_fields` line (the struct; the rest are
    its field names, not surface members)."""
    members: set[str] = set()
    mode = None
    for line in AUDIT.read_text().splitlines():
        if line.startswith("end LogicalInduction"):
            break
        if line.startswith("#assert_axioms_clean"):
            mode = "ax"
            # idents may sit on the head line itself, e.g. `#assert_axioms_clean foo bar`
            rest = re.sub(r"^#assert_axioms_clean(_except)?\b", "", line)
            for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", rest):
                members.add(short(tok))
            continue
        if line.startswith("#assert_fields"):
            rest = line[len("#assert_fields"):].split()
            if rest:
                members.add(short(rest[0]))
            mode = None
            continue
        if mode == "ax" and re.match(r"^  [A-Za-z]", line):
            for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", line):
                members.add(short(tok))
            continue
        mode = None
    return members


def annotated_decls() -> list[tuple[set[str], str]]:
    """Every (labels, decl-shortname) pair: the labels on a `Paper node(s):` line and the
    next declaration within the following few lines."""
    out: list[tuple[set[str], str]] = []
    for path in sorted(LIB.rglob("*.lean")):
        lines = path.read_text().splitlines()
        for i, line in enumerate(lines):
            if "Paper node:" not in line and "Paper nodes:" not in line:
                continue
            labels = set(LABEL.findall(line))
            if not labels:
                continue
            # scan forward for the first declaration keyword (past the docstring `-/`)
            for j in range(i + 1, min(i + 8, len(lines))):
                m = DECL.match(lines[j])
                if m:
                    out.append((labels, short(m.group(1))))
                    break
    return out


def main() -> int:
    inv = inventory_members()
    decls = annotated_decls()

    used: set[str] = set()
    covered: set[str] = set()
    for labels, name in decls:
        used |= labels
        if name in inv:
            covered |= labels

    def excluded(lab: str) -> bool:
        return lab.startswith(EXCLUDE_PREFIXES) or lab in EXCLUDE_LABELS

    gap = sorted(lab for lab in (used - covered) if not excluded(lab))

    if gap:
        print("endpoint-coverage check: FAIL")
        print(f"  {len(gap)} paper label(s) annotated but with no AxiomAudit endpoint:")
        for lab in gap:
            carriers = sorted({n for ls, n in decls if lab in ls})
            print(f"    {lab}   (carried by: {', '.join(carriers)})")
        print("  Either add a full-strength endpoint to AxiomAudit.lean, or, if the label")
        print("  is genuinely internal, add it to EXCLUDE_LABELS with a justification.")
        return 1

    # --- 3. per-label strength classification (F9, second half) ---------------
    # scripts/coverage-classification.md must classify exactly the non-excluded labels,
    # each with a valid tier — no unclassified label, no stale row, no invented tier.
    classified: dict[str, str] = {}
    row = re.compile(r"^\|\s*([a-z]+:[a-zA-Z0-9_-]+)\s*\|\s*(\w+)\s*\|")
    for line in CLASSIFICATION.read_text().splitlines():
        m = row.match(line)
        if m:
            classified[m.group(1)] = m.group(2)
    tracked = {lab for lab in used if not excluded(lab)}
    missing = sorted(tracked - classified.keys())
    stale = sorted(classified.keys() - tracked)
    badtier = sorted((lab, t) for lab, t in classified.items() if t not in TIERS)
    if missing or stale or badtier:
        print("endpoint-coverage check: FAIL (strength classification)")
        for lab in missing:
            print(f"  unclassified label: {lab} (add a row to {CLASSIFICATION})")
        for lab in stale:
            print(f"  stale classification row: {lab} (no longer annotated)")
        for lab, t in badtier:
            print(f"  invalid tier '{t}' for {lab} (allowed: {sorted(TIERS)})")
        return 1

    n_excl = len({lab for lab in used if excluded(lab)})
    counts = {t: sum(1 for v in classified.values() if v == t) for t in sorted(TIERS)}
    print(
        f"endpoint-coverage check: OK "
        f"({len(covered)} labels have an inventory endpoint; "
        f"{n_excl} excluded appendix/internal; 0 uncovered; "
        f"strength: {', '.join(f'{k}={v}' for k, v in counts.items())})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
