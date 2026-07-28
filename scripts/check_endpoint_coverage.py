#!/usr/bin/env python3
"""Paper-node validity and endpoint coverage for the Critch PBL formalization.

Adapted from the logical-induction branch's check-paper-nodes.sh + check_endpoint_coverage.py.
Critch 2019 is a PDF source with no `\\label`s, so the label convention is §-citations
(see AxiomAudit.lean's header) and label validity is checked against the recorded section
map below instead of a TeX `\\label` sweep. Three directions:

  1. **§-citation validity** — every section number cited on a `Paper node:` line is a
     real section of Critch 2019 (map recorded below from the PDF's headings).
  2. **Inventory → annotation** — every declaration listed in `AxiomAudit.lean` (Tier-1
     `#assert_axioms_clean` endpoint or Tier-2 `#assert_fields` structure) carries a
     `Paper node:` docstring line ("infrastructure — no paper node" counts: it is an
     explicit annotation, not a missing one).
  3. **Annotation → inventory** — every section cited by any annotated declaration is
     also cited by at least one inventory endpoint (§§-ranges expanded on both sides).
     A section annotated only on internal lemmas is paper material we claim to formalize
     but never expose on the audited trust surface.

Coverage is a *statement-surface* check, deliberately orthogonal to axiom cleanliness:
`lake env lean AxiomAudit.lean` enforces cleanliness; this enforces completeness of the
enumerated surface. Run from the repo root. Exit status nonzero on any violation.
"""

import re
import sys
from pathlib import Path

LIB = Path("Critch")
AUDIT = Path("AxiomAudit.lean")
AUDIT_END = "end LO.FirstOrder.Critch"

# Section map of Critch 2019 (JSL), in paper order, from the PDF's §-headings.
SECTIONS = [
    "1", "1.1",
    "2", "2.1", "2.2", "2.3", "2.4", "2.5",
    "3", "3.1", "3.2",
    "4", "4.1", "4.2",
    "5", "6",
]

# Sections that legitimately have no inventory endpoint of their own.
# Add entries only with a one-line justification; the default posture is "no exclusion".
EXCLUDE_SECTIONS: dict[str, str] = {}

SINGLE = re.compile(r"(?<!§)§(?!§)\s*(\d+(?:\.\d+)?)")
RANGE = re.compile(r"§§\s*(\d+(?:\.\d+)?)\s*[–—-]\s*(\d+(?:\.\d+)?)")
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:structure|def|theorem|lemma|abbrev|class|instance)\s+([A-Za-z_][\w.'₀-₉]*)"
)


def short(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def expand(lo: str, hi: str, where: str, errors: list[str]) -> set[str]:
    """Sections in [lo, hi] per the paper-order map; both endpoints must be real."""
    for s in (lo, hi):
        if s not in SECTIONS:
            errors.append(f"{where}: §{s} is not a section of Critch 2019")
    if lo in SECTIONS and hi in SECTIONS:
        i, j = SECTIONS.index(lo), SECTIONS.index(hi)
        if i > j:
            errors.append(f"{where}: backwards range §§{lo}–{hi}")
            return set()
        return set(SECTIONS[i : j + 1])
    return set()


def parse_annotation(text: str, where: str, errors: list[str]) -> set[str]:
    """Validated section set cited by one `Paper node:` annotation body."""
    secs: set[str] = set()
    for lo, hi in RANGE.findall(text):
        secs |= expand(lo, hi, where, errors)
    for s in SINGLE.findall(RANGE.sub("", text)):
        if s not in SECTIONS:
            errors.append(f"{where}: §{s} is not a section of Critch 2019")
        else:
            secs.add(s)
    return secs


def inventory_members() -> set[str]:
    """Short-names listed in AxiomAudit.lean, up to `end LO.FirstOrder.Critch`.

    Tier-1: every ident on an `#assert_axioms_clean` head/continuation line.
    Tier-2: the *first* ident of each `#assert_fields` line (the struct; the rest are
    its field names, not surface members)."""
    members: set[str] = set()
    mode = None
    for line in AUDIT.read_text().splitlines():
        if line.startswith(AUDIT_END):
            break
        if line.startswith("#assert_axioms_clean"):
            mode = "ax"
            rest = re.sub(r"^#assert_axioms_clean(_except)?\b", "", line)
            for tok in re.findall(r"[A-Za-z_][\w.'₀-₉]*", rest):
                members.add(short(tok))
            continue
        if line.startswith("#assert_fields"):
            rest = line[len("#assert_fields"):].split()
            if rest:
                members.add(short(rest[0]))
            mode = None
            continue
        if mode == "ax" and re.match(r"^  [A-Za-z]", line):
            for tok in re.findall(r"[A-Za-z_][\w.'₀-₉]*", line):
                members.add(short(tok))
            continue
        mode = None
    return members


def annotated_decls(errors: list[str]) -> list[tuple[set[str], str]]:
    """Every (validated section set, decl-shortname) pair: the full `Paper node:`
    annotation body (through the closing `-/`) and the next declaration after it."""
    out: list[tuple[set[str], str]] = []
    for path in sorted(LIB.rglob("*.lean")):
        lines = path.read_text().splitlines()
        for i, line in enumerate(lines):
            if "Paper node:" not in line and "Paper nodes:" not in line:
                continue
            body = []
            end = i
            for j in range(i, min(i + 12, len(lines))):
                body.append(lines[j])
                end = j
                if lines[j].rstrip().endswith("-/"):
                    break
            secs = parse_annotation("\n".join(body), f"{path}:{i + 1}", errors)
            for j in range(end + 1, min(end + 8, len(lines))):
                m = DECL.match(lines[j])
                if m:
                    out.append((secs, short(m.group(1))))
                    break
    return out


def main() -> int:
    errors: list[str] = []
    inv = inventory_members()
    decls = annotated_decls(errors)

    # --- 1. §-citation validity (accumulated in `errors` during parsing) -----------
    if errors:
        print("paper-node check: FAIL (§-citation validity)")
        for e in errors:
            print(f"  {e}")
        return 1

    # --- 2. inventory → annotation --------------------------------------------------
    have = {name for _, name in decls}
    missing = sorted(inv - have)
    if missing:
        print("paper-node check: FAIL (inventory members without a Paper node annotation)")
        for nm in missing:
            print(f"  {nm}")
        return 1

    # --- 3. annotation → inventory --------------------------------------------------
    used: set[str] = set()
    covered: set[str] = set()
    for secs, name in decls:
        used |= secs
        if name in inv:
            covered |= secs
    gap = sorted(
        (s for s in used - covered if s not in EXCLUDE_SECTIONS),
        key=SECTIONS.index,
    )
    if gap:
        print("endpoint-coverage check: FAIL")
        print(f"  {len(gap)} cited section(s) with no AxiomAudit endpoint citing them:")
        for s in gap:
            carriers = sorted({n for ss, n in decls if s in ss})
            print(f"    §{s}   (annotated on: {', '.join(carriers)})")
        print("  Either add a full-strength endpoint to AxiomAudit.lean, or, if the section")
        print("  is genuinely internal, add it to EXCLUDE_SECTIONS with a justification.")
        return 1

    n_excl = len({s for s in used if s in EXCLUDE_SECTIONS})
    print(
        f"paper-node check: OK ({len(inv)} inventory members annotated; "
        f"{len(covered)} cited sections covered by endpoints; "
        f"{n_excl} excluded; 0 uncovered)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
