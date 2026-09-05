#!/usr/bin/env python3
"""Enforce the repo-wide declaration-keyword rules (CLAUDE.md, "Working conventions"):

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
* `Condensation/` — that paper labels nothing and no TeX source for it exists, so the
  printed number read off the committed text extraction is the key.  Its counter is
  section-scoped and shared across every environment including `definition` and
  `example`, so node numbers read `<section>.<n>` and a bare integer will not do.

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
# paper-facing `theorem` there cites `Theorem n`, `Proposition n`, `Lemma n`,
# `Corollary n` or (for the claim the paper attaches to Example 4 in prose)
# `Example n` — never a `<section>.<n>` pair.
FFS_LABEL = re.compile(
    r"Paper node:.*(Theorem|Proposition|Lemma|Corollary|Example)\s+[0-9]+")

MA_LABEL = re.compile(
    r"Paper node:.*(Theorem|Lemma|Proposition|Corollary|Condition)\s+[0-9]+\.[0-9]+"
)
# Condensation shares one section-scoped counter across every environment, so its
# node ids read `<section>.<n>` as ModalAgents' do — but `Definition` and `Example` are
# counted there, so both are accepted kinds.
CD_LABEL = re.compile(
    r"Paper node:.*(Definition|Proposition|Lemma|Theorem|Corollary|Example)"
    r"\s+[0-9]+\.[0-9]+"
)

# Factored Space Models shares one section-scoped counter across every environment and
# letters its appendix sections, so a paper-facing `theorem` cites `Lemma 4.7`,
# `Theorem 6.2`, `Corollary C.14`, … — a `<section>.<n>` pair with a numeric or lettered
# section.  A `theorem` renders a paper *result*, so `Definition` is not accepted here.
FSM_LABEL = re.compile(
    r"Paper node:.*(Theorem|Lemma|Proposition|Corollary)\s+(?:[0-9]+|[A-Z])\.[0-9]+"
)
# A declaration's `theorem` keyword can be preceded by any number of attribute blocks
# and modifiers, in any order (`private @[simp] theorem`, `@[simp] private theorem`,
# `noncomputable protected theorem`, …), and an attribute block may be split across
# lines.  `logical_lines` below rejoins those continuations first, so the matcher only
# has to accept an arbitrary prefix on a single (logical) line.
MODIFIER = (r"(?:@\[[^\]]*\]"
            r"|(?:private|protected|nonrec|noncomputable|scoped)\b)\s*")
DECL = re.compile(rf"^\s*(?P<mods>(?:{MODIFIER})*)theorem\s+(?P<name>[\w.]+)")
MODIFIERS_ONLY = re.compile(rf"^\s*(?:{MODIFIER})*\s*$")
JOINABLE = re.compile(r"^\s*(?:@\[|private\b|protected\b|nonrec\b|noncomputable\b|scoped\b)")
PRIVATE = re.compile(r"(?:^|\s)private\s")


def logical_lines(lines, depths):
    """`(start_index, text)` per declaration-carrying logical line.

    Two continuations are folded in, both of which otherwise let a `theorem` slip past
    the matcher entirely: an attribute block whose `]` lands on a later line, and an
    attribute/modifier prefix sitting alone on the line above the keyword.  Only lines
    that begin with an attribute or a modifier are ever joined, and never across a
    block comment, so ordinary code is untouched.  The reported line number is the
    first line of the group, which is where a reader looks for the declaration.
    """
    out = []
    i, n = 0, len(lines)
    while i < n:
        start, text = i, lines[i]
        if depths[i] == 0 and JOINABLE.match(text):
            # (a) attribute block left open by an unbalanced `[`
            while text.count("[") > text.count("]") and i + 1 < n and depths[i + 1] == 0:
                i += 1
                text = text.rstrip() + " " + lines[i].lstrip()
            # (b) nothing but attributes/modifiers on this line — the keyword follows
            while MODIFIERS_ONLY.match(text) and i + 1 < n and depths[i + 1] == 0:
                i += 1
                text = text.rstrip() + " " + lines[i].lstrip()
                while text.count("[") > text.count("]") and i + 1 < n and depths[i + 1] == 0:
                    i += 1
                    text = text.rstrip() + " " + lines[i].lstrip()
        out.append((start, text))
        i += 1
    return out

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
    Path("Condensation"): CD_LABEL,
    Path("FactoredSpaces"): FSM_LABEL,
}
paths = [(path, label) for library, label in libraries.items()
         for path in library.rglob("*.lean")]
for path, label in sorted(paths, key=lambda entry: entry[0]):
    lines = path.read_text().splitlines()
    depths, depth = [], 0
    for line in lines:
        depths.append(depth)  # depth at the *start* of the line
        depth = block_depth_after(line, depth)
    for i, line in logical_lines(lines, depths):
        if depths[i] > 0:  # line begins inside a block comment / docstring — prose, not a decl
            continue
        m = DECL.match(line)
        if not m:
            continue
        if PRIVATE.search(" " + m.group("mods")):
            violations.append(f"{path}:{i + 1}: private theorem {m.group('name')} (use private lemma)")
            continue
        j = i - 1
        while j >= 0 and not lines[j].strip():
            j -= 1
        if j < 0 or not lines[j].rstrip().endswith("-/"):
            violations.append(f"{path}:{i + 1}: theorem {m.group('name')} has no docstring")
            continue
        # Walk back to the line that OPENED this comment block — the first line at depth 0,
        # or line `j` itself for a one-liner — and demand it be a `/--` docstring.  A `/-!`
        # section header or a plain `/-` comment sitting above a `theorem` is not a
        # docstring, and treating it as one was a silent blind spot: the walk-back used to
        # search for `/--` and, failing to find it, ran to the top of the file, so the label
        # match then succeeded against unrelated prose anywhere above.
        k = j
        while k > 0 and depths[k] > 0:
            k -= 1
        if "/--" not in lines[k]:
            violations.append(f"{path}:{i + 1}: theorem {m.group('name')} has no docstring"
                              f" (the block above is a section header or comment, not `/--`)")
            continue
        doc = lines[k:j + 1]
        if not label.search("\n".join(doc)):
            violations.append(f"{path}:{i + 1}: theorem {m.group('name')} docstring names no paper label")

for v in violations:
    print(v)
print(f"\n{len(violations)} violation(s)." if violations else "All theorems carry paper labels.")
sys.exit(1 if violations else 0)
