#!/usr/bin/env python3
"""Regenerate the node-by-node table in LogicalInduction/README.md.

The table's content is derived, never hand-maintained:

* the **paper order**, the **printed name** and the **label** come from
  `LogicalInduction/notes/1609.03543v5-main.tex` (the order is the order the labelled
  environments appear in the source);
* the **Lean carriers** come from the *endpoints* table of
  `scripts/coverage-classification.md` — the same list `AxiomAudit.lean`'s
  `LI-CANONICAL` block is checked against, so the README cannot name an endpoint the
  inventory does not publish;
* the **module** of each carrier is found by scanning `LogicalInduction/` for its
  declaration;
* the **tier** comes from the *strength* table of `scripts/coverage-classification.md`.

Run `python3 scripts/gen-li-node-table.py --write` after any change to those inputs; the
generated block sits between the `<!-- NODE-TABLE-BEGIN -->` and `<!-- NODE-TABLE-END -->`
markers in the README.  With no `--write` the script prints the block and exits non-zero if
the README is out of date, which is what CI runs.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TEX = os.path.join(ROOT, "LogicalInduction/notes/1609.03543v5-main.tex")
COV = os.path.join(ROOT, "scripts/coverage-classification.md")
README = os.path.join(ROOT, "LogicalInduction/README.md")
BEGIN = "<!-- NODE-TABLE-BEGIN -->"
END = "<!-- NODE-TABLE-END -->"

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|public|noncomputable|partial|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)")


TEXMACRO = [("\\LIA", "LIA"), ("\\MP", "\u2119"), ("\\LItitle", "logical inductor"),
            ("\\LICtitle", "logical induction criterion"), ("\\ec", "e.c."),
            ("\\pgenable", "\u2119-generable"), ("\\seq", ""), ("\\fuz", "\u03dd")]


def clean_tex(s):
    for a, b in TEXMACRO:
        s = s.replace(a, b)
    s = re.sub(r"\\texorpdfstring\{([^{}]*)\}\{([^{}]*)\}", r"\2", s)
    s = re.sub(r"\\[A-Za-z]+", "", s)
    return s.replace("$", "").replace("{", "").replace("}", "").strip()


def paper_nodes():
    """[(label, printed name, environment)] in the order the source declares them."""
    out, seen = [], set()
    text = open(TEX, encoding="utf-8").read()
    begin = re.compile(r"\\begin\{([A-Za-z]+)\}")
    label = re.compile(r"\\label\{([a-z]+:[A-Za-z0-9_]+)\}")
    for m in begin.finditer(text):
        env = m.group(1)
        if env not in ("restatable", "theorem", "lemma", "definition", "keydef", "defalg",
                       "proposition", "corollary"):
            continue
        head = text[m.end():m.end() + 300]
        head = head.split("\n\n")[0]
        stop = head.find("\\begin{")
        if stop >= 0:
            head = head[:stop]
        printed = ""
        if head.startswith("["):
            depth, i = 0, 0
            for i, ch in enumerate(head):
                if ch == "[":
                    depth += 1
                elif ch == "]":
                    depth -= 1
                    if depth == 0:
                        break
            printed = clean_tex(head[1:i])
            head = head[i + 1:]
        for lm in label.finditer(head):
            lab = lm.group(1)
            if lab in seen:
                continue
            seen.add(lab)
            out.append((lab, printed, env))
    return out


def cov_tables():
    """(endpoints, tiers) keyed by label."""
    endpoints, tiers = {}, {}
    section = None
    for line in open(COV, encoding="utf-8"):
        if line.startswith("<!-- table: "):
            section = line.split()[2]
            continue
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 2 or cells[0] in ("label", "---") or set(cells[0]) <= {"-"}:
            continue
        if section == "endpoints":
            endpoints[cells[0]] = cells[1]
        elif section == "strength" and len(cells) >= 2:
            tiers[cells[0]] = cells[1]
    return endpoints, tiers


def decl_modules():
    """base declaration name -> module path (first match wins, deterministic order)."""
    where = {}
    for dirpath, dirnames, filenames in os.walk(os.path.join(ROOT, "LogicalInduction")):
        dirnames.sort()
        for fn in sorted(filenames):
            if not fn.endswith(".lean"):
                continue
            p = os.path.join(dirpath, fn)
            rel = os.path.relpath(p, ROOT)
            for line in open(p, encoding="utf-8"):
                m = DECL.match(line)
                if m:
                    where.setdefault(m.group(1), rel)
                    where.setdefault(m.group(1).split(".")[-1], rel)
    return where


def carrier_names(cell):
    """Backticked names in the cell, with the parenthetical role notes stripped."""
    prev = None
    while prev != cell:
        prev = cell
        cell = re.sub(r"\([^()]*\)", "", cell)
    return re.findall(r"`([^`]+)`", cell)


def build():
    endpoints, tiers = cov_tables()
    where = decl_modules()
    rows = []
    for lab, printed, kind in paper_nodes():
        if lab not in endpoints:
            continue
        names = carrier_names(endpoints[lab])
        mods = []
        for n in names:
            base = n.split(".")[-1]
            m = where.get(n) or where.get(base)
            if m and m not in mods:
                mods.append(m)
        carriers = "; ".join("`%s`" % n for n in names)
        modcell = "; ".join(m[len("LogicalInduction/"):] for m in mods) or "—"
        rows.append("| `%s` | %s | %s | %s | %s |" %
                    (lab, printed or "—", carriers, modcell, tiers.get(lab, "—")))
    head = ["| label | printed name | Lean carrier(s) | module | tier |",
            "|---|---|---|---|---|"]
    return "\n".join(head + rows)


def main():
    block = build()
    text = open(README, encoding="utf-8").read()
    i, j = text.find(BEGIN), text.find(END)
    if i < 0 or j < 0:
        sys.stderr.write("README markers not found\n")
        return 2
    current = text[i + len(BEGIN):j].strip("\n")
    if "--write" in sys.argv:
        open(README, "w", encoding="utf-8").write(
            text[:i + len(BEGIN)] + "\n" + block + "\n" + text[j:])
        print("node table written: %d rows" % (block.count("\n") - 1))
        return 0
    if current != block:
        sys.stderr.write("node table in README.md is stale; run with --write\n")
        return 1
    print("node table check: OK (%d rows)" % (block.count("\n") - 1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
