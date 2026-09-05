#!/usr/bin/env python3
"""Endpoint-coverage and curation check for the Logical Induction trust surface.

`check-paper-nodes.sh` verifies the *inventory → paper* direction: every declaration
listed in `AxiomAudit.lean` cites a real `\\label` and carries a `Paper node:` field.

This script closes the other directions, and — since the 2026-08 curation audit — enforces
that the three trust-surface artifacts agree with each other. They are:

  1. **provenance** — `Paper node:` docstring lines. Association is not publication.
  2. **canonical public endpoints** — the *endpoints* table of
     `scripts/coverage-classification.md`. This is what `docs/trust-surface.html` renders
     with full signatures.
  3. **strength** — the *strength* table of the same file.

The checks, all fail-closed:

  A. coverage: every non-excluded annotated label has at least one declaration in the
     `AxiomAudit.lean` inventory (Tier-1 `#assert_axioms_clean` or Tier-2 `#assert_fields`).
  A2. **per-declaration coverage**: every *declaration* carrying a `Paper node:` line is
     itself named in some `#assert_axioms_clean` block. Check A is per-*label*, and a
     label is satisfied by one carrier: a second annotated declaration for an
     already-covered label used to pass every checker while sitting in no inventory and
     under no axiom gate. That is how two applied `thm:incons` witnesses reached the
     surface unasserted (found by the R11 blind audit, closed here). This is the
     per-declaration rule the Cartesian Frames / ModalAgents / Finite Factored Sets
     checkers get from `paper_nodes.run_node_check`; LI's inventory is many small blocks
     rather than one marker-delimited block, so the rule is implemented here over the
     same `paper_nodes` scanner.
  B. curation completeness: the endpoints table and the strength table classify exactly the
     non-excluded annotated labels — no missing label, no stale row, in either table.
  C. **curation resolves**: every canonical endpoint name resolves to a declaration under
     `LogicalInduction/`. The generator used to substitute an arbitrary fallback for a name
     it could not resolve, which is how a mis-curated node stayed invisible; there is no
     fallback any more, and an unresolvable name fails here first.
  D. **curation is on-label**: every canonical endpoint carries, in its own `Paper node:`
     line, the label it is listed under.
  E. **curation is axiom-checked**: the `AxiomAudit.lean` block delimited by
     `LI-CANONICAL-BEGIN` / `LI-CANONICAL-END` names exactly the endpoints table's names,
     same spelling, no more and no less. That block is the public canonical endpoint
     inventory; every other `#assert_axioms_clean` block is an internal axiom regression
     assertion, checked by the build but not public trust surface.
  F. strength tiers are drawn from the declared vocabulary, and the secondary axis from
     its own.
  G. **the ledger's own headline counts are its rows'**: every number in
     `scripts/coverage-classification.md`'s *Headline counts* section — the theorem/lemma
     total, each per-status count, the definition-node split, the instantiated sub-count
     and its split — is recomputed from the strength table and compared. These were
     hand-entered, and one recently stood twelve nodes wrong while still adding up, because
     nothing recomputed the total from the rows. A number that disagrees fails; a sentence
     that no longer matches its pattern also fails, so a check cannot be silently lost by
     rewording. The counts live in the classification file and nowhere else: a README is a
     conceptual document, and a tally mirrored into one is a tally that outlives the thing
     it counted.

Run from the repo root. Exit status is nonzero on any violation.
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_nodes  # noqa: E402 - path fixed up just above

LIB = Path("LogicalInduction")
AUDIT = Path("AxiomAudit.lean")
CLASSIFICATION = Path("scripts/coverage-classification.md")

STATUSES = {"exact", "strengthened", "corrected", "refuted", "qualified"}
AXES = {"universal", "instantiated", "n/a"}

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
    r"(?:structure|def|theorem|lemma|abbrev|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]*)"
)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)")
END_NS = re.compile(r"^end\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$")

ROW = re.compile(r"^\|\s*([a-z]+:[a-zA-Z0-9_-]+)\s*\|(.*)\|\s*$")
ENDPOINT_CELL = re.compile(
    r"`([A-Za-z_][A-Za-z0-9_.'\u2080-\u2089]*)`\s*(\([^()]*\))?")


def short(name: str) -> str:
    return name.rsplit(".", 1)[-1]


# ----------------------------------------------------------------------------
# Shared readers — `gen-trust-surface.py` imports these, so the page and this
# check cannot be reading different curations.
# ----------------------------------------------------------------------------

def _tables(root: Path = Path(".")) -> tuple[dict, dict]:
    """(endpoints, strength) from `coverage-classification.md`.

    endpoints: label -> [(name, role note or '')], in the file's order.
    strength:  label -> {'status', 'axis', 'just'}.
    """
    endpoints: dict[str, list[tuple[str, str]]] = {}
    strength: dict[str, dict] = {}
    which = None
    for line in (root / CLASSIFICATION).read_text(encoding="utf-8").splitlines():
        if line.strip() == "<!-- table: endpoints -->":
            which = "e"
            continue
        if line.strip() == "<!-- table: strength -->":
            which = "s"
            continue
        m = ROW.match(line)
        if not m or which is None:
            continue
        lab, rest = m.group(1), m.group(2)
        if which == "e":
            # `\u0060Name\u0060 (role note)` items, `;`-separated for the human reader.
            # Parsed by structure rather than by splitting on `;`, because a role note may
            # itself contain `;`, `,` and backticked names.
            cells = [(m.group(1), (m.group(2) or "").strip())
                     for m in ENDPOINT_CELL.finditer(rest)]
            if not cells and rest.strip():
                cells = [("", rest.strip())]
            endpoints[lab] = cells
        else:
            parts = rest.split("|")
            if len(parts) < 3:
                continue
            strength[lab] = {"status": parts[0].strip(), "axis": parts[1].strip(),
                             "just": "|".join(parts[2:]).strip()}
    return endpoints, strength


def canonical_endpoints(root: Path = Path(".")) -> dict[str, list[tuple[str, str]]]:
    """label -> [(qualified name, role note)] — the curated public endpoint set."""
    return _tables(root)[0]


def strength_rows(root: Path = Path(".")) -> dict[str, dict]:
    """label -> {'status', 'axis', 'just'}."""
    return _tables(root)[1]


def audit_canonical_block(root: Path = Path(".")) -> list[str]:
    """Names inside AxiomAudit's LI-CANONICAL-BEGIN/END delimiters, in order."""
    names: list[str] = []
    inside = False
    for line in (root / AUDIT).read_text(encoding="utf-8").splitlines():
        if line.strip() == "-- LI-CANONICAL-BEGIN":
            inside = True
            continue
        if line.strip() == "-- LI-CANONICAL-END":
            inside = False
            continue
        if not inside or line.lstrip().startswith(("--", "#assert_axioms_clean")):
            if inside and line.lstrip().startswith("#assert_axioms_clean"):
                rest = re.sub(r"^\s*#assert_axioms_clean(_except)?\b", "", line)
                names += re.findall(r"[A-Za-z_][A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]*", rest)
            continue
        names += re.findall(r"[A-Za-z_][A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]*", line)
    return list(dict.fromkeys(names))


def declarations(root: Path = Path(".")) -> dict[str, dict]:
    """Qualified name -> {'file', 'line' (0-based), 'labels'} for every declaration
    under `LogicalInduction/`, namespaces resolved."""
    out: dict[str, dict] = {}
    for path in sorted((root / LIB).rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        stack: list[str] = []
        stacks: list[list[str]] = []
        for line in lines:
            m = NAMESPACE.match(line)
            if m:
                stack = stack + m.group(1).split(".")
            else:
                m2 = END_NS.match(line)
                if m2 and stack and ".".join(stack).endswith(m2.group(1)):
                    stack = stack[: len(stack) - len(m2.group(1).split("."))]
            stacks.append(list(stack))
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if not m:
                continue
            full = ".".join(stacks[i] + [m.group(1)])
            if full in out:
                continue
            # docstring above: scan back past attributes/blank lines
            labels: set[str] = set()
            j = i - 1
            while j >= 0 and (lines[j].strip().startswith(("attribute", "set_option",
                                                           "open", "@[", "include",
                                                           "variable"))
                              or lines[j].strip() == ""):
                j -= 1
            if j >= 0 and lines[j].rstrip().endswith("-/"):
                k = j
                while k >= 0 and "/--" not in lines[k]:
                    k -= 1
                doc = "\n".join(lines[k:j + 1])
                for dl in doc.splitlines():
                    if "Paper node:" in dl or "Paper nodes:" in dl:
                        labels |= set(LABEL.findall(dl))
            out[full] = {"file": str(path), "line": i, "labels": labels}
    return out


def resolve(decls: dict[str, dict], name: str) -> str | None:
    """The qualified declaration a curated name denotes, or None.

    A curated name is written the way `AxiomAudit.lean` writes it — qualified within
    `LogicalInduction`. Match the fully qualified name, then the `LogicalInduction.`-
    prefixed form, then a unique dotted-suffix match; never a bare short-name guess when
    that is ambiguous.
    """
    if name in decls:
        return name
    pref = "LogicalInduction." + name
    if pref in decls:
        return pref
    hits = [k for k in decls if k == name or k.endswith("." + name)]
    if len(hits) == 1:
        return hits[0]
    return None


# ----------------------------------------------------------------------------


def inventory_members(root: Path = Path(".")) -> set[str]:
    """Short-names listed in AxiomAudit.lean, up to `end LogicalInduction`.

    Tier-1: every ident on an `#assert_axioms_clean` head/continuation line.
    Tier-2: the *first* ident of each `#assert_fields` line (the struct; the rest are
    its field names, not surface members)."""
    members: set[str] = set()
    mode = None
    for line in (root / AUDIT).read_text(encoding="utf-8").splitlines():
        if line.startswith("end LogicalInduction"):
            break
        if line.startswith("#assert_axioms_clean"):
            mode = "ax"
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


def annotated_decls(root: Path = Path(".")) -> list[tuple[set[str], str]]:
    """Every (labels, decl-shortname) pair: the labels on a `Paper node(s):` line and the
    next declaration within the following few lines."""
    out: list[tuple[set[str], str]] = []
    for path in sorted((root / LIB).rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            if "Paper node:" not in line and "Paper nodes:" not in line:
                continue
            labels = set(LABEL.findall(line))
            if not labels:
                continue
            for j in range(i + 1, min(i + 8, len(lines))):
                m = DECL.match(lines[j])
                if m:
                    out.append((labels, short(m.group(1))))
                    break
    return out


def excluded(lab: str) -> bool:
    return lab.startswith(EXCLUDE_PREFIXES) or lab in EXCLUDE_LABELS


# ----------------------------------------------------------------------------
# A2. per-declaration inventory coverage
#
# Check A asks whether each annotated *label* has an endpoint. This asks the stricter
# question, of each annotated *declaration*: is this very name inside an
# `#assert_axioms_clean` block, hence under the axiom gate `lake build AxiomAudit`
# enforces? `#assert_fields` deliberately does NOT count: it freezes a structure's field
# names and checks no axioms, so a Tier-2 freeze alone leaves a declaration ungated.
#
# The scan is `paper_nodes`', not this file's own `declarations()`: the latter finds a
# docstring by walking back to the nearest `/--`, which happily crosses a `/-! … -/`
# section header and attributes an earlier declaration's `Paper node:` line to an
# unrelated lemma. `paper_nodes.scan` tokenizes comments properly and
# `paper_nodes.following_declaration` accumulates continuation lines, so a multi-line
# signature is not missed either.
# ----------------------------------------------------------------------------

# Annotated declarations deliberately outside the axiom gate. The default posture is "no
# exemption": an annotated declaration that is not asserted should be asserted, since
# adding a name to an internal `#assert_axioms_clean` block costs one line and disturbs
# no count (labels, not declarations, drive the classification tallies). Add an
# entry only for a declaration an assertion genuinely cannot reach — e.g. a `private`
# declaration, which `#assert_axioms_clean` cannot name from `AxiomAudit.lean` — with a
# one-line reason. Every entry is itself checked: it must name a real annotated carrier
# that really is uninventoried, so an exemption cannot outlive its cause.
PER_DECLARATION_EXEMPTIONS: dict[str, str] = {
    # e.g. "LogicalInduction.Foo.bar": "private; `#assert_axioms_clean` cannot name it",
}


def annotated_carriers(root: Path = Path(".")) -> list[tuple[str, str, str, int]]:
    """Every `Paper node:`-annotated declaration under `LogicalInduction/`.

    Returns `(qualified name, keyword, file, line)`, one entry per annotated docstring
    that introduces a named declaration.
    """
    out: list[tuple[str, str, str, int]] = []
    for path in sorted((root / LIB).rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        lines = text.splitlines()
        code, docs = paper_nodes.scan(text)
        prefixes = paper_nodes.namespace_prefixes(code, len(lines))
        for _start, end, body in docs:
            if not any("Paper node:" in bl or "Paper nodes:" in bl
                       for bl in body.splitlines()):
                continue
            decl_line, keyword, name = paper_nodes.following_declaration(
                code, end, len(lines))
            if keyword is None or not name:
                # DANGLING / ANONYMOUS carriers are reported by check-paper-nodes.sh's
                # own label pass; nothing to gate here.
                continue
            if name.startswith("_root_."):
                qualified = name[len("_root_."):]
            else:
                prefix = prefixes.get(decl_line, "")
                qualified = f"{prefix}.{name}" if prefix else name
            out.append((qualified, keyword, str(path), decl_line))
    return out


def tier1_entries(root: Path = Path(".")) -> list[str]:
    """Names listed in the LogicalInduction section's `#assert_axioms_clean` blocks.

    Spelled as written in `AxiomAudit.lean` — that file sits inside `namespace
    LogicalInduction` and `open`s several sub-namespaces, so entries are relative names
    resolved by `_resolve_entry` below, not fully qualified ones.
    """
    entries: list[str] = []
    mode = None
    for line in (root / AUDIT).read_text(encoding="utf-8").splitlines():
        if line.startswith("end LogicalInduction"):
            break
        if line.startswith("#assert_axioms_clean"):
            mode = "ax"
            rest = re.sub(r"^#assert_axioms_clean(_except)?\b", "", line)
            entries += re.findall(r"[A-Za-z_][A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]*", rest)
            continue
        if mode == "ax" and re.match(r"^  [A-Za-z]", line):
            entries += re.findall(r"[A-Za-z_][A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]*", line)
            continue
        mode = None
    return entries


def _resolve_entry(entry: str, pool: set[str]) -> str | None:
    """The declaration an inventory entry names, or None if it names none uniquely.

    Exact match, then the `LogicalInduction.`-qualified form, then a *unique* dotted
    suffix — the last is what an `open`ed namespace in `AxiomAudit.lean` needs
    (`lic_wubaff_ofFeedbackTruth` for `LogicalInduction.FeedbackEmission.…`). An
    ambiguous suffix resolves to nothing, so a listed name never launders coverage onto a
    same-short-named declaration in another namespace.
    """
    if entry in pool:
        return entry
    qualified = "LogicalInduction." + entry
    if qualified in pool:
        return qualified
    hits = [name for name in pool if name.endswith("." + entry)]
    return hits[0] if len(hits) == 1 else None


def check_per_declaration_coverage(root: Path) -> tuple[list[str], int, int]:
    """(violations, carriers checked, exemptions used)."""
    carriers = annotated_carriers(root)
    names = {name for name, _kw, _f, _ln in carriers}
    covered = {hit for entry in tier1_entries(root)
               if (hit := _resolve_entry(entry, names)) is not None}
    errs: list[str] = []
    used = 0
    for name, keyword, path, line in sorted(carriers):
        if name in covered:
            if name in PER_DECLARATION_EXEMPTIONS:
                errs.append(
                    f"per-declaration coverage check: FAIL — stale exemption: {name!r} is "
                    f"listed in PER_DECLARATION_EXEMPTIONS but is now named in an "
                    f"`#assert_axioms_clean` block; remove the exemption")
            continue
        if name in PER_DECLARATION_EXEMPTIONS:
            used += 1
            continue
        errs.append(
            f"{path}:{line}: UNINVENTORIED CARRIER: the `{keyword}` {name!r} carries a "
            f"`Paper node:` annotation but is named in no `#assert_axioms_clean` block "
            f"of {AUDIT}, so no axiom gate covers it")
    for name in sorted(PER_DECLARATION_EXEMPTIONS):
        if name not in names:
            errs.append(
                f"per-declaration coverage check: FAIL — stale exemption: {name!r} is "
                f"listed in PER_DECLARATION_EXEMPTIONS but carries no `Paper node:` "
                f"annotation under {LIB}/")
    if errs and any("UNINVENTORIED CARRIER" in e for e in errs):
        errs.append(
            "  Add each name to the `#assert_axioms_clean` block for its file in "
            f"{AUDIT} (an annotated declaration is claimed as paper-facing, so it belongs "
            "under the axiom gate). Only if an assertion is genuinely impossible, add it "
            "to PER_DECLARATION_EXEMPTIONS with a one-line reason.")
    return errs, len(carriers), used


# ----------------------------------------------------------------------------
# G. the ledger's headline counts, re-derived from the ledger's own rows
# ----------------------------------------------------------------------------

def tally(strength: dict[str, dict]) -> dict[str, dict[str, int]]:
    """Ledger counts, split the way the Headline counts section reports them.

    'thm' — theorem and lemma nodes; 'def' — definition nodes (`def:` labels), which the
    headline table deliberately keeps out; 'inst' — the theorem/lemma nodes additionally
    instantiated over the constructed inductor.
    """
    out = {"thm": {}, "def": {}, "inst": {}}
    for lab, row in strength.items():
        kind = "def" if lab.startswith("def:") else "thm"
        out[kind][row["status"]] = out[kind].get(row["status"], 0) + 1
        if kind == "thm" and row["axis"] == "instantiated":
            out["inst"][row["status"]] = out["inst"].get(row["status"], 0) + 1
    return out


def check_headline_counts(root: Path, strength: dict[str, dict]) -> list[str]:
    """Every number in the ledger's *Headline counts* section must equal its own rows.

    Those numbers were hand-entered, and hand-entered numbers drift: one recently stood
    twelve nodes wrong and happened to still add up, because nothing recomputed the total
    from the rows. So each is re-derived here from the strength table and compared.

    They are checked here, in the classification file, and nowhere else — the file that
    carries the rows is the file that may carry their tally.

    Fail-closed in both directions. A number that disagrees fails; a sentence that no
    longer matches its pattern *also* fails, rather than silently dropping a check —
    reword freely, but keep the number in a shape this can find, or update the pattern in
    the same commit.
    """
    text = re.sub(r"\s+", " ", (root / CLASSIFICATION).read_text(encoding="utf-8"))
    counts = tally(strength)
    n_thm = sum(counts["thm"].values())
    n_def = sum(counts["def"].values())
    n_inst = sum(counts["inst"].values())
    errs: list[str] = []

    def one(pattern: str, what: str, expected: list[int]) -> None:
        m = re.search(pattern, text)
        if not m:
            errs.append(
                f"headline-count check: FAIL — {CLASSIFICATION} no longer states {what} in a "
                f"recognizable form (pattern {pattern!r}). Keep the number greppable or "
                "update this pattern in the same commit; a count nothing checks is how "
                "the last wrong one survived.")
            return
        got = [int(g) for g in m.groups()]
        if got != expected:
            errs.append(
                f"headline-count check: FAIL — {CLASSIFICATION} says {what} = "
                f"{', '.join(map(str, got))}, but its own strength rows yield "
                f"{', '.join(map(str, expected))}")

    # the two totals, stated twice each in the prose
    one(r"(\d+) of the paper\'s labelled\s+results are carried as annotated nodes", "the theorem/lemma node total", [n_thm])
    one(r"over the (\d+) annotated theorem and\s+lemma nodes", "the strength-table denominator",
        [n_thm])
    # the status table itself
    for status in sorted(STATUSES):
        one(rf"\|\s*\*\*{status}\*\*\s*\|\s*(\d+)\s*\|",
            f"the {status} count", [counts["thm"].get(status, 0)])
    # definitions, kept out of that table
    one(r"paper's (\d+) \*definition\* nodes are classified separately "
        r"\((\d+) exact, (\d+) qualified\)",
        "the definition-node split",
        [n_def, counts["def"].get("exact", 0), counts["def"].get("qualified", 0)])
    # the instantiated sub-count and its own split
    one(r"Of the (\d+), \*\*(\d+) are also instantiated", "the instantiated sub-count",
        [n_thm, n_inst])
    one(r"(\d+) of them at exact or strengthened, (\d+) at qualified",
        "the instantiated split",
        [counts["inst"].get("exact", 0) + counts["inst"].get("strengthened", 0),
         counts["inst"].get("qualified", 0)])
    return errs


# Labelled paper results that are deliberately not carried as annotated nodes.
# Each is formalized in the development but cited from a module header rather than a
# `Paper node:` line, because it is appendix construction machinery rather than a
# statement the trust surface renders.  Adding a label here is a disclosure, not a
# dismissal: it must stay true that the result is worked somewhere in the library.
UNANNOTATED_PAPER_RESULTS = {
    "lem:fpl":           "MarketMaker.lean — fixed_point_lemma",
    "lem:mm":            "MarketMaker.lean — MarketMaker inexploitability",
    "lem:budgeter":      "Budgeter.lean — BudgeterAt_value_eq_of_safe, "
                         "budgetedTrader_netWorth_floor, exists_budgetedTrader_exploits "
                         "(the lemma's three parts)",
    "prop:enumeration":  "TradingFirm.lean — the trader enumeration",
    "lem:type3":         "ROI.lean — type-3 return-on-investment bound",
    "lem:type2":         "NonDogmatism.lean — the parametric-trader lemma behind the "
                         "scale ladder (module header, `## The scale ladder`)",
    "lem:conluvapprox":  "ExpectationConvergence.lean — LUV approximation",
    "lem:limexpapprox":  "ExpectationProperties.lean — limiting-expectation approximation",
}

# `restatable` is also used for definitions and for the §1 desiderata, which are not
# theorem-like results and are not expected to carry a node.
_NON_RESULT_PREFIXES = ("des:", "def:")

TEX = Path("LogicalInduction/notes/1609.03543v5-main.tex")
_TEX_ENV = re.compile(
    r"\\begin\{(?:restatable|theorem|lemma|proposition|corollary)\}"
    r"(?:\[[^\]]*\]|\{[^}]*\}|\s)*"
    r"\\label\{([^}]+)\}")


def check_paper_results_covered(root: Path, used: set[str]) -> list[str]:
    """Paper -> annotation.  Every other check runs annotation -> paper, so an
    unformalized paper result would otherwise be invisible to the whole gate suite."""
    tex = (root / TEX).read_text(encoding="utf-8")
    errs: list[str] = []
    labels = {m.group(1) for m in _TEX_ENV.finditer(tex)}
    for lab in sorted(labels):
        if lab.startswith(_NON_RESULT_PREFIXES):
            continue
        if lab in used or lab in UNANNOTATED_PAPER_RESULTS:
            continue
        errs.append(f"UNCARRIED PAPER RESULT: `{lab}` is a labelled theorem-like "
                    f"environment in the paper but is carried by no `Paper node:` line "
                    f"and is not listed in UNANNOTATED_PAPER_RESULTS")
    for lab in sorted(UNANNOTATED_PAPER_RESULTS):
        if lab not in labels:
            errs.append(f"STALE EXCUSE: `{lab}` is listed in UNANNOTATED_PAPER_RESULTS "
                        f"but is not a labelled theorem-like environment in the paper")
        if lab in used:
            errs.append(f"STALE EXCUSE: `{lab}` is listed in UNANNOTATED_PAPER_RESULTS "
                        f"but is now carried by a `Paper node:` line — remove the excuse")
    return errs


def main() -> int:
    root = Path(".")
    inv = inventory_members(root)
    decls = annotated_decls(root)

    used: set[str] = set()
    covered: set[str] = set()
    for labels, name in decls:
        used |= labels
        if name in inv:
            covered |= labels

    # --- A. every annotated label has an inventory endpoint -------------------
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

    tracked = {lab for lab in used if not excluded(lab)}
    endpoints, strength = _tables(root)
    all_decls = declarations(root)
    fail = False

    # --- A2. every annotated declaration is itself axiom-gated ----------------
    perdecl_errs, n_carriers, n_exempt = check_per_declaration_coverage(root)
    for err in perdecl_errs:
        print(err)
        fail = True

    # --- B. both tables classify exactly the tracked labels -------------------
    for what, table in (("endpoints", endpoints), ("strength", strength)):
        missing = sorted(tracked - table.keys())
        stale = sorted(table.keys() - tracked)
        for lab in missing:
            print(f"curation check: FAIL — {lab} has no row in the {what} table "
                  f"of {CLASSIFICATION}")
            fail = True
        for lab in stale:
            print(f"curation check: FAIL — stale {what} row {lab} (no longer annotated)")
            fail = True

    # --- C/D. every canonical endpoint resolves and is on-label ---------------
    curated: list[str] = []
    for lab in sorted(endpoints):
        if not endpoints[lab]:
            print(f"curation check: FAIL — {lab} has an empty canonical endpoint list; "
                  "a curated node may not fall back")
            fail = True
        for name, note in endpoints[lab]:
            if not name:
                print(f"curation check: FAIL — {lab}: unparseable endpoint cell {note!r} "
                      "(expected a `backticked.Name`)")
                fail = True
                continue
            curated.append(name)
            target = resolve(all_decls, name)
            if target is None:
                print(f"curation check: FAIL — {lab}: canonical endpoint `{name}` does "
                      "not resolve to a declaration under LogicalInduction/")
                fail = True
                continue
            if lab not in all_decls[target]["labels"]:
                have = ", ".join(sorted(all_decls[target]["labels"])) or "none"
                print(f"curation check: FAIL — {lab}: canonical endpoint `{name}` "
                      f"({target}) carries Paper node(s) {have}, not {lab}")
                fail = True

    # --- E. the audit's canonical block is exactly this set -------------------
    block = audit_canonical_block(root)
    want, got = set(curated), set(block)
    for name in sorted(want - got):
        print(f"curation check: FAIL — canonical endpoint `{name}` is not in "
              "AxiomAudit.lean's LI-CANONICAL block, so it is not axiom-checked as "
              "public surface")
        fail = True
    for name in sorted(got - want):
        print(f"curation check: FAIL — AxiomAudit.lean's LI-CANONICAL block lists "
              f"`{name}`, which is not a canonical endpoint in {CLASSIFICATION}")
        fail = True

    # --- F. vocabulary --------------------------------------------------------
    for lab, row in sorted(strength.items()):
        if row["status"] not in STATUSES:
            print(f"curation check: FAIL — {lab}: invalid status {row['status']!r} "
                  f"(allowed: {sorted(STATUSES)})")
            fail = True
        if row["axis"] not in AXES:
            print(f"curation check: FAIL — {lab}: invalid axis {row['axis']!r} "
                  f"(allowed: {sorted(AXES)})")
            fail = True

    # --- G. the ledger's headline counts match its own rows -------------------
    for err in check_headline_counts(root, strength):
        print(err)
        fail = True

    # --- H. every labelled paper result is carried, or explicitly excused ------
    for err in check_paper_results_covered(root, used):
        print(err)
        fail = True

    if fail:
        print("  The curated mapping fails closed by design: the page is generated from")
        print(f"  {CLASSIFICATION}'s endpoints table and nothing else, so a name that")
        print("  does not resolve is an error rather than a silent fallback.")
        return 1

    n_excl = len({lab for lab in used if excluded(lab)})
    counts = tally(strength)

    def fmt(d: dict[str, int]) -> str:
        return ", ".join(f"{k}={v}" for k, v in sorted(d.items()))

    print(
        f"endpoint-coverage check: OK "
        f"({len(covered)} labels have an inventory endpoint; "
        f"{n_excl} excluded appendix/internal; 0 uncovered; "
        f"{len(curated)} canonical endpoints over {len(endpoints)} nodes, all resolving, "
        f"on-label and axiom-checked; "
        f"{sum(counts['thm'].values())} theorem/lemma nodes: {fmt(counts['thm'])}; "
        f"{sum(counts['def'].values())} definition nodes: {fmt(counts['def'])}; "
        f"ledger headline counts match)"
    )
    print(
        f"per-declaration coverage check: OK "
        f"({n_carriers} annotated declarations, every one named in an "
        f"`#assert_axioms_clean` block; {n_exempt} exempt)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
