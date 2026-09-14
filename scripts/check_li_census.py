#!/usr/bin/env python3
"""Recompute the LogicalInduction metering censuses and module counts the prose prints.

Every number below was hand-entered into a document whose whole purpose is to be
checkable, and hand-entered numbers drift.  The closing audit found five independent
count errors of exactly this kind in one pass — a class census that said 23 where the
source said 21, three field tallies that disagreed with the table printed directly
beneath them, and a module closure that was off by one — none of which any gate read.
This recomputes each of them from the Lean source and fails when a document disagrees.

What is gated
-------------
(a) **The printed-binder census on the canonical endpoints.**  For each class of the
    machine ladder, how many canonical endpoints print a binder at it and how many
    occurrences there are; and, for every fuel-, token- and value-metered class, that the
    figure is zero — printed and through a boundary structure.  Three classes the CLASS
    CENSUS reports by paper label rather than by count are checked as label *sets*, which
    is the more useful form and the easier one to get wrong.  So is the count of endpoints
    binding a `DeferralFunction` and a `FeedbackTruthComputation` — the two clocks that are
    not emission premises.  Stated in `AxiomAudit.lean`'s CLASS CENSUS block, in the
    `def:ec` row of `scripts/coverage-classification.md`, in
    `LogicalInduction/README.md`'s machine-readings paragraph, and in the `def:ec` reading
    note in `scripts/gen-trust-surface.py` that the published guide renders.

(b) **The FIELD METERING TABLE.**  Both directions: every row of the table in
    `AxiomAudit.lean` must name a structure that exists, a field that exists on it, and the
    class that field is actually stated at; and every boundary-structure field at a gated
    class must have a row.  The per-class summary lines above the table are then recomputed
    from the same parse, so the summary and the table can no longer disagree.

(c) **The module counts.**  The library's module total and the import closures of the four
    graded entry points, as printed in `LogicalInduction/README.md`, `LogicalInduction/API.lean`
    and `LogicalInduction/KNOWLEDGE.md`'s *Layout* section, plus the count of modules the
    API import does not reach.  Reachability is `check_li_file_closure.py`'s.

(d) The definition-node split and the headline theorem tiers are **not** recomputed here:
    `scripts/check_endpoint_coverage.py` owns them and gates them against the ledger's own
    strength rows.  This script only confirms that the owner's patterns still match, so a
    reworded headline section fails somewhere rather than nowhere.

Every prose figure is read through an explicit pattern, listed beside its site and a
plain-English description in the `prose` table in `main()`, and a pattern that no longer
matches is a failure in its own right — reword freely,
but keep the number greppable or update the pattern in the same commit.  A count nothing
checks is how the last wrong one survived.

Needs neither Lean nor network.  Exit 0 clean, 1 on a violation, 2 on a broken input.
"""

import os
import re
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import check_li_rollcall as roll  # noqa: E402
import check_endpoint_coverage as cov  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
AUDIT = os.path.join(ROOT, "AxiomAudit.lean")
README = os.path.join(ROOT, "LogicalInduction/README.md")
API = os.path.join(ROOT, "LogicalInduction/API.lean")
KNOWLEDGE = os.path.join(ROOT, "LogicalInduction/KNOWLEDGE.md")
LEDGER = os.path.join(ROOT, "scripts/coverage-classification.md")
GENERATOR = os.path.join(ROOT, "scripts/gen-trust-surface.py")

NUMWORDS = {
    "zero": 0, "one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6,
    "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11, "twelve": 12,
    "thirteen": 13, "fourteen": 14, "fifteen": 15, "sixteen": 16, "seventeen": 17,
    "eighteen": 18, "nineteen": 19, "twenty": 20, "twenty-one": 21, "twenty-two": 22,
    "twenty-three": 23, "twenty-four": 24, "twenty-five": 25,
}

# The machine ladder, whose census figures the prose prints.
MACHINE = [
    "MachineSentenceCodes", "MachineRatCodes", "MachineMachineCodes", "MachineDigits",
    "MachineSpliceStream", "MachineTokenStream", "MachineArithmeticSourceSeq",
    "UnaryRuler", "LUV.MachineThresholdCodes", "LUV.MachineThresholdCodeSeq",
]

# The fuel-, token- and value-metered classes.  The `def:ec` row lists exactly these by
# name and calls them "twenty-four names in all", counting the three `(Seq)` pairs once.
FUEL = [
    "BigSentenceCodes", "RpnSentenceCodes", "PolySentenceCodes", "DigitSentenceCodes",
    "BigSpliceStream", "RpnSpliceStream", "BigTokenStream", "PolySegStream",
    "PolyTokenStream", "BigDigits", "DigitMachineCodes", "DigitRatCodes", "PolyRatCodes",
    "LUV.BigThresholdCodes", "LUV.BigThresholdCodeSeq",
    "LUV.RpnThresholdCodes", "LUV.RpnThresholdCodeSeq",
    "LUV.PolyThresholdCodes", "LUV.PolyThresholdCodeSeq",
    "PolyArithmeticSourceSeq", "PolyArithmeticFormulaSeq",
    "PolyNatCodes", "PolyMachineCodes", "PolyFueled",
]

# `def:ec`'s two carriers are the fuel *certification* device, not data premises, so they
# are the one place `PolyFueled*` may occur in a canonical endpoint's signature.
FUEL_CARRIERS = ("PolyFueledTrader", "PolyFueledTrader.toEfficientlyComputable")

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.M)
ENTRY_POINTS = ("LogicalInduction.Framework", "LogicalInduction.Properties",
                "LogicalInduction.API", "LogicalInduction")


def die(msg):
    sys.exit("FAIL(2): %s" % msg)


def read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def flat(text):
    """One long line: Lean comment markers dropped, whitespace collapsed.

    The prose being read wraps across lines and, in `AxiomAudit.lean`, sits behind `--`.
    Patterns are written against the flattened form so a reflow cannot disarm one.
    """
    text = re.sub(r"(?m)^\s*--[ \t]?", "", text)
    return re.sub(r"\s+", " ", text)


def num(token):
    token = token.strip().lower().replace("*", "")
    if token in NUMWORDS:
        return NUMWORDS[token]
    if re.fullmatch(r"\d+", token):
        return int(token)
    return None


# ---------------------------------------------------------------------------
# (a) the printed-binder census on the canonical endpoints
# ---------------------------------------------------------------------------

def endpoint_census(canon, sigs):
    """class -> (endpoints printing a binder at it, total occurrences).

    Printed binders only, read off the comment-stripped signature; the transitive part
    is reported separately by `structure_reach` below, because the prose distinguishes
    "prints a binder" from "reaches one through a boundary structure".
    """
    out = {}
    for cls in MACHINE + FUEL:
        eps, occ = [], 0
        for name in sorted(canon):
            k = roll.occurrences(cls, roll.strip_comments(sigs[name][1]))
            if k:
                eps.append(name)
                occ += k
        out[cls] = (eps, occ)
    return out


def structure_reach(canon, sigs, structs):
    """(structures reachable from a canonical endpoint, fuel-metered fields among them)."""
    reached = set()
    for name in sorted(canon):
        reached |= roll.reachable_structures(roll.strip_comments(sigs[name][1]), structs)
    bad = []
    for s in sorted(reached):
        for field, (ty, line) in sorted(structs[s]["fields"].items()):
            for cls in FUEL:
                if roll.mentions(cls, ty):
                    bad.append((s, field, cls))
    return reached, bad


def binds(canon, sigs, structs, target):
    """Canonical endpoints binding the structure `target`, printed or transitively.

    The structure's own declaration is a canonical endpoint in its own right and is not
    counted: the prose says "twenty-three canonical endpoints bind a `DeferralFunction`"
    and then, separately, that `DeferralFunction` itself is the `def:deferralfunc`
    carrier, which is what makes the census block twenty-four rows.
    """
    out = []
    for name in sorted(canon):
        if name.rsplit(".", 1)[-1] == target.rsplit(".", 1)[-1]:
            continue
        sig = roll.strip_comments(sigs[name][1])
        reach = roll.reachable_structures(sig, structs)
        if roll.mentions(target, sig) or any(roll.mentions(target, s) for s in reach):
            out.append(name)
    return out


# ---------------------------------------------------------------------------
# (b) the FIELD METERING TABLE
# ---------------------------------------------------------------------------

TABLE_HEAD = "--   STRUCTURE"
TABLE_ROW = re.compile(r"^--\s{3}(\S+)\s+(\S+)\s+(\S+)")


def metering_table():
    """[(structure, field, class, line number)] from AxiomAudit's FIELD METERING TABLE."""
    rows = []
    inside = False
    for lineno, line in enumerate(read(AUDIT).splitlines(), 1):
        if line.startswith(TABLE_HEAD):
            inside = True
            continue
        if not inside:
            continue
        if line.startswith("--   ---"):
            continue
        m = TABLE_ROW.match(line)
        if not m:
            if line.strip() in ("--", ""):
                break
            continue
        rows.append((m.group(1), m.group(2), m.group(3), lineno))
    if not rows:
        die("no FIELD METERING TABLE rows found in AxiomAudit.lean")
    return rows


def field_census(structs, cls):
    """(structures, fields) carrying a field at `cls`, library-wide."""
    seen, fields = set(), 0
    for name in {d["name"] for d in structs.values()}:
        hit = sum(1 for ty, _ in structs[name]["fields"].values()
                  if roll.mentions(cls, ty))
        if hit:
            seen.add(name)
            fields += hit
    return seen, fields


# ---------------------------------------------------------------------------
# (c) module counts
# ---------------------------------------------------------------------------

def module_path(mod):
    return os.path.join(ROOT, mod.replace(".", "/") + ".lean")


def all_modules():
    mods = {"LogicalInduction"}
    for base, _dirs, files in os.walk(os.path.join(ROOT, "LogicalInduction")):
        for name in files:
            if name.endswith(".lean"):
                rel = os.path.relpath(os.path.join(base, name), ROOT)
                mods.add(rel[:-5].replace(os.sep, "."))
    return mods


def import_closure(root):
    seen, stack = set(), [root]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        for imp in IMPORT_RE.findall(read(module_path(mod))):
            if imp.startswith("LogicalInduction") and os.path.exists(module_path(imp)):
                stack.append(imp)
    return seen


# ---------------------------------------------------------------------------
# the prose sites
# ---------------------------------------------------------------------------

def main():
    problems = []
    canon = roll.canonical_endpoints()
    sigs, _ = roll.declaration_signatures()
    structs = roll.boundary_structures()
    for name in sorted(canon):
        if name not in sigs:
            die("no signature found for canonical endpoint %r" % name)

    census = endpoint_census(canon, sigs)
    reached, fuel_fields = structure_reach(canon, sigs, structs)

    # The substantive negative claim, recomputed rather than read: no canonical endpoint
    # takes a fuel-, token- or value-metered data premise, printed or through a structure.
    for cls in FUEL:
        eps = [e for e in census[cls][0] if e not in FUEL_CARRIERS]
        if eps:
            problems.append(
                "%d canonical endpoint(s) print a `%s` binder (%s); every document here "
                "states that figure as zero" % (len(eps), cls, ", ".join(eps)))
    for s, field, cls in fuel_fields:
        problems.append(
            "boundary structure `%s` is reachable from a canonical endpoint and its "
            "field `%s` is at the fuel/value class `%s`; every document here states "
            "that no such field is reachable" % (s, field, cls))

    deferral = binds(canon, sigs, structs, "DeferralFunction")
    feedback = binds(canon, sigs, structs, "FeedbackTruthComputation")

    ms_eps, ms_occ = census["MachineSentenceCodes"]
    mt_eps = sorted(set(census["LUV.MachineThresholdCodes"][0])
                    | set(census["LUV.MachineThresholdCodeSeq"][0]))

    field_counts = {}
    for cls in MACHINE:
        field_counts[cls] = field_census(structs, cls)

    thr_structs = (field_counts["LUV.MachineThresholdCodes"][0]
                   | field_counts["LUV.MachineThresholdCodeSeq"][0])
    thr_fields = (field_counts["LUV.MachineThresholdCodes"][1]
                  + field_counts["LUV.MachineThresholdCodeSeq"][1])

    mods = all_modules()
    closures = {e: len(import_closure(e)) for e in ENTRY_POINTS}
    unreached = len(mods - import_closure("LogicalInduction.API"))

    # Every entry: (file, human description, pattern, expected values).  The pattern runs
    # against `flat(file)`; each capture group is read as a number (digits or number word).
    prose = [
        # ---- (a) the printed-binder census -------------------------------------
        (AUDIT, "the CLASS CENSUS `MachineSentenceCodes` tally",
         r"`MachineSentenceCodes` — \*\*(\d+)\*\* endpoints, \*\*(\d+)\*\* occurrences",
         [len(ms_eps), ms_occ]),
        (AUDIT, "the CLASS CENSUS `BigSentenceCodes` zero",
         r"`BigSentenceCodes` — \*\*(\d+)\*\*, printed or structure-mediated",
         [0]),
        (AUDIT, "the CLASS CENSUS LUV-threshold zeroes",
         r"`LUV\.RpnThresholdCodeSeq` and `LUV\.BigThresholdCode\(Seq\)` — \*\*(\d+)\*\*",
         [0]),
        (AUDIT, "the CLASS CENSUS rational-class zeroes",
         r"`DigitRatCodes` — \*\*(\d+)\*\*, and `PolyRatCodes` — \*\*(\d+)\*\*",
         [0, 0]),
        (AUDIT, "the CLASS CENSUS digit-class zeroes",
         r"`DigitMachineCodes` — \*\*(\d+)\*\*, and `BigDigits` — \*\*(\d+)\*\*",
         [0, 0]),
        (AUDIT, "the CLASS CENSUS canonical-endpoint total",
         r"binders printed on the (\d+) canonical endpoints", [len(canon)]),
        (AUDIT, "the output-sensitive clocks' endpoint count",
         r"`FeedbackTruth\.FeedbackTruthComputation\.computes` \(tex:\d+\), on ([a-z-]+) "
         r"endpoints between them", [len(deferral)]),
        (AUDIT, "the `DeferralFunction` census",
         r"([A-Za-z-]+) canonical endpoints bind a `DeferralFunction`, ([a-z-]+) of them "
         r"a `FeedbackTruthComputation` as well", [len(deferral), len(feedback)]),
        (AUDIT, "the deferral census block's row count",
         r"so the census block lists ([a-z-]+) rows", [len(deferral) + 1]),
        (LEDGER, "the `def:ec` row's `DeferralFunction` census",
         r"\*\*([A-Za-z-]+) canonical endpoints bind a `DeferralFunction`\*\*, ([a-z-]+) "
         r"of them a `FeedbackTruthComputation` as well",
         [len(deferral), len(feedback)]),
        (LEDGER, "the `def:ec` row's deferral census row count",
         r"so the census block lists ([a-z-]+) rows", [len(deferral) + 1]),
        (GENERATOR, "the `def:ec` reading note's `DeferralFunction` census",
         r"([A-Za-z-]+) canonical endpoints bind a `DeferralFunction`", [len(deferral)]),
        (LEDGER, "the `def:ec` row's printed-binder count",
         r"Counted over the (\d+) canonical endpoints.{0,200}?"
         r"\*\*(\d+)\*\* print a `MachineSentenceCodes` binder outright",
         [len(canon), len(ms_eps)]),
        (LEDGER, "the `def:ec` row's fuel/value class-name scope",
         r"— (\w+(?:-\w+)?) names in all", [len(FUEL)]),
        (README, "the README's machine-readings sentence-lane census",
         r"all ([a-z-]+) canonical endpoints that print a sentence-codes binder print "
         r"`MachineSentenceCodes` — ([a-z-]+) occurrences", [len(ms_eps), ms_occ]),
        (GENERATOR, "the `def:ec` reading note's per-class census",
         r"\*\*(\d+)\*\* print a `MachineSentenceCodes` binder outright, "
         r"`LUV\.MachineThresholdCodeSeq` (\d+), `MachineMachineCodes` (\d+), "
         r"`MachineRatCodes` (\d+), `MachineDigits` (\d+)",
         [len(ms_eps), len(census["LUV.MachineThresholdCodeSeq"][0]),
          len(census["MachineMachineCodes"][0]), len(census["MachineRatCodes"][0]),
          len(census["MachineDigits"][0])]),
        (GENERATOR, "the `def:ec` reading note's canonical-endpoint total",
         r"Counted over the (\d+) canonical endpoints", [len(canon)]),
        # ---- (b) the field metering summary ------------------------------------
        (AUDIT, "the sentence-field summary line",
         r"\*\*(\d+)\*\* carry a sentence field at `MachineSentenceCodes`, "
         r"\*\*(\d+)\*\* fields in all",
         [len(field_counts["MachineSentenceCodes"][0]),
          field_counts["MachineSentenceCodes"][1]]),
        (AUDIT, "the threshold-field summary line",
         r"\*\*(\d+)\*\* threshold fields across \*\*(\d+)\*\* structures are at "
         r"`LUV\.MachineThresholdCodes\(Seq\)` \((\d+) fields over (\d+) structures at "
         r"the sequence form, (\d+) at the single-LUV form\)",
         [thr_fields, len(thr_structs),
          field_counts["LUV.MachineThresholdCodeSeq"][1],
          len(field_counts["LUV.MachineThresholdCodeSeq"][0]),
          field_counts["LUV.MachineThresholdCodes"][1]]),
        (AUDIT, "the rational-field summary line",
         r"\*\*([a-z]+)\*\* rational fields across \*\*([a-z]+)\*\* structures are at "
         r"`MachineRatCodes`",
         [field_counts["MachineRatCodes"][1], len(field_counts["MachineRatCodes"][0])]),
        (AUDIT, "the emission-field summary line",
         r"\*\*(\d+)\*\* emission fields across \*\*(\d+)\*\* structures are at "
         r"`MachineSpliceStream`",
         [field_counts["MachineSpliceStream"][1],
          len(field_counts["MachineSpliceStream"][0])]),
        (AUDIT, "the count-field summary line",
         r"\*\*(\d+)\*\* count fields across \*\*(\d+)\*\* structures are at `UnaryRuler`",
         [field_counts["UnaryRuler"][1], len(field_counts["UnaryRuler"][0])]),
        (README, "the README's sentence-lane structure count",
         r"the ([a-z-]+) sentence-lane boundary structures are stated at it, "
         r"([a-z-]+) fields in all",
         [len(field_counts["MachineSentenceCodes"][0]),
          field_counts["MachineSentenceCodes"][1]]),
        # ---- (c) module counts ---------------------------------------------------
        (README, "the README's module total",
         r"the count is how many of the library's (\d+) modules it elaborates",
         [len(mods)]),
        (README, "the README's `Framework` entry-point closure",
         r"\| `LogicalInduction\.Framework` \| (\d+) \|",
         [closures["LogicalInduction.Framework"]]),
        (README, "the README's `Properties` entry-point closure",
         r"\| `LogicalInduction\.Properties` \| (\d+) \|",
         [closures["LogicalInduction.Properties"]]),
        (README, "the README's `API` entry-point closure",
         r"\| `LogicalInduction\.API` \| (\d+) \|", [closures["LogicalInduction.API"]]),
        (README, "the README's roll-up entry-point closure",
         r"\| `LogicalInduction` \| (\d+) \|", [closures["LogicalInduction"]]),
        (README, "the README's unreached-module count",
         r"The ([a-z-]+) modules `LogicalInduction\.API` does not reach", [unreached]),
        (API, "API.lean's import closure and module total",
         r"Its import closure is (\d+) of the library's (\d+) modules",
         [closures["LogicalInduction.API"], len(mods)]),
        (API, "API.lean's `Framework` closure",
         r"`LogicalInduction\.Framework` \((\d+) modules",
         [closures["LogicalInduction.Framework"]]),
        (API, "API.lean's `Properties` closure",
         r"`LogicalInduction\.Properties` \((\d+),",
         [closures["LogicalInduction.Properties"]]),
        (API, "API.lean's roll-up closure",
         r"`LogicalInduction` itself \((\d+)\)", [closures["LogicalInduction"]]),
        (KNOWLEDGE, "KNOWLEDGE.md's Layout module total and closures",
         r"The library is (\d+) modules.{0,200}?four graded entry points elaborate "
         r"(\d+) / (\d+) / (\d+) / (\d+) of them",
         [len(mods)] + [closures[e] for e in ENTRY_POINTS]),
    ]

    for path, what, pattern, expected in prose:
        text = flat(read(path))
        m = re.search(pattern, text)
        rel = os.path.relpath(path, ROOT)
        if not m:
            problems.append(
                "%s no longer states %s in a recognizable form (pattern %r). Keep the "
                "number greppable or update the pattern in the same commit; a count "
                "nothing checks is how the last wrong one survived." % (rel, what, pattern))
            continue
        got = [num(g) for g in m.groups()]
        if None in got:
            problems.append("%s: %s — could not read %r as a number"
                            % (rel, what, m.groups()))
        elif got != expected:
            problems.append(
                "%s: %s says %s; the source yields %s"
                % (rel, what, ", ".join(map(str, got)), ", ".join(map(str, expected))))

    # ---- (a), the CLASS CENSUS's per-class *node* lists --------------------------
    # Three classes are censused by paper label rather than by count, which is the more
    # useful form and the easier one to get wrong: the block once said `MachineDigits`
    # was on four nodes when it is on three.  Recomputed here from the signatures.
    labels_of = {}
    for lab, cells in cov.canonical_endpoints(ROOT).items():
        for name, _note in cells:
            if name in canon:
                labels_of.setdefault(name, set()).add(lab)
    audit_flat = flat(read(AUDIT))
    label_claims = [
        ("MachineRatCodes", "the direct rational binders",
         r"Direct rational binders: `MachineRatCodes` on ((?:`[a-z]+:[a-z]+`(?:, | and )?)+)"),
        ("MachineMachineCodes", "the direct machine-code binders",
         r"`MachineMachineCodes` on ((?:`[a-z]+:[a-z]+`(?:, | and )?)+)"),
        ("MachineDigits", "the direct digit binders",
         r"`MachineDigits` on the first ([a-z]+) of those"),
    ]
    machine_code_nodes = None
    for cls, what, pattern in label_claims:
        computed = set()
        for name in census[cls][0]:
            computed |= labels_of.get(name, set())
        m = re.search(pattern, audit_flat)
        if not m:
            problems.append(
                "AxiomAudit.lean no longer states %s in a recognizable form (pattern %r). "
                "Keep the node list greppable or update the pattern in the same commit."
                % (what, pattern))
            continue
        if cls == "MachineMachineCodes":
            machine_code_nodes = re.findall(r"`([a-z]+:[a-z]+)`", m.group(1))
        if cls == "MachineDigits":
            # "on the first <n> of those" — the first n of the machine-code node list.
            n = num(m.group(1))
            if n is None or machine_code_nodes is None:
                problems.append("AxiomAudit.lean: %s — cannot resolve %r against the "
                                "machine-code node list" % (what, m.group(1)))
                continue
            stated = set(machine_code_nodes[:n])
        else:
            stated = set(re.findall(r"`([a-z]+:[a-z]+)`", m.group(1)))
        if stated != computed:
            problems.append(
                "AxiomAudit.lean: %s names {%s}; the signatures put `%s` on {%s}"
                % (what, ", ".join(sorted(stated)), cls, ", ".join(sorted(computed))))

    # ---- (b), the table itself -------------------------------------------------
    table = metering_table()
    listed = set()
    for structure, field, cls, lineno in table:
        entry = structs.get(structure)
        if entry is None:
            problems.append("AxiomAudit.lean:%d: FIELD METERING TABLE names structure "
                            "`%s`, which does not exist" % (lineno, structure))
            continue
        if field not in entry["fields"]:
            problems.append("AxiomAudit.lean:%d: FIELD METERING TABLE names field `%s` on "
                            "`%s`, which has no such field" % (lineno, field, structure))
            continue
        ty = entry["fields"][field][0]
        if not roll.mentions(cls, ty):
            problems.append(
                "AxiomAudit.lean:%d: FIELD METERING TABLE states `%s.%s` at `%s`; its type "
                "is `%s`" % (lineno, structure, field, cls, ty.strip()[:80]))
        listed.add((entry["name"], field))

    for cls in MACHINE + FUEL:
        for name in {d["name"] for d in structs.values()}:
            for field, (ty, line) in structs[name]["fields"].items():
                if roll.mentions(cls, ty) and (name, field) not in listed:
                    problems.append(
                        "%s:%d: `%s.%s` is at `%s` but has no FIELD METERING TABLE row; "
                        "the table freezes the metering class of every boundary-structure "
                        "field, so an unlisted one is unfrozen"
                        % (os.path.relpath(structs[name]["path"], ROOT), line,
                           name, field, cls))

    # ---- (d) confirm the owner's headline patterns still match ------------------
    owner = cov.check_headline_counts(Path(ROOT), cov.strength_rows(ROOT))
    for err in owner:
        problems.append("check_endpoint_coverage.py (owner of the headline counts): %s"
                        % err)

    if problems:
        print("FAIL: LogicalInduction censuses and module counts")
        for p in problems:
            print("  - %s" % p)
        return 1

    print("OK: %d canonical endpoints, %d print a `MachineSentenceCodes` binder "
          "(%d occurrences), %d a LUV machine-threshold binder; 0 print any of the %d "
          "fuel/token/value classes and none of the %d structures they reach carries a "
          "field at one; FIELD METERING TABLE %d rows all recompute; modules %d "
          "(%s)"
          % (len(canon), len(ms_eps), ms_occ, len(mt_eps), len(FUEL), len(reached),
             len(table), len(mods),
             " / ".join("%s %d" % (e.rsplit(".", 1)[-1], closures[e])
                        for e in ENTRY_POINTS)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
