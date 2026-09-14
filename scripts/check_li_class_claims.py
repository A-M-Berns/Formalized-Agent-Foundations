#!/usr/bin/env python3
"""Gate the prose that names a metering class as a hypothesis of a LogicalInduction node.

The documentation around `def:ec` is where this library's claims are actually read, and it
is the layer nothing checked.  A strength row or a reading note that says an endpoint
"carries `BigSentenceCodes`" is a statement about the Lean source, but it is written by
hand, in a different file from the source, and stays green forever after the binder moves.
Every checked gate here reads labels, names or counts; none of them reads a *class claim*.
That is the whole defect class this closes.

What is checked
---------------
For every canonical endpoint (`AxiomAudit.lean`'s LI-CANONICAL block), the set of metering
classes it may legitimately be said to take is computed from the source:

  * the class names occurring in its elaborated signature (`declaration_signatures()`,
    comment-stripped), and
  * the class names occurring in a field type of any boundary structure the signature
    binds, transitively (`reachable_structures()`).

The prose that makes claims about that endpoint is then read:

  * its strength row in `scripts/coverage-classification.md` — the row whose first cell is
    the endpoint's paper label — and any other strength row that names the endpoint in
    backticks;
  * the `LI_READING` note for that label in `scripts/gen-trust-surface.py`, which is what
    the published guide renders on the node's card.

Any metering class the prose attributes to the endpoint *as a current hypothesis* must be
in that computed set.  Exit non-zero on any flag, with `file:line` and the reason.

"Attributes as a current hypothesis"
------------------------------------
This is the whole design problem, because the same prose legitimately names fuel classes as
producer routes, as strictness foils, and as things that are deliberately *not* binders.
The test is per sentence, and deliberately conservative — it must be possible to write the
true sentence without tripping it:

  1. The unit is a **clause**: backticked spans are masked before splitting (so
     `LUV.MachineThresholdCodes` and `tex:753-755` cannot split one in half), then the
     text is cut at sentence ends and at semicolons.  Semicolons matter — this prose
     chains several independent claims into one sentence, and reading such a sentence
     whole makes every name in it look like a claim about every other.
  2. In each clause, `CLASSES` names occurring inside a backticked span are the candidate
     attributions.  (Unbackticked prose mentions are not read as claims: the ledger uses
     bare words like "the machine classes" generically.)  Spans that are file paths are
     not read as names at all: `Construction/LUV/Syntax.lean` names no `LUV`.
  3. A clause containing any word of `EXEMPT` is not read as attributing anything.  Those
     are the vocabulary of the legitimate non-hypothesis uses: a *negative* claim ("no
     `BigSentenceCodes` binder survives"), a *producer route* or *bridge* ("reached by
     `BigSentenceCodes.toMachine`"), a *foil* ("exists only to be refuted"), and a
     *retirement* ("the `PolyRatCodes` hypotheses that once stood here are gone").  The
     exemption vocabulary is read off the prose only, never off a backticked name, so
     `not_polyNatCodes_ack` does not exempt the clause it appears in.
  4. A clause that names **no** canonical endpoint attributes nothing: the definition
     rows and the `def:ec` reading note explain the metering ladder in general terms, and
     reading those as claims about a node's carriers is how a linter cries wolf on true
     prose.  A clause that does name one is checked against the union of the endpoints it
     names and the endpoints of the row's or note's own label, and the class must occur in
     at least one of them — a node's endpoints do not all take the same premises, but a
     class occurring in none of them is not a hypothesis of the node.
  5. Endpoints that *are* metering classes (`EfficientlyComputable`, `IsLogicalInductor`,
     `PolyFueledTrader` and its inclusion) are never attribution targets: prose about them
     is prose about a class, not about a theorem's hypotheses.

Tuned so that the current files raise zero flags, and verified against a planted defect in
both sites — naming `BigSentenceCodes` on `lic_provind` in the `thm:provind` strength row
and again in its reading note; each is reported with its own `file:line`.

Needs neither Lean nor network.  Exit 0 clean, 1 on a flag, 2 on a broken input.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import check_li_rollcall as roll  # noqa: E402
import check_endpoint_coverage as cov  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(ROOT, "scripts/coverage-classification.md")
GENERATOR = os.path.join(ROOT, "scripts/gen-trust-surface.py")

# The metering vocabulary, by fully qualified name.  Every entry must resolve to a
# declaration under `LogicalInduction/`; a rename therefore fails this checker loudly
# rather than silently removing a name from the scan.
CLASSES = [
    # the machine ladder — `def:ec`'s own write-out metering
    "MachineTokenStream", "MachineSentenceCodes", "MachineSpliceStream", "MachineDigits",
    "MachineMachineCodes", "MachineRatCodes", "MachineArithmeticSourceSeq", "UnaryRuler",
    "LUV.MachineThresholdCodes", "LUV.MachineThresholdCodeSeq",
    # the fuel side
    "BigSentenceCodes", "BigDigits", "BigSpliceStream", "BigTokenStream",
    "LUV.BigThresholdCodes", "LUV.BigThresholdCodeSeq",
    "DigitRatCodes", "DigitMachineCodes", "DigitSentenceCodes",
    "RpnSentenceCodes", "RpnSpliceStream",
    "LUV.RpnThresholdCodes", "LUV.RpnThresholdCodeSeq",
    # the value side
    "PolyRatCodes", "PolySentenceCodes", "PolyMachineCodes", "PolyNatCodes",
    "LUV.PolyThresholdCodes", "LUV.PolyThresholdCodeSeq",
    "PolySegStream", "PolyTokenStream",
    "PolyArithmeticSourceSeq", "PolyArithmeticFormulaSeq", "PolyFueled",
    # the criterion classes
    "EfficientlyComputable", "IsLogicalInductor", "PolyFueledTrader",
]

# A sentence containing one of these is not read as attributing a hypothesis.  Keep this
# list small: every entry is a hole, and a wider list is a checker that passes for the
# wrong reason.
EXEMPT = (
    "not", "no", "never", "none", "nothing",
    "route", "routes", "producer", "producers", "foil", "foils",
    "bridge", "bridges", "cross", "crosses", "crossed",
    "retired", "refuted", "refutes", "gone", "deleted", "withdrawn",
    "was", "were", "used",
)
EXEMPT_RE = re.compile(r"\b(" + "|".join(EXEMPT) + r")\b", re.I)
# `toMachine` is the name of the forward bridge, so a sentence naming one is a route
# sentence whatever else it says; it is matched as a substring rather than a word.
EXEMPT_SUBSTRINGS = ("toMachine", "of_polyFueled", "ofPolyFueled")

# Canonical endpoints that ARE metering classes.  Prose naming one is prose about a
# class, not about a theorem's hypotheses, so they are never attribution targets.
CLASS_VALUED_ENDPOINTS = (
    "EfficientlyComputable",
    "PolyFueledTrader",
    "PolyFueledTrader.toEfficientlyComputable",
    "IsLogicalInductor",
)

BACKTICK = re.compile(r"`([^`]+)`")
SENTENCE_SPLIT = re.compile("(?<=[.!?])\\s+(?=[\\x01\"'(*\u2014A-Z])")


def die(msg):
    sys.exit("FAIL(2): %s" % msg)


def name_re(name):
    base = name.rsplit(".", 1)[-1]
    return re.compile(r"(?<![A-Za-z0-9_.'])(?:[A-Za-z0-9_.']*\.)?" + re.escape(base)
                      + r"(?![A-Za-z0-9_'])")


CLASS_RE = {c: name_re(c) for c in CLASSES}


def sentences(text):
    """Split `text` into sentences without letting a backticked span split one."""
    spans = []

    def mask(m):
        spans.append(m.group(0))
        # A sentinel no prose can contain, and not a digit: the ledger's own text says
        # "**22** print a `MachineSentenceCodes` binder", and a numeric placeholder is
        # indistinguishable from that.
        return "\x01%d\x01" % (len(spans) - 1)

    masked = BACKTICK.sub(mask, text)
    out = []
    for part in SENTENCE_SPLIT.split(masked):
        # Semicolons separate independent clauses in this prose, and a clause is the
        # unit an attribution lives in: "`toLUV` compiles it into `LUV`; `PaperLUVSeq`
        # compiles the threshold syntax to `LUV.MachineThresholdCodeSeq`" attributes
        # nothing to `LUV`, and reading the two clauses as one says it does.
        for clause in part.split(";"):
            out.append(re.sub(r"\x01(\d+)\x01",
                              lambda m: spans[int(m.group(1))], clause))
    return out


def backticked(sentence):
    return BACKTICK.findall(sentence)


def is_path(span):
    """A backticked file path is not a name: `Construction/LUV/Syntax.lean` names no `LUV`."""
    return "/" in span or span.endswith(".lean")


def exempt(sentence):
    if any(s in sentence for s in EXEMPT_SUBSTRINGS):
        return True
    # Read the exemption vocabulary off the prose only, never off a backticked name:
    # `not_polyNatCodes_ack` must not exempt the sentence it appears in.
    prose = BACKTICK.sub(" ", sentence)
    return EXEMPT_RE.search(prose) is not None


def ledger_rows():
    """label -> (line number, full row text), for the per-label strength table."""
    rows = {}
    inside = False
    with open(LEDGER, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            if line.strip() == "<!-- table: strength -->":
                inside = True
                continue
            if not inside:
                continue
            m = re.match(r"^\|\s*([a-z]+:[a-zA-Z0-9_-]+)\s*\|(.*)\|\s*$", line.rstrip("\n"))
            if m:
                # Only the justification cell is prose; `status` and `axis` are gated by
                # `check_endpoint_coverage.py` and have no sentences to read.
                cells = m.group(2).split("|")
                rows[m.group(1)] = (lineno, "|".join(cells[2:]).strip())
    if not rows:
        die("no strength rows found in %s" % LEDGER)
    return rows


def reading_notes():
    """label -> (line number, note text), from `gen-trust-surface.py`'s LI_READING."""
    lines = open(GENERATOR, encoding="utf-8").read().splitlines()
    try:
        start = next(i for i, l in enumerate(lines) if l.startswith("LI_READING = {"))
        end = next(i for i in range(start, len(lines)) if lines[i].startswith("}"))
    except StopIteration:
        die("could not find the LI_READING dictionary in %s" % GENERATOR)
    namespace = {}
    exec("\n".join(lines[start:end + 1]), namespace)  # noqa: S102 - our own source
    notes = namespace["LI_READING"]
    at = {}
    for i in range(start, end):
        m = re.match(r"^\s*'([a-z]+:[a-zA-Z0-9_-]+)'\s*:", lines[i])
        if m:
            at[m.group(1)] = i + 1
    missing = set(notes) - set(at)
    if missing:
        die("LI_READING keys not locatable by line: %s" % ", ".join(sorted(missing)))
    return {lab: (at[lab], notes[lab]) for lab in notes}


def main():
    canon = roll.canonical_endpoints()
    sigs, _ = roll.declaration_signatures()
    structs = roll.boundary_structures()

    for name in CLASSES:
        if not any(roll.mentions(name, roll.strip_comments(roll.read(p)))
                   for p in roll.lean_files()):
            die("metering class %r occurs nowhere under LogicalInduction/ — the "
                "vocabulary this checker scans for has gone stale, and a stale "
                "vocabulary is a checker that passes for the wrong reason." % name)

    # Which classes each endpoint may be said to take.
    allowed = {}
    for name in sorted(canon):
        entry = sigs.get(name)
        if entry is None:
            die("no signature found for canonical endpoint %r" % name)
        sig = roll.strip_comments(entry[1])
        text = sig
        for s in roll.reachable_structures(sig, structs):
            text += "\n" + "\n".join(ty for ty, _ in structs[s]["fields"].values())
        allowed[name] = {c for c in CLASSES if CLASS_RE[c].search(text)}

    for name in CLASS_VALUED_ENDPOINTS:
        if name not in canon:
            die("%r is exempted as a class-valued endpoint but is not in the "
                "LI-CANONICAL block" % name)
    targets = sorted(set(canon) - set(CLASS_VALUED_ENDPOINTS))
    if not targets:
        die("every canonical endpoint was classified as a metering class")

    # label -> canonical endpoints, from the ledger's endpoints table.
    by_label = {}
    for lab, cells in cov.canonical_endpoints(ROOT).items():
        names = [n for n, _note in cells
                 if n in canon and n not in CLASS_VALUED_ENDPOINTS]
        if names:
            by_label[lab] = names

    short = {}
    for n in targets:
        short.setdefault(n.rsplit(".", 1)[-1], []).append(n)

    def named_endpoints(sentence):
        found = set()
        for span in backticked(sentence):
            if is_path(span):
                continue
            for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", span):
                base = tok.rsplit(".", 1)[-1]
                for n in short.get(base, ()):
                    found.add(n)
        return sorted(found)

    flags = []

    def scan(where, lineno, text, label):
        own = by_label.get(label, [])
        for sentence in sentences(text):
            if exempt(sentence):
                continue
            spans = backticked(sentence)
            if not spans:
                continue
            claimed = [c for c in CLASSES
                       if any(CLASS_RE[c].search(s) for s in spans)]
            if not claimed:
                continue
            named = named_endpoints(sentence)
            if not named:
                # A sentence naming no endpoint is not read as attributing a hypothesis
                # to one.  Definition rows in particular explain the metering ladder in
                # general terms, and reading those as claims about the node's carriers
                # is how a linter ends up crying wolf on true prose.
                continue
            here = sorted(set(named) | set(own))
            for c in claimed:
                if any(c in allowed[e] for e in here):
                    continue
                flags.append(
                    "%s:%d: the %s prose attributes `%s` to %s as a current hypothesis, "
                    "but `%s` occurs in no signature, and in no bound structure field, of "
                    "%s.\n      sentence: %s"
                    % (os.path.relpath(where, ROOT), lineno, label, c,
                       " / ".join(named), c,
                       "it" if len(here) == 1 else "any of them",
                       re.sub(r"\s+", " ", sentence).strip()[:400]))

    rows = ledger_rows()
    notes = reading_notes()

    for lab in sorted(rows):
        lineno, row = rows[lab]
        scan(LEDGER, lineno, row, lab)
    for lab in sorted(notes):
        lineno, note = notes[lab]
        scan(GENERATOR, lineno, note, lab)

    if flags:
        print("FAIL: prose attributes a metering class no endpoint takes")
        for f in flags:
            print("  - %s" % f)
        return 1

    n_sites = len([lab for lab in by_label if lab in rows]) \
        + len([lab for lab in by_label if lab in notes])
    print("OK: %d canonical endpoints, %d metering classes, %d label-keyed prose sites "
          "(%d strength rows, %d reading notes); no class claim outstrips its signature"
          % (len(targets), len(CLASSES), n_sites,
             len([lab for lab in by_label if lab in rows]),
             len([lab for lab in by_label if lab in notes])))
    return 0


if __name__ == "__main__":
    sys.exit(main())
