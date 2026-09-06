#!/usr/bin/env python3
"""Gate the LogicalInduction roll-call and the two hypothesis tallies its prose states.

Three things drift silently and nothing else catches them.

1. **The roll-call.** `APITests/LogicalInduction.lean`'s last section elaborates every
   canonical endpoint by name, so that a move or a rename fails the client test before it
   reaches a reader.  That only works while the section names *exactly* the endpoints
   `AxiomAudit.lean`'s LI-CANONICAL block publishes; a hand-maintained pair of lists is one
   typo away from a published endpoint nobody elaborates.  This checker diffs the two sets
   in both directions, and checks that every prose count of them agrees.

2. **The `𝗜𝚺₁ ⪯ T` endpoints.** `LogicalInduction/README.md` names the canonical endpoints
   that ask for that binder — the one place the trust surface states how far the background
   theory is strengthened.  The list is recomputed here from the signatures.

3. **The `Construction/Primcodable.lean` importers.** `LogicalInduction/Construction.lean`
   states how many lane modules take the code layer directly; recomputed from the imports.

Needs neither Lean nor network.  Exit 0 clean, 1 on a violation, 2 on a broken input.
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

AUDIT = os.path.join(ROOT, "AxiomAudit.lean")
APITESTS = os.path.join(ROOT, "APITests/LogicalInduction.lean")
README = os.path.join(ROOT, "LogicalInduction/README.md")
API = os.path.join(ROOT, "LogicalInduction/API.lean")
CONSTRUCTION_MAP = os.path.join(ROOT, "LogicalInduction/Construction.lean")
COV = os.path.join(ROOT, "scripts/coverage-classification.md")
LIB = os.path.join(ROOT, "LogicalInduction")

CANON_BEGIN = "-- LI-CANONICAL-BEGIN"
CANON_END = "-- LI-CANONICAL-END"
ROLLCALL_BEGIN = "/-! ## 16. The published surface, name by name"
ROLLCALL_END = "/-! ### Documented routes beside the published endpoints"
ISIGMA_BEGIN = "<!-- ISIGMA1-ENDPOINTS-BEGIN -->"
ISIGMA_END = "<!-- ISIGMA1-ENDPOINTS-END -->"

ISIGMA_BINDER = "𝗜𝚺₁ ⪯"

NUMWORDS = {
    "one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6, "seven": 7,
    "eight": 8, "nine": 9, "ten": 10, "eleven": 11, "twelve": 12,
}

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
    r"([A-Za-z_Ͱ-￿][^\s:({\[]*)"
)


def read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def region(text, begin, end, what, path):
    i = text.find(begin)
    if i < 0:
        sys.exit("FAIL(2): %s: marker %r not found in %s" % (what, begin, path))
    j = text.find(end, i)
    if j < 0:
        sys.exit("FAIL(2): %s: marker %r not found in %s" % (what, end, path))
    return text[i + len(begin):j]


def canonical_endpoints():
    body = region(read(AUDIT), CANON_BEGIN, CANON_END, "canonical block", AUDIT)
    names = set()
    for tok in body.split():
        if tok in ("#assert_axioms_clean",):
            continue
        if not re.match(r"^[A-Za-z_][A-Za-z0-9_.'!?]*$", tok):
            sys.exit("FAIL(2): canonical block: unexpected token %r" % tok)
        names.add(tok)
    if not names:
        sys.exit("FAIL(2): canonical block parsed empty")
    return names


def rollcall_names():
    body = region(read(APITESTS), ROLLCALL_BEGIN, ROLLCALL_END, "roll-call", APITESTS)
    names = []
    for line in body.splitlines():
        s = line.strip()
        if not s or s.startswith("--") or s.startswith("/-") or s.endswith("-/"):
            continue
        m = re.match(r"^example := @([A-Za-z_][A-Za-z0-9_.'!?]*)$", s)
        if not m:
            if s.startswith("example"):
                sys.exit("FAIL(2): roll-call: unparsable entry %r" % s)
            continue
        names.append(m.group(1))
    dupes = {n for n in names if names.count(n) > 1}
    if dupes:
        sys.exit("FAIL: roll-call names a declaration twice: %s"
                 % ", ".join(sorted(dupes)))
    if not names:
        sys.exit("FAIL(2): roll-call parsed empty")
    return set(names)


def lean_files():
    for base, _dirs, files in os.walk(LIB):
        for name in sorted(files):
            if name.endswith(".lean"):
                yield os.path.join(base, name)


def declaration_signatures():
    """name -> (path, signature text), over every declaration under LogicalInduction/.

    The signature is the declaration head up to the first `:=` / `where` / `by`, which is
    where the binders live; proof bodies are excluded so a `haveI` inside one cannot be
    mistaken for a hypothesis of the statement.
    """
    sigs = {}
    file_vars = {}
    for path in lean_files():
        lines = read(path).splitlines()
        stack = []
        vars_here = []
        for idx, line in enumerate(lines):
            m = re.match(r"^namespace\s+(\S+)", line)
            if m:
                stack.append(m.group(1))
                continue
            if re.match(r"^section\b", line):
                stack.append(None)
                continue
            if re.match(r"^end\b", line):
                if stack:
                    stack.pop()
                continue
            if re.match(r"^variable\b", line) and ISIGMA_BINDER in line:
                vars_here.append(line.strip())
            m = DECL_RE.match(line)
            if not m:
                continue
            short = m.group(2)
            opened = [s for s in stack if s]
            full = ".".join(opened + [short]) if opened else short
            body = []
            for line2 in lines[idx:idx + 60]:
                body.append(line2)
                if ":=" in line2 or re.search(r"\bwhere\s*$", line2):
                    break
                if line2.strip() == "by" or line2.rstrip().endswith(" by"):
                    break
            sig = "\n".join(body)
            sig = sig.split(":=")[0]
            # Register every dotted suffix, so that a declaration written
            # `theorem BoundedSequence.expcoh_ofSyntax` inside `namespace LUVCombination`
            # resolves under the name the audit inventory uses for it.
            parts = full.split(".")
            for k in range(len(parts)):
                sigs.setdefault(".".join(parts[k:]), (path, sig))
        if vars_here:
            file_vars[path] = vars_here
    return sigs, file_vars


def isigma1_endpoints(canon):
    sigs, file_vars = declaration_signatures()
    found = set()
    for name in canon:
        entry = sigs.get(name)
        if entry is None:
            continue
        path, sig = entry
        if ISIGMA_BINDER in sig:
            found.add(name)
            continue
        # A section `variable [𝗜𝚺₁ ⪯ T]` reaches a declaration only when that declaration
        # mentions `T`, since Lean includes an instance binder with its subject.
        if path in file_vars and re.search(r"\bT\b", sig):
            found.add(name)
    return found


def readme_isigma1_names(canon):
    """The endpoints the README names as carrying the binder, and the count it states.

    Only backticked tokens that are canonical endpoints are read as list members, so the
    surrounding prose may name other declarations freely; the count is read from a fixed
    anchor phrase rather than from whichever number word comes first.
    """
    body = region(read(README), ISIGMA_BEGIN, ISIGMA_END, "README 𝗜𝚺₁ list", README)
    names = {n for n in re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)`", body) if n in canon}
    m = re.search(r"on ([a-z]+) of the published endpoints", body)
    return names, m.group(1) if m else None


MARKET_BEGIN = "<!-- MARKET-CENSUS-BEGIN -->"
MARKET_END = "<!-- MARKET-CENSUS-END -->"

# The constructed markets a statement can name, in the order the census reports them.
MARKETS = ("paperDP", "canonicalCCEEDP")


def market_census(canon):
    """How many canonical endpoints name which market, read off their signatures."""
    sigs, _ = declaration_signatures()
    counts = {"paperDP": 0, "canonicalCCEEDP": 0, "generic": 0, "none": 0}
    for name in canon:
        _path, sig = sigs[name]
        named = [m for m in MARKETS if m in sig]
        if len(named) > 1:
            # A statement naming two constructed markets is not something the census
            # sentence can describe; fail rather than pick one.
            return None, name
        if named:
            counts[named[0]] += 1
        elif "liaHistory" in sig:
            counts["generic"] += 1
        else:
            counts["none"] += 1
    return counts, None


def stated_market_census():
    body = region(read(COV), MARKET_BEGIN, MARKET_END, "market census", COV)
    def one(pat):
        m = re.search(pat, body)
        return int(m.group(1)) if m else None
    return {
        "paperDP": one(r"\*\*(\d+)\*\* at `liaHistory \(paperDP T\)`"),
        "canonicalCCEEDP": one(r"\*\*(\d+)\*\* at `liaHistory \(canonicalCCEEDP T\)`"),
        "generic": one(r"\*\*(\d+)\*\* at\s*\n?`liaHistory` over an arbitrary"),
        "none": one(r"\*\*(\d+)\*\* naming no market"),
    }


def primcodable_lane_importers():
    want = "import LogicalInduction.Construction.Primcodable"
    lanes = {}
    for path in lean_files():
        rel = os.path.relpath(path, ROOT)
        parts = rel.split(os.sep)
        # A lane module is LogicalInduction/Construction/<Lane>/<Module>.lean.
        if len(parts) != 4 or parts[1] != "Construction":
            continue
        for line in read(path).splitlines():
            if line.strip() == want:
                lanes.setdefault(parts[2], []).append(rel)
                break
    return lanes


def main():
    problems = []

    canon = canonical_endpoints()
    roll = rollcall_names()

    missing = sorted(canon - roll)
    extra = sorted(roll - canon)
    if missing:
        problems.append(
            "APITests roll-call does not elaborate %d published endpoint(s): %s"
            % (len(missing), ", ".join(missing)))
    if extra:
        problems.append(
            "APITests roll-call elaborates %d name(s) that are not published endpoints: %s"
            % (len(extra), ", ".join(extra)))

    # Every prose statement of the endpoint count must agree with the block.
    n = len(canon)
    count_re = re.compile(r"(\d+)\s+(?:canonical|published)\s+endpoints")
    for path in (README, API, APITESTS, CONSTRUCTION_MAP):
        for lineno, line in enumerate(read(path).splitlines(), 1):
            for m in count_re.finditer(line):
                if int(m.group(1)) != n:
                    problems.append(
                        "%s:%d says %s endpoints; the LI-CANONICAL block names %d"
                        % (os.path.relpath(path, ROOT), lineno, m.group(1), n))

    computed = isigma1_endpoints(canon)
    stated, word = readme_isigma1_names(canon)
    if computed != stated:
        problems.append(
            "README's `𝗜𝚺₁ ⪯ T` endpoint list is out of step with the signatures: "
            "computed {%s}, README names {%s}"
            % (", ".join(sorted(computed)), ", ".join(sorted(stated))))
    if word is None:
        problems.append(
            "README's `𝗜𝚺₁ ⪯ T` region no longer states the count in the gated form "
            "'on <word> of the published endpoints'")
    elif NUMWORDS.get(word) != len(computed):
        problems.append(
            "README's `𝗜𝚺₁ ⪯ T` region says %r; %d endpoints carry the binder"
            % (word, len(computed)))

    census, clash = market_census(canon)
    if census is None:
        problems.append(
            "%s names two constructed markets; the market census sentence in "
            "scripts/coverage-classification.md cannot describe it" % clash)
    else:
        stated = stated_market_census()
        for key in sorted(census):
            if stated.get(key) is None:
                problems.append(
                    "the market census in scripts/coverage-classification.md no longer "
                    "states the %r figure in the gated form" % key)
            elif stated[key] != census[key]:
                problems.append(
                    "the market census says %d endpoints are %r; %d are"
                    % (stated[key], key, census[key]))

    lanes = primcodable_lane_importers()
    nmods = sum(len(v) for v in lanes.values())
    nlanes = len(lanes)
    text = read(CONSTRUCTION_MAP)
    m = re.search(r"([A-Za-z]+) modules across the ((?:[^.]|\n)*?) lanes import it directly",
                  text)
    if not m:
        problems.append(
            "Construction.lean no longer states the `Primcodable` importer count in the "
            "gated form '<word> modules across the … lanes import it directly'")
    else:
        word = m.group(1).lower()
        if word not in NUMWORDS:
            problems.append("Construction.lean: %r is not a number word" % m.group(1))
        elif NUMWORDS[word] != nmods:
            problems.append(
                "Construction.lean says %s modules import `Construction/Primcodable.lean` "
                "directly; %d lane modules do (%s)"
                % (word, nmods,
                   ", ".join(sorted(r for v in lanes.values() for r in v))))
        named = set(re.findall(r"`([A-Za-z]+)/`", m.group(2)))
        if named != set(lanes):
            problems.append(
                "Construction.lean names lanes {%s} as `Primcodable` importers; the "
                "imports are in {%s}"
                % (", ".join(sorted(named)), ", ".join(sorted(lanes))))
        if nlanes != len(set(lanes)):  # defensive; keeps `nlanes` meaningful
            problems.append("internal: lane count mismatch")

    if problems:
        print("FAIL: LogicalInduction roll-call / hypothesis tallies")
        for p in problems:
            print("  - %s" % p)
        return 1

    print("OK: %d canonical endpoints, all elaborated in APITests; "
          "%d endpoint(s) carry [𝗜𝚺₁ ⪯ T]; markets %d/%d/%d/%d "
          "(paperDP/canonicalCCEEDP/generic/none); %d lane modules across %d lanes import "
          "Construction/Primcodable.lean"
          % (len(canon), len(computed), census["paperDP"], census["canonicalCCEEDP"],
             census["generic"], census["none"], nmods, nlanes))
    return 0


if __name__ == "__main__":
    sys.exit(main())
