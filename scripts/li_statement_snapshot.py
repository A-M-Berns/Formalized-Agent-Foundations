#!/usr/bin/env python3
"""Freeze and compare the Logical Induction statement surface.

The trust surface of `LogicalInduction/` is the set of statements a reader is asked to
check against the paper.  A refactor may rename a proof, delete a helper, or rewrite a
docstring, but it must not move a statement in that set.  This tool makes that
mechanical.

    python3 scripts/li_statement_snapshot.py snapshot OUT.txt [--extra NAME ...]
    python3 scripts/li_statement_snapshot.py diff BEFORE.txt AFTER.txt [--renames MAP]

`snapshot` collects the **freeze set** — every `Paper node:`-annotated declaration, every
name in `AxiomAudit.lean`'s LogicalInduction inventory, every `theorem` under
`LogicalInduction/`, and every declaration in `LogicalInduction/API.lean` — elaborates
`#check @name` for each (and `#print` for structures and classes, so the field surface is
frozen too) against the built oleans, and writes one block per name.  It needs a green
`lake build` of the library first; it does not build.

`diff` compares two snapshots block by block and exits nonzero if any block changed or
vanished.  `--renames MAP` names a file of `old new` lines: a renamed declaration is
compared under its new name, with the old name substituted back in its printed type, so
a sanctioned rename is not reported as a change.  New names in AFTER are listed but are
not failures — the surface may grow.
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import check_endpoint_coverage as cov  # noqa: E402
import paper_nodes  # noqa: E402

LIB = ROOT / "LogicalInduction"
API = LIB / "API.lean"
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable |protected |nonrec )*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)\s+"
    r"([^\s:({\[]+)"
)
IMPORTS = [
    "LogicalInduction",
    "LogicalInduction.API",
    "LogicalInduction.Construction.Machine",
]


def qualified_decls(path: Path, keywords: set[str]) -> list[tuple[str, str]]:
    """`(qualified name, keyword)` for every declaration in `path` whose keyword is in
    `keywords`, resolved through the file's `namespace` nesting."""
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    code, _docs = paper_nodes.scan(text)
    prefixes = paper_nodes.namespace_prefixes(code, len(lines))
    out = []
    for i in range(1, len(lines) + 1):
        # Comment-free code only: prose inside docstrings can start with a keyword.
        m = DECL.match(code.get(i, ""))
        if not m or m.group(1) not in keywords:
            continue
        name = m.group(2)
        if m.group(1) == "instance" and not re.match(r"[A-Za-z_]", name):
            continue
        if name.startswith("_root_."):
            out.append((name[len("_root_."):], m.group(1)))
        else:
            prefix = prefixes.get(i, "")
            out.append((f"{prefix}.{name}" if prefix else name, m.group(1)))
    return out


def freeze_set() -> dict[str, str]:
    """Qualified name → keyword for the whole freeze set."""
    names: dict[str, str] = {}
    for qualified, keyword, _file, _line in cov.annotated_carriers(ROOT):
        names[qualified] = keyword
    for path in sorted(LIB.rglob("*.lean")):
        for qualified, keyword in qualified_decls(path, {"theorem"}):
            names.setdefault(qualified, keyword)
    for qualified, keyword in qualified_decls(
            API, {"theorem", "lemma", "def", "abbrev", "structure", "class", "inductive"}):
        names.setdefault(qualified, keyword)
    pool = {q for q in names}
    # Inventory entries are relative names resolved the way the coverage checker does.
    all_decls: dict[str, str] = {}
    for path in sorted(LIB.rglob("*.lean")):
        for qualified, keyword in qualified_decls(
                path, {"theorem", "lemma", "def", "abbrev", "structure", "class",
                       "inductive", "instance", "opaque"}):
            all_decls.setdefault(qualified, keyword)
    big_pool = set(all_decls) | pool
    for entry in cov.tier1_entries(ROOT):
        resolved = cov._resolve_entry(entry, big_pool)
        if resolved is None:
            resolved = "LogicalInduction." + entry
        names.setdefault(resolved, all_decls.get(resolved, "def"))
    return names


def lean_file(names: dict[str, str]) -> str:
    out = [f"import {m}" for m in IMPORTS]
    out += ["set_option pp.proofs false", "set_option pp.fullNames true",
            "set_option maxHeartbeats 400000", "",
            # Inside the library namespace, so a name whose namespace the source scanner
            # could not resolve still elaborates; printed names are fully qualified anyway.
            "namespace LogicalInduction", ""]
    for name in sorted(names):
        keyword = names[name]
        out.append(f'#eval IO.println "=== {name}"')
        if keyword in ("structure", "class", "inductive"):
            out.append(f"#print {name}")
        else:
            out.append(f"#check @{name}")
    out += ["", "end LogicalInduction"]
    return "\n".join(out) + "\n"


def parse_blocks(text: str) -> dict[str, str]:
    blocks: dict[str, str] = {}
    current = None
    buf: list[str] = []
    for line in text.splitlines():
        if line.startswith("=== "):
            if current is not None:
                blocks[current] = "\n".join(buf).strip()
            current = line[4:].strip()
            buf = []
        else:
            buf.append(line)
    if current is not None:
        blocks[current] = "\n".join(buf).strip()
    return blocks


def cmd_snapshot(args: argparse.Namespace) -> int:
    names = freeze_set()
    for extra in args.extra or []:
        names.setdefault(extra, "def")
    src = lean_file(names)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=str(ROOT),
                                     prefix="LIStatementSnapshot_", delete=False) as fh:
        fh.write(src)
        tmp = fh.name
    try:
        proc = subprocess.run(["lake", "env", "lean", tmp], cwd=str(ROOT),
                              capture_output=True, text=True)
    finally:
        os.unlink(tmp)
    blocks = parse_blocks(proc.stdout)
    errors = [l for l in proc.stdout.splitlines() + proc.stderr.splitlines()
              if "error" in l]
    Path(args.out).write_text(proc.stdout, encoding="utf-8")
    print(f"snapshot: {len(names)} names in the freeze set, {len(blocks)} blocks written "
          f"to {args.out}")
    if errors:
        print(f"snapshot: {len(errors)} error lines (a name that failed to elaborate is a "
              "surface defect, not a tooling one):")
        for l in errors[:20]:
            print("  " + l)
        return 1
    if proc.returncode != 0:
        print(proc.stderr[-2000:])
        return proc.returncode
    return 0


def cmd_diff(args: argparse.Namespace) -> int:
    before = parse_blocks(Path(args.before).read_text(encoding="utf-8"))
    after = parse_blocks(Path(args.after).read_text(encoding="utf-8"))
    renames: dict[str, str] = {}
    if args.renames:
        for line in Path(args.renames).read_text(encoding="utf-8").splitlines():
            parts = line.split()
            if len(parts) == 2:
                renames[parts[0]] = parts[1]
    failures = 0
    for name, body in sorted(before.items()):
        new = renames.get(name, name)
        if new not in after:
            print(f"MISSING: {name}" + (f" (expected under {new})" if new != name else ""))
            failures += 1
            continue
        body_after = after[new]
        for old, nw in renames.items():
            body_after = re.sub(r"(?<![A-Za-z0-9_.'])" + re.escape(nw) + r"(?![A-Za-z0-9_'])",
                                old, body_after)
        if body_after.replace(new, name) != body:
            print(f"CHANGED: {name}")
            print("  before: " + body.replace("\n", "\n          "))
            print("  after:  " + after[new].replace("\n", "\n          "))
            failures += 1
    new_names = sorted(set(after) - {renames.get(n, n) for n in before})
    if new_names:
        print(f"new in AFTER ({len(new_names)}): " + ", ".join(new_names[:40])
              + (" …" if len(new_names) > 40 else ""))
    if failures:
        print(f"statement-freeze check: FAIL — {failures} frozen statement(s) moved")
        return 1
    print(f"statement-freeze check: OK ({len(before)} frozen statements unchanged, "
          f"{len(renames)} sanctioned renames)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("snapshot")
    s.add_argument("out")
    s.add_argument("--extra", nargs="*")
    s.set_defaults(fn=cmd_snapshot)
    d = sub.add_parser("diff")
    d.add_argument("before")
    d.add_argument("after")
    d.add_argument("--renames")
    d.set_defaults(fn=cmd_diff)
    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
