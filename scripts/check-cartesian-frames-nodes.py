#!/usr/bin/env python3
"""Check Cartesian Frames `Paper node:` annotations against the arXiv source.

The paper numbers nodes in prose rather than assigning LaTeX labels to most of them.
This checker treats the printed `(Definition|Claim|Theorem) n` as the stable source ID.
It enforces, fail-closed:

1. **Validity** — every node cited in a `Paper node:` line is actually numbered in the
   committed TeX source (a line may cite several nodes, comma-separated), and a
   `Paper node:` line that parses to *no* node at all is a violation (catches typos
   such as "Defnition 4" that would otherwise be silently ignored).
2. **Anchoring** — the literal string `Paper node:` is reserved for the audited
   surface.  Every occurrence must sit inside a `/-- … -/` declaration docstring, must
   be that docstring's last line, and that docstring must be followed by a *named*
   declaration (an anonymous `instance` cannot be inventoried, so it cannot carry an
   annotation).  Internal lemmas and worked examples cite paper nodes in prose, without
   the reserved string.
3. **Per-declaration coverage** — every annotated declaration must itself be listed in
   `AxiomAudit.lean`'s CF-INVENTORY block.  Sharing a node with some other listed
   declaration is *not* enough: the annotation claims a paper node for *this*
   statement, so this statement is what must be axiom-checked.

Declaration identity is namespace-aware: the checker tracks `namespace`/`section`/`end`
nesting to compute each declaration's fully qualified name, and matches it against the
inventory exactly (inventory entries may omit the `CartesianFrames.` root prefix, since
the block is elaborated under `open CartesianFrames in`).  There is no bare-suffix
matching — `foo` in the inventory never covers `A.B.foo` in the library.

Run from the repo root.
"""

import re
import sys
from pathlib import Path

TEX = Path("notes/2109.10996v1-main.tex")
LIB = Path("CartesianFrames")
ROOT_MODULE = Path("CartesianFrames.lean")
AUDIT = Path("AxiomAudit.lean")

NODE = re.compile(r"\\textbf\{(Definition|Claim|Theorem)\s+([0-9]+)\}")
NODE_ID = re.compile(r"(Definition|Claim|Theorem)\s+([0-9]+)")
IDENT = r"[A-Za-z_][A-Za-z0-9_.'!?₀₁₂₃₄₅₆₇₈₉]*"
NAMESPACE = re.compile(rf"^\s*namespace\s+({IDENT})")
SECTION = re.compile(rf"^\s*section\b\s*({IDENT})?")
END = re.compile(rf"^\s*end\b\s*({IDENT})?\s*$")
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|scoped|partial|unsafe|nonrec|local)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)"
    rf"\b\s*({IDENT})?"
)
MARKER = "Paper node:"


def scan(text):
    """Split a Lean source into comment-free code lines and `/-- … -/` docstrings.

    Returns `(code, docs)` where `code` maps 1-based line numbers to that line's code
    with all comments removed, and `docs` is a list of `(start_line, end_line, body)`
    for doc comments opened with `/--` (not `/-!`, which is prose, and not `/-`).
    """
    n = len(text)
    code: dict[int, str] = {}
    docs: list[tuple[int, int, str]] = []
    i, line, depth = 0, 1, 0
    doc_start_line = doc_start_index = 0
    doc_is_decl_doc = False
    while i < n:
        two = text[i:i + 2]
        if depth == 0:
            if two == "--":
                while i < n and text[i] != "\n":
                    i += 1
                continue
            if two == "/-":
                depth = 1
                doc_is_decl_doc = text[i:i + 3] == "/--"
                doc_start_line, doc_start_index = line, i
                i += 2
                continue
            if text[i] == '"':
                code[line] = code.get(line, "") + '"'
                i += 1
                while i < n:
                    if text[i] == "\\":
                        i += 2
                        continue
                    if text[i] == "\n":
                        line += 1
                    code[line] = code.get(line, "") + text[i]
                    if text[i] == '"':
                        i += 1
                        break
                    i += 1
                continue
            if text[i] == "\n":
                line += 1
            else:
                code[line] = code.get(line, "") + text[i]
            i += 1
            continue
        # inside a comment
        if two == "/-":
            depth += 1
            i += 2
            continue
        if two == "-/":
            depth -= 1
            i += 2
            if depth == 0 and doc_is_decl_doc:
                docs.append((doc_start_line, line, text[doc_start_index:i]))
            continue
        if text[i] == "\n":
            line += 1
        i += 1
    return code, docs


def namespace_prefixes(code, last_line):
    """Fully qualified namespace prefix in effect at each line, as a dict."""
    stack: list[tuple[str, str]] = []
    prefixes: dict[int, str] = {}
    for lineno in range(1, last_line + 1):
        text = code.get(lineno, "")
        m = NAMESPACE.match(text)
        if m:
            stack.append(("ns", m.group(1)))
        elif END.match(text):
            name = END.match(text).group(1)
            if name:
                while stack:
                    if stack.pop()[1] == name:
                        break
            elif stack:
                stack.pop()
        elif SECTION.match(text) and text.strip().startswith("section"):
            stack.append(("sec", SECTION.match(text).group(1) or ""))
        prefixes[lineno] = ".".join(name for kind, name in stack if kind == "ns")
    return prefixes


def following_declaration(code, end_line, last_line):
    """The `(lineno, keyword, name)` of the declaration a docstring introduces."""
    accumulated: list[str] = []
    first_line = None
    for lineno in range(end_line, last_line + 1):
        chunk = code.get(lineno, "").strip()
        if not chunk:
            continue
        if first_line is None:
            first_line = lineno
        accumulated.append(chunk)
        m = DECL.match(" ".join(accumulated))
        if m:
            return first_line, m.group(1), m.group(2)
        if len(accumulated) >= 8:
            break
    return first_line, None, None


def read_inventory():
    """Identifier tokens of CF-INVENTORY's `#assert_axioms_clean` command."""
    audit_text = AUDIT.read_text()
    match = re.search(r"-- CF-INVENTORY-BEGIN(.*?)-- CF-INVENTORY-END", audit_text, re.S)
    if match is None:
        return None
    block = re.sub(r"--[^\n]*", "", match.group(1))
    inventory: set[str] = set()
    command = None
    for token in block.split():
        if token.startswith("#"):
            command = token
        elif command == "#assert_axioms_clean" and re.fullmatch(IDENT, token):
            inventory.add(token)
    return inventory


violations: list[str] = []

source = {f"{kind} {number}" for kind, number in NODE.findall(TEX.read_text())}

inventory = read_inventory()
if inventory is None:
    violations.append(f"{AUDIT}: missing CF-INVENTORY-BEGIN/END markers")
    inventory = set()
resolved = inventory | {f"CartesianFrames.{entry}" for entry in inventory}

citations = 0
annotated_nodes: set[str] = set()

for path in [ROOT_MODULE, *sorted(LIB.rglob("*.lean"))]:
    text = path.read_text()
    lines = text.splitlines()
    code, docs = scan(text)
    prefixes = namespace_prefixes(code, len(lines))

    # Every `Paper node:` occurrence, and the docstring (if any) containing it.
    for lineno, line in enumerate(lines, start=1):
        if MARKER not in line:
            continue
        nodes = [f"{kind} {number}" for kind, number in NODE_ID.findall(line)]
        citations += len(nodes)
        annotated_nodes |= set(nodes)
        if not nodes:
            violations.append(
                f"{path}:{lineno}: MALFORMED ANNOTATION: a '{MARKER}' line naming no "
                f"'(Definition|Claim|Theorem) <number>' node"
            )
        violations += [
            f"{path}:{lineno}: INVALID NODE: {node!r} is not numbered in {TEX}"
            for node in nodes
            if node not in source
        ]
        if not any(start <= lineno <= end for start, end, _ in docs):
            violations.append(
                f"{path}:{lineno}: UNANCHORED ANNOTATION: '{MARKER}' is reserved for "
                f"declaration docstrings (`/-- … -/`); cite the paper in prose instead"
            )

    # Every annotated docstring: last-line discipline, a named carrier, inventory.
    for start, end, body in docs:
        body_lines = body.removeprefix("/--").removesuffix("-/").splitlines()
        if not any(MARKER in body_line for body_line in body_lines):
            continue
        content = [body_line for body_line in body_lines if body_line.strip()]
        if content and MARKER not in content[-1]:
            violations.append(
                f"{path}:{end}: MISPLACED ANNOTATION: the '{MARKER}' line must be the "
                f"last line of its docstring"
            )
        decl_line, keyword, name = following_declaration(code, end, len(lines))
        if keyword is None:
            violations.append(
                f"{path}:{end}: DANGLING ANNOTATION: no declaration follows this "
                f"'{MARKER}' docstring"
            )
            continue
        if not name:
            violations.append(
                f"{path}:{decl_line}: ANONYMOUS CARRIER: the annotated `{keyword}` has "
                f"no name, so it cannot be listed in {AUDIT}'s CF-INVENTORY block"
            )
            continue
        prefix = prefixes.get(decl_line, "")
        qualified = f"{prefix}.{name}" if prefix else name
        if qualified not in resolved:
            violations.append(
                f"{path}:{decl_line}: UNINVENTORIED ENDPOINT: {qualified!r} carries a "
                f"'{MARKER}' annotation but is not listed in {AUDIT}'s CF-INVENTORY block"
            )

for violation in violations:
    print(violation)

if violations:
    print(f"\n{len(violations)} violation(s).")
    sys.exit(1)

print(
    "cartesian-frames node check: OK "
    f"({citations} citations, {len(annotated_nodes)} distinct nodes, "
    f"{len(inventory)} inventoried endpoints)"
)
