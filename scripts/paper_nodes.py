#!/usr/bin/env python3
"""Locating paper nodes, and the Lean declarations that cite them.

This is the single implementation of each node-citation scheme registered in
`scripts/papers.py`.  Both the per-paper provenance checkers
(`check-cartesian-frames-nodes.py`, `check-modal-agents-nodes.py`) and the
trust-surface generator (`gen-trust-surface.py`) import it, so a paper's notion of
"where is node N in the source" exists exactly once.

Two directions, deliberately separated:

* **source side** — `source_nodes(scheme, tex)` gives the set of node IDs the paper
  actually numbers, and `declarations(scheme, tex)` additionally locates each node's
  printed *statement* (kind, title, body TeX, enclosing section).  The checkers need
  only the first; the generator needs the second.
* **Lean side** — `collect_annotations` walks a library, finds every `Paper node:`
  docstring marker, and resolves the fully qualified name of the declaration it
  introduces.  This is the same walk the checkers audit and the generator renders.

`run_node_check` is the checker driver: the two per-paper checkers are thin
configuration around it, and their output is unchanged by the factoring.
"""

import hashlib
import os
import re
import sys
from pathlib import Path

# --------------------------------------------------------------------------- Lean side

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


def read_inventory(audit_path, block):
    """Identifier tokens of `block`'s (`CF`/`MA`) `#assert_axioms_clean` command."""
    audit_text = Path(audit_path).read_text()
    match = re.search(rf"-- {block}-BEGIN(.*?)-- {block}-END", audit_text, re.S)
    if match is None:
        return None
    body = re.sub(r"--[^\n]*", "", match.group(1))
    inventory: set[str] = set()
    command = None
    for token in body.split():
        if token.startswith("#"):
            command = token
        elif command == "#assert_axioms_clean" and re.fullmatch(IDENT, token):
            inventory.add(token)
    return inventory


def library_sources(root_module, lib_dir):
    """The Lean files of a library, in the order the checkers walk them."""
    return [Path(root_module), *sorted(Path(lib_dir).rglob("*.lean"))]


class Annotation:
    """One `Paper node:` docstring and the declaration it introduces."""

    __slots__ = ("path", "doc_start", "doc_end", "decl_line", "keyword", "name",
                 "qualified", "nodes", "doc")

    def __init__(self, path, doc_start, doc_end, decl_line, keyword, name, qualified,
                 nodes, doc):
        self.path = path
        self.doc_start = doc_start
        self.doc_end = doc_end
        self.decl_line = decl_line
        self.keyword = keyword
        self.name = name
        self.qualified = qualified
        self.nodes = nodes
        self.doc = doc


def collect_annotations(root_module, lib_dir, node_id_re):
    """Every annotated declaration of a library, resolved to its qualified name.

    Only well-formed annotations are returned (a named carrier, at least one parsed
    node); the checkers are what report the malformed ones.  Paths are returned as
    given, so callers control absolute-vs-relative rendering.
    """
    found: list[Annotation] = []
    for path in library_sources(root_module, lib_dir):
        text = path.read_text()
        lines = text.splitlines()
        code, docs = scan(text)
        prefixes = namespace_prefixes(code, len(lines))
        for start, end, body in docs:
            body_lines = body.removeprefix("/--").removesuffix("-/").splitlines()
            marker_lines = [bl for bl in body_lines if MARKER in bl]
            if not marker_lines:
                continue
            nodes = []
            for bl in marker_lines:
                nodes += [f"{kind} {number}" for kind, number in node_id_re.findall(bl)]
            decl_line, keyword, name = following_declaration(code, end, len(lines))
            if keyword is None or not name or not nodes:
                continue
            prefix = prefixes.get(decl_line, "")
            qualified = f"{prefix}.{name}" if prefix else name
            doc = "\n".join(body_lines).strip()
            found.append(Annotation(path, start, end, decl_line, keyword, name,
                                    qualified, nodes, doc))
    return found


# ---------------------------------------------------------------------- checker driver

def run_node_check(*, tex, lib, root_module, audit, inventory_block, node_id_re,
                   source_nodes, node_shape, root_prefix=None, empty_source_message=None,
                   summary):
    """Drive one paper's provenance check; returns the process exit status.

    Every message this emits is the message the per-paper checkers emitted before the
    scheme logic was factored out here — the checkers differ only in configuration.
    """
    violations: list[str] = []

    if empty_source_message is not None and not source_nodes:
        violations.append(empty_source_message)

    inventory = read_inventory(audit, inventory_block)
    if inventory is None:
        violations.append(f"{audit}: missing {inventory_block}-BEGIN/END markers")
        inventory = set()
    resolved = inventory if root_prefix is None else (
        inventory | {f"{root_prefix}.{entry}" for entry in inventory})

    citations = 0
    annotated_nodes: set[str] = set()

    for path in library_sources(root_module, lib):
        text = path.read_text()
        lines = text.splitlines()
        code, docs = scan(text)
        prefixes = namespace_prefixes(code, len(lines))

        # Every `Paper node:` occurrence, and the docstring (if any) containing it.
        for lineno, line in enumerate(lines, start=1):
            if MARKER not in line:
                continue
            nodes = [f"{kind} {number}" for kind, number in node_id_re.findall(line)]
            citations += len(nodes)
            annotated_nodes |= set(nodes)
            if not nodes:
                violations.append(
                    f"{path}:{lineno}: MALFORMED ANNOTATION: a '{MARKER}' line naming no "
                    f"'{node_shape}' node"
                )
            violations += [
                f"{path}:{lineno}: INVALID NODE: {node!r} is not numbered in {tex}"
                for node in nodes
                if node not in source_nodes
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
                    f"no name, so it cannot be listed in {audit}'s {inventory_block} block"
                )
                continue
            prefix = prefixes.get(decl_line, "")
            qualified = f"{prefix}.{name}" if prefix else name
            if qualified not in resolved:
                violations.append(
                    f"{path}:{decl_line}: UNINVENTORIED ENDPOINT: {qualified!r} carries a "
                    f"'{MARKER}' annotation but is not listed in {audit}'s "
                    f"{inventory_block} block"
                )

    for violation in violations:
        print(violation)

    if violations:
        print(f"\n{len(violations)} violation(s).")
        return 1

    print(summary(citations=citations, nodes=annotated_nodes, source=source_nodes,
                  inventory=inventory))
    return 0


# ------------------------------------------------------------------ node-citation schemes

class Node:
    """A numbered (or labelled) result located in a paper's TeX source."""

    __slots__ = ("id", "kind", "number", "title", "body", "position")

    def __init__(self, id, kind, number, title, body, position):
        self.id = id
        self.kind = kind
        self.number = number
        self.title = title
        self.body = body
        self.position = position


# --- latex-label (Logical Induction): the source labels its own results ---------------

LATEX_LABEL_NODE_ID = re.compile(r"([A-Za-z]+):([A-Za-z0-9_]+)")


def latex_label_declarations(tex, labels):
    """Locate each requested `\\label{…}` inside its enclosing theorem environment."""
    out = {}
    for label in labels:
        pos = tex.find("\\label{%s}" % label)
        if pos < 0:
            continue
        start = tex.rfind("\\begin{", 0, pos)
        m = re.match(r"\\begin\{(\w+)\}", tex[start:])
        env = m.group(1)
        end = tex.find("\\end{%s}" % env, pos)
        body = tex[start:end]
        tm = re.match(r"\\begin\{\w+\}(?:\[([^\]]*)\])?(?:\{(\w+)\})?", body)
        title = tm.group(1) or ""
        kind = tm.group(2) or env
        body = re.sub(r"^\\begin\{\w+\}(\[[^\]]*\])?(\{\w+\})?(\{\w+\})?", "", body)
        body = re.sub(r"\\label\{[^}]*\}", "", body)
        out[label] = Node(label, kind, label, title, body.strip(), pos)
    return out


# --- printed-inline (Cartesian Frames): `\textbf{Definition 7}` in prose --------------

PRINTED_INLINE_KINDS = ("Definition", "Claim", "Theorem")
PRINTED_INLINE_SOURCE = re.compile(
    r"\\textbf\{(" + "|".join(PRINTED_INLINE_KINDS) + r")\s+([0-9]+)\}")
PRINTED_INLINE_NODE_ID = re.compile(
    r"(" + "|".join(PRINTED_INLINE_KINDS) + r")\s+([0-9]+)")
# A node is *declared* where its bold number opens a paragraph; the same bold text
# occurring mid-sentence (e.g. the footnote referring back to Definition 1) is a
# cross-reference, not a declaration.
PRINTED_INLINE_DECL = re.compile(
    r"^\s*\\noindent\s*\\textbf\{(" + "|".join(PRINTED_INLINE_KINDS) +
    r")\s+([0-9]+)\}(.*)$")
# A node's printed statement runs to the end of its own paragraph.  It ends at the
# paper's own paragraph markers, at its proof, at a sectioning command — or at the next
# `\noindent`, which is how this paper opens every following commentary paragraph.
PRINTED_INLINE_STOP = re.compile(
    r"^\s*\\(?:bigskip|medskip|smallskip|section|subsection|subsubsection|"
    r"begin\{proof\}|end\{document\}|appendix|noindent)(?![A-Za-z])")


def printed_inline_nodes(tex):
    return {f"{kind} {number}" for kind, number in PRINTED_INLINE_SOURCE.findall(tex)}


def _strip_node_preamble(rest):
    """Peel a declaration line's optional `(Title)`, `\\label{…}` and separating dot."""
    title = ""
    while True:
        stripped = rest.lstrip()
        if stripped.startswith("(") and ")" in stripped:
            close = stripped.index(")")
            title = stripped[1:close].strip()
            rest = stripped[close + 1:]
            continue
        m = re.match(r"\\label\{[^}]*\}", stripped)
        if m:
            rest = stripped[m.end():]
            continue
        if stripped.startswith("."):
            rest = stripped[1:]
            continue
        return title, stripped


def printed_inline_declarations(tex):
    """Every `Definition n` / `Claim n` / `Theorem n` with its printed statement."""
    lines = tex.splitlines()
    starts = []
    for idx, line in enumerate(lines):
        m = PRINTED_INLINE_DECL.match(line)
        if m:
            starts.append((idx, m))
    out = {}
    offsets = []
    running = 0
    for line in lines:
        offsets.append(running)
        running += len(line) + 1
    for k, (idx, m) in enumerate(starts):
        kind, number, rest = m.group(1), m.group(2), m.group(3)
        title, rest = _strip_node_preamble(rest)
        body = [rest] if rest.strip() else []
        for j in range(idx + 1, len(lines)):
            if PRINTED_INLINE_STOP.match(lines[j]) or PRINTED_INLINE_DECL.match(lines[j]):
                break
            body.append(lines[j])
        text = "\n".join(body).strip()
        # A few nodes print their parenthesised title on the line *below* the number.
        if not title:
            first, _, rest = text.partition("\n")
            tm = re.fullmatch(r"\(([^()]*)\)\.?", first.strip())
            if tm:
                title, text = tm.group(1).strip(), rest.strip()
        node_id = f"{kind} {number}"
        out[node_id] = Node(node_id, kind, number, title, text, offsets[idx])
    return out


# --- printed-counter (ModalAgents): numbers derived by emulating \newtheorem ----------

PRINTED_COUNTER_ENVS = ("theorem", "lemma", "proposition", "corollary", "condition")
PRINTED_COUNTER_BEGIN = re.compile(r"\\begin\{(" + "|".join(PRINTED_COUNTER_ENVS) + r")\}")
# `Definition` is accepted by the *parser* so that citing one yields a precise
# INVALID NODE rather than a vague MALFORMED ANNOTATION; this paper numbers none.
PRINTED_COUNTER_NODE_ID = re.compile(
    r"(Definition|Theorem|Lemma|Proposition|Corollary|Condition)\s+([0-9]+(?:\.[0-9]+)?)"
)


def strip_tex_comment(line):
    """Drop a TeX line's comment, respecting `\\%`."""
    out = []
    k = 0
    while k < len(line):
        if line[k] == "\\" and k + 1 < len(line):
            out.append(line[k:k + 2])
            k += 2
            continue
        if line[k] == "%":
            break
        out.append(line[k])
        k += 1
    return "".join(out)


def printed_counter_nodes(tex_text):
    """The paper's printed node IDs, by emulating its LaTeX counters.

    `\\newtheorem{theorem}{Theorem}[section]` resets the theorem counter whenever the
    section counter steps, and `lemma`/`proposition`/`corollary`/`condition` are declared
    `[theorem]`, so they share it.  A starred `\\section*` does not step the section
    counter, so it does not reset the theorem counter either.
    """
    nodes = set()
    section = theorem = 0
    for raw in tex_text.splitlines():
        line = strip_tex_comment(raw)
        for match in re.finditer(r"\\section(\*?)|" + PRINTED_COUNTER_BEGIN.pattern, line):
            if match.group(0).startswith("\\section"):
                if match.group(1) != "*":
                    section += 1
                    theorem = 0
                continue
            theorem += 1
            nodes.add(f"{match.group(2).capitalize()} {section}.{theorem}")
    return nodes


def printed_counter_declarations(tex_text):
    """Every counted environment with its number, optional title and body TeX."""
    stripped = "\n".join(strip_tex_comment(raw) for raw in tex_text.splitlines())
    out = {}
    section = theorem = 0
    pattern = re.compile(r"\\section(\*?)|" + PRINTED_COUNTER_BEGIN.pattern)
    for match in pattern.finditer(stripped):
        if match.group(0).startswith("\\section"):
            if match.group(1) != "*":
                section += 1
                theorem = 0
            continue
        env = match.group(2)
        theorem += 1
        node_id = f"{env.capitalize()} {section}.{theorem}"
        end = stripped.find("\\end{%s}" % env, match.end())
        body = stripped[match.end():end if end >= 0 else len(stripped)]
        title = ""
        tm = re.match(r"\s*\[((?:[^\[\]]|\[[^\]]*\])*)\]", body)
        if tm:
            title = tm.group(1).strip()
            body = body[tm.end():]
        body = re.sub(r"\\label\{[^}]*\}", "", body)
        out[node_id] = Node(node_id, env.capitalize(),
                            "%d.%d" % (section, theorem), title, body.strip(),
                            match.start())
    return out


SCHEMES = {
    "latex-label": {
        "node_id_re": LATEX_LABEL_NODE_ID,
        "source_nodes": lambda tex: set(re.findall(r"\\label\{([^}]*)\}", tex)),
        "declarations": None,  # label-driven; see latex_label_declarations
    },
    "printed-inline": {
        "node_id_re": PRINTED_INLINE_NODE_ID,
        "source_nodes": printed_inline_nodes,
        "declarations": printed_inline_declarations,
    },
    "printed-counter": {
        "node_id_re": PRINTED_COUNTER_NODE_ID,
        "source_nodes": printed_counter_nodes,
        "declarations": printed_counter_declarations,
    },
}


# ------------------------------------------------------- trust-surface freshness inputs

def trust_surface_inputs(root):
    """Every file the trust-surface page is generated from, in a stable order.

    The generator hashes exactly this list into the page and
    `scripts/check_trust_surface.py` recomputes it, so the two cannot drift.  It covers
    the shared tooling, and — per registered paper — the committed source, the prose the
    page quotes (README, knowledge base, errata, coverage table) and **every Lean file of
    the library**, since the page renders those files' `Paper node:` annotations and
    statement signatures.

    Kept free of third-party imports: the freshness check must run in CI without the
    generator's `latex2mathml` dependency.
    """
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from papers import PAPERS  # noqa: PLC0415 - deliberately local, see docstring

    root = str(root).rstrip("/") + "/"
    files = [
        "scripts/papers.py",
        "scripts/paper_nodes.py",
        "scripts/gen-trust-surface.py",
        "scripts/trust-surface-template.html",
        "AxiomAudit.lean",
    ]
    for key in sorted(PAPERS):
        paper = PAPERS[key]
        for field in ("source", "coverage_table", "readme", "knowledge", "errata"):
            rel = paper.get(field)
            if rel:
                files.append(rel)
        lib = paper["library"]
        files.append("%s.lean" % lib)
        files += sorted(
            os.path.relpath(os.path.join(dirpath, name), root).replace(os.sep, "/")
            for dirpath, _, names in os.walk(os.path.join(root, lib))
            for name in names
            if name.endswith(".lean")
        )
    # De-duplicate while keeping order: a file may be named by two registry fields.
    seen = set()
    ordered = []
    for rel in files:
        if rel not in seen and os.path.exists(root + rel):
            seen.add(rel)
            ordered.append(rel)
    return ordered


def trust_surface_hash(root):
    """SHA-256 over `trust_surface_inputs`, path-qualified so renames are visible."""
    h = hashlib.sha256()
    for rel in trust_surface_inputs(root):
        h.update(rel.encode("utf-8"))
        h.update(b"\0")
        h.update(open(str(root).rstrip("/") + "/" + rel, "rb").read())
        h.update(b"\0")
    return h.hexdigest()
