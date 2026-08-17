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


INVENTORY_COMMAND = re.compile(r"#assert_[A-Za-z_][A-Za-z0-9_]*")

# Tokens that are identifier-shaped but are Lean syntax, not declaration names.  A
# declaration accidentally written inside the marker block is the failure this list
# exists to catch: `lemma foo : True := trivial` is four identifier-shaped tokens, and
# an inventory reader that merely filters on `IDENT` absorbs all four — after which the
# gate believes `foo` is axiom-checked when nothing checks it.  A *qualified* name is
# never bare-equal to one of these (`Condensation.end` is one token, not `end`), so
# rejecting the bare forms cannot reject a real entry.
INVENTORY_KEYWORDS = frozenset({
    "abbrev", "attribute", "axiom", "by", "class", "declare_syntax_cat", "def",
    "deriving", "do", "elab", "else", "end", "example", "extends", "fun", "have",
    "if", "import", "in", "inductive", "infix", "infixl", "infixr", "initialize",
    "instance", "let", "local", "macro", "macro_rules", "match", "mutual",
    "namespace", "nonrec", "notation", "noncomputable", "opaque", "open", "partial",
    "postfix", "prefix", "private", "protected", "scoped", "section", "set_option",
    "structure", "syntax", "then", "theorem", "lemma", "unsafe", "variable",
    "variables", "where", "with",
})


class Inventory:
    """The parse of one `-- <BLOCK>-BEGIN/END` `#assert_axioms_clean` block.

    `names` is the set of declaration names the block's `#assert_axioms_clean` command
    checks.  `problems` is a list of ready-to-print violation messages, one per token
    that is not legitimately part of an `#assert_*` command, already carrying
    `path:line:` — a caller reports them as violations rather than absorbing them, so a
    Lean declaration written inside the markers cannot silently disarm the gate.
    """

    __slots__ = ("names", "problems")

    def __init__(self, names, problems):
        self.names = names
        self.problems = problems


def read_inventory(audit_path, block):
    """Parse `block`'s `#assert_axioms_clean` command into an `Inventory`.

    Returns `None` when the markers are absent, otherwise an `Inventory`.  The block
    body (comments stripped) is tokenised and every token must be one of:

    * an `#assert_*` command;
    * an identifier-shaped declaration name inside such a command's argument list — the
      names of `#assert_axioms_clean` are what `Inventory.names` collects, and the
      arguments of any other `#assert_*` command are accepted but not collected, exactly
      as before;
    * a well-formed `open <Namespace>… in` prefix group immediately preceding an
      `#assert_*` command.

    Anything else — a Lean keyword, an `@[…]` attribute, a non-identifier token, a
    stray name before any command — is a violation reported in `Inventory.problems`,
    and it *disarms* the command it interrupted: every following token is rejected too
    until the next `#assert_*` command.  That cascade is the point.  Rejecting only the
    keyword of a smuggled `lemma foo : True := trivial` would still let `foo`, `True`
    and `trivial` into `names`, which is most of the original hole; disarming rejects
    all four and collects none.

    No `-BEGIN/-END` block in this repository contains an `open … in` prefix today; it
    is permitted (only in that strict prefix position, never inside an argument list)
    because `#assert_axioms_clean` may legitimately need one, and rejecting it there
    would be a trap for a later editor rather than a protection.
    """
    audit_text = Path(audit_path).read_text()
    match = re.search(rf"-- {block}-BEGIN(.*?)-- {block}-END", audit_text, re.S)
    if match is None:
        return None
    first_line = audit_text.count("\n", 0, match.start(1)) + 1
    names: set[str] = set()
    problems: list[str] = []

    def reject(lineno, token, why):
        # One contaminating token disarms the rest of the command, so a smuggled
        # declaration reports many lines.  Spell the rationale out on the first one
        # only; repeating it fourteen times buries the token that actually caused it.
        rationale = "" if problems else (
            f".  The {block} block may hold nothing but `#assert_*` commands, the "
            f"declaration names they check, and an `open … in` prefix before a command; "
            f"anything else — a Lean declaration written inside the markers, say — "
            f"would be absorbed into the inventory and silently disarm the gate.  Every "
            f"token after this one is rejected too, until the next `#assert_*` command"
        )
        problems.append(
            f"{audit_path}:{lineno}: INVENTORY BLOCK CONTAMINATED: {token!r} {why}"
            f"{rationale}"
        )

    command = None
    # Set once a token has been rejected, and cleared by the next `#assert_*` command.
    # Rejecting the keyword alone is not enough: `lemma foo : True := trivial` would
    # still contribute `foo`, `True` and `trivial`, which is most of the original hole.
    # A contaminating token therefore disarms the rest of the command's argument list,
    # so every token of the smuggled declaration is reported and none is collected.
    disarmed = False
    # `None` outside an `open … in` prefix; `'names'` while consuming the namespaces;
    # `'in'` once `in` is seen and the next token must be the command it prefixes.
    open_state = None
    for offset, raw in enumerate(match.group(1).split("\n")):
        lineno = first_line + offset
        for token in re.sub(r"--[^\n]*", "", raw).split():
            if open_state == "names":
                if token == "in":
                    open_state = "in"
                elif re.fullmatch(IDENT, token) and token not in INVENTORY_KEYWORDS:
                    pass  # a namespace being opened
                else:
                    open_state, disarmed = None, True
                    reject(lineno, token,
                           "is not a namespace name inside an `open … in` prefix")
                continue
            if open_state == "in":
                open_state = None
                if INVENTORY_COMMAND.fullmatch(token):
                    command, disarmed = token, False
                else:
                    disarmed = True
                    reject(lineno, token, "follows an `open … in` prefix but is not an "
                                          "`#assert_*` command")
                continue
            if token.startswith("#"):
                if INVENTORY_COMMAND.fullmatch(token):
                    command, disarmed = token, False
                else:
                    command, disarmed = None, True
                    reject(lineno, token, "is not an `#assert_*` command")
                continue
            if token == "open":
                command, disarmed = None, False
                open_state = "names"
                continue
            if token.startswith("@[") or token in INVENTORY_KEYWORDS:
                command, disarmed = None, True
                reject(lineno, token,
                       "is Lean syntax (a keyword or attribute), not a declaration name")
                continue
            if not re.fullmatch(IDENT, token):
                command, disarmed = None, True
                reject(lineno, token, "is not identifier-shaped")
                continue
            if command is None:
                reject(lineno, token,
                       "follows a rejected token, so it is not inside an `#assert_*` "
                       "command's argument list" if disarmed else
                       "appears before any `#assert_*` command")
                continue
            if command == "#assert_axioms_clean":
                names.add(token)
    if open_state is not None:
        problems.append(
            f"{audit_path}:{first_line}: INVENTORY BLOCK CONTAMINATED: the {block} "
            f"block ends inside an unfinished `open … in` prefix"
        )
    return Inventory(names, problems)


class Pending:
    """The parse of one `-- <BLOCK>-BEGIN/END` staging block.

    `entries` maps each staged declaration name to the reason given for it (the rest of
    its line, with a leading `--` peeled off).  `consumers` is the same mapping for the
    block's `SECTION: consumers` half: declarations that depend on a `sorry` but carry
    no `Paper node:` annotation of their own, so they are not endpoints and the
    endpoint-coverage rules do not apply to them, yet the ledger must still name them.
    A block with no section marker leaves `consumers` empty.

    `problems` is a list of ready-to-print violation messages, one per malformed line,
    already carrying `path:line:` — a caller reports them as violations rather than
    silently dropping the lines, so the block cannot degrade into a place to hide
    things.
    """

    __slots__ = ("entries", "consumers", "problems")

    def __init__(self, entries, problems, consumers=None):
        self.entries = entries
        self.problems = problems
        self.consumers = {} if consumers is None else consumers


PENDING_SECTION = re.compile(r"^SECTION:\s*(\S.*)$")
# The section a `-- SECTION: <label>` line switches to, keyed by the label's first word
# (so `SECTION: consumers (un-annotated)` and a bare `SECTION: consumers` are the same
# section, and the parenthetical is free prose).
PENDING_SECTIONS = {
    "annotated": "entries",
    "consumers": "consumers",
    "endpoints": "entries",
    "main": "entries",
}


def read_pending(audit_path, block):
    """Declaration names staged in `block`'s `-- <block>-BEGIN/END` comment block.

    The block is *pure comment* — it holds declarations that are annotated endpoints but
    whose proofs are still `sorry`, so they cannot be listed in `#assert_axioms_clean`:

        -- CONDENSATION-PENDING-BEGIN
        -- Condensation.LatentModel.perfect_tfae_A     -- M2: proof pending
        -- CONDENSATION-PENDING-END

    Returns `None` when the markers are absent (which is *not* the same as an empty
    block, which returns a `Pending` with no entries), otherwise a `Pending`.  Every
    non-blank line strictly between the markers must be a `--` comment whose first token
    is identifier-shaped (that token is the declaration name) and which gives a non-empty
    reason after that name, and names no declaration twice; each line failing any of
    those is reported in `Pending.problems` rather than skipped.

    The block has a second, optional half, opened by a section line:

        -- SECTION: consumers (un-annotated)
        -- Condensation.LatentModel.entropy_joint_le_condScore  -- consumes (4.7)-(4.9)

    Its lines obey exactly the same rules and land in `Pending.consumers` instead, and
    a name may not be repeated across the two halves.  The section is for declarations
    that depend on a `sorry` but carry *no* `Paper node:` annotation: they are not
    endpoints, so the endpoint rules do not apply to them, but the sorry-ledger must
    still be able to name them.  The section-line test runs *before* the declaration-name
    test, since `SECTION` is itself identifier-shaped and would otherwise parse as a
    staged declaration called `SECTION`.  A block with no section line parses exactly as
    it did before this half existed.
    """
    audit_text = Path(audit_path).read_text()
    match = re.search(rf"-- {block}-BEGIN(.*?)-- {block}-END", audit_text, re.S)
    if match is None:
        return None
    first_line = audit_text.count("\n", 0, match.start(1)) + 1
    entries: dict[str, str] = {}
    consumers: dict[str, str] = {}
    problems: list[str] = []
    current = entries
    for offset, raw in enumerate(match.group(1).split("\n")):
        lineno = first_line + offset
        line = raw.strip()
        if not line:
            continue
        if not line.startswith("--"):
            problems.append(
                f"{audit_path}:{lineno}: MALFORMED PENDING ENTRY: every line of the "
                f"{block} block must be a `--` comment, but this one is code"
            )
            continue
        content = line[2:].strip()
        section_match = PENDING_SECTION.match(content)
        if section_match is not None:
            label = section_match.group(1).strip()
            key = re.split(r"[^A-Za-z]", label, 1)[0].lower()
            target = PENDING_SECTIONS.get(key)
            if target is None:
                problems.append(
                    f"{audit_path}:{lineno}: UNKNOWN PENDING SECTION: {label!r} is not a "
                    f"section of the {block} block; the known sections are "
                    + ", ".join(sorted(PENDING_SECTIONS))
                )
                continue
            current = consumers if target == "consumers" else entries
            continue
        name_match = re.match(rf"({IDENT})", content)
        if name_match is None:
            problems.append(
                f"{audit_path}:{lineno}: MALFORMED PENDING ENTRY: no declaration name "
                f"at the start of this {block} entry"
            )
            continue
        name = name_match.group(1)
        reason = re.sub(r"^--\s*", "", content[name_match.end():].strip()).strip()
        if not reason:
            problems.append(
                f"{audit_path}:{lineno}: MALFORMED PENDING ENTRY: {name!r} is staged in "
                f"the {block} block with no reason given"
            )
            continue
        if name in entries or name in consumers:
            problems.append(
                f"{audit_path}:{lineno}: DUPLICATE PENDING ENTRY: {name!r} is staged "
                f"twice in the {block} block"
            )
            continue
        current[name] = reason
    return Pending(entries, problems, consumers)


def library_sources(root_module, lib_dir):
    """The Lean files of a library, in the order the checkers walk them.

    A library registered `in-progress` may not have its aggregator module yet, so a
    missing root module is skipped rather than raised: an annotation check over a
    library with no Lean is vacuous, not broken.  That the library exists and contains
    Lean at all is `scripts/check_paper_wiring.py`'s job, and it is checked there.
    """
    paths = [Path(root_module), *sorted(Path(lib_dir).rglob("*.lean"))]
    return [path for path in paths if path.is_file()]


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
                   summary, scope_manifest=None, inventory_required=True,
                   pending_block=None, paper_status=None):
    """Drive one paper's provenance check; returns the process exit status.

    Every message this emits is the message the per-paper checkers emitted before the
    scheme logic was factored out here — the checkers differ only in configuration.

    `scope_manifest`, when given, is a dict with `out_of_scope` and `mathlib_rendered`
    lists of node ids (plus a `path` for messages).  It turns the completeness sentence
    "every in-scope node has a carrier or is Mathlib-rendered" into a fail-closed check:
    (source nodes) − out_of_scope − mathlib_rendered must equal the annotated node set,
    in both directions.  Papers that do not pass a manifest keep the old behaviour.

    `inventory_required=False` is for a paper registered `in-progress` before its
    `AxiomAudit.lean` block exists.  It downgrades *only* the "the block is absent"
    message, and only while nothing in the library is annotated, to a note; the moment a
    declaration carries an annotation the block is demanded again, and each annotated
    declaration is an uninventoried endpoint until it is listed.  So this loosens the
    gate exactly over the window in which there is nothing for the gate to protect.

    `pending_block`, when given, names a second block in the same `audit` file — a pure
    comment block, read by `read_pending` — that stages endpoints whose statements are
    final but whose proofs are still `sorry`.  Such a declaration is a real endpoint and
    must carry its annotation, yet it cannot go into `#assert_axioms_clean`, which would
    fail on the `sorry`; without somewhere to say so it reads as an uninventoried
    endpoint, which is a false alarm.  An annotated declaration therefore satisfies the
    coverage rule by appearing in *either* block, and the staging is fenced so that it
    buys nothing else: a name in both blocks is a violation (an endpoint is
    axiom-checked or proof-pending, never both), a pending entry naming no annotated
    declaration is a violation (staging must not outlive the endpoint it stages), and a
    malformed pending line is a violation rather than a skipped line.  A non-empty
    pending block that survives all of that is reported as a *note*, never a failure;
    an absent block is a note too, since a paper may legitimately stage nothing.

    The pending block's optional `SECTION: consumers` half is checked by its own rules,
    since its names are by construction *not* endpoints: a consumer must name a real
    declaration under `lib`, must **not** carry a `Paper node:` annotation (one that
    acquires an annotation is an endpoint and moves into the main section — a
    violation), and must not be inventoried.  Consumers never satisfy the annotated
    endpoints' coverage rule; they only keep the ledger complete, so
    `scripts/check_sorry_ledger.py` can demand that every `sorryAx`-dependent
    declaration is named somewhere.

    `paper_status`, when given, is the paper's registered status.  `'completed'` with a
    non-empty pending set (in *either* section) is a violation: staging is a mid-flight
    device, and a finished paper has every endpoint inside the axiom gate.
    """
    violations: list[str] = []
    notes: list[str] = []

    if empty_source_message is not None and not source_nodes:
        violations.append(empty_source_message)

    inventory_parse = read_inventory(audit, inventory_block)
    inventory_missing = inventory_parse is None
    if inventory_missing:
        inventory = set()
        if inventory_required:
            violations.append(f"{audit}: missing {inventory_block}-BEGIN/END markers")
    else:
        inventory = inventory_parse.names
        violations += inventory_parse.problems
    resolved = inventory if root_prefix is None else (
        inventory | {f"{root_prefix}.{entry}" for entry in inventory})

    def forms_of(entry):
        """The qualified names a listed entry may resolve to, per `root_prefix`."""
        return {entry} if root_prefix is None else {entry, f"{root_prefix}.{entry}"}

    pending_names: set[str] = set()
    consumer_names: set[str] = set()
    resolved_pending: set[str] = set()
    if pending_block is not None:
        pending = read_pending(audit, pending_block)
        if pending is None:
            notes.append(
                f"note: {audit} has no {pending_block}-BEGIN/END block, so nothing is "
                f"staged as proof-pending."
            )
        else:
            violations += pending.problems
            pending_names = set(pending.entries)
            consumer_names = set(pending.consumers)
            for entry in pending_names:
                resolved_pending |= forms_of(entry)

    accepted = resolved | resolved_pending

    citations = 0
    annotated_nodes: set[str] = set()
    annotated_qualified: set[str] = set()
    annotated_carriers = 0
    # Every declaration name under the library, collected only when the pending block
    # has a consumers section to check against it — the consumers rule is the one check
    # that needs the *unannotated* declarations too.
    declared_qualified: set[str] = set()

    for path in library_sources(root_module, lib):
        text = path.read_text()
        lines = text.splitlines()
        code, docs = scan(text)
        prefixes = namespace_prefixes(code, len(lines))

        if consumer_names:
            for lineno in range(1, len(lines) + 1):
                chunk = code.get(lineno, "").strip()
                if not chunk or not DECL.match(chunk):
                    continue
                decl_line, _, name = following_declaration(code, lineno, len(lines))
                if not name:
                    continue
                prefix = prefixes.get(decl_line, "")
                declared_qualified.add(f"{prefix}.{name}" if prefix else name)

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
            annotated_carriers += 1
            annotated_qualified.add(qualified)
            if qualified not in accepted:
                where = (f"{inventory_block} block" if pending_block is None else
                         f"{inventory_block} block, nor staged in its "
                         f"{pending_block} block")
                violations.append(
                    f"{path}:{decl_line}: UNINVENTORIED ENDPOINT: {qualified!r} carries a "
                    f"'{MARKER}' annotation but is not listed in {audit}'s {where}"
                )

    for entry in sorted(pending_names):
        if forms_of(entry) & resolved:
            violations.append(
                f"{audit}: PENDING ENTRY ALSO INVENTORIED: {entry!r} is listed in both "
                f"the {inventory_block} block and the {pending_block} block of {audit}; "
                f"an endpoint is either axiom-checked or proof-pending, not both"
            )
        if not (forms_of(entry) & annotated_qualified):
            violations.append(
                f"{audit}: STALE PENDING ENTRY: {entry!r} is listed in the "
                f"{pending_block} block but names no declaration carrying a '{MARKER}' "
                f"annotation under {lib}/; staging must not outlive the endpoint it "
                f"stages"
            )

    for entry in sorted(consumer_names):
        if forms_of(entry) & resolved:
            violations.append(
                f"{audit}: PENDING ENTRY ALSO INVENTORIED: {entry!r} is listed in both "
                f"the {inventory_block} block and the {pending_block} block of {audit}; "
                f"an endpoint is either axiom-checked or proof-pending, not both"
            )
        if forms_of(entry) & annotated_qualified:
            violations.append(
                f"{audit}: ANNOTATED CONSUMER: {entry!r} is listed in the "
                f"{pending_block} block's consumers section, which is for declarations "
                f"carrying no '{MARKER}' annotation, but it now carries one; a consumer "
                f"that becomes an endpoint moves into the block's main section"
            )
        elif not (forms_of(entry) & declared_qualified):
            violations.append(
                f"{audit}: STALE PENDING ENTRY: {entry!r} is listed in the "
                f"{pending_block} block's consumers section but names no declaration "
                f"under {lib}/; staging must not outlive what it stages"
            )

    if paper_status == "completed" and (pending_names or consumer_names):
        staged = (f"{len(pending_names)} endpoint(s) are staged as proof-pending"
                  if not consumer_names else
                  f"{len(pending_names)} endpoint(s) are staged as proof-pending and "
                  f"{len(consumer_names)} un-annotated consumer(s) are listed")
        violations.append(
            f"{audit}: PENDING BLOCK NON-EMPTY: paper status is 'completed' but "
            f"{staged}; a completed paper has no pending endpoints"
        )

    if scope_manifest is not None:
        mpath = scope_manifest.get("path", "scope manifest")
        out = set(scope_manifest.get("out_of_scope", []))
        rendered = set(scope_manifest.get("mathlib_rendered", []))
        for label, group in (("out_of_scope", out), ("mathlib_rendered", rendered)):
            violations += [
                f"{mpath}: SCOPE MANIFEST: {label} names {node!r}, which is not numbered in {tex}"
                for node in sorted(group) if node not in source_nodes
            ]
        overlap = out & rendered
        violations += [
            f"{mpath}: SCOPE MANIFEST: {node!r} is listed as both out_of_scope and mathlib_rendered"
            for node in sorted(overlap)
        ]
        expected = set(source_nodes) - out - rendered
        violations += [
            f"{mpath}: UNCOVERED NODE: {node!r} is in scope but no declaration carries a "
            f"'{MARKER}' annotation for it"
            for node in sorted(expected - annotated_nodes)
        ]
        violations += [
            f"{mpath}: SCOPE MANIFEST: {node!r} carries a '{MARKER}' annotation but the "
            f"manifest lists it as out_of_scope or mathlib_rendered"
            for node in sorted(annotated_nodes & (out | rendered))
        ]

    if inventory_missing and not inventory_required:
        if annotated_carriers:
            violations.append(f"{audit}: missing {inventory_block}-BEGIN/END markers")
        else:
            notes.append(
                f"note: {audit} has no {inventory_block}-BEGIN/END block yet, and "
                f"nothing under {lib}/ carries a '{MARKER}' annotation, so there is no "
                f"endpoint to inventory. The block is required from the first annotated "
                f"declaration onwards."
            )

    if (pending_names or consumer_names) and not violations:
        notes.append(
            f"note: {len(pending_names)} endpoints pending (sorry)"
            + (f" + {len(consumer_names)} un-annotated consumers" if consumer_names
               else "")
            + " — not axiom-checked")

    for entry in notes:
        print(entry)
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


# --- printed-independent (Finite Factored Sets): one global counter per environment ---
#
# Garrabrant (arXiv:2109.11513) declares its theorem environments *without* a `[section]`
# argument and without sharing counters, so each environment numbers independently and
# never resets: `Definition 1`…`Definition 50` run the length of the paper alongside
# `Proposition 1`…`Proposition 36`.  That is a different counter discipline from
# ModalAgents' single section-scoped counter, not a variant of it.
#
# The environment name is not the printed name.  That paper's `miritools.sty` declares a
# `lemma` environment and `main.tex` declares a *second* one, `lemma2`, which also prints
# "Lemma"; only `lemma2` is ever used, and all three printed Lemmas come from it.  A
# checker that emulated `lemma` and ignored `lemma2` would silently find no lemmas at all,
# so the map below is explicit and `_printed_independent_scan` fails closed if two
# environments sharing a printed name are both used — that would make the printed number
# genuinely ambiguous, and an ambiguous ID cannot be a provenance key.
PRINTED_INDEPENDENT_ENVS = {
    "definition": "Definition",
    "theorem": "Theorem",
    "proposition": "Proposition",
    "corollary": "Corollary",
    "lemma": "Lemma",
    "lemma2": "Lemma",
    "example": "Example",
    "conjecture": "Conjecture",
    "problem": "Problem",
}
PRINTED_INDEPENDENT_BEGIN = re.compile(
    r"\\begin\{(" + "|".join(sorted(PRINTED_INDEPENDENT_ENVS, key=len, reverse=True)) + r")\}")
PRINTED_INDEPENDENT_NODE_ID = re.compile(
    r"(" + "|".join(sorted(set(PRINTED_INDEPENDENT_ENVS.values()))) + r")\s+([0-9]+)")


def _printed_independent_scan(tex_text):
    """Every counted environment in source order, as `(node_id, env, body_start, match)`."""
    stripped = "\n".join(strip_tex_comment(raw) for raw in tex_text.splitlines())
    counters: dict[str, int] = {}
    seen_by_printed: dict[str, set[str]] = {}
    out = []
    for match in PRINTED_INDEPENDENT_BEGIN.finditer(stripped):
        env = match.group(1)
        printed = PRINTED_INDEPENDENT_ENVS[env]
        seen_by_printed.setdefault(printed, set()).add(env)
        if len(seen_by_printed[printed]) > 1:
            raise ValueError(
                f"ambiguous printed node kind {printed!r}: environments "
                f"{sorted(seen_by_printed[printed])} both number independently and both "
                f"print {printed!r}, so a printed number does not identify a node")
        counters[env] = counters.get(env, 0) + 1
        out.append((f"{printed} {counters[env]}", env, match))
    return stripped, out


def printed_independent_nodes(tex_text):
    return {node_id for node_id, _env, _m in _printed_independent_scan(tex_text)[1]}


def printed_independent_declarations(tex_text):
    """Every counted environment with its number, optional title and body TeX."""
    stripped, scanned = _printed_independent_scan(tex_text)
    out = {}
    for node_id, env, match in scanned:
        end = stripped.find("\\end{%s}" % env, match.end())
        body = stripped[match.end():end if end >= 0 else len(stripped)]
        title = ""
        tm = re.match(r"\s*\[((?:[^\[\]]|\[[^\]]*\])*)\]", body)
        if tm:
            title = tm.group(1).strip()
            body = body[tm.end():]
        body = re.sub(r"\\label\{[^}]*\}", "", body)
        out[node_id] = Node(node_id, PRINTED_INDEPENDENT_ENVS[env],
                            node_id.rsplit(" ", 1)[1], title, body.strip(), match.start())
    return out


# --- printed-counter read off a text extraction (Condensation) -----------------------
#
# Eisenstat's *Condensation* numbers its results exactly the way ModalAgents does — a
# single section-scoped counter shared by `definition`, `proposition`, `lemma`,
# `theorem`, `corollary` and `example`, so ids read `<section>.<n>` — but no TeX source
# for it exists in this project.  The committed source is a `pdftotext -layout`
# extraction of the committed PDF, so the counter cannot be emulated: the printed
# numbers are read straight off the extraction's header lines.
#
# That makes the extraction itself provenance-bearing, which is a weaker position than
# holding the TeX, and the checker compensates by asserting the expected node count (see
# `scripts/check-condensation-nodes.py`).  A re-extraction that reflows a header, or a
# `pdftotext` version that mangles one, then fails loudly instead of quietly shrinking
# the set of nodes a `Paper node:` annotation is allowed to name.
#
# The extractor does not resolve the paper's f-ligatures to letters: it emits the font's
# own slot for them, a C0 control character.  "Definition" therefore comes out as
# `De\x1cnition` — which prints as "Denition" and reads as a dropped `fi` — and likewise
# `\x1b` for `ff`, `\x1d` for `fl`, `\x1e` for `ffi`.  `De(?:fi)?.?nition` accepts the
# extraction's spelling, the control-character spelling and plain "Definition", and
# nothing else; the kind is normalised to `Definition` before it becomes part of a node
# id.  The optional parenthetical covers the two titled nodes, `Theorem 4.15 (Comparison
# of perfect condensations).` and `Theorem 5.8 (Comparison of latent variable models).`
# The trailing period is what separates a *header* from a cross-reference: "Corollary
# 4.6 tells us something about…" opens a line but does not end its number with a dot.
#
# **Split this text with `split("\n")`, never `splitlines()`.**  Python's `splitlines`
# also breaks on `\x1c`, `\x1d`, `\x1e`, `\x0b`, `\x0c` and `\x85`, four of which are
# exactly the ligature slots above — so `splitlines()` tears `De\x1cnition` into a line
# ending "De" and a line beginning "nition", and every Definition header in the paper
# silently disappears from the node set.

PRINTED_EXTRACTION_KINDS = ("Definition", "Proposition", "Lemma", "Theorem",
                            "Corollary", "Example")
PRINTED_EXTRACTION_HEADER = re.compile(
    r"^[ \t]*(De(?:fi)?.?nition|Proposition|Lemma|Theorem|Corollary|Example)"
    r"[ \t]+([0-9]+)\.([0-9]+)((?:[ \t]*\([^)]*\))?)\.")
# The extraction's font slots, resolved for display.  Only glyphs whose identity is
# unambiguous from the paper are mapped; anything else is left exactly as extracted, so
# a reader of the rendered statement sees the extraction, not our guess at it.
PRINTED_EXTRACTION_GLYPHS = {
    "\x1b": "ff", "\x1c": "fi", "\x1d": "fl", "\x1e": "ffi",
    "\x10": "“", "\x11": "”", "\x12": "‘", "\x13": "’",
    "\x15": "–", "\x16": "—",
}
PRINTED_EXTRACTION_NODE_ID = re.compile(
    r"(" + "|".join(PRINTED_EXTRACTION_KINDS) + r")\s+([0-9]+\.[0-9]+)")
# Sectioning in this layout: numbered sections are centred on their own line, and
# subsections are run in at the left margin ("5.2.   Comparison of latent variable
# models. We now proceed…").  The table of contents indents its entries, so anchoring
# subsections at column 0 keeps the contents listing out of the section index.
PRINTED_EXTRACTION_SECTION = re.compile(
    r"^[ \t]{8,}([0-9]+)\.[ \t]+([A-Z][^\n]*?)[ \t]*$")
PRINTED_EXTRACTION_SUBSECTION = re.compile(
    r"^([0-9]+\.[0-9]+)\.[ \t]{2,}([A-Z][^\n.]*)\.")
# A statement's printed body ends at the proof, at the next node, at a sectioning line,
# or where the paper starts a fresh prose paragraph — which this layout marks with a
# small left indent (display equations are indented far further, or carry their equation
# number at the margin, so they are not mistaken for one).  Two things are indented like
# a new paragraph without being one, and both are continuations: the paper's enumerated
# conditions, `(1)` / `(A2)` / `(iii)`; and the remainder of a statement that a page
# break interrupted, which is re-indented on the next page.  A third case is a sentence
# resumed after an inline display, which `-layout` also indents — so a paragraph break is
# only believed where the statement so far has actually ended a sentence.
PRINTED_EXTRACTION_PARAGRAPH = re.compile(r"^[ \t]{2,4}\S")
PRINTED_EXTRACTION_ITEM = re.compile(r"^[ \t]{0,8}\((?:[A-Za-z]{0,2}[0-9]+|[ivxIVX]+)\)")
PRINTED_EXTRACTION_PROOF = re.compile(r"^[ \t]*Proof\.")
# The bibliography, whose entries open with their citation key.  The paper's last node
# is followed by commentary rather than a proof, so without this the final statement
# would run on into the references.
PRINTED_EXTRACTION_BIBLIOGRAPHY = re.compile(r"^[ \t]*\[[A-Za-z][A-Za-z0-9+]*\]")
# Belt and braces on the paragraph heuristics: no printed statement in this paper is
# anywhere near this long, so a card can be imprecise but never unbounded.
PRINTED_EXTRACTION_MAX_LINES = 60


def extraction_lines(text):
    """The extraction's lines.  See the warning above: never `splitlines()` this."""
    return text.split("\n")


def resolve_extraction_glyphs(s):
    """Resolve the extraction's font slots (ligatures, quotes, dashes) for display."""
    for slot, glyph in PRINTED_EXTRACTION_GLYPHS.items():
        s = s.replace(slot, glyph)
    return s


def _extraction_furniture(text):
    """Predicate: is this line running head / page number, not paper content?

    `pdftotext -layout` keeps the running head and folio of every page, which would
    otherwise land in the middle of any statement that spans a page break.  The running
    head is taken from the extraction's own first non-blank line (the title as it is set
    on the page), so this stays a property of the file rather than a hard-coded string.
    """
    head = ""
    for line in extraction_lines(text):
        if line.strip():
            head = line.strip()
            break

    def furniture(line):
        stripped = line.strip()
        if not stripped:
            return False
        if head and stripped.startswith(head):
            return True
        if re.fullmatch(r"[0-9]{1,3}", stripped):
            return True
        # Other running heads set in caps ("REFERENCES   26"), which `pdftotext` can
        # emit in the middle of a statement that spans the page break.
        return bool(re.fullmatch(r"[A-Z][A-Z0-9 ,.:;'’—–-]{3,}?(?:\s+[0-9]{1,3})?",
                                 stripped))

    return furniture


def _extraction_kind(raw):
    """Normalise a header's printed kind, healing the extractor's ligature slot."""
    return "Definition" if raw.startswith("De") else raw


def printed_extraction_node_sort_key(node_id):
    """Sort `Definition 3.10` after `Definition 3.9`, and by section first."""
    kind, _, number = node_id.partition(" ")
    section, _, index = number.partition(".")
    return (int(section or 0), int(index or 0), kind)


def printed_extraction_sections(text):
    """`(offset, title)` for each numbered section and subsection, in source order."""
    out = []
    offset = 0
    for line in extraction_lines(text):
        m = PRINTED_EXTRACTION_SECTION.match(line)
        if m:
            out.append((offset, "%s. %s" % (m.group(1), m.group(2).strip())))
        else:
            m = PRINTED_EXTRACTION_SUBSECTION.match(line)
            if m:
                out.append((offset, "%s. %s" % (m.group(1), m.group(2).strip())))
        offset += len(line) + 1
    return out


def printed_extraction_nodes(text):
    """The paper's printed node ids, read off the extraction's header lines."""
    return {node.id for node in printed_extraction_declarations(text).values()}


def printed_extraction_declarations(text):
    """Every numbered node with its printed statement, read off the extraction."""
    lines = extraction_lines(text)
    offsets, running = [], 0
    for line in lines:
        offsets.append(running)
        running += len(line) + 1

    furniture = _extraction_furniture(text)
    starts = [(idx, m) for idx, m in
              ((idx, PRINTED_EXTRACTION_HEADER.match(line)) for idx, line in enumerate(lines))
              if m and not furniture(lines[idx])]

    out = {}
    for idx, m in starts:
        kind = _extraction_kind(m.group(1))
        number = "%s.%s" % (m.group(2), m.group(3))
        title = (m.group(4) or "").strip().strip("()").strip()
        body = [lines[idx][m.end():].strip()]
        across_page_break = False
        for j in range(idx + 1, len(lines)):
            following = lines[j]
            if furniture(following) or "\x0c" in following:
                across_page_break = True
                continue
            if (PRINTED_EXTRACTION_HEADER.match(following)
                    or PRINTED_EXTRACTION_PROOF.match(following)
                    or PRINTED_EXTRACTION_SECTION.match(following)
                    or PRINTED_EXTRACTION_SUBSECTION.match(following)
                    or PRINTED_EXTRACTION_BIBLIOGRAPHY.match(following)
                    or len(body) >= PRINTED_EXTRACTION_MAX_LINES):
                break
            ended = next((chunk.rstrip() for chunk in reversed(body) if chunk.strip()), "")
            if (PRINTED_EXTRACTION_PARAGRAPH.match(following)
                    and not PRINTED_EXTRACTION_ITEM.match(following)
                    and not across_page_break
                    and ended.rstrip("”’\"')").endswith((".", "!", "?"))):
                break
            if following.strip():
                across_page_break = False
            body.append(following)
        node_id = "%s %s" % (kind, number)
        out[node_id] = Node(node_id, kind, number, resolve_extraction_glyphs(title),
                            resolve_extraction_glyphs("\n".join(body).strip("\n").rstrip()),
                            offsets[idx])
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
    "printed-independent": {
        "node_id_re": PRINTED_INDEPENDENT_NODE_ID,
        "source_nodes": printed_independent_nodes,
        "declarations": printed_independent_declarations,
    },
}

# A paper's `scheme` says how the *paper* numbers its results; its `source_format` says
# what the committed source physically is.  The two are independent, and the parser is
# chosen by the pair: `printed-counter` over TeX emulates the counter, `printed-counter`
# over a text extraction reads the printed numbers off the page.  Registry entries
# without a `source_format` are TeX, which is the case for every paper but Condensation.
EXTRACTION_SCHEMES = {
    "printed-counter": {
        "node_id_re": PRINTED_EXTRACTION_NODE_ID,
        "source_nodes": printed_extraction_nodes,
        "declarations": printed_extraction_declarations,
    },
}


def scheme_of(paper):
    """The `{node_id_re, source_nodes, declarations}` parser for a registered paper.

    Always prefer this to indexing `SCHEMES` by `paper['scheme']`: the scheme name alone
    does not determine the parser once a paper's source is an extraction rather than TeX,
    and picking the TeX parser for an extraction fails *silently* — it simply finds no
    nodes, which reads as "this paper numbers nothing" rather than as an error.
    """
    fmt = paper.get("source_format", "tex")
    if fmt == "tex":
        table = SCHEMES
    elif fmt == "text-extraction":
        table = EXTRACTION_SCHEMES
    else:
        raise KeyError("unknown source_format %r (expected 'tex' or 'text-extraction')"
                       % fmt)
    scheme = paper.get("scheme")
    if scheme not in table:
        raise KeyError("no parser for scheme %r over source_format %r; registered: %s"
                       % (scheme, fmt, ", ".join(sorted(table))))
    return table[scheme]


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
