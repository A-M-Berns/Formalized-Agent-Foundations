"""The register of formalized papers — the single source of truth about what this
repository formalizes and how each paper is wired up.

Every tool that needs to know "which papers are here, where is each one's source, how
are its nodes cited" reads this file: `check_paper_wiring.py` (which enforces that the
wiring is complete), `gen-trust-surface.py`, and the per-paper node checkers' CI step.

**Adding a paper.** Add an entry here, then run `python3 scripts/check_paper_wiring.py`
and fix what it reports. It fails closed: a `lean_lib` in `lakefile.lean` that is
neither registered below nor listed in `NON_PAPER_LIBRARIES` is itself a failure, so a
new formalization cannot quietly ship without its paper source, its provenance
checker, its inventory coverage, and its place in the trust-surface guide.

Register work in progress with `status: "in-progress"`. Before changing that status to
`"completed"`, add `api` and `api_test`: the documented recommended Lean entrypoint and
an isolated client test importing only that entrypoint. The wiring gate then makes both
artifacts, their aggregation in `APITests.lean`, and their default CI build mandatory.

**Node-citation schemes.** The papers cite nodes differently, because the
sources differ, not by preference:

* `latex-label`   — the source labels its results (`\\label{thm:foo}`) and the
                    formalization cites those labels.  Checked two-way.
* `printed-inline` — the source numbers its results in prose
                    (`\\textbf{Definition 7}`) with no labels; the printed number is
                    the stable identifier.
* `printed-counter` — the source numbers results through LaTeX theorem counters, so
                    the printed number must be *derived* by emulating the counter
                    (`\\newtheorem{theorem}{Theorem}[section]` and friends).
* `printed-independent` — likewise counter-derived, but each environment carries its
                    own global counter that never resets (`\\newtheorem{theorem}{Theorem}`
                    with no `[section]`), so numbers read `Definition 34` rather than
                    `Theorem 4.5`.

A paper's scheme is a fact about its source; do not "harmonize" them.

**Source formats.** `scheme` says how the *paper* numbers its results; the optional
`source_format` says what the committed source file physically is, and therefore which
parser derives the numbers:

* absent (the default, `"tex"`) — the committed source is the paper's LaTeX, and the
  scheme's parser reads the TeX directly.
* `"text-extraction"` — no TeX source is in hand, so the committed source is a
  `pdftotext -layout` extraction of the committed PDF and the printed numbers are read
  off its header lines rather than derived from counters.  The extraction is then the
  thing under version control that the provenance check is against, so its checker
  asserts the expected node count to catch extraction drift.

`paper_nodes.scheme_of(paper)` resolves the pair; do not index `SCHEMES` by `scheme`
alone.
"""

PAPERS = {
    "logical-induction": {
        "title": "Logical Induction",
        "authors": "Garrabrant, Benson-Tilsen, Critch, Soares, Taylor",
        "year": 2016,
        "arxiv": "1609.03543",
        "library": "LogicalInduction",
        "status": "completed",
        "api": "LogicalInduction/API.lean",
        "api_test": "APITests/LogicalInduction.lean",
        "source": "LogicalInduction/notes/1609.03543v5-main.tex",
        "pdf": "LogicalInduction/notes/1609.03543v5.pdf",
        "scheme": "latex-label",
        "node_checker": "scripts/check-paper-nodes.sh",
        "readme": "LogicalInduction/README.md",
        "knowledge": "LogicalInduction/KNOWLEDGE.md",
        "errata": "LogicalInduction/notes/paper-errata.md",
        # Carries the repository's per-node strength classification.
        "coverage_table": "scripts/coverage-classification.md",
    },
    "modal-agents": {
        "title": "Robust Cooperation in the Prisoner's Dilemma: "
                 "Program Equilibrium via Provability Logic",
        "authors": "Barász, Christiano, Fallenstein, Herreshoff, LaVictoire, Yudkowsky",
        "year": 2014,
        "arxiv": "1401.5577",
        "library": "ModalAgents",
        "status": "completed",
        "api": "ModalAgents/API.lean",
        "api_test": "APITests/ModalAgents.lean",
        "source": "ModalAgents/notes/1401.5577-main.tex",
        "pdf": "ModalAgents/notes/1401.5577.pdf",
        "scheme": "printed-counter",
        "node_checker": "scripts/check-modal-agents-nodes.py",
        "readme": "ModalAgents/README.md",
        "knowledge": None,
        "errata": None,
    },
    "cartesian-frames": {
        "title": "Cartesian Frames",
        "authors": "Garrabrant, Herrmann, Lopez-Wild",
        "year": 2021,
        "arxiv": "2109.10996",
        "library": "CartesianFrames",
        "status": "completed",
        "api": "CartesianFrames/API.lean",
        "api_test": "APITests/CartesianFrames.lean",
        "source": "CartesianFrames/notes/2109.10996v1-main.tex",
        "pdf": "CartesianFrames/notes/2109.10996v1.pdf",
        "scheme": "printed-inline",
        "node_checker": "scripts/check-cartesian-frames-nodes.py",
        "readme": "CartesianFrames/README.md",
        "knowledge": "CartesianFrames/KNOWLEDGE.md",
        "errata": "CartesianFrames/notes/paper-errata.md",
    },
    "finite-factored-sets": {
        "title": "Temporal Inference with Finite Factored Sets",
        "authors": "Garrabrant",
        "year": 2021,
        "arxiv": "2109.11513",
        "status": "completed",
        "library": "FiniteFactoredSets",
        "source": "FiniteFactoredSets/notes/2109.11513-main.tex",
        "pdf": "FiniteFactoredSets/notes/2109.11513.pdf",
        "scheme": "printed-independent",
        "node_checker": "scripts/check-finite-factored-sets-nodes.py",
        "readme": "FiniteFactoredSets/README.md",
        "knowledge": "FiniteFactoredSets/KNOWLEDGE.md",
        "errata": "FiniteFactoredSets/notes/paper-errata.md",
        # Complete for its ruled scope (§2–§7; Examples 3 and 4 out of scope, Conjecture 1
        # stated and deliberately unproved), and the consumer surface is the whole of it
        # rather than an incremental slice (root CLAUDE.md, "Consumer readiness is part of
        # paper completion").
        "api": "FiniteFactoredSets/API.lean",
        "api_test": "APITests/FiniteFactoredSets.lean",
    },
    "condensation": {
        "title": "Condensation: A Theory of Concepts",
        "authors": "Eisenstat",
        "year": 2025,
        # No preprint server ID: this paper is not on arXiv.  The record is the
        # OpenReview submission below; the committed PDF is the author's copy from
        # https://sameisenstat.net/doc/condensation-25-07.pdf.
        "arxiv": None,
        "openreview": "HwKFJ3odui",
        "url": "https://openreview.net/forum?id=HwKFJ3odui",
        "library": "Condensation",
        "status": "in-progress",
        "source": "Condensation/notes/condensation-25-07.txt",
        "pdf": "Condensation/notes/condensation-25-07.pdf",
        # The paper numbers through a *single* section-scoped LaTeX theorem counter
        # shared by Definition/Proposition/Lemma/Theorem/Corollary/Example, so node ids
        # read `<section>.<n>` exactly as in ModalAgents — hence `printed-counter`,
        # which is a fact about the paper and stays true whatever we can read.
        #
        # What differs is the source we hold.  No TeX exists in this project, so the
        # counter cannot be *emulated*; the committed source is the `pdftotext -layout`
        # extraction of the PDF, and `scripts/check-condensation-nodes.py` reads the
        # printed numbers straight off its header lines (`source_format` below selects
        # that parser).  The extraction is therefore itself provenance-bearing: the
        # checker asserts the derived set is exactly the paper's 42 nodes, so a
        # re-extraction that silently drops or mangles a header fails rather than
        # narrowing the node set behind our backs.  Ligature loss in the extraction
        # ("Denition") is a tool artifact and is absorbed by the checker's regex.
        "scheme": "printed-counter",
        "source_format": "text-extraction",
        "node_checker": "scripts/check-condensation-nodes.py",
        "readme": "Condensation/README.md",
        "knowledge": "Condensation/KNOWLEDGE.md",
        "errata": "Condensation/notes/paper-errata.md",
    },
}

# Libraries in `lakefile.lean` that are deliberately not paper formalizations.  The
# reason is required: it is what stops this from becoming a place to silence the gate.
NON_PAPER_LIBRARIES = {
    "APITests": "client-style smoke tests for completed papers — a gate, not a formalization",
    "AxiomAudit": "the checked endpoint inventory itself — a gate, not a formalization",
    "Scratchpad": "scratch verification of the Mathlib/Foundation substrate; excluded "
                  "from the default target",
    "ProvabilityLogic": "vendored subset of FormalizedFormalLogic/ProvabilityLogic "
                        "(pinned in lakefile.lean) — dependency code, not a paper "
                        "formalized by this project",
    "PFR": "vendored subset of teorth/pfr @ 01c9b66 (Apache-2.0) supplying Shannon "
           "information theory, which the pinned Mathlib lacks — dependency code, not a "
           "paper formalized by this project; see ShannonInformation/vendor/PROVENANCE.md",
    "ShannonInformation": "shared, paper-neutral consumer surface over the vendored PFR "
                          "entropy substrate — infrastructure used by paper libraries, "
                          "not itself a paper; see ShannonInformation/README.md",
}
