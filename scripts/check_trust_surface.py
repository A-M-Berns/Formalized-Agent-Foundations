#!/usr/bin/env python3
"""Fail if docs/trust-surface.html is stale relative to its inputs.

The generator (scripts/gen-trust-surface.py) stamps the page with a SHA-256 over every
file it reads, and this check recomputes that hash and compares it to the stamp.  The
input list is built by `paper_nodes.trust_surface_inputs`, imported by both, so the
generator and the check cannot drift apart.

It covers *all* registered papers: each paper's committed source, every Lean file of
every library (the page renders their `Paper node:` annotations and statement
signatures), the prose the page quotes (READMEs, knowledge bases, errata, the coverage
table), `AxiomAudit.lean`, the registry, the template and the tooling.  So editing any
paper's source, any library's annotations, or `scripts/papers.py` marks the page stale
and fails CI — without CI needing the generator's dependencies (latex2mathml).
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paper_nodes import trust_surface_hash, trust_surface_inputs  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__))) + '/'

expected = trust_surface_hash(ROOT)
count = len(trust_surface_inputs(ROOT))

page = open(ROOT + 'docs/trust-surface.html', encoding='utf-8').read()
m = re.search(r'<!-- trust-surface-sources: ([0-9a-f]{64}) -->', page)
if not m:
    print('trust-surface check: FAIL — no sources stamp in docs/trust-surface.html')
    sys.exit(1)
if m.group(1) != expected:
    print('trust-surface check: FAIL — docs/trust-surface.html is stale.')
    print('  One of its %d inputs changed since the page was generated. Regenerate with:'
          % count)
    print('    python3 scripts/gen-trust-surface.py   (pip install latex2mathml)')
    sys.exit(1)
print('trust-surface check: OK (page matches its %d inputs)' % count)
