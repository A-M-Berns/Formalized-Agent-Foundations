#!/usr/bin/env python3
"""Fail if docs/trust-surface.html is stale relative to its inputs.

The generator (scripts/gen-trust-surface.py) stamps the page with a SHA-256 over its
five inputs: the coverage table, AxiomAudit.lean, the paper TeX, the template, and the
generator itself. This check recomputes that hash and compares it to the stamp, so any
surface or table change that skipped regeneration fails CI without CI needing the
generator's dependencies (latex2mathml).
"""
import hashlib, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__))) + '/'
INPUTS = ['scripts/coverage-classification.md', 'AxiomAudit.lean',
          'notes/1609.03543v5-main.tex', 'scripts/trust-surface-template.html',
          'scripts/gen-trust-surface.py']

h = hashlib.sha256()
for f in INPUTS:
    h.update(open(ROOT + f, 'rb').read())
expected = h.hexdigest()

page = open(ROOT + 'docs/trust-surface.html').read()
m = re.search(r'<!-- trust-surface-sources: ([0-9a-f]{64}) -->', page)
if not m:
    print('trust-surface check: FAIL — no sources stamp in docs/trust-surface.html')
    sys.exit(1)
if m.group(1) != expected:
    print('trust-surface check: FAIL — docs/trust-surface.html is stale.')
    print('  An input changed since the page was generated. Regenerate with:')
    print('    python3 scripts/gen-trust-surface.py   (pip install latex2mathml)')
    sys.exit(1)
print('trust-surface check: OK (page matches its five inputs)')
