# Attribution and modification notice

This repository redistributes, in the top-level `PFR/` directory, a subset of the
**Polynomial Freiman–Ruzsa conjecture formalization** by Terence Tao and contributors:

> <https://github.com/teorth/pfr>, commit `01c9b666945eaf73b3f7d8b20ffe003f8640e630`.

That work is licensed under the **Apache License, Version 2.0**. A verbatim copy of the
licence, as shipped by upstream, is in `LICENSE-PFR` alongside this file. Upstream's
`LICENSE` is the bare Apache-2.0 template with no copyright line filled in, and the
individual source files carry no per-file copyright headers; this file therefore supplies
the attribution that would otherwise be missing, so that the origin of the code is
unambiguous regardless of which file a reader lands on.

## Statement of modification (Apache-2.0 §4(b))

The redistributed files are **modified**. Two files differ from upstream:

- `PFR/ForMathlib/Entropy/Measure.lean`
- `PFR/ForMathlib/Entropy/Kernel/Basic.lean`

Both modifications are marked in place with a comment beginning `FAF VENDOR PATCH`, are
recorded as unified diffs in `patches/`, and are described in `PROVENANCE.md`. Both are
compatibility repairs against a different Mathlib pin; **neither alters a mathematical
statement, definition, or proof**.

All other files in `PFR/` are byte-identical to upstream at the commit above, as verified
by `vendor-pfr.sh --verify`.

## Relationship to this repository's own licence

This repository is itself licensed under the **Apache License, Version 2.0** (top-level
`LICENSE`), the same licence as the redistributed work, so there is no licence-compatibility
question to resolve. FAF's own code — `ShannonInformation/`, its API, tests, tooling and
documentation — is FAF-copyright under that licence; the `PFR/` directory remains
upstream's work, redistributed under the same terms and modified as stated above.
