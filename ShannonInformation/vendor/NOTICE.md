# Attribution and modification notice

This repository redistributes, in the top-level `PFR/` directory, a subset of the
**Polynomial Freiman–Ruzsa conjecture formalization** by Terence Tao and contributors:

> <https://github.com/teorth/pfr>, commit `65691129be2d8ca3e164c0822d95a456b88ee259`.

That work is licensed under the **Apache License, Version 2.0**. A verbatim copy of the
licence, as shipped by upstream, is in `LICENSE-PFR` alongside this file. Upstream's
`LICENSE` is the bare Apache-2.0 template with no copyright line filled in, and the
individual source files carry no per-file copyright headers; this file therefore supplies
the attribution that would otherwise be missing, so that the origin of the code is
unambiguous regardless of which file a reader lands on.

## Statement of modification (Apache-2.0 §4(b))

The redistributed files are **unmodified**: every file in `PFR/` is byte-identical to
upstream at the commit above, as verified by `vendor-pfr.sh --verify`. (Earlier vendorings
carried two compatibility patches; both are retired, see `PROVENANCE.md`.)

## Relationship to this repository's own licence

This repository is itself licensed under the **Apache License, Version 2.0** (top-level
`LICENSE`), the same licence as the redistributed work, so there is no licence-compatibility
question to resolve. FAF's own code — `ShannonInformation/`, its API, tests, tooling and
documentation — is FAF-copyright under that licence; the `PFR/` directory remains
upstream's work, redistributed under the same terms, unmodified.
