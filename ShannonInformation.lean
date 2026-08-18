/-
Root module for FAF's shared Shannon-information layer.

This exists so `lake` has a root for the `ShannonInformation` library and so that
`import ShannonInformation` works.  **The documented, recommended import is
`ShannonInformation.API`** — see `ShannonInformation/README.md`.

This is shared infrastructure, not a paper formalization: it is deliberately absent from
`scripts/papers.py`'s `PAPERS` registry and listed in `NON_PAPER_LIBRARIES` instead.
-/
module

public import ShannonInformation.API
