# `PFR/` — vendored third-party source. Do not edit.

This directory is **not** FAF mathematics. It is a pinned subset of the
[PFR project](https://github.com/teorth/pfr) (Tao et al.), redistributed under
Apache-2.0, providing the Shannon-information library that FAF's pinned Mathlib does not
have.

- **Upstream commit:** `01c9b666945eaf73b3f7d8b20ffe003f8640e630`
- **Licence:** Apache-2.0 — `ShannonInformation/vendor/LICENSE-PFR`, attribution and
  modification notice in `ShannonInformation/vendor/NOTICE.md`
- **Full provenance, closure and patch record:** `ShannonInformation/vendor/PROVENANCE.md`

Files sit at **upstream module paths** so that diffing against an upstream checkout stays
readable. Exactly two files are modified from upstream, each marked in place with a
`FAF VENDOR PATCH` comment; both are compatibility repairs, neither touches mathematics.

## If you want to change something here

Don't, directly. Either:

- **re-vendor** — `ShannonInformation/vendor/vendor-pfr.sh` regenerates this tree from
  upstream plus the recorded patches; or
- **add a patch** — if a new compatibility repair is genuinely needed, add a numbered
  diff under `ShannonInformation/vendor/patches/` with a written justification, then
  re-run the script. `vendor-pfr.sh --verify` must report `IDENTICAL` afterwards.

A change that alters a mathematical statement does not belong in a vendoring patch; take
it upstream.

## If you want to *use* this

Don't import `PFR.*` directly. Import the FAF consumer surface:

```lean
import ShannonInformation.API
```

See `ShannonInformation/README.md`, and `ShannonInformation/SCOPE.md` for what class of
random variables the results actually cover.
