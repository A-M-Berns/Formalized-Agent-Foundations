# Paper errata — Garrabrant, Mayer, Wache, Lang, Eisenstat, Dell, *Factored space models* (arXiv:2412.02579v2)

Defects found in the paper while formalizing it, recorded so that a reader comparing the
Lean against the printed page is not misled. Numbering follows the paper's printed
section-scoped counter (`Definition 4.2`, `Lemma C.3`, …).

| # | Where | Printed | Should read | Found |
|---|---|---|---|---|
| E1 | Lemma C.3, proof of (ii)⟹(i) (§C.1) | "Let `f(x)` be arbitrary if there is no `ω ∈ C` with `X(ω) = x`" | presupposes `Val(Y) ≠ ∅`. With `C = ∅`, `Val(X) ≠ ∅` and `Val(Y) = ∅`, (ii) holds vacuously and no `f : Val(X) → Val(Y)` exists, so the equivalence fails. `derivedOn_iff` carries `[Nonempty β]`; harmless for the paper's random variables (a value space is the codomain of a function out of a nonempty `Ω`) but a genuine hypothesis | spike (2026-08-17) |
| E2 | Definition 4.2 (§4.1) | "finite sets `Ω_i`" | nothing requires `Ω_i ≠ ∅`, so `Ω` may be empty, while later arguments choose points of `Ω` or distributions on it (e.g. Lemma C.20 takes "any strictly positive distribution", Lemma 4.12's ⟸ direction takes `Z = U_i` and needs `Ω_i` to vary). Not an error in any statement so far; the Lean adds the hypothesis where it is used | spike |
