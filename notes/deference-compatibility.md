# Compatibility with the deference / "Deference Done Better" port

_2026-08-08. Assessed against the note dump of 2026-06-27 (Demski, with Claude): the
research notes, the statement-level `AUDIT.md`, and all five Lean modules
(`LeanDeference`, `SelfReferentialTarget`, `FrozenDeliberation`, `FaithfulAcceleration`,
`TowerAndAcceleration`; 2315 lines, `sorry`-free, axiom-clean). Every claim below about
what that corpus assumes or proves was made with its Lean open, not from its prose._

## The one-line summary

The two developments are **complementary, not overlapping**: that corpus takes the
Logical-Induction theorems as named hypotheses and proves what follows from them; this
repo proves those theorems from the criterion, with constructed traders. Its single
largest disclosed gap is this repo's content.

## What the deference corpus assumes that this repo proves

Its `AUDIT.md` classifies hypothesis provenance with the same vocabulary this repo uses —
`(a)` derived, `(b)` LI citation, `(c)` modeling substitution — and records `thm:ccee`,
`thm:cee`, `thm:loe` and `thm:expprovind` as type-`(b)`: taken as-stated, not re-proved.
Its severity-1 finding is structural:

> the market and traders are entirely unmodeled … the inference "criterion ⇒ the forcing
> inequality" is nowhere in the corpus … converting it to type-`(b)` would require
> modeling a minimal market — a real project, not a patch.

Its recommendation #5 is to build exactly that, and calls it "the difference between 'the
algebra composes' and 'deference is forced.'" That is what `Framework/` + `Properties/` +
`Construction/` are. The complementarity is exact: **they assume the LI theorems; we
construct the traders that force them.**

One concrete, cheap integration target. Their `ccee_bridge_satisfiable` is classified
`N−` — a degenerate constant-sequence non-vacuity witness, and their own finding #9.
This repo's `thm:ccee` endpoint would replace it with a genuine instantiation, converting
a flagged weak guard into a real one.

## The `thm:ccee` interface, and why the slack does not matter

`thm:ccee` is the engine of the port, not an incidental citation — Value has a five-line
proof whose only engine is `thm:ccee`, and the notes carry a section on why it must be
`thm:ccee` and not `thm:cee`. So the question of how good our `thm:ccee` is, is a live
one for them.

The interface is narrow. In `LeanDeference.lean` the theorem is consumed as

```lean
(hCcee : Approx Exw Eew)
```

with `Exw`, `Eew : ℕ → ℝ` abstract real sequences (`E_now(X·w)` and `E_now(E_later(X)·w)`)
and `Approx a b := Tendsto (fun n => a n − b n) atTop (𝓝 0)` — the same `≈ₙ` this repo
defines in `Asymptotics`. **No LUV structure, no deductive process, and no slack term
crosses that boundary.**

`lic_no_expected_net_update_conditional_closed` concludes in exactly that shape. So the
mesh endpoint discharges `hCcee` as well as an exactly-reflecting one would, and the
`1/(n+1)` reflection slack — a declared type-`(c)` substitution internal to our proof —
is invisible to the consumer. This closes an open question the repo README previously
recorded ("whether the slack is acceptable depends on the consuming argument").

Their weight is a softmax over day-`f(n)` market prices, which is market-generable and
matches `thm:ccee`'s `\pgenable` hypothesis; it is *not* a fixed polynomial-time rational
sequence. This is independent evidence for the finding in
[`ccee-exact-scope.md`](ccee-exact-scope.md) that narrowing `w` to `PolyRatCodes` would be
worse than the slack it removes — it would drop the actual downstream consumer as well as
the paper's own worked example.

## What the exact route would add here: nothing, plus two obligations

Since freshness and the extended process do not appear in `hCcee`, the exact route buys
the consumer nothing at the interface. It would add two obligations at instantiation:

* **atom-freshness** over their `X` (menu options and bundles, whose thresholds are over
  the base language — plausible, but unverified against their families);
* an inductor over `base ∪ product-definitions`, which is the unbuilt computability step.

Their sharpest negative results are quote-referencing diagonal constructions, so a
no-self-reference side condition is not obviously free furniture in that setting; it is
the premise most likely to bite a real consumer, and it deserves checking against their
`X` before being treated as mild.

## Mechanical notes for any code-level integration

* Their toolchain is Lean/Mathlib `v4.27.0`; this repo is on `v4.28.0-rc1`. A bump is
  needed before their modules build against ours.
* Their `Approx`/`AsympLE` definitions coincide with this repo's `≈ₙ`/`≳ₙ` (`dd:asymp`),
  so the asymptotic vocabulary composes without a shim.

## Scope of this assessment

Read: the curated notes, `README.md`, `INDEX.md`, `AUDIT.md`, and the five Lean modules.
Not read: the ~10 MB of raw exported conversations. Not done: verifying atom-freshness
against their concrete `X` families, and building their modules against this toolchain.
