# Logical Induction, formalized

A Lean 4 formalization of Garrabrant, Benson-Tilsen, Critch, Soares, Taylor,
[*Logical Induction*](https://arxiv.org/abs/1609.03543) (arXiv:1609.03543v5).

This is a **near-complete formalization of the paper**: the existence theorem is proved
in the paper's full sense, and every named theorem and lemma of the paper — 53 of them —
is formalized, named after its paper label, and build-audited. How strong each one is:

| | count | what it means |
|---|---:|---|
| **paper strength** | 39 | proved exactly as the paper states it — for every logical inductor, on the paper's own hypotheses |
| **qualified** | 12 | proved with one explicitly named representation interface or class restriction retained |
| **not yet witnessed** | 2 | proved, but from a premise that currently has no inhabitant — see below |

Each qualified node says in one line which premise it retains and why. The per-node
table is [`scripts/coverage-classification.md`](../scripts/coverage-classification.md),
machine-checked against the endpoint inventory so a node cannot ship without a strength
call.

Separately, and beyond what the paper claims: **19 of the 39 are also instantiated over
the concrete inductor constructed here**, so they hold of a specific algorithm rather
than of a hypothetical one. The paper states no such theorems; these are a
strengthening, not a different degree of faithfulness.

**Zero `sorry`, zero `axiom` declarations** — every public endpoint reports only Lean's
standard `propext`, `Classical.choice`, `Quot.sound`, enforced by the build
(`AxiomAudit.lean` enumerates the public surface and fails compilation on any
regression), and every paper-label citation is verified two-way by script. One
qualification to that, stated up front because it is easy to miss: see *One upstream
gap* below. The two declared modeling choices, and the planned future work that would
tighten them further, are described after it.

## The main theorem

For every computable deductive process, a logical inductor exists — in the paper's full
sense:

* `exists_computable_beliefSequence_logical_inductor` — there is a computable sequence
  of explicit finite-support rational belief states (one program emits the day-`n`
  association list) whose induced pricing satisfies the logical induction criterion.
* `LIA_is_logical_inductor` — the concrete recursively-constructed rational market
  built here (the paper's §5 algorithm: market maker via a from-scratch Sperner/Brouwer
  fixed point, budgeter, trading firm over a universal trader enumeration) satisfies
  the criterion.

The §4 property tail — convergence, coherence, provability induction, persistence,
preemptive learning, calibration, unbiasedness, pseudorandomness, logical
relationships, non-dogmatism, Occam bounds, universal-semimeasure domination, closure
under conditioning and perturbation, expectations, introspection, paradox resistance,
and self-trust — is proved for **every** logical inductor (`[IsLogicalInductor P DP]`),
with paper-facing names mirroring the paper's labels (`lic_provind` ↔ `thm:provind`).
Where a theorem needs representation machinery (quotation, arithmetic,
computation-representing theories), that machinery is *constructed* over the concrete
inductor wherever the model permits, yielding `_unconditional` and `_closed` endpoints
with no hypotheses beyond the statement's own data; where a residual interface remains,
the per-node table says which.

## Two nodes are currently vacuous — domination of the universal semimeasure

`thm:dus` and `thm:strict` are proved, but from a premise we have since proved
**uninhabited**, so as they stand they carry no content. This is disclosed here rather
than buried in the per-node table because it is the most serious defect currently on the
surface.

The cause is a metering mismatch of our own making. `BitPrefixSentences.prefix_codes`
requires `PolySentenceCodes` — *whole-value* metering, where the emitted Gödel **number**
must be polynomially bounded in the enumeration index. But the sentences it meters are
prefix conjunctions of unbounded depth: a binary connective costs two nested `Nat.pair`s
(a fourth power) while a `List Bool` cons costs one (a square), so the sentence's code is
about `2^(4^m)` at an index of about `5^(2^m)`. No polynomial closes that gap, for any
atom family over any deductive process — `bitPrefixCodeComputation_isEmpty`
(`Construction/Witnesses/BitPrefixSyntax.lean`) proves it.

The repair is known and the tooling for it already exists in this repo: switch the field
to the symbol-metered `RpnSentenceCodes` — the class built for exactly this pathology,
whose own docstring names it — since the prefix conjunction's Polish form is `Θ(m)` small
tokens. That also requires indexing the family length-lex rather than by list code (so the
emitter never has to invert an exponential-valued index) and migrating the trader's
emission chain onto the `RpnSpliceStream` mirrors. Until that lands, treat these two nodes
as unproved.

## One upstream gap

The theorems that quantify over an arithmetic theory — the quotation family (`thm:ref`,
`thm:lp`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st`) and the
computation family (`thm:halts`, `thm:pac`, …) — are stated parametrically:
`(T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]`. As stated they are
axiom-clean, and the paper's own hypothesis is the same ("Θ represents computations").

But *instantiating* them at a concrete theory currently costs one upstream axiom:
Foundation provides `Δ₁`-definability of `𝗜𝚺₁` and `𝗣𝗔` only as `axiom
ISigma1_delta1Definable` / `axiom PA_delta1Definable`, marked *TODO: Prove* in
Foundation's own source. So a concrete instance of, say, `thm:st` over `𝗜𝚺₁` reports that
axiom, even though the parametric endpoint does not.

This is an upstream gap rather than a modeling choice here, and nothing in this
development assumes it — but it is invisible to a parametric axiom check, so
`AxiomAudit.lean` now pins it explicitly: it builds one concrete instantiation and
asserts it clean *except* for that named axiom. If Foundation proves `𝗜𝚺₁.Δ₁`, that
assertion starts failing and gets promoted to a plain clean assertion.

## The two modeling boundaries

1. **Efficient computability is a fuel-clocked interpreter model, not a machine
   complexity class.** Traders and every "polynomial" certificate are metered by
   Mathlib's clocked interpreter `Nat.Partrec.Code.evaln` under a polynomial fuel
   bound. The model card (`Framework/Computable.lean`) proves its calibration facts
   and states the open question plainly: there is no theorem that every
   polynomial-time trader in the paper's sense lands in this class. Precisely: the
   existence theorem defeats this class rather than the paper's, and is weaker than the
   paper's `thm:li` if the inclusion fails. For the property tail the choice is
   conservative wherever a theorem's exploiting trader is constructed and certified
   inside the class — which is everywhere except **closure under finite perturbations**
   (`thm:ifp`), whose transported trader needs a fuel-class closure property the model
   provably lacks (the inverse-operation ceiling on the digit calculus), so that
   endpoint stays restricted to efficiently patchable market prefixes and has no
   instantiation over the constructed inductor.

   Worth noting: the paper itself is explicit (remark after `def:ec`) that its
   framework is not wedded to polynomial time — any efficiency class with suitable
   closure properties yields logical inductors, with stricter classes giving weaker
   but faster ones. Poly-time was their choice of convenience, not a load-bearing
   one. The fuel class carries the closure properties the theory's core needs — the
   construction and all but one of the property theorems completed inside it — so even
   if the inclusion question resolves negatively, what is formalized here is a logical
   inductor over a legitimate neighboring instantiation of the framework, not a
   different kind of theorem. The `thm:ifp` exception above is the one place where the
   class's closure gap is load-bearing rather than cosmetic.
2. **The logical substrate is propositional.** Sentences are Foundation's
   propositional formulas; the paper's first-order theory Θ enters through explicit
   interfaces, instantiated by arithmetic theories for the unconditional endpoints. In
   particular a logically uncertain variable (LUV) is presented by its family of
   threshold sentences `⌜X > r⌝`, with its world-value semantics carried as explicit,
   build-frozen certificate structures rather than derived from first-order syntax.

Both are disclosed at every affected statement, not just here.

## Planned future work

Each item has a verified obstruction on record; none blocks the results above.

* **An efficient prefix patch over the constructed inductor** — would lift `thm:ifp`
  from the efficiently-patchable restriction to the paper's unrestricted statement. The
  obstruction is the same fuel-class closure gap as boundary 1 (the emitted freeze
  stream's certificate needs a decode test on exponentially large codes, which the
  digit calculus provably does not close under), so closing boundary 1 would also close
  this. Note the paper's own proof of `thm:ifp` is separately invalid — see paper
  erratum PE1.
* **Close boundary 1** — the realistic route is a two-model architecture: define
  efficiency at a genuine machine class, let the trading firm enumerate it via
  poly-overhead universal simulation, and keep the fuel calculus as the certification
  tool through the easy inclusion (fuel-poly ⟹ machine-poly). A direct bridge theorem
  for the current class is judged unlikely: the fuel model lacks cheap poly-bit
  random-access state. A staged plan with effort estimates, scoped against what
  Mathlib actually provides, is in
  [`notes/two-model-ec-feasibility.md`](../notes/two-model-ec-feasibility.md).

## Faithfulness

The statement surface was hardened by fresh-context adversarial audit (independent
auditors plus a cross-family model check) and a fix wave that repaired every finding at
the statement level or pinned it to a verified obstruction; the finding-by-finding
ledger — including its own corrected misjudgments — is
[`notes/faithfulness-audit-2026-07-28.md`](../notes/faithfulness-audit-2026-07-28.md).
The process surfaced five errata in the paper itself, recorded with repairs in
[`notes/logical-induction-paper-errata.md`](../notes/logical-induction-paper-errata.md).

`brouwer_fixed_point`, used by the market maker, was proved from scratch via Sperner's
lemma (Mathlib has no Brouwer theorem); its proof body was autoformalized by Harmonic's
Aristotle and kernel-revalidated here. Its statement and axiom report are audited
surface; the generated proof interior has not had a human line-by-line read.

## Layout

* `Framework/` — the paper's §2–3: sentences, markets, features, traders,
  exploitation, the criterion, efficient computability, expectations, and the shared
  asymptotic vocabulary.
* `Properties/` — the §4 property tail, one file per theorem family.
* `Construction/` — the §5 existence proof, with `Construction/Witnesses/` holding the
  constructed representation machinery that discharges the property tail's interfaces
  over the concrete inductor.
