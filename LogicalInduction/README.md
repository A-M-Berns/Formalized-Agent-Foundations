# Logical Induction, formalized

A Lean 4 formalization of Garrabrant, Benson-Tilsen, Critch, Soares, Taylor,
[*Logical Induction*](https://arxiv.org/abs/1609.03543) (arXiv:1609.03543v5).

This is a **near-complete formalization of the paper**: the existence theorem is proved
in the paper's full sense, and every named theorem of the paper is formalized and
build-audited. Of the 53 theorem/lemma nodes, **34 are stated at the paper's own
hypotheses** — for every logical inductor, as the paper states them — and **14 of those
are additionally unconditional over the concrete constructed inductor**; the remaining
**19 retain an explicitly named representation interface or class restriction**, each
recorded per-node in
[`scripts/coverage-classification.md`](../scripts/coverage-classification.md), which is
machine-checked against the endpoint inventory. **Zero `sorry`, zero `axiom`
declarations** —
every public endpoint reports only Lean's standard `propext`, `Classical.choice`,
`Quot.sound`, enforced by the build (`AxiomAudit.lean` enumerates the public surface
and fails compilation on any regression), and every paper-label citation is verified
two-way by script. The two declared modeling choices, and the planned future work that
would tighten them further, are described below.

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
* **A variable-width gated affine layer** — would relax the self-trust chain's
  injectivity assumption on deferral functions to the paper's bare `f(n) > n`. The
  design is settled and its analytic core is Lean-verified (a division-free
  first-violator selector over the deferral fibre; an earlier gated-*sum* plan was
  proved unsound); what remains is the variable-width affine-combination and
  feature-fold infrastructure it needs.

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
