# Project: Formalized Agent Foundations — ethos & standards

This repo formalizes papers in agent foundations / open-source game theory in Lean 4,
on top of [Foundation](https://github.com/FormalizedFormalLogic/Foundation) and Mathlib.

The active major effort is a full Lean 4 formalization of **Logical Induction**
(Garrabrant et al., arXiv:1609.03543). The spec is `notes/logical-induction-roadmap.md`
— read it before touching `LogicalInduction/`. Every node carries the paper's real
`\label`; mirror those labels in comments so status maps back to the dependency graph.

The finished `Barasz/` formalization is the model for disclosure discipline: a clean
proof with its two unproved facts named, cited, and isolated in the README's "Axioms"
section. Do the same kind of honest accounting everywhere.

---

## The standard (non-negotiable)

The one-sentence bar:

> A kernel-clean proof certifies that the **body** matches the **statement**. It says
> nothing about whether the statement is the one we meant. The statement — its
> definitions, its hypotheses, its conclusion — is the trust surface, and it is only
> honest if its hypotheses are satisfiable and its constructed objects are real.

We are building the photo-negative of the deference corpus, whose failure was *proving
the implications of the theory while assuming the antecedents*. Here the antecedents —
the trader constructions and the criterion applications — **are** the content. A
property "proof" that takes the forcing inequality as a hypothesis, or stubs it with
one-line arithmetic, has formalized nothing we didn't already assume.

### Load-bearing rules

1. **The exploiting trader is the work.** No property proof is "done" until its
   exploiting trader is *constructed* and its efficient-computability *discharged through
   `EF.cost`*. A `sorry` on the trader construction is honest. An arithmetic stub
   *standing in for* the trader is the one thing the ledger exists to catch — never green
   it. (This is why M2 — wiring the assume-fail → build-trader → invoke-criterion loop
   once, end-to-end, on the easiest property — is the most important milestone in the
   roadmap. Don't rush past it into the satisfying volume of M3.)

2. **Never invent a Mathlib/Foundation name.** Before using a lemma, def, or instance,
   confirm it exists in the installed source: `rg` the `.lake/packages` tree, or use
   `#check` / `exact?` / `apply?` / `loogle`. If what you need doesn't exist, leave
   `sorry` with `-- TODO(blueprint:LABEL): need <statement>` and move on. Do not
   fabricate. (We have already found one roadmap assumption that fails this test:
   Mathlib has **no** Brouwer fixed-point theorem. See `Scratchpad.lean`.)

2b. **Search before you prove — the dual of rule 2, and the one that actually bites.**
   Rule 2 stops you using a name that doesn't exist. It does *nothing* to stop you
   spending an hour proving a lemma that already does. **Before writing the first tactic
   of any new lemma, grep for the fact — not the name you'd give it.** Search the
   *statement's shape* and its vocabulary, in this order: `rg` this repo (including
   `Construction/`, which is downstream and easy to miss from an upstream file), then
   `.lake/packages/mathlib`, then `exact?` / `loogle`. Names differ; the fact is what
   collides.

   This is not hypothetical. In one session, three separate re-proofs of existing
   results were committed and then reverted:
   - `pair_lt_sq` — Mathlib already had it verbatim as `Nat.pair_lt_max_add_one_sq`,
     and this repo's own `pair_lt_sq` was *already built on it*;
   - a ~90-line `evaln` output bound — already in the repo as `codeEvaln_result_le`
     + `codeEvalBound_poly` (`Construction/M7Witnesses.lean`), and the existing version
     was **better** (an explicit bound function, not an existential);
   - `DeductiveProcess.mono_le` — already in `Construction/Budgeter.lean`.

   Only the third was caught by the compiler. The other two were caught by accident,
   while reading for something unrelated — so assume your hit rate for noticing this
   unaided is near zero, and make the grep mechanical rather than a judgment call.
   A duplicate is worse than wasted time: it is a second, divergent proof of the same
   fact that some later reader must reconcile.

   Corollary for the ledger: if you *do* find you duplicated something, the honest fix
   is to delete yours and cite the original — even when yours is the one you just
   debugged, and even when it is in a more convenient file.

3. **The build stays green at every stopping point.** `sorry` is allowed and expected;
   elaboration/type errors are not. Small compiling commits over large broken ones.

4. **Ledger rows are written at proof time, by the person who knows they cheated.**
   `PROGRESS.md` maps `label → Lean decl → status → kind → provenance`. The kind and
   provenance columns are the anti-self-deception mechanism; they only work if filled
   honestly as you go, never retroactively. **A new theorem does not get committed
   without its ledger row in the same commit.**
   - *kind:* `Def` · `P` proved · `C` composition · `S` squeeze-over-named (conclusion ≡
     a hypothesis — flag and justify) · `T` trivial stub · `N±` non-vacuity witness.
   - *provenance* (per hypothesis): `(a)` derived in-project · `(b)` Foundation/Mathlib
     citation · `(c)` modeling substitution (a weaker/different object stands in for the
     intended one — the dangerous kind; eliminate it or disclose it).

5. **Modeling choices are disclosed, not discovered.** `dd:fuel` (efficiency = a
   fuel-clocked interpreter, not a complexity class) is itself a type-`(c)` substitution
   in disguise: the construction's correctness is relative to that model. Write that down
   in the ledger rather than letting an auditor find it later.

6. **Surface friction; don't work around it silently.** The roadmap's design decisions
   (`dd:fuel`, `dd:dsl`, `dd:abstract`, `dd:asymp`) are load-bearing. If one fights
   Lean's type system, say so in the session report — do not quietly route around it. A
   stop-and-report (e.g. "Foundation doesn't expose what `def:ec` needs", "Mathlib lacks
   Brouwer") is a *success*, not a failure.

### Human read-through

The kernel covers proof bodies; it does not cover statements. Anson reads every
top-level **statement** and every **definition** before a milestone is marked done. The
trust surface is small and this is tractable — it is the specific discipline the
deference methodology skipped. Keep statements legible to that read-through.

### Scheduled adversarial audit

At the end of M3, M5, and M7, run a **separate, fresh-context** statement-level audit
over the milestone's top-level theorems, hunting specifically for: vacuous theorems
(hypotheses unsatisfiable/unrealizable); conclusion-in-hypothesis squeezes; oversold
stubs; type-`(c)` substitutions; degenerate non-vacuity (constant-sequence witnesses);
and off-loaded steps (a hand-computation where a Mathlib lemma should carry it). Where
possible, the non-vacuity guard should be discharged **by the construction (M7)** rather
than a stand-in witness — that is the principled reason the construction is in scope.

### Risk posture

Property-tail-first, construction-last is deliberate: it front-loads the tractable,
downstream-relevant, *conditional* results. A green property tail conditioned on
`[IsLogicalInductor P]` is real and valuable — but only if the exploiting traders are
genuinely constructed and e.c.-certified. Until M7 lands, every result is **conditional
on the existence of a logical inductor, which is assumed, not proved.** Any public
writeup must say so explicitly.

---

## Working conventions

- Namespace `LogicalInduction`; file layout mirrors the roadmap's Parts (see
  `LogicalInduction.lean`).
- One `Asymptotics` module owns the limit vocabulary (`≈ₙ`/`≳ₙ`, "eventually within ε",
  "converges to"), built on Mathlib's `Tendsto (· − ·) atTop (𝓝 0)` and `∀ᶠ n in atTop`.
  Do not redefine these per file (`dd:asymp`). Default to the **limiting** form (the
  downstream deference work consumes it); add the finite-stage form only where needed.
- Foundation supplies the propositional substrate: `Formula α` (with
  `Encodable (Formula α)` for `[Encodable α]` → computable sentence codes),
  `LO.Entailment` (`⊢`, `⊬`, `Consistent`), and `Propositional.Cl`. Wrap what we use
  behind a thin `LogicalInduction.Sentence` interface; don't scatter Foundation internals.
- Commit messages: no Claude/AI co-authorship lines. Push to `origin` freely; ask before
  pushing anywhere else.
