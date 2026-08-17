# Specification: a renderable, manipulable calculus of approximate Bayes-net diagrams

**Status:** specification + feasibility spike. Nothing here is a formalization of *Natural
Latents*; this defines the object that would have to exist first.

## 0. Why this document exists

*Natural Latents* (Wentworth & Lorell, arXiv:2509.03780) states both of its theorems, both
corollaries, its key lemma and **the entire proof of its main theorem** as raster images —
verified from the arXiv source, where every `\includegraphics` is a `.png`. There is no
printed formula to check a Lean statement against.

That relocates the trust surface. Ordinarily a formalization is reviewed by reading the
Lean statement beside the paper's displayed equation. Here that comparison is impossible,
so **transcription becomes the load-bearing, unreviewable step** — precisely the failure
mode this repository's standards exist to prevent ("a kernel-clean proof certifies that the
body matches the statement; it says nothing about whether the statement is the one we
meant").

The fix is not to transcribe more carefully. It is to make the diagram a **first-class
formal object** that (a) can be rendered back to a picture a human compares against the
paper's figure, and (b) is manipulated by proved lemmas rather than by hand. Then the
unreviewable step is replaced by a *visual* comparison, which is the review the paper's
format actually permits.

This is also why it is worth doing at all: a 4-node paper does not justify the effort, but
a reusable approximate-Bayes-net calculus does. Condensation's §5 error bookkeeping wants
substantially the same vocabulary.

---

## 1. Scope

**In scope.** A paper-neutral Lean library providing:

1. a type of Bayes-net diagrams with approximation annotations;
2. a semantics: what it means for a distribution to satisfy a diagram to within `ε`;
3. the diagram-rewriting rules as proved lemmas;
4. a renderer emitting TikZ.

**Out of scope.** Natural Latents' theorems themselves; d-separation (see §6.3); anything
continuous (see §5).

---

## 2. Requirements

### R1 — Rendering fidelity (the reviewability requirement)

**R1.1** Every diagram value must render to TikZ via a total function
`render : Diagram → String`, with no manual steps.

**R1.2** The rendered output must carry every feature the paper's figures carry, because a
missing feature is a silent divergence:

| feature | appears in | must render |
| --- | --- | --- |
| nodes with labels (`Λ`, `Λ'`, `X₁`, `Xᵢ`, `Xⱼ`) | all figures | ✅ |
| directed edges | all | ✅ |
| **repeated variable at two nodes** (`Λ' ← Λ → Λ'`) | Figs 4, 5, 6, 7, 8, 9 | ✅ — see R2.1 |
| `ε` annotation under a diagram | Figs 2, 4–9 | ✅ |
| **compound `ε` expressions** (`ε_med + 2ε_red`) | Figs 7, 9 | ✅ |
| dashed grouping box around a sub-diagram | Figs 4, 5, 6, 7, 9 | ✅ |
| group captions (`Redundancy of Λ'`, `Mediation by Λ`) | Figs 4–7, 9 | ✅ |
| `∀k` badge on a schema | Figs 3, 9 | ✅ |
| conditioning-on-a-model bar (`| Mᴮ`) | Fig 7 | ✅ |

**R1.3** The comparison is **human, side-by-side, and documented as such.** It is
impossible to *prove* a renderer matches a PNG. The README must say: "this renders to a
diagram a reader can compare against Figure N", never "verified equivalent to Figure N".

**R1.4** Each rendered figure is committed next to the paper's PNG with a short note
recording who compared them and when — the same discipline as this repo's human statement
read-through, applied to pictures.

**R1.5** The renderer must be *derived from the same value the theorems are about.* A
separate hand-written TikZ file that happens to look right is worthless: the point is that
what is rendered **is** what is proved about.

### R2 — Formal manipulability

**R2.1 (the crux) — node identity is not variable identity.** The paper's determinism
notation is `Y ← X → Y`: the same random variable at two distinct nodes. The D.B. Lemma is
literally "add another copy of `Y` as a child of `X`". So:

- diagrams are over an abstract **node** type;
- an **interpretation** assigns a random variable to each node and **must be permitted to
  be non-injective**;
- nothing in the API may assume injectivity.

Identifying nodes with variables makes the D.B. Lemma unstatable, not merely awkward. This
is the single decision that determines whether the design works.

**R2.2** The rules the paper uses must be *lemmas about the diagram type*, not
metatheoretic side conditions:

| rule | source | note |
| --- | --- | --- |
| Frankenstein | App. A.1, proved | stated but never used in the paper |
| Factorization Transfer | App. A.2, proved | |
| Bookkeeping | App. A.3, proved | stated but never used; hypothesis is semantic — see §6.3 |
| Dangly Bit | App. B, proved | needs R2.1 |
| **Marginalize** | **used twice in Fig 9, never stated or proved** | must be supplied |

**R2.3** A proof in the calculus must be a *chain of these lemmas*, so that the Lean proof
of Theorem 1 has the same five steps as Figure 9 (Marginalize → D.B. → D.B. → Marginalize),
in the same order, with the same `ε` arithmetic. A proof that reaches the right conclusion
by unrelated means fails this requirement: the point is that the Lean proof is *checkable
against the picture*.

**R2.4** `ε` must be first-class and compositional, so `ε_med + 2ε_red` is a value in the
diagram, not a comment.

### R3 — Semantics anchored to the paper

**R3.1** `Satisfies P D ι ε` must unfold to the paper's own definition:
`ε ≥ D_KL(P ‖ ∏ᵢ P[Yᵢ | Y_pa(i)])`. Note the factorization is built **from `P` itself**.

**R3.2 — the acceptance test.** The paper derives in text (p. 2, the one place it does
this) that the determinism diagram reduces to conditional entropy. The library must prove:

> For the diagram `y₁ ← x → y₂` interpreted with `var y₁ = var y₂ = Y` and `var x = X`,
> `Satisfies P D ι ε ↔ ε ≥ H[Y | X]`.

This is the bridge between the diagram calculus and the entropy layer, it is the only
diagram identity the paper writes out longhand, and it is therefore the one place the
formal semantics can be **checked against text rather than against a picture**. It should
be proved before anything else is built on top.

**R3.3** Satisfaction must be monotone in `ε`, and `ε = 0` must recover exact
factorization.

### R4 — Reusability

Paper-neutral: no NL vocabulary (`mediation`, `redundancy`, `naturality`, `Λ`) in the
calculus. Those are *definitions a consumer writes* using it.

### R5 — Trust surface

`sorry`-free; no new axioms; axiom-audited endpoints; and an explicit four-way split in the
docs between **inherited mathematics**, **the calculus's own proofs**, **the transcription
claims** (R1.4, human-checked), and **known gaps in the source paper** (§6).

---

## 3. Findings from the spike

Established in `Spike.lean` on this branch (compiles, `sorry`-free):

**F1 — R2.1 is satisfiable, and cheap.** Splitting nodes from variables typechecks and
supports the repeated-variable pattern directly. `detDiagram` below has two distinct nodes
carrying the same variable; nothing objects.

**F2 — the factorization needs no measure-theoretic disintegration in the discrete case.**
This is the significant cost finding. Over a finite sample space the factorization is
*pointwise arithmetic*:

```
q(y) = ∏ᵢ P[Yᵢ = yᵢ | Y_pa(i) = y_pa(i)]
```

— elementary conditional probabilities and a product, not kernels. The 948-line
`Kernel/Disintegration` machinery I expected to need is **not** required for the
finite-range fragment. The calculus can therefore sit on a small bespoke finite-pmf layer,
using the vendored entropy library only for the R3.2 bridge. That materially lowers the
estimate.

**F3 — rendering is trivial and worth doing first.** `render` is ~40 lines and produces
compilable TikZ. Sample output for the mediation diagram is committed as
`rendered/mediation.tex`. Doing it early is the right order: it makes every subsequent
design decision visible.

**F3a — `import Mathlib` does not co-exist with the vendored PFR layer.**  Hit immediately:

```
import PFR.Mathlib.Probability.IdentDistrib failed, environment already contains
'ProbabilityTheory.IdentDistrib.prodMk' from Mathlib.Probability.IdentDistribIndep
```

PFR's `Mathlib/` shims re-declare lemmas that FAF's newer Mathlib pin has since acquired, so
a file importing *all* of Mathlib alongside `ShannonInformation.API` fails.  Targeted
imports work fine, and the existing client tests are unaffected — but a downstream paper
library that opens with `import Mathlib` (common) plus the entropy layer will hit this.
This is a real usability constraint on the consumer surface and is now recorded in
`ShannonInformation/README.md`.  Worth investigating whether a third vendor patch deleting
the now-redundant shim declarations removes the constraint entirely; not attempted here.

**F3b — heterogeneous node types are deferred, and are a real design question.**  The spike
uses a single value type for all nodes.  The paper's nodes are heterogeneous (`Λ` and `Xᵢ`
need not share a value type), so the real encoding wants `Val : N → Type` — at which point
constructing example interpretations fights `fin_cases`, which cannot eliminate into `Type`.
How to carry per-node `Fintype`/`DecidableEq` instances is an open question for the
encoding, not a difficulty in the mathematics.

**F4 — the acceptance test's proof is exactly the paper's p.2 derivation**, and I
re-derived it independently to the same answer:

```
D_KL(P ‖ q) = Σ_{a,b,b'} P(a,b,b') log( P(a,b,b') / (P(a)·P(b|a)·P(b'|a)) )
            = Σ_{a,b}    P(a,b)    log( P(a,b)   / (P(a,b)·P(b|a)) )
            = Σ_{a,b}    P(a,b) · (−log P(b|a))  =  H(Y|X)
```

the collapse being that `P` is supported on the diagonal `b = b'`. The spike states this;
**it does not prove it** — see §7.

## 4. Non-goals

- Proving the renderer correct against the PNGs (impossible; R1.3).
- General measure-theoretic diagrams (§5).
- A d-separation library (§6.3).

## 5. Scope boundary: discrete and finite

The calculus as specified is for **finite discrete** distributions, consistent with
`ShannonInformation/SCOPE.md`. This is narrower than *Natural Latents* as written — its
worked example uses a latent uniform on `[0,1]` — and the boundary must be disclosed by any
consumer, not inferred. See that file for the general argument; it applies verbatim here.

## 6. Known gaps in the source paper that the design must accommodate

**6.1 Marginalize is missing.** Used twice in the only proof the paper gives; never stated,
never proved. The library must supply and prove it. Expected form: if `P` over `(X,Y)`
satisfies `D` to within `ε`, the `X`-marginal satisfies the node-restricted diagram to
within `ε`. This should follow from the KL chain rule, but it is *new work*, not
transcription.

**6.2 Theorem 2's approximate converse has no written `ε` accounting.** The "only if"
direction is one sentence of exact-case reasoning ("consider `Λᴮ = X₁` or `X₂`") attached to
a statement carrying `ε_med' + 2ε_red'`. Nothing in text or figure says what `ε` the
converse recovers. A formalization must either derive it or state the theorem in a weaker,
honest form and disclose the divergence.

**6.3 The Bookkeeping rule's hypothesis is semantic.** "Every distribution factoring over
`G₁` also factors over `G₂`" is independence-model inclusion — a d-separation question, and
the one place d-separation could re-enter a project that otherwise avoids it. **Design
decision required:** either (a) keep the hypothesis abstract and only ever instantiate it at
concrete pairs where inclusion is proved directly, or (b) build a decision procedure and
inherit the whole d-separation problem. **(a) is recommended**; the paper never uses the
rule anyway.

## 7. Deliberately open

The R3.2 acceptance test is **stated but not proved** in the spike. That is intentional: it
is the design target, and how cleanly it proves is the measure of whether an encoding is
right. An encoding that makes it fall out in a dozen lines is a good encoding; one that
makes it a three-hundred-line slog has the wrong `Satisfies`.

It is the first thing to hand to whoever designs the real encoding.
